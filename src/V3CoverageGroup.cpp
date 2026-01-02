// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Covergroup lowering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3COVERAGEGROUP TRANSFORMATIONS:
//      For each covergroup (AstClass with isCovergroup()):
//          For each coverpoint:
//              Create counter variables for each bin
//              Add sample() body to check expression and increment counters
//              Add get_coverage() body to calculate coverage percentage
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3CoverageGroup.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// CoverageGroup state, as a visitor of each AstNode

class CoverageGroupVisitor final : public VNVisitor {
    // NODE STATE
    // Entire netlist:
    //  AstClass::user1()  -> bool. True indicates covergroup already processed
    const VNUser1InUse m_inuser1;

    // STATE
    AstClass* m_classp = nullptr;  // Current covergroup class
    AstFunc* m_sampleFuncp = nullptr;  // sample() function to add code to
    AstFunc* m_getCoverageFuncp = nullptr;  // get_coverage() (static) function
    AstFunc* m_getInstCoverageFuncp = nullptr;  // get_inst_coverage() function
    int m_binCount = 0;  // Total number of bins in this covergroup
    int m_coveredExpr = 0;  // Running count expression for get_coverage

    // List of hit flags for get_coverage calculation (instance level)
    std::vector<AstVar*> m_hitVars;

    // List of counter variables for at_least support (parallel to m_hitVars)
    std::vector<AstVar*> m_counterVars;

    // List of static hit flags for get_coverage() (type level)
    std::vector<AstVar*> m_staticHitVars;

    // Cross coverage support: bin info including value ranges for intersect
    struct CovBinInfo {
        string name;
        AstVar* hitVar;
        std::vector<std::pair<int64_t, int64_t>> valueRanges;  // (lo, hi) pairs
        CovBinInfo(const string& n, AstVar* v)
            : name{n}
            , hitVar{v} {}
        CovBinInfo(const string& n, AstVar* v, int64_t lo, int64_t hi)
            : name{n}
            , hitVar{v}
            , valueRanges{{lo, hi}} {}
        void addRange(int64_t lo, int64_t hi) { valueRanges.push_back({lo, hi}); }
    };
    std::map<string, std::vector<CovBinInfo>> m_cpBinHitVars;

    // Sample arg support: map arg name -> function argument AstVar
    std::map<string, AstVar*> m_sampleArgs;

    // Enclosing class support (for class-embedded covergroups)
    AstClass* m_enclosingClassp = nullptr;  // Enclosing class if covergroup is class-embedded
    AstVar* m_parentPtrVarp = nullptr;  // __Vparentp member variable

    // Covergroup inheritance support: track bin info by covergroup name (for covergroup extends)
    // Static map from covergroup name to (coverpoint name -> bin names list)
    static std::map<string, std::map<string, std::vector<string>>> s_cgBinInfo;

    // Coverage options extracted from option.* assignments
    struct CovergroupOptions {
        bool perInstance = false;
        string comment;
        int weight = 1;
        int atLeast = 1;
        int goal = 100;
        int autoBinMax = 64;  // IEEE default
    };

    // Current covergroup options
    CovergroupOptions m_options;

    // METHODS

    // Extract coverage options from AstCgOptionAssign nodes
    CovergroupOptions extractOptions(AstClass* classp) {
        CovergroupOptions opts;
        // Search for AstCgOptionAssign nodes in the class
        classp->foreach([&](AstCgOptionAssign* const op) {
            const string& name = op->name();
            AstConst* const valp = VN_CAST(op->valuep(), Const);
            if (name == "per_instance" && valp) {
                opts.perInstance = valp->toUInt();
                UINFO(4, "  option.per_instance = " << opts.perInstance << endl);
            } else if (name == "weight" && valp) {
                opts.weight = valp->toSInt();
                UINFO(4, "  option.weight = " << opts.weight << endl);
            } else if (name == "at_least" && valp) {
                opts.atLeast = valp->toSInt();
                UINFO(4, "  option.at_least = " << opts.atLeast << endl);
            } else if (name == "auto_bin_max" && valp) {
                opts.autoBinMax = valp->toSInt();
                UINFO(4, "  option.auto_bin_max = " << opts.autoBinMax << endl);
            } else if (name == "goal" && valp) {
                opts.goal = valp->toSInt();
                UINFO(4, "  option.goal = " << opts.goal << endl);
            } else if (name == "comment") {
                if (AstConst* const sp = VN_CAST(op->valuep(), Const)) {
                    opts.comment = sp->num().toString();
                    UINFO(4, "  option.comment = " << opts.comment << endl);
                }
            }
        });
        return opts;
    }
    string makeVarName(const string& prefix, const string& cpName, const string& binName) {
        string name = prefix + cpName;
        if (!binName.empty()) name += "_" + binName;
        return name;
    }

    // Create a counter variable in the covergroup class
    AstVar* createCounterVar(FileLine* fl, const string& name) {
        AstVar* const varp
            = new AstVar{fl, VVarType::MEMBER, name, m_classp->findUInt32DType()};
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        varp->valuep(new AstConst{fl, 0});
        m_classp->addMembersp(varp);
        return varp;
    }

    // Create a hit flag variable in the covergroup class (instance level)
    AstVar* createHitVar(FileLine* fl, const string& name) {
        AstVar* const varp = new AstVar{fl, VVarType::MEMBER, name, m_classp->findBitDType()};
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        varp->valuep(new AstConst{fl, AstConst::BitFalse{}});
        m_classp->addMembersp(varp);
        return varp;
    }

    // Create a static hit flag for type-level coverage (get_coverage())
    AstVar* createStaticHitVar(FileLine* fl, const string& name) {
        AstVar* const varp
            = new AstVar{fl, VVarType::MEMBER, name + "_s", m_classp->findBitDType()};
        varp->lifetime(VLifetime::STATIC_EXPLICIT);
        varp->valuep(new AstConst{fl, AstConst::BitFalse{}});
        m_classp->addMembersp(varp);
        return varp;
    }

    // Transform expression to use sample() function arguments instead of class members
    // This is needed because coverpoint expressions reference temporary class members
    // but at runtime they need to reference the sample() function arguments
    class SampleArgTransformVisitor final : public VNVisitor {
        std::map<string, AstVar*>& m_sampleArgs;

    public:
        explicit SampleArgTransformVisitor(AstNodeExpr* exprp, std::map<string, AstVar*>& sampleArgs)
            : m_sampleArgs{sampleArgs} {
            iterate(exprp);
        }
        void visit(AstVarRef* nodep) override {
            // Check if this VarRef matches a sample argument name
            if (nodep->varp()) {
                auto it = m_sampleArgs.find(nodep->varp()->name());
                if (it != m_sampleArgs.end()) {
                    // Replace with reference to sample function argument
                    nodep->varp(it->second);
                }
            }
        }
        void visit(AstNode* nodep) override { iterateChildren(nodep); }
    };

    // Visitor to detect and transform references to enclosing class members
    // This transforms VarRefs that point to the enclosing class to use __Vparentp->member
    class EnclosingClassTransformVisitor final : public VNVisitor {
        AstClass* m_covergroupp;  // The covergroup class
        AstClass* m_enclosingClassp;  // The enclosing class
        AstVar* m_parentPtrVarp;  // __Vparentp member variable
        // Collect nodes to transform (avoid modifying tree during iteration)
        std::vector<AstMemberSel*> m_memberSelsToTransform;
        std::vector<AstVarRef*> m_varRefsToTransform;

    public:
        explicit EnclosingClassTransformVisitor(AstNodeExpr* exprp, AstClass* covergroupp,
                                                AstClass* enclosingClassp, AstVar* parentPtrVarp)
            : m_covergroupp{covergroupp}
            , m_enclosingClassp{enclosingClassp}
            , m_parentPtrVarp{parentPtrVarp} {
            if (exprp) {
                // First pass: collect nodes to transform
                iterate(exprp);
                // Second pass: perform transformations
                doTransforms();
            }
        }

        void doTransforms() {
            // Collect VarRefs that are fromp of MemberSels we'll transform
            // (these should not be transformed separately as standalone VarRefs)
            std::set<AstVarRef*> handledByMemberSel;
            for (AstMemberSel* nodep : m_memberSelsToTransform) {
                if (AstVarRef* const varrefp = VN_CAST(nodep->fromp(), VarRef)) {
                    handledByMemberSel.insert(varrefp);
                }
            }

            // Transform MemberSel nodes: cfg.mode -> __Vparentp->cfg.mode
            for (AstMemberSel* nodep : m_memberSelsToTransform) {
                AstVarRef* const varrefp = VN_AS(nodep->fromp(), VarRef);
                FileLine* const fl = nodep->fileline();

                // Create new VarRef to __Vparentp
                AstVarRef* const parentRefp = new AstVarRef{fl, m_parentPtrVarp, VAccess::READ};

                // Unlink original VarRef from MemberSel and reuse it
                AstNode* const originalFromp = nodep->fromp()->unlinkFrBack();
                AstVarRef* const originalVarRefp = VN_AS(originalFromp, VarRef);
                originalVarRefp->classOrPackagep(nullptr);  // Clear static class context

                // Create: __Vparentp->cfg
                AstMemberSel* const newFromp
                    = new AstMemberSel{fl, parentRefp, originalVarRefp->varp()};

                // Set the new fromp on the original MemberSel
                // This transforms: cfg.mode -> (__Vparentp->cfg).mode
                nodep->fromp(newFromp);

                // Delete the original VarRef we unlinked (we used its info but replaced it)
                VL_DO_DANGLING(originalFromp->deleteTree(), originalFromp);

                UINFO(4, "Transform enclosing class MemberSel: " << originalVarRefp->varp()->name()
                                                                 << endl);
            }

            // Transform standalone VarRef nodes (not part of MemberSel)
            for (AstVarRef* nodep : m_varRefsToTransform) {
                // Skip if this VarRef was already handled as part of a MemberSel
                if (handledByMemberSel.count(nodep)) continue;

                // For standalone VarRefs like 'data' in 'coverpoint data':
                // Just clear the classOrPackagep to make it access through instance
                // The __Vparentp member is accessed implicitly because we're in a method
                // of the covergroup that has __Vparentp pointing to the enclosing class
                //
                // Actually this needs more work - for now just clear the static class context
                // and we'll need to handle this differently at code generation time
                //
                // ALTERNATIVE: Don't transform standalone VarRefs - instead transform
                // the entire coverpoint to use __Vparentp explicitly
                nodep->classOrPackagep(nullptr);

                UINFO(4, "Cleared classOrPackagep on enclosing class VarRef: "
                              << nodep->varp()->name() << endl);
            }
        }

        void visit(AstVarRef* nodep) override {
            // Check if this VarRef references a member of the enclosing class
            // Note: MemberSel's VarRef children are handled in visit(AstMemberSel)
            // This handles standalone VarRef nodes (direct enclosing class member access)
            if (nodep->varp() && nodep->classOrPackagep() == m_enclosingClassp) {
                // Don't track here - we'll handle ALL VarRefs in doTransforms
                // by checking if they're still linked to the tree
                m_varRefsToTransform.push_back(nodep);
            }
        }

        void visit(AstMemberSel* nodep) override {
            // Check if the base of this member select is a VarRef to enclosing class
            if (AstVarRef* const varrefp = VN_CAST(nodep->fromp(), VarRef)) {
                if (varrefp->varp() && varrefp->classOrPackagep() == m_enclosingClassp) {
                    // Collect for transformation
                    m_memberSelsToTransform.push_back(nodep);
                    // Don't iterate children - the VarRef is handled as part of this
                    return;
                }
            }
            iterateChildren(nodep);
        }

        void visit(AstNode* nodep) override { iterateChildren(nodep); }
    };

    // Find enclosing class by checking VarRef nodes in coverpoint expressions
    AstClass* findEnclosingClass(AstCoverpoint* cpp) {
        AstClass* enclosingp = nullptr;

        // Check VarRef nodes in the expression to find references to enclosing class
        cpp->exprp()->foreach([&](AstVarRef* varrefp) {
            if (varrefp->classOrPackagep() && varrefp->classOrPackagep() != m_classp) {
                if (AstClass* const classp = VN_CAST(varrefp->classOrPackagep(), Class)) {
                    if (!classp->isCovergroup()) {
                        enclosingp = classp;
                        UINFO(4, "Found enclosing class: " << classp->name() << endl);
                    }
                }
            }
        });

        // Also check MemberSel chains
        cpp->exprp()->foreach([&](AstMemberSel* memberselp) {
            if (AstVarRef* const varrefp = VN_CAST(memberselp->fromp(), VarRef)) {
                if (varrefp->classOrPackagep() && varrefp->classOrPackagep() != m_classp) {
                    if (AstClass* const classp = VN_CAST(varrefp->classOrPackagep(), Class)) {
                        if (!classp->isCovergroup()) {
                            enclosingp = classp;
                            UINFO(4, "Found enclosing class via MemberSel: " << classp->name()
                                                                             << endl);
                        }
                    }
                }
            }
        });

        return enclosingp;
    }

    // Create __Vparentp member variable for enclosing class access
    void createParentPtrVar(FileLine* fl, AstClass* enclosingClassp) {
        if (m_parentPtrVarp) return;  // Already created

        // Create a RefDType to the enclosing class
        AstClassRefDType* const refDTypep = new AstClassRefDType{fl, enclosingClassp, nullptr};
        // Add to the global type table (not to the class)
        v3Global.rootp()->typeTablep()->addTypesp(refDTypep);

        // Create __Vparentp as a member variable of the covergroup class
        m_parentPtrVarp = new AstVar{fl, VVarType::MEMBER, "__Vparentp", refDTypep};
        m_parentPtrVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        m_classp->addMembersp(m_parentPtrVarp);

        UINFO(4, "Created __Vparentp for enclosing class: " << enclosingClassp->name() << endl);
    }

    // Clone expression and transform to use sample args and enclosing class parent pointer
    AstNodeExpr* cloneWithTransforms(AstNodeExpr* exprp) {
        AstNodeExpr* clonep = exprp->cloneTree(false);
        // Transform sample args first
        if (!m_sampleArgs.empty()) { SampleArgTransformVisitor{clonep, m_sampleArgs}; }
        // Transform enclosing class references to use __Vparentp
        if (m_enclosingClassp && m_parentPtrVarp) {
            EnclosingClassTransformVisitor{clonep, m_classp, m_enclosingClassp, m_parentPtrVarp};
        }
        return clonep;
    }

    // Create condition checking if expr matches a transition step value/range
    AstNodeExpr* createStepMatch(FileLine* fl, AstNodeExpr* exprp, AstNode* stepp) {
        if (AstInsideRange* const irp = VN_CAST(stepp, InsideRange)) {
            return irp->newAndFromInside(exprp, irp->lhsp()->cloneTree(false),
                                         irp->rhsp()->cloneTree(false));
        } else if (AstRange* const rp = VN_CAST(stepp, Range)) {
            AstNodeExpr* const geq = new AstGte{fl, exprp, rp->leftp()->cloneTree(false)};
            AstNodeExpr* const leq
                = new AstLte{fl, exprp->cloneTree(false), rp->rightp()->cloneTree(false)};
            return new AstLogAnd{fl, geq, leq};
        } else if (AstConst* const cp = VN_CAST(stepp, Const)) {
            return new AstEq{fl, exprp, cp->cloneTree(false)};
        } else if (AstNodeExpr* const ep = VN_CAST(stepp, NodeExpr)) {
            return new AstEq{fl, exprp, ep->cloneTree(false)};
        }
        return nullptr;
    }

    // Process a transition bin (e.g., bins x = (0 => 1 => 2))
    // Returns true if transition was processed, false if it should be skipped
    bool processTransitionBin(AstCoverBin* binp, AstCovTransition* transp, AstNodeExpr* cpExprp,
                              const string& cpName, AstNodeExpr* cpIffp, AstVar* anyMatchedVarp) {
        FileLine* const fl = binp->fileline();
        const string binName = binp->name().empty() ? "trans" + cvtToStr(m_binCount) : binp->name();

        // Count transition steps
        int numSteps = 0;
        for (AstNode* stepp = transp->stepsp(); stepp; stepp = stepp->nextp()) { ++numSteps; }

        if (numSteps < 2) {
            transp->v3warn(COVERIGN, "Transition coverage requires at least 2 values");
            return false;
        }

        UINFO(4, "Processing transition bin '" << binName << "' with " << numSteps
                                               << " steps" << endl);

        // Now create the state variable and other tracking variables
        const string stateName = makeVarName("__Vcov_trans_state_", cpName, binName);
        AstVar* const stateVarp
            = new AstVar{fl, VVarType::MEMBER, stateName, m_classp->findUInt32DType()};
        stateVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        stateVarp->valuep(new AstConst{fl, 0});
        m_classp->addMembersp(stateVarp);

        // Create counter and hit flag variables
        const string counterName = makeVarName("__Vcov_cnt_", cpName, binName);
        const string hitName = makeVarName("__Vcov_hit_", cpName, binName);
        AstVar* const counterVarp = createCounterVar(fl, counterName);
        AstVar* const hitVarp = createHitVar(fl, hitName);
        AstVar* const staticHitVarp = createStaticHitVar(fl, hitName);

        // Collect steps into a vector (don't clone yet)
        std::vector<AstNode*> steps;
        for (AstNode* stepp = transp->stepsp(); stepp; stepp = stepp->nextp()) {
            steps.push_back(stepp);
        }

        // Build state machine logic
        // For n steps: states 0..n-1, where state i means we've matched steps 0..i-1
        // When in state i and value matches step[i]:
        //   - If i == n-1: bin hit, reset to state 0
        //   - Else: advance to state i+1
        // When value doesn't match: reset to 0 (but check if matches step[0])

        // Default action: reset state to 0
        AstNode* defaultActionp
            = new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE}, new AstConst{fl, 0}};

        // If current value matches step[0], set state to 1 (start new sequence)
        // Otherwise, reset to 0
        // Note: Use cloneWithTransforms to properly handle sample args and enclosing class refs
        AstNodeExpr* step0Matchp
            = createStepMatch(fl, cloneWithTransforms(cpExprp), steps[0]->cloneTree(false));
        if (!step0Matchp) {
            transp->v3warn(COVERIGN, "Transition coverage step 0 cannot be matched");
            return false;
        }
        AstIf* resetIfp = new AstIf{
            fl, step0Matchp,
            new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE}, new AstConst{fl, 1}},
            defaultActionp};

        AstIf* outerIfp = resetIfp;

        // Build from state n-1 down to state 0
        for (int i = numSteps - 1; i >= 0; --i) {
            // Condition: state == i && value matches step[i]
            AstNodeExpr* stateEqp = new AstEq{fl, new AstVarRef{fl, stateVarp, VAccess::READ},
                                              new AstConst{fl, static_cast<uint32_t>(i)}};
            // Create a fresh step match each time
            // Note: Use cloneWithTransforms to properly handle sample args and enclosing class refs
            AstNodeExpr* stepMatchp
                = createStepMatch(fl, cloneWithTransforms(cpExprp), steps[i]->cloneTree(false));
            if (!stepMatchp) continue;
            AstNodeExpr* condp = new AstLogAnd{fl, stateEqp, stepMatchp};

            // Apply iff conditions
            if (cpIffp) { condp = new AstLogAnd{fl, cpIffp->cloneTree(false), condp}; }
            if (binp->iffp()) {
                condp = new AstLogAnd{fl, cloneWithTransforms(binp->iffp()), condp};
            }

            AstIf* ifp;
            if (i == numSteps - 1) {
                // Last step - bin is hit!
                AstAssign* const incCounterp = new AstAssign{
                    fl, new AstVarRef{fl, counterVarp, VAccess::WRITE},
                    new AstAdd{fl, new AstVarRef{fl, counterVarp, VAccess::READ},
                               new AstConst{fl, 1}}};
                AstAssign* const setHitp = new AstAssign{
                    fl, new AstVarRef{fl, hitVarp, VAccess::WRITE},
                    new AstConst{fl, AstConst::BitTrue{}}};
                AstAssign* const setStaticHitp = new AstAssign{
                    fl, new AstVarRef{fl, staticHitVarp, VAccess::WRITE},
                    new AstConst{fl, AstConst::BitTrue{}}};
                AstAssign* const resetStatep = new AstAssign{
                    fl, new AstVarRef{fl, stateVarp, VAccess::WRITE}, new AstConst{fl, 0}};

                ifp = new AstIf{fl, condp, incCounterp, outerIfp};
                ifp->addThensp(setHitp);
                ifp->addThensp(setStaticHitp);
                ifp->addThensp(resetStatep);

                if (anyMatchedVarp) {
                    AstAssign* const setAnyMatchedp = new AstAssign{
                        fl, new AstVarRef{fl, anyMatchedVarp, VAccess::WRITE},
                        new AstConst{fl, AstConst::BitTrue{}}};
                    ifp->addThensp(setAnyMatchedp);
                }
            } else {
                // Intermediate step - advance state
                AstAssign* const advanceStatep = new AstAssign{
                    fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
                    new AstConst{fl, static_cast<uint32_t>(i + 1)}};
                ifp = new AstIf{fl, condp, advanceStatep, outerIfp};
            }

            outerIfp = ifp;
        }

        m_sampleFuncp->addStmtsp(outerIfp);

        // Track for coverage calculations
        m_hitVars.push_back(hitVarp);
        m_counterVars.push_back(counterVarp);
        m_staticHitVars.push_back(staticHitVarp);
        // Transition bins don't have simple value ranges for intersect
        m_cpBinHitVars[cpName].push_back(CovBinInfo{binName, hitVarp});

        ++m_binCount;
        return true;
    }

    // Create condition: expr >= lo && expr <= hi
    // Note: exprp is consumed (not cloned here), caller must provide a fresh clone
    AstNodeExpr* createRangeCheck(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* lop,
                                  AstNodeExpr* hip) {
        if (!hip) {
            // Single value, not a range
            return new AstEq{fl, exprp, lop->cloneTree(false)};
        }
        AstNodeExpr* const geq = new AstGte{fl, exprp, lop->cloneTree(false)};
        AstNodeExpr* const leq = new AstLte{fl, exprp->cloneTree(false), hip->cloneTree(false)};
        return new AstLogAnd{fl, geq, leq};
    }

    // Process a single bin within a coverpoint
    // cpIffp is the optional coverpoint-level iff condition (already transformed)
    // anyMatchedVarp is optional - if provided, set to 1 when this bin matches (for default bins)
    void processBin(AstCoverBin* binp, AstNodeExpr* cpExprp, const string& cpName,
                    AstNodeExpr* cpIffp = nullptr, AstVar* anyMatchedVarp = nullptr) {
        FileLine* const fl = binp->fileline();
        const string binName = binp->name().empty() ? "bin" + cvtToStr(m_binCount) : binp->name();

        // Skip ignore_bins from coverage calculation
        if (binp->binType().m_e == VCoverBinType::IGNORE_BINS) return;

        // Check for transition bins FIRST before creating variables
        // This avoids creating duplicate variables when processTransitionBin also creates them
        for (AstNode* rangep = binp->rangesp(); rangep; rangep = rangep->nextp()) {
            if (AstCovTransition* const transp = VN_CAST(rangep, CovTransition)) {
                // Transition coverage - process via state machine
                // processTransitionBin creates its own counter/hit/state variables
                if (processTransitionBin(binp, transp, cpExprp, cpName, cpIffp, anyMatchedVarp)) {
                    return;  // Successfully processed transition bin
                }
                // Failed to process, fall through to try regular processing
            }
        }

        // Create counter and hit flag variables (instance level)
        const string counterName = makeVarName("__Vcov_cnt_", cpName, binName);
        const string hitName = makeVarName("__Vcov_hit_", cpName, binName);
        AstVar* const counterVarp = createCounterVar(fl, counterName);
        AstVar* const hitVarp = createHitVar(fl, hitName);

        // Create static hit flag for type-level coverage (get_coverage())
        AstVar* const staticHitVarp = createStaticHitVar(fl, hitName);

        // Build condition from bin ranges
        // Note: Use cloneWithTransforms to transform sample args and enclosing class refs
        AstNodeExpr* condp = nullptr;
        for (AstNode* rangep = binp->rangesp(); rangep; rangep = rangep->nextp()) {
            AstNodeExpr* rangeCondp = nullptr;

            if (VN_IS(rangep, CovTransition)) {
                // Already handled above, skip
                continue;
            } else if (VN_IS(rangep, CovRepetition)) {
                // Coverage repetition - already warned in V3Width, skip
                continue;
            } else if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                // InsideRange [lo:hi] - use its built-in method to create comparison
                rangeCondp = irp->newAndFromInside(cloneWithTransforms(cpExprp),
                                                   irp->lhsp()->cloneTree(false),
                                                   irp->rhsp()->cloneTree(false));
            } else if (AstRange* const rp = VN_CAST(rangep, Range)) {
                // Range [lo:hi]
                rangeCondp = createRangeCheck(fl, cloneWithTransforms(cpExprp),
                                              rp->leftp(), rp->rightp());
            } else if (AstConst* const cp = VN_CAST(rangep, Const)) {
                // Single value
                if (binp->isWildcard() && cp->num().isAnyXZ()) {
                    // Wildcard bin with X/Z bits - use mask-based comparison
                    // For value like 4'b01??: mask=4'b1100, expected=4'b0100
                    // Comparison: (cpExpr & mask) == expected
                    const int width = cp->width();
                    V3Number maskNum{cp, width};
                    V3Number valueNum{cp, width};
                    for (int i = 0; i < width; i++) {
                        if (cp->num().bitIsXZ(i)) {
                            // X or Z bit - mask bit is 0 (don't care)
                            maskNum.setBit(i, '0');
                            valueNum.setBit(i, '0');
                        } else {
                            // Defined bit - mask bit is 1, value from const
                            maskNum.setBit(i, '1');
                            valueNum.setBit(i, cp->num().bitIs1(i) ? '1' : '0');
                        }
                    }
                    AstNodeExpr* const cpExprClonep = cloneWithTransforms(cpExprp);
                    AstConst* const maskConstp = new AstConst{fl, maskNum};
                    AstAnd* const maskedValuep = new AstAnd{fl, cpExprClonep, maskConstp};
                    AstConst* const expectedConstp = new AstConst{fl, valueNum};
                    rangeCondp = new AstEq{fl, maskedValuep, expectedConstp};
                } else {
                    rangeCondp
                        = new AstEq{fl, cloneWithTransforms(cpExprp), cp->cloneTree(false)};
                }
            } else if (AstNodeExpr* const ep = VN_CAST(rangep, NodeExpr)) {
                // Expression value
                rangeCondp = new AstEq{fl, cloneWithTransforms(cpExprp), ep->cloneTree(false)};
            }

            if (rangeCondp) {
                if (condp) {
                    condp = new AstLogOr{fl, condp, rangeCondp};
                } else {
                    condp = rangeCondp;
                }
            }
        }

        // If no condition was built, skip this bin
        if (!condp) return;

        // Apply bin-level iff condition if present
        // Must use cloneWithTransforms to resolve sample arguments correctly
        if (binp->iffp()) {
            condp = new AstLogAnd{fl, cloneWithTransforms(binp->iffp()), condp};
        }

        // Apply coverpoint-level iff condition if present
        // Note: cpIffp is already transformed by caller
        if (cpIffp) {
            condp = new AstLogAnd{fl, cpIffp->cloneTree(false), condp};
        }

        // For illegal_bins, generate error when hit
        if (binp->binType().m_e == VCoverBinType::ILLEGAL_BINS) {
            // if (condp) { $display("Error: illegal bin hit"); $stop; }
            AstDisplay* const displayp
                = new AstDisplay{fl, VDisplayType::DT_ERROR,
                                 "Illegal bin '" + binName + "' hit in coverpoint '" + cpName + "'",
                                 nullptr, nullptr};
            // Set timeunit to avoid "Use of %t must be under AstDisplay" error
            displayp->fmtp()->timeunit(v3Global.rootp()->timeunit());
            AstStop* const stopp = new AstStop{fl, false};
            AstIf* const ifp = new AstIf{fl, condp, displayp, nullptr};
            ifp->addThensp(stopp);
            m_sampleFuncp->addStmtsp(ifp);
            return;
        }

        // Generate: if (condp) { counter++; hit = 1; staticHit = 1; }
        AstVarRef* const counterRefW
            = new AstVarRef{fl, counterVarp, VAccess::WRITE};
        AstVarRef* const counterRefR = new AstVarRef{fl, counterVarp, VAccess::READ};
        AstAssign* const incCounterp = new AstAssign{
            fl, counterRefW, new AstAdd{fl, counterRefR, new AstConst{fl, 1}}};

        AstVarRef* const hitRefW = new AstVarRef{fl, hitVarp, VAccess::WRITE};
        AstAssign* const setHitp = new AstAssign{fl, hitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        // Also set static hit flag for type-level coverage
        AstVarRef* const staticHitRefW = new AstVarRef{fl, staticHitVarp, VAccess::WRITE};
        AstAssign* const setStaticHitp
            = new AstAssign{fl, staticHitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        AstIf* const ifp = new AstIf{fl, condp, incCounterp, nullptr};
        ifp->addThensp(setHitp);
        ifp->addThensp(setStaticHitp);

        // If tracking matches for default bin, set the anyMatched flag
        if (anyMatchedVarp) {
            AstVarRef* const anyMatchedRefW = new AstVarRef{fl, anyMatchedVarp, VAccess::WRITE};
            AstAssign* const setAnyMatchedp
                = new AstAssign{fl, anyMatchedRefW, new AstConst{fl, AstConst::BitTrue{}}};
            ifp->addThensp(setAnyMatchedp);
        }

        m_sampleFuncp->addStmtsp(ifp);

        // Track for get_inst_coverage() (counter for at_least, hit for legacy)
        m_hitVars.push_back(hitVarp);
        m_counterVars.push_back(counterVarp);

        // Track for get_coverage() (static)
        m_staticHitVars.push_back(staticHitVarp);

        // Track for cross coverage (map coverpoint name -> bin name + hit var)
        // Extract value ranges from rangesp for intersect support
        CovBinInfo binInfo{binName, hitVarp};
        for (AstNode* rangep = binp->rangesp(); rangep; rangep = rangep->nextp()) {
            if (AstRange* const rp = VN_CAST(rangep, Range)) {
                // Range [lo:hi] (legacy format)
                if (AstConst* const lop = VN_CAST(rp->leftp(), Const)) {
                    if (AstConst* const hip = VN_CAST(rp->rightp(), Const)) {
                        if (!lop->num().isFourState() && !hip->num().isFourState()) {
                            binInfo.addRange(lop->num().toSQuad(), hip->num().toSQuad());
                        }
                    }
                }
            } else if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                // InsideRange [lo:hi] (from value_range in grammar)
                if (AstConst* const lop = VN_CAST(irp->lhsp(), Const)) {
                    if (AstConst* const hip = VN_CAST(irp->rhsp(), Const)) {
                        if (!lop->num().isFourState() && !hip->num().isFourState()) {
                            binInfo.addRange(lop->num().toSQuad(), hip->num().toSQuad());
                        }
                    }
                }
            } else if (AstConst* const cp = VN_CAST(rangep, Const)) {
                // Single value - skip if 4-state (wildcard bins with x/z)
                if (!cp->num().isFourState()) {
                    binInfo.addRange(cp->num().toSQuad(), cp->num().toSQuad());
                }
            }
        }
        m_cpBinHitVars[cpName].push_back(binInfo);

        ++m_binCount;
    }

    // Process a default bin - matches when no other bin in the coverpoint matches
    // anyMatchedVarp is set to true by regular bins when they match
    void processDefaultBin(AstCoverBin* binp, AstNodeExpr* cpExprp, const string& cpName,
                           AstNodeExpr* cpIffp, AstVar* anyMatchedVarp) {
        FileLine* const fl = binp->fileline();
        const string binName = binp->name().empty() ? "default" : binp->name();

        // Create counter and hit flag variables (instance level)
        const string counterName = makeVarName("__Vcov_cnt_", cpName, binName);
        const string hitName = makeVarName("__Vcov_hit_", cpName, binName);
        AstVar* const counterVarp = createCounterVar(fl, counterName);
        AstVar* const hitVarp = createHitVar(fl, hitName);

        // Create static hit flag for type-level coverage (get_coverage())
        AstVar* const staticHitVarp = createStaticHitVar(fl, hitName);

        // Build condition: NOT anyMatched (meaning no other bin matched)
        AstVarRef* const anyMatchedRef = new AstVarRef{fl, anyMatchedVarp, VAccess::READ};
        AstNodeExpr* condp = new AstLogNot{fl, anyMatchedRef};

        // Apply coverpoint-level iff condition if present
        if (cpIffp) {
            condp = new AstLogAnd{fl, cpIffp->cloneTree(false), condp};
        }

        // Apply bin-level iff condition if present
        if (binp->iffp()) {
            condp = new AstLogAnd{fl, cloneWithTransforms(binp->iffp()), condp};
        }

        UINFO(4, "Processing default bin '" << binName << "' for coverpoint '" << cpName << "'"
                                            << endl);

        // Generate: if (condp) { counter++; hit = 1; staticHit = 1; }
        AstVarRef* const counterRefW = new AstVarRef{fl, counterVarp, VAccess::WRITE};
        AstVarRef* const counterRefR = new AstVarRef{fl, counterVarp, VAccess::READ};
        AstAssign* const incCounterp
            = new AstAssign{fl, counterRefW, new AstAdd{fl, counterRefR, new AstConst{fl, 1}}};

        AstVarRef* const hitRefW = new AstVarRef{fl, hitVarp, VAccess::WRITE};
        AstAssign* const setHitp
            = new AstAssign{fl, hitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        AstVarRef* const staticHitRefW = new AstVarRef{fl, staticHitVarp, VAccess::WRITE};
        AstAssign* const setStaticHitp
            = new AstAssign{fl, staticHitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        AstIf* const ifp = new AstIf{fl, condp, incCounterp, nullptr};
        ifp->addThensp(setHitp);
        ifp->addThensp(setStaticHitp);
        m_sampleFuncp->addStmtsp(ifp);

        // Track for get_inst_coverage() (counter for at_least, hit for legacy)
        m_hitVars.push_back(hitVarp);
        m_counterVars.push_back(counterVarp);

        // Track for get_coverage() (static)
        m_staticHitVars.push_back(staticHitVarp);

        // Track for cross coverage (map coverpoint name -> bin name + hit var)
        // Default bins cover "everything else" - no simple value ranges for intersect
        m_cpBinHitVars[cpName].push_back(CovBinInfo{binName, hitVarp});

        ++m_binCount;
    }

    // Generate automatic bins for a coverpoint without explicit bins
    // Per IEEE 1800-2017, auto bins are generated based on the expression width
    void generateAutoBins(AstCoverpoint* cpp, AstNodeExpr* exprp, const string& cpName,
                          AstNodeExpr* cpIffp) {
        FileLine* const fl = cpp->fileline();
        const int width = exprp->width();

        // Use auto_bin_max from options (default 64)
        const int autoBinMax = m_options.autoBinMax;

        // Calculate number of possible values
        // For width > 63, limit to avoid overflow
        uint64_t numValues;
        if (width >= 64) {
            numValues = UINT64_MAX;  // Will use ranged bins
        } else {
            numValues = 1ULL << width;
        }

        UINFO(4, "Generating auto bins for " << cpName << " width=" << width
                                             << " numValues=" << numValues
                                             << " autoBinMax=" << autoBinMax << endl);

        if (numValues <= (uint64_t)autoBinMax) {
            // Create one bin per value
            for (uint64_t i = 0; i < numValues; ++i) {
                createAutoBinForValue(fl, exprp, cpName, cpIffp, i, width);
            }
        } else {
            // Create ranged bins - divide the value space into autoBinMax bins
            uint64_t binSize = numValues / autoBinMax;
            for (int i = 0; i < autoBinMax; ++i) {
                uint64_t lo = (uint64_t)i * binSize;
                uint64_t hi = (i == autoBinMax - 1) ? (numValues - 1) : (((uint64_t)i + 1) * binSize - 1);
                createAutoBinForRange(fl, exprp, cpName, cpIffp, lo, hi, i, width);
            }
        }
    }

    // Create an automatic bin for a single value
    void createAutoBinForValue(FileLine* fl, AstNodeExpr* exprp, const string& cpName,
                               AstNodeExpr* cpIffp, uint64_t value, int width) {
        const string binName = "auto[" + cvtToStr(value) + "]";

        // Create counter and hit flag variables (instance level)
        const string counterName = makeVarName("__Vcov_cnt_", cpName, "auto_" + cvtToStr(value));
        const string hitName = makeVarName("__Vcov_hit_", cpName, "auto_" + cvtToStr(value));
        AstVar* const counterVarp = createCounterVar(fl, counterName);
        AstVar* const hitVarp = createHitVar(fl, hitName);

        // Create static hit flag for type-level coverage
        AstVar* const staticHitVarp = createStaticHitVar(fl, hitName);

        // Condition: exprp == value
        AstConst* const valuep = new AstConst{fl, AstConst::Unsized64{}, value};
        valuep->dtypeSetBitSized(width, VSigning::UNSIGNED);
        AstNodeExpr* condp
            = new AstEq{fl, cloneWithTransforms(exprp), valuep};

        // Apply coverpoint-level iff condition if present
        if (cpIffp) {
            condp = new AstLogAnd{fl, cpIffp->cloneTree(false), condp};
        }

        // Generate: if (condp) { counter++; hit = 1; staticHit = 1; }
        AstVarRef* const counterRefW = new AstVarRef{fl, counterVarp, VAccess::WRITE};
        AstVarRef* const counterRefR = new AstVarRef{fl, counterVarp, VAccess::READ};
        AstAssign* const incCounterp = new AstAssign{
            fl, counterRefW, new AstAdd{fl, counterRefR, new AstConst{fl, 1}}};

        AstVarRef* const hitRefW = new AstVarRef{fl, hitVarp, VAccess::WRITE};
        AstAssign* const setHitp
            = new AstAssign{fl, hitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        AstVarRef* const staticHitRefW = new AstVarRef{fl, staticHitVarp, VAccess::WRITE};
        AstAssign* const setStaticHitp
            = new AstAssign{fl, staticHitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        AstIf* const ifp = new AstIf{fl, condp, incCounterp, nullptr};
        ifp->addThensp(setHitp);
        ifp->addThensp(setStaticHitp);
        m_sampleFuncp->addStmtsp(ifp);

        // Track for coverage calculations (counter for at_least, hit for legacy)
        m_hitVars.push_back(hitVarp);
        m_counterVars.push_back(counterVarp);
        m_staticHitVars.push_back(staticHitVarp);
        m_cpBinHitVars[cpName].push_back(CovBinInfo{binName, hitVarp, (int64_t)value, (int64_t)value});

        ++m_binCount;
    }

    // Create an automatic bin for a range of values
    void createAutoBinForRange(FileLine* fl, AstNodeExpr* exprp, const string& cpName,
                               AstNodeExpr* cpIffp, uint64_t lo, uint64_t hi, int binIdx,
                               int width) {
        const string binName = "auto[" + cvtToStr(lo) + ":" + cvtToStr(hi) + "]";

        // Create counter and hit flag variables
        const string counterName = makeVarName("__Vcov_cnt_", cpName, "auto_" + cvtToStr(binIdx));
        const string hitName = makeVarName("__Vcov_hit_", cpName, "auto_" + cvtToStr(binIdx));
        AstVar* const counterVarp = createCounterVar(fl, counterName);
        AstVar* const hitVarp = createHitVar(fl, hitName);

        // Create static hit flag for type-level coverage
        AstVar* const staticHitVarp = createStaticHitVar(fl, hitName);

        // Condition: exprp >= lo && exprp <= hi
        AstConst* const lop = new AstConst{fl, AstConst::Unsized64{}, lo};
        AstConst* const hip = new AstConst{fl, AstConst::Unsized64{}, hi};
        lop->dtypeSetBitSized(width, VSigning::UNSIGNED);
        hip->dtypeSetBitSized(width, VSigning::UNSIGNED);

        AstNodeExpr* const geq = new AstGte{fl, cloneWithTransforms(exprp), lop};
        AstNodeExpr* const leq = new AstLte{fl, cloneWithTransforms(exprp), hip};
        AstNodeExpr* condp = new AstLogAnd{fl, geq, leq};

        // Apply coverpoint-level iff condition if present
        if (cpIffp) {
            condp = new AstLogAnd{fl, cpIffp->cloneTree(false), condp};
        }

        // Generate: if (condp) { counter++; hit = 1; staticHit = 1; }
        AstVarRef* const counterRefW = new AstVarRef{fl, counterVarp, VAccess::WRITE};
        AstVarRef* const counterRefR = new AstVarRef{fl, counterVarp, VAccess::READ};
        AstAssign* const incCounterp = new AstAssign{
            fl, counterRefW, new AstAdd{fl, counterRefR, new AstConst{fl, 1}}};

        AstVarRef* const hitRefW = new AstVarRef{fl, hitVarp, VAccess::WRITE};
        AstAssign* const setHitp
            = new AstAssign{fl, hitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        AstVarRef* const staticHitRefW = new AstVarRef{fl, staticHitVarp, VAccess::WRITE};
        AstAssign* const setStaticHitp
            = new AstAssign{fl, staticHitRefW, new AstConst{fl, AstConst::BitTrue{}}};

        AstIf* const ifp = new AstIf{fl, condp, incCounterp, nullptr};
        ifp->addThensp(setHitp);
        ifp->addThensp(setStaticHitp);
        m_sampleFuncp->addStmtsp(ifp);

        // Track for coverage calculations (counter for at_least, hit for legacy)
        m_hitVars.push_back(hitVarp);
        m_counterVars.push_back(counterVarp);
        m_staticHitVars.push_back(staticHitVarp);
        m_cpBinHitVars[cpName].push_back(CovBinInfo{binName, hitVarp, (int64_t)lo, (int64_t)hi});

        ++m_binCount;
    }

    // Process a coverpoint
    void processCoverpoint(AstCoverpoint* cpp) {
        FileLine* const fl = cpp->fileline();
        const string cpName = cpp->name().empty() ? "cp" + cvtToStr(m_binCount) : cpp->name();

        // Get the expression being covered
        AstNodeExpr* const exprp = cpp->exprp();
        if (!exprp) return;

        // Transform coverpoint iff condition if present
        // Must use cloneWithTransforms to resolve sample arguments correctly
        AstNodeExpr* cpIffp = cpp->iffp() ? cloneWithTransforms(cpp->iffp()) : nullptr;

        // Check if there are any explicit bins (excluding default bins)
        bool hasExplicitBins = false;
        AstCoverBin* defaultBinp = nullptr;
        for (AstNode* nodep = cpp->binsp(); nodep; nodep = nodep->nextp()) {
            if (AstCoverBin* const binp = VN_CAST(nodep, CoverBin)) {
                if (binp->isDefault()) {
                    defaultBinp = binp;
                } else {
                    hasExplicitBins = true;
                }
            }
        }

        if (!hasExplicitBins) {
            // No explicit bins - generate automatic bins
            UINFO(4, "Coverpoint " << cpName << " has no explicit bins, generating auto bins"
                                   << endl);
            generateAutoBins(cpp, exprp, cpName, cpIffp);
            return;
        }

        // If there's a default bin, create a member variable to track if any regular bin matched
        // This variable is reset to 0 at start of sample(), set to 1 by any matching bin
        AstVar* anyMatchedVarp = nullptr;
        if (defaultBinp) {
            const string matchedName = makeVarName("__Vcov_any_match_", cpName, "");
            anyMatchedVarp = new AstVar{fl, VVarType::MEMBER, matchedName,
                                        m_classp->findBitDType()};
            anyMatchedVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            anyMatchedVarp->valuep(new AstConst{fl, AstConst::BitFalse{}});
            m_classp->addMembersp(anyMatchedVarp);
            // Reset to 0 at start of sample()
            AstVarRef* const matchedRefW = new AstVarRef{fl, anyMatchedVarp, VAccess::WRITE};
            AstAssign* const initMatchedp
                = new AstAssign{fl, matchedRefW, new AstConst{fl, AstConst::BitFalse{}}};
            m_sampleFuncp->addStmtsp(initMatchedp);
        }

        // Process each explicit bin, passing the coverpoint-level iff condition
        // and the anyMatched variable if we have a default bin
        for (AstNode* nodep = cpp->binsp(); nodep; nodep = nodep->nextp()) {
            if (AstCoverBin* const binp = VN_CAST(nodep, CoverBin)) {
                if (!binp->isDefault()) {
                    processBin(binp, exprp, cpName, cpIffp, anyMatchedVarp);
                }
            }
        }

        // Process default bin last - it matches when no other bin matched
        if (defaultBinp && anyMatchedVarp) {
            processDefaultBin(defaultBinp, exprp, cpName, cpIffp, anyMatchedVarp);
        }
    }

    // Helper to check if a bin's value ranges overlap with intersect values
    static bool binValuesOverlap(const CovBinInfo& binInfo, AstNode* intersectp) {
        if (!intersectp) return true;  // No intersect means match everything
        if (binInfo.valueRanges.empty()) return true;  // No ranges tracked means unknown, assume match

        // Check each intersect value/range against bin's value ranges
        for (AstNode* rangep = intersectp; rangep; rangep = rangep->nextp()) {
            int64_t intLo = 0, intHi = 0;
            if (AstConst* const cp = VN_CAST(rangep, Const)) {
                intLo = intHi = cp->num().toSQuad();
            } else if (AstRange* const rp = VN_CAST(rangep, Range)) {
                if (AstConst* const lop = VN_CAST(rp->leftp(), Const)) {
                    if (AstConst* const hip = VN_CAST(rp->rightp(), Const)) {
                        intLo = lop->num().toSQuad();
                        intHi = hip->num().toSQuad();
                    } else {
                        continue;  // Skip non-constant ranges
                    }
                } else {
                    continue;
                }
            } else if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                // InsideRange [lo:hi] (from covergroup_value_range in grammar)
                if (AstConst* const lop = VN_CAST(irp->lhsp(), Const)) {
                    if (AstConst* const hip = VN_CAST(irp->rhsp(), Const)) {
                        intLo = lop->num().toSQuad();
                        intHi = hip->num().toSQuad();
                    } else {
                        continue;
                    }
                } else {
                    continue;
                }
            } else {
                continue;
            }

            // Check if intersect range [intLo:intHi] overlaps with any bin range
            for (const auto& binRange : binInfo.valueRanges) {
                // Ranges overlap if: binLo <= intHi && intLo <= binHi
                if (binRange.first <= intHi && intLo <= binRange.second) { return true; }
            }
        }
        return false;
    }

    // Helper to evaluate a binsof expression against a specific cross bin combination
    // Returns true if the binsof expression matches the current combination
    // cpNames: list of coverpoint names in the cross
    // indices: current bin indices for each coverpoint
    // cpBinLists: list of CovBinInfo for each coverpoint
    bool evaluateBinsofExpr(AstNode* exprp, const std::vector<string>& cpNames,
                            const std::vector<size_t>& indices,
                            const std::vector<const std::vector<CovBinInfo>*>& cpBinLists) {
        if (!exprp) return false;

        // Handle && operator
        if (AstCovSelectAnd* const andp = VN_CAST(exprp, CovSelectAnd)) {
            bool lhsMatch = evaluateBinsofExpr(andp->lhsp(), cpNames, indices, cpBinLists);
            bool rhsMatch = evaluateBinsofExpr(andp->rhsp(), cpNames, indices, cpBinLists);
            return lhsMatch && rhsMatch;
        }

        // Handle || operator
        if (AstCovSelectOr* const orp = VN_CAST(exprp, CovSelectOr)) {
            bool lhsMatch = evaluateBinsofExpr(orp->lhsp(), cpNames, indices, cpBinLists);
            bool rhsMatch = evaluateBinsofExpr(orp->rhsp(), cpNames, indices, cpBinLists);
            return lhsMatch || rhsMatch;
        }

        // Handle binsof() expression
        if (AstCovBinsof* const binsofp = VN_CAST(exprp, CovBinsof)) {
            const string& cpBinRef = binsofp->coverpointName();  // e.g., "cp_a.low"

            // Parse coverpoint.bin reference
            string cpName, binName;
            size_t dotPos = cpBinRef.find('.');
            if (dotPos != string::npos) {
                cpName = cpBinRef.substr(0, dotPos);
                binName = cpBinRef.substr(dotPos + 1);
            } else {
                // Just coverpoint name without bin - matches any bin in that coverpoint
                cpName = cpBinRef;
                binName = "";  // Empty means match any bin
            }

            // Find which coverpoint index this refers to
            for (size_t i = 0; i < cpNames.size(); ++i) {
                if (cpNames[i] == cpName) {
                    const CovBinInfo& currentBin = (*cpBinLists[i])[indices[i]];

                    // Check if there's an intersect clause
                    if (binsofp->intersectp()) {
                        // binsof(cp) intersect {values} - check if bin values overlap
                        bool overlaps = binValuesOverlap(currentBin, binsofp->intersectp());
                        return binsofp->negate() ? !overlaps : overlaps;
                    }

                    // No intersect clause
                    if (binName.empty()) {
                        // Match any bin in this coverpoint - always true
                        return !binsofp->negate();
                    }
                    // Check if current bin name matches
                    bool matches = (currentBin.name == binName);
                    return binsofp->negate() ? !matches : matches;
                }
            }
            // Coverpoint not found in cross - no match
            return false;
        }

        // Unknown expression type
        return false;
    }

    // Process cross coverage
    void processCross(AstCoverCross* xp) {
        FileLine* const fl = xp->fileline();
        const string crossName = xp->name().empty() ? "cross" + cvtToStr(m_binCount) : xp->name();

        // Collect referenced coverpoint names
        std::vector<string> cpNames;
        for (AstNode* itemp = xp->itemsp(); itemp; itemp = itemp->nextp()) {
            if (AstText* const textp = VN_CAST(itemp, Text)) {
                cpNames.push_back(textp->text());
            }
        }

        if (cpNames.size() < 2) {
            xp->v3warn(E_UNSUPPORTED, "Cross coverage requires at least 2 coverpoints");
            return;
        }

        // Look up bin info for each coverpoint
        std::vector<const std::vector<CovBinInfo>*> cpBinLists;
        for (const string& cpName : cpNames) {
            auto it = m_cpBinHitVars.find(cpName);
            if (it == m_cpBinHitVars.end()) {
                // For extended covergroups, inherited coverpoints aren't fully supported yet
                if (m_classp->isExtended()) {
                    xp->v3warn(COVERIGN, "Cross coverage with inherited coverpoint '"
                                             << cpName << "' not fully supported");
                    return;
                }
                xp->v3warn(E_UNSUPPORTED,
                           "Cross coverage references unknown coverpoint '" << cpName << "'");
                return;
            }
            cpBinLists.push_back(&(it->second));
        }

        // Calculate total number of cross bins and log
        size_t totalCrossBins = 1;
        std::ostringstream crossDesc;
        for (size_t i = 0; i < cpNames.size(); ++i) {
            if (i > 0) crossDesc << " x ";
            crossDesc << cpNames[i] << " (" << cpBinLists[i]->size() << " bins)";
            totalCrossBins *= cpBinLists[i]->size();
        }
        UINFO(4, "Processing cross " << crossName << " of " << crossDesc.str()
                                     << " = " << totalCrossBins << " cross bins" << endl);

        // Collect ignore_bins and illegal_bins expressions for cross bin filtering
        // These use binsof() expressions to specify which combinations to skip
        std::vector<AstNode*> ignoreBinsExprs;
        std::vector<AstNode*> illegalBinsExprs;
        if (xp->binsp()) {
            for (AstNode* binp = xp->binsp(); binp; binp = binp->nextp()) {
                if (AstCoverBin* const cbinp = VN_CAST(binp, CoverBin)) {
                    // Get the binsof expression from rangesp
                    AstNode* binsofExpr = cbinp->rangesp();
                    if (binsofExpr) {
                        // Check if this is a binsof-based expression (CovBinsof, CovSelectAnd, or
                        // CovSelectOr)
                        if (VN_IS(binsofExpr, CovBinsof) || VN_IS(binsofExpr, CovSelectAnd)
                            || VN_IS(binsofExpr, CovSelectOr)) {
                            if (cbinp->binType().m_e == VCoverBinType::IGNORE_BINS) {
                                ignoreBinsExprs.push_back(binsofExpr);
                                UINFO(4, "  Found ignore_bins with binsof expression: "
                                             << cbinp->name() << endl);
                            } else if (cbinp->binType().m_e == VCoverBinType::ILLEGAL_BINS) {
                                illegalBinsExprs.push_back(binsofExpr);
                                UINFO(4, "  Found illegal_bins with binsof expression: "
                                             << cbinp->name() << endl);
                            }
                        }
                    }
                }
            }
        }

        // Generate N-way cross product bins using iterative approach
        // Use indices to iterate through all combinations
        std::vector<size_t> indices(cpNames.size(), 0);
        size_t ignoredCount = 0;

        while (true) {
            // Build cross bin name and collect hit vars for current combination
            string crossBinName = crossName;
            std::vector<AstVar*> hitVars;
            for (size_t i = 0; i < cpNames.size(); ++i) {
                const CovBinInfo& binInfo = (*cpBinLists[i])[indices[i]];
                crossBinName += "_" + binInfo.name;
                hitVars.push_back(binInfo.hitVar);
            }

            // Check if this combination should be ignored due to ignore_bins
            bool shouldIgnore = false;
            for (AstNode* exprp : ignoreBinsExprs) {
                if (evaluateBinsofExpr(exprp, cpNames, indices, cpBinLists)) {
                    shouldIgnore = true;
                    UINFO(5, "    Skipping cross bin '" << crossBinName
                                                        << "' due to ignore_bins" << endl);
                    break;
                }
            }
            // Also check illegal_bins (treated same as ignore_bins for coverage purposes)
            if (!shouldIgnore) {
                for (AstNode* exprp : illegalBinsExprs) {
                    if (evaluateBinsofExpr(exprp, cpNames, indices, cpBinLists)) {
                        shouldIgnore = true;
                        UINFO(5, "    Skipping cross bin '" << crossBinName
                                                            << "' due to illegal_bins" << endl);
                        break;
                    }
                }
            }

            if (shouldIgnore) {
                ++ignoredCount;
                // Skip to next combination
                size_t pos = cpNames.size() - 1;
                while (true) {
                    indices[pos]++;
                    if (indices[pos] < cpBinLists[pos]->size()) break;
                    indices[pos] = 0;
                    if (pos == 0) goto done;
                    --pos;
                }
                continue;
            }

            // Create cross bin hit flag
            AstVar* const crossHitVarp
                = createHitVar(fl, makeVarName("__Vcov_hit_", crossBinName, ""));

            // Track for coverage calculation
            m_hitVars.push_back(crossHitVarp);
            ++m_binCount;

            // Generate condition: hit1 && hit2 && hit3 && ...
            AstNodeExpr* condp = new AstVarRef{fl, hitVars[0], VAccess::READ};
            for (size_t i = 1; i < hitVars.size(); ++i) {
                AstVarRef* const hitRefp = new AstVarRef{fl, hitVars[i], VAccess::READ};
                condp = new AstLogAnd{fl, condp, hitRefp};
            }

            // Apply iff condition if present
            // Must use cloneWithTransforms to resolve sample arguments correctly
            AstNodeExpr* finalCondp = condp;
            if (xp->iffp()) {
                finalCondp = new AstLogAnd{fl, cloneWithTransforms(xp->iffp()), condp};
            }

            AstVarRef* const crossHitRefW = new AstVarRef{fl, crossHitVarp, VAccess::WRITE};
            AstAssign* const setHitp
                = new AstAssign{fl, crossHitRefW, new AstConst{fl, AstConst::BitTrue{}}};

            AstIf* const ifp = new AstIf{fl, finalCondp, setHitp, nullptr};
            m_sampleFuncp->addStmtsp(ifp);

            // Advance to next combination (like incrementing a multi-digit number)
            size_t pos = cpNames.size() - 1;
            while (true) {
                indices[pos]++;
                if (indices[pos] < cpBinLists[pos]->size()) break;  // No overflow
                indices[pos] = 0;  // Reset this digit and carry
                if (pos == 0) goto done;  // All combinations exhausted
                --pos;
            }
        }
    done:
        if (ignoredCount > 0) {
            UINFO(4, "  Cross " << crossName << ": ignored " << ignoredCount << " of "
                                << totalCrossBins << " cross bins due to ignore_bins/illegal_bins"
                                << endl);
        }
    }

    // Generate coverage percentage calculation expression
    // Uses option.at_least to determine coverage threshold
    // Uses option.weight to scale the result (weight=0 means don't count)
    AstNodeExpr* generateCoverageExpr(FileLine* fl, AstFunc* funcp) {
        if (m_hitVars.empty() || m_options.weight == 0) {
            // No bins or weight=0 means 0% coverage contribution
            V3Number zeroNum{funcp, V3Number::Double{}, 0.0};
            return new AstConst{fl, zeroNum};
        }

        // Build expression: sum of bins that meet coverage threshold
        // For at_least=1: use hit flags directly (hit1 + hit2 + ...)
        // For at_least>1: use (counter1 >= at_least) + (counter2 >= at_least) + ...
        AstNodeExpr* sumExprp = nullptr;
        const int atLeast = m_options.atLeast;

        for (size_t i = 0; i < m_hitVars.size(); ++i) {
            AstNodeExpr* coveredp;
            if (atLeast <= 1) {
                // Use hit flag directly (optimization for default case)
                AstVarRef* const hitRefp = new AstVarRef{fl, m_hitVars[i], VAccess::READ};
                coveredp = hitRefp;
            } else {
                // Use counter >= atLeast
                // Note: counterVars may be shorter if cross coverage bins were added
                // Cross bins don't have counters, they just use hit flags
                if (i < m_counterVars.size()) {
                    AstVarRef* const counterRefp
                        = new AstVarRef{fl, m_counterVars[i], VAccess::READ};
                    AstConst* const atLeastp = new AstConst{fl, static_cast<uint32_t>(atLeast)};
                    coveredp = new AstGte{fl, counterRefp, atLeastp};
                } else {
                    // Fall back to hit flag for cross bins
                    AstVarRef* const hitRefp = new AstVarRef{fl, m_hitVars[i], VAccess::READ};
                    coveredp = hitRefp;
                }
            }

            // Cast to 32-bit int for proper arithmetic
            AstNodeExpr* const extendedp = new AstExtend{fl, coveredp, 32};
            if (sumExprp) {
                sumExprp = new AstAdd{fl, sumExprp, extendedp};
            } else {
                sumExprp = extendedp;
            }
        }

        // Calculate: (sum / binCount) * 100.0
        // Convert to real: real'(sum) / real'(binCount) * 100.0
        const int totalBins = static_cast<int>(m_hitVars.size());

        // Cast sum to real
        AstNodeExpr* const sumRealp = new AstIToRD{fl, sumExprp};

        // Create constant for total bins
        V3Number totalNum{funcp, V3Number::Double{}, static_cast<double>(totalBins)};
        AstConst* const totalBinsDblp = new AstConst{fl, totalNum};

        // Divide: sum / totalBins
        AstNodeExpr* const dividep = new AstDivD{fl, sumRealp, totalBinsDblp};

        // Multiply by 100.0
        V3Number hundredNum{funcp, V3Number::Double{}, 100.0};
        AstConst* const hundredp = new AstConst{fl, hundredNum};
        return new AstMulD{fl, dividep, hundredp};
    }

    // Generate get_inst_coverage() function body (instance method - can access instance members)
    void generateGetInstCoverage() {
        if (!m_getInstCoverageFuncp) return;

        FileLine* const fl = m_getInstCoverageFuncp->fileline();
        AstNodeExpr* const percentp = generateCoverageExpr(fl, m_getInstCoverageFuncp);

        // Find return variable and assign to it
        if (AstVar* const fvarp = VN_CAST(m_getInstCoverageFuncp->fvarp(), Var)) {
            AstVarRef* const retRefp = new AstVarRef{fl, fvarp, VAccess::WRITE};
            AstAssign* const assignp = new AstAssign{fl, retRefp, percentp};
            m_getInstCoverageFuncp->addStmtsp(assignp);
        }
    }

    // Generate static coverage percentage expression from static hit flags
    // Uses option.weight to scale the result (weight=0 means don't count)
    AstNodeExpr* generateStaticCoverageExpr(FileLine* fl, AstFunc* funcp) {
        if (m_staticHitVars.empty() || m_options.weight == 0) {
            // No bins or weight=0 means 0% coverage contribution
            V3Number zeroNum{funcp, V3Number::Double{}, 0.0};
            return new AstConst{fl, zeroNum};
        }

        // Build expression: (staticHit1 + staticHit2 + ... + staticHitN)
        AstNodeExpr* sumExprp = nullptr;
        for (AstVar* hitVarp : m_staticHitVars) {
            AstVarRef* const hitRefp = new AstVarRef{fl, hitVarp, VAccess::READ};
            // Cast bit to 32-bit int for proper arithmetic
            AstNodeExpr* const extendedp = new AstExtend{fl, hitRefp, 32};
            if (sumExprp) {
                sumExprp = new AstAdd{fl, sumExprp, extendedp};
            } else {
                sumExprp = extendedp;
            }
        }

        // Calculate: (sum / binCount) * 100.0
        const int totalBins = static_cast<int>(m_staticHitVars.size());

        // Cast sum to real
        AstNodeExpr* const sumRealp = new AstIToRD{fl, sumExprp};

        // Create constant for total bins
        V3Number totalNum{funcp, V3Number::Double{}, static_cast<double>(totalBins)};
        AstConst* const totalBinsDblp = new AstConst{fl, totalNum};

        // Divide: sum / totalBins
        AstNodeExpr* const dividep = new AstDivD{fl, sumRealp, totalBinsDblp};

        // Multiply by 100.0
        V3Number hundredNum{funcp, V3Number::Double{}, 100.0};
        AstConst* const hundredp = new AstConst{fl, hundredNum};
        return new AstMulD{fl, dividep, hundredp};
    }

    // Generate get_coverage() function body (static method - type-level coverage)
    // IEEE: get_coverage() returns coverage percentage across all instances
    void generateGetCoverage() {
        if (!m_getCoverageFuncp) return;

        FileLine* const fl = m_getCoverageFuncp->fileline();
        AstNodeExpr* const percentp = generateStaticCoverageExpr(fl, m_getCoverageFuncp);

        // Find return variable and assign to it
        if (AstVar* const fvarp = VN_CAST(m_getCoverageFuncp->fvarp(), Var)) {
            AstVarRef* const retRefp = new AstVarRef{fl, fvarp, VAccess::WRITE};
            AstAssign* const assignp = new AstAssign{fl, retRefp, percentp};
            m_getCoverageFuncp->addStmtsp(assignp);
        }
    }

    // VISITORS
    void visit(AstClass* nodep) override {
        if (nodep->user1SetOnce()) return;  // Already processed
        if (!nodep->isCovergroup()) {
            iterateChildren(nodep);
            return;
        }

        UINFO(4, "Processing covergroup: " << nodep->name() << endl);

        // Reset state for this covergroup
        m_classp = nodep;
        m_sampleFuncp = nullptr;
        m_getCoverageFuncp = nullptr;
        m_getInstCoverageFuncp = nullptr;
        m_binCount = 0;
        m_hitVars.clear();
        m_counterVars.clear();
        m_staticHitVars.clear();
        m_cpBinHitVars.clear();
        m_sampleArgs.clear();
        m_enclosingClassp = nullptr;
        m_parentPtrVarp = nullptr;

        // Extract coverage options from the covergroup
        m_options = extractOptions(nodep);

        // Find sample(), get_coverage(), and get_inst_coverage() functions
        for (AstNode* memberp = nodep->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                if (funcp->name() == "sample") {
                    m_sampleFuncp = funcp;
                } else if (funcp->name() == "get_coverage") {
                    m_getCoverageFuncp = funcp;
                } else if (funcp->name() == "get_inst_coverage") {
                    m_getInstCoverageFuncp = funcp;
                }
            }
        }

        if (!m_sampleFuncp) {
            nodep->v3warn(E_UNSUPPORTED, "Covergroup missing sample() function");
            return;
        }

        // Extract sample() function arguments for coverpoint expression transformation
        for (AstNode* stmtp = m_sampleFuncp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->direction().isAny() && varp->isFuncLocal()) {
                    // This is a function argument
                    m_sampleArgs[varp->name()] = varp;
                    UINFO(4, "Found sample arg: " << varp->name() << endl);
                }
            }
        }

        // Collect coverpoints to process (they may be in constructor or stmtsp)
        std::vector<AstCoverpoint*> coverpoints;

        // Look in class statements
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstCoverpoint* const cpp = VN_CAST(stmtp, Coverpoint)) {
                coverpoints.push_back(cpp);
            }
        }

        // Also look in member functions (coverpoints may be in the constructor)
        for (AstNode* memberp = nodep->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstCoverpoint* const cpp = VN_CAST(stmtp, Coverpoint)) {
                        coverpoints.push_back(cpp);
                    }
                }
            }
        }

        UINFO(4, "Found " << coverpoints.size() << " coverpoints" << endl);

        // Detect enclosing class references in coverpoint expressions
        bool multipleEnclosingClasses = false;
        for (AstCoverpoint* cpp : coverpoints) {
            AstClass* const enclosingp = findEnclosingClass(cpp);
            if (enclosingp) {
                if (m_enclosingClassp && m_enclosingClassp != enclosingp) {
                    // Multiple enclosing classes detected (e.g., covergroup extends with
                    // references to both base and derived class members). Skip
                    // enclosing class transformation for this covergroup.
                    UINFO(4, "Covergroup references multiple enclosing classes: "
                                 << m_enclosingClassp->name() << " and " << enclosingp->name()
                                 << endl);
                    multipleEnclosingClasses = true;
                    m_enclosingClassp = nullptr;
                    break;
                }
                m_enclosingClassp = enclosingp;
            }
        }

        // Create __Vparentp if we found a single enclosing class
        if (m_enclosingClassp && !multipleEnclosingClasses) {
            createParentPtrVar(nodep->fileline(), m_enclosingClassp);
        }

        // Process all coverpoints
        for (AstCoverpoint* cpp : coverpoints) {
            processCoverpoint(cpp);
        }

        // Collect cross coverage nodes (process after coverpoints are done)
        std::vector<AstCoverCross*> crosses;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstCoverCross* const xp = VN_CAST(stmtp, CoverCross)) {
                crosses.push_back(xp);
            }
        }
        for (AstNode* memberp = nodep->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstCoverCross* const xp = VN_CAST(stmtp, CoverCross)) {
                        crosses.push_back(xp);
                    }
                }
            }
        }

        UINFO(4, "Found " << crosses.size() << " cross coverage items" << endl);

        // Process cross coverage (must be after coverpoints so bin hit vars are available)
        for (AstCoverCross* xp : crosses) {
            processCross(xp);
        }

        // Generate get_coverage() and get_inst_coverage() bodies (after all bins are created)
        generateGetCoverage();
        generateGetInstCoverage();

        // Clean up - remove AstCoverpoint nodes as they've been lowered
        for (AstCoverpoint* cpp : coverpoints) {
            VL_DO_DANGLING(cpp->unlinkFrBack()->deleteTree(), cpp);
        }

        // Clean up - remove AstCoverCross nodes after processing
        for (AstCoverCross* xp : crosses) {
            VL_DO_DANGLING(xp->unlinkFrBack()->deleteTree(), xp);
        }

        // Clean up - remove AstCgOptionAssign nodes after processing
        // These nodes were processed in extractOptions() and are no longer needed
        std::vector<AstCgOptionAssign*> optionsToDelete;
        nodep->foreach([&](AstCgOptionAssign* const op) {
            optionsToDelete.push_back(op);
        });
        for (AstCgOptionAssign* op : optionsToDelete) {
            VL_DO_DANGLING(op->unlinkFrBack()->deleteTree(), op);
        }

        // Initialize __Vparentp in the enclosing class if we have enclosing class references
        if (m_enclosingClassp && m_parentPtrVarp) {
            initializeParentPtr(nodep);
        }

        // Handle covergroup clocking event (automatic sampling)
        if (AstSenItem* const clockEventp = nodep->coverClockEventp()) {
            // For now, issue a warning that automatic sampling requires manual sample() calls
            // TODO: Generate an always block in the containing module that calls sample()
            clockEventp->v3warn(COVERIGN,
                                "Covergroup clocking event parsed but automatic sampling "
                                "not yet implemented; call sample() manually");
            // Remove the clocking event to prevent issues in later passes (like V3Gate)
            clockEventp->unlinkFrBack();
            VL_DO_DANGLING(clockEventp->deleteTree(), clockEventp);
            nodep->coverClockEventp(nullptr);
        }

        m_classp = nullptr;
    }

    // Initialize __Vparentp in the enclosing class
    // Finds the AstNew for the covergroup and adds assignment: cg.__Vparentp = this
    void initializeParentPtr(AstClass* covergroupp) {
        UINFO(4, "Initializing __Vparentp for covergroup " << covergroupp->name() << endl);

        // Find the member variable in enclosing class that holds this covergroup
        string cgMemberName;
        AstVar* cgMemberVarp = nullptr;
        for (AstNode* memberp = m_enclosingClassp->membersp(); memberp;
             memberp = memberp->nextp()) {
            if (AstVar* const varp = VN_CAST(memberp, Var)) {
                // Check if this variable's type is the covergroup
                if (AstClassRefDType* const refp = VN_CAST(varp->dtypep(), ClassRefDType)) {
                    if (refp->classp() == covergroupp) {
                        cgMemberName = varp->name();
                        cgMemberVarp = varp;
                        UINFO(4, "Found covergroup member var: " << cgMemberName << endl);
                        break;
                    }
                }
            }
        }

        if (!cgMemberVarp) {
            UINFO(4, "Could not find covergroup member variable" << endl);
            return;
        }

        // Find AstNew nodes that create the covergroup in the enclosing class
        // Look in all functions (especially constructor)
        m_enclosingClassp->foreach([&](AstAssign* assignp) {
            // Check if RHS is AstNew for the covergroup type
            if (AstNew* const newp = VN_CAST(assignp->rhsp(), New)) {
                // Check if LHS references the covergroup member
                if (AstVarRef* const lhsRefp = VN_CAST(assignp->lhsp(), VarRef)) {
                    if (lhsRefp->varp() == cgMemberVarp) {
                        // Found: cg = new;
                        // Add after: cg.__Vparentp = this;
                        FileLine* const fl = assignp->fileline();

                        // Create: cg.__Vparentp
                        AstVarRef* const cgRefp
                            = new AstVarRef{fl, cgMemberVarp, VAccess::READWRITE};
                        AstMemberSel* const lhsp
                            = new AstMemberSel{fl, cgRefp, m_parentPtrVarp};

                        // Create: this
                        // Need to create ClassRefDType for the enclosing class
                        AstClassRefDType* const thisTypep
                            = new AstClassRefDType{fl, m_enclosingClassp, nullptr};
                        v3Global.rootp()->typeTablep()->addTypesp(thisTypep);
                        AstNodeExpr* const thisp = new AstThisRef{fl, thisTypep};

                        // Create assignment: cg.__Vparentp = this;
                        AstAssign* const initAssignp = new AstAssign{fl, lhsp, thisp};

                        // Insert after the original assignment
                        assignp->addNextHere(initAssignp);

                        UINFO(4, "Added __Vparentp initialization after: " << assignp << endl);
                    }
                }
            }
        });
    }

    void visit(AstNodeModule* nodep) override { iterateChildren(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CoverageGroupVisitor(AstNetlist* rootp) { iterateChildren(rootp); }
    ~CoverageGroupVisitor() override = default;
};

// Static member definition
std::map<string, std::map<string, std::vector<string>>> CoverageGroupVisitor::s_cgBinInfo;

//######################################################################
// CoverageGroup class functions

void V3CoverageGroup::coverageGroup(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { CoverageGroupVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coveragegroup", 0, dumpTreeEitherLevel() >= 3);
}
