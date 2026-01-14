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

    // Constructor arg support: map constructor param name -> class member AstVar
    // These are used to transform VARREFs that reference constructor params to class members
    std::map<string, AstVar*> m_constructorArgs;

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
        int crossAutoBinMax = 0;  // IEEE default (0 = unlimited)
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
            } else if (name == "cross_auto_bin_max" && valp) {
                opts.crossAutoBinMax = valp->toSInt();
                UINFO(4, "  option.cross_auto_bin_max = " << opts.crossAutoBinMax << endl);
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
        // Sanitize: replace [] with _ for C++ identifier compatibility
        for (size_t i = 0; i < name.size(); ++i) {
            if (name[i] == '[' || name[i] == ']') name[i] = '_';
        }
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

    // Transform expression to use class members instead of constructor parameters
    // This is needed because coverpoint expressions may reference constructor params
    // but these get deleted by V3Task, so we need to use the class member copies
    class ConstructorArgTransformVisitor final : public VNVisitor {
        std::map<string, AstVar*>& m_constructorArgs;

    public:
        explicit ConstructorArgTransformVisitor(AstNodeExpr* exprp,
                                                std::map<string, AstVar*>& constructorArgs)
            : m_constructorArgs{constructorArgs} {
            iterate(exprp);
        }
        void visit(AstVarRef* nodep) override {
            // Check if this VarRef matches a constructor argument name
            if (nodep->varp()) {
                auto it = m_constructorArgs.find(nodep->varp()->name());
                if (it != m_constructorArgs.end()) {
                    // Replace with reference to class member
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
        AstNodeExpr* m_rootExprp;  // Root expression being transformed
        AstNodeExpr* m_newRootp = nullptr;  // New root if the root itself was replaced
        // Collect nodes to transform (avoid modifying tree during iteration)
        std::vector<AstMemberSel*> m_memberSelsToTransform;
        std::vector<AstVarRef*> m_varRefsToTransform;

    public:
        explicit EnclosingClassTransformVisitor(AstNodeExpr* exprp, AstClass* covergroupp,
                                                AstClass* enclosingClassp, AstVar* parentPtrVarp)
            : m_covergroupp{covergroupp}
            , m_enclosingClassp{enclosingClassp}
            , m_parentPtrVarp{parentPtrVarp}
            , m_rootExprp{exprp} {
            if (exprp) {
                // First pass: collect nodes to transform
                iterate(exprp);
                // Second pass: perform transformations
                doTransforms();
            }
        }

        // Get the (possibly new) root expression after transformation
        AstNodeExpr* rootp() const { return m_newRootp ? m_newRootp : m_rootExprp; }

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
            // For direct enclosing class member access like 'color', transform to:
            // __Vparentp->color
            for (AstVarRef* nodep : m_varRefsToTransform) {
                // Skip if this VarRef was already handled as part of a MemberSel
                if (handledByMemberSel.count(nodep)) continue;

                FileLine* const fl = nodep->fileline();
                AstVar* const memberVarp = nodep->varp();

                // Create new VarRef to __Vparentp
                AstVarRef* const parentRefp = new AstVarRef{fl, m_parentPtrVarp, VAccess::READ};

                // Create: __Vparentp->member
                AstMemberSel* const newMemberSelp = new AstMemberSel{fl, parentRefp, memberVarp};

                // Check if this is the root expression (no parent)
                if (nodep == m_rootExprp) {
                    // Can't use replaceWith - save new root and delete original
                    m_newRootp = newMemberSelp;
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                } else {
                    // Replace within tree
                    nodep->replaceWith(newMemberSelp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                }

                UINFO(4, "Transform enclosing class VarRef to MemberSel: " << memberVarp->name()
                                                                           << endl);
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

    // Clone expression and transform to use sample args, constructor args, and enclosing class
    AstNodeExpr* cloneWithTransforms(AstNodeExpr* exprp) {
        AstNodeExpr* clonep = exprp->cloneTree(false);
        // Transform constructor args first (replace refs to constructor params with class members)
        if (!m_constructorArgs.empty()) {
            ConstructorArgTransformVisitor{clonep, m_constructorArgs};
        }
        // Transform sample args
        if (!m_sampleArgs.empty()) { SampleArgTransformVisitor{clonep, m_sampleArgs}; }
        // Transform enclosing class references to use __Vparentp
        // Note: This may return a different root if the entire expression was a single VarRef
        if (m_enclosingClassp && m_parentPtrVarp) {
            EnclosingClassTransformVisitor visitor{clonep, m_classp, m_enclosingClassp,
                                                   m_parentPtrVarp};
            clonep = visitor.rootp();
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
        } else if (AstCovTolerance* const tp = VN_CAST(stepp, CovTolerance)) {
            // Tolerance range: [center +/- tol] or [center +%- pct]
            // For +/-: check center - tol <= expr <= center + tol
            // For +%-: check center * (1 - pct/100) <= expr <= center * (1 + pct/100)
            AstConst* const centerConstp = VN_CAST(tp->centerp(), Const);
            AstConst* const tolConstp = VN_CAST(tp->tolerancep(), Const);
            if (!centerConstp || !tolConstp) {
                tp->v3warn(COVERIGN, "Tolerance range requires constant values");
                return nullptr;
            }
            AstNodeExpr* lop;
            AstNodeExpr* hip;
            if (tp->isPercent()) {
                // Percentage: center * (1 - pct/100) to center * (1 + pct/100)
                // Get center as integer (toUQuad works for both int and real)
                const double center = static_cast<double>(centerConstp->num().toUQuad());
                // Get percentage - could be real (25.0) or integer (25)
                double pct;
                if (tolConstp->num().isDouble()) {
                    pct = tolConstp->num().toDouble() / 100.0;
                } else {
                    pct = static_cast<double>(tolConstp->num().toUQuad()) / 100.0;
                }
                const uint64_t lo = static_cast<uint64_t>(center * (1.0 - pct));
                const uint64_t hi = static_cast<uint64_t>(center * (1.0 + pct));
                lop = new AstConst{fl, AstConst::WidthedValue{}, centerConstp->width(),
                                   static_cast<uint32_t>(lo)};
                hip = new AstConst{fl, AstConst::WidthedValue{}, centerConstp->width(),
                                   static_cast<uint32_t>(hi)};
            } else {
                // Absolute: center - tol to center + tol
                lop = new AstSub{fl, centerConstp->cloneTree(false), tolConstp->cloneTree(false)};
                hip = new AstAdd{fl, centerConstp->cloneTree(false), tolConstp->cloneTree(false)};
            }
            AstNodeExpr* const geq = new AstGte{fl, exprp, lop};
            AstNodeExpr* const leq = new AstLte{fl, exprp->cloneTree(false), hip};
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

    // Process a repetition bin (e.g., bins x = (3 [*5]) or (3 [->5]))
    // Returns true if repetition was processed, false if it should be skipped
    bool processRepetitionBin(AstCoverBin* binp, AstCovRepetition* repp, AstNodeExpr* cpExprp,
                              const string& cpName, AstNodeExpr* cpIffp, AstVar* anyMatchedVarp) {
        FileLine* const fl = binp->fileline();
        const string binName = binp->name().empty() ? "rep" + cvtToStr(m_binCount) : binp->name();

        // Get the item being repeated (value or range)
        AstNode* const itemp = repp->itemp();
        if (!itemp) {
            repp->v3warn(COVERIGN, "Repetition coverage requires a value");
            return false;
        }

        // Get repetition count (must be constant for now)
        AstConst* const countConstp = VN_CAST(repp->countp(), Const);
        if (!countConstp) {
            repp->v3warn(COVERIGN, "Repetition count must be constant");
            return false;
        }
        const uint32_t repCountLo = countConstp->toUInt();
        if (repCountLo == 0) {
            repp->v3warn(COVERIGN, "Repetition count must be non-zero");
            return false;
        }

        // Handle range (e.g., [*5:6]) - get high bound if present
        uint32_t repCountHi = repCountLo;  // Default to same as low (exact count)
        if (repp->count2p()) {
            AstConst* const count2Constp = VN_CAST(repp->count2p(), Const);
            if (!count2Constp) {
                repp->v3warn(COVERIGN, "Repetition range high bound must be constant");
                return false;
            }
            repCountHi = count2Constp->toUInt();
            if (repCountHi < repCountLo) {
                repp->v3warn(COVERIGN, "Repetition range high bound must be >= low bound");
                return false;
            }
        }

        UINFO(4, "Processing repetition bin '" << binName << "' type=" << repp->repTypeString()
                                               << " count=" << repCountLo
                                               << (repCountHi != repCountLo
                                                       ? ":" + cvtToStr(repCountHi)
                                                       : "")
                                               << endl);

        // Create state counter for tracking repetitions
        const string stateName = makeVarName("__Vcov_rep_cnt_", cpName, binName);
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

        // Create condition for value match
        AstNodeExpr* matchCondp = createStepMatch(fl, cloneWithTransforms(cpExprp), itemp);
        if (!matchCondp) {
            repp->v3warn(COVERIGN, "Repetition value cannot be matched");
            return false;
        }

        // Apply iff conditions to match
        if (cpIffp) { matchCondp = new AstLogAnd{fl, cpIffp->cloneTree(false), matchCondp}; }
        if (binp->iffp()) {
            matchCondp = new AstLogAnd{fl, cloneWithTransforms(binp->iffp()), matchCondp};
        }

        // Build state machine logic based on repetition type
        const VCovRepetitionType repType = repp->repType();

        // For CONSECUTIVE [*N]: increment on match, reset on mismatch
        // For GOTO [->N] or NONCONSEC [=N]: increment on match only (don't reset)

        // Statements when value matches
        AstNode* matchStmtsp = nullptr;

        // Increment state counter: state = state + 1
        AstAssign* const incStatep = new AstAssign{
            fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
            new AstAdd{fl, new AstVarRef{fl, stateVarp, VAccess::READ}, new AstConst{fl, 1}}};
        matchStmtsp = incStatep;

        // Check if we've reached the target range: state >= N && state <= M
        // For exact count (N==M), this simplifies to state == N
        AstNodeExpr* reachedTargetp;
        if (repCountLo == repCountHi) {
            // Exact count: state == N
            reachedTargetp = new AstEq{fl, new AstVarRef{fl, stateVarp, VAccess::READ},
                                       new AstConst{fl, repCountLo}};
        } else {
            // Range: state >= N && state <= M
            AstNodeExpr* const geq = new AstGte{fl, new AstVarRef{fl, stateVarp, VAccess::READ},
                                                new AstConst{fl, repCountLo}};
            AstNodeExpr* const leq = new AstLte{fl, new AstVarRef{fl, stateVarp, VAccess::READ},
                                                new AstConst{fl, repCountHi}};
            reachedTargetp = new AstLogAnd{fl, geq, leq};
        }

        // Statements when target reached
        AstAssign* const incCounterp = new AstAssign{
            fl, new AstVarRef{fl, counterVarp, VAccess::WRITE},
            new AstAdd{fl, new AstVarRef{fl, counterVarp, VAccess::READ}, new AstConst{fl, 1}}};
        AstAssign* const setHitp = new AstAssign{
            fl, new AstVarRef{fl, hitVarp, VAccess::WRITE}, new AstConst{fl, AstConst::BitTrue{}}};
        AstAssign* const setStaticHitp = new AstAssign{
            fl, new AstVarRef{fl, staticHitVarp, VAccess::WRITE},
            new AstConst{fl, AstConst::BitTrue{}}};
        AstAssign* const resetStatep = new AstAssign{
            fl, new AstVarRef{fl, stateVarp, VAccess::WRITE}, new AstConst{fl, 0}};

        AstIf* reachedIfp = new AstIf{fl, reachedTargetp, incCounterp, nullptr};
        reachedIfp->addThensp(setHitp);
        reachedIfp->addThensp(setStaticHitp);
        // For exact count, reset immediately; for range, reset only at upper bound
        if (repCountLo == repCountHi) {
            reachedIfp->addThensp(resetStatep);
        }

        if (anyMatchedVarp) {
            AstAssign* const setAnyMatchedp = new AstAssign{
                fl, new AstVarRef{fl, anyMatchedVarp, VAccess::WRITE},
                new AstConst{fl, AstConst::BitTrue{}}};
            reachedIfp->addThensp(setAnyMatchedp);
        }

        matchStmtsp->addNext(reachedIfp);

        // For ranges: reset when exceeding upper bound M (after M matches)
        if (repCountLo != repCountHi) {
            // if (state > M) state = 0;
            AstNodeExpr* const exceedMaxp = new AstGt{
                fl, new AstVarRef{fl, stateVarp, VAccess::READ}, new AstConst{fl, repCountHi}};
            AstIf* const resetMaxIfp = new AstIf{
                fl, exceedMaxp,
                new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE}, new AstConst{fl, 0}},
                nullptr};
            matchStmtsp->addNext(resetMaxIfp);
        }

        // For CONSECUTIVE: also need to reset on mismatch
        AstNode* mismatchStmtsp = nullptr;
        if (repType == VCovRepetitionType::CONSECUTIVE) {
            mismatchStmtsp = new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
                                           new AstConst{fl, 0}};
        }

        // Create the if statement: if (match) { inc; check } else { reset (if consecutive) }
        AstIf* const ifp = new AstIf{fl, matchCondp, matchStmtsp, mismatchStmtsp};
        m_sampleFuncp->addStmtsp(ifp);

        // Track for coverage calculations
        m_hitVars.push_back(hitVarp);
        m_counterVars.push_back(counterVarp);
        m_staticHitVars.push_back(staticHitVarp);
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
    // Process a single value as a bin (used by bin array expansion)
    void processSingleValueBin(AstCoverBin* binp, AstNodeExpr* cpExprp, const string& cpName,
                               const string& indexedBinName, int64_t value,
                               AstNodeExpr* cpIffp = nullptr, AstVar* anyMatchedVarp = nullptr) {
        FileLine* const fl = binp->fileline();

        // Create counter and hit flag variables (instance level)
        const string counterName = makeVarName("__Vcov_cnt_", cpName, indexedBinName);
        const string hitName = makeVarName("__Vcov_hit_", cpName, indexedBinName);
        AstVar* const counterVarp = createCounterVar(fl, counterName);
        AstVar* const hitVarp = createHitVar(fl, hitName);

        // Create static hit flag for type-level coverage (get_coverage())
        AstVar* const staticHitVarp = createStaticHitVar(fl, hitName);

        // Track this bin for coverage
        ++m_binCount;
        m_hitVars.push_back(hitVarp);
        m_staticHitVars.push_back(staticHitVarp);

        // Register bin for cross coverage lookup
        m_cpBinHitVars[cpName].push_back(CovBinInfo{indexedBinName, hitVarp, value, value});

        // Build condition: cpExpr == value
        V3Number valNum{cpExprp, cpExprp->width()};
        valNum.setQuad(value);
        AstNodeExpr* condp = new AstEq{fl, cloneWithTransforms(cpExprp),
                                        new AstConst{fl, valNum}};

        // Apply bin-level iff condition if present
        if (binp->iffp()) {
            condp = new AstLogAnd{fl, cloneWithTransforms(binp->iffp()), condp};
        }

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
        AstAssign* const setHitp = new AstAssign{fl, hitRefW, new AstConst{fl, AstConst::BitTrue{}}};

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
    }

    // Process bin array: bins arr[] = {[lo:hi]} expands to arr[0], arr[1], etc.
    // Returns true if handled as array, false if should be processed normally
    bool processBinArray(AstCoverBin* binp, AstNodeExpr* cpExprp, const string& cpName,
                         AstNodeExpr* cpIffp = nullptr, AstVar* anyMatchedVarp = nullptr) {
        if (!binp->isArray()) return false;

        const string binName = binp->name().empty() ? "bin" + cvtToStr(m_binCount) : binp->name();
        int arrayIndex = 0;

        // Iterate through ranges and expand each value
        for (AstNode* rangep = binp->rangesp(); rangep; rangep = rangep->nextp()) {
            if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                // InsideRange [lo:hi]
                AstConst* const lop = VN_CAST(irp->lhsp(), Const);
                AstConst* const hip = VN_CAST(irp->rhsp(), Const);
                if (lop && hip) {
                    const int64_t lo = lop->num().toSQuad();
                    const int64_t hi = hip->num().toSQuad();
                    for (int64_t v = lo; v <= hi; ++v) {
                        const string indexedName = binName + "[" + cvtToStr(arrayIndex++) + "]";
                        processSingleValueBin(binp, cpExprp, cpName, indexedName, v,
                                              cpIffp, anyMatchedVarp);
                    }
                } else {
                    // Non-constant range, fall back to single bin
                    return false;
                }
            } else if (AstRange* const rp = VN_CAST(rangep, Range)) {
                // Range [lo:hi]
                AstConst* const lop = VN_CAST(rp->leftp(), Const);
                AstConst* const hip = VN_CAST(rp->rightp(), Const);
                if (lop && hip) {
                    const int64_t lo = lop->num().toSQuad();
                    const int64_t hi = hip->num().toSQuad();
                    for (int64_t v = lo; v <= hi; ++v) {
                        const string indexedName = binName + "[" + cvtToStr(arrayIndex++) + "]";
                        processSingleValueBin(binp, cpExprp, cpName, indexedName, v,
                                              cpIffp, anyMatchedVarp);
                    }
                } else {
                    return false;
                }
            } else if (AstConst* const cp = VN_CAST(rangep, Const)) {
                // Single value
                const int64_t v = cp->num().toSQuad();
                const string indexedName = binName + "[" + cvtToStr(arrayIndex++) + "]";
                processSingleValueBin(binp, cpExprp, cpName, indexedName, v,
                                      cpIffp, anyMatchedVarp);
            } else if (AstNodeExpr* const ep = VN_CAST(rangep, NodeExpr)) {
                // Non-constant expression - cannot expand at compile time
                return false;
            }
        }

        return arrayIndex > 0;  // Return true if we created at least one bin
    }

    void processBin(AstCoverBin* binp, AstNodeExpr* cpExprp, const string& cpName,
                    AstNodeExpr* cpIffp = nullptr, AstVar* anyMatchedVarp = nullptr) {
        FileLine* const fl = binp->fileline();
        const string binName = binp->name().empty() ? "bin" + cvtToStr(m_binCount) : binp->name();

        // Skip ignore_bins from coverage calculation
        if (binp->binType().m_e == VCoverBinType::IGNORE_BINS) return;

        // Handle bin arrays: bins arr[] = {[0:3]} expands to arr[0], arr[1], arr[2], arr[3]
        if (processBinArray(binp, cpExprp, cpName, cpIffp, anyMatchedVarp)) return;

        // Check for transition/repetition bins FIRST before creating variables
        // This avoids creating duplicate variables when process*Bin also creates them
        for (AstNode* rangep = binp->rangesp(); rangep; rangep = rangep->nextp()) {
            if (AstCovTransition* const transp = VN_CAST(rangep, CovTransition)) {
                // Transition coverage - process via state machine
                // processTransitionBin creates its own counter/hit/state variables
                if (processTransitionBin(binp, transp, cpExprp, cpName, cpIffp, anyMatchedVarp)) {
                    return;  // Successfully processed transition bin
                }
                // Failed to process, fall through to try regular processing
            } else if (AstCovRepetition* const repp = VN_CAST(rangep, CovRepetition)) {
                // Repetition coverage - process via state counter
                // processRepetitionBin creates its own counter/hit/state variables
                if (processRepetitionBin(binp, repp, cpExprp, cpName, cpIffp, anyMatchedVarp)) {
                    return;  // Successfully processed repetition bin
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
                // Coverage repetition - already processed above, skip
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
            } else if (AstCovTolerance* const tp = VN_CAST(rangep, CovTolerance)) {
                // Tolerance range [value +/- tol] or [value +%- pct]
                rangeCondp = createStepMatch(fl, cloneWithTransforms(cpExprp), tp);
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
            int64_t lo = 0, hi = 0;
            if (AstRange* const rp = VN_CAST(rangep, Range)) {
                // Range [lo:hi] (legacy format)
                if (extractIntValue(rp->leftp(), lo) && extractIntValue(rp->rightp(), hi)) {
                    binInfo.addRange(lo, hi);
                }
            } else if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                // InsideRange [lo:hi] (from value_range in grammar)
                if (extractIntValue(irp->lhsp(), lo) && extractIntValue(irp->rhsp(), hi)) {
                    binInfo.addRange(lo, hi);
                }
            } else if (extractIntValue(rangep, lo)) {
                // Single value (Const or EnumItemRef)
                binInfo.addRange(lo, lo);
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

    // Get effective name for a coverpoint (IEEE 1800-2023 19.5)
    // If coverpoint has no explicit name, use expression name if it's a simple varref
    static string getCpEffectiveName(AstCoverpoint* cpp, int binCount) {
        if (!cpp->name().empty()) return cpp->name();
        // For unlabeled coverpoints, use expression name if it's a simple varref
        if (AstVarRef* const vrp = VN_CAST(cpp->exprp(), VarRef)) {
            return vrp->name();
        }
        return "cp" + cvtToStr(binCount);  // Fall back to auto-generated name
    }

    // Process a coverpoint
    void processCoverpoint(AstCoverpoint* cpp) {
        FileLine* const fl = cpp->fileline();
        const string cpName = getCpEffectiveName(cpp, m_binCount);

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

    // Helper to extract integer value from various node types
    static bool extractIntValue(AstNode* nodep, int64_t& value) {
        if (AstConst* const cp = VN_CAST(nodep, Const)) {
            if (!cp->num().isFourState()) {
                value = cp->num().toSQuad();
                return true;
            }
        } else if (AstEnumItemRef* const eip = VN_CAST(nodep, EnumItemRef)) {
            // Get the enum item's value
            if (eip->itemp() && eip->itemp()->valuep()) {
                if (AstConst* const valcp = VN_CAST(eip->itemp()->valuep(), Const)) {
                    if (!valcp->num().isFourState()) {
                        value = valcp->num().toSQuad();
                        return true;
                    }
                }
            }
        }
        return false;
    }

    // Helper to check if a bin's value ranges overlap with intersect values
    static bool binValuesOverlap(const CovBinInfo& binInfo, AstNode* intersectp) {
        if (!intersectp) return true;  // No intersect means match everything
        if (binInfo.valueRanges.empty()) return true;  // No ranges tracked means unknown, assume match

        // Check each intersect value/range against bin's value ranges
        for (AstNode* rangep = intersectp; rangep; rangep = rangep->nextp()) {
            int64_t intLo = 0, intHi = 0;
            // Try to extract value from single value nodes (Const or EnumItemRef)
            if (extractIntValue(rangep, intLo)) {
                intHi = intLo;
            } else if (AstRange* const rp = VN_CAST(rangep, Range)) {
                if (!extractIntValue(rp->leftp(), intLo)) continue;
                if (!extractIntValue(rp->rightp(), intHi)) continue;
            } else if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                // InsideRange [lo:hi] (from covergroup_value_range in grammar)
                if (!extractIntValue(irp->lhsp(), intLo)) continue;
                if (!extractIntValue(irp->rhsp(), intHi)) continue;
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

    // Helper to check if any bin value satisfies a comparison expression
    // withExpr is expected to be a comparison like: cp > 5, item == 3, etc.
    // cpName is the coverpoint name being referenced
    // Returns true if any value in the bin's ranges satisfies the expression
    static bool binValuesSatisfyWithExpr(const CovBinInfo& binInfo, AstNodeExpr* withExpr,
                                         const string& cpName) {
        if (!withExpr) return true;
        if (binInfo.valueRanges.empty()) return true;  // No ranges tracked, assume match

        // Try to extract a simple comparison: varref <op> const or const <op> varref
        int64_t constVal = 0;
        bool constOnRight = false;
        bool foundComparison = false;
        enum CompareOp { OP_EQ, OP_NE, OP_LT, OP_GT, OP_LE, OP_GE };
        CompareOp op = OP_EQ;

        // Check for different comparison types
        if (AstEq* const eqp = VN_CAST(withExpr, Eq)) {
            op = OP_EQ;
            if (AstConst* const cp = VN_CAST(eqp->rhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = true;
                foundComparison = true;
            } else if (AstConst* const cp = VN_CAST(eqp->lhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = false;
                foundComparison = true;
            }
        } else if (AstNeq* const neqp = VN_CAST(withExpr, Neq)) {
            op = OP_NE;
            if (AstConst* const cp = VN_CAST(neqp->rhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = true;
                foundComparison = true;
            } else if (AstConst* const cp = VN_CAST(neqp->lhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = false;
                foundComparison = true;
            }
        } else if (AstLt* const ltp = VN_CAST(withExpr, Lt)) {
            if (AstConst* const cp = VN_CAST(ltp->rhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = true;
                op = OP_LT;  // var < const
                foundComparison = true;
            } else if (AstConst* const cp = VN_CAST(ltp->lhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = false;
                op = OP_GT;  // const < var means var > const
                foundComparison = true;
            }
        } else if (AstGt* const gtp = VN_CAST(withExpr, Gt)) {
            if (AstConst* const cp = VN_CAST(gtp->rhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = true;
                op = OP_GT;  // var > const
                foundComparison = true;
            } else if (AstConst* const cp = VN_CAST(gtp->lhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = false;
                op = OP_LT;  // const > var means var < const
                foundComparison = true;
            }
        } else if (AstLte* const ltep = VN_CAST(withExpr, Lte)) {
            if (AstConst* const cp = VN_CAST(ltep->rhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = true;
                op = OP_LE;  // var <= const
                foundComparison = true;
            } else if (AstConst* const cp = VN_CAST(ltep->lhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = false;
                op = OP_GE;  // const <= var means var >= const
                foundComparison = true;
            }
        } else if (AstGte* const gtep = VN_CAST(withExpr, Gte)) {
            if (AstConst* const cp = VN_CAST(gtep->rhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = true;
                op = OP_GE;  // var >= const
                foundComparison = true;
            } else if (AstConst* const cp = VN_CAST(gtep->lhsp(), Const)) {
                constVal = cp->num().toSQuad();
                constOnRight = false;
                op = OP_LE;  // const >= var means var <= const
                foundComparison = true;
            }
        }

        if (!foundComparison) {
            // Complex expression we can't evaluate at compile time - assume match
            return true;
        }

        // Check if any value in the bin's ranges satisfies the comparison
        for (const auto& range : binInfo.valueRanges) {
            int64_t lo = range.first;
            int64_t hi = range.second;

            // For each value in [lo, hi], check if it satisfies the comparison
            // For efficiency, we check range endpoints and boundaries
            bool satisfies = false;
            switch (op) {
            case OP_EQ:
                // constVal must be within [lo, hi]
                satisfies = (constVal >= lo && constVal <= hi);
                break;
            case OP_NE:
                // Any value != constVal exists in [lo, hi] if range has more than one value
                // or if constVal is outside the range
                satisfies = (lo < hi) || (lo != constVal);
                break;
            case OP_LT:
                // Any value < constVal exists if lo < constVal
                satisfies = (lo < constVal);
                break;
            case OP_GT:
                // Any value > constVal exists if hi > constVal
                satisfies = (hi > constVal);
                break;
            case OP_LE:
                // Any value <= constVal exists if lo <= constVal
                satisfies = (lo <= constVal);
                break;
            case OP_GE:
                // Any value >= constVal exists if hi >= constVal
                satisfies = (hi >= constVal);
                break;
            }

            if (satisfies) return true;
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

                    // Check if there's a with clause
                    if (binsofp->withp()) {
                        // binsof(cp) with (expr) - check if bin values satisfy the expression
                        bool satisfies
                            = binValuesSatisfyWithExpr(currentBin, binsofp->withp(), cpName);
                        return binsofp->negate() ? !satisfies : satisfies;
                    }

                    // No intersect or with clause
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

        // Check cross_auto_bin_max limit (0 = unlimited)
        if (m_options.crossAutoBinMax > 0
            && totalCrossBins > static_cast<size_t>(m_options.crossAutoBinMax)) {
            xp->v3warn(COVERIGN, "Cross coverage '" << crossName << "' has " << totalCrossBins
                                                    << " bins, exceeds cross_auto_bin_max ("
                                                    << m_options.crossAutoBinMax
                                                    << "); skipping auto bin generation");
            return;
        }

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

        // Calculate: min((sum / binCount) * 100.0 * (100.0 / goal), 100.0)
        // For goal < 100, scale up so hitting 'goal' percent gives 100%
        // Convert to real: real'(sum) / real'(binCount) * 100.0 * (100.0 / goal)
        const int totalBins = static_cast<int>(m_hitVars.size());
        const int goal = m_options.goal;

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
        AstNodeExpr* rawPercentp = new AstMulD{fl, dividep, hundredp};

        // Apply option.goal scaling: (raw_percent / goal) * 100.0
        // If goal < 100, this scales up so hitting 'goal' percent gives 100%
        if (goal != 100 && goal > 0) {
            V3Number goalNum{funcp, V3Number::Double{}, static_cast<double>(goal)};
            AstConst* const goalp = new AstConst{fl, goalNum};
            rawPercentp = new AstDivD{fl, rawPercentp, goalp};
            AstConst* const hundred2p = new AstConst{fl, hundredNum};
            rawPercentp = new AstMulD{fl, rawPercentp, hundred2p};

            // Cap at 100.0%: (rawPercent > 100.0) ? 100.0 : rawPercent
            V3Number hundredCap{funcp, V3Number::Double{}, 100.0};
            AstConst* const cap1p = new AstConst{fl, hundredCap};
            AstConst* const cap2p = new AstConst{fl, hundredCap};
            AstNodeExpr* const gtCondp = new AstGtD{fl, rawPercentp, cap1p};
            rawPercentp = new AstCond{fl, gtCondp, cap2p, rawPercentp->cloneTree(false)};
        }

        return rawPercentp;
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

        // Calculate: min((sum / binCount) * 100.0 * (100.0 / goal), 100.0)
        // For goal < 100, scale up so hitting 'goal' percent gives 100%
        const int totalBins = static_cast<int>(m_staticHitVars.size());
        const int goal = m_options.goal;

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
        AstNodeExpr* rawPercentp = new AstMulD{fl, dividep, hundredp};

        // Apply option.goal scaling: (raw_percent / goal) * 100.0
        // If goal < 100, this scales up so hitting 'goal' percent gives 100%
        if (goal != 100 && goal > 0) {
            V3Number goalNum{funcp, V3Number::Double{}, static_cast<double>(goal)};
            AstConst* const goalp = new AstConst{fl, goalNum};
            rawPercentp = new AstDivD{fl, rawPercentp, goalp};
            AstConst* const hundred2p = new AstConst{fl, hundredNum};
            rawPercentp = new AstMulD{fl, rawPercentp, hundred2p};

            // Cap at 100.0%: (rawPercent > 100.0) ? 100.0 : rawPercent
            V3Number hundredCap{funcp, V3Number::Double{}, 100.0};
            AstConst* const cap1p = new AstConst{fl, hundredCap};
            AstConst* const cap2p = new AstConst{fl, hundredCap};
            AstNodeExpr* const gtCondp = new AstGtD{fl, rawPercentp, cap1p};
            rawPercentp = new AstCond{fl, gtCondp, cap2p, rawPercentp->cloneTree(false)};
        }

        return rawPercentp;
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

    // Generate per-coverpoint coverage function
    // Returns coverage percentage for a single coverpoint's bins
    AstNodeExpr* generateCpCoverageExpr(FileLine* fl, AstFunc* funcp,
                                        const std::vector<CovBinInfo>& binInfos) {
        if (binInfos.empty()) {
            V3Number zeroNum{funcp, V3Number::Double{}, 0.0};
            return new AstConst{fl, zeroNum};
        }

        // Build expression: sum of hit flags for this coverpoint's bins
        AstNodeExpr* sumExprp = nullptr;
        for (const CovBinInfo& binInfo : binInfos) {
            AstVarRef* const hitRefp = new AstVarRef{fl, binInfo.hitVar, VAccess::READ};
            AstNodeExpr* const extendedp = new AstExtend{fl, hitRefp, 32};
            if (sumExprp) {
                sumExprp = new AstAdd{fl, sumExprp, extendedp};
            } else {
                sumExprp = extendedp;
            }
        }

        // Calculate: (sum / binCount) * 100.0
        const int totalBins = static_cast<int>(binInfos.size());

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
        AstNodeExpr* percentp = new AstMulD{fl, dividep, hundredp};

        return percentp;
    }

    // Generate per-coverpoint member variables and coverage functions
    // Creates a VlCoverpointRef<cgclass> member for each named coverpoint
    void generateCoverpointMembers(AstFunc* constructorFuncp) {
        if (!m_classp || m_cpBinHitVars.empty()) return;

        FileLine* const fl = m_classp->fileline();

        // Find all coverpoint names
        // Skip only truly auto-generated names (cp0, cp1, etc.) that came from anonymous coverpoints
        // Names derived from expression (like 'a', 'b') should be kept
        for (const auto& cpPair : m_cpBinHitVars) {
            const string& cpName = cpPair.first;
            const std::vector<CovBinInfo>& binInfos = cpPair.second;

            // 1. Create per-coverpoint coverage function
            const string funcName = "__Vcp_" + cpName + "_get_inst_coverage";

            UINFO(4, "Looking for placeholder function: " << funcName << " for coverpoint "
                                                          << cpName << " with " << binInfos.size()
                                                          << " bins" << endl);

            // Check if function already exists (created by V3Width as placeholder)
            // V3Width creates placeholder when user accesses coverpoint like cg.cp.get_coverage()
            AstFunc* cpFuncp = nullptr;
            for (AstNode* memberp = m_classp->membersp(); memberp; memberp = memberp->nextp()) {
                if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                    UINFO(9, "  Checking member function: " << funcp->name() << endl);
                    if (funcp->name() == funcName) {
                        cpFuncp = funcp;
                        UINFO(4, "  Found existing placeholder function" << endl);
                        break;
                    }
                }
            }

            // Only generate function body if a placeholder was created by V3Width
            // (meaning the user actually accessed this coverpoint's coverage method)
            if (!cpFuncp) {
                UINFO(4, "  No placeholder found, skipping coverpoint " << cpName << endl);
                continue;
            }

            // Generate coverage expression for this coverpoint
            AstNodeExpr* const coverageExprp = generateCpCoverageExpr(fl, cpFuncp, binInfos);

            // Assign to return variable - find the return variable in the function
            UINFO(4, "  cpFuncp->fvarp() = " << (cpFuncp->fvarp() ? "exists" : "nullptr") << endl);
            UASSERT_OBJ(cpFuncp->fvarp(), cpFuncp, "Coverpoint function missing fvarp");
            AstVar* funcRetp = VN_AS(cpFuncp->fvarp(), Var);
            AstVarRef* const retRefp = new AstVarRef{fl, funcRetp, VAccess::WRITE};
            AstAssign* const assignp = new AstAssign{fl, retRefp, coverageExprp};
            cpFuncp->addStmtsp(assignp);

            // Note: We don't create a VlCoverpointRef member variable here because:
            // 1. V3Width transforms cg.cp.get_inst_coverage() directly to cg.__Vcp_cp_get_inst_coverage()
            // 2. Creating a member variable would require knowing the mangled C++ class name
            //    which is not available at this stage
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
        m_constructorArgs.clear();
        m_enclosingClassp = nullptr;
        m_parentPtrVarp = nullptr;

        // Extract coverage options from the covergroup
        m_options = extractOptions(nodep);

        // Find sample(), get_coverage(), get_inst_coverage(), and new() functions
        AstFunc* newFuncp = nullptr;
        for (AstNode* memberp = nodep->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                if (funcp->name() == "sample") {
                    m_sampleFuncp = funcp;
                } else if (funcp->name() == "get_coverage") {
                    m_getCoverageFuncp = funcp;
                } else if (funcp->name() == "get_inst_coverage") {
                    m_getInstCoverageFuncp = funcp;
                } else if (funcp->name() == "new") {
                    newFuncp = funcp;
                }
            }
        }

        if (!m_sampleFuncp) {
            nodep->v3warn(E_UNSUPPORTED, "Covergroup missing sample() function");
            return;
        }

        // Build map of class member names to their AstVar nodes
        std::map<string, AstVar*> memberVars;
        for (AstNode* memberp = nodep->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstVar* const varp = VN_CAST(memberp, Var)) {
                if (varp->varType() == VVarType::MEMBER) {
                    memberVars[varp->name()] = varp;
                }
            }
        }

        // Extract constructor arguments and map to class members
        // Constructor args are cloned as class members in the parser (verilog.y)
        if (newFuncp) {
            for (AstNode* stmtp = newFuncp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->direction().isAny() && varp->isFuncLocal()) {
                        // This is a constructor argument - find matching class member
                        auto it = memberVars.find(varp->name());
                        if (it != memberVars.end()) {
                            m_constructorArgs[varp->name()] = it->second;
                            UINFO(4, "Found constructor arg: " << varp->name()
                                                               << " -> member" << endl);
                        }
                    }
                }
            }
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
                    // Multiple enclosing classes detected.
                    // For extended covergroups, check if one class inherits from the other.
                    // If so, use the derived class as the enclosing class.
                    bool resolved = false;
                    if (nodep->isExtended()) {
                        // Check if enclosingp is a base of m_enclosingClassp
                        for (AstClassExtends* extp = m_enclosingClassp->extendsp(); extp;
                             extp = VN_AS(extp->nextp(), ClassExtends)) {
                            if (extp->classp() == enclosingp) {
                                // enclosingp is a base, keep m_enclosingClassp (the derived)
                                UINFO(4, "Extended covergroup: keeping derived class "
                                             << m_enclosingClassp->name() << " (base: "
                                             << enclosingp->name() << ")" << endl);
                                resolved = true;
                                break;
                            }
                        }
                        // Check if m_enclosingClassp is a base of enclosingp
                        if (!resolved) {
                            for (AstClassExtends* extp = enclosingp->extendsp(); extp;
                                 extp = VN_AS(extp->nextp(), ClassExtends)) {
                                if (extp->classp() == m_enclosingClassp) {
                                    // m_enclosingClassp is a base, use enclosingp (the derived)
                                    UINFO(4, "Extended covergroup: using derived class "
                                                 << enclosingp->name() << " (base: "
                                                 << m_enclosingClassp->name() << ")" << endl);
                                    m_enclosingClassp = enclosingp;
                                    resolved = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (!resolved) {
                        UINFO(4, "Covergroup references multiple unrelated enclosing classes: "
                                     << m_enclosingClassp->name() << " and " << enclosingp->name()
                                     << endl);
                        multipleEnclosingClasses = true;
                        m_enclosingClassp = nullptr;
                        break;
                    }
                } else {
                    m_enclosingClassp = enclosingp;
                }
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

        // Generate per-coverpoint members for coverpoint member access (cg.cp.get_inst_coverage())
        generateCoverpointMembers(newFuncp);

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
            if (nodep->isExtended()) {
                // For extended covergroups, we need to add the instantiation code
                // since there's no explicit g1 = new() in the derived class
                instantiateExtendedCovergroup(nodep);
            } else {
                // For regular covergroups, find existing new() and add __Vparentp init
                initializeParentPtr(nodep);
            }
        }

        // Handle covergroup clocking event (automatic sampling)
        if (AstSenItem* const clockEventp = nodep->coverClockEventp()) {
            // Check if sample() has arguments (beyond the return value)
            bool hasSampleArgs = !m_sampleArgs.empty();
            if (hasSampleArgs) {
                // Cannot auto-sample when sample() has arguments
                clockEventp->v3warn(COVERIGN,
                                    "Covergroup clocking event with sample() arguments not "
                                    "supported; call sample() manually");
            } else {
                // Generate automatic sampling:
                // fork forever @(clock_event) this.sample(); join_none
                generateAutoSampling(nodep, clockEventp);
            }
            // Remove the clocking event from the class to prevent issues in later passes
            clockEventp->unlinkFrBack();
            VL_DO_DANGLING(clockEventp->deleteTree(), clockEventp);
            nodep->coverClockEventp(nullptr);
        }

        m_classp = nullptr;
    }

    // Generate automatic sampling code in the constructor
    // Adds: fork forever @(clock_event) sample(); join_none
    void generateAutoSampling(AstClass* covergroupp, AstSenItem* clockEventp) {
        UINFO(4, "Generating automatic sampling for covergroup " << covergroupp->name() << endl);

        // Find the constructor function
        AstFunc* constructorFuncp = nullptr;
        for (AstNode* memberp = covergroupp->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                if (funcp->isConstructor()) {
                    constructorFuncp = funcp;
                    break;
                }
            }
        }

        if (!constructorFuncp) {
            clockEventp->v3warn(COVERIGN, "Covergroup missing constructor for automatic sampling");
            return;
        }

        FileLine* const fl = clockEventp->fileline();

        // Create: this.sample()
        // First, create 'this' reference
        AstClassRefDType* const thisTypep
            = new AstClassRefDType{fl, covergroupp, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(thisTypep);
        AstNodeExpr* const thisp = new AstThisRef{fl, thisTypep};

        // Create method call: this.sample()
        // m_sampleFuncp should already be set from earlier processing
        if (!m_sampleFuncp) {
            clockEventp->v3warn(COVERIGN,
                                "Covergroup missing sample() function for automatic sampling");
            return;
        }
        AstMethodCall* const sampleCallp
            = new AstMethodCall{fl, thisp, "sample", nullptr};
        sampleCallp->taskp(m_sampleFuncp);  // Link to actual sample() function
        sampleCallp->dtypep(covergroupp->findVoidDType());

        // Wrap method call in statement context
        AstStmtExpr* const sampleStmtp = new AstStmtExpr{fl, sampleCallp};

        // Create event control: @(clock_event) sample();
        // Clone the clock event and create a SenTree
        AstSenItem* const clonedEventp = clockEventp->cloneTree(false);
        AstSenTree* const sentreep = new AstSenTree{fl, clonedEventp};
        AstEventControl* const eventCtrlp = new AstEventControl{fl, sentreep, sampleStmtp};

        // Create forever loop: forever @(clock_event) sample();
        AstLoop* const foreverp = new AstLoop{fl, eventCtrlp};

        // Create a begin block for the fork branch
        AstBegin* const forkBranchp = new AstBegin{fl, "", foreverp, false};

        // Create fork...join_none with the forever loop
        AstFork* const forkp = new AstFork{fl, VJoinType::JOIN_NONE, ""};
        forkp->addForksp(forkBranchp);

        // Add the fork statement to the end of the constructor
        constructorFuncp->addStmtsp(forkp);

        UINFO(4, "Added automatic sampling fork to constructor" << endl);
    }

    // Instantiate extended covergroup in the enclosing class constructor
    // For extended covergroups, there's no explicit g1 = new() in user code,
    // so we need to add it: this.g1 = new(); this.g1.__Vparentp = this;
    void instantiateExtendedCovergroup(AstClass* covergroupp) {
        if (!m_enclosingClassp) {
            UINFO(4, "No enclosing class for extended covergroup instantiation" << endl);
            return;
        }

        UINFO(4, "Instantiating extended covergroup " << covergroupp->name()
                                                      << " in " << m_enclosingClassp->name()
                                                      << endl);

        // Find the member variable in enclosing class that holds this covergroup
        AstVar* cgMemberVarp = nullptr;
        for (AstNode* memberp = m_enclosingClassp->membersp(); memberp;
             memberp = memberp->nextp()) {
            if (AstVar* const varp = VN_CAST(memberp, Var)) {
                // Check if this variable's type is the covergroup
                if (AstClassRefDType* const refp = VN_CAST(varp->dtypep(), ClassRefDType)) {
                    if (refp->classp() == covergroupp) {
                        cgMemberVarp = varp;
                        UINFO(4,
                              "Found extended covergroup member var: " << varp->name() << endl);
                        break;
                    }
                }
            }
        }

        if (!cgMemberVarp) {
            UINFO(4, "Could not find extended covergroup member variable" << endl);
            return;
        }

        // Find the enclosing class's constructor
        AstFunc* constructorFuncp = nullptr;
        for (AstNode* memberp = m_enclosingClassp->membersp(); memberp;
             memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                if (funcp->isConstructor()) {
                    constructorFuncp = funcp;
                    break;
                }
            }
        }

        if (!constructorFuncp) {
            UINFO(4, "Could not find enclosing class constructor" << endl);
            return;
        }

        FileLine* const fl = covergroupp->fileline();

        // Create: this.g1 = new();
        // LHS: this.g1
        AstClassRefDType* const thisTypep
            = new AstClassRefDType{fl, m_enclosingClassp, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(thisTypep);
        AstThisRef* const thisp = new AstThisRef{fl, thisTypep};
        AstMemberSel* const lhsp = new AstMemberSel{fl, thisp, cgMemberVarp};

        // RHS: new()
        AstClassRefDType* const cgTypep = new AstClassRefDType{fl, covergroupp, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(cgTypep);

        // Find the covergroup's constructor
        AstFunc* cgConstructorFuncp = nullptr;
        for (AstNode* memberp = covergroupp->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                if (funcp->isConstructor()) {
                    cgConstructorFuncp = funcp;
                    break;
                }
            }
        }

        AstNew* const newp = new AstNew{fl, nullptr};
        newp->dtypep(cgTypep);
        newp->classOrPackagep(covergroupp);
        if (cgConstructorFuncp) newp->taskp(cgConstructorFuncp);

        // Create assignment: this.g1 = new();
        AstAssign* const assignp = new AstAssign{fl, lhsp, newp};

        // Add to constructor - after any super.new() call
        // Find the last statement (or super call) and add after it
        AstNode* lastStmtp = nullptr;
        for (AstNode* stmtp = constructorFuncp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            // Skip variable declarations
            if (!VN_IS(stmtp, Var)) {
                lastStmtp = stmtp;
            }
        }

        if (lastStmtp) {
            lastStmtp->addNextHere(assignp);
        } else {
            constructorFuncp->addStmtsp(assignp);
        }

        UINFO(4, "Added extended covergroup instantiation: " << assignp << endl);

        // Now add __Vparentp initialization
        if (m_parentPtrVarp) {
            // Create: this.g1.__Vparentp
            AstClassRefDType* const thisTypep2 = thisTypep->cloneTree(false);
            v3Global.rootp()->typeTablep()->addTypesp(thisTypep2);
            AstThisRef* const thisp2 = new AstThisRef{fl, thisTypep2};
            AstMemberSel* const cgRefp = new AstMemberSel{fl, thisp2, cgMemberVarp};
            AstMemberSel* const parentPtrp = new AstMemberSel{fl, cgRefp, m_parentPtrVarp};

            // Create: this
            AstClassRefDType* const thisTypep3 = thisTypep->cloneTree(false);
            v3Global.rootp()->typeTablep()->addTypesp(thisTypep3);
            AstThisRef* const thisp3 = new AstThisRef{fl, thisTypep3};

            // Create assignment: this.g1.__Vparentp = this;
            AstAssign* const initp = new AstAssign{fl, parentPtrp, thisp3};

            // Add after the new() assignment
            assignp->addNextHere(initp);

            UINFO(4, "Added __Vparentp initialization: " << initp << endl);
        }
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
