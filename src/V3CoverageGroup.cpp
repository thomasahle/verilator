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

    // List of static hit flags for get_coverage() (type level)
    std::vector<AstVar*> m_staticHitVars;

    // Cross coverage support: map coverpoint name -> list of (bin name, hit var)
    std::map<string, std::vector<std::pair<string, AstVar*>>> m_cpBinHitVars;

    // Sample arg support: map arg name -> function argument AstVar
    std::map<string, AstVar*> m_sampleArgs;

    // Enclosing class support (for class-embedded covergroups)
    AstClass* m_enclosingClassp = nullptr;  // Enclosing class if covergroup is class-embedded
    AstVar* m_parentPtrVarp = nullptr;  // __Vparentp member variable

    // METHODS
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
    void processBin(AstCoverBin* binp, AstNodeExpr* cpExprp, const string& cpName) {
        FileLine* const fl = binp->fileline();
        const string binName = binp->name().empty() ? "bin" + cvtToStr(m_binCount) : binp->name();

        // Skip ignore_bins from coverage calculation
        if (binp->binType().m_e == VCoverBinType::IGNORE_BINS) return;

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

            if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
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
                rangeCondp = new AstEq{fl, cloneWithTransforms(cpExprp), cp->cloneTree(false)};
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

        // Apply iff condition if present
        if (binp->iffp()) {
            condp = new AstLogAnd{fl, binp->iffp()->cloneTree(false), condp};
        }

        // For illegal_bins, generate error when hit
        if (binp->binType().m_e == VCoverBinType::ILLEGAL_BINS) {
            // if (condp) { $display("Error: illegal bin hit"); $stop; }
            AstDisplay* const displayp
                = new AstDisplay{fl, VDisplayType::DT_ERROR,
                                 "Illegal bin '" + binName + "' hit in coverpoint '" + cpName + "'",
                                 nullptr, nullptr};
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
        m_sampleFuncp->addStmtsp(ifp);

        // Track for get_inst_coverage()
        m_hitVars.push_back(hitVarp);

        // Track for get_coverage() (static)
        m_staticHitVars.push_back(staticHitVarp);

        // Track for cross coverage (map coverpoint name -> bin name + hit var)
        m_cpBinHitVars[cpName].push_back({binName, hitVarp});

        ++m_binCount;
    }

    // Process a coverpoint
    void processCoverpoint(AstCoverpoint* cpp) {
        FileLine* const fl = cpp->fileline();
        const string cpName = cpp->name().empty() ? "cp" + cvtToStr(m_binCount) : cpp->name();

        // Get the expression being covered
        AstNodeExpr* const exprp = cpp->exprp();
        if (!exprp) return;

        // Apply coverpoint iff condition to sample
        AstNodeExpr* cpIffp = cpp->iffp() ? cpp->iffp()->cloneTree(false) : nullptr;

        // Process each bin
        for (AstNode* nodep = cpp->binsp(); nodep; nodep = nodep->nextp()) {
            if (AstCoverBin* const binp = VN_CAST(nodep, CoverBin)) {
                // If coverpoint has iff, wrap bin processing
                if (cpIffp) {
                    // We'll apply the iff condition to each bin
                    // For now, handled in processBin by checking cpp->iffp()
                }
                processBin(binp, exprp, cpName);
            }
        }
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

        // For now, only support 2-way crosses (most common case)
        if (cpNames.size() > 2) {
            xp->v3warn(E_UNSUPPORTED,
                       "Cross coverage with more than 2 coverpoints not yet supported");
            return;
        }

        // Look up bin hit vars for each coverpoint
        const string& cp1Name = cpNames[0];
        const string& cp2Name = cpNames[1];

        auto it1 = m_cpBinHitVars.find(cp1Name);
        auto it2 = m_cpBinHitVars.find(cp2Name);

        if (it1 == m_cpBinHitVars.end()) {
            xp->v3warn(E_UNSUPPORTED,
                       "Cross coverage references unknown coverpoint '" << cp1Name << "'");
            return;
        }
        if (it2 == m_cpBinHitVars.end()) {
            xp->v3warn(E_UNSUPPORTED,
                       "Cross coverage references unknown coverpoint '" << cp2Name << "'");
            return;
        }

        const auto& cp1Bins = it1->second;
        const auto& cp2Bins = it2->second;

        UINFO(4, "Processing cross " << crossName << " of " << cp1Name << " (" << cp1Bins.size()
                                     << " bins) x " << cp2Name << " (" << cp2Bins.size()
                                     << " bins)" << endl);

        // Generate cross product bins
        for (const auto& bin1 : cp1Bins) {
            const string& bin1Name = bin1.first;
            AstVar* hit1Varp = bin1.second;
            for (const auto& bin2 : cp2Bins) {
                const string& bin2Name = bin2.first;
                AstVar* hit2Varp = bin2.second;
                // Create cross bin hit flag
                const string crossBinName = crossName + "_" + bin1Name + "_" + bin2Name;
                AstVar* const crossHitVarp
                    = createHitVar(fl, makeVarName("__Vcov_hit_", crossBinName, ""));

                // Track for coverage calculation
                m_hitVars.push_back(crossHitVarp);
                ++m_binCount;

                // Generate: if (hit1 && hit2) crossHit = 1;
                AstVarRef* const hit1Refp = new AstVarRef{fl, hit1Varp, VAccess::READ};
                AstVarRef* const hit2Refp = new AstVarRef{fl, hit2Varp, VAccess::READ};
                AstNodeExpr* const condp = new AstLogAnd{fl, hit1Refp, hit2Refp};

                // Apply iff condition if present
                AstNodeExpr* finalCondp = condp;
                if (xp->iffp()) {
                    finalCondp = new AstLogAnd{fl, xp->iffp()->cloneTree(false), condp};
                }

                AstVarRef* const crossHitRefW = new AstVarRef{fl, crossHitVarp, VAccess::WRITE};
                AstAssign* const setHitp
                    = new AstAssign{fl, crossHitRefW, new AstConst{fl, AstConst::BitTrue{}}};

                AstIf* const ifp = new AstIf{fl, finalCondp, setHitp, nullptr};
                m_sampleFuncp->addStmtsp(ifp);
            }
        }
    }

    // Generate coverage percentage calculation expression
    AstNodeExpr* generateCoverageExpr(FileLine* fl, AstFunc* funcp) {
        if (m_hitVars.empty()) {
            // No bins, return 0.0
            V3Number zeroNum{funcp, V3Number::Double{}, 0.0};
            return new AstConst{fl, zeroNum};
        }

        // Build expression: (hit1 + hit2 + ... + hitN)
        AstNodeExpr* sumExprp = nullptr;
        for (AstVar* hitVarp : m_hitVars) {
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
    AstNodeExpr* generateStaticCoverageExpr(FileLine* fl, AstFunc* funcp) {
        if (m_staticHitVars.empty()) {
            // No bins, return 0.0
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
        m_staticHitVars.clear();
        m_cpBinHitVars.clear();
        m_sampleArgs.clear();
        m_enclosingClassp = nullptr;
        m_parentPtrVarp = nullptr;

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

        // Initialize __Vparentp in the enclosing class if we have enclosing class references
        if (m_enclosingClassp && m_parentPtrVarp) {
            initializeParentPtr(nodep);
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

//######################################################################
// CoverageGroup class functions

void V3CoverageGroup::coverageGroup(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { CoverageGroupVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coveragegroup", 0, dumpTreeEitherLevel() >= 3);
}
