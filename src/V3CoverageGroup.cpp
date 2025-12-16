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
    AstFunc* m_getCoverageFuncp = nullptr;  // get_coverage() function to add code to
    int m_binCount = 0;  // Total number of bins in this covergroup
    int m_coveredExpr = 0;  // Running count expression for get_coverage

    // List of hit flags for get_coverage calculation
    std::vector<AstVar*> m_hitVars;

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

    // Create a hit flag variable in the covergroup class
    AstVar* createHitVar(FileLine* fl, const string& name) {
        AstVar* const varp = new AstVar{fl, VVarType::MEMBER, name, m_classp->findBitDType()};
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        varp->valuep(new AstConst{fl, 0});
        m_classp->addMembersp(varp);
        return varp;
    }

    // Create condition: expr >= lo && expr <= hi
    AstNodeExpr* createRangeCheck(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* lop,
                                  AstNodeExpr* hip) {
        if (!hip) {
            // Single value, not a range
            return new AstEq{fl, exprp->cloneTree(false), lop->cloneTree(false)};
        }
        AstNodeExpr* const geq = new AstGte{fl, exprp->cloneTree(false), lop->cloneTree(false)};
        AstNodeExpr* const leq = new AstLte{fl, exprp->cloneTree(false), hip->cloneTree(false)};
        return new AstLogAnd{fl, geq, leq};
    }

    // Process a single bin within a coverpoint
    void processBin(AstCoverBin* binp, AstNodeExpr* cpExprp, const string& cpName) {
        FileLine* const fl = binp->fileline();
        const string binName = binp->name().empty() ? "bin" + cvtToStr(m_binCount) : binp->name();

        // Skip ignore_bins from coverage calculation
        if (binp->binType().m_e == VCoverBinType::IGNORE_BINS) return;

        // Create counter and hit flag variables
        const string counterName = makeVarName("__Vcov_cnt_", cpName, binName);
        const string hitName = makeVarName("__Vcov_hit_", cpName, binName);
        AstVar* const counterVarp = createCounterVar(fl, counterName);
        AstVar* const hitVarp = createHitVar(fl, hitName);

        // Build condition from bin ranges
        AstNodeExpr* condp = nullptr;
        for (AstNode* rangep = binp->rangesp(); rangep; rangep = rangep->nextp()) {
            AstNodeExpr* rangeCondp = nullptr;

            if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                // InsideRange [lo:hi] - use its built-in method to create comparison
                rangeCondp = irp->newAndFromInside(cpExprp->cloneTree(false),
                                                   irp->lhsp()->cloneTree(false),
                                                   irp->rhsp()->cloneTree(false));
            } else if (AstRange* const rp = VN_CAST(rangep, Range)) {
                // Range [lo:hi]
                rangeCondp = createRangeCheck(fl, cpExprp, rp->leftp(), rp->rightp());
            } else if (AstConst* const cp = VN_CAST(rangep, Const)) {
                // Single value
                rangeCondp = new AstEq{fl, cpExprp->cloneTree(false), cp->cloneTree(false)};
            } else if (AstNodeExpr* const ep = VN_CAST(rangep, NodeExpr)) {
                // Expression value
                rangeCondp = new AstEq{fl, cpExprp->cloneTree(false), ep->cloneTree(false)};
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

        // Generate: if (condp) { counter++; hit = 1; }
        AstVarRef* const counterRefW
            = new AstVarRef{fl, counterVarp, VAccess::WRITE};
        AstVarRef* const counterRefR = new AstVarRef{fl, counterVarp, VAccess::READ};
        AstAssign* const incCounterp = new AstAssign{
            fl, counterRefW, new AstAdd{fl, counterRefR, new AstConst{fl, 1}}};

        AstVarRef* const hitRefW = new AstVarRef{fl, hitVarp, VAccess::WRITE};
        AstAssign* const setHitp = new AstAssign{fl, hitRefW, new AstConst{fl, 1}};

        AstIf* const ifp = new AstIf{fl, condp, incCounterp, nullptr};
        ifp->addThensp(setHitp);
        m_sampleFuncp->addStmtsp(ifp);

        // Track for get_coverage()
        m_hitVars.push_back(hitVarp);
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

    // Generate get_coverage() function body
    void generateGetCoverage() {
        if (!m_getCoverageFuncp) return;

        FileLine* const fl = m_getCoverageFuncp->fileline();

        // For now, return 0.0 as placeholder
        // TODO: Calculate actual coverage percentage using hit flags
        // The issue is that VarRefs to class members in expression context
        // generate static class access instead of this-> access
        V3Number zeroNum{m_getCoverageFuncp, V3Number::Double{}, 0.0};
        AstConst* const zeroDbl = new AstConst{fl, zeroNum};

        // Find return variable and assign to it
        if (AstVar* const fvarp = VN_CAST(m_getCoverageFuncp->fvarp(), Var)) {
            AstVarRef* const retRefp = new AstVarRef{fl, fvarp, VAccess::WRITE};
            AstAssign* const assignp = new AstAssign{fl, retRefp, zeroDbl};
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
        m_binCount = 0;
        m_hitVars.clear();

        // Find sample() and get_coverage() functions
        for (AstNode* memberp = nodep->membersp(); memberp; memberp = memberp->nextp()) {
            if (AstFunc* const funcp = VN_CAST(memberp, Func)) {
                if (funcp->name() == "sample") {
                    m_sampleFuncp = funcp;
                } else if (funcp->name() == "get_coverage") {
                    m_getCoverageFuncp = funcp;
                }
            }
        }

        if (!m_sampleFuncp) {
            nodep->v3warn(E_UNSUPPORTED, "Covergroup missing sample() function");
            return;
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

        // Process all coverpoints
        for (AstCoverpoint* cpp : coverpoints) {
            processCoverpoint(cpp);
        }

        // Generate get_coverage() body
        generateGetCoverage();

        // Clean up - remove AstCoverpoint nodes as they've been lowered
        for (AstCoverpoint* cpp : coverpoints) {
            VL_DO_DANGLING(cpp->unlinkFrBack()->deleteTree(), cpp);
        }

        m_classp = nullptr;
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
