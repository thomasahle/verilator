// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  Pre steps:
//      Attach clocks to each assertion
//      Substitute property references by property body (IEEE 1800-2012 16.12.1).
//      Transform clocking blocks into imperative logic
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertPre.h"

#include "V3Const.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Assert class functions

class AssertPreVisitor final : public VNVisitor {
    // Removes clocks and other pre-optimizations
    // Eventually inlines calls to sequences, properties, etc.
    // We're not parsing the tree, or anything more complicated.
private:
    // NODE STATE
    // AstClockingItem::user1p()         // AstVar*.      varp() of ClockingItem after unlink
    const VNUser1InUse m_inuser1;
    // STATE
    // Current context:
    AstNetlist* const m_netlistp = nullptr;  // Current netlist
    AstNodeModule* m_modp = nullptr;  // Current module
    AstClocking* m_clockingp = nullptr;  // Current clocking block
    // Reset each module:
    AstClocking* m_defaultClockingp = nullptr;  // Default clocking for current module
    AstDefaultDisable* m_defaultDisablep = nullptr;  // Default disable for current module
    // Reset each assertion:
    AstSenItem* m_senip = nullptr;  // Last sensitivity
    // Reset each always:
    AstSenItem* m_seniAlwaysp = nullptr;  // Last sensitivity in always
    // Reset each assertion:
    AstNodeExpr* m_disablep = nullptr;  // Last disable
    // Other:
    V3UniqueNames m_cycleDlyNames{"__VcycleDly"};  // Cycle delay counter name generator
    V3UniqueNames m_propVarNames{"__Vprop"};  // Property local variable name generator
    bool m_inAssign = false;  // True if in an AssignNode
    bool m_inAssignDlyLhs = false;  // True if in AssignDly's LHS
    bool m_inSynchDrive = false;  // True if in synchronous drive
    std::vector<AstVarXRef*> m_xrefsp;  // list of xrefs that need name fixup
    bool m_inPExpr = false;  // True if in AstPExpr

    // METHODS

    AstSenTree* newSenTree(AstNode* nodep, AstSenTree* useTreep = nullptr) {
        // Create sentree based on clocked or default clock
        // Return nullptr for always
        if (useTreep) return useTreep;
        AstSenTree* newp = nullptr;
        AstSenItem* senip = m_senip;
        if (!senip && m_defaultClockingp) senip = m_defaultClockingp->sensesp();
        if (!senip) senip = m_seniAlwaysp;
        if (!senip) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Unclocked assertion");
            newp = new AstSenTree{nodep->fileline(), nullptr};
        } else {
            newp = new AstSenTree{nodep->fileline(), senip->cloneTree(true)};
        }
        return newp;
    }
    AstPropSpec* getPropertyExprp(const AstProperty* const propp) {
        // The only statements possible in AstProperty are AstPropSpec (body)
        // and AstVar (arguments).
        AstNode* propExprp = propp->stmtsp();
        while (VN_IS(propExprp, Var)) propExprp = propExprp->nextp();
        return VN_CAST(propExprp, PropSpec);
    }
    AstPropSpec* substitutePropertyCall(AstPropSpec* nodep) {
        if (AstFuncRef* const funcrefp = VN_CAST(nodep->propp(), FuncRef)) {
            if (const AstProperty* const propp = VN_CAST(funcrefp->taskp(), Property)) {
                AstPropSpec* propExprp = getPropertyExprp(propp);
                // Substitute inner property call before copying in order to not doing the same for
                // each call of outer property call.
                propExprp = substitutePropertyCall(propExprp);
                // Clone property local variables (non-IO vars) into module scope
                std::unordered_map<const AstVar*, AstVar*> localVarMap;
                for (AstNode* stmtp = propp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (VN_IS(stmtp, PropSpec)) break;
                    AstVar* const varp = VN_CAST(stmtp, Var);
                    if (!varp || varp->isIO()) continue;
                    UASSERT_OBJ(m_modp, varp, "Property local var outside module");
                    AstVar* const newvarp = varp->cloneTree(false);
                    newvarp->funcLocal(false);
                    newvarp->name(m_propVarNames.get(varp->name()));
                    m_modp->addStmtsp(newvarp);
                    localVarMap.emplace(varp, newvarp);
                }
                // Clone subtree after substitution. It is needed, because property might be called
                // multiple times with different arguments.
                propExprp = propExprp->cloneTree(false);
                // Substitute formal arguments with actual arguments
                const V3TaskConnects tconnects = V3Task::taskConnects(funcrefp, propp->stmtsp());
                for (const auto& tconnect : tconnects) {
                    const AstVar* const portp = tconnect.first;
                    // cppcheck-suppress constVariablePointer // 'exprp' unlinked below
                    AstArg* const argp = tconnect.second;
                    propExprp->foreach([&](AstVarRef* refp) {
                        if (refp->varp() == portp) {
                            refp->replaceWith(argp->exprp()->cloneTree(false));
                            VL_DO_DANGLING(pushDeletep(refp), refp);
                        }
                    });
                    pushDeletep(argp->exprp()->unlinkFrBack());
                }
                if (!localVarMap.empty()) {
                    propExprp->foreach([&](AstVarRef* refp) {
                        const auto it = localVarMap.find(refp->varp());
                        if (it != localVarMap.end()) refp->varp(it->second);
                    });
                }
                // Handle case with 2 disable iff statement (IEEE 1800-2023 16.12.1)
                if (nodep->disablep() && propExprp->disablep()) {
                    nodep->v3error("disable iff expression before property call and in its "
                                   "body is not legal");
                    pushDeletep(propExprp->disablep()->unlinkFrBack());
                }
                // If disable iff is in outer property, move it to inner
                if (nodep->disablep()) {
                    AstNodeExpr* const disablep = nodep->disablep()->unlinkFrBack();
                    propExprp->disablep(disablep);
                }

                if (nodep->sensesp() && propExprp->sensesp()) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Clock event before property call and in its body");
                    pushDeletep(propExprp->sensesp()->unlinkFrBack());
                }
                // If clock event is in outer property, move it to inner
                if (nodep->sensesp()) {
                    AstSenItem* const sensesp = nodep->sensesp();
                    sensesp->unlinkFrBack();
                    propExprp->sensesp(sensesp);
                }

                // Substitute any property calls introduced by argument replacement
                propExprp = substitutePropertyCall(propExprp);

                // Now substitute property reference with property body
                if (!nodep->backp()) {
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return propExprp;
                }
                nodep->replaceWith(propExprp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return propExprp;
            }
        }
        return nodep;
    }

    // VISITORS
    //========== Statements
    void visit(AstClocking* const nodep) override {
        VL_RESTORER(m_clockingp);
        m_clockingp = nodep;
        UINFO(8, "   CLOCKING" << nodep);
        iterateChildren(nodep);
        if (nodep->eventp()) nodep->addNextHere(nodep->eventp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstModportClockingRef* const nodep) override {
        // It has to be converted to a list of ModportClockingVarRefs,
        // because clocking blocks are removed in this pass
        for (AstNode* itemp = nodep->clockingp()->itemsp(); itemp; itemp = itemp->nextp()) {
            if (AstClockingItem* citemp = VN_CAST(itemp, ClockingItem)) {
                if (AstVar* const varp
                    = citemp->varp() ? citemp->varp() : VN_AS(citemp->user1p(), Var)) {
                    AstModportVarRef* const modVarp = new AstModportVarRef{
                        nodep->fileline(), varp->name(), citemp->direction()};
                    modVarp->varp(varp);
                    nodep->addNextHere(modVarp);
                }
            }
        }
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstClockingItem* const nodep) override {
        // Get a ref to the sampled/driven variable
        AstVar* const varp = nodep->varp();
        if (!varp) {
            // Unused item
            return;
        }
        FileLine* const flp = nodep->fileline();
        V3Const::constifyEdit(nodep->skewp());
        if (!VN_IS(nodep->skewp(), Const)) {
            nodep->skewp()->v3error("Skew must be constant (IEEE 1800-2023 14.4)");
            return;
        }
        AstConst* const skewp = VN_AS(nodep->skewp(), Const);
        if (skewp->num().isNegative()) skewp->v3error("Skew cannot be negative");
        AstNodeExpr* const exprp = nodep->exprp();
        varp->name(m_clockingp->name() + "__DOT__" + varp->name());
        m_clockingp->addNextHere(varp->unlinkFrBack());
        nodep->user1p(varp);
        varp->user1p(nodep);
        if (nodep->direction() == VDirection::OUTPUT) {
            exprp->foreach([](const AstNodeVarRef* varrefp) {
                // Prevent confusing BLKANDNBLK warnings on clockvars due to generated assignments
                varrefp->fileline()->warnOff(V3ErrorCode::BLKANDNBLK, true);
            });
            AstVarRef* const skewedReadRefp = new AstVarRef{flp, varp, VAccess::READ};
            skewedReadRefp->user1(true);
            // Initialize the clockvar
            AstVarRef* const skewedWriteRefp = new AstVarRef{flp, varp, VAccess::WRITE};
            skewedWriteRefp->user1(true);
            AstInitialStatic* const initClockvarp = new AstInitialStatic{
                flp, new AstAssign{flp, skewedWriteRefp, exprp->cloneTreePure(false)}};
            m_modp->addStmtsp(initClockvarp);
            // A var to keep the previous value of the clockvar
            AstVar* const prevVarp = new AstVar{
                flp, VVarType::MODULETEMP, "__Vclocking_prev__" + varp->name(), exprp->dtypep()};
            prevVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            AstInitialStatic* const initPrevClockvarp = new AstInitialStatic{
                flp, new AstAssign{flp, new AstVarRef{flp, prevVarp, VAccess::WRITE},
                                   skewedReadRefp->cloneTreePure(false)}};
            m_modp->addStmtsp(prevVarp);
            m_modp->addStmtsp(initPrevClockvarp);
            // Assign the clockvar to the actual var; only do it if the clockvar's value has
            // changed
            AstAssign* const assignp
                = new AstAssign{flp, exprp->cloneTreePure(false), skewedReadRefp};
            AstIf* const ifp
                = new AstIf{flp,
                            new AstNeq{flp, new AstVarRef{flp, prevVarp, VAccess::READ},
                                       skewedReadRefp->cloneTreePure(false)},
                            assignp};
            ifp->addThensp(new AstAssign{flp, new AstVarRef{flp, prevVarp, VAccess::WRITE},
                                         skewedReadRefp->cloneTree(false)});
            if (skewp->isZero()) {
                // Drive the var in Re-NBA (IEEE 1800-2023 14.16)
                AstSenTree* senTreep
                    = new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)};
                senTreep->addSensesp(
                    new AstSenItem{flp, VEdgeType::ET_CHANGED, skewedReadRefp->cloneTree(false)});
                AstCMethodHard* const trigp = new AstCMethodHard{
                    nodep->fileline(),
                    new AstVarRef{flp, m_clockingp->ensureEventp(), VAccess::READ},
                    VCMethod::EVENT_IS_TRIGGERED};
                trigp->dtypeSetBit();
                ifp->condp(new AstLogAnd{flp, ifp->condp()->unlinkFrBack(), trigp});
                m_clockingp->addNextHere(new AstAlwaysReactive{flp, senTreep, ifp});
            } else if (skewp->fileline()->timingOn()) {
                // Create a fork so that this AlwaysObserved can be retriggered before the
                // assignment happens. Also then it can be combo, avoiding the need for creating
                // new triggers.
                AstFork* const forkp = new AstFork{flp, VJoinType::JOIN_NONE};
                forkp->addForksp(new AstBegin{flp, "", ifp, true});
                // Use Observed for this to make sure we do not miss the event
                m_clockingp->addNextHere(new AstAlwaysObserved{
                    flp, new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, forkp});
                if (v3Global.opt.timing().isSetTrue()) {
                    AstDelay* const delayp = new AstDelay{flp, skewp->unlinkFrBack(), false};
                    delayp->timeunit(m_modp->timeunit());
                    assignp->timingControlp(delayp);
                } else if (v3Global.opt.timing().isSetFalse()) {
                    nodep->v3warn(E_NOTIMING,
                                  "Clocking output skew greater than #0 requires --timing");
                } else {
                    nodep->v3warn(E_NEEDTIMINGOPT,
                                  "Use --timing or --no-timing to specify how "
                                  "clocking output skew greater than #0 should be handled");
                }
            }
        } else if (nodep->direction() == VDirection::INPUT) {
            // Ref to the clockvar
            AstVarRef* const refp = new AstVarRef{flp, varp, VAccess::WRITE};
            refp->user1(true);
            if (skewp->num().is1Step()) {
                // #1step means the value that is sampled is always the signal's last value
                // before the clock edge (IEEE 1800-2023 14.4)
                AstSampled* const sampledp = new AstSampled{flp, exprp->cloneTreePure(false)};
                sampledp->dtypeFrom(exprp);
                AstAssign* const assignp = new AstAssign{flp, refp, sampledp};
                m_clockingp->addNextHere(new AstAlways{
                    flp, VAlwaysKwd::ALWAYS,
                    new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, assignp});
            } else if (skewp->isZero()) {
                // #0 means the var has to be sampled in Observed (IEEE 1800-2023 14.13)
                AstAssign* const assignp = new AstAssign{flp, refp, exprp->cloneTreePure(false)};
                m_clockingp->addNextHere(new AstAlwaysObserved{
                    flp, new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, assignp});
            } else {
                // Create a queue where we'll store sampled values with timestamps
                AstSampleQueueDType* const queueDtp
                    = new AstSampleQueueDType{flp, exprp->dtypep()};
                m_netlistp->typeTablep()->addTypesp(queueDtp);
                AstVar* const queueVarp
                    = new AstVar{flp, VVarType::MODULETEMP, "__Vqueue__" + varp->name(), queueDtp};
                queueVarp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_clockingp->addNextHere(queueVarp);
                // Create a process like this:
                //     always queue.push(<sampled var>);
                AstCMethodHard* const pushp = new AstCMethodHard{
                    flp, new AstVarRef{flp, queueVarp, VAccess::WRITE}, VCMethod::DYN_PUSH,
                    new AstTime{nodep->fileline(), m_modp->timeunit()}};
                pushp->addPinsp(exprp->cloneTreePure(false));
                pushp->dtypeSetVoid();
                m_clockingp->addNextHere(
                    new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, pushp->makeStmt()});
                // Create a process like this:
                //     always @<clocking event> queue.pop(<skew>, /*out*/<skewed var>);
                AstCMethodHard* const popp = new AstCMethodHard{
                    flp, new AstVarRef{flp, queueVarp, VAccess::READWRITE}, VCMethod::DYN_POP,
                    new AstTime{nodep->fileline(), m_modp->timeunit()}};
                popp->addPinsp(skewp->unlinkFrBack());
                popp->addPinsp(refp);
                popp->dtypeSetVoid();
                m_clockingp->addNextHere(
                    new AstAlways{flp, VAlwaysKwd::ALWAYS,
                                  new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)},
                                  popp->makeStmt()});
            }
        } else {
            nodep->v3fatalSrc("Invalid direction");
        }
    }
    void visit(AstDelay* nodep) override {
        // Only cycle delays are relevant in this stage; also only process once
        if (!nodep->isCycleDelay()) {
            if (m_inSynchDrive) {
                nodep->v3error("Only cycle delays can be used in synchronous drives"
                               " (IEEE 1800-2023 14.16)");
            }
            iterateChildren(nodep);
            return;
        }
        if (m_inAssign && !m_inSynchDrive) {
            nodep->v3error("Cycle delays not allowed as intra-assignment delays"
                           " (IEEE 1800-2023 14.11)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        if (nodep->stmtsp()) nodep->addNextHere(nodep->stmtsp()->unlinkFrBackWithNext());
        FileLine* const flp = nodep->fileline();

        // Get min delay value
        AstNodeExpr* minValuep = V3Const::constifyEdit(nodep->lhsp()->unlinkFrBack());
        const AstConst* const minConstp = VN_CAST(minValuep, Const);
        if (!minConstp) {
            nodep->v3error(
                "Delay value is not an elaboration-time constant (IEEE 1800-2023 16.7)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            VL_DO_DANGLING(minValuep->deleteTree(), minValuep);
            return;
        }

        // Check for range delay ##[min:max] or ##[min:$]
        const bool isRange = nodep->isRangeDelay();
        uint32_t minVal = minConstp->toUInt();
        uint32_t maxVal = minVal;  // Default: fixed delay
        bool isUnbounded = false;  // True for ##[n:$]

        if (isRange) {
            AstNodeExpr* maxValuep = nodep->rhsp()->unlinkFrBack();
            // Check for unbounded range (##[n:$])
            // After width resolution, AstUnbounded may be wrapped in AstExtend
            const AstNodeExpr* checkp = maxValuep;
            if (const AstExtend* const extp = VN_CAST(maxValuep, Extend)) {
                checkp = extp->lhsp();
            }
            if (VN_IS(checkp, Unbounded)) {
                isUnbounded = true;
                maxVal = UINT32_MAX;  // Use max value to indicate unbounded
                VL_DO_DANGLING(maxValuep->deleteTree(), maxValuep);
            } else {
                maxValuep = V3Const::constifyEdit(maxValuep);
                const AstConst* const maxConstp = VN_CAST(maxValuep, Const);
                if (!maxConstp) {
                    nodep->v3error(
                        "Range delay max is not an elaboration-time constant (IEEE 1800-2023 16.7)");
                    VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                    VL_DO_DANGLING(minValuep->deleteTree(), minValuep);
                    VL_DO_DANGLING(maxValuep->deleteTree(), maxValuep);
                    return;
                }
                maxVal = maxConstp->toUInt();
                VL_DO_DANGLING(maxValuep->deleteTree(), maxValuep);

                if (minVal > maxVal) {
                    nodep->v3error("Range delay min (" + std::to_string(minVal)
                                   + ") > max (" + std::to_string(maxVal) + ")");
                    VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                    VL_DO_DANGLING(minValuep->deleteTree(), minValuep);
                    return;
                }
            }
        }

        if (minVal == 0 && maxVal == 0) {
            // ##0 means no delay - just execute the following statements immediately
            // Statements were already moved to siblings, so just delete the delay
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            VL_DO_DANGLING(minValuep->deleteTree(), minValuep);
            return;
        }

        AstSenItem* sensesp = nullptr;
        if (!m_defaultClockingp) {
            if (!m_inPExpr) {
                nodep->v3error("Usage of cycle delays requires default clocking"
                               " (IEEE 1800-2023 14.11)");
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                VL_DO_DANGLING(minValuep->deleteTree(), minValuep);
                return;
            }
            sensesp = m_senip;
            if (!sensesp) {
                nodep->v3error("Cycle delay requires property clocking event"
                               " (IEEE 1800-2023 16.7)");
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                VL_DO_DANGLING(minValuep->deleteTree(), minValuep);
                return;
            }
        } else {
            sensesp = m_defaultClockingp->sensesp();
        }

        const std::string delayName = m_cycleDlyNames.get(nodep);
        AstVar* const cntVarp = new AstVar{flp, VVarType::BLOCKTEMP, delayName + "__counter",
                                           nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        cntVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        AstBegin* const beginp = new AstBegin{flp, delayName + "__block", cntVarp, true};
        beginp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE}, minValuep});

        // Wait for min cycles
        {
            AstEventControl* const controlp = new AstEventControl{
                flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr};
            AstLoop* const loopp = new AstLoop{flp};
            loopp->addStmtsp(new AstLoopTest{
                flp, loopp,
                new AstGt{flp, new AstVarRef{flp, cntVarp, VAccess::READ}, new AstConst{flp, 0}}});
            loopp->addStmtsp(controlp);
            loopp->addStmtsp(
                new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                              new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                         new AstConst{flp, 1}}});
            beginp->addStmtsp(loopp);
        }

        // For range delays, we need to check the following expression at each cycle
        // in the range [min, max]. The following expression is in the next sibling.
        // For unbounded (##[n:$]), we keep checking until the condition is met.
        if ((isRange && maxVal > minVal) || isUnbounded) {
            // Get the next sibling (should be an AstIf checking the sequence expression)
            AstNode* const nextp = nodep->nextp();
            if (nextp && VN_IS(nextp, If)) {
                AstIf* const checkIfp = VN_AS(nextp, If);

                // Create matched flag
                AstVar* const matchedVarp = new AstVar{
                    flp, VVarType::BLOCKTEMP, delayName + "__matched",
                    nodep->findBasicDType(VBasicDTypeKwd::BIT)};
                matchedVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                beginp->addStmtsp(matchedVarp);
                beginp->addStmtsp(new AstAssign{
                    flp, new AstVarRef{flp, matchedVarp, VAccess::WRITE},
                    new AstConst{flp, AstConst::BitFalse{}}});

                // For bounded ranges, create attempts counter
                // For ##[min:max], we have (max - min + 1) chances to match
                AstVar* attemptsVarp = nullptr;
                if (!isUnbounded) {
                    const uint32_t numAttempts = maxVal - minVal + 1;
                    attemptsVarp = new AstVar{
                        flp, VVarType::BLOCKTEMP, delayName + "__attempts",
                        nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
                    attemptsVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                    beginp->addStmtsp(attemptsVarp);
                    beginp->addStmtsp(new AstAssign{
                        flp, new AstVarRef{flp, attemptsVarp, VAccess::WRITE},
                        new AstConst{flp, numAttempts}});
                }

                // Unlink the check from its current position
                checkIfp->unlinkFrBack();

                // Create the retry loop structure
                AstLoop* const tryLoop = new AstLoop{flp};

                // Loop test: continue while not matched
                // For bounded delays, also check that attempts > 0 (haven't exhausted all tries)
                AstNodeExpr* loopCondp
                    = new AstNot{flp, new AstVarRef{flp, matchedVarp, VAccess::READ}};
                if (!isUnbounded) {
                    // For bounded: !matched && attempts > 0
                    // attempts starts at (maxVal - minVal + 1), decremented each failed attempt
                    loopCondp = new AstAnd{
                        flp, loopCondp,
                        new AstGt{flp, new AstVarRef{flp, attemptsVarp, VAccess::READ},
                                  new AstConst{flp, 0}}};
                }
                tryLoop->addStmtsp(new AstLoopTest{flp, tryLoop, loopCondp});

                // Clone the condition for checking
                AstNodeExpr* const condp = checkIfp->condp()->cloneTreePure(false);

                AstNode* retryStmts = nullptr;
                if (isUnbounded) {
                    // For unbounded: just wait one cycle (keep trying forever)
                    retryStmts = new AstEventControl{
                        flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr};
                } else {
                    // For bounded: decrement attempts and wait one cycle if attempts > 1
                    // (attempts == 1 means this is our last chance, no need to wait)
                    AstAssign* const decrement = new AstAssign{
                        flp, new AstVarRef{flp, attemptsVarp, VAccess::WRITE},
                        new AstSub{flp, new AstVarRef{flp, attemptsVarp, VAccess::READ},
                                   new AstConst{flp, 1}}};
                    AstEventControl* const retryControl = new AstEventControl{
                        flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr};
                    // Wait only if we have more attempts after decrement
                    AstIf* const waitIf = new AstIf{
                        flp,
                        new AstGt{flp, new AstVarRef{flp, attemptsVarp, VAccess::READ},
                                  new AstConst{flp, 0}},
                        retryControl};
                    decrement->addNextHere(waitIf);
                    retryStmts = decrement;
                }

                // Success case: condition true - set matched flag
                // Else branch: retry (unbounded) or retry if attempts > 0 (bounded)
                AstIf* const successIf = new AstIf{
                    flp, condp,
                    new AstAssign{flp, new AstVarRef{flp, matchedVarp, VAccess::WRITE},
                                  new AstConst{flp, AstConst::BitTrue{}}},
                    retryStmts};

                tryLoop->addStmtsp(successIf);
                beginp->addStmtsp(tryLoop);

                // After loop: if matched, execute success path; else execute fail path
                AstNode* const thenp = checkIfp->thensp()
                                           ? checkIfp->thensp()->cloneTree(true)
                                           : nullptr;
                AstNode* const elsep = checkIfp->elsesp()
                                           ? checkIfp->elsesp()->cloneTree(true)
                                           : nullptr;
                AstIf* const resultIf = new AstIf{
                    flp, new AstVarRef{flp, matchedVarp, VAccess::READ},
                    thenp, elsep};
                beginp->addStmtsp(resultIf);

                // Delete the original check (we've cloned what we need)
                VL_DO_DANGLING(checkIfp->deleteTree(), checkIfp);
            }
        }

        nodep->replaceWith(beginp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstSenTree* nodep) override {
        if (m_inSynchDrive) {
            nodep->v3error("Event controls cannot be used in "
                           "synchronous drives (IEEE 1800-2023 14.16)");
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        UINFO(8, " -varref:  " << nodep);
        UINFO(8, " -varref-var-back:  " << nodep->varp()->backp());
        UINFO(8, " -varref-var-user1:  " << nodep->varp()->user1p());
        if (AstClockingItem* const itemp = VN_CAST(
                nodep->varp()->user1p() ? nodep->varp()->user1p() : nodep->varp()->firstAbovep(),
                ClockingItem)) {
            if (nodep->user1()) return;

            // ensure linking still works, this has to be done only once
            if (AstVarXRef* xrefp = VN_CAST(nodep, VarXRef)) {
                UINFO(8, " -clockvarxref-in:  " << xrefp);
                string dotted = xrefp->dotted();
                const size_t dotPos = dotted.rfind('.');
                dotted.erase(dotPos, string::npos);
                xrefp->dotted(dotted);
                UINFO(8, " -clockvarxref-out: " << xrefp);
                m_xrefsp.emplace_back(xrefp);
            }

            if (nodep->access().isReadOrRW() && itemp->direction() == VDirection::OUTPUT) {
                nodep->v3error("Cannot read from output clockvar (IEEE 1800-2023 14.3)");
            }
            if (nodep->access().isWriteOrRW()) {
                if (itemp->direction() == VDirection::OUTPUT) {
                    if (!m_inAssignDlyLhs) {
                        nodep->v3error("Only non-blocking assignments can write "
                                       "to clockvars (IEEE 1800-2023 14.16)");
                    }
                    if (m_inAssign) m_inSynchDrive = true;
                } else if (itemp->direction() == VDirection::INPUT) {
                    nodep->v3error("Cannot write to input clockvar (IEEE 1800-2023 14.3)");
                }
            }
            nodep->user1(true);
        }
    }
    void visit(AstMemberSel* nodep) override {
        if (AstClockingItem* const itemp = VN_CAST(
                nodep->varp()->user1p() ? nodep->varp()->user1p() : nodep->varp()->firstAbovep(),
                ClockingItem)) {
            if (nodep->access().isReadOrRW() && itemp->direction() == VDirection::OUTPUT) {
                nodep->v3error("Cannot read from output clockvar (IEEE 1800-2023 14.3)");
            }
            if (nodep->access().isWriteOrRW()) {
                if (itemp->direction() == VDirection::OUTPUT) {
                    if (!m_inAssignDlyLhs) {
                        nodep->v3error("Only non-blocking assignments can write "
                                       "to clockvars (IEEE 1800-2023 14.16)");
                    }
                    if (m_inAssign) m_inSynchDrive = true;
                } else if (itemp->direction() == VDirection::INPUT) {
                    nodep->v3error("Cannot write to input clockvar (IEEE 1800-2023 14.3)");
                }
            }
        }
    }
    void visit(AstNodeAssign* nodep) override {
        if (nodep->user1()) return;
        VL_RESTORER(m_inAssign);
        VL_RESTORER(m_inSynchDrive);
        m_inAssign = true;
        m_inSynchDrive = false;
        {
            VL_RESTORER(m_inAssignDlyLhs);
            m_inAssignDlyLhs = VN_IS(nodep, AssignDly);
            iterate(nodep->lhsp());
        }
        iterate(nodep->rhsp());
        if (nodep->timingControlp()) {
            iterate(nodep->timingControlp());
        } else if (m_inSynchDrive) {
            AstAssign* const assignp = new AstAssign{
                nodep->fileline(), nodep->lhsp()->unlinkFrBack(), nodep->rhsp()->unlinkFrBack()};
            assignp->user1(true);
            nodep->replaceWith(assignp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void visit(AstAlways* nodep) override {
        iterateAndNextNull(nodep->sentreep());
        if (nodep->sentreep()) m_seniAlwaysp = nodep->sentreep()->sensesp();
        iterateAndNextNull(nodep->stmtsp());
        m_seniAlwaysp = nullptr;
    }

    void visit(AstNodeCoverOrAssert* nodep) override {
        if (nodep->sentreep()) return;  // Already processed

        VL_RESTORER(m_senip);
        VL_RESTORER(m_disablep);
        m_senip = nullptr;
        m_disablep = nullptr;

        // Find Clocking's buried under nodep->exprsp
        iterateChildren(nodep);
        // EXPECT without clocking event behaves like immediate assertion (IEEE 1800-2017 16.17)
        const bool expectNoClk = nodep->type() == VAssertType::EXPECT && !m_senip
                                 && !m_defaultClockingp && !m_seniAlwaysp;
        if (!nodep->immediate() && !expectNoClk) nodep->sentreep(newSenTree(nodep));
    }
    void visit(AstFalling* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstNodeExpr* const futurep = new AstFuture{fl, exprp, newSenTree(nodep)};
        futurep->dtypeFrom(exprp);
        exprp = new AstAnd{fl, exprp->cloneTreePure(false), new AstNot{fl, futurep}};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstFell* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstPast* const pastp = new AstPast{fl, exprp};
        pastp->dtypeFrom(exprp);
        pastp->sentreep(newSenTree(nodep, sentreep));
        exprp = new AstAnd{fl, pastp, new AstNot{fl, exprp->cloneTreePure(false)}};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstFuture* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        AstSenTree* const sentreep = nodep->sentreep();
        if (sentreep) VL_DO_DANGLING(pushDeletep(sentreep->unlinkFrBack()), sentreep);
        nodep->sentreep(newSenTree(nodep));
    }
    void visit(AstPast* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        nodep->sentreep(newSenTree(nodep));
    }
    void visit(AstRising* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstNodeExpr* const futurep = new AstFuture{fl, exprp, newSenTree(nodep)};
        futurep->dtypeFrom(exprp);
        exprp = new AstAnd{fl, new AstNot{fl, exprp->cloneTreePure(false)}, futurep};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstRose* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstPast* const pastp = new AstPast{fl, exprp};
        pastp->dtypeFrom(exprp);
        pastp->sentreep(newSenTree(nodep, sentreep));
        exprp = new AstAnd{fl, new AstNot{fl, pastp}, exprp->cloneTreePure(false)};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstStable* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstPast* const pastp = new AstPast{fl, exprp};
        pastp->dtypeFrom(exprp);
        pastp->sentreep(newSenTree(nodep, sentreep));
        exprp = new AstEq{fl, pastp, exprp->cloneTreePure(false)};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstSteady* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstNodeExpr* const futurep = new AstFuture{fl, exprp, newSenTree(nodep)};
        futurep->dtypeFrom(exprp);
        exprp = new AstEq{fl, exprp->cloneTreePure(false), futurep};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstImplication* nodep) override {
        if (nodep->sentreep()) return;  // Already processed

        iterateChildren(nodep);

        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* lhsp = nodep->lhsp()->unlinkFrBack();
        if (nodep->isOverlapped()) {
            nodep->replaceWith(new AstLogOr{flp, new AstLogNot{flp, lhsp}, rhsp});
        } else {
            if (m_disablep) {
                lhsp = new AstAnd{flp, new AstNot{flp, m_disablep->cloneTreePure(false)}, lhsp};
            }

            AstPast* const pastp = new AstPast{flp, lhsp};
            pastp->dtypeFrom(lhsp);
            pastp->sentreep(newSenTree(nodep));
            AstNodeExpr* const exprp = new AstOr{flp, new AstNot{flp, pastp}, rhsp};
            exprp->dtypeSetBit();
            nodep->replaceWith(exprp);
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstDefaultDisable* nodep) override {
        // Done with these
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstInferredDisable* nodep) override {
        AstNode* newp;
        if (m_defaultDisablep) {
            newp = m_defaultDisablep->condp()->cloneTreePure(true);
        } else {
            newp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstPropSpec* nodep) override {
        nodep = substitutePropertyCall(nodep);
        iterateAndNextNull(nodep->sensesp());
        if (m_senip && m_senip != nodep->sensesp())
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Only one PSL clock allowed per assertion");
        if (!nodep->disablep() && m_defaultDisablep) {
            nodep->disablep(m_defaultDisablep->condp()->cloneTreePure(true));
        }
        m_disablep = nodep->disablep();
        // Unlink and just keep a pointer to it, convert to sentree as needed
        m_senip = nodep->sensesp();
        iterateNull(nodep->disablep());
        if (VN_AS(nodep->backp(), NodeCoverOrAssert)->type() == VAssertType::CONCURRENT) {
            const AstNodeDType* const propDtp = nodep->propp()->dtypep();
            nodep->propp(new AstSampled{nodep->fileline(), nodep->propp()->unlinkFrBack()});
            nodep->propp()->dtypeFrom(propDtp);
        }
        iterate(nodep->propp());
    }
    void visit(AstPExpr* nodep) override {
        VL_RESTORER(m_inPExpr);
        m_inPExpr = true;

        if (AstLogNot* const notp = VN_CAST(nodep->backp(), LogNot)) {
            notp->replaceWith(nodep->unlinkFrBack());
            VL_DO_DANGLING(pushDeletep(notp), notp);
            iterate(nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    void visit(AstSExprClocked* nodep) override {
        // Clocked sequence expression: @(event) sexpr
        // Set m_senip so cycle delays within can use this clock
        // Also set m_inPExpr so cycle delay handler knows we're in a valid context
        VL_RESTORER(m_senip);
        VL_RESTORER(m_inPExpr);
        m_senip = nodep->sensesp();
        m_inPExpr = true;  // Clocked sequence acts like a property expression for delays
        iterateChildren(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_defaultClockingp);
        VL_RESTORER(m_defaultDisablep);
        VL_RESTORER(m_modp);
        m_defaultClockingp = nullptr;
        nodep->foreach([&](AstClocking* const clockingp) {
            if (clockingp->isDefault()) {
                if (m_defaultClockingp) {
                    clockingp->v3error("Only one default clocking block allowed per module"
                                       " (IEEE 1800-2023 14.12)");
                }
                m_defaultClockingp = clockingp;
            }
        });
        m_defaultDisablep = nullptr;
        nodep->foreach([&](AstDefaultDisable* const disablep) {
            if (m_defaultDisablep) {
                disablep->v3error("Only one 'default disable iff' allowed per module"
                                  " (IEEE 1800-2023 16.15)");
            }
            m_defaultDisablep = disablep;
        });
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstProperty* nodep) override {
        // The body will be visited when will be substituted in place of property reference
        // (AstFuncRef)
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstSequence* nodep) override {
        // Sequence bodies are already substituted/inlined by V3LinkResolve.
        // Delete the original to prevent visiting cycle delays without proper context.
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AssertPreVisitor(AstNetlist* nodep)
        : m_netlistp{nodep} {
        // Process
        iterate(nodep);
        // Fix up varref names
        for (AstVarXRef* xrefp : m_xrefsp) xrefp->name(xrefp->varp()->name());
    }
    ~AssertPreVisitor() override = default;
};

//######################################################################
// Top Assert class

void V3AssertPre::assertPreAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { AssertPreVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assertpre", 0, dumpTreeEitherLevel() >= 3);
}
