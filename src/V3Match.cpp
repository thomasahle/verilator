// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Pattern match binding support
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Match.h"

#include "V3Global.h"
#include "V3MemberMap.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

//======================================================================
// &&& rewriting

class CondAndRewriteVisitor final : public VNVisitor {
    void splitCondAnd(AstNodeExpr* exprp, std::vector<AstNodeExpr*>& condsp) {
        if (!exprp) return;
        if (AstLogAnd* const andp = VN_CAST(exprp, LogAnd)) {
            if (andp->isCondAnd()) {
                AstNodeExpr* const lhsp = andp->lhsp()->unlinkFrBack();
                AstNodeExpr* const rhsp = andp->rhsp()->unlinkFrBack();
                VL_DO_DANGLING(pushDeletep(andp), andp);
                splitCondAnd(lhsp, condsp);
                splitCondAnd(rhsp, condsp);
                return;
            }
        }
        condsp.push_back(exprp);
    }

    void visit(AstIf* nodep) override {
        AstLogAnd* const andp = VN_CAST(nodep->condp(), LogAnd);
        if (andp && andp->isCondAnd()) {
            std::vector<AstNodeExpr*> condsp;
            AstNodeExpr* const rootp = nodep->condp()->unlinkFrBack();
            splitCondAnd(rootp, condsp);
            if (condsp.size() <= 1) {
                if (!condsp.empty()) nodep->condp(condsp.front());
                return;
            } else {
                AstNode* const thenp
                    = nodep->thensp() ? nodep->thensp()->unlinkFrBackWithNext() : nullptr;
                AstNode* const elsep
                    = nodep->elsesp() ? nodep->elsesp()->unlinkFrBackWithNext() : nullptr;
                AstNode* chainp = thenp;
                for (size_t i = condsp.size(); i-- > 0;) {
                    AstNode* const elseHere
                        = elsep ? (i == 0 ? elsep : elsep->cloneTree(true)) : nullptr;
                    AstIf* const ifp = new AstIf{nodep->fileline(), condsp[i], chainp, elseHere};
                    if (i == 0) {
                        if (nodep->uniquePragma()) ifp->uniquePragma(true);
                        if (nodep->unique0Pragma()) ifp->unique0Pragma(true);
                        if (nodep->priorityPragma()) ifp->priorityPragma(true);
                    }
                    chainp = ifp;
                }
                nodep->replaceWith(chainp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                iterateChildren(chainp);
                return;
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit CondAndRewriteVisitor(AstNetlist* rootp) { iterate(rootp); }
};

//======================================================================
// Binding variable declarations

class MatchCollector final : public VNVisitor {
    std::vector<AstMatches*> m_matches;

    void visit(AstMatches* nodep) override {
        m_matches.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit MatchCollector(AstNodeExpr* nodep) { iterate(nodep); }
    const std::vector<AstMatches*>& matches() const { return m_matches; }
};

class BindCollector final : public VNVisitor {
    std::vector<AstPatBind*> m_binds;

    void visit(AstPatBind* nodep) override { m_binds.push_back(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit BindCollector(AstNodeExpr* nodep) { iterate(nodep); }
    const std::vector<AstPatBind*>& binds() const { return m_binds; }
};

class BindDeclVisitor final : public VNVisitor {
    AstNodeBlock* ensureIfThenBlock(AstIf* nodep) {
        if (AstNodeBlock* const blockp = VN_CAST(nodep->thensp(), NodeBlock)) return blockp;
        AstNode* const stmtsp
            = nodep->thensp() ? nodep->thensp()->unlinkFrBackWithNext() : nullptr;
        AstBegin* const beginp = new AstBegin{nodep->fileline(), "", nullptr, true};
        if (stmtsp) beginp->addStmtsp(stmtsp);
        nodep->addThensp(beginp);
        return beginp;
    }

    AstNodeBlock* ensureCaseItemBlock(AstCaseItem* itemp) {
        if (AstNodeBlock* const blockp = VN_CAST(itemp->stmtsp(), NodeBlock)) return blockp;
        AstNode* const stmtsp
            = itemp->stmtsp() ? itemp->stmtsp()->unlinkFrBackWithNext() : nullptr;
        AstBegin* const beginp = new AstBegin{itemp->fileline(), "", nullptr, true};
        if (stmtsp) beginp->addStmtsp(stmtsp);
        itemp->addStmtsp(beginp);
        return beginp;
    }

    AstVar* ensureBindVar(AstNodeBlock* blockp, AstPatBind* bindp) {
        const string& name = bindp->name();
        if (name.empty() || bindp->isWildcard()) return nullptr;
        for (AstNode* declp = blockp->declsp(); declp; declp = declp->nextp()) {
            if (AstVar* const varp = VN_CAST(declp, Var)) {
                if (varp->name() == name) return varp;
            }
        }
        AstBasicDType* const dtypep
            = new AstBasicDType{bindp->fileline(), VBasicDTypeKwd::LOGIC};
        AstVar* const varp = new AstVar{bindp->fileline(), VVarType::BLOCKTEMP, name,
                                        VFlagChildDType{}, dtypep};
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        blockp->addDeclsp(varp);
        return varp;
    }

    void addBindingsToBlock(AstNodeBlock* blockp, const std::vector<AstPatBind*>& binds) {
        for (AstPatBind* const bindp : binds) {
            if (bindp->isWildcard()) continue;
            AstVar* const varp = ensureBindVar(blockp, bindp);
            if (varp) bindp->varp(varp);
        }
    }

    void visit(AstIf* nodep) override {
        std::vector<AstPatBind*> binds;
        MatchCollector matchCollector{nodep->condp()};
        for (AstMatches* const matchp : matchCollector.matches()) {
            if (!matchp->patternp()) continue;
            BindCollector bindCollector{matchp->patternp()};
            const auto& patBinds = bindCollector.binds();
            binds.insert(binds.end(), patBinds.begin(), patBinds.end());
        }
        if (!binds.empty()) {
            AstNodeBlock* const blockp = ensureIfThenBlock(nodep);
            addBindingsToBlock(blockp, binds);
        }
        iterateChildren(nodep);
    }

    void visit(AstCase* nodep) override {
        if (!nodep->caseMatches()) {
            iterateChildren(nodep);
            return;
        }
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            std::vector<AstPatBind*> binds;
            for (AstNodeExpr* condp = itemp->condsp(); condp;
                 condp = VN_AS(condp->nextp(), NodeExpr)) {
                BindCollector bindCollector{condp};
                const auto& patBinds = bindCollector.binds();
                binds.insert(binds.end(), patBinds.begin(), patBinds.end());
            }
            if (!binds.empty()) {
                AstNodeBlock* const blockp = ensureCaseItemBlock(itemp);
                addBindingsToBlock(blockp, binds);
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit BindDeclVisitor(AstNetlist* rootp) { iterate(rootp); }
};

//======================================================================
// Binding type resolution

class MatchResolveVisitor final : public VNVisitor {
    VMemberMap m_memberMap;
    std::unordered_set<AstVar*> m_updated;

    AstNodeDType* dtypeFromExpr(AstNodeExpr* exprp) {
        if (!exprp) return nullptr;
        if (AstVarRef* const varrefp = VN_CAST(exprp, VarRef)) {
            AstVar* const varp = varrefp->varp();
            if (!varp) return nullptr;
            if (varp->dtypep()) return varp->dtypep();
            return varp->childDTypep();
        }
        return exprp->dtypep();
    }

    void updateBindVar(AstPatBind* bindp, AstNodeDType* dtypep) {
        if (!bindp || bindp->isWildcard()) return;
        AstVar* const varp = bindp->varp();
        if (!varp) return;
        if (m_updated.count(varp)) return;
        if (!dtypep) return;
        AstNodeDType* const newDtp = dtypep->cloneTree(false);
        if (AstNodeDType* const oldp = varp->childDTypep()) {
            VL_DO_DANGLING(pushDeletep(oldp->unlinkFrBack()), oldp);
        }
        varp->childDTypep(newDtp);
        varp->dtypep(nullptr);
        m_updated.insert(varp);
    }

    void resolvePatternTypes(AstNodeDType* dtypep, AstNodeExpr* patternp) {
        if (!patternp || !dtypep) return;
        if (AstPatBind* const bindp = VN_CAST(patternp, PatBind)) {
            updateBindVar(bindp, dtypep);
            return;
        }
        if (AstTagged* const tagp = VN_CAST(patternp, Tagged)) {
            AstUnionDType* const unionp
                = VN_CAST(dtypep->skipRefp(), UnionDType);
            if (!unionp || !unionp->isTagged()) {
                tagp->v3error("Tagged pattern requires tagged union type");
                return;
            }
            AstMemberDType* const memberp
                = VN_CAST(m_memberMap.findMember(unionp, tagp->member()), MemberDType);
            if (!memberp) {
                tagp->v3error("Tagged union member '" << tagp->member()
                                                     << "' not found in union "
                                                     << unionp->prettyTypeName());
                return;
            }
            resolvePatternTypes(memberp->subDTypep(), tagp->exprp());
            return;
        }
        if (AstPattern* const patp = VN_CAST(patternp, Pattern)) {
            AstNodeUOrStructDType* const structp
                = VN_CAST(dtypep->skipRefp(), NodeUOrStructDType);
            if (!structp) return;
            AstMemberDType* posp = structp->membersp();
            for (AstPatMember* patm = VN_AS(patp->itemsp(), PatMember); patm;
                 patm = VN_AS(patm->nextp(), PatMember)) {
                if (patm->isDefault()) continue;
                AstMemberDType* memp = nullptr;
                if (AstText* const textp = VN_CAST(patm->keyp(), Text)) {
                    memp = VN_CAST(m_memberMap.findMember(structp, textp->text()), MemberDType);
                } else if (!patm->keyp()) {
                    memp = posp;
                    if (posp) posp = VN_AS(posp->nextp(), MemberDType);
                }
                if (!memp) continue;
                AstNodeExpr* const subpatp = patm->lhssp();
                resolvePatternTypes(memp->subDTypep(), subpatp);
            }
            return;
        }
    }

    void visit(AstMatches* nodep) override {
        AstNodeDType* dtypep = dtypeFromExpr(nodep->exprp());
        if (!dtypep) return;
        dtypep = dtypep->skipRefp();
        AstUnionDType* const unionp = VN_CAST(dtypep, UnionDType);
        if (!unionp || !unionp->isTagged()) return;
        AstMemberDType* const memberp
            = VN_CAST(m_memberMap.findMember(unionp, nodep->member()), MemberDType);
        if (!memberp) return;
        resolvePatternTypes(memberp->subDTypep(), nodep->patternp());
        iterateChildren(nodep);
    }

    void visit(AstCase* nodep) override {
        if (!nodep->caseMatches()) {
            iterateChildren(nodep);
            return;
        }
        AstNodeDType* dtypep = dtypeFromExpr(nodep->exprp());
        if (!dtypep) {
            iterateChildren(nodep);
            return;
        }
        dtypep = dtypep->skipRefp();
        AstUnionDType* const unionp = VN_CAST(dtypep, UnionDType);
        if (!unionp || !unionp->isTagged()) {
            iterateChildren(nodep);
            return;
        }
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNodeExpr* condp = itemp->condsp(); condp;
                 condp = VN_AS(condp->nextp(), NodeExpr)) {
                AstTagged* const tagp = VN_CAST(condp, Tagged);
                if (!tagp) continue;
                AstMemberDType* const memberp
                    = VN_CAST(m_memberMap.findMember(unionp, tagp->member()), MemberDType);
                if (!memberp) continue;
                resolvePatternTypes(memberp->subDTypep(), tagp->exprp());
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit MatchResolveVisitor(AstNetlist* rootp) { iterate(rootp); }
};

//======================================================================
// Lower matches and case...matches

struct MatchBuild {
    AstNodeExpr* condp = nullptr;
    std::vector<AstAssign*> assigns;
};

class MatchLowerVisitor final : public VNVisitor {
    VMemberMap m_memberMap;

    struct UnionInfo {
        AstUnionDType* unionp = nullptr;
        AstMemberDType* memberp = nullptr;
        int tagIndex = -1;
        int numMembers = 0;
        int tagWidth = 0;
        int dataWidth = 0;
        int totalWidth = 0;
    };

    UnionInfo computeUnionInfo(AstUnionDType* unionp, const string& member, AstNode* ctxp) {
        UnionInfo info;
        if (!unionp || !unionp->isTagged()) {
            ctxp->v3error("Matches operator requires a tagged union type, not "
                          << (unionp ? unionp->prettyTypeName() : "unknown"));
            return info;
        }
        int tagIndex = -1;
        int numMembers = 0;
        AstMemberDType* foundMemberp = nullptr;
        for (AstNode* itemp = unionp->membersp(); itemp; itemp = itemp->nextp()) {
            if (AstMemberDType* const memberp = VN_CAST(itemp, MemberDType)) {
                if (memberp->name() == member) {
                    foundMemberp = memberp;
                    tagIndex = numMembers;
                }
                ++numMembers;
            }
        }
        if (!foundMemberp) {
            ctxp->v3error("Tagged union member '" << member << "' not found in union "
                                                   << unionp->prettyTypeName());
            return info;
        }
        int tagWidth = 1;
        while ((1 << tagWidth) < numMembers) ++tagWidth;
        const int totalWidth = unionp->width();
        const int dataWidth = totalWidth - tagWidth;
        info.unionp = unionp;
        info.memberp = foundMemberp;
        info.tagIndex = tagIndex;
        info.numMembers = numMembers;
        info.tagWidth = tagWidth;
        info.totalWidth = totalWidth;
        info.dataWidth = dataWidth;
        return info;
    }

    UnionInfo computeUnionInfo(AstNodeExpr* exprp, const string& member, AstNode* ctxp) {
        if (!exprp || !exprp->dtypep()) {
            ctxp->v3error("Matches expression has no type");
            return {};
        }
        AstNodeDType* const dtypep = exprp->dtypep()->skipRefp();
        return computeUnionInfo(VN_CAST(dtypep, UnionDType), member, ctxp);
    }

    AstNodeExpr* buildTagCond(FileLine* fl, AstNodeExpr* exprp, const UnionInfo& info) {
        AstNodeExpr* const exprClonep = exprp->cloneTree(false);
        AstNodeExpr* tagExtrp = nullptr;
        if (info.tagWidth == info.totalWidth) {
            tagExtrp = exprClonep;
        } else {
            const int tagLsb = info.totalWidth - info.tagWidth;
            tagExtrp = new AstSel{fl, exprClonep, tagLsb, info.tagWidth};
        }
        AstNodeExpr* const tagConstp
            = new AstConst{fl, AstConst::WidthedValue{}, info.tagWidth,
                           static_cast<uint32_t>(info.tagIndex)};
        return new AstEq{fl, tagExtrp, tagConstp};
    }

    AstNodeExpr* buildPayloadExpr(FileLine* fl, AstNodeExpr* exprp, const UnionInfo& info,
                                  int memberWidth) {
        if (info.dataWidth <= 0 || memberWidth <= 0) return nullptr;
        AstNodeExpr* const exprClonep = exprp->cloneTree(false);
        AstNodeExpr* datap = nullptr;
        if (info.dataWidth == info.totalWidth) {
            datap = exprClonep;
        } else {
            datap = new AstSel{fl, exprClonep, 0, info.dataWidth};
        }
        if (memberWidth < info.dataWidth) {
            datap = new AstSel{fl, datap, 0, memberWidth};
        }
        return datap;
    }

    AstNodeExpr* combineConds(AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        if (!lhsp) return rhsp;
        if (!rhsp) return lhsp;
        return new AstLogAnd{lhsp->fileline(), lhsp, rhsp};
    }

    AstNodeExpr* adjustWidth(AstNodeExpr* exprp, int width) {
        if (!exprp || width <= 0) return exprp;
        const int exprWidth = exprp->width();
        if (exprWidth == width) return exprp;
        if (exprWidth > width) return new AstSel{exprp->fileline(), exprp, 0, width};
        return new AstExtend{exprp->fileline(), exprp, width};
    }

    AstAssign* buildBindAssign(AstPatBind* bindp, AstNodeExpr* valuep) {
        AstVar* const varp = bindp->varp();
        if (!varp || !valuep) return nullptr;
        AstNodeExpr* const rhs = adjustWidth(valuep->cloneTree(false), varp->width());
        AstVarRef* const lhs = new AstVarRef{bindp->fileline(), varp, VAccess::WRITE};
        return new AstAssign{bindp->fileline(), lhs, rhs};
    }

    AstNodeExpr* buildStructField(FileLine* fl, AstNodeExpr* basep, AstMemberDType* memp) {
        const int width = memp->width();
        const int lsb = memp->lsb();
        if (width <= 0) return nullptr;
        return new AstSel{fl, basep->cloneTree(false), lsb, width};
    }

    MatchBuild buildPattern(AstNodeExpr* valuep, AstNodeDType* dtypep, AstNodeExpr* patternp) {
        MatchBuild out;
        if (!patternp) return out;
        if (AstPatBind* const bindp = VN_CAST(patternp, PatBind)) {
            if (!bindp->isWildcard()) {
                if (AstAssign* const assignp = buildBindAssign(bindp, valuep)) {
                    out.assigns.push_back(assignp);
                }
            }
            return out;
        }
        if (AstTagged* const tagp = VN_CAST(patternp, Tagged)) {
            AstUnionDType* const unionp = VN_CAST(dtypep->skipRefp(), UnionDType);
            if (!unionp || !unionp->isTagged()) {
                tagp->v3error("Tagged pattern requires tagged union type");
                return out;
            }
            UnionInfo info = computeUnionInfo(unionp, tagp->member(), tagp);
            MatchBuild nested = buildMatchWithInfo(valuep, info, tagp->exprp(), tagp);
            out.assigns.insert(out.assigns.end(), nested.assigns.begin(), nested.assigns.end());
            out.condp = combineConds(out.condp, nested.condp);
            return out;
        }
        if (AstPattern* const patp = VN_CAST(patternp, Pattern)) {
            AstNodeUOrStructDType* const structp
                = VN_CAST(dtypep->skipRefp(), NodeUOrStructDType);
            if (!structp) return out;
            AstMemberDType* posp = structp->membersp();
            for (AstPatMember* patm = VN_AS(patp->itemsp(), PatMember); patm;
                 patm = VN_AS(patm->nextp(), PatMember)) {
                if (patm->isDefault()) continue;
                AstMemberDType* memp = nullptr;
                if (AstText* const textp = VN_CAST(patm->keyp(), Text)) {
                    memp = VN_CAST(m_memberMap.findMember(structp, textp->text()), MemberDType);
                } else if (!patm->keyp()) {
                    memp = posp;
                    if (posp) posp = VN_AS(posp->nextp(), MemberDType);
                }
                if (!memp) continue;
                AstNodeExpr* const subpatp = patm->lhssp();
                AstNodeExpr* const fieldp = buildStructField(patm->fileline(), valuep, memp);
                MatchBuild sub = buildPattern(fieldp, memp->subDTypep(), subpatp);
                out.assigns.insert(out.assigns.end(), sub.assigns.begin(), sub.assigns.end());
                out.condp = combineConds(out.condp, sub.condp);
            }
            return out;
        }
        if (valuep) {
            AstNodeExpr* const lhs = valuep->cloneTree(false);
            AstNodeExpr* const rhs = patternp->cloneTree(false);
            out.condp = combineConds(out.condp, new AstEq{patternp->fileline(), lhs, rhs});
        }
        return out;
    }

    MatchBuild buildMatchWithInfo(AstNodeExpr* exprp, const UnionInfo& info, AstNodeExpr* patternp,
                                  AstNode* ctxp) {
        MatchBuild out;
        if (!info.memberp) {
            out.condp = new AstConst{ctxp->fileline(), AstConst::BitFalse{}};
            return out;
        }
        AstNodeExpr* const tagCondp = buildTagCond(ctxp->fileline(), exprp, info);
        const int memberWidth = info.memberp->subDTypep()->width();
        AstNodeExpr* const payloadp
            = buildPayloadExpr(ctxp->fileline(), exprp, info, memberWidth);
        MatchBuild pat = buildPattern(payloadp, info.memberp->subDTypep(), patternp);
        out.assigns.insert(out.assigns.end(), pat.assigns.begin(), pat.assigns.end());
        out.condp = combineConds(tagCondp, pat.condp);
        return out;
    }

    MatchBuild buildMatch(AstNodeExpr* exprp, const string& member, AstNodeExpr* patternp,
                          AstNode* ctxp) {
        UnionInfo info = computeUnionInfo(exprp, member, ctxp);
        return buildMatchWithInfo(exprp, info, patternp, ctxp);
    }

    AstNodeBlock* ensureIfThenBlock(AstIf* nodep) {
        if (AstNodeBlock* const blockp = VN_CAST(nodep->thensp(), NodeBlock)) return blockp;
        AstNode* const stmtsp
            = nodep->thensp() ? nodep->thensp()->unlinkFrBackWithNext() : nullptr;
        AstBegin* const beginp = new AstBegin{nodep->fileline(), "", nullptr, true};
        if (stmtsp) beginp->addStmtsp(stmtsp);
        nodep->addThensp(beginp);
        return beginp;
    }

    AstNodeBlock* ensureStmtBlock(AstNode* stmtsp, FileLine* fl, AstNode*& slotp) {
        if (AstNodeBlock* const blockp = VN_CAST(stmtsp, NodeBlock)) return blockp;
        AstBegin* const beginp = new AstBegin{fl, "", nullptr, true};
        if (stmtsp) beginp->addStmtsp(stmtsp->unlinkFrBackWithNext());
        slotp = beginp;
        return beginp;
    }

    void prependStatements(AstNodeBlock* blockp, AstNode* stmtsp) {
        if (!stmtsp) return;
        if (AstNode* const oldsp = blockp->stmtsp()) {
            VNRelinker relink;
            oldsp->unlinkFrBack(&relink);
            stmtsp->addNext(oldsp);
            relink.relink(stmtsp);
        } else {
            blockp->addStmtsp(stmtsp);
        }
    }

    AstNode* assignList(const std::vector<AstAssign*>& assigns) {
        AstNode* headp = nullptr;
        for (AstAssign* const assignp : assigns) {
            if (!headp) {
                headp = assignp;
            } else {
                headp->addNext(assignp);
            }
        }
        return headp;
    }

    void lowerIfMatch(AstIf* nodep, AstMatches* matchp) {
        MatchBuild match = buildMatch(matchp->exprp(), matchp->member(), matchp->patternp(), matchp);
        AstNodeExpr* const condp = match.condp ? match.condp
                                               : new AstConst{matchp->fileline(), AstConst::BitTrue{}};
        matchp->unlinkFrBack();
        nodep->condp(condp);
        VL_DO_DANGLING(pushDeletep(matchp), matchp);
        if (!match.assigns.empty()) {
            AstNodeBlock* const blockp = ensureIfThenBlock(nodep);
            prependStatements(blockp, assignList(match.assigns));
        }
    }

    void lowerCaseMatches(AstCase* nodep) {
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
        AstNode* defaultStmts = nullptr;
        struct CasePatternInfo {
            AstTagged* taggedp = nullptr;
            AstNode* stmtsp = nullptr;
        };
        std::vector<CasePatternInfo> patterns;

        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                if (itemp->stmtsp()) defaultStmts = itemp->stmtsp()->unlinkFrBackWithNext();
                continue;
            }
            AstNode* itemStmts = itemp->stmtsp() ? itemp->stmtsp()->unlinkFrBackWithNext() : nullptr;
            bool first = true;
            for (AstNodeExpr *nextp, *condp = itemp->condsp(); condp; condp = nextp) {
                nextp = VN_AS(condp->nextp(), NodeExpr);
                AstTagged* const taggedp = VN_CAST(condp, Tagged);
                if (!taggedp) {
                    condp->v3error("Case...matches patterns must be tagged patterns");
                    continue;
                }
                taggedp->unlinkFrBack();
                AstNode* stmtsp = nullptr;
                if (itemStmts) {
                    stmtsp = first ? itemStmts : itemStmts->cloneTree(true);
                }
                patterns.push_back({taggedp, stmtsp});
                first = false;
            }
        }

        AstNode* elsep = defaultStmts;
        for (size_t i = patterns.size(); i-- > 0;) {
            AstTagged* const taggedp = patterns[i].taggedp;
            AstNode* stmtsp = patterns[i].stmtsp;
            if (!taggedp) continue;
            MatchBuild match
                = buildMatch(exprp, taggedp->member(), taggedp->exprp(), taggedp);
            if (!match.assigns.empty()) {
                AstNodeBlock* const blockp = ensureStmtBlock(stmtsp, fl, stmtsp);
                prependStatements(blockp, assignList(match.assigns));
            }
            AstNodeExpr* const condp
                = match.condp ? match.condp : new AstConst{fl, AstConst::BitTrue{}};
            AstIf* const ifp = new AstIf{fl, condp, stmtsp, elsep};
            if (nodep->uniquePragma()) ifp->uniquePragma(true);
            if (nodep->unique0Pragma()) ifp->unique0Pragma(true);
            if (nodep->priorityPragma()) ifp->priorityPragma(true);
            elsep = ifp;
            VL_DO_DANGLING(pushDeletep(taggedp), taggedp);
        }
        VL_DO_DANGLING(pushDeletep(exprp), exprp);

        if (elsep) {
            nodep->replaceWith(elsep);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstIf* nodep) override {
        if (AstMatches* const matchp = VN_CAST(nodep->condp(), Matches)) {
            lowerIfMatch(nodep, matchp);
        }
        iterateChildren(nodep);
    }

    void visit(AstCase* nodep) override {
        if (nodep->caseMatches()) {
            lowerCaseMatches(nodep);
            return;
        }
        iterateChildren(nodep);
    }

    void visit(AstMatches* nodep) override {
        MatchBuild match = buildMatch(nodep->exprp(), nodep->member(), nodep->patternp(), nodep);
        if (!match.assigns.empty()) {
            nodep->v3error("Binding patterns only supported in statements");
        }
        AstNodeExpr* const condp
            = match.condp ? match.condp : new AstConst{nodep->fileline(), AstConst::BitTrue{}};
        nodep->replaceWith(condp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit MatchLowerVisitor(AstNetlist* rootp) { iterate(rootp); }
};

}  // namespace

//======================================================================

void V3Match::preLink(AstNetlist* nodep) {
    UINFO(4, "V3Match::preLink\n");
    CondAndRewriteVisitor{nodep};
    BindDeclVisitor{nodep};
}

void V3Match::resolve(AstNetlist* nodep) {
    UINFO(4, "V3Match::resolve\n");
    MatchResolveVisitor{nodep};
}

void V3Match::lower(AstNetlist* nodep) {
    UINFO(4, "V3Match::lower\n");
    MatchLowerVisitor{nodep};
}
