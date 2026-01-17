// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add common contents to modules
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
// V3Common's Transformations:
//
//  Each class:
//      Create string access functions
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Common.h"

#include "V3EmitCBase.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Common component builders

string V3Common::makeToStringCall(AstNodeDType* nodep, const std::string& lhs) {
    std::string stmt;
    if (VN_IS(nodep->skipRefp(), BasicDType) && nodep->isWide()) {
        stmt += "VL_TO_STRING_W(";
        stmt += cvtToStr(nodep->widthWords());
        stmt += ", ";
    } else if (VN_IS(nodep->skipRefp(), BasicDType) && nodep->isWide()) {
        stmt += "VL_TO_STRING_W(";
        stmt += cvtToStr(nodep->widthWords());
        stmt += ", ";
    } else {
        stmt += "VL_TO_STRING(";
    }
    stmt += lhs;
    stmt += ")";
    return stmt;
}

static void makeVlToString(AstClass* nodep) {
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const VlClassRef<" + EmitCUtil::prefixNameProtect(nodep) + ">& obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);
    AstNodeExpr* const exprp
        = new AstCExpr{nodep->fileline(), "obj ? obj->to_string() : \"null\""};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});
    nodep->addStmtsp(funcp);
}
static void makeVlToString(AstIface* nodep) {
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const " + EmitCUtil::prefixNameProtect(nodep) + "* obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);
    AstNodeExpr* const exprp = new AstCExpr{nodep->fileline(), "obj ? obj->vlNamep : \"null\""};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});
    nodep->addStmtsp(funcp);
}
static void makeVlToString(AstNodeUOrStructDType* nodep) {
    AstNodeModule* const modp = nodep->classOrPackagep();
    UASSERT_OBJ(modp, nodep, "Unlinked struct package");
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const " + EmitCUtil::prefixNameProtect(nodep) + "& obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "std::string out;"});
    for (const AstMemberDType* itemp = nodep->membersp(); itemp;
         itemp = VN_AS(itemp->nextp(), MemberDType)) {
        std::string stmt = "out += \"";
        if (itemp == nodep->membersp()) {
            stmt += "'{";
        } else {
            stmt += ", ";
        }
        stmt += VIdProtect::protect(itemp->prettyName()) + ":\" + ";
        stmt += V3Common::makeToStringCall(itemp->dtypep(), "obj."s + itemp->nameProtect());
        stmt += ";";
        funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
    }
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "out += \"}\";"});

    AstCExpr* const exprp = new AstCExpr{nodep->fileline(), "out"};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});

    modp->addStmtsp(funcp);
}
static void makeVlToStringTaggedUnion(AstUnionDType* nodep) {
    // Generate VL_TO_STRING for tagged unions
    // Tagged unions have a discriminant (tag) at the MSB that identifies the active member
    AstNodeModule* const modp = nodep->classOrPackagep();
    UASSERT_OBJ(modp, nodep, "Unlinked union package");

    // Count members and calculate tag width
    int numMembers = 0;
    int maxMemberWidth = 0;
    for (const AstMemberDType* itemp = nodep->membersp(); itemp;
         itemp = VN_CAST(itemp->nextp(), MemberDType)) {
        ++numMembers;
        if (itemp->width() > maxMemberWidth) maxMemberWidth = itemp->width();
    }
    int tagWidth = 1;
    while ((1 << tagWidth) < numMembers) ++tagWidth;

    // Determine the data type name based on union width
    const int totalWidth = nodep->width();
    std::string ctype;
    if (totalWidth <= 8) {
        ctype = "uint8_t";
    } else if (totalWidth <= 16) {
        ctype = "uint16_t";
    } else if (totalWidth <= 32) {
        ctype = "uint32_t";
    } else if (totalWidth <= 64) {
        ctype = "uint64_t";
    } else {
        ctype = "VlWide<" + cvtToStr((totalWidth + 31) / 32) + ">";
    }

    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const " + ctype + "& obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);

    // Extract tag bits (MSB)
    const int dataWidth = maxMemberWidth;
    const std::string tagExtract = (totalWidth <= 64)
                                       ? "(obj >> " + cvtToStr(dataWidth) + ") & "
                                             + cvtToStr((1 << tagWidth) - 1)
                                       : "/* wide tag extraction not yet supported */ 0";
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "const int tag = " + tagExtract + ";"});

    // Generate switch statement
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "switch (tag) {"});
    int tagValue = 0;
    for (const AstMemberDType* itemp = nodep->membersp(); itemp;
         itemp = VN_CAST(itemp->nextp(), MemberDType)) {
        const std::string memberName = VIdProtect::protect(itemp->prettyName());
        std::string caseStmt = "case " + cvtToStr(tagValue) + ": ";
        if (itemp->width() == 0) {
            // void member (e.g., "void Invalid")
            caseStmt += "return \"'{" + memberName + "}\";";
        } else {
            // Member with data
            const std::string dataMask = cvtToStr((1ULL << itemp->width()) - 1);
            caseStmt += "return \"'{" + memberName + ":\" + VL_TO_STRING(obj & " + dataMask
                        + ") + \"}\";";
        }
        funcp->addStmtsp(new AstCStmt{nodep->fileline(), caseStmt});
        ++tagValue;
    }
    funcp->addStmtsp(
        new AstCStmt{nodep->fileline(), "default: return \"'{<invalid tag>}\";"});
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "}"});

    // This shouldn't be reached but needed for C++ return
    AstCExpr* const exprp = new AstCExpr{nodep->fileline(), "\"\""};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});

    modp->addStmtsp(funcp);
}
static void makeToString(AstClass* nodep) {
    AstCFunc* const funcp = new AstCFunc{nodep->fileline(), "to_string", nullptr, "std::string"};
    funcp->isConst(true);
    funcp->isStatic(false);
    funcp->protect(false);
    AstCExpr* const exprp = new AstCExpr{nodep->fileline(), R"("'{"s + to_string_middle() + "}")"};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});
    nodep->addStmtsp(funcp);
}
static void makeToStringMiddle(AstClass* nodep) {
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "to_string_middle", nullptr, "std::string"};
    funcp->isConst(true);
    funcp->isStatic(false);
    funcp->protect(false);
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "std::string out;"});
    std::string comma;
    for (AstNode* itemp = nodep->membersp(); itemp; itemp = itemp->nextp()) {
        if (const auto* const varp = VN_CAST(itemp, Var)) {
            if (!varp->isParam() && !varp->isInternal()
                && !(varp->dtypeSkipRefp()->basicp()
                     && (varp->dtypeSkipRefp()->basicp()->isRandomGenerator()
                         || varp->dtypeSkipRefp()->basicp()->isStdRandomGenerator()))) {
                string stmt = "out += \"";
                stmt += comma;
                comma = ", ";
                stmt += itemp->origNameProtect();
                stmt += ":\" + ";
                stmt += V3Common::makeToStringCall(itemp->dtypep(), itemp->nameProtect());
                stmt += ";";
                nodep->user1(true);  // So what we extend dumps this
                funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
            }
        }
    }
    if (nodep->extendsp()) {
        string stmt = "out += ";
        if (!comma.empty()) stmt += "\", \"+ ";
        // comma = ", ";  // Nothing further so not needed
        stmt += EmitCUtil::prefixNameProtect(nodep->extendsp()->dtypep());
        stmt += "::to_string_middle();";
        nodep->user1(true);  // So what we extend dumps this
        funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
    }

    AstCExpr* const exprp = new AstCExpr{nodep->fileline(), "out"};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});

    nodep->addStmtsp(funcp);
}

//######################################################################
// V3Common class functions

void V3Common::commonAll() {
    UINFO(2, __FUNCTION__ << ":");
    // NODE STATE
    // Entire netlist:
    //  AstClass::user1()     -> bool.  True if class needs to_string dumper
    const VNUser1InUse m_inuser1;
    // Create common contents for each module
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            // Create ToString methods
            makeVlToString(classp);
            makeToString(classp);
            makeToStringMiddle(classp);
        } else if (AstIface* const ifacep = VN_CAST(nodep, Iface)) {
            makeVlToString(ifacep);
        }
    }
    for (AstNode* nodep = v3Global.rootp()->typeTablep()->typesp(); nodep;
         nodep = nodep->nextp()) {
        if (AstUnionDType* const unionp = VN_CAST(nodep, UnionDType)) {
            // Tagged unions need special VL_TO_STRING even though they're packed
            if (unionp->isTagged()) {
                // Skip if no package - the union type may have had its package link cleared
                // during dead code elimination. %p formatting will still work with the
                // default integer output.
                if (unionp->classOrPackagep()) {
                    makeVlToStringTaggedUnion(unionp);
                }
            } else if (!unionp->packed()) {
                makeVlToString(unionp);
            }
        } else if (AstNodeUOrStructDType* const dtypep = VN_CAST(nodep, NodeUOrStructDType)) {
            if (!dtypep->packed()) makeVlToString(dtypep);
        }
    }
    V3Global::dumpCheckGlobalTree("common", 0, dumpTreeEitherLevel() >= 3);
}
