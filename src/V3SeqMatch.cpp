// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Sequence match item lowering
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SeqMatch.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class SeqMatchVisitor final : public VNVisitor {
    void visit(AstSeqMatchAction* nodep) override {
        AstNode* matchItemsp = nullptr;
        if (nodep->matchItemsp()) {
            matchItemsp = nodep->matchItemsp()->unlinkFrBackWithNext();
        }
        if (matchItemsp) {
            nodep->replaceWith(matchItemsp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit SeqMatchVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~SeqMatchVisitor() override = default;
};

void V3SeqMatch::seqMatchAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { SeqMatchVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("seqmatch", 0, dumpTreeEitherLevel() >= 3);
}
