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

#ifndef VERILATOR_V3SEQMATCH_H_
#define VERILATOR_V3SEQMATCH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

class V3SeqMatch final {
public:
    static void seqMatchAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
