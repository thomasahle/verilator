// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2024-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated assertion statistics implementation
///
//=============================================================================

#include "verilated_assert_stats.h"

#include <memory>

//=============================================================================
// Global assertion statistics singleton

static VerilatedMutex s_assertStatsMutex;
static std::unique_ptr<VerilatedAssertStats> s_assertStatsp VL_GUARDED_BY(s_assertStatsMutex);

VerilatedAssertStats* vlAssertStatsp() VL_MT_SAFE {
    // Thread-safe lazy initialization
    if (VL_UNLIKELY(!s_assertStatsp)) {
        const VerilatedLockGuard lock(s_assertStatsMutex);
        if (!s_assertStatsp) {
            s_assertStatsp.reset(new VerilatedAssertStats);
        }
    }
    return s_assertStatsp.get();
}

//=============================================================================
// Print assertion summary on program exit (optional)

// Destructor helper to print summary
class VerilatedAssertStatsExitPrinter {
public:
    ~VerilatedAssertStatsExitPrinter() {
        if (s_assertStatsp && s_assertStatsp->numAsserts() > 0) {
            s_assertStatsp->printSummary(std::cerr);
            std::cerr.flush();
        }
    }
};

// Create static instance to print on exit
static VerilatedAssertStatsExitPrinter s_exitPrinter;
