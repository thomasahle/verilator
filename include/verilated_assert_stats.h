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
/// \brief Verilated assertion statistics header
///
/// This provides runtime tracking of assertion pass/fail counts.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_ASSERT_STATS_H_
#define VERILATOR_VERILATED_ASSERT_STATS_H_

#include "verilatedos.h"
#include "verilated.h"

#include <atomic>
#include <fstream>
#include <iostream>
#include <map>
#include <mutex>
#include <string>
#include <vector>

//=============================================================================
// VerilatedAssertStats - Track assertion statistics

class VerilatedAssertStats final {
public:
    struct AssertInfo {
        std::string name;        // Assertion name (from label)
        std::string filename;    // Source filename
        int lineno = 0;          // Source line number
        std::string hier;        // Hierarchy path
        std::atomic<uint64_t> passCount{0};  // Number of times assertion passed
        std::atomic<uint64_t> failCount{0};  // Number of times assertion failed
        std::atomic<uint64_t> evalCount{0};  // Total evaluations

        AssertInfo() = default;
        AssertInfo(const std::string& n, const std::string& f, int l, const std::string& h)
            : name(n), filename(f), lineno(l), hier(h) {}
        // Copy constructor for map insertion
        AssertInfo(const AssertInfo& other)
            : name(other.name), filename(other.filename), lineno(other.lineno), hier(other.hier)
            , passCount(other.passCount.load()), failCount(other.failCount.load())
            , evalCount(other.evalCount.load()) {}
    };

private:
    mutable VerilatedMutex m_mutex;
    std::map<uint32_t, AssertInfo> m_asserts VL_GUARDED_BY(m_mutex);
    uint32_t m_nextId VL_GUARDED_BY(m_mutex) = 0;
    bool m_enabled = true;

public:
    // CONSTRUCTORS
    VerilatedAssertStats() = default;
    ~VerilatedAssertStats() = default;
    VL_UNCOPYABLE(VerilatedAssertStats);

    // METHODS
    /// Register an assertion and return its ID
    uint32_t registerAssert(const std::string& name, const std::string& filename,
                            int lineno, const std::string& hier) VL_MT_SAFE {
        const VerilatedLockGuard lock(m_mutex);
        uint32_t id = m_nextId++;
        m_asserts.emplace(id, AssertInfo(name, filename, lineno, hier));
        return id;
    }

    /// Record assertion pass
    void recordPass(uint32_t id) VL_MT_SAFE {
        if (!m_enabled) return;
        const VerilatedLockGuard lock(m_mutex);
        auto it = m_asserts.find(id);
        if (it != m_asserts.end()) {
            it->second.passCount.fetch_add(1, std::memory_order_relaxed);
            it->second.evalCount.fetch_add(1, std::memory_order_relaxed);
        }
    }

    /// Record assertion fail
    void recordFail(uint32_t id) VL_MT_SAFE {
        if (!m_enabled) return;
        const VerilatedLockGuard lock(m_mutex);
        auto it = m_asserts.find(id);
        if (it != m_asserts.end()) {
            it->second.failCount.fetch_add(1, std::memory_order_relaxed);
            it->second.evalCount.fetch_add(1, std::memory_order_relaxed);
        }
    }

    /// Enable/disable tracking
    void enabled(bool flag) VL_MT_SAFE { m_enabled = flag; }
    bool enabled() const VL_MT_SAFE { return m_enabled; }

    /// Get total number of registered assertions
    size_t numAsserts() const VL_MT_SAFE {
        const VerilatedLockGuard lock(m_mutex);
        return m_asserts.size();
    }

    /// Get number of assertions that have been exercised (evaluated at least once)
    size_t numExercised() const VL_MT_SAFE {
        const VerilatedLockGuard lock(m_mutex);
        size_t count = 0;
        for (const auto& pair : m_asserts) {
            if (pair.second.evalCount > 0) ++count;
        }
        return count;
    }

    /// Get number of assertions that have failed
    size_t numFailed() const VL_MT_SAFE {
        const VerilatedLockGuard lock(m_mutex);
        size_t count = 0;
        for (const auto& pair : m_asserts) {
            if (pair.second.failCount > 0) ++count;
        }
        return count;
    }

    /// Print assertion summary to stream
    void printSummary(std::ostream& os = std::cout) const VL_MT_SAFE {
        const VerilatedLockGuard lock(m_mutex);
        if (m_asserts.empty()) return;

        os << "\n";
        os << "=== Assertion Summary ===\n";

        uint64_t totalPass = 0, totalFail = 0, totalEval = 0;
        size_t exercised = 0;

        for (const auto& pair : m_asserts) {
            const AssertInfo& info = pair.second;
            const uint64_t pass = info.passCount.load();
            const uint64_t fail = info.failCount.load();
            const uint64_t eval = info.evalCount.load();

            totalPass += pass;
            totalFail += fail;
            totalEval += eval;
            if (eval > 0) ++exercised;

            // Format: name: STATUS (pass: N, fail: N)
            os << "  " << (info.name.empty() ? "(unnamed)" : info.name) << ": ";
            if (eval == 0) {
                os << "NOT EXERCISED";
            } else if (fail > 0) {
                os << "FAIL";
            } else {
                os << "PASS";
            }
            os << " (pass: " << pass << ", fail: " << fail << ")";
            if (!info.hier.empty()) os << " [" << info.hier << "]";
            os << "\n";
        }

        os << "-------------------------\n";
        os << "Total: " << m_asserts.size() << " assertions, "
           << exercised << " exercised, "
           << numFailed() << " failed\n";
        os << "Coverage: " << exercised << "/" << m_asserts.size()
           << " (" << (m_asserts.empty() ? 100 : (exercised * 100 / m_asserts.size())) << "%)\n";
        os << "=========================\n";
    }

    /// Write assertion statistics to file (compatible with coverage tools)
    void write(const std::string& filename) const VL_MT_SAFE {
        const VerilatedLockGuard lock(m_mutex);
        std::ofstream os(filename);
        if (!os) {
            VL_PRINTF_MT("%%Warning: Cannot open assertion stats file: %s\n", filename.c_str());
            return;
        }

        os << "# Verilator Assertion Statistics\n";
        os << "# name\tfilename\tlineno\thier\tpass\tfail\teval\n";
        for (const auto& pair : m_asserts) {
            const AssertInfo& info = pair.second;
            os << info.name << "\t"
               << info.filename << "\t"
               << info.lineno << "\t"
               << info.hier << "\t"
               << info.passCount << "\t"
               << info.failCount << "\t"
               << info.evalCount << "\n";
        }
    }
};

//=============================================================================
// Global assertion statistics access

/// Get global assertion statistics (creates if needed)
VerilatedAssertStats* vlAssertStatsp() VL_MT_SAFE;

/// Macro to register an assertion at elaboration time
#define VL_ASSERT_REGISTER(name, filename, lineno, hier) \
    vlAssertStatsp()->registerAssert(name, filename, lineno, hier)

/// Macro to record assertion pass
#define VL_ASSERT_PASS(id) vlAssertStatsp()->recordPass(id)

/// Macro to record assertion fail
#define VL_ASSERT_FAIL(id) vlAssertStatsp()->recordFail(id)

#endif  // VERILATOR_VERILATED_ASSERT_STATS_H_
