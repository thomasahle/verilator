// DESCRIPTION: Verilog: Test for interface with multiple initial blocks
//
// This file is part of the software.
//
// This software is free software; you can redistribute it and/or modify it
// under the terms of the GNU Lesser General Public License Version 3.0
// as published by the Free Software Foundation.
//
// SPDX-License-Identifier: LGPL-3.0-only
//
// Test that interfaces with multiple unnamed initial blocks don't cause
// "Duplicate declaration of member name: ''" errors in VMemberMap

interface iface_with_multiple_initials;
  // Multiple initial blocks should not cause duplicate empty name errors
  string name = "TEST_IFACE";

  initial begin
    $display("Initial block 1: %s", name);
  end

  initial begin
    $display("Initial block 2");
  end

  initial begin
    $display("Initial block 3");
  end
endinterface

module t(/*AUTOARG*/);
  iface_with_multiple_initials ifc();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
