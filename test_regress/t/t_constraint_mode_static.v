// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// Test constraint_mode() on static constraints

class Packet;
   rand int m_one;
   static constraint cons { m_one > 0 && m_one < 10; }
endclass

class PacketMixed;
   rand int m_val;
   static constraint static_cons { m_val > 0; }
   constraint dynamic_cons { m_val < 100; }
endclass

module t;
   Packet p;
   PacketMixed pm;

   initial begin
      // Test basic static constraint
      p = new;

      // Check default mode is enabled (1)
      if (p.cons.constraint_mode() != 1) $stop;

      // Disable the static constraint
      p.cons.constraint_mode(0);
      if (p.cons.constraint_mode() != 0) $stop;

      // Re-enable the static constraint
      p.cons.constraint_mode(1);
      if (p.cons.constraint_mode() != 1) $stop;

      // Test with mixed static/dynamic constraints
      pm = new;

      // Both should be enabled by default
      if (pm.static_cons.constraint_mode() != 1) $stop;
      if (pm.dynamic_cons.constraint_mode() != 1) $stop;

      // Disable static constraint
      pm.static_cons.constraint_mode(0);
      if (pm.static_cons.constraint_mode() != 0) $stop;
      if (pm.dynamic_cons.constraint_mode() != 1) $stop;

      // Disable all constraints
      pm.constraint_mode(0);
      if (pm.static_cons.constraint_mode() != 0) $stop;
      if (pm.dynamic_cons.constraint_mode() != 0) $stop;

      // Enable all constraints
      pm.constraint_mode(1);
      if (pm.static_cons.constraint_mode() != 1) $stop;
      if (pm.dynamic_cons.constraint_mode() != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
