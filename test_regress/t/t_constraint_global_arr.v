// DESCRIPTION: Verilator: Verilog Test module
//
// Test nested array access in global constraints with constant indices
// (IEEE 1800-2017 18.3) - Testing with primitive arrays

/* verilator lint_off WIDTHTRUNC */

class Inner;
  rand int m_vals[4];  // Primitive array
  rand int m_x;
endclass

class Outer;
  rand Inner m_obj;
  rand int m_arr[3];  // Primitive array at outer level

  function new();
    m_obj = new;
  endfunction

  // Case 1: Simple member access
  constraint c_simple {
    m_obj.m_x == 42;
  }

  // Case 2: Constraint on outer primitive array with constant index
  constraint c_outer_arr {
    m_arr[0] == 100;
    m_arr[1] == 200;
    m_arr[2] == 300;
  }

  // Case 3: Constraint on inner primitive array via member access with constant index
  constraint c_inner_arr {
    m_obj.m_vals[0] == 10;
    m_obj.m_vals[1] == 20;
    m_obj.m_vals[2] == 30;
    m_obj.m_vals[3] == 40;
  }
endclass

module t;
  initial begin
    Outer o = new;
    if (!o.randomize()) begin
      $display("*-* FAILED: randomize() returned 0 *-*");
      $stop;
    end

    $display("Case 1 - Simple: obj.x = %0d (expected 42)", o.m_obj.m_x);
    $display("Case 2 - Outer arr[0] = %0d (expected 100)", o.m_arr[0]);
    $display("Case 2 - Outer arr[1] = %0d (expected 200)", o.m_arr[1]);
    $display("Case 2 - Outer arr[2] = %0d (expected 300)", o.m_arr[2]);
    $display("Case 3 - Inner obj.vals[0] = %0d (expected 10)", o.m_obj.m_vals[0]);
    $display("Case 3 - Inner obj.vals[1] = %0d (expected 20)", o.m_obj.m_vals[1]);
    $display("Case 3 - Inner obj.vals[2] = %0d (expected 30)", o.m_obj.m_vals[2]);
    $display("Case 3 - Inner obj.vals[3] = %0d (expected 40)", o.m_obj.m_vals[3]);

    // Check results
    if (o.m_obj.m_x == 42 &&
        o.m_arr[0] == 100 && o.m_arr[1] == 200 && o.m_arr[2] == 300 &&
        o.m_obj.m_vals[0] == 10 && o.m_obj.m_vals[1] == 20 &&
        o.m_obj.m_vals[2] == 30 && o.m_obj.m_vals[3] == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $display("*-* FAILED *-*");
      $stop;
    end
  end
endmodule
