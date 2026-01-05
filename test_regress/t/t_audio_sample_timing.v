// DESCRIPTION: Verilator: Test audio-style sample timing and FIFO patterns
// Tests I2S-like word select timing and stereo channel synchronization
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module t;
   // Audio format enum
   typedef enum bit [1:0] {
      FMT_8BIT  = 2'b00,
      FMT_16BIT = 2'b01,
      FMT_24BIT = 2'b10,
      FMT_32BIT = 2'b11
   } audio_format_e;

   // Channel enum
   typedef enum bit {
      CH_LEFT  = 1'b1,
      CH_RIGHT = 1'b0
   } channel_e;

   // Audio sample with metadata
   class AudioSample;
      bit [31:0] data;
      channel_e channel;
      audio_format_e format;
      int sample_index;

      function new();
         data = 0;
         channel = CH_LEFT;
         format = FMT_16BIT;
         sample_index = 0;
      endfunction

      function int get_bit_width();
         case (format)
            FMT_8BIT:  return 8;
            FMT_16BIT: return 16;
            FMT_24BIT: return 24;
            FMT_32BIT: return 32;
         endcase
      endfunction

      function bit [31:0] get_masked_data();
         return data & ((1 << get_bit_width()) - 1);
      endfunction
   endclass

   // Audio FIFO with overflow/underflow detection
   class AudioFIFO #(int DEPTH = 4);
      AudioSample buffer[$];
      int max_depth;
      int overflow_count;
      int underflow_count;

      function new();
         max_depth = DEPTH;
         overflow_count = 0;
         underflow_count = 0;
      endfunction

      function void push(AudioSample sample);
         if (buffer.size() >= max_depth) begin
            overflow_count++;
            $display("  WARNING: FIFO overflow (size=%0d, max=%0d)", buffer.size(), max_depth);
            // Drop oldest sample
            void'(buffer.pop_front());
         end
         buffer.push_back(sample);
      endfunction

      function AudioSample pop();
         AudioSample sample;
         if (buffer.size() == 0) begin
            underflow_count++;
            $display("  WARNING: FIFO underflow");
            sample = new();  // Return empty sample
            return sample;
         end
         sample = buffer.pop_front();
         return sample;
      endfunction

      function int size();
         return buffer.size();
      endfunction

      function bit is_empty();
         return buffer.size() == 0;
      endfunction

      function bit is_full();
         return buffer.size() >= max_depth;
      endfunction

      function void clear();
         buffer.delete();
      endfunction
   endclass

   // Word Select timing monitor
   class WSTimingMonitor;
      int ws_period_clocks;
      int expected_ws_period;
      int timing_errors;
      channel_e current_channel;
      int clocks_since_toggle;

      function new(int expected_period);
         expected_ws_period = expected_period;
         timing_errors = 0;
         current_channel = CH_LEFT;
         clocks_since_toggle = 0;
      endfunction

      function void clock_tick(bit ws_signal);
         channel_e detected_channel = channel_e'(ws_signal);

         if (detected_channel != current_channel) begin
            // WS toggled
            if (clocks_since_toggle != 0 && clocks_since_toggle != expected_ws_period) begin
               // Allow first toggle to be any time
               if (clocks_since_toggle > 0) begin
                  timing_errors++;
                  $display("  ERROR: WS period mismatch - expected %0d, got %0d",
                           expected_ws_period, clocks_since_toggle);
               end
            end
            ws_period_clocks = clocks_since_toggle;
            clocks_since_toggle = 0;
            current_channel = detected_channel;
         end

         clocks_since_toggle++;
      endfunction

      function int get_timing_errors();
         return timing_errors;
      endfunction
   endclass

   // Stereo pair validator
   class StereoPairValidator;
      AudioSample left_sample;
      AudioSample right_sample;
      bit has_left;
      bit has_right;
      int pair_count;
      int mismatch_count;

      function new();
         has_left = 0;
         has_right = 0;
         pair_count = 0;
         mismatch_count = 0;
      endfunction

      function void receive_sample(AudioSample sample);
         if (sample.channel == CH_LEFT) begin
            left_sample = sample;
            has_left = 1;
         end else begin
            right_sample = sample;
            has_right = 1;
         end

         // Check if we have a complete stereo pair
         if (has_left && has_right) begin
            pair_count++;

            // Validate: formats should match within a pair
            if (left_sample.format != right_sample.format) begin
               mismatch_count++;
               $display("  ERROR: Format mismatch in stereo pair %0d (L=%s, R=%s)",
                        pair_count, left_sample.format.name(), right_sample.format.name());
            end

            // Reset for next pair
            has_left = 0;
            has_right = 0;
         end
      endfunction

      function int get_pair_count();
         return pair_count;
      endfunction

      function int get_mismatch_count();
         return mismatch_count;
      endfunction
   endclass

   // Clock generation
   reg clk = 0;
   always #10 clk = ~clk;  // 50MHz SCLK

   // Test signals
   reg ws = 1;  // Word select (1=left, 0=right)
   reg [31:0] sd = 0;  // Serial data

   initial begin
      AudioFIFO #(4) tx_fifo;
      AudioFIFO #(4) rx_fifo;
      WSTimingMonitor ws_mon;
      StereoPairValidator stereo_val;
      AudioSample sample;
      int pass_count = 0;
      int test_count = 0;

      tx_fifo = new();
      rx_fifo = new();

      // Test 1: Basic FIFO operations
      $display("Test 1: Audio FIFO basic operations");
      test_count++;

      for (int i = 0; i < 3; i++) begin
         sample = new();
         sample.data = 32'h1000 + i;
         sample.channel = (i % 2) ? CH_RIGHT : CH_LEFT;
         sample.format = FMT_16BIT;
         sample.sample_index = i;
         tx_fifo.push(sample);
      end

      if (tx_fifo.size() == 3 && !tx_fifo.is_full() && !tx_fifo.is_empty()) begin
         $display("  PASS: FIFO has 3 samples, not full, not empty");
         pass_count++;
      end else begin
         $display("  FAIL: FIFO state incorrect (size=%0d)", tx_fifo.size());
      end

      // Test 2: FIFO overflow detection
      $display("Test 2: FIFO overflow detection");
      test_count++;

      tx_fifo.clear();
      tx_fifo.overflow_count = 0;

      // Push 6 samples into 4-deep FIFO
      for (int i = 0; i < 6; i++) begin
         sample = new();
         sample.data = i;
         tx_fifo.push(sample);
      end

      if (tx_fifo.overflow_count == 2 && tx_fifo.size() == 4) begin
         $display("  PASS: Detected %0d overflows, FIFO capped at %0d",
                  tx_fifo.overflow_count, tx_fifo.size());
         pass_count++;
      end else begin
         $display("  FAIL: overflow_count=%0d, size=%0d",
                  tx_fifo.overflow_count, tx_fifo.size());
      end

      // Test 3: FIFO underflow detection
      $display("Test 3: FIFO underflow detection");
      test_count++;

      rx_fifo.clear();
      rx_fifo.underflow_count = 0;

      // Try to pop from empty FIFO
      sample = rx_fifo.pop();
      sample = rx_fifo.pop();

      if (rx_fifo.underflow_count == 2) begin
         $display("  PASS: Detected %0d underflows", rx_fifo.underflow_count);
         pass_count++;
      end else begin
         $display("  FAIL: underflow_count=%0d", rx_fifo.underflow_count);
      end

      // Test 4: Word Select timing monitor
      $display("Test 4: WS timing monitor (16-clock period)");
      test_count++;

      ws_mon = new(16);  // Expect WS to toggle every 16 clocks

      // Simulate correct WS timing
      for (int frame = 0; frame < 4; frame++) begin
         for (int i = 0; i < 16; i++) begin
            ws_mon.clock_tick(1);  // Left channel
            @(posedge clk);
         end
         for (int i = 0; i < 16; i++) begin
            ws_mon.clock_tick(0);  // Right channel
            @(posedge clk);
         end
      end

      if (ws_mon.get_timing_errors() == 0) begin
         $display("  PASS: No WS timing errors");
         pass_count++;
      end else begin
         $display("  FAIL: %0d WS timing errors", ws_mon.get_timing_errors());
      end

      // Test 5: WS timing violation detection
      $display("Test 5: WS timing violation detection");
      test_count++;

      ws_mon = new(16);

      // Simulate incorrect timing (10 clocks instead of 16)
      for (int i = 0; i < 16; i++) begin
         ws_mon.clock_tick(1);
         @(posedge clk);
      end
      for (int i = 0; i < 10; i++) begin  // Only 10 clocks - violation!
         ws_mon.clock_tick(0);
         @(posedge clk);
      end
      for (int i = 0; i < 16; i++) begin
         ws_mon.clock_tick(1);
         @(posedge clk);
      end

      if (ws_mon.get_timing_errors() == 1) begin
         $display("  PASS: Detected WS timing violation");
         pass_count++;
      end else begin
         $display("  FAIL: timing_errors=%0d (expected 1)", ws_mon.get_timing_errors());
      end

      // Test 6: Stereo pair validation
      $display("Test 6: Stereo pair validation");
      test_count++;

      stereo_val = new();

      // Send matching stereo pairs
      for (int i = 0; i < 4; i++) begin
         sample = new();
         sample.data = 32'hABCD_0000 + i;
         sample.channel = CH_LEFT;
         sample.format = FMT_16BIT;
         stereo_val.receive_sample(sample);

         sample = new();
         sample.data = 32'h1234_0000 + i;
         sample.channel = CH_RIGHT;
         sample.format = FMT_16BIT;
         stereo_val.receive_sample(sample);
      end

      if (stereo_val.get_pair_count() == 4 && stereo_val.get_mismatch_count() == 0) begin
         $display("  PASS: 4 stereo pairs validated, no mismatches");
         pass_count++;
      end else begin
         $display("  FAIL: pairs=%0d, mismatches=%0d",
                  stereo_val.get_pair_count(), stereo_val.get_mismatch_count());
      end

      // Test 7: Stereo format mismatch detection
      $display("Test 7: Stereo format mismatch detection");
      test_count++;

      stereo_val = new();

      // Send mismatched stereo pair
      sample = new();
      sample.channel = CH_LEFT;
      sample.format = FMT_16BIT;
      stereo_val.receive_sample(sample);

      sample = new();
      sample.channel = CH_RIGHT;
      sample.format = FMT_24BIT;  // Different format!
      stereo_val.receive_sample(sample);

      if (stereo_val.get_mismatch_count() == 1) begin
         $display("  PASS: Detected stereo format mismatch");
         pass_count++;
      end else begin
         $display("  FAIL: mismatch_count=%0d (expected 1)", stereo_val.get_mismatch_count());
      end

      // Test 8: Multiple audio formats
      $display("Test 8: Audio sample bit widths");
      test_count++;

      sample = new();
      sample.data = 32'hFFFFFFFF;

      sample.format = FMT_8BIT;
      if (sample.get_bit_width() != 8 || sample.get_masked_data() != 32'hFF) begin
         $display("  FAIL: 8-bit format incorrect");
      end else begin
         sample.format = FMT_16BIT;
         if (sample.get_bit_width() != 16 || sample.get_masked_data() != 32'hFFFF) begin
            $display("  FAIL: 16-bit format incorrect");
         end else begin
            sample.format = FMT_24BIT;
            if (sample.get_bit_width() != 24 || sample.get_masked_data() != 32'hFFFFFF) begin
               $display("  FAIL: 24-bit format incorrect");
            end else begin
               sample.format = FMT_32BIT;
               if (sample.get_bit_width() != 32 || sample.get_masked_data() != 32'hFFFFFFFF) begin
                  $display("  FAIL: 32-bit format incorrect");
               end else begin
                  $display("  PASS: All audio formats correct");
                  pass_count++;
               end
            end
         end
      end

      // Summary
      $display("");
      $display("Results: %0d/%0d tests passed", pass_count, test_count);

      if (pass_count == test_count) begin
         $display("*-* All Finished *-*");
      end else begin
         $display("FAIL: Some tests failed");
         $stop;
      end
      $finish;
   end

endmodule
