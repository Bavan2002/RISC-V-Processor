// ============================================================================
// RISC-V Core Testbench - Industry Standard SystemVerilog Testbench
// ============================================================================
// Description: Top-level testbench for complete RISC-V processor.
//              Tests instruction execution and validates results.
// ============================================================================

`timescale 1ns/1ps

module tb_riscv_core;

    import riscv_pkg::*;
    
    // ========================================================================
    // Parameters
    // ========================================================================
    parameter int CLK_PERIOD = 10;
    parameter int DATA_WIDTH = 32;
    
    // ========================================================================
    // DUT Signals
    // ========================================================================
    logic                    clk;
    logic                    rst_n;
    logic                    zero_flag;
    logic [DATA_WIDTH-1:0]   pc;
    logic [DATA_WIDTH-1:0]   instruction;
    
    // ========================================================================
    // Test Variables
    // ========================================================================
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    int cycle_count = 0;
    
    // ========================================================================
    // DUT Instantiation
    // ========================================================================
    riscv_core #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk_i          (clk),
        .rst_ni         (rst_n),
        .zero_flag_o    (zero_flag),
        .pc_o           (pc),
        .instruction_o  (instruction)
    );
    
    // ========================================================================
    // Clock Generation
    // ========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // ========================================================================
    // Task: Check Register Value
    // ========================================================================
    task automatic check_register(
        input int reg_num,
        input logic [DATA_WIDTH-1:0] expected,
        input string test_name
    );
        logic [DATA_WIDTH-1:0] actual;
        actual = dut.u_register_file.registers[reg_num];
        test_count++;
        
        if (actual === expected) begin
            pass_count++;
            $display("[PASS] Test %0d: %s | x%0d = 0x%08h (Expected: 0x%08h)", 
                     test_count, test_name, reg_num, actual, expected);
        end else begin
            fail_count++;
            $error("[FAIL] Test %0d: %s | x%0d = 0x%08h (Expected: 0x%08h)", 
                   test_count, test_name, reg_num, actual, expected);
        end
    endtask
    
    // ========================================================================
    // Task: Wait for Cycles
    // ========================================================================
    task automatic wait_cycles(input int num_cycles);
        repeat(num_cycles) @(posedge clk);
    endtask
    
    // ========================================================================
    // Task: Display Processor State
    // ========================================================================
    task automatic display_state();
        $display("\n--- Processor State at Cycle %0d ---", cycle_count);
        $display("PC:          0x%08h", pc);
        $display("Instruction: 0x%08h", instruction);
        $display("Zero Flag:   %0b", zero_flag);
        
        $display("\nRegister File:");
        for (int i = 0; i < 32; i += 4) begin
            $display("x%02d=0x%08h  x%02d=0x%08h  x%02d=0x%08h  x%02d=0x%08h",
                     i,   dut.u_register_file.registers[i],
                     i+1, dut.u_register_file.registers[i+1],
                     i+2, dut.u_register_file.registers[i+2],
                     i+3, dut.u_register_file.registers[i+3]);
        end
        $display("");
    endtask
    
    // ========================================================================
    // Main Test Sequence
    // ========================================================================
    initial begin
        $display("=================================================================");
        $display("RISC-V Core Testbench Started");
        $display("=================================================================");
        
        // Initialize
        rst_n = 0;
        cycle_count = 0;
        
        // Reset sequence
        $display("\n--- Applying Reset ---");
        repeat(5) @(posedge clk);
        rst_n = 1;
        @(posedge clk);  // Let reset propagate
        
        $display("--- Reset Released ---");
        display_state();
        
        // ====================================================================
        // Execute Test Program
        // ====================================================================
        $display("\n=================================================================");
        $display("Executing Test Program");
        $display("=================================================================");
        
        // The instruction memory contains:
        // 0: ADD x6, x8, x9   -> x6 = x8 + x9 = 0x8 + 0x9 = 0x11
        // 1: SUB x7, x10, x11 -> x7 = x10 - x11 = 0xA - 0xB = 0xFFFFFFFF (-1)
        // 2: MUL x5, x12, x13 -> x5 = x12 * x13 = 0xC * 0xD = 0x9C
        // 3: XOR x14, x15, x16 -> x14 = x15 ^ x16 = 0xF ^ 0x10 = 0x1F
        // 4: SLL x17, x18, x19 -> x17 = x18 << x19 = 0x12 << 19 = 0x00900000
        // 5: SRL x20, x21, x22 -> x20 = x21 >> x22 = 0x15 >> 22 = 0
        // 6: AND x23, x24, x25 -> x23 = x24 & x25 = 0x18 & 0x19 = 0x18
        // 7: OR x26, x27, x28  -> x26 = x27 | x28 = 0x1B | 0x1C = 0x1F
        
        // Execute instruction 0: ADD x6, x8, x9
        $display("\n--- Instruction 0: ADD x6, x8, x9 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        check_register(6, 32'h00000011, "ADD x6, x8, x9");
        
        // Execute instruction 1: SUB x7, x10, x11
        $display("\n--- Instruction 1: SUB x7, x10, x11 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        check_register(7, 32'hFFFFFFFF, "SUB x7, x10, x11");
        
        // Execute instruction 2: MUL x5, x12, x13
        $display("\n--- Instruction 2: MUL x5, x12, x13 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        check_register(5, 32'h0000009C, "MUL x5, x12, x13");
        
        // Execute instruction 3: XOR x14, x15, x16
        $display("\n--- Instruction 3: XOR x14, x15, x16 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        check_register(14, 32'h0000001F, "XOR x14, x15, x16");
        
        // Execute instruction 4: SLL x17, x18, x19
        $display("\n--- Instruction 4: SLL x17, x18, x19 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        // x18 = 0x12, x19 = 0x13, 0x12 << (0x13 & 0x1F) = 0x12 << 19 = 0x00900000
        check_register(17, 32'h00900000, "SLL x17, x18, x19");
        
        // Execute instruction 5: SRL x20, x21, x22
        $display("\n--- Instruction 5: SRL x20, x21, x22 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        // x21 = 0x15, x22 = 0x16, 0x15 >> (0x16 & 0x1F) = 0x15 >> 22 = 0
        check_register(20, 32'h00000000, "SRL x20, x21, x22");
        
        // Execute instruction 6: AND x23, x24, x25
        $display("\n--- Instruction 6: AND x23, x24, x25 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        // x24 = 0x18, x25 = 0x19, 0x18 & 0x19 = 0x18
        check_register(23, 32'h00000018, "AND x23, x24, x25");
        
        // Execute instruction 7: OR x26, x27, x28
        $display("\n--- Instruction 7: OR x26, x27, x28 ---");
        @(posedge clk);
        cycle_count++;
        display_state();
        // x27 = 0x1B, x28 = 0x1C, 0x1B | 0x1C = 0x1F
        check_register(26, 32'h0000001F, "OR x26, x27, x28");
        
        // ====================================================================
        // Additional Verification Tests
        // ====================================================================
        $display("\n=================================================================");
        $display("Additional Verification");
        $display("=================================================================");
        
        // Verify x0 is still zero
        check_register(0, 32'h00000000, "x0 always zero");
        
        // Verify PC progression
        // After 8 instructions (PC: 0x00→0x04→0x08→0x0C→0x10→0x14→0x18→0x1C→0x20)
        // PC should now be at 0x20
        test_count++;
        if (pc == 32'h00000020) begin
            pass_count++;
            $display("[PASS] PC progression correct: 0x%08h", pc);
        end else begin
            fail_count++;
            $error("[FAIL] PC progression incorrect: 0x%08h (Expected: 0x00000020)", pc);
        end
        
        // ====================================================================
        // Test Summary
        // ====================================================================
        wait_cycles(5);
        
        $display("\n=================================================================");
        $display("RISC-V Core Testbench Completed");
        $display("=================================================================");
        $display("Total Cycles:     %0d", cycle_count);
        $display("Total Tests:      %0d", test_count);
        $display("Passed:           %0d", pass_count);
        $display("Failed:           %0d", fail_count);
        $display("Pass Rate:        %0.2f%%", (real'(pass_count) / real'(test_count)) * 100.0);
        $display("=================================================================");
        
        if (fail_count == 0) begin
            $display("*** ALL TESTS PASSED ***");
        end else begin
            $display("*** SOME TESTS FAILED ***");
        end
        
        $finish;
    end
    
    // ========================================================================
    // Cycle Counter
    // ========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            // Count active cycles
        end
    end
    
    // ========================================================================
    // Instruction Monitor
    // ========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            $display("[Cycle %0d] PC=0x%08h, INST=0x%08h", 
                     cycle_count, pc, instruction);
        end
    end
    
    // ========================================================================
    // Timeout Watchdog
    // ========================================================================
    initial begin
        #10ms;
        $error("Testbench timeout!");
        $finish;
    end
    
    // ========================================================================
    // Waveform Dump (Disabled for Vivado - use built-in waveform viewer)
    // ========================================================================
    // Vivado/Xsim automatically captures waveforms
    // No need for $dumpfile/$dumpvars

endmodule : tb_riscv_core
