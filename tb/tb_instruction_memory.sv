// ============================================================================
// Instruction Memory Testbench - Industry Standard SystemVerilog Testbench
// ============================================================================

`timescale 1ns/1ps

module tb_instruction_memory;

    import riscv_pkg::*;
    
    // ========================================================================
    // Parameters
    // ========================================================================
    parameter int CLK_PERIOD = 10;
    parameter int MEM_SIZE = 256;
    parameter int ADDR_WIDTH = 32;
    parameter int DATA_WIDTH = 32;
    
    // ========================================================================
    // DUT Signals
    // ========================================================================
    logic                    clk;
    logic                    rst_n;
    logic [ADDR_WIDTH-1:0]   addr;
    logic [DATA_WIDTH-1:0]   data;
    logic                    valid;
    
    // ========================================================================
    // Test Variables
    // ========================================================================
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
    // ========================================================================
    // DUT Instantiation
    // ========================================================================
    instruction_memory #(
        .MEM_SIZE_BYTES(MEM_SIZE),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk_i      (clk),
        .rst_ni     (rst_n),
        .addr_i     (addr),
        .data_o     (data),
        .valid_o    (valid)
    );
    
    // ========================================================================
    // Clock Generation
    // ========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // ========================================================================
    // Task: Check Read
    // ========================================================================
    task automatic check_read(
        input logic [ADDR_WIDTH-1:0] address,
        input logic [DATA_WIDTH-1:0] expected,
        input string test_name
    );
        addr = address;
        @(posedge clk);
        #1;
        test_count++;
        
        if (data === expected && valid) begin
            pass_count++;
            $display("[PASS] Test %0d: %s | Addr=0x%08h, Data=0x%08h", 
                     test_count, test_name, address, data);
        end else begin
            fail_count++;
            $error("[FAIL] Test %0d: %s | Addr=0x%08h, Got=0x%08h, Expected=0x%08h, Valid=%0b", 
                   test_count, test_name, address, data, expected, valid);
        end
    endtask
    
    // ========================================================================
    // Main Test Sequence
    // ========================================================================
    initial begin
        $display("=================================================================");
        $display("Instruction Memory Testbench Started");
        $display("=================================================================");
        
        // Initialize
        rst_n = 0;
        addr = 0;
        
        // Reset
        repeat(3) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // ====================================================================
        // Test 1: Read Pre-loaded Instructions
        // ====================================================================
        $display("\n--- Test 1: Read Pre-loaded Instructions ---");
        check_read(32'h00000000, 32'h009403b3, "Instruction 0");
        check_read(32'h00000004, 32'h40b503b3, "Instruction 1");
        check_read(32'h00000008, 32'h02d602b3, "Instruction 2");
        check_read(32'h0000000C, 32'h0107c733, "Instruction 3");
        check_read(32'h00000010, 32'h013918b3, "Instruction 4");
        check_read(32'h00000014, 32'h016ada33, "Instruction 5");
        check_read(32'h00000018, 32'h019c7bb3, "Instruction 6");
        check_read(32'h0000001C, 32'h01cded33, "Instruction 7");
        
        // ====================================================================
        // Test 2: Sequential Access
        // ====================================================================
        $display("\n--- Test 2: Sequential Access ---");
        for (int i = 0; i < 32; i += 4) begin
            addr = i;
            @(posedge clk);
            #1;
            if (valid) begin
                $display("  Addr 0x%08h: Data = 0x%08h", addr, data);
            end
        end
        
        // ====================================================================
        // Test 3: Alignment Check
        // ====================================================================
        $display("\n--- Test 3: Unaligned Access (should be invalid) ---");
        addr = 32'h00000001;
        @(posedge clk);
        #1;
        test_count++;
        if (!valid) begin
            pass_count++;
            $display("[PASS] Unaligned access properly flagged as invalid");
        end else begin
            fail_count++;
            $error("[FAIL] Unaligned access should be invalid");
        end
        
        // ====================================================================
        // Test 4: Out of Range Access
        // ====================================================================
        $display("\n--- Test 4: Out of Range Access ---");
        addr = 32'h00000100;  // Beyond memory size
        @(posedge clk);
        #1;
        test_count++;
        if (!valid || data == 0) begin
            pass_count++;
            $display("[PASS] Out of range access handled correctly");
        end else begin
            fail_count++;
            $error("[FAIL] Out of range access not handled properly");
        end
        
        // ====================================================================
        // Test Summary
        // ====================================================================
        repeat(3) @(posedge clk);
        
        $display("\n=================================================================");
        $display("Instruction Memory Testbench Completed");
        $display("=================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %0.2f%%", (real'(pass_count) / real'(test_count)) * 100.0);
        $display("=================================================================");
        
        if (fail_count == 0) begin
            $display("*** ALL TESTS PASSED ***");
        end else begin
            $display("*** SOME TESTS FAILED ***");
        end
        
        $finish;
    end
    
    // ========================================================================
    // Timeout Watchdog
    // ========================================================================
    initial begin
        #1ms;
        $error("Testbench timeout!");
        $finish;
    end
    
    // ========================================================================
    // Waveform Dump
    // ========================================================================
    initial begin
        $dumpfile("sim/tb_instruction_memory.vcd");
        $dumpvars(0, tb_instruction_memory);
    end

endmodule : tb_instruction_memory
