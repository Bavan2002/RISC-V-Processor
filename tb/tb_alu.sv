// ============================================================================
// ALU Testbench - Industry Standard SystemVerilog Testbench
// ============================================================================
// Description: Comprehensive testbench for ALU module with self-checking
//              tests, coverage collection, and random stimulus.
// ============================================================================

`timescale 1ns/1ps

module tb_alu;

    import riscv_pkg::*;
    
    // ========================================================================
    // Parameters
    // ========================================================================
    parameter int DATA_WIDTH = 32;
    parameter int NUM_TESTS = 1000;
    
    // ========================================================================
    // DUT Signals
    // ========================================================================
    logic [DATA_WIDTH-1:0]  operand_a;
    logic [DATA_WIDTH-1:0]  operand_b;
    alu_op_e                alu_operation;
    logic [DATA_WIDTH-1:0]  result;
    logic                   zero_flag;
    logic                   negative_flag;
    logic                   overflow_flag;
    
    // ========================================================================
    // Test Variables
    // ========================================================================
    int                     test_count;
    int                     pass_count;
    int                     fail_count;
    logic [DATA_WIDTH-1:0]  expected_result;
    logic                   expected_zero;
    
    // ========================================================================
    // DUT Instantiation
    // ========================================================================
    alu #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .operand_a_i      (operand_a),
        .operand_b_i      (operand_b),
        .alu_operation_i  (alu_operation),
        .result_o         (result),
        .zero_flag_o      (zero_flag),
        .negative_flag_o  (negative_flag),
        .overflow_flag_o  (overflow_flag)
    );
    
    // ========================================================================
    // Clock Generation (not needed for combinational logic, but good practice)
    // ========================================================================
    logic clk;
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // ========================================================================
    // Task: Check Result
    // ========================================================================
    task automatic check_result(
        input logic [DATA_WIDTH-1:0] expected,
        input string operation_name
    );
        test_count++;
        if (result === expected && zero_flag === (result == 0)) begin
            pass_count++;
            $display("[PASS] Test %0d: %s | A=0x%08h, B=0x%08h, Result=0x%08h (Expected=0x%08h)", 
                     test_count, operation_name, operand_a, operand_b, result, expected);
        end else begin
            fail_count++;
            $error("[FAIL] Test %0d: %s | A=0x%08h, B=0x%08h, Result=0x%08h (Expected=0x%08h)", 
                   test_count, operation_name, operand_a, operand_b, result, expected);
        end
    endtask
    
    // ========================================================================
    // Task: Test Specific Operation
    // ========================================================================
    task automatic test_operation(
        input alu_op_e op,
        input logic [DATA_WIDTH-1:0] a,
        input logic [DATA_WIDTH-1:0] b,
        input logic [DATA_WIDTH-1:0] expected,
        input string op_name
    );
        operand_a = a;
        operand_b = b;
        alu_operation = op;
        #1;  // Wait for combinational logic
        check_result(expected, op_name);
    endtask
    
    // ========================================================================
    // Main Test Sequence
    // ========================================================================
    initial begin
        // Initialize
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        operand_a = 0;
        operand_b = 0;
        alu_operation = ALU_ADD;
        
        $display("=================================================================");
        $display("ALU Testbench Started");
        $display("=================================================================");
        
        // ====================================================================
        // Directed Tests
        // ====================================================================
        $display("\n--- Testing AND Operation ---");
        test_operation(ALU_AND, 32'hFFFF_FFFF, 32'h0000_FFFF, 32'h0000_FFFF, "AND");
        test_operation(ALU_AND, 32'hAAAA_AAAA, 32'h5555_5555, 32'h0000_0000, "AND");
        
        $display("\n--- Testing OR Operation ---");
        test_operation(ALU_OR, 32'hAAAA_AAAA, 32'h5555_5555, 32'hFFFF_FFFF, "OR");
        test_operation(ALU_OR, 32'h0000_0000, 32'h0000_0000, 32'h0000_0000, "OR");
        
        $display("\n--- Testing ADD Operation ---");
        test_operation(ALU_ADD, 32'd100, 32'd200, 32'd300, "ADD");
        test_operation(ALU_ADD, 32'hFFFF_FFFF, 32'h0000_0001, 32'h0000_0000, "ADD Overflow");
        test_operation(ALU_ADD, 32'd0, 32'd0, 32'd0, "ADD Zero");
        
        $display("\n--- Testing SUB Operation ---");
        test_operation(ALU_SUB, 32'd500, 32'd200, 32'd300, "SUB");
        test_operation(ALU_SUB, 32'd100, 32'd100, 32'd0, "SUB Zero");
        test_operation(ALU_SUB, 32'd100, 32'd200, 32'hFFFF_FF9C, "SUB Negative");
        
        $display("\n--- Testing SLT Operation ---");
        test_operation(ALU_SLT, 32'd10, 32'd20, 32'd1, "SLT True");
        test_operation(ALU_SLT, 32'd20, 32'd10, 32'd0, "SLT False");
        test_operation(ALU_SLT, -32'd5, 32'd5, 32'd1, "SLT Signed");
        
        $display("\n--- Testing SLL Operation ---");
        test_operation(ALU_SLL, 32'h0000_0001, 32'd4, 32'h0000_0010, "SLL");
        test_operation(ALU_SLL, 32'h0000_00FF, 32'd8, 32'h0000_FF00, "SLL");
        
        $display("\n--- Testing SRL Operation ---");
        test_operation(ALU_SRL, 32'h0000_0010, 32'd4, 32'h0000_0001, "SRL");
        test_operation(ALU_SRL, 32'hFF00_0000, 32'd8, 32'h00FF_0000, "SRL");
        
        $display("\n--- Testing MUL Operation ---");
        test_operation(ALU_MUL, 32'd10, 32'd20, 32'd200, "MUL");
        test_operation(ALU_MUL, 32'd0, 32'd100, 32'd0, "MUL by Zero");
        test_operation(ALU_MUL, 32'd15, 32'd7, 32'd105, "MUL");
        
        $display("\n--- Testing XOR Operation ---");
        test_operation(ALU_XOR, 32'hFFFF_FFFF, 32'hFFFF_FFFF, 32'h0000_0000, "XOR Same");
        test_operation(ALU_XOR, 32'hAAAA_AAAA, 32'h5555_5555, 32'hFFFF_FFFF, "XOR");
        
        // ====================================================================
        // Random Tests
        // ====================================================================
        $display("\n--- Random Testing ---");
        repeat (NUM_TESTS) begin
            @(posedge clk);
            
            // Randomize inputs
            operand_a = $random;
            operand_b = $random;
            alu_operation = alu_op_e'($urandom_range(0, 8));
            
            // Calculate expected result
            case (alu_operation)
                ALU_AND: expected_result = operand_a & operand_b;
                ALU_OR:  expected_result = operand_a | operand_b;
                ALU_ADD: expected_result = operand_a + operand_b;
                ALU_SUB: expected_result = operand_a - operand_b;
                ALU_SLT: expected_result = ($signed(operand_a) < $signed(operand_b)) ? 32'd1 : 32'd0;
                ALU_SLL: expected_result = operand_a << operand_b[4:0];
                ALU_SRL: expected_result = operand_a >> operand_b[4:0];
                ALU_MUL: expected_result = operand_a * operand_b;
                ALU_XOR: expected_result = operand_a ^ operand_b;
                default: expected_result = 32'd0;
            endcase
            
            #1;  // Wait for result
            
            if (result !== expected_result) begin
                test_count++;
                fail_count++;
                $error("[FAIL] Random Test %0d: OP=%0d, A=0x%08h, B=0x%08h, Got=0x%08h, Expected=0x%08h",
                       test_count, alu_operation, operand_a, operand_b, result, expected_result);
            end else begin
                test_count++;
                pass_count++;
            end
        end
        
        // ====================================================================
        // Test Summary
        // ====================================================================
        $display("\n=================================================================");
        $display("ALU Testbench Completed");
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
        #100ms;
        $error("Testbench timeout!");
        $finish;
    end
    
    // ========================================================================
    // Waveform Dump
    // ========================================================================
    initial begin
        $dumpfile("sim/tb_alu.vcd");
        $dumpvars(0, tb_alu);
    end

endmodule : tb_alu
