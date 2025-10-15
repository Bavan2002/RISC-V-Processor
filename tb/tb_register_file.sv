// ============================================================================
// Register File Testbench - Industry Standard SystemVerilog Testbench
// ============================================================================
// Description: Comprehensive testbench for register file with self-checking
//              tests and corner case verification.
// ============================================================================

`timescale 1ns/1ps

module tb_register_file;

    import riscv_pkg::*;
    
    // ========================================================================
    // Parameters
    // ========================================================================
    parameter int DATA_WIDTH = 32;
    parameter int NUM_REGS = 32;
    parameter int ADDR_WIDTH = 5;
    parameter int CLK_PERIOD = 10;
    
    // ========================================================================
    // DUT Signals
    // ========================================================================
    logic                    clk;
    logic                    rst_n;
    logic [ADDR_WIDTH-1:0]   rd_addr1;
    logic [DATA_WIDTH-1:0]   rd_data1;
    logic [ADDR_WIDTH-1:0]   rd_addr2;
    logic [DATA_WIDTH-1:0]   rd_data2;
    logic                    wr_enable;
    logic [ADDR_WIDTH-1:0]   wr_addr;
    logic [DATA_WIDTH-1:0]   wr_data;
    
    // ========================================================================
    // Test Variables
    // ========================================================================
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
    // ========================================================================
    // DUT Instantiation
    // ========================================================================
    register_file #(
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_REGS(NUM_REGS),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) dut (
        .clk_i          (clk),
        .rst_ni         (rst_n),
        .rd_addr1_i     (rd_addr1),
        .rd_data1_o     (rd_data1),
        .rd_addr2_i     (rd_addr2),
        .rd_data2_o     (rd_data2),
        .wr_enable_i    (wr_enable),
        .wr_addr_i      (wr_addr),
        .wr_data_i      (wr_data)
    );
    
    // ========================================================================
    // Clock Generation
    // ========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // ========================================================================
    // Task: Check Read Data
    // ========================================================================
    task automatic check_read(
        input int port,
        input logic [DATA_WIDTH-1:0] expected,
        input string test_name
    );
        logic [DATA_WIDTH-1:0] actual;
        actual = (port == 1) ? rd_data1 : rd_data2;
        test_count++;
        
        if (actual === expected) begin
            pass_count++;
            $display("[PASS] Test %0d: %s | Port%0d = 0x%08h (Expected: 0x%08h)", 
                     test_count, test_name, port, actual, expected);
        end else begin
            fail_count++;
            $error("[FAIL] Test %0d: %s | Port%0d = 0x%08h (Expected: 0x%08h)", 
                   test_count, test_name, port, actual, expected);
        end
    endtask
    
    // ========================================================================
    // Task: Write Register
    // ========================================================================
    task automatic write_register(
        input logic [ADDR_WIDTH-1:0] addr,
        input logic [DATA_WIDTH-1:0] data
    );
        @(posedge clk);
        wr_enable = 1'b1;
        wr_addr = addr;
        wr_data = data;
        @(posedge clk);
        wr_enable = 1'b0;
    endtask
    
    // ========================================================================
    // Task: Read Register
    // ========================================================================
    task automatic read_register(
        input logic [ADDR_WIDTH-1:0] addr,
        input int port
    );
        if (port == 1) begin
            rd_addr1 = addr;
        end else begin
            rd_addr2 = addr;
        end
        #1;  // Wait for combinational read
    endtask
    
    // ========================================================================
    // Main Test Sequence
    // ========================================================================
    initial begin
        // Initialize
        logic [DATA_WIDTH-1:0] expected_values [NUM_REGS];
        rst_n = 0;
        wr_enable = 0;
        wr_addr = 0;
        wr_data = 0;
        rd_addr1 = 0;
        rd_addr2 = 0;
        
        $display("=================================================================");
        $display("Register File Testbench Started");
        $display("=================================================================");
        
        // Reset
        repeat(2) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // ====================================================================
        // Test 1: Initial Values After Reset
        // ====================================================================
        $display("\n--- Test 1: Initial Values After Reset ---");
        for (int i = 0; i < NUM_REGS; i++) begin
            read_register(i, 1);
            check_read(1, i, $sformatf("Initial x%0d", i));
        end
        
        // ====================================================================
        // Test 2: x0 Always Zero
        // ====================================================================
        $display("\n--- Test 2: x0 Hardwired to Zero ---");
        write_register(0, 32'hDEAD_BEEF);
        read_register(0, 1);
        check_read(1, 32'h0000_0000, "Write to x0 ignored");
        
        // ====================================================================
        // Test 3: Write and Read Back
        // ====================================================================
        $display("\n--- Test 3: Write and Read Back ---");
        for (int i = 1; i < NUM_REGS; i++) begin
            logic [DATA_WIDTH-1:0] test_value;
            test_value = $random;
            write_register(i, test_value);
            read_register(i, 1);
            check_read(1, test_value, $sformatf("Write/Read x%0d", i));
        end
        
        // ====================================================================
        // Test 4: Dual Port Read
        // ====================================================================
        $display("\n--- Test 4: Dual Port Simultaneous Read ---");
        write_register(5, 32'hAAAA_AAAA);
        write_register(10, 32'h5555_5555);
        
        rd_addr1 = 5;
        rd_addr2 = 10;
        #1;
        check_read(1, 32'hAAAA_AAAA, "Dual Read Port 1");
        check_read(2, 32'h5555_5555, "Dual Read Port 2");
        
        // ====================================================================
        // Test 5: Write During Read (No Bypass)
        // ====================================================================
        $display("\n--- Test 5: Write Timing ---");
        write_register(15, 32'h1234_5678);
        rd_addr1 = 15;
        #1;
        check_read(1, 32'h1234_5678, "Read after write");
        
        // ====================================================================
        // Test 6: All Registers Different Values
        // ====================================================================
        $display("\n--- Test 6: Pattern Test ---");
        // Write pattern
        for (int i = 1; i < NUM_REGS; i++) begin
            write_register(i, 32'hA000_0000 | i);
        end
        
        // Verify pattern
        for (int i = 1; i < NUM_REGS; i++) begin
            read_register(i, 1);
            check_read(1, 32'hA000_0000 | i, $sformatf("Pattern x%0d", i));
        end
        
        // ====================================================================
        // Test 7: Boundary Values
        // ====================================================================
        $display("\n--- Test 7: Boundary Values ---");
        write_register(31, 32'hFFFF_FFFF);
        read_register(31, 1);
        check_read(1, 32'hFFFF_FFFF, "Max value");
        
        write_register(1, 32'h0000_0000);
        read_register(1, 1);
        check_read(1, 32'h0000_0000, "Min value");
        
        // ====================================================================
        // Test 8: Random Access Pattern
        // ====================================================================
        $display("\n--- Test 8: Random Access Pattern ---");
        
        // Initialize expected values to current register state after pattern test
        for (int i = 0; i < NUM_REGS; i++) begin
            if (i == 0) begin
                expected_values[i] = 32'h0000_0000;  // x0 is always 0
            end else begin
                expected_values[i] = 32'hA000_0000 | i;  // From pattern test
            end
        end
        
        // Random writes
        repeat(100) begin
            int addr;
            logic [DATA_WIDTH-1:0] data;
            
            addr = $urandom_range(1, NUM_REGS-1);  // Avoid x0
            data = $random;
            
            write_register(addr, data);
            expected_values[addr] = data;
        end
        
        // Verify all registers
        for (int i = 0; i < NUM_REGS; i++) begin
            read_register(i, 1);
            check_read(1, expected_values[i], $sformatf("Random x%0d", i));
        end
        
        // ====================================================================
        // Test 9: Write Enable Control
        // ====================================================================
        $display("\n--- Test 9: Write Enable Control ---");
        write_register(20, 32'hCAFE_BABE);
        read_register(20, 1);
        check_read(1, 32'hCAFE_BABE, "Write enable high");
        
        @(posedge clk);
        wr_enable = 1'b0;
        wr_addr = 20;
        wr_data = 32'hDEAD_BEEF;
        @(posedge clk);
        
        read_register(20, 1);
        check_read(1, 32'hCAFE_BABE, "Write enable low (no change)");
        
        // ====================================================================
        // Test Summary
        // ====================================================================
        repeat(5) @(posedge clk);
        
        $display("\n=================================================================");
        $display("Register File Testbench Completed");
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
        #10ms;
        $error("Testbench timeout!");
        $finish;
    end
    
    // ========================================================================
    // Waveform Dump (Disabled for Vivado - use built-in waveform viewer)
    // ========================================================================
    // Vivado/Xsim automatically captures waveforms

endmodule : tb_register_file
