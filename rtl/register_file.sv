// ============================================================================
// Register File - SystemVerilog Implementation
// ============================================================================
// Description: 32-entry register file with dual read ports and single write
//              port. Register x0 is hardwired to zero per RISC-V spec.
// ============================================================================

module register_file 
import riscv_pkg::*;
#(
    parameter int DATA_WIDTH = 32,
    parameter int NUM_REGS   = 32,
    parameter int ADDR_WIDTH = 5
) (
    // Clock and Reset
    input  logic                    clk_i,
    input  logic                    rst_ni,      // Active low reset
    
    // Read Port 1
    input  logic [ADDR_WIDTH-1:0]   rd_addr1_i,
    output logic [DATA_WIDTH-1:0]   rd_data1_o,
    
    // Read Port 2
    input  logic [ADDR_WIDTH-1:0]   rd_addr2_i,
    output logic [DATA_WIDTH-1:0]   rd_data2_o,
    
    // Write Port
    input  logic                    wr_enable_i,
    input  logic [ADDR_WIDTH-1:0]   wr_addr_i,
    input  logic [DATA_WIDTH-1:0]   wr_data_i
);

    // ========================================================================
    // Register Array
    // ========================================================================
    logic [DATA_WIDTH-1:0] registers [NUM_REGS];
    
    // ========================================================================
    // Register Initialization and Write Logic
    // ========================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // Initialize registers on reset
            for (int i = 0; i < NUM_REGS; i++) begin
                registers[i] <= DATA_WIDTH'(i);  // Initialize with index values
            end
            // Ensure x0 is always zero
            registers[0] <= '0;
        end else begin
            // Write operation
            if (wr_enable_i && (wr_addr_i != '0)) begin
                // x0 cannot be written (hardwired to 0)
                registers[wr_addr_i] <= wr_data_i;
            end
            // Always enforce x0 = 0
            registers[0] <= '0;
        end
    end
    
    // ========================================================================
    // Asynchronous Read Logic
    // ========================================================================
    // Read Port 1 - combinational read
    assign rd_data1_o = registers[rd_addr1_i];
    
    // Read Port 2 - combinational read
    assign rd_data2_o = registers[rd_addr2_i];
    
    // ========================================================================
    // Assertions for Verification
    // ========================================================================
    `ifdef ENABLE_ASSERTIONS
        // x0 must always be zero
        property x0_always_zero;
            @(posedge clk_i) (registers[0] == '0);
        endproperty
        
        assert_x0_zero: assert property(x0_always_zero)
            else $error("Register x0 is not zero: %0h", registers[0]);
        
        // Write enable check
        property write_to_x0_ignored;
            @(posedge clk_i) disable iff (!rst_ni)
            (wr_enable_i && (wr_addr_i == '0)) |=> (registers[0] == '0);
        endproperty
        
        assert_no_write_x0: assert property(write_to_x0_ignored)
            else $error("Write to x0 not properly ignored");
        
        // Valid address range check
        property valid_rd_addr1;
            @(rd_addr1_i) (rd_addr1_i < NUM_REGS);
        endproperty
        
        assert_valid_rd1: assert property(valid_rd_addr1)
            else $error("Invalid read address 1: %0d", rd_addr1_i);
        
        property valid_rd_addr2;
            @(rd_addr2_i) (rd_addr2_i < NUM_REGS);
        endproperty
        
        assert_valid_rd2: assert property(valid_rd_addr2)
            else $error("Invalid read address 2: %0d", rd_addr2_i);
    `endif

endmodule : register_file
