// ============================================================================
// Program Counter - SystemVerilog Implementation
// ============================================================================
// Description: Manages the program counter with support for sequential
//              execution and branch/jump operations.
// ============================================================================

module program_counter 
import riscv_pkg::*;
#(
    parameter int PC_WIDTH = 32
) (
    // Clock and Reset
    input  logic                   clk_i,
    input  logic                   rst_ni,       // Active low reset
    
    // Control Signals
    input  logic                   enable_i,     // PC update enable
    input  logic                   branch_i,     // Branch taken
    input  logic [PC_WIDTH-1:0]    branch_target_i,
    
    // Program Counter Output
    output logic [PC_WIDTH-1:0]    pc_o,
    output logic [PC_WIDTH-1:0]    pc_next_o
);

    // ========================================================================
    // Internal Registers
    // ========================================================================
    logic [PC_WIDTH-1:0] pc_reg;
    logic [PC_WIDTH-1:0] pc_next;
    
    // ========================================================================
    // PC Update Logic
    // ========================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            pc_reg <= '0;  // Reset PC to 0
        end else if (enable_i) begin
            pc_reg <= pc_next;
        end
    end
    
    // ========================================================================
    // Next PC Calculation
    // ========================================================================
    always_comb begin
        if (branch_i) begin
            pc_next = branch_target_i;
        end else begin
            pc_next = pc_reg + 4;  // Sequential: PC + 4 (word-aligned)
        end
    end
    
    // ========================================================================
    // Output Assignments
    // ========================================================================
    assign pc_o      = pc_reg;
    assign pc_next_o = pc_next;
    
    // ========================================================================
    // Assertions for Verification
    // ========================================================================
    `ifdef ENABLE_ASSERTIONS
        // PC should be word-aligned
        property pc_aligned;
            @(posedge clk_i) (pc_reg[1:0] == 2'b00);
        endproperty
        
        assert_pc_aligned: assert property(pc_aligned)
            else $error("PC is not word-aligned: 0x%0h", pc_reg);
        
        // Sequential increment check
        property sequential_increment;
            @(posedge clk_i) disable iff (!rst_ni || branch_i || !enable_i)
            (pc_next == (pc_reg + 4));
        endproperty
        
        assert_seq_inc: assert property(sequential_increment)
            else $error("Sequential PC increment failed");
    `endif

endmodule : program_counter
