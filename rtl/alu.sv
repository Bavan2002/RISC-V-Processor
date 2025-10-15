// ============================================================================
// Arithmetic Logic Unit (ALU) - SystemVerilog Implementation
// ============================================================================
// Description: Performs arithmetic and logical operations based on control
//              signals. Supports all RV32I base integer operations.
// ============================================================================

module alu 
import riscv_pkg::*;
#(
    parameter int DATA_WIDTH = 32
) (
    // Input operands
    input  logic [DATA_WIDTH-1:0]  operand_a_i,
    input  logic [DATA_WIDTH-1:0]  operand_b_i,
    
    // Control signal
    input  alu_op_e                alu_operation_i,
    
    // Output result
    output logic [DATA_WIDTH-1:0]  result_o,
    
    // Status flags
    output logic                   zero_flag_o,
    output logic                   negative_flag_o,
    output logic                   overflow_flag_o
);

    // ========================================================================
    // Internal Signals
    // ========================================================================
    logic [DATA_WIDTH-1:0] alu_result;
    logic                  overflow;
    
    // ========================================================================
    // ALU Operation Logic
    // ========================================================================
    always_comb begin
        // Default values
        alu_result = '0;
        overflow   = 1'b0;
        
        unique case (alu_operation_i)
            ALU_AND: begin
                alu_result = operand_a_i & operand_b_i;
            end
            
            ALU_OR: begin
                alu_result = operand_a_i | operand_b_i;
            end
            
            ALU_ADD: begin
                {overflow, alu_result} = {1'b0, operand_a_i} + {1'b0, operand_b_i};
            end
            
            ALU_SUB: begin
                {overflow, alu_result} = {1'b0, operand_a_i} - {1'b0, operand_b_i};
            end
            
            ALU_SLT: begin
                // Signed comparison
                alu_result = ($signed(operand_a_i) < $signed(operand_b_i)) ? 
                             {{(DATA_WIDTH-1){1'b0}}, 1'b1} : '0;
            end
            
            ALU_SLL: begin
                // Shift left logical - use lower 5 bits of operand_b
                alu_result = operand_a_i << operand_b_i[4:0];
            end
            
            ALU_SRL: begin
                // Shift right logical - use lower 5 bits of operand_b
                alu_result = operand_a_i >> operand_b_i[4:0];
            end
            
            ALU_MUL: begin
                // Lower 32 bits of multiplication
                alu_result = operand_a_i * operand_b_i;
            end
            
            ALU_XOR: begin
                alu_result = operand_a_i ^ operand_b_i;
            end
            
            default: begin
                alu_result = '0;
            end
        endcase
    end
    
    // ========================================================================
    // Output Assignments
    // ========================================================================
    assign result_o = alu_result;
    
    // Flag Generation
    assign zero_flag_o     = (alu_result == '0);
    assign negative_flag_o = alu_result[DATA_WIDTH-1];
    assign overflow_flag_o = overflow;
    
    // ========================================================================
    // Assertions for Verification
    // ========================================================================
    `ifdef ENABLE_ASSERTIONS
        // Check for valid ALU operations
        property valid_alu_op;
            @(alu_operation_i) 
            (alu_operation_i inside {ALU_AND, ALU_OR, ALU_ADD, ALU_SUB, 
                                     ALU_SLT, ALU_SLL, ALU_SRL, ALU_MUL, ALU_XOR});
        endproperty
        
        assert_valid_op: assert property(valid_alu_op)
            else $error("Invalid ALU operation: %0h", alu_operation_i);
        
        // Zero flag correctness
        property zero_flag_check;
            @(alu_result) (alu_result == '0) |-> (zero_flag_o == 1'b1);
        endproperty
        
        assert_zero_flag: assert property(zero_flag_check)
            else $error("Zero flag mismatch");
    `endif

endmodule : alu
