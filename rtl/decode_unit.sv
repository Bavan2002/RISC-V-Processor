// ============================================================================
// Decode Unit - SystemVerilog Implementation
// ============================================================================
// Description: Decodes RISC-V instructions and generates control signals.
//              Supports RV32I base instruction set.
// ============================================================================

module decode_unit 
import riscv_pkg::*;
#(
    parameter int INST_WIDTH = 32
) (
    // Instruction Input
    input  logic [INST_WIDTH-1:0]  instruction_i,
    
    // Decoded Fields
    output logic [6:0]             opcode_o,
    output logic [4:0]             rd_addr_o,
    output logic [4:0]             rs1_addr_o,
    output logic [4:0]             rs2_addr_o,
    output logic [2:0]             funct3_o,
    output logic [6:0]             funct7_o,
    
    // Control Signals
    output alu_op_e                alu_op_o,
    output logic                   reg_write_enable_o,
    output logic                   alu_src_imm_o,
    output logic                   mem_read_o,
    output logic                   mem_write_o,
    output logic                   mem_to_reg_o,
    output logic                   branch_o,
    output logic                   jump_o,
    
    // Immediate Value
    output logic [31:0]        immediate_o
);

    // ========================================================================
    // Instruction Field Extraction
    // ========================================================================
    logic [6:0] opcode;
    logic [4:0] rd, rs1, rs2;
    logic [2:0] funct3;
    logic [6:0] funct7;
    
    assign opcode = instruction_i[6:0];
    assign rd     = instruction_i[11:7];
    assign rs1    = instruction_i[19:15];
    assign rs2    = instruction_i[24:20];
    assign funct3 = instruction_i[14:12];
    assign funct7 = instruction_i[31:25];
    
    // ========================================================================
    // Immediate Generation
    // ========================================================================
    logic [31:0] imm_i, imm_s, imm_b, imm_u, imm_j;
    logic [31:0] immediate;
    
    always_comb begin
        // I-type immediate
        imm_i = {{20{instruction_i[31]}}, instruction_i[31:20]};
        
        // S-type immediate
        imm_s = {{20{instruction_i[31]}}, instruction_i[31:25], instruction_i[11:7]};
        
        // B-type immediate
        imm_b = {{19{instruction_i[31]}}, instruction_i[31], instruction_i[7], 
                 instruction_i[30:25], instruction_i[11:8], 1'b0};
        
        // U-type immediate
        imm_u = {instruction_i[31:12], 12'b0};
        
        // J-type immediate
        imm_j = {{11{instruction_i[31]}}, instruction_i[31], instruction_i[19:12],
                 instruction_i[20], instruction_i[30:21], 1'b0};
    end
    
    // ========================================================================
    // Control Signal Generation
    // ========================================================================
    always_comb begin
        // Default values
        reg_write_enable_o = 1'b0;
        alu_src_imm_o      = 1'b0;
        mem_read_o         = 1'b0;
        mem_write_o        = 1'b0;
        mem_to_reg_o       = 1'b0;
        branch_o           = 1'b0;
        jump_o             = 1'b0;
        alu_op_o           = ALU_ADD;
        immediate          = '0;
        
        unique case (opcode)
            OP_RTYPE: begin
                // R-type instructions
                reg_write_enable_o = 1'b1;
                alu_src_imm_o      = 1'b0;
                
                // Decode ALU operation from funct3 and funct7
                case (funct3)
                    F3_ADD_SUB: alu_op_o = (funct7[5]) ? ALU_SUB : ALU_ADD;
                    F3_SLL:     alu_op_o = ALU_SLL;
                    F3_SLT:     alu_op_o = ALU_SLT;
                    F3_XOR:     alu_op_o = ALU_XOR;
                    F3_SRL_SRA: alu_op_o = ALU_SRL;  // SRL (no SRA support yet)
                    F3_OR:      alu_op_o = ALU_OR;
                    F3_AND:     alu_op_o = ALU_AND;
                    default:    alu_op_o = ALU_ADD;
                endcase
                
                // Check for MUL instruction (funct7 = 0x01 for RV32M)
                if (funct7 == 7'h01 && funct3 == 3'b000) begin
                    alu_op_o = ALU_MUL;
                end
            end
            
            OP_ITYPE: begin
                // I-type arithmetic instructions
                reg_write_enable_o = 1'b1;
                alu_src_imm_o      = 1'b1;
                immediate          = imm_i;
                
                case (funct3)
                    F3_ADD_SUB: alu_op_o = ALU_ADD;  // ADDI
                    F3_SLL:     alu_op_o = ALU_SLL;  // SLLI
                    F3_SLT:     alu_op_o = ALU_SLT;  // SLTI
                    F3_XOR:     alu_op_o = ALU_XOR;  // XORI
                    F3_SRL_SRA: alu_op_o = ALU_SRL;  // SRLI
                    F3_OR:      alu_op_o = ALU_OR;   // ORI
                    F3_AND:     alu_op_o = ALU_AND;  // ANDI
                    default:    alu_op_o = ALU_ADD;
                endcase
            end
            
            OP_LOAD: begin
                // Load instructions
                reg_write_enable_o = 1'b1;
                alu_src_imm_o      = 1'b1;
                mem_read_o         = 1'b1;
                mem_to_reg_o       = 1'b1;
                alu_op_o           = ALU_ADD;
                immediate          = imm_i;
            end
            
            OP_STORE: begin
                // Store instructions
                alu_src_imm_o = 1'b1;
                mem_write_o   = 1'b1;
                alu_op_o      = ALU_ADD;
                immediate     = imm_s;
            end
            
            OP_BRANCH: begin
                // Branch instructions
                branch_o  = 1'b1;
                alu_op_o  = ALU_SUB;
                immediate = imm_b;
            end
            
            OP_LUI: begin
                // LUI instruction
                reg_write_enable_o = 1'b1;
                immediate          = imm_u;
            end
            
            OP_JAL: begin
                // JAL instruction
                reg_write_enable_o = 1'b1;
                jump_o             = 1'b1;
                immediate          = imm_j;
            end
            
            OP_JALR: begin
                // JALR instruction
                reg_write_enable_o = 1'b1;
                jump_o             = 1'b1;
                alu_src_imm_o      = 1'b1;
                immediate          = imm_i;
            end
            
            default: begin
                // NOP or invalid instruction
                reg_write_enable_o = 1'b0;
            end
        endcase
    end
    
    // ========================================================================
    // Output Assignments
    // ========================================================================
    assign opcode_o     = opcode;
    assign rd_addr_o    = rd;
    assign rs1_addr_o   = rs1;
    assign rs2_addr_o   = rs2;
    assign funct3_o     = funct3;
    assign funct7_o     = funct7;
    assign immediate_o  = immediate;

endmodule : decode_unit
