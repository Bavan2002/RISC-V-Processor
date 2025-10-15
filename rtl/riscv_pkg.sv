// ============================================================================
// RISC-V Package - Common Definitions and Types
// ============================================================================
// Description: Contains all shared types, enumerations, and parameters
//              for the RISC-V processor implementation
// ============================================================================

package riscv_pkg;
    
    // ========================================================================
    // Global Parameters
    // ========================================================================
    parameter int XLEN = 32;              // Data width
    parameter int ILEN = 32;              // Instruction width
    parameter int REG_COUNT = 32;         // Number of registers
    parameter int REG_ADDR_WIDTH = 5;     // Register address width
    parameter int IMEM_SIZE = 256;        // Instruction memory size (bytes)
    parameter int IMEM_ADDR_WIDTH = 32;   // Instruction memory address width
    
    // ========================================================================
    // ALU Operation Enumeration
    // ========================================================================
    typedef enum logic [3:0] {
        ALU_AND  = 4'b0000,   // Bitwise AND
        ALU_OR   = 4'b0001,   // Bitwise OR
        ALU_ADD  = 4'b0010,   // Addition
        ALU_SUB  = 4'b0100,   // Subtraction
        ALU_SLT  = 4'b1000,   // Set less than
        ALU_SLL  = 4'b0011,   // Shift left logical
        ALU_SRL  = 4'b0101,   // Shift right logical
        ALU_MUL  = 4'b0110,   // Multiply
        ALU_XOR  = 4'b0111    // Bitwise XOR
    } alu_op_e;
    
    // ========================================================================
    // Opcode Enumeration (RISC-V Base)
    // ========================================================================
    typedef enum logic [6:0] {
        OP_RTYPE = 7'b0110011,  // R-type instructions
        OP_ITYPE = 7'b0010011,  // I-type instructions
        OP_LOAD  = 7'b0000011,  // Load instructions
        OP_STORE = 7'b0100011,  // Store instructions
        OP_BRANCH= 7'b1100011,  // Branch instructions
        OP_JAL   = 7'b1101111,  // JAL instruction
        OP_JALR  = 7'b1100111,  // JALR instruction
        OP_LUI   = 7'b0110111,  // LUI instruction
        OP_AUIPC = 7'b0010111   // AUIPC instruction
    } opcode_e;
    
    // ========================================================================
    // Function3 Encodings
    // ========================================================================
    typedef enum logic [2:0] {
        F3_ADD_SUB = 3'b000,
        F3_SLL     = 3'b001,
        F3_SLT     = 3'b010,
        F3_XOR     = 3'b100,
        F3_SRL_SRA = 3'b101,
        F3_OR      = 3'b110,
        F3_AND     = 3'b111
    } funct3_e;
    
    // ========================================================================
    // Instruction Format Structure
    // ========================================================================
    typedef struct packed {
        logic [6:0]  funct7;
        logic [4:0]  rs2;
        logic [4:0]  rs1;
        logic [2:0]  funct3;
        logic [4:0]  rd;
        logic [6:0]  opcode;
    } r_type_inst_t;
    
    typedef struct packed {
        logic [11:0] imm;
        logic [4:0]  rs1;
        logic [2:0]  funct3;
        logic [4:0]  rd;
        logic [6:0]  opcode;
    } i_type_inst_t;
    
endpackage : riscv_pkg
