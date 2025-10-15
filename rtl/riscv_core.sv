// ============================================================================
// RISC-V Core Top Level - SystemVerilog Implementation
// ============================================================================
// Description: Top-level integration of all processor components.
//              Implements a simple single-cycle RISC-V processor.
// ============================================================================

module riscv_core 
import riscv_pkg::*;
#(
    parameter int DATA_WIDTH = 32
) (
    // Clock and Reset
    input  logic                   clk_i,
    input  logic                   rst_ni,       // Active low reset
    
    // Status Outputs
    output logic                   zero_flag_o,
    output logic [DATA_WIDTH-1:0]  pc_o,
    output logic [DATA_WIDTH-1:0]  instruction_o
);

    // ========================================================================
    // Internal Signals
    // ========================================================================
    
    // Program Counter Signals
    logic [DATA_WIDTH-1:0]  pc_current;
    logic [DATA_WIDTH-1:0]  pc_next;
    logic                   pc_enable;
    logic                   branch_taken;
    logic [DATA_WIDTH-1:0]  branch_target;
    
    // Instruction Memory Signals
    logic [31:0]        instruction;
    logic                   inst_valid;
    
    // Decode Signals
    logic [6:0]             opcode;
    logic [4:0]             rd_addr;
    logic [4:0]             rs1_addr;
    logic [4:0]             rs2_addr;
    logic [2:0]             funct3;
    logic [6:0]             funct7;
    alu_op_e                alu_operation;
    logic                   reg_write_en;
    logic                   alu_src_imm;
    logic                   mem_read;
    logic                   mem_write;
    logic                   mem_to_reg;
    logic                   branch;
    logic                   jump;
    logic [DATA_WIDTH-1:0]  immediate;
    
    // Register File Signals
    logic [DATA_WIDTH-1:0]  rs1_data;
    logic [DATA_WIDTH-1:0]  rs2_data;
    logic [DATA_WIDTH-1:0]  rd_data;
    
    // ALU Signals
    logic [DATA_WIDTH-1:0]  alu_operand_a;
    logic [DATA_WIDTH-1:0]  alu_operand_b;
    logic [DATA_WIDTH-1:0]  alu_result;
    logic                   alu_zero;
    logic                   alu_negative;
    logic                   alu_overflow;
    
    // ========================================================================
    // Module Instantiations
    // ========================================================================
    
    // Program Counter
    program_counter u_program_counter (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .enable_i           (pc_enable),
        .branch_i           (branch_taken),
        .branch_target_i    (branch_target),
        .pc_o               (pc_current),
        .pc_next_o          (pc_next)
    );
    
    // Instruction Memory
    instruction_memory u_instruction_memory (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .addr_i             (pc_current),
        .data_o             (instruction),
        .valid_o            (inst_valid)
    );
    
    // Decode Unit
    decode_unit u_decode_unit (
        .instruction_i      (instruction),
        .opcode_o           (opcode),
        .rd_addr_o          (rd_addr),
        .rs1_addr_o         (rs1_addr),
        .rs2_addr_o         (rs2_addr),
        .funct3_o           (funct3),
        .funct7_o           (funct7),
        .alu_op_o           (alu_operation),
        .reg_write_enable_o (reg_write_en),
        .alu_src_imm_o      (alu_src_imm),
        .mem_read_o         (mem_read),
        .mem_write_o        (mem_write),
        .mem_to_reg_o       (mem_to_reg),
        .branch_o           (branch),
        .jump_o             (jump),
        .immediate_o        (immediate)
    );
    
    // Register File
    register_file u_register_file (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .rd_addr1_i         (rs1_addr),
        .rd_data1_o         (rs1_data),
        .rd_addr2_i         (rs2_addr),
        .rd_data2_o         (rs2_data),
        .wr_enable_i        (reg_write_en),
        .wr_addr_i          (rd_addr),
        .wr_data_i          (rd_data)
    );
    
    // ALU
    alu u_alu (
        .operand_a_i        (alu_operand_a),
        .operand_b_i        (alu_operand_b),
        .alu_operation_i    (alu_operation),
        .result_o           (alu_result),
        .zero_flag_o        (alu_zero),
        .negative_flag_o    (alu_negative),
        .overflow_flag_o    (alu_overflow)
    );
    
    // ========================================================================
    // Datapath Logic
    // ========================================================================
    
    // ALU Operand Selection
    assign alu_operand_a = rs1_data;
    assign alu_operand_b = alu_src_imm ? immediate : rs2_data;
    
    // Write-back Data Selection
    // For this simple implementation, we only support ALU results
    // Memory operations would require data memory
    assign rd_data = alu_result;
    
    // PC Control
    assign pc_enable = 1'b1;  // Always enabled in single-cycle
    
    // Branch/Jump Logic
    always_comb begin
        branch_taken = 1'b0;
        branch_target = pc_next;
        
        if (jump) begin
            // Jump instruction
            branch_taken = 1'b1;
            if (opcode == OP_JAL) begin
                branch_target = pc_current + immediate;
            end else begin  // JALR
                branch_target = (rs1_data + immediate) & ~32'h1;
            end
        end else if (branch) begin
            // Branch instruction - simplified (only BEQ support)
            if (alu_zero && funct3 == 3'b000) begin  // BEQ
                branch_taken = 1'b1;
                branch_target = pc_current + immediate;
            end
        end
    end
    
    // ========================================================================
    // Output Assignments
    // ========================================================================
    assign zero_flag_o   = alu_zero;
    assign pc_o          = pc_current;
    assign instruction_o = instruction;
    
    // ========================================================================
    // Debug and Monitoring
    // ========================================================================
    `ifdef SIMULATION
        // Display instruction execution for debugging
        always @(posedge clk_i) begin
            if (rst_ni && inst_valid) begin
                $display("[%0t] PC=0x%08h, INST=0x%08h, OP=%02h, RD=%02d, RS1=%02d, RS2=%02d", 
                         $time, pc_current, instruction, opcode, rd_addr, rs1_addr, rs2_addr);
                if (reg_write_en) begin
                    $display("         Write: x%0d <= 0x%08h", rd_addr, rd_data);
                end
            end
        end
    `endif

endmodule : riscv_core
