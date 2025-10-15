// ============================================================================
// Instruction Memory - SystemVerilog Implementation
// ============================================================================
// Description: Read-only instruction memory with byte-addressable storage.
//              Initialized with a test program during reset.
// ============================================================================

module instruction_memory
import riscv_pkg::*;
#(
    parameter int MEM_SIZE_BYTES = IMEM_SIZE,
    parameter int ADDR_WIDTH     = IMEM_ADDR_WIDTH,
    parameter int DATA_WIDTH     = ILEN
) (
    // Clock and Reset
    input  logic                    clk_i,
    input  logic                    rst_ni,      // Active low reset
    
    // Read Interface
    input  logic [ADDR_WIDTH-1:0]   addr_i,
    output logic [DATA_WIDTH-1:0]   data_o,
    output logic                    valid_o
);

    // ========================================================================
    // Memory Array (Byte Addressable)
    // ========================================================================
    logic [7:0] memory [MEM_SIZE_BYTES];
    
    // ========================================================================
    // Internal Signals
    // ========================================================================
    logic                    addr_valid;
    logic [DATA_WIDTH-1:0]   read_data;
    
    // ========================================================================
    // Memory Initialization
    // ========================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // Clear memory
            for (int i = 0; i < MEM_SIZE_BYTES; i++) begin
                memory[i] <= 8'h00;
            end
            
            // Load test program
            // Instruction 0: ADD x6, x8, x9 (R-type)
            // Encoding: 0x009403b3
            memory[3]  <= 8'h00;
            memory[2]  <= 8'h94;
            memory[1]  <= 8'h03;
            memory[0]  <= 8'hb3;
            
            // Instruction 1: SUB x7, x10, x11 (R-type)
            // Encoding: 0x40b503b3
            memory[7]  <= 8'h40;
            memory[6]  <= 8'hb5;
            memory[5]  <= 8'h03;
            memory[4]  <= 8'hb3;
            
            // Instruction 2: MUL x5, x12, x13 (R-type)
            // Encoding: 0x02d602b3
            memory[11] <= 8'h02;
            memory[10] <= 8'hd6;
            memory[9]  <= 8'h02;
            memory[8]  <= 8'hb3;
            
            // Instruction 3: XOR x14, x15, x16 (R-type)
            // Encoding: 0x010\7c733
            memory[15] <= 8'h01;
            memory[14] <= 8'h07;
            memory[13] <= 8'hc7;
            memory[12] <= 8'h33;
            
            // Instruction 4: SLL x17, x18, x19 (R-type)
            // Encoding: 0x013918b3
            memory[19] <= 8'h01;
            memory[18] <= 8'h39;
            memory[17] <= 8'h18;
            memory[16] <= 8'hb3;
            
            // Instruction 5: SRL x20, x21, x22 (R-type)
            // Encoding: 0x016ada33
            memory[23] <= 8'h01;
            memory[22] <= 8'h6a;
            memory[21] <= 8'hda;
            memory[20] <= 8'h33;
            
            // Instruction 6: AND x23, x24, x25 (R-type)
            // Encoding: 0x019c7bb3
            memory[27] <= 8'h01;
            memory[26] <= 8'h9c;
            memory[25] <= 8'h7b;
            memory[24] <= 8'hb3;
            
            // Instruction 7: OR x26, x27, x28 (R-type)
            // Encoding: 0x01cded33
            memory[31] <= 8'h01;
            memory[30] <= 8'hcd;
            memory[29] <= 8'hed;
            memory[28] <= 8'h33;
        end
    end
    
    // ========================================================================
    // Address Validation
    // ========================================================================
    assign addr_valid = (addr_i < (MEM_SIZE_BYTES - 3)) && ((addr_i & 2'b11) == 2'b00);
    
    // ========================================================================
    // Memory Read Logic (Little Endian)
    // ========================================================================
    always_comb begin
        if (addr_valid) begin
            // Little endian: LSB at lowest address
            read_data = {memory[addr_i+3], memory[addr_i+2], 
                        memory[addr_i+1], memory[addr_i]};
        end else begin
            read_data = '0;  // Return NOP on invalid address
        end
    end
    
    // ========================================================================
    // Output Assignments
    // ========================================================================
    assign data_o  = read_data;
    assign valid_o = addr_valid;
    
    // ========================================================================
    // Assertions for Verification
    // ========================================================================
    `ifdef ENABLE_ASSERTIONS
        // Check for aligned addresses
        property aligned_access;
            @(addr_i) (addr_i[1:0] == 2'b00);
        endproperty
        
        assert_aligned: assert property(aligned_access)
            else $warning("Unaligned instruction access at address: 0x%0h", addr_i);
        
        // Check for valid address range
        property valid_address;
            @(addr_i) (addr_i < MEM_SIZE_BYTES);
        endproperty
        
        assert_valid_addr: assert property(valid_address)
            else $error("Address out of range: 0x%0h", addr_i);
    `endif

endmodule : instruction_memory
