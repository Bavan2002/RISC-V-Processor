# RISC-V 32-bit Processor - SystemVerilog Implementation

## Overview

This project implements a 32-bit RISC-V processor core in SystemVerilog, featuring a clean, modular architecture designed for educational purposes and further development. The implementation follows industry-standard coding practices with comprehensive testbenches and verification.

## Features

- **RV32I Base Integer Instruction Set** support
- **Single-cycle execution** architecture
- **Industry-standard SystemVerilog** (.sv) implementation
- **Comprehensive testbenches** with self-checking capabilities
- **Modular design** for easy extension and modification
- **Parameterized modules** for scalability
- **Built-in assertions** for verification
- **Full simulation support** with waveform generation

## Architecture

### Core Components

```
┌─────────────────────────────────────────────────────────┐
│                    RISC-V Core                          │
│  ┌──────────┐  ┌──────────┐  ┌──────────────────────┐  │
│  │ Program  │→ │Instruction│→ │   Decode Unit        │  │
│  │ Counter  │  │  Memory   │  │  (Control Signals)   │  │
│  └──────────┘  └──────────┘  └──────────────────────┘  │
│       ↑                                ↓                 │
│       │         ┌────────────┐   ┌─────────┐           │
│       └─────────│   Branch   │←──│   ALU   │           │
│                 │   Logic    │   └─────────┘           │
│                 └────────────┘        ↑                 │
│                                       │                 │
│                      ┌────────────────┴──────────────┐  │
│                      │    Register File (32 x 32)    │  │
│                      └───────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
```

### Module Descriptions

#### 1. **riscv_pkg.sv**
- Package containing all shared types, enumerations, and parameters
- Defines ALU operations, instruction formats, and opcodes
- Centralizes all constants for easy modification

#### 2. **alu.sv** (Arithmetic Logic Unit)
- Performs all arithmetic and logical operations
- Supports: AND, OR, ADD, SUB, SLT, SLL, SRL, MUL, XOR
- Generates status flags (zero, negative, overflow)
- Fully combinational with immediate results

#### 3. **register_file.sv**
- 32 general-purpose registers (x0-x31)
- Dual read ports for simultaneous operand access
- Single write port
- x0 hardwired to zero per RISC-V specification
- Synchronous write, asynchronous read

#### 4. **instruction_memory.sv**
- Byte-addressable instruction storage (256 bytes default)
- Pre-loaded with test program
- Word-aligned access validation
- Little-endian encoding

#### 5. **program_counter.sv**
- Manages program counter with sequential increment
- Supports branch and jump operations
- Word-aligned (4-byte increment)
- Synchronous update

#### 6. **decode_unit.sv**
- Decodes RISC-V instructions
- Generates all control signals
- Extracts immediate values for all instruction formats
- Supports R-type, I-type, S-type, B-type, U-type, J-type

#### 7. **riscv_core.sv** (Top Level)
- Integrates all components
- Implements single-cycle datapath
- Handles instruction fetch, decode, execute, writeback
- Debug monitoring in simulation mode

## Directory Structure

```
RISC-V-Processor/
├── rtl/                          # RTL source files
│   ├── riscv_pkg.sv             # Package with types and constants
│   ├── alu.sv                   # Arithmetic Logic Unit
│   ├── register_file.sv         # Register file
│   ├── instruction_memory.sv    # Instruction memory
│   ├── program_counter.sv       # Program counter
│   ├── decode_unit.sv           # Instruction decoder
│   └── riscv_core.sv            # Top-level integration
├── tb/                           # Testbench files
│   ├── tb_alu.sv                # ALU testbench
│   ├── tb_register_file.sv      # Register file testbench
│   ├── tb_instruction_memory.sv # Instruction memory testbench
│   └── tb_riscv_core.sv         # Full processor testbench
├── sim/                          # Simulation outputs
│   ├── run_sim.sh               # Simulation script
│   └── (generated files)        # VCD, logs, etc.
├── docs/                         # Documentation
│   └── ARCHITECTURE.md          # This file
├── Makefile                      # Build automation
└── README.md                     # Project overview
```

## Supported Instructions

### R-Type Instructions
- `ADD rd, rs1, rs2` - Addition
- `SUB rd, rs1, rs2` - Subtraction
- `AND rd, rs1, rs2` - Bitwise AND
- `OR rd, rs1, rs2` - Bitwise OR
- `XOR rd, rs1, rs2` - Bitwise XOR
- `SLL rd, rs1, rs2` - Shift Left Logical
- `SRL rd, rs1, rs2` - Shift Right Logical
- `SLT rd, rs1, rs2` - Set Less Than
- `MUL rd, rs1, rs2` - Multiply (RV32M extension)

### I-Type Instructions (Partial Support)
- `ADDI rd, rs1, imm` - Add Immediate
- `ANDI rd, rs1, imm` - AND Immediate
- `ORI rd, rs1, imm` - OR Immediate
- `XORI rd, rs1, imm` - XOR Immediate
- `SLTI rd, rs1, imm` - Set Less Than Immediate
- `SLLI rd, rs1, imm` - Shift Left Logical Immediate
- `SRLI rd, rs1, imm` - Shift Right Logical Immediate

### Control Flow (Basic Support)
- `BEQ rs1, rs2, offset` - Branch if Equal
- `JAL rd, offset` - Jump and Link
- `JALR rd, rs1, offset` - Jump and Link Register

## Getting Started

### Prerequisites

```bash
# Install Icarus Verilog (simulator)
sudo apt-get install iverilog

# Install GTKWave (waveform viewer)
sudo apt-get install gtkwave

# Optional: Verilator (for linting)
sudo apt-get install verilator
```

### Building and Simulation

#### Using Makefile (Recommended)

```bash
# Run all tests
make all

# Run specific test
make alu
make register_file
make instruction_memory
make riscv_core

# View waveforms
make wave_alu
make wave_riscv_core

# Clean build artifacts
make clean

# Show help
make help
```

#### Using Shell Script

```bash
# Make script executable
chmod +x sim/run_sim.sh

# Run all tests
./sim/run_sim.sh

# Run specific test
./sim/run_sim.sh alu

# View waveform
./sim/run_sim.sh wave tb_alu

# Clean
./sim/run_sim.sh clean
```

#### Manual Simulation

```bash
# Compile
iverilog -g2012 -o sim/tb_alu.out -Irtl rtl/*.sv tb/tb_alu.sv

# Run simulation
vvp sim/tb_alu.out

# View waveform
gtkwave sim/tb_alu.vcd
```

## Test Program

The instruction memory is pre-loaded with a test program:

```assembly
# Address : Instruction
0x00000000: ADD  x6,  x8,  x9   # x6  = 0x8 + 0x9 = 0x11
0x00000004: SUB  x7,  x10, x11  # x7  = 0xA - 0xB = 0xFFFFFFFF
0x00000008: MUL  x5,  x12, x13  # x5  = 0xC * 0xD = 0x9C
0x0000000C: XOR  x14, x15, x16  # x14 = 0xF ^ 0x10 = 0x1F
0x00000010: SLL  x17, x18, x19  # x17 = 0x12 << 19 = 0x90000
0x00000014: SRL  x20, x21, x22  # x20 = 0x15 >> 22 = 0
0x00000018: AND  x23, x24, x25  # x23 = 0x18 & 0x19 = 0x18
0x0000001C: OR   x26, x27, x28  # x26 = 0x1B | 0x1C = 0x1F
```

## Verification

### Testbench Features

Each testbench includes:
- **Self-checking tests** with automatic pass/fail detection
- **Directed tests** for specific scenarios
- **Random stimulus** for corner case coverage
- **Waveform generation** for debugging
- **Comprehensive reporting** with pass rates
- **Timeout watchdogs** to prevent hangs

### Example Test Output

```
=================================================================
ALU Testbench Started
=================================================================

--- Testing AND Operation ---
[PASS] Test 1: AND | A=0xFFFFFFFF, B=0x0000FFFF, Result=0x0000FFFF

--- Testing ADD Operation ---
[PASS] Test 2: ADD | A=0x00000064, B=0x000000C8, Result=0x0000012C

=================================================================
ALU Testbench Completed
=================================================================
Total Tests: 1000
Passed:      1000
Failed:      0
Pass Rate:   100.00%
=================================================================
*** ALL TESTS PASSED ***
```

## Design Principles

### 1. **Modularity**
- Each component is self-contained and reusable
- Clear interfaces between modules
- Easy to extend with new features

### 2. **Industry Standards**
- SystemVerilog modern syntax
- Proper use of types and enumerations
- Meaningful signal names with suffixes (_i, _o, _e)

### 3. **Verification First**
- Comprehensive testbenches for all modules
- Built-in assertions for runtime checking
- Self-checking tests with automatic verification

### 4. **Parameterization**
- Configurable data widths
- Adjustable memory sizes
- Easy to scale for different applications

### 5. **Documentation**
- Inline comments explaining design decisions
- Module headers with descriptions
- Clear signal naming conventions

## Signal Naming Conventions

- `_i` : Input signal
- `_o` : Output signal
- `_e` : Enumerated type
- `_t` : Type definition
- `_n` : Active low signal (e.g., `rst_ni`)

## Future Enhancements

### Short Term
- [ ] Complete I-type instruction support
- [ ] Implement all branch instructions
- [ ] Add data memory for load/store operations
- [ ] Hazard detection and forwarding

### Medium Term
- [ ] Pipeline implementation (5-stage)
- [ ] Cache hierarchy
- [ ] Interrupt handling
- [ ] CSR (Control and Status Registers)

### Long Term
- [ ] RV32M extension (multiply/divide)
- [ ] RV32F extension (floating point)
- [ ] Multi-core support
- [ ] Memory management unit (MMU)

## Performance Characteristics

- **Clock Period**: Configurable (10ns in testbenches)
- **CPI**: 1 (single-cycle implementation)
- **Latency**: 
  - Instruction fetch: 1 cycle
  - Decode: Combinational
  - Execute: Combinational
  - Writeback: Same cycle

## Known Limitations

1. **Single-cycle design** - No pipelining, lower maximum frequency
2. **Limited instruction set** - Only basic RV32I subset implemented
3. **No data memory** - Only instruction execution, no load/store
4. **No hazard handling** - Not needed in single-cycle
5. **Simple branch prediction** - No prediction, direct execution

## Debugging Tips

### Viewing Internal Signals

```systemverilog
// In testbench, access internal signals:
logic [31:0] reg_value;
reg_value = dut.u_register_file.registers[5];
```

### Enabling Debug Output

```systemverilog
// Add -DSIMULATION flag during compilation
iverilog -g2012 -DSIMULATION ...
```

### GTKWave Signals of Interest

- Program Counter: `dut.pc_o`
- Current Instruction: `dut.instruction_o`
- ALU Result: `dut.u_alu.result_o`
- Register File: `dut.u_register_file.registers[*]`

## Contributing

When extending this design:
1. Follow existing naming conventions
2. Add testbenches for new modules
3. Update documentation
4. Ensure all tests pass
5. Add assertions for verification

## References

- [RISC-V Instruction Set Manual](https://riscv.org/technical/specifications/)
- [RISC-V ISA Specifications](https://github.com/riscv/riscv-isa-manual)
- SystemVerilog IEEE 1800-2017 Standard

## License

This is an educational implementation. Please refer to the main README for licensing information.

## Authors

Redesigned and rewritten as a clean, original implementation for educational purposes.

---

**Note**: This implementation is designed for learning and experimentation. For production use, consider more robust implementations with formal verification and extensive testing.
