# RISC-V 32-bit Processor

[![RISC-V](https://img.shields.io/badge/RISC--V-RV32I-blue)](https://riscv.org/)
[![SystemVerilog](https://img.shields.io/badge/Language-SystemVerilog-green)](https://en.wikipedia.org/wiki/SystemVerilog)
[![License](https://img.shields.io/badge/License-Educational-orange)](LICENSE)

Implementation of a 32-bit RISC-V processor core in SystemVerilog with comprehensive testbenches and industry-standard verification.

## Features

- **RV32I Base Integer Instruction Set**
- **Single-cycle execution architecture**

## 📋 Table of Contents

- [Architecture](#architecture)
- [Quick Start](#quick-start)
- [Directory Structure](#directory-structure)
- [Supported Instructions](#supported-instructions)
- [Verification](#verification)
- [Documentation](#documentation)
- [Examples](#examples)
- [Contributing](#contributing)

## Architecture

The processor implements a classic single-cycle RISC-V architecture:

```
┌─────────────────────────────────────────────────────┐
│                  RISC-V Core                        │
│                                                     │
│  PC → Instruction Memory → Decode → Register File  │
│   ↑                           ↓                     │
│   │                          ALU                    │
│   │                           ↓                     │
│   └──────── Branch Logic ─────┘                    │
└─────────────────────────────────────────────────────┘
```

### Core Modules

| Module | Description | File |
|--------|-------------|------|
| **riscv_pkg** | Common types and constants | `rtl/riscv_pkg.sv` |
| **ALU** | Arithmetic Logic Unit | `rtl/alu.sv` |
| **Register File** | 32 x 32-bit registers | `rtl/register_file.sv` |
| **Instruction Memory** | Program storage | `rtl/instruction_memory.sv` |
| **Program Counter** | PC management | `rtl/program_counter.sv` |
| **Decode Unit** | Instruction decoder | `rtl/decode_unit.sv` |
| **RISC-V Core** | Top-level integration | `rtl/riscv_core.sv` |

## Using with Vivado

### Creating a Vivado Project

1. **Open Vivado** and create a new project

2. **Add Source Files:**
   - Add all files from `rtl/` directory
   - **Important:** Add `riscv_pkg.sv` FIRST (it must be compiled before other files)
   - Order: riscv_pkg.sv → alu.sv, register_file.sv, etc. → riscv_core.sv

3. **Add Simulation Sources:**
   - Add desired testbench from `tb/` directory
   - For full processor test: `tb/tb_riscv_core.sv`
   - For individual module test: `tb/tb_alu.sv`, `tb/tb_register_file.sv`, etc.

4. **Run Simulation:**
   - Click "Run Simulation" → "Run Behavioral Simulation"
   - Xsim will compile and run the testbench
   - Check console for test results

### Simulation Setup

**Recommended Settings:**
- **Simulation Time**: 10 ms (or until testbench finishes)
- **Language**: SystemVerilog

##  Directory Structure

```
RISC-V-Processor/
├── rtl/                    # RTL source files (.sv)
│   ├── riscv_pkg.sv       # Package definitions
│   ├── alu.sv             # ALU implementation
│   ├── register_file.sv   # Register file
│   ├── instruction_memory.sv
│   ├── program_counter.sv
│   ├── decode_unit.sv
│   └── riscv_core.sv      # Top-level
├── tb/                     # Testbenches (.sv)
│   ├── tb_alu.sv
│   ├── tb_register_file.sv
│   ├── tb_instruction_memory.sv
│   └── tb_riscv_core.sv
├── sim/                    # Simulation outputs
│   ├── run_sim.sh         # Simulation script
│   └── *.vcd, *.log       # Generated files
├── docs/                   # Documentation
│   ├── ARCHITECTURE.md    # Detailed architecture
│   └── INSTRUCTIONS.md    # Instruction set reference
├── Makefile               # Build automation
└── README.md              # This file
```

## Supported Instructions

### Arithmetic & Logic (R-Type)
```assembly
ADD  rd, rs1, rs2    # rd = rs1 + rs2
SUB  rd, rs1, rs2    # rd = rs1 - rs2
AND  rd, rs1, rs2    # rd = rs1 & rs2
OR   rd, rs1, rs2    # rd = rs1 | rs2
XOR  rd, rs1, rs2    # rd = rs1 ^ rs2
SLL  rd, rs1, rs2    # rd = rs1 << rs2
SRL  rd, rs1, rs2    # rd = rs1 >> rs2
SLT  rd, rs1, rs2    # rd = (rs1 < rs2) ? 1 : 0
MUL  rd, rs1, rs2    # rd = rs1 * rs2 (RV32M)
```

### Immediate Operations (I-Type)
```assembly
ADDI rd, rs1, imm    # rd = rs1 + imm
ANDI rd, rs1, imm    # rd = rs1 & imm
ORI  rd, rs1, imm    # rd = rs1 | imm
XORI rd, rs1, imm    # rd = rs1 ^ imm
SLLI rd, rs1, imm    # rd = rs1 << imm
SRLI rd, rs1, imm    # rd = rs1 >> imm
SLTI rd, rs1, imm    # rd = (rs1 < imm) ? 1 : 0
```

### Control Flow
```assembly
BEQ  rs1, rs2, offset   # if (rs1 == rs2) PC += offset
JAL  rd, offset         # rd = PC+4; PC += offset
JALR rd, rs1, offset    # rd = PC+4; PC = rs1 + offset
```

## Verification

Each module includes comprehensive testbenches:

### ALU Testbench (`tb/tb_alu.sv`)
- All 9 operations tested
- Edge cases (overflow, zero, max values)
- Flag verification

### Register File Testbench (`tb/tb_register_file.sv`)
- Initial value verification
- x0 hardwired to zero test
- Dual-port read verification
- Write-enable control

### Core Testbench (`tb/tb_riscv_core.sv`)
- Complete program execution
- Register state verification
- PC progression tracking
- Instruction monitoring

## Documentation

- **[ARCHITECTURE.md](docs/ARCHITECTURE.md)** - Detailed design documentation

## Development

### Adding New Instructions

1. Update `riscv_pkg.sv` with new ALU operation (if needed)
2. Modify `decode_unit.sv` to decode the instruction
3. Update `alu.sv` if new operation required
4. Add tests to appropriate testbench
5. Update documentation

### Extending the Design

- **Pipeline**: Add pipeline registers between stages
- **Cache**: Add instruction/data cache modules
- **Interrupts**: Implement interrupt handling logic
- **Peripherals**: Add memory-mapped I/O

## Performance

- **Architecture**: Single-cycle
- **CPI**: 1 (one cycle per instruction)
- **Resource Usage**: Minimal (suitable for small FPGAs)

## License

This project is for educational purposes.

## 🗺️ Roadmap

- [x] Basic RV32I implementation
- [x] Comprehensive testbenches
- [x] Documentation
- [ ] Complete I-type instruction support
- [ ] All branch instructions
- [ ] Data memory and load/store
- [ ] 5-stage pipeline
- [ ] Cache hierarchy
- [ ] RV32M extension
- [ ] FPGA synthesis scripts

---

**Built with ❤️ for learning RISC-V architecture**

**Last Updated**: October 2025
