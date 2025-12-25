# CARL16 Computer

A fun summer project 2025 with the goal to build a simple 16-bit computer that can hold a simple OS, programming language and some games.

## Project Structure

### `/chipset` - Hardware Components

Hardware chipset for the Carl16 computer using a simple hardware descriptive language for the architecture of the logic gates.

The chipset is organized by complexity and dependencies:

#### Combinational Logic (`/chipset/combinational`)

- **1_basic/** - Fundamental gates (AND, OR, NOT, XOR, etc.)
- **2_adders/** - Arithmetic components (HalfAdder, FullAdder, Add16)
- **3_routing/** - Data routing (Mux, DMux and their variants)
- **4_logic/** - Complex logic units (ALU, Inc16)

#### Sequential Logic (`/chipset/sequential`)

- **1_storage/** - Basic memory (Bit, Register)
- **2_memory/** - Memory hierarchy (RAM8, RAM16, RAM512, RAM4K, RAM16K, Memory)
- **3_control/** - Control flow (Program Counter)
- **4_processing/** - Central components (CPU, Computer)

## C16 Assembly Language

### `/assembler` - C16 Assembler (Rust)

The Carl16 computer uses C16 assembly language, a simple assembly language with:

- 16-bit instructions
- Memory-mapped I/O
- Screen memory (addresses 0x4000-0x5FFF)
- Keyboard input (address 0x6000)

The assembler is implemented in Rust and includes:

- **src/** - Assembler source code
- **tests/** - C16 assembly test programs
  - `basic.asm` - Basic load/store operations
  - `add.asm` - Addition of two numbers
  - `multiply.asm` - Multiplication via repeated addition
  - `branching.asm` - Conditional branching
  - `iteration.asm` - Loop iteration and summation
  - `variables.asm` - Variable manipulation and swapping
  - `pointers.asm` - Array manipulation with pointers
  - `screen.asm` - Screen drawing operations
  - `rectangle.asm` - Interactive screen filling

### Building the Assembler

```bash
cd assembler
cargo build --release
```

## Resources

Based on concepts from "The Elements of Computing Systems" by Nisan and Schocken.
