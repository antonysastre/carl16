//! # CARL16 Assembler
//!
//! This crate provides functionality to assemble CARL16 assembly language
//! into binary machine code.
//!
//! # Example
//!
//! ```no_run
//! use c16::assemble;
//!
//! assemble("program.asm", "program.c16")?;
//! # Ok::<(), c16::AssemblyError>(())
//! ```

use std::collections::HashMap;
use std::fs::{read_to_string, File};
use std::io::Write;

// ============================================================================
// CONSTANTS
// ============================================================================

/// Starting address for variable allocation in RAM
const VAR_START_ADDRESS: u16 = 16;

/// Screen memory map address
const SCREEN_ADDRESS: u16 = 16384;

/// Keyboard memory map address
const KBD_ADDRESS: u16 = 24576;

// ============================================================================
// PUBLIC API
// ============================================================================

/// Assemble a .asm file to a .c16 file
///
/// # Arguments
/// * `input_path` - Path to the input assembly file
/// * `output_path` - Path where the binary output will be written
///
/// # Errors
/// Returns `AssemblyError` if file I/O fails or assembly fails
///
/// # Example
/// ```no_run
/// use c16::assemble;
///
/// assemble("program.asm", "program.c16")?;
/// # Ok::<(), c16::AssemblyError>(())
/// ```
pub fn assemble(input_path: &str, output_path: &str) -> Result<(), AssemblyError> {
    let content = read_to_string(input_path).map_err(AssemblyError::FileIOError)?;

    let machine_code = assemble_string(&content)?;
    write_object_file(output_path, &machine_code)?;

    Ok(())
}

/// Assemble source code string to binary output
///
/// # Arguments
/// * `content` - The assembly source code as a string
///
/// # Returns
/// A vector of binary strings, one per instruction
///
/// # Errors
/// Returns `AssemblyError` if assembly fails
///
/// # Example
/// ```
/// use c16::assemble_string;
///
/// let source = "@42\nD=M\n";
/// let binary = assemble_string(source)?;
/// assert_eq!(binary[0], "0000000000101010");
/// # Ok::<(), c16::AssemblyError>(())
/// ```
pub fn assemble_string(content: &str) -> Result<Vec<String>, AssemblyError> {
    let symbol_table = first_pass(content)?;
    second_pass(content, symbol_table)
}

// ============================================================================
// FIRST PASS: Build symbol table with labels
// ============================================================================

/// First pass: Build symbol table with labels
///
/// Scans through the assembly code to identify label declarations
/// and record their addresses in the symbol table.
fn first_pass(content: &str) -> Result<SymbolTable, AssemblyError> {
    let mut symbol_table = SymbolTable::new();
    let mut location_counter: u16 = 0;

    for line in content.lines() {
        let preprocessed_line = preprocess_line(line);
        if preprocessed_line.is_empty() {
            continue;
        }

        match parse_instruction_type(&preprocessed_line) {
            InstructionType::Label(label) => {
                // Labels point to the next instruction address
                symbol_table.insert(label, location_counter);
            }
            InstructionType::A(_) | InstructionType::C { .. } => {
                // Real instructions increment location counter
                location_counter += 1;
            }
        }
    }

    Ok(symbol_table)
}

// ============================================================================
// SECOND PASS: Generate binary code
// ============================================================================

/// Second pass: Generate binary code
///
/// Processes each instruction and converts it to binary,
/// resolving symbols and allocating variables as needed.
fn second_pass(content: &str, mut symbol_table: SymbolTable) -> Result<Vec<String>, AssemblyError> {
    let mut machine_code = Vec::new();
    let mut variable_counter: u16 = VAR_START_ADDRESS;

    for (line_num, line) in content.lines().enumerate() {
        let preprocessed_line = preprocess_line(line);
        if preprocessed_line.is_empty() {
            continue;
        }

        let binary = match parse_instruction_type(&preprocessed_line) {
            InstructionType::A(symbol) => {
                let address = resolve_address(
                    &symbol,
                    &mut symbol_table,
                    &mut variable_counter,
                    line_num + 1,
                    line,
                )?;
                format!("{:016b}", address)
            }
            InstructionType::C { dest, comp, jump } => encode_c_instruction(&dest, &comp, &jump)
                .map_err(|e| AssemblyError::InvalidSyntax {
                    line: line_num + 1,
                    content: line.to_string(),
                    reason: e.to_string(),
                })?,
            InstructionType::Label(_) => {
                // Labels don't generate code
                continue;
            }
        };

        machine_code.push(binary);
    }

    Ok(machine_code)
}

// ============================================================================
// SYMBOL TABLE
// ============================================================================

pub struct SymbolTable {
    symbols: HashMap<String, u16>,
}

impl SymbolTable {
    fn new() -> Self {
        let mut table = SymbolTable {
            symbols: HashMap::new(),
        };
        table.initialize_predefined();
        table
    }

    fn initialize_predefined(&mut self) {
        // Virtual registers R0-R15
        for i in 0..=15 {
            self.symbols.insert(format!("R{}", i), i);
        }

        // Pointer symbols
        self.symbols.insert("SP".to_string(), 0);
        self.symbols.insert("LCL".to_string(), 1);
        self.symbols.insert("ARG".to_string(), 2);
        self.symbols.insert("THIS".to_string(), 3);
        self.symbols.insert("THAT".to_string(), 4);

        // I/O pointers
        self.symbols.insert("SCREEN".to_string(), SCREEN_ADDRESS);
        self.symbols.insert("KBD".to_string(), KBD_ADDRESS);
    }

    fn insert(&mut self, symbol: String, address: u16) {
        self.symbols.insert(symbol, address);
    }

    fn get(&self, symbol: &str) -> Option<u16> {
        self.symbols.get(symbol).copied()
    }
}

// ============================================================================
// INSTRUCTION TYPES
// ============================================================================

enum InstructionType {
    A(String), // @value (symbol or number)
    C {
        // dest=comp;jump
        dest: Option<String>,
        comp: String,
        jump: Option<String>,
    },
    Label(String), // (LABEL)
}

/// Parse an instruction line to determine its type
///
/// Recognizes three instruction types:
/// - A-instructions: `@value` where value is a number or symbol
/// - C-instructions: `dest=comp;jump` format
/// - Labels: `(LABEL)` format
fn parse_instruction_type(line: &str) -> InstructionType {
    if let Some(stripped) = line.strip_prefix('@') {
        // A-instruction
        InstructionType::A(stripped.to_string())
    } else if line.starts_with('(') && line.ends_with(')') && line.len() > 2 {
        // Label declaration - safely extract content between parentheses
        InstructionType::Label(line[1..line.len() - 1].to_string())
    } else {
        // C-instruction: parse dest=comp;jump
        let (dest_part, rest) = if let Some(eq_pos) = line.find('=') {
            (Some(line[..eq_pos].trim().to_string()), &line[eq_pos + 1..])
        } else {
            (None, line)
        };

        let (comp_part, jump_part) = if let Some(semi_pos) = rest.find(';') {
            (
                rest[..semi_pos].trim().to_string(),
                Some(rest[semi_pos + 1..].trim().to_string()),
            )
        } else {
            (rest.trim().to_string(), None)
        };

        InstructionType::C {
            dest: dest_part,
            comp: comp_part,
            jump: jump_part,
        }
    }
}

// ============================================================================
// A-INSTRUCTION RESOLUTION
// ============================================================================

/// Resolve a symbol to an address
///
/// Tries to resolve the symbol in this order:
/// 1. Parse as a numeric literal
/// 2. Look up in symbol table (predefined symbols or labels)
/// 3. Allocate as a new variable
fn resolve_address(
    symbol: &str,
    symbol_table: &mut SymbolTable,
    variable_counter: &mut u16,
    line: usize,
    line_content: &str,
) -> Result<u16, AssemblyError> {
    // Try to parse as number
    if let Ok(num) = symbol.parse::<u16>() {
        return Ok(num);
    }

    // Look up in symbol table
    if let Some(address) = symbol_table.get(symbol) {
        return Ok(address);
    }

    // Check for address overflow
    if *variable_counter == u16::MAX {
        return Err(AssemblyError::InvalidSyntax {
            line,
            content: line_content.to_string(),
            reason: "Variable address space exhausted".to_string(),
        });
    }

    // New variable - allocate address
    let address = *variable_counter;
    symbol_table.insert(symbol.to_string(), address);
    *variable_counter += 1;

    Ok(address)
}

// ============================================================================
// C-INSTRUCTION ENCODING
// ============================================================================

/// Encode a C-instruction to binary
///
/// C-instructions have the format: `111a cccccc ddd jjj`
/// where `a` is the A-bit, `cccccc` is the computation,
/// `ddd` is the destination, and `jjj` is the jump condition.
fn encode_c_instruction(
    dest: &Option<String>,
    comp: &str,
    jump: &Option<String>,
) -> Result<String, AssemblyError> {
    let (a_bit, comp_bits) = encode_comp(comp)?;
    let dest_bits = encode_dest(dest.as_deref())?;
    let jump_bits = encode_jump(jump.as_deref())?;

    Ok(format!(
        "111{}{}{}{}",
        a_bit, comp_bits, dest_bits, jump_bits
    ))
}

/// Encode the computation part of a C-instruction
///
/// Returns the A-bit and the 6-bit computation code.
fn encode_comp(comp: &str) -> Result<(char, &'static str), AssemblyError> {
    match comp {
        // a=0 (A-register operations)
        "0" => Ok(('0', "101010")),
        "1" => Ok(('0', "111111")),
        "-1" => Ok(('0', "111010")),
        "D" => Ok(('0', "001100")),
        "A" => Ok(('0', "110000")),
        "!D" => Ok(('0', "001101")),
        "!A" => Ok(('0', "110001")),
        "-D" => Ok(('0', "001111")),
        "-A" => Ok(('0', "110011")),
        "D+1" => Ok(('0', "011111")),
        "A+1" => Ok(('0', "110111")),
        "D-1" => Ok(('0', "001110")),
        "A-1" => Ok(('0', "110010")),
        "D+A" => Ok(('0', "000010")),
        "D-A" => Ok(('0', "010011")),
        "A-D" => Ok(('0', "000111")),
        "D&A" => Ok(('0', "000000")),
        "D|A" => Ok(('0', "010101")),

        // a=1 (M-register/memory operations)
        "M" => Ok(('1', "110000")),
        "!M" => Ok(('1', "110001")),
        "-M" => Ok(('1', "110011")),
        "M+1" => Ok(('1', "110111")),
        "M-1" => Ok(('1', "110010")),
        "D+M" => Ok(('1', "000010")),
        "D-M" => Ok(('1', "010011")),
        "M-D" => Ok(('1', "000111")),
        "D&M" => Ok(('1', "000000")),
        "D|M" => Ok(('1', "010101")),

        _ => Err(AssemblyError::InvalidComputation(comp.to_string())),
    }
}

/// Encode the destination part of a C-instruction
///
/// Returns a 3-bit destination code.
fn encode_dest(dest: Option<&str>) -> Result<&'static str, AssemblyError> {
    match dest {
        None => Ok("000"),
        Some("M") => Ok("001"),
        Some("D") => Ok("010"),
        Some("MD") => Ok("011"),
        Some("A") => Ok("100"),
        Some("AM") => Ok("101"),
        Some("AD") => Ok("110"),
        Some("AMD") => Ok("111"),
        Some(d) => Err(AssemblyError::InvalidDestination(d.to_string())),
    }
}

/// Encode the jump condition part of a C-instruction
///
/// Returns a 3-bit jump condition code.
fn encode_jump(jump: Option<&str>) -> Result<&'static str, AssemblyError> {
    match jump {
        None => Ok("000"),
        Some("JGT") => Ok("001"),
        Some("JEQ") => Ok("010"),
        Some("JGE") => Ok("011"),
        Some("JLT") => Ok("100"),
        Some("JNE") => Ok("101"),
        Some("JLE") => Ok("110"),
        Some("JMP") => Ok("111"),
        Some(j) => Err(AssemblyError::InvalidJump(j.to_string())),
    }
}

// ============================================================================
// UTILITIES
// ============================================================================

/// Preprocess a line by removing comments and trimming whitespace
fn preprocess_line(line: &str) -> String {
    // Remove comments and whitespace
    let without_comment = line.split("//").next().unwrap_or("");
    without_comment.trim().to_string()
}

/// Write object file (machine code) to disk
fn write_object_file(output_path: &str, machine_code: &[String]) -> Result<(), AssemblyError> {
    let mut file = File::create(output_path).map_err(AssemblyError::FileIOError)?;

    for line in machine_code {
        writeln!(file, "{}", line).map_err(AssemblyError::FileIOError)?;
    }

    Ok(())
}

// ============================================================================
// ERROR HANDLING
// ============================================================================

#[derive(Debug)]
pub enum AssemblyError {
    InvalidSyntax {
        line: usize,
        content: String,
        reason: String,
    },
    InvalidComputation(String),
    InvalidDestination(String),
    InvalidJump(String),
    FileIOError(std::io::Error),
}

impl std::fmt::Display for AssemblyError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::InvalidSyntax {
                line,
                content,
                reason,
            } => {
                write!(
                    f,
                    "Syntax error on line {}: '{}'\n  Reason: {}",
                    line, content, reason
                )
            }
            Self::InvalidComputation(comp) => {
                write!(f, "Invalid computation: '{}'\n  Valid: 0, 1, -1, D, A, M, !D, !A, !M, -D, -A, -M, D+1, A+1, M+1, D-1, A-1, M-1, D+A, D+M, D-A, D-M, A-D, M-D, D&A, D&M, D|A, D|M", comp)
            }
            Self::InvalidDestination(dest) => {
                write!(
                    f,
                    "Invalid destination: '{}'\n  Valid: M, D, MD, A, AM, AD, AMD",
                    dest
                )
            }
            Self::InvalidJump(jump) => {
                write!(
                    f,
                    "Invalid jump: '{}'\n  Valid: JGT, JEQ, JGE, JLT, JNE, JLE, JMP",
                    jump
                )
            }
            Self::FileIOError(e) => {
                write!(f, "File I/O error: {}", e)
            }
        }
    }
}

impl std::error::Error for AssemblyError {}

// ============================================================================
// UNIT TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_predefined_symbols() {
        let table = SymbolTable::new();
        assert_eq!(table.get("R0"), Some(0));
        assert_eq!(table.get("R15"), Some(15));
        assert_eq!(table.get("SP"), Some(0));
        assert_eq!(table.get("LCL"), Some(1));
        assert_eq!(table.get("ARG"), Some(2));
        assert_eq!(table.get("THIS"), Some(3));
        assert_eq!(table.get("THAT"), Some(4));
        assert_eq!(table.get("SCREEN"), Some(16384));
        assert_eq!(table.get("KBD"), Some(24576));
    }

    #[test]
    fn test_encode_comp() {
        // Test a=0 operations
        assert_eq!(encode_comp("0").unwrap(), ('0', "101010"));
        assert_eq!(encode_comp("1").unwrap(), ('0', "111111"));
        assert_eq!(encode_comp("-1").unwrap(), ('0', "111010"));
        assert_eq!(encode_comp("D").unwrap(), ('0', "001100"));
        assert_eq!(encode_comp("A").unwrap(), ('0', "110000"));
        assert_eq!(encode_comp("D+1").unwrap(), ('0', "011111"));
        assert_eq!(encode_comp("D+A").unwrap(), ('0', "000010"));

        // Test a=1 operations (M-register)
        assert_eq!(encode_comp("M").unwrap(), ('1', "110000"));
        assert_eq!(encode_comp("D+M").unwrap(), ('1', "000010"));
        assert_eq!(encode_comp("D-M").unwrap(), ('1', "010011"));
        assert_eq!(encode_comp("M-1").unwrap(), ('1', "110010"));

        // Test invalid computation
        assert!(encode_comp("INVALID").is_err());
    }

    #[test]
    fn test_encode_dest() {
        assert_eq!(encode_dest(None).unwrap(), "000");
        assert_eq!(encode_dest(Some("M")).unwrap(), "001");
        assert_eq!(encode_dest(Some("D")).unwrap(), "010");
        assert_eq!(encode_dest(Some("MD")).unwrap(), "011");
        assert_eq!(encode_dest(Some("A")).unwrap(), "100");
        assert_eq!(encode_dest(Some("AM")).unwrap(), "101");
        assert_eq!(encode_dest(Some("AD")).unwrap(), "110");
        assert_eq!(encode_dest(Some("AMD")).unwrap(), "111");

        // Test invalid destination
        assert!(encode_dest(Some("INVALID")).is_err());
    }

    #[test]
    fn test_encode_jump() {
        assert_eq!(encode_jump(None).unwrap(), "000");
        assert_eq!(encode_jump(Some("JGT")).unwrap(), "001");
        assert_eq!(encode_jump(Some("JEQ")).unwrap(), "010");
        assert_eq!(encode_jump(Some("JGE")).unwrap(), "011");
        assert_eq!(encode_jump(Some("JLT")).unwrap(), "100");
        assert_eq!(encode_jump(Some("JNE")).unwrap(), "101");
        assert_eq!(encode_jump(Some("JLE")).unwrap(), "110");
        assert_eq!(encode_jump(Some("JMP")).unwrap(), "111");

        // Test invalid jump
        assert!(encode_jump(Some("INVALID")).is_err());
    }

    #[test]
    fn test_parse_instruction_type() {
        // Test A-instruction
        match parse_instruction_type("@123") {
            InstructionType::A(val) => assert_eq!(val, "123"),
            _ => panic!("Expected A-instruction"),
        }

        // Test Label
        match parse_instruction_type("(LOOP)") {
            InstructionType::Label(val) => assert_eq!(val, "LOOP"),
            _ => panic!("Expected Label"),
        }

        // Test C-instruction with dest and comp
        match parse_instruction_type("D=M") {
            InstructionType::C { dest, comp, jump } => {
                assert_eq!(dest, Some("D".to_string()));
                assert_eq!(comp, "M");
                assert_eq!(jump, None);
            }
            _ => panic!("Expected C-instruction"),
        }

        // Test C-instruction with comp and jump
        match parse_instruction_type("D;JGT") {
            InstructionType::C { dest, comp, jump } => {
                assert_eq!(dest, None);
                assert_eq!(comp, "D");
                assert_eq!(jump, Some("JGT".to_string()));
            }
            _ => panic!("Expected C-instruction"),
        }

        // Test C-instruction with all three
        match parse_instruction_type("MD=D+1;JEQ") {
            InstructionType::C { dest, comp, jump } => {
                assert_eq!(dest, Some("MD".to_string()));
                assert_eq!(comp, "D+1");
                assert_eq!(jump, Some("JEQ".to_string()));
            }
            _ => panic!("Expected C-instruction"),
        }
    }

    #[test]
    fn test_preprocess_line() {
        assert_eq!(preprocess_line("  @123  "), "@123");
        assert_eq!(preprocess_line("D=M // comment"), "D=M");
        assert_eq!(preprocess_line("// full comment"), "");
        assert_eq!(preprocess_line("   "), "");
    }

    #[test]
    fn test_encode_c_instruction() {
        // Test D=M
        assert_eq!(
            encode_c_instruction(&Some("D".to_string()), "M", &None).unwrap(),
            "1111110000010000"
        );

        // Test M=D
        assert_eq!(
            encode_c_instruction(&Some("M".to_string()), "D", &None).unwrap(),
            "1110001100001000"
        );

        // Test 0;JMP
        assert_eq!(
            encode_c_instruction(&None, "0", &Some("JMP".to_string())).unwrap(),
            "1110101010000111"
        );

        // Test D=D+M
        assert_eq!(
            encode_c_instruction(&Some("D".to_string()), "D+M", &None).unwrap(),
            "1111000010010000"
        );
    }

    #[test]
    fn test_variable_allocation() {
        let mut symbol_table = SymbolTable::new();
        let mut variable_counter = VAR_START_ADDRESS;

        // First variable
        let addr1 =
            resolve_address("temp", &mut symbol_table, &mut variable_counter, 1, "test").unwrap();
        assert_eq!(addr1, VAR_START_ADDRESS);

        // Second variable
        let addr2 =
            resolve_address("count", &mut symbol_table, &mut variable_counter, 2, "test").unwrap();
        assert_eq!(addr2, VAR_START_ADDRESS + 1);

        // Reference to first variable again
        let addr3 =
            resolve_address("temp", &mut symbol_table, &mut variable_counter, 3, "test").unwrap();
        assert_eq!(addr3, VAR_START_ADDRESS); // Should be same address as first
    }

    #[test]
    fn test_first_pass_with_labels() {
        let code = "(LOOP)\nD=M\n@LOOP\n0;JMP\n(END)\n@END\n";
        let symbol_table = first_pass(code).unwrap();

        assert_eq!(symbol_table.get("LOOP"), Some(0)); // Points to D=M
        assert_eq!(symbol_table.get("END"), Some(3)); // Points to @END
    }

    #[test]
    fn test_second_pass_simple() {
        let code = "@42\nD=M\n";
        let symbol_table = SymbolTable::new();
        let binary = second_pass(code, symbol_table).unwrap();

        assert_eq!(binary.len(), 2);
        assert_eq!(binary[0], "0000000000101010"); // @42
        assert_eq!(binary[1], "1111110000010000"); // D=M
    }

    // ============================================================================
    // COMPREHENSIVE COMPUTATION ENCODING TESTS
    // ============================================================================

    #[test]
    fn test_encode_comp_all_operations() {
        // Test all a=0 (A-register) operations
        assert_eq!(encode_comp("0").unwrap(), ('0', "101010"));
        assert_eq!(encode_comp("1").unwrap(), ('0', "111111"));
        assert_eq!(encode_comp("-1").unwrap(), ('0', "111010"));
        assert_eq!(encode_comp("D").unwrap(), ('0', "001100"));
        assert_eq!(encode_comp("A").unwrap(), ('0', "110000"));
        assert_eq!(encode_comp("!D").unwrap(), ('0', "001101"));
        assert_eq!(encode_comp("!A").unwrap(), ('0', "110001"));
        assert_eq!(encode_comp("-D").unwrap(), ('0', "001111"));
        assert_eq!(encode_comp("-A").unwrap(), ('0', "110011"));
        assert_eq!(encode_comp("D+1").unwrap(), ('0', "011111"));
        assert_eq!(encode_comp("A+1").unwrap(), ('0', "110111"));
        assert_eq!(encode_comp("D-1").unwrap(), ('0', "001110"));
        assert_eq!(encode_comp("A-1").unwrap(), ('0', "110010"));
        assert_eq!(encode_comp("D+A").unwrap(), ('0', "000010"));
        assert_eq!(encode_comp("D-A").unwrap(), ('0', "010011"));
        assert_eq!(encode_comp("A-D").unwrap(), ('0', "000111"));
        assert_eq!(encode_comp("D&A").unwrap(), ('0', "000000"));
        assert_eq!(encode_comp("D|A").unwrap(), ('0', "010101"));

        // Test all a=1 (M-register) operations
        assert_eq!(encode_comp("M").unwrap(), ('1', "110000"));
        assert_eq!(encode_comp("!M").unwrap(), ('1', "110001"));
        assert_eq!(encode_comp("-M").unwrap(), ('1', "110011"));
        assert_eq!(encode_comp("M+1").unwrap(), ('1', "110111"));
        assert_eq!(encode_comp("M-1").unwrap(), ('1', "110010"));
        assert_eq!(encode_comp("D+M").unwrap(), ('1', "000010"));
        assert_eq!(encode_comp("D-M").unwrap(), ('1', "010011"));
        assert_eq!(encode_comp("M-D").unwrap(), ('1', "000111"));
        assert_eq!(encode_comp("D&M").unwrap(), ('1', "000000"));
        assert_eq!(encode_comp("D|M").unwrap(), ('1', "010101"));
    }

    #[test]
    fn test_encode_comp_invalid() {
        assert!(encode_comp("INVALID").is_err());
        assert!(encode_comp("").is_err());
        assert!(encode_comp("X").is_err());
        assert!(encode_comp("D+X").is_err());
        assert!(encode_comp("1+1").is_err());
    }

    // ============================================================================
    // ERROR HANDLING TESTS
    // ============================================================================

    #[test]
    fn test_assembly_error_display() {
        let error = AssemblyError::InvalidSyntax {
            line: 5,
            content: "@INVALID".to_string(),
            reason: "Symbol not found".to_string(),
        };
        let error_msg = format!("{}", error);
        assert!(error_msg.contains("line 5"));
        assert!(error_msg.contains("@INVALID"));
        assert!(error_msg.contains("Symbol not found"));

        let error = AssemblyError::InvalidComputation("BAD".to_string());
        let error_msg = format!("{}", error);
        assert!(error_msg.contains("Invalid computation"));
        assert!(error_msg.contains("BAD"));

        let error = AssemblyError::InvalidDestination("XYZ".to_string());
        let error_msg = format!("{}", error);
        assert!(error_msg.contains("Invalid destination"));
        assert!(error_msg.contains("XYZ"));

        let error = AssemblyError::InvalidJump("BADJUMP".to_string());
        let error_msg = format!("{}", error);
        assert!(error_msg.contains("Invalid jump"));
        assert!(error_msg.contains("BADJUMP"));

        let io_error = std::io::Error::new(std::io::ErrorKind::NotFound, "File not found");
        let error = AssemblyError::FileIOError(io_error);
        let error_msg = format!("{}", error);
        assert!(error_msg.contains("File I/O error"));
    }

    #[test]
    fn test_assembly_error_is_error() {
        let error = AssemblyError::InvalidComputation("TEST".to_string());
        // Verify it implements std::error::Error trait
        let _: &dyn std::error::Error = &error;
    }

    #[test]
    fn test_address_overflow_error() {
        let mut symbol_table = SymbolTable::new();
        let mut variable_counter = u16::MAX;

        // Try to allocate a variable when counter is at max
        let result = resolve_address(
            "overflow",
            &mut symbol_table,
            &mut variable_counter,
            1,
            "@overflow",
        );

        assert!(result.is_err());
        if let Err(AssemblyError::InvalidSyntax { reason, .. }) = result {
            assert!(reason.contains("exhausted"));
        } else {
            panic!("Expected InvalidSyntax error for address overflow");
        }
    }

    // ============================================================================
    // SYMBOL TABLE TESTS
    // ============================================================================

    #[test]
    fn test_symbol_table_insert_and_get() {
        let mut table = SymbolTable::new();

        // Test inserting a new symbol
        table.insert("MYLABEL".to_string(), 42);
        assert_eq!(table.get("MYLABEL"), Some(42));

        // Test inserting another symbol
        table.insert("ANOTHER".to_string(), 100);
        assert_eq!(table.get("ANOTHER"), Some(100));

        // Verify first symbol still exists
        assert_eq!(table.get("MYLABEL"), Some(42));
    }

    #[test]
    fn test_symbol_table_get_nonexistent() {
        let table = SymbolTable::new();
        assert_eq!(table.get("NONEXISTENT"), None);
    }

    #[test]
    fn test_symbol_table_overwrite() {
        let mut table = SymbolTable::new();

        // Insert symbol
        table.insert("LABEL".to_string(), 10);
        assert_eq!(table.get("LABEL"), Some(10));

        // Overwrite with new address
        table.insert("LABEL".to_string(), 20);
        assert_eq!(table.get("LABEL"), Some(20));
    }

    #[test]
    fn test_symbol_table_all_registers() {
        let table = SymbolTable::new();

        // Test all R0-R15 registers
        for i in 0..=15 {
            assert_eq!(table.get(&format!("R{}", i)), Some(i));
        }
    }

    // ============================================================================
    // PARSING EDGE CASE TESTS
    // ============================================================================

    #[test]
    fn test_parse_empty_string() {
        // Empty string should be parsed as C-instruction with empty comp
        match parse_instruction_type("") {
            InstructionType::C { comp, dest, jump } => {
                assert_eq!(comp, "");
                assert_eq!(dest, None);
                assert_eq!(jump, None);
            }
            _ => panic!("Empty string should parse as C-instruction"),
        }
    }

    #[test]
    fn test_parse_malformed_labels() {
        // Valid label
        match parse_instruction_type("(VALID)") {
            InstructionType::Label(label) => assert_eq!(label, "VALID"),
            _ => panic!("Expected valid label"),
        }

        // Empty parentheses - should parse as C-instruction (len <= 2)
        match parse_instruction_type("()") {
            InstructionType::C { .. } => {}
            _ => panic!("Empty parentheses should parse as C-instruction"),
        }

        // Single char parentheses - actually parses as label (len > 2)
        match parse_instruction_type("(A)") {
            InstructionType::Label(label) => assert_eq!(label, "A"),
            _ => panic!("Single char parentheses should parse as label"),
        }

        // Missing closing parenthesis - should parse as C-instruction
        match parse_instruction_type("(LABEL") {
            InstructionType::C { .. } => {}
            _ => panic!("Missing closing paren should parse as C-instruction"),
        }

        // Missing opening parenthesis - should parse as C-instruction
        match parse_instruction_type("LABEL)") {
            InstructionType::C { .. } => {}
            _ => panic!("Missing opening paren should parse as C-instruction"),
        }
    }

    #[test]
    fn test_parse_whitespace_handling() {
        // Note: parse_instruction_type expects preprocessed input (no leading/trailing whitespace)
        // But it handles whitespace within the instruction parts

        // A-instruction - whitespace in value is preserved (though unusual)
        match parse_instruction_type("@123") {
            InstructionType::A(val) => assert_eq!(val, "123"),
            _ => panic!("Expected A-instruction"),
        }

        // C-instruction with whitespace around = (trimmed by parse logic)
        match parse_instruction_type("D  =  M") {
            InstructionType::C { dest, comp, jump } => {
                assert_eq!(dest, Some("D".to_string()));
                assert_eq!(comp, "M");
                assert_eq!(jump, None);
            }
            _ => panic!("Expected C-instruction"),
        }

        // C-instruction with whitespace around semicolon (trimmed by parse logic)
        match parse_instruction_type("D ; JGT") {
            InstructionType::C { dest, comp, jump } => {
                assert_eq!(dest, None);
                assert_eq!(comp, "D");
                assert_eq!(jump, Some("JGT".to_string()));
            }
            _ => panic!("Expected C-instruction"),
        }
    }

    #[test]
    fn test_parse_multiple_equals_and_semicolons() {
        // Multiple equals signs - should use first one
        match parse_instruction_type("D=M=N") {
            InstructionType::C { dest, comp, jump } => {
                assert_eq!(dest, Some("D".to_string()));
                assert_eq!(comp, "M=N"); // Rest after first =
                assert_eq!(jump, None);
            }
            _ => panic!("Expected C-instruction"),
        }

        // Multiple semicolons - should use first one
        match parse_instruction_type("D;JGT;JEQ") {
            InstructionType::C { dest, comp, jump } => {
                assert_eq!(dest, None);
                assert_eq!(comp, "D");
                assert_eq!(jump, Some("JGT;JEQ".to_string())); // Rest after first ;
            }
            _ => panic!("Expected C-instruction"),
        }
    }

    #[test]
    fn test_parse_a_instruction_variations() {
        // Standard A-instruction
        match parse_instruction_type("@123") {
            InstructionType::A(val) => assert_eq!(val, "123"),
            _ => panic!("Expected A-instruction"),
        }

        // A-instruction with symbol
        match parse_instruction_type("@LABEL") {
            InstructionType::A(val) => assert_eq!(val, "LABEL"),
            _ => panic!("Expected A-instruction"),
        }

        // A-instruction with whitespace (should be trimmed by preprocess)
        match parse_instruction_type("@  123  ") {
            InstructionType::A(val) => assert_eq!(val.trim(), "123"),
            _ => panic!("Expected A-instruction"),
        }
    }

    // ============================================================================
    // PREPROCESSING EDGE CASE TESTS
    // ============================================================================

    #[test]
    fn test_preprocess_line_edge_cases() {
        // Tabs
        assert_eq!(preprocess_line("\t@123\t"), "@123");

        // Mixed whitespace
        assert_eq!(preprocess_line("  \t  @123  \t  "), "@123");

        // Multiple comment markers (should only remove first)
        assert_eq!(preprocess_line("D=M // comment // another"), "D=M");

        // Comment with special characters
        assert_eq!(preprocess_line("D=M // comment with @ and ="), "D=M");

        // Comment at start
        assert_eq!(preprocess_line("// comment at start"), "");

        // Comment only
        assert_eq!(preprocess_line("//"), "");

        // No comment
        assert_eq!(preprocess_line("D=M"), "D=M");

        // Only whitespace
        assert_eq!(preprocess_line("   \t  "), "");

        // Empty string
        assert_eq!(preprocess_line(""), "");

        // Comment with no space
        assert_eq!(preprocess_line("D=M//comment"), "D=M");
    }

    #[test]
    fn test_preprocess_line_preserves_instruction() {
        // Ensure preprocessing doesn't break valid instructions
        assert_eq!(preprocess_line("@123 // comment"), "@123");
        assert_eq!(preprocess_line("D=M // comment"), "D=M");
        assert_eq!(preprocess_line("D;JGT // comment"), "D;JGT");
        assert_eq!(preprocess_line("(LABEL) // comment"), "(LABEL)");
    }

    // ============================================================================
    // LOCATION COUNTER TESTS
    // ============================================================================

    #[test]
    fn test_location_counter_increments() {
        // All three A-instructions should increment location counter
        // So location counter should be 3 after processing
        // (Labels point to next instruction, so if we had a label at start,
        // it would point to address 0)
        let code = "(LABEL)\n@1\n@2\n@3\n";
        let symbol_table = first_pass(code).unwrap();
        assert_eq!(symbol_table.get("LABEL"), Some(0)); // Points to first @1
    }

    #[test]
    fn test_location_counter_with_labels() {
        let code = "@1\n(LABEL)\n@2\n@3\n";
        let symbol_table = first_pass(code).unwrap();

        // LABEL should point to address 1 (after first @1)
        assert_eq!(symbol_table.get("LABEL"), Some(1));
    }

    #[test]
    fn test_location_counter_skips_labels() {
        let code = "(LABEL1)\n(LABEL2)\n@1\n";
        let symbol_table = first_pass(code).unwrap();

        // Both labels should point to address 0 (next instruction)
        assert_eq!(symbol_table.get("LABEL1"), Some(0));
        assert_eq!(symbol_table.get("LABEL2"), Some(0));
    }

    // ============================================================================
    // ADDRESS RESOLUTION EDGE CASE TESTS
    // ============================================================================

    #[test]
    fn test_resolve_address_numeric_literals() {
        let mut symbol_table = SymbolTable::new();
        let mut variable_counter = VAR_START_ADDRESS;

        // Test zero
        assert_eq!(
            resolve_address("0", &mut symbol_table, &mut variable_counter, 1, "test").unwrap(),
            0
        );

        // Test max u16
        assert_eq!(
            resolve_address("65535", &mut symbol_table, &mut variable_counter, 1, "test").unwrap(),
            65535
        );

        // Test various numbers
        assert_eq!(
            resolve_address("42", &mut symbol_table, &mut variable_counter, 1, "test").unwrap(),
            42
        );
        assert_eq!(
            resolve_address("100", &mut symbol_table, &mut variable_counter, 1, "test").unwrap(),
            100
        );
    }

    #[test]
    fn test_resolve_address_symbol_resolution_order() {
        let mut symbol_table = SymbolTable::new();
        let mut variable_counter = VAR_START_ADDRESS;

        // Number should be parsed first (not allocated as variable)
        assert_eq!(
            resolve_address("16", &mut symbol_table, &mut variable_counter, 1, "test").unwrap(),
            16
        );
        assert_eq!(variable_counter, VAR_START_ADDRESS); // Counter shouldn't increment

        // Predefined symbol should be found
        assert_eq!(
            resolve_address("R0", &mut symbol_table, &mut variable_counter, 1, "test").unwrap(),
            0
        );
        assert_eq!(variable_counter, VAR_START_ADDRESS); // Counter shouldn't increment

        // New symbol should be allocated
        assert_eq!(
            resolve_address(
                "NEWVAR",
                &mut symbol_table,
                &mut variable_counter,
                1,
                "test"
            )
            .unwrap(),
            VAR_START_ADDRESS
        );
        assert_eq!(variable_counter, VAR_START_ADDRESS + 1); // Counter should increment
    }

    #[test]
    fn test_resolve_address_variable_counter_increments() {
        let mut symbol_table = SymbolTable::new();
        let mut variable_counter = VAR_START_ADDRESS;

        // Allocate first variable
        resolve_address("var1", &mut symbol_table, &mut variable_counter, 1, "test").unwrap();
        assert_eq!(variable_counter, VAR_START_ADDRESS + 1);

        // Allocate second variable
        resolve_address("var2", &mut symbol_table, &mut variable_counter, 1, "test").unwrap();
        assert_eq!(variable_counter, VAR_START_ADDRESS + 2);

        // Reuse first variable - counter shouldn't increment
        resolve_address("var1", &mut symbol_table, &mut variable_counter, 1, "test").unwrap();
        assert_eq!(variable_counter, VAR_START_ADDRESS + 2); // Should stay same
    }
}
