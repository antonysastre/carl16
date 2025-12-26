use c16::assemble_string;

#[test]
fn test_simple_a_instruction() {
    let source = "@42\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 1);
    assert_eq!(output[0], "0000000000101010"); // 42 in binary
}

#[test]
fn test_predefined_symbols() {
    let source = "@R0\n@R15\n@SP\n@SCREEN\n@KBD\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 5);
    assert_eq!(output[0], "0000000000000000"); // R0 = 0
    assert_eq!(output[1], "0000000000001111"); // R15 = 15
    assert_eq!(output[2], "0000000000000000"); // SP = 0
    assert_eq!(output[3], "0100000000000000"); // SCREEN = 16384
    assert_eq!(output[4], "0110000000000000"); // KBD = 24576
}

#[test]
fn test_variable_allocation() {
    let source = "@var1\n@var2\n@var1\n@var3\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 4);
    assert_eq!(output[0], "0000000000010000"); // var1 = RAM[16]
    assert_eq!(output[1], "0000000000010001"); // var2 = RAM[17]
    assert_eq!(output[2], "0000000000010000"); // var1 again (same address)
    assert_eq!(output[3], "0000000000010010"); // var3 = RAM[18]
}

#[test]
fn test_c_instruction_basic() {
    let source = "D=M\nM=D\n0;JMP\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 3);
    assert_eq!(output[0], "1111110000010000"); // D=M
    assert_eq!(output[1], "1110001100001000"); // M=D
    assert_eq!(output[2], "1110101010000111"); // 0;JMP
}

#[test]
fn test_labels_and_forward_references() {
    let source = "@END\n0;JMP\nD=1\n(END)\n@END\n0;JMP\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 5); // Labels don't generate code
    assert_eq!(output[0], "0000000000000011"); // @END points to instruction 3
    assert_eq!(output[1], "1110101010000111"); // 0;JMP
    assert_eq!(output[2], "1110111111010000"); // D=1
    assert_eq!(output[3], "0000000000000011"); // @END again
    assert_eq!(output[4], "1110101010000111"); // 0;JMP
}

#[test]
fn test_add_program() {
    let source = include_str!("add.asm");
    let output = assemble_string(source).expect("Assembly failed for add.asm");

    assert_eq!(output.len(), 8);
    assert_eq!(output[0], "0000000000000000"); // @0
    assert_eq!(output[1], "1111110000010000"); // D=M
    assert_eq!(output[2], "0000000000000001"); // @1
    assert_eq!(output[3], "1111000010010000"); // D=D+M
    assert_eq!(output[4], "0000000000000010"); // @2
    assert_eq!(output[5], "1110001100001000"); // M=D
    assert_eq!(output[6], "0000000000000111"); // @7
    assert_eq!(output[7], "1110101010000111"); // 0;JMP
}

#[test]
fn test_basic_program() {
    let source = include_str!("basic.asm");
    let output = assemble_string(source).expect("Assembly failed for basic.asm");

    assert_eq!(output.len(), 2);
    assert_eq!(output[0], "0000000011111111"); // @255
    assert_eq!(output[1], "1111110000010000"); // D=M
}

#[test]
fn test_branching_program() {
    let source = include_str!("branching.asm");
    let output = assemble_string(source).expect("Assembly failed for branching.asm");

    // Verify it generates code without errors
    assert!(output.len() > 5);

    // All lines should be valid 16-bit binary
    for line in &output {
        assert_eq!(line.len(), 16, "Each line should be 16 bits");
        assert!(
            line.chars().all(|c| c == '0' || c == '1'),
            "Should only contain 0 and 1"
        );
    }
}

#[test]
fn test_iteration_program() {
    let source = include_str!("iteration.asm");
    let output = assemble_string(source).expect("Assembly failed for iteration.asm");

    // Verify it generates code without errors
    assert!(output.len() > 10);

    // Verify binary format
    for line in &output {
        assert_eq!(line.len(), 16);
        assert!(line.chars().all(|c| c == '0' || c == '1'));
    }
}

#[test]
fn test_variables_program() {
    let source = include_str!("variables.asm");
    let output = assemble_string(source).expect("Assembly failed for variables.asm");

    // Verify it generates code
    assert!(!output.is_empty());

    // Verify binary format
    for line in &output {
        assert_eq!(line.len(), 16);
        assert!(line.chars().all(|c| c == '0' || c == '1'));
    }
}

#[test]
fn test_comments_are_ignored() {
    let source = "// Full line comment\n@1 // Inline comment\nD=M // Another\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 2); // Only 2 instructions (comment line ignored)
}

#[test]
fn test_empty_lines_ignored() {
    let source = "@1\n\n\nD=M\n\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 2);
}

#[test]
fn test_all_jump_conditions() {
    let source = "D;JGT\nD;JEQ\nD;JGE\nD;JLT\nD;JNE\nD;JLE\n0;JMP\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 7);
    assert!(output[0].ends_with("001")); // JGT
    assert!(output[1].ends_with("010")); // JEQ
    assert!(output[2].ends_with("011")); // JGE
    assert!(output[3].ends_with("100")); // JLT
    assert!(output[4].ends_with("101")); // JNE
    assert!(output[5].ends_with("110")); // JLE
    assert!(output[6].ends_with("111")); // JMP
}

#[test]
fn test_all_destinations() {
    let source = "M=1\nD=1\nMD=1\nA=1\nAM=1\nAD=1\nAMD=1\n";
    let output = assemble_string(source).expect("Assembly failed");

    assert_eq!(output.len(), 7);
    // All should start with 111 (C-instruction)
    for line in &output {
        assert!(line.starts_with("111"));
    }
}

#[test]
fn test_invalid_computation() {
    let source = "D=INVALID\n";
    let result = assemble_string(source);

    assert!(result.is_err(), "Should fail on invalid computation");
}

#[test]
fn test_invalid_destination() {
    let source = "XYZ=1\n";
    let result = assemble_string(source);

    assert!(result.is_err(), "Should fail on invalid destination");
}

#[test]
fn test_invalid_jump() {
    let source = "D;INVALID\n";
    let result = assemble_string(source);

    assert!(result.is_err(), "Should fail on invalid jump");
}
