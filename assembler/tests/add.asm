// add.asm
// Test: Addition of two numbers
// Adds the values from memory addresses 0 and 1, stores result in address 2

@0
D=M
@1
D=D+M
@2
M=D
@7
0;JMP