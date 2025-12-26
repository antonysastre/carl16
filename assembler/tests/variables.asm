// variables.asm
// Test: Variable manipulation and swapping
// Swaps the values of R0 and R1 using a temporary variable

  @R1
  D=M
  @temp
  M=D

  @R0
  D=M
  @R1
  M=D

  @temp
  D=M
  @R0
  M=D

(END)
  @END
  0;JMP