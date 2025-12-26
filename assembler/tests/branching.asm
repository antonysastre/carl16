// branching.asm
// Test: Conditional branching with JGT instruction
// Checks if R0 is positive; sets R1=1 if true, R1=0 if false

  @R0
  D=M
  @POSITIVE
  D;JGT
  @R1
  M=0
  @END
  0;JMP

(POSITIVE)
  @R1
  M=1

(END)
  @END
  0;JMP