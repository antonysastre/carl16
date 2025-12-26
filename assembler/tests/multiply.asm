// multiply.asm
// Test: Multiplication using repeated addition
// Multiplies R0 * R1 using a loop, stores result in R2

  @R0
  D=M
  @x
  M=D

  @R1
  D=M
  @y
  M=D

  @i
  M=1

  @sum
  M=0

(LOOP)
  @i
  D=M
  @x
  D=D-M
  @STOP
  D;JGT

  @y
  D=M
  @sum
  D=D+M
  @sum
  M=D
  @i
  M=M+1
  @LOOP
  0;JMP

(STOP)
  @sum
  D=M
  @R2
  M=D

(END)
  @END
  0;JMP
