// rectangle.asm
// Test: Interactive screen drawing with keyboard input
// Fills/clears the entire screen based on keyboard input
// Press any key to fill screen black, release to clear

@SCREEN
  D=A
  @drow
  M=D

  @8191
  D=A
  @n
  M=D

  @i
  M=0

(LOOP)
  @i
  D=M
  @n
  D=D-M
  @RESET
  D;JGT

  @KBD
  D=M
  @BLACK
  D;JGT

  @drow
  A=M
  M=0
  @CONT
  0;JMP

(BLACK)
  @drow
  A=M
  M=-1

(CONT)
  @i
  M=M+1
  @drow
  M=M+1
  @LOOP
  0;JMP

(RESET)
  @i
  M=0

  @SCREEN
  D=A
  @drow
  M=D

  @LOOP
  0;JMP