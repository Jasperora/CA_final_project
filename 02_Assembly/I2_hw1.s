.data
    n: .word 10
    
.text
.globl __start

FUNCTION:
  # Todo: Define your own function in HW1
  # You should store the output into x10

  addi sp, sp, -8
  sw x1, 0(sp)
  jal x1, T
  lw x1, 0(sp)
  addi sp, sp, 8

  add x10, x0, a1
  jalr x0, 0(x1)
  
T:
  addi sp, sp, -16
  sw x1, 8(sp)
  sw a0, 0(sp)
  
  addi t2, x0, 1
  bne a0, t2, L1  # if n != 1
  
  lw a0, 0(sp)
  lw x1, 8(sp)
  addi sp, sp, 16
  
  addi a1, x0, 2 # else return 2
  
  jalr x0, 0(x1)
  
L1:
  srli a0, a0, 1 # t1 = ceil(n/2)
  jal x1, T
  
  lw a0, 0(sp)
  lw x1, 8(sp)
  addi sp, sp, 16
  
  addi t2, x0, 5
  mul a1, a1, t2 # a1 = 5T(n/2)
  addi a1, a1, 4 # a1 = 5T(n/2) + 4
  addi t2, x0, 6
  mul t2, t2, a0
  add a1, a1, t2 # a1 = 5T(n/2) + 6n + 4
  
  jalr x0, 0(x1) # return 0
    

# Do NOT modify this part!!!
__start:
  la   t0, n
  lw   x10, 0(t0)
  jal  x1,FUNCTION
  la   t0, n
  sw   x10, 4(t0)
  addi a0,x0,10
  ecall