# L1 Compiler

## Overview
lab1 is register allocation. Students are required to 
1) Submit 10 test cases for l1 including scenarios in success, error and exception.
2) Implement register allocation algorithm.
3) Generate AT&T x86 assembly code for L1 syntax.
The temporaries in test input file is formatted to be SSA.
More information can be reached in [handout](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab1.pdf) and [checkpoint](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab1checkpoint.pdf).

## Data structure
We use hash table from temp to temp Set as adjacency list to denote interference graph. Notice that interference graph only records interference info between temporaries. Once SEO and greedy coloring are done, relationship between temporaries and registers is generated.

## x86 Assembly Code Generation
Part of code generation has already done in starter code. However, we need to generate x86 instructions in AT&T convention based on pseudo code. I will talk about x86 AT&T convention including: 1) register restrictions(precolor) for special op like div, mod and mul, and 2) special usage for general purpose registers(i know its ridiculous, but it's convention).

Then I will show the const propagation based on SSA. This will greatly reduce the time cost for register allocation. It demonstrates up to 5 time faster in compilation, and better performance in runtime because optimized code has less temporary and less memory read/write operation(read from spilled register). 
### x86 Hardware Feature and AT&T Syntax
x86 instruction set provides a variety of operand source including immediate, register and memory. However, there are some restrictions for some instructions.
1) For imul(stands for integer multiplication), the result is stored in RDX:RAX(for 64 bit operand. RDX will store higher bits and RAX lower bits. If the operand is 32 bit, result will be stored in EDX:EAX). We cannot assign the multiplied result to any other registers. 
2) For idiv(integer divide). The quotient is stored in RAX and remainder is stored in RDX. Therefore mod instruction will use idiv x86 instruction as well. Check [idiv](https://www.felixcloutier.com/x86/idiv) for more details. 

There are only 15 general purpose registers, some of them are used specially like RBP and RSP. Also, some registers are caller saved registers and some are callee saved registers. We follow this conventions during x86 code generation. Check (AT&T assembly syntax and IA-32 instructions)[https://gist.github.com/mishurov/6bcf04df329973c15044] for more details.

There are two mainstream x86 instruction formats including Intel and AT&T. The main difference is the memory address representation and the order between source and destination in binary instruction. More details can be found in [AT&T Syntax versus Intel Syntax](https://www.cs.mcgill.ca/~cs573/winter2001/AttLinux_syntax.htm). 

Notice that our operating system is Ubuntu 20.04, which is 64 bit. However, our operand is 32 bit. In order to make things easier to explain, we omit this difference in this README.md and take our x86 instruction is of 64 bit. However, our implementation take this issue carefully by adding a field which specify 32/64 bit for instructions. Also, some operation related to base pointer and stack pointer should use RBP and RSP during implementation even though it is 32-bit instruction set because our OS is 64 bit.
#### Precolor
We need to assign each temporary with a register during register allocation. However, some temporaries must be bind to some specific registers. For example, the result of multiplication, division and module should be stored in RAX/RDX. Some compilers assign RAX/RDX to these temporaries during register allocation before other temporaries get assigned, so it is called precolor. 

However, we will handle this issue in another way. During pseudo code generation, we do not specify any hardware specific requirement. The binary pseudo instruction is of format t1 <- t2 binop t3. t1 and t2 are not assigned to the same register as x86 convention requires. Also, t1 can be assigned to any registers, where x86 requires result of mul, div, mod located at RAX/RDX. Our register allocation algorithm will follow this format and do not assign RAX/RDX to the result of mul, div and mod. The key here is we preserve RAX and RDX during register allocation, and they are not assigned to any temporaries during allocation. When we generate x86 assembly code based on pseudo code and register allocation information, we will add padding instructions for mul, div, and mod as following. We take RAX/RDX as a intermediate register to keep result of mul, div and mod, and then move it to the destination. Also, we take R15 as a swap register and it is not assigned to any temporary during register allocation.
```
| Mul -> [AS_x86.Mov {dest=EAX; src=lhs; layout=DWORD};
          AS_x86.Mul {src=rhs; dest=EAX; layout=DWORD};
          AS_x86.Mov {dest=dest; src=EAX; layout=DWORD}]
| Div -> [AS_x86.Mov {dest=EAX; src=lhs; layout=DWORD};
          AS_x86.Mov {dest=AS_x86.Reg swap; src=rhs; layout=DWORD};
          AS_x86.Cvt {layout=DWORD};
          AS_x86.Div {src=AS_x86.Reg swap; layout=DWORD};
          AS_x86.Mov {dest=dest; src=EAX; layout=DWORD};] 
| Mod -> [AS_x86.Mov {dest=EAX; src=lhs; layout=DWORD};
          AS_x86.Mov {dest=AS_x86.Reg swap; src=rhs; layout=DWORD};
          AS_x86.Cvt {layout=DWORD};
          AS_x86.Div {src=AS_x86.Reg swap; layout=DWORD};
          AS_x86.Mov {dest=dest; src=EDX; layout=DWORD};]
```
#### General Registers
There are 15 general purpose registers in x86. If we need more registers, we will use spill registers, which in fact are memory locations. There are caller saved registers: RAX, RCX, and RDX. Callee saved registers are RBX, RDI, RSI, RSP and RBP. We will save them properly before calling any functions including the main function.

We can calculate the number of required registers during register allocation, before x86 instructions are generated. So we know how many registers to spill and we can preserve enough space in stack and use them as spilled registers. 
### SSA
SSA stands for Single Static Assignment. Which means a temporary will only be assigned once. Its value will never be changed. SSA is of pseudo assembly code level, and it is not conflict if source code or x86 assembly code are not SSA. In other words, our goal is to generate SSA pseudo assembly code from a non SSA high level source code.

The key to achieve SSA in lab1 is to generate a fresh new temporary for each destination in instruction. It will only be used on right hand side of each instruction. So it achieves "one time initialization and never change" goal. We use mov instruction to take the generated temporary as operand for other instruction. However, this may produce lots of redundant temporaries and make register allocation quite slow. Also redundant temporaries will lead to redundant spilled registers. Use spilled registers can greatly degrade program performance because memory access is time-consuming.
### Optimizations
In order to tackle above issue, we need to eliminate redundant temporaries and still keep pseudo code as SSA. So we deploy const propagation strategy in the optimization. Optimized pseudo code will eliminate redundant move instructions and temporaries are replaced by immediate as much as possible. Chain like below are settled as well like
```
a <- 1
b <- a
c <- b
d <- b + c
```
The optimized pseudo code is of, and each use of b and c is replaced by 1.
```
a <- 1
d <- 1 + 1
```
## Register Allocation Algorithm
The basic allocation procedure follows:
### 1) Build interference graph
We build edge from line.define to line.live_out. Nodes represent temporaries in the interference graph. We do not build clique based on live_out because this may ignore dependency between define and live_out. For example, if the defined temporary is not used in the future, so it may not in live_out set, then scheduler may allocate a register which is already allocated for the live_out for the current register (because there is no edge between define and live_out). 
PS:If we can eliminate redundant defination in SSA, which means every defination will be in the live_out set, then we can build clique purely based on live_out set.
Complexity: O(v + e)
### 2) Build SEO
Theoratically, We initialize every vertex with weight 0. Then, each time we start from a vertex u with maximum weight and update its neighbors weight by one. Then we record vertex u and delete from graph, and keep doing so until no vertex left on graph. Notice temporaries in interference graph is pure SSA. So we can apply maximum cardinality to find optimal register allocation policy.

Also, since we preserve RAX and RDX during register allocation, so there is no pre-coloring in the SEO or greedy coloring. Each node(temporary) in the interference graph can be assigned to any available registers. 
Complexity: O(v + e)
### 3) Greedy coloring based on SEO
Greedy assign registers in SEO order. We generate register name based on x86 convention, and %SXX as spilled register with index xx. The internal order is recorded as a index, and can be checked in x86_reg.ml file. The rule is generate register with minimum index which is greater than its allocated neighbors.
Complexity: O(v + e)
    
## Test
Start container. Mount workspace to the Root project which contains test cases. Root project contains compiler directory.
sudo docker run -v ROOT_PROJECT:/workspace --name 411 -td cmu411/autograder-ocaml
### Task 1 (test cases)
First, modify ROOT_PROJECT/runverifier, change the last line from 
```
"$script_directory/harness/runHarness" verifyCheckpoint "$@"
``` 
to 
```
"$script_directory/harness/runHarness" gradeTests "$@"
```
Then, save the hand written test cases to /workspace/tests/l1-my-tests, then run
```
/workspace/compiler# ../runverifier l1-my-tests
```

### Task 2 (register allocation)
```
cd /workspace/compiler
../runverifier l1-basic-checkpoint
../runverifier l1-large-checkpoint
```

### Task 3 (grade compiler)
```
cd /workspace/compiler
../gradecompiler  ../tests/l1-basic/
../gradecompiler  ../tests/l1-large/
```