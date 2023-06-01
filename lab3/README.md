# L3 Compiler

## Overview Workflow

**l3 program** ——c0_lexer, c0_parser——> **CST** ——elaborate——> **AST** ——semantic analysis——> **AST** ——ir_tree_trans——> **IR trees** ——dominator tree——> **IR trees in SSA form** ——quads_trans——> **Quads**  ——abs_codegen——> **Abstract Assembly** ——dataflow graph, liveness analysis, register allocation, x86codegen——> **x86-64 machine code**


## CST
CST stands for Concret Syntax Tree, it is parsed from l3 source file. CST eliminate parenthesis and brackets compared with the actual syntax tree. However, the basic structure for CST and actual syntax tree is the same, for example, CST have if, while, for, block, postops etc.

## Elaboration and AST
In order to make following analysis simpler, an elaboration pass is added after CST is constructed. The elaborated syntax tree is AST(Abstract Syntax Tree). This elaboration pass tries to simplify CST through

* for loops are elaborated into while loop.
* Unary operations(negative, logical not, bitwise not) are elaborated into binary operations by identical value.
* Logical operations are elaborated to ternary operation.
* Bin assign operations (like +=, *=, etc.) are elaborated to binary operation.
* Declare is elaborated to provide a namespace for the variable. So typecheck and controlflow check is much easier on AST.
* Custom typenames are elaborated to primitive type

Elaboration pass also provides simple checks for type definations because type alias is elaborated afterwards.

* Type definitions cannot conflict with variable names.
* Type definitions cannot conflict with function names.
* Type definitions cannot alias void. 
* Same type definition only declared once.
* No variable declaration at for loop iteration filed.

## Semantic Analysis
Semantic analysis checks variable and function semantic correctness on AST. Specifically, it checks

* Variables are declared before defination, and all variables are defined before usage.
* No variable can be declared more than once.
* Variable names do not collide with type names, but can shadow function names.
* No variable of type void. Void is only used as return type for function.
* Functions may be declared more than once, but with the same argument and return type.
* Functions are defined before calling, forward declare allowed.
* Expressions are well typed. Including function call arguments, variable assignment, conditions, return etc. 
* Control flow path with non-void return has proper returned.

## IR tree
The IR data structure provides assembly-like statements and expressions. High-level controlflow statements in AST, like while and if, are translated to low-level jump and conditional jump in IR. Ternary operation are also translated to statements with jump.

Statements may have side effect and expressions are guaranteed to be effect-free. Some expressions(div, mod, shift) are transformed to effect statement, and the rest are pure as it is. New temporaries are created as destination of expressions with side-effect. 

Variables in AST are translated to temporary in IR. Boolean constant is replaced with integer(true for 1 and false for 0). 

## Dominator and SSA
SSA is built on IR trees. SSA is composed with basic blocks, where each block start with a label and read until next label. SSA first build dominator trees based on [A Simple, Fast Dominance Algorithm](https://www.cs.rice.edu/~keith/EMBED/dom.pdf).

Then, use [SSA algorithm](https://pfalcon.github.io/ssabook/latest/book.pdf)(section 3) to rename the temporaries. Critical edges are properly handled at the end of SSA. Also, SSA works for each function independently, and their parameters are translated to a block at the beginning of the function body. So the rename process takes into parameters as well.

Notice that parallel copy in SSA deconstruction is not finished yet. This is still a ongoing task.

## Quads
Quads is of assembly-like instructions. IR statements are translated to instructions using maximal munch algorithm. IR expressions are translated to binary/move instructions. 

Quads provide operand of temporary and immediate. Quads is hardware-independent, so operands of register and memory are not provided.

## Abstract Assembly
Abstract assembly provides operand of register, frame memory, temporary and immediate. This is the immediate layer before register allocation, so information for define, use, liveout is attached to each instruction. Instructions requiring special registers can add those registers to define field, so register allocation algorithm will preserve those register unassigned when those instructions are executed. In the x86 assembly code generation, we can move operand/destination to those special registers without risk.

Instructions with special register treatments are

* Div and mod. Preserve %RAX and %RDX.
* Shift. Preserve %RCX.

Calling a function will 

* Move parameters to %RDI, %RSI, %RDX, %RCX, %R8, %R9 respectively. If parameters are more than 6, then push them to the memory. Last parameter is pushed first, and gradually to the 7th.
* Save caller-saved register by defining %R10 and %R11 at fcall instruction. 
* Preserve parameter registers by defining %RDI, %RSI, %RDX, %RCX, %R8, %R9 at fcall as well. So the parameter source will not collide with those registers.
* Preserve return register %RAX by defining it at fcall.

When a function is called, it will 

* Save %RBP(caller func return address) and update %RBP to %RSP(called func address) based on local allocated memory.
* Store the callee-saved registers.
* Read parameters from registers. Read from memories if necessary.
* Execute function. Move result to %RAX if function returns.
* Restore callee-saved registers.
* Restore %RBP and %RSP.

## Dataflow analysis
Dataflow analysis provide four modes: forward/backward must/may analysis. Now we only need liveness analysis(backward may analysis) to allocate register. Abstract assembly code within a function defination will be decomposed to basic blocks. Define and use information is used to calculate liveout info. Operand in this process is of int type, and each value represents a unique register/temporary in abstract assembly operand. 0-15 represent 16 general registers, and higher value represent distinct temporaries.

## Register allocation
Interference graph edge is built between def and liveout for each instruction. Some instructions may define multiple registers/temporaries, and they are mutually linked as well.

Register allocation is done based on interference graph. Pre-color is not necessary because special registers are already preserved for those special instructions. Simply apply SEO and greedy coloring will do the rest work.

13 registers are available for allocation. %RBP and %RSP are preserved for function call return address. And %R15 is used as swap register.

If there are more than 5000 temporaries in the graph, it may cost much time to run the algorithm. In this case, it will spill all temporary to stack and do not allocate any register.

## x86-64 machine code
Abstract assembly code is translated to x86-64 machine code based on the information of register allocation. The transformation includs

* Transform temporary to allocated register/memory address.
* Transform frame memory(used in function call parameter passing) to real memory
* Compared result is calculated by CMP and a followed SETCC.
* MOV use swap register to handle memory to memory move.
* RAX and RDX are preserved for div, mod. CVT is used to extend higher bits.
* RCX is preserved for SAL and SAR.
* Safety check for SAL and SAR is done by cmp and jump tp fpe handler.
* Based on allocated memory, provide callee function rsp subtraction value.