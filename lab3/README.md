# L2 Compiler

## Overview
lab2 is dataflow analysis. Students are required to 
1) Submit 10 test cases for l2 including scenarios in success, error and exception.
2) Implement dataflow analysis algorithm.
Core concept in dataflow analysis is gen and kill set. Each expression has a value on the left and an
expression on the right. Gen is the right side part. Kill corresponds to expression using left side part.
More information can be reached in [handout](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2.pdf) and [checkpoint](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2checkpoint.pdf).

## Data structure
Instead of traversing line by line, we use basic block as the traverse unit. Each block has gen, kill, pred, succ, in and out field. Once we calculate in set and out set for each block, we calculate in and out set for each line from the end/beginning of each block.

## Algorithm
The dataflow analysis procedure is shown below, we first provide a dataflow analysis by statement, and then take block as a unit.

### 1) Dataflow analysis algorithm by statement and complexity
The dataflow analysis algorithm works as follows, check tiger book chapter 10 for more details. Here we take liveness analysis as an example to show complexity.
```
for each statement n
    in[n] <- {}
    out[n] <- {}
repeat
    for each statement n
        in'[n] <- in[n]; out'[n] <- out[n]
        out[n] = U in[s] for s belongs to successors of n
        in[n] = use[n] U (out[n] - def[n])
until in[n] = in'[n] and out[n] = out'[n]
```

Complexity analysis

Initialization will take $O(n)$.

The repeat part will run $O(n^2)$ iterations to terminate. We can union the in set and out set for every statements. Then this set will at most have $2n^2$ elements. Remeber each statement will have at most n element in its in set and its out set. So n statements will have at most $2n^2$ elements. Also notice that the in and out set for each statement will be increase monotonically(def and use are fixed, so the increase for in set will lead to increase for out set due to union operation, vice versa). Each iteration(update the whole n statements) will increase at least one element, otherwise it will terminate. There are at most $2n^2$ elements in the union set, so it will terminate at most $2n^2$ times iteration.

Each iteration in the repeat part will traverse n statement, each statement will take $O(n)$ time to union(order the element and then use merge sort to union). So each iteration will take $O(n^2)$ complexity. 

Therefore, the overall complexity is $O(n^4)$. If we use bit vector to denote the set, then the union takes $O(1)$, and the overall compelxity is $O(n^3)$

### 2) Worklist algorithm complexity
We provide naive dataflow analysis complexity, now we introduce worklist algorithm and its complexity.
We take forward union analysis as an example here.
```
for each statement n
    in[n] <- {}
    out[n] <- {}
Q <- first statement
while Q not empty
    for any statement n in Q:
        remove n from Q
        out'[n] <- out[n]
        in[n] = U out[s] for s belongs to predecessor of n
        out[n] = gen[n] U (in[n] - kill[n])
        if out[n] != out'[n] then Q <- Q U succ[n]
```
Complexity analysis

Initialization will take $O(n)$.

The repeat part will run $O(nk)$ iterations to terminate. There are two constraints, which is satisfied for all gen-kill scenarios.
1) Transfer function is monotonic. Which means out[s] will never decrease in above example.
2) Lattice set is finite. Which means in[s] or out[s] cannot be infinite. Consider our program is finite, so the expression/variable
is obvious finite, so the set cannot be inifinite.

Suppose the longest path from top to fixed point in the lattice is $k$. The complexity for worklist algorithm is infact the number
of adding node happens. Each state s can change atmost k times, which is the longest path from top to the fixed point, and there are
n states, so the overall adding can be up to $O(nk)$ times. Notice that a state can atmost add 2 state once because their successor
can at most be two, which is the case for CJump.

Each iteration in the repeat part will traverse n statement, each statement will take $O(n)$ time to union(order the element and then use merge sort to union). So each iteration will take $O(n^2)$ complexity. 

Therefore, the overall complexity is $O(n^2k)$. If we use bit vector to denote the set for each statement, the complexity for union is 
O(1), then the overall complexity for worklist algorithm is $O(nk)$

### 3) Build control flow graph in terms of basic block
Lines within the same block are grouped together in order(dependes on forward/backward, check dfana.ml for more details). Gen, kill, successor, predecessor field are calculated for each basic block(BB) in this step. Specifically, traverse each statement by order and update as below:

    gen[BB] <- gen[BB] U gen[s] - kill[s]

    kill[BB] <- kill[BB] U kill[s] - gen[s]

Complexity: O(l) where l is number of lines in input file.

### 4) Update block until converge
Initialize the process queue(check dfana.ml for details about the order).

For forward-may analysis, we calculate in set by

    in[BB] <- U out[BB'] where BB' are predecessors of BB. out[BB'] are initialized to empty set in the begining.

For forward-must analysis, 

    in[BB] <- Intersect out[BB'] where BB' are predecessors of BB. out[BB'] are initialized to full set.

Then use below formula to update out set for BB. If new out[BB] is different from previous ones, then push its successors to process queue.

    out[BB] <- gen[BB] U (in[BB] - kill) 

Complexity: Check [notes](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/lec/09-df-theory.pdf) for details.
### 5) Transform from block to line
Finally, we should traverse each block and transfrom from block in/out set to line in/out set. We can apply in and out formula in terms of line from above step.

Complexity: O(l)
    
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
Then, save the hand written test cases to /workspace/tests/l2-my-tests, then run
```
/workspace/compiler# ../runverifier l2-my-tests
```

### Task 2 (dataflow analysis)
Modify ROOT_PROJECT/runverifier, change the last line to
```
"$script_directory/harness/runHarness" verifyCheckpoint "$@"
``` 
then run
```
cd /workspace/compiler
../runverifier l2-basic-checkpoint
../runverifier l2-large-checkpoint
```