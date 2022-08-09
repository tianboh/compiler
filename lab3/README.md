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
The dataflow analysis procedure is shown below:
### 1) Build control flow graph in terms of basic block
Lines within the same block are grouped together in order(dependes on forward/backward, check dfana.ml for more details). Gen, kill, successor, predecessor field are calculated for each basic block(BB) in this step. Specifically, traverse each statement by order and update as below:

    gen[BB] <- gen[BB] U gen[s] - kill[s]

    kill[BB] <- kill[BB] U kill[s] - gen[s]

Complexity: O(l) where l is number of lines in input file.
### 2) Update block until converge
Initialize the process queue(check dfana.ml for details about the order).

For forward-may analysis, we calculate in set by

    in[BB] <- U out[BB'] where BB' are predecessors of BB. out[BB'] are initialized to empty set in the begining.

For forward-must analysis, 

    in[BB] <- Intersect out[BB'] where BB' are predecessors of BB. out[BB'] are initialized to full set.

Then use below formula to update out set for BB. If new out[BB] is different from previous ones, then push its successors to process queue.

    out[BB] <- gen[BB] U (in[BB] - kill) 

Complexity: Check [notes](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/lec/09-df-theory.pdf) for details.
### 3) Transform from block to line
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