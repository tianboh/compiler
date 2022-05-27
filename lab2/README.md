# L1 Compiler

## Overview
lab1 is register allocation. Students are required to 
1) Submit 10 test cases for l1 including scenarios in success, error and exception.
2) Implement register allocation algorithm.
The temporaries in test input file is formatted to be SSA.
More information can be reached in [handout](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab1.pdf) and [checkpoint](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab1checkpoint.pdf).

## Data structure
Hash table from register to register Set as adjacency list to denote interference graph.

## Algorithm
The basic allocation procedure follows:
### 1) Build interference graph
We build edge from line.define to line.live_out. We do not build clique based on live_out because this may ignore dependency between define and live_out. For example, if the defined temporary is not used in the future, so it may not in live_out set, then scheduler may allocate a register which is already allocated for the live_out for the current register (because there is no edge between define and live_out). 
PS:If we can eliminate redundant defination in SSA, which means every defination will be in the live_out set, then we can build clique purely based on live_out set.
Complexity: O(v + e)
### 2) Build SEO
Theoratically, We initialize every vertex with weight 0. Then, each time we start from a vertex u with maximum weight and update its neighbors weight by one. Then we record vertex u and delete from graph, and keep doing so until no vertex left on graph. There are lines where %eax or %edx is in the define field. We isolate these nodes in the interferance graph because interferance graph is used to describe the relationship between temporaries during register alloc to keep the consistance, we do not use %eax nor %edx for temporary register allcation as well. In addition, for line whose define field is %eax or %edx, we do not allocate other register as well, which means these lines will use %eax or %edx to execute. This avoid superfluous allocation. Notice temporaries in interference graph is pure SSA. So we can apply maximum cardinality to find optimal register allocation policy.
Complexity: O(v + e)
### 3) Greedy coloring based on SEO
Greedy assign registers in SEO order. We generate register name based on %rxx. where xx is index number. The rule is generate register with minimum index which is greater than its allocated neighbors.
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