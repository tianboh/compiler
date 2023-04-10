(* (* Notice the difference between CST and AST
* CST is basically transferred from source code literaly.
* AST add more structure statement unit based on CST, and it looks like a tree.
*
* Statement level benefit:
* To be specific, AST classify statement from CST into below
* 1) Asign(x,e)
* 2) if(e,s,s)
* 3) while(e,s)
* 4) return(e)
* 5) nop
* 6) seq(s,s)
* 7) declare(x,t,s)
* The obvious advantage is that we can handle variable namespace more efficiently.
* We can see if the use of x is in a declare statement. Notice that the use of x 
* may be nested in many seq statement in declare(x,t,s).
* In addition, we will simplify for from CST to while statement in AST. 
* This will reduce the Intermediate Representation.
*
* Expression level benefit: we obtain from CST -> AST is that.
* 1) logical operation && || ^ can be denoted in ternary
* 2) <binop>= b can be simplified to a = a binop b
* This can simplify our work in IR level
* More details can be checked in 
* https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2.pdf Page 5 and 6
*
* Author: Tianbo Hao <tianboh@alumni.cmu.edu>
*)

let elab () = ();; *)