(* The entry point to your c0c executable. This module is run for its top level
 * effects. Here, we just call the main function from the Compiler library. You
 * shouldn't write any code in this file or add any files to this executable.
 * All your code should be written in the lib/ directory which you can use utop
 * on and write unit tests for. If you write code here, you won't be able to expect
 * test it or call into it in the REPL. *)
let () = Compiler.Top.main ()
