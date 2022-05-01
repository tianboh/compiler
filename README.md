#### Authorship
 * Author: Frank Pfenning (<fp@cs.cmu.edu>)
 * Modified: Anand Subramanian (<asubrama@andrew.cmu.edu>)
 * Modified for OCaml from SML: Michael Duggan (<md5i@cs.cmu.edu>)
 * Modified: Alice Rao (<alrao@andrew.cmu.edu>)
 * Modified: Nick Roberts (<nroberts@alumni.cmu.edu>)
 * Modified: Henry Nelson (<hcnelson99@gmail.com>)

---

## Welcome to 15-411!

This is some starter code for the L1 compiler you have to build for Lab 1.  It contains a lexer, parser, translator, and even a code generator, except that the code generator creates pseudo assembly language with fictitious instructions and an unlimited number of registers.  We took some care to use good style (according to the past TAs); you may consider this a model for your own coding.  Feel free to modify any and all of this code as you see fit.

Bug reports to the course staff are welcome.

---

## OCaml Notes

If you use Windows, it is strongly recommended that you use an Ubuntu 18.04 LTS Windows subsystem, detailed [here](https://docs.microsoft.com/en-us/windows/wsl/install-win10).

This starter code assumes OCaml 4.10.0, the version available on the autograder. However, the starter code should work with any version >=4.08. There are a few steps to installing OCaml.

  1. Install the package manager [opam](https://opam.ocaml.org/doc/Install.html). The linked page includes a shell command that you can run to install opam directly.
  2. Initialize opam with the correct compiler version. You can run this command:
     ```
      opam init --dot-profile=~/.bashrc --auto-setup
     ```
     (If you use a different shell, like `zsh`, just change the dot profile as appropriate.) This command will take a while to finish. If the installation process fails, you may have to install the packages indicated by the error message. If you use Ubuntu 16.04, the `bubblewrap` package is not found in the apt repository, so you will have to install it manually ([example of this on GitHub](https://github.com/ocaml/opam/issues/3424#issuecomment-461660006)).
  3. Install packages used in the starter code. The starter code uses the Jane Street Core standard library replacement `core`,  the `ppx_jane` syntax extensions, the `cmdliner` package for getopt-like command line parsing, the `menhir` parser generator, the `yojson` json library, and some development tools. Run `opam install core.v0.14.0 ppx_jane cmdliner menhir yojson utop merlin ocamlformat` to install everything you will need.

For information on the OCaml Standard Library, ocamllex, and other sundry details, see: <http://caml.inria.fr/pub/docs/manual-ocaml-4.10/index.html>.

For documentation on the Core library, see:
<https://ocaml.janestreet.com/ocaml-core/v0.14/doc/core/Core/index.html>.

For documentation on menhir, see:
<http://gallium.inria.fr/~fpottier/menhir/manual.pdf>.

---

## Strongly consider using Merlin
If you use Vim, Atom, Emacs, Spacemacs, or VS Code, [Merlin](https://github.com/ocaml/merlin) is a must.
(See [here](https://github.com/hackwaly/vscode-ocaml) for the VS Code link.)

Merlin allows you to associate keyboard shortcuts with extremely useful actions:
  * Detect the type of the expression currently under the cursor.
  * Globally rename a symbol.
  * Autocomplete the identifier currently being typed. (Ever wanted to see all the bindings in a module, like List? Type "List." followed by the omnicomplete keybinding to see a navigable list of available functions.)

You should invest the few hours it takes to learn Merlin so that you can take advantage of its features for the entirety of this course.

Dune will automatically generate the correct .merlin files for your project.

---

## Expect testing

You can run expect tests using `dune runtest` in the starter code directory.
This will automatically run a special kind of test called an expect test.
Expect tests are tests which confirm that a certain snippet of code has a
certain output. In `lib/parse.ml`, you will see one such type of expect test,
which lexes and parses a string and then prints out resulting AST. When you run
`dune runtest`, the code in each expect test will be compiled and run and then
the output (from stdout) will be diffed with the text in the `[%expect {| |}]`
block (the `{| |}` is OCaml's multiline string syntax). The test passes if the
output is identical. If the output is different, `dune runtest` will notify you
that a test failed and show the diff. If you'd like to accept the latest output
as the new correct output, you can run `dune promote` and dune will
automatically replace the text in your `[%expect ]` block with the latest
output from running the tests.

Go ahead and try modifying the expect test to see what the diff looks like for
a failing test and how `dune promote` works. You can also try adding another
test to another part of the starter code to help understand how the starter
code works. Expect tests are also a great way to test and document the behavior
of your code as you write it. One benefit of expect tests is that they have
less maintenance burden than unit tests -- if the behavior of your code ever
changes and the new behavior is correct, you can just inspect the diffs and run
`dune promote` and all your tests will pass with no hassle.

---

## Utop: the better REPL

The default OCaml repl is not very user-friendly. Just try it out: it's called `ocaml`.

Fortunately, dune makes it easy to use `utop`, the improved REPL for ocaml. You
should have already installed it when following the installation steps above.
If installed, you can start a utop REPL for your compiler by running
`dune utop`.

You can then run small programs, like:

```
utop# open Core;;
utop# open Compiler;;
utop# let n = Mark.naked;;
utop# Typechecker.typecheck Ast.[ n (Return (n (Const 0l))) ];;
```

(Hopefully this clues you in on some nice features of OCaml, too, like opening
a module locally to an expression [e.g. the Ast module is open inside the
subsequent list literal] and int32 literals [e.g. `0l`]).

When starting a new REPL session, you will pretty much always want to start by
running `open Core;; open Compiler;;` to bring the jane street standard library
(core) and your compiler code into the top level namespace.

---

## Source Files
The following are the source files for the L1 compiler

    README.md               -- this file

    Makefile             -- makefile for the compiler
                            For a quick test

        % make          (generates file ../bin/c0c using dune build)

        % ../bin/c0c --verbose --emit abs ../tests/l1-basic/return01.l1.

                        should generate ../tests/l1-basic/return01.l1.abs in pseudo
                        assembly

        % make clean        (removes generated files)

    .merlin           The file that merlin uses for determining where build
                      artifacts are located. This is autogenerated by dune and
                      should not be committed.  Merlin is useful for
                      determining types of expressions and for autocomplete.

    ../bin/c0c        The native executable generated by the Makefile

    top.ml          This is the main driver.  It calls all the other parts
                    of the compiler.

    ast.ml          abstract syntax tree for the l1 language
    c0_lexer.mll    lexer for l1 (ocamllex file)
    c0_parser.mly   parser for l1 (menhir file)
    parse.ml        code that sets up and calls the parser/lexer

    typechecker.ml  basic type checker over the ast

    tree.ml         data structure representing the IR tree
    trans.ml        converts from the AST to the IR tree
    temp.ml         generates temporary variables on the fly

    assem.ml        representation of assembly used by the compiler
    codegen.ml      generates pseudo-assembly with temporaries from IR

    error_msg.ml    error message utilities
    mark.ml         library for tracking source file positions
    symbol.ml       symbol table library

---

Debugging Hints
---

`dune build ./bin/c0c.bc` will generate a debuggable bytecode version of the
compiler in `_build/default/bin/c0c.bc`.  You can run this in the OCaml debugger:

    ocamldebug _build/default/bin/c0c.bc
    set arguments ../tests/return01.l1
    step

The debugger is a time-traveling debugger.  It allows you to step
backwards as well as forwards.  See the OCaml manual for more
information.

You can use

    ../bin/c0c --verbose --dump-ast --dump-ir --dump-assem file.l1

to print information from all the phases of the current compiler.

You can use

    ../bin/c0c --debug-parse file.l1

to get a debug trace of the parser.

To get a state table for the parser, you can run

    menhir -v lib/c0_parser.mly

This will generate a `lib/c0_parser.automaton` file which contains
information about the parse states.  The `lib/c0_parser.conflicts` file will
also contain explanations of any parser state conflicts due to ambiguities in
your grammar. Remove the generated `lib/c0_parser.ml` and `lib/c0_parser.mli`
files before recompiling, as they will confuse dune.  (Try it and see. It is
kafe.)
