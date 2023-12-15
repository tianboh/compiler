(* C0 Compiler
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *)

open Core

module T = struct
  type t =
    { name : string [@compare.ignore] [@hash.ignore]
    ; unique_id : int
    }
  [@@deriving compare, hash, sexp]
end

include T

let cache : t String.Table.t = String.Table.create ()
let next_unique_id = ref 0

(* Variables declared in an outer scope (either as function parameters of
 * an enclosing block) can not be declared again in an inner block with the
 * same name. According to https://c0.cs.cmu.edu/docs/c0-reference.pdf Sec 6.5
 * In other words, Symbol.name can be used as the hash key. *)
let symbol (name : string) : t =
  match Hashtbl.find cache name with
  | Some t -> t
  | None ->
    let unique_id = !next_unique_id in
    let t = { name; unique_id } in
    incr next_unique_id;
    Hashtbl.add_exn cache ~key:name ~data:t;
    t
;;

let name : t -> string = fun x -> x.name

include Comparable.Make (T)

let c0_prefix =
  match Sys.getenv "UNAME" with
  | Some "Darwin" -> "__c0_"
  | _ -> "_c0_"
;;

(* There are three types of functions.
 * 1) C0 function. Generate from source file
 * 2) External. Declared in header file
 * 3) Internal. Compiler provided.
 * .globl provide C0 type function for linker. *)
let pp_scope = function
  | `C0 -> c0_prefix
  | `External -> ""
  | `Internal -> "_"
;;

module Fname = struct
  (* This module stores assembly function provided by GNU C library. 
   * Though the signature is C level, assembly version is implemented as well. *)

  (* void *calloc (size_t count, size_t eltsize)
   * <stdlib.h>
   * Allocate a block of count * eltsize bytes using malloc, and set its contents to
   * zero. See Section 3.2.3.5 [Allocating Cleared Space], page 49 *)
  let calloc = symbol "calloc"

  (* int raise (int signum)
   * <signal.h>
   * The raise function sends the signal signum to the calling process. 
   * It returns zero if successful and a nonzero value if it fails. 
   * About the only reason for failure would be if the value of signum is invalid. *)
  let raise = symbol "raise"

  (* check https://www.codequoi.com/en/sending-and-intercepting-a-signal-in-c/
   * for more signals. *)
  let abrt = 6L
  let fpe = 8L
  let segv = 11L
  let usr2 = 12L
end
