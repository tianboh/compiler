(* L4 Compiler
 * Temporaries
 * 
 * Temporaries only store small type values
 *  - int
 *  - bool
 *  - pointer
 *  - array 
 * PS: array type is only a reference to array.
 *
 * Large type value is stored on heap and is out of temporary's
 * charge. We can access them through pointer or reference
 *  - struct
 *  - allocated array
 * 
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core

module T = struct
  type t = { id : int } [@@deriving sexp, compare, hash]

  let pp_exp (t : t) : string = sprintf "%%t%d" t.id
end

include T

let counter = ref 16
let reset () = counter := 16
let cache : t Int.Table.t = Int.Table.create ()

(* create and create' cannot be used at the same time *)
let create () : t =
  let id = !counter in
  ignore (incr counter : unit);
  let t = { id } in
  Hashtbl.add_exn cache ~key:id ~data:t;
  t
;;

(* Only used in checkpoint. *)
let create' (id : int) : t =
  let t = { id } in
  Hashtbl.add_exn cache ~key:id ~data:t;
  t
;;

let of_int (id : int) : t = Hashtbl.find_exn cache id
let count () = !counter
let name (t : t) : string = sprintf "%%t%d" t.id

let name' (t : t) (size : Size.primitive) : string =
  sprintf "%%t%d_%s" t.id (Size.pp_size size)
;;

let get_id (t : t) = t.id

include Comparable.Make (T)
