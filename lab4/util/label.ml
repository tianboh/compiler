(* C0 Compiler
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
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

let cache : t Int.Table.t = Int.Table.create ()
let next_unique_id = ref 0

(* Generate a new label *)
let label (name : string option) : t =
  let unique_id = !next_unique_id in
  let name =
    match name with
    | None -> ""
    | Some s -> s
  in
  let t = { name; unique_id } in
  incr next_unique_id;
  Hashtbl.add_exn cache ~key:unique_id ~data:t;
  t
;;

let name : t -> string = fun x -> "_" ^ x.name ^ "_" ^ Int.to_string x.unique_id
let content t = name t ^ ":"

include Comparable.Make (T)

module Handler = struct
  let sigfpe = label (Some "sigfpe")
  let sigabrt = label (Some "sigabrt")
  let sigusr2 = label (Some "sigusr2")
end
