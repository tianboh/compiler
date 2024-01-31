(* C0 Compiler
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core

module T = struct
  type t =
    { name : string [@compare.ignore] [@hash.ignore]
    ; unique_id : int
    ; is_unique : bool (* Only function name has unique label. *)
    }
  [@@deriving compare, hash, sexp]
end

include T

let id_table : t Int.Table.t = Int.Table.create ()

(* label -> id. Only stores unique label *)
let label_table : int String.Table.t = String.Table.create ()
let next_unique_id = ref 0

(* Generate a new label *)
let label (name : string option) : t =
  let unique_id = !next_unique_id in
  let name =
    match name with
    | None -> ""
    | Some s -> s
  in
  let t = { name; unique_id; is_unique = false } in
  incr next_unique_id;
  Int.Table.add_exn id_table ~key:unique_id ~data:t;
  t
;;

(* Generate unique label *)
let label' (name : string) : t =
  if String.Table.mem label_table name
  then (
    let id = String.Table.find_exn label_table name in
    Int.Table.find_exn id_table id)
  else (
    let unique_id = !next_unique_id in
    let t = { name; unique_id; is_unique = true } in
    incr next_unique_id;
    Int.Table.add_exn id_table ~key:unique_id ~data:t;
    String.Table.add_exn label_table ~key:name ~data:unique_id;
    t)
;;

let name (label : t) : string =
  if label.is_unique
  then label.name
  else "_" ^ label.name ^ "_" ^ Int.to_string label.unique_id
;;

let content t = name t ^ ":"

include Comparable.Make (T)

module Handler = struct
  let sigfpe = label (Some "sigfpe")
  let sigabrt = label (Some "sigabrt")
  let sigusr2 = label (Some "sigusr2")
end
