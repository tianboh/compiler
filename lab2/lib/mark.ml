(* L1 Compiler
 * Positional Markers
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Annotations / bugfixes: Alex Vaynberg <alv@andrew.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *)

open Core

type src_loc =
  { line : int
  ; col : int
  }
[@@deriving compare, sexp]

module Compare_src_loc = Comparable.Make (struct
  type t = src_loc [@@deriving compare, sexp]
end)

type src_span =
  { start_loc : src_loc
  ; end_loc : src_loc
  ; file : string
  }

let of_position (pos : Lexing.position) : src_loc =
  Lexing.{ line = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol + 1 (* 1-indexed *) }
;;

let of_positions (pos_start : Lexing.position) (pos_end : Lexing.position) =
  { start_loc = of_position pos_start
  ; end_loc = of_position pos_end
  ; file = Lexing.(pos_start.pos_fname)
  }
;;

let show : src_span -> string =
  let show_src_loc = function
    | { line; col = 0 } -> string_of_int line
    | { line; col } -> string_of_int line ^ "." ^ string_of_int col
  in
  fun span ->
    sprintf "%s:%s-%s" span.file (show_src_loc span.start_loc) (show_src_loc span.end_loc)
;;

type 'a t = 'a * src_span option

let mark (data : 'a) (span : src_span) : 'a t = data, Some span
let mark' (data : 'a) (span : src_span option) : 'a t = data, span
let naked (data : 'a) : 'a t = data, None
let data : 'a t -> 'a = fst
let src_span : 'a t -> src_span option = snd

let wrap : src_span option list -> src_span option =
 fun span_opts ->
  List.fold_right span_opts ~init:`None_seen ~f:(fun span_opt acc ->
      match span_opt, acc with
      | _, `Different_files -> acc
      | None, `None_seen -> `None_seen
      | Some s, `None_seen -> `Merging s
      | None, `Merging _ -> acc
      | Some s1, `Merging s2 ->
        if String.equal s1.file s2.file
        then
          `Merging
            { file = s1.file
            ; start_loc = Compare_src_loc.min s1.start_loc s2.start_loc
            ; end_loc = Compare_src_loc.max s1.end_loc s2.end_loc
            }
        else `Different_files)
  |> function
  | `Merging span -> Some span
  | `None_seen | `Different_files -> None
;;

let map ~(f : 'a -> 'b) : 'a t -> 'b t = Tuple2.map_fst ~f
let map' ~(f : 'a t -> 'b) : 'a t -> 'b t = fun ((_, pos) as mark) -> f mark, pos
