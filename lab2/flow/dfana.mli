open Json_reader.Lab2_checkpoint
open Args
open Core

(* module IntSet : Core_kernel__.Set.S with type Elt.t = int = struct
   include Core_kernel__.Set.Make(Int)
   end *)

module IntSet : Set.S

type block =
  { pred : IntSet.t
  ; succ : IntSet.t
  ; gen : IntSet.t
  ; kill : IntSet.t
  ; in_ : IntSet.t
  ; out_ : IntSet.t
  ; no : int
  }

val print_b2l : (int, int * int) Base.Hashtbl.t -> unit
val print_l2b : (int, int) Base.Hashtbl.t -> unit
val print_blocks : (int, block) Base.Hashtbl.t -> unit
val print_IntSet : IntSet.t -> string
val print_IntList : int list -> string
val dfana : program -> Df_analysis.t -> dflines
