(* Memory
 * Memory used for x86 convention.
 * Base pointer + offset is the memory adress to inquire. 
 * WARNNING: offset is not index! It should be multiple of 0x8, 0x10, or 0x20.
 * Dataload size is the size to fetch on the memory address.
 * Author: tianboh
 *)

 open Core

 module T = struct
   type t = 
   {  index : int (* This is a global unique id for memory.*)
    ; base : X86_reg.t
    ; offset : int (* base + offset is start address of a variable *)
    ; size : int (* size of corresponding variable, byte as unit.*)
   }[@@deriving sexp, compare, hash]
 end
 include T
 
 let create index base offset size =
   {
    index; base; offset; size
   }
 ;;
 
 let mem_to_str t = Printf.sprintf "%d(%s)" (-t.offset * t.size) (X86_reg.reg_to_str t.base)
 
 let from_reg reg = 
  if X86_reg.need_spill reg
    then 
      let reg_idx = X86_reg.spilled_idx reg in
      create reg_idx (X86_reg.get_base_pointer ()) reg_idx 8
    else failwith "general purpose register should not map to memory index"
;;

 include Comparable.Make (T)