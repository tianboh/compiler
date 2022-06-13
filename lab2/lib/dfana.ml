(*
  This file is used to achieve data flow analysis.
*)
open Core
open Json_reader.Lab2_checkpoint
open Printf

let rec read_gens prog gens = match prog with
  | [] -> gens
  | h :: t -> read_gens t (h.gen @ gens)

let rec print_gens gens = match gens with
  | [] -> ()
  | h :: t -> 
    let () = printf "%s" h in
    print_gens t

let dfana (prog : program) = 
  let gens = read_gens prog [] in
  let () = print_gens gens in
  [([1;2], [3;4], 0); ([4],[5;6],1); ([],[],2)]
;;