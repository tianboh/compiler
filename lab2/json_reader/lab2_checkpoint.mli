open! Core

type reg = string

type line =
  { gen : reg list
  ; kill : reg
  ; succs : reg list
  ; is_label : bool
  ; line_number : int
  }

type program = line list

val program_of_json : Yojson.Basic.t -> program

type allocation = (reg * reg) option
type allocations = allocation list

val json_of_allocations : allocations -> Yojson.Basic.t
