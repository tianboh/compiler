open! Core

type line =
  { gen : string list
  ; kill : string list
  ; succs : int list
  ; is_label : bool
  ; line_number : int
  }

type program = line list

val program_of_json : Yojson.Basic.t -> program

type dfline = (int list * int list * int)
type dflines = dfline list

val json_of_dflines : dflines -> string
