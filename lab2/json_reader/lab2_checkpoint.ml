open Core

type reg = string

type line =
  { gen : reg list
  ; kill : reg
  ; succs : reg list
  ; is_label : bool
  ; line_number : int
  }

type program = line list

let line_of_json json =
  let open Yojson.Basic.Util in
  let gen = json |> member "Gen" |> to_list |> List.map ~f:to_string in
  let kill = json |> member "Kill" |> to_list |> List.map ~f:to_string |> String.concat in
  let succs = json |> member "Successors" |> to_list |> List.map ~f:to_string in
  let is_label = json |> member "Is_label" |> to_bool in
  let line_number = json |> member "Line" |> to_int in
  { gen; kill; succs; is_label; line_number };
;;

let program_of_json (json : Yojson.Basic.t) =
  json |> Yojson.Basic.Util.to_list |> List.map ~f:line_of_json
;;

type allocation = (reg * reg) option
type allocations = allocation list

let json_of_allocations allocations =
  `List
    (List.map allocations ~f:(fun allocation ->
         Option.value_map allocation ~default:(`Assoc []) ~f:(fun (r1, r2) ->
             `Assoc [ r1, `String r2 ])))
;;