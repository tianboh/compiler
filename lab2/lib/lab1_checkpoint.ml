open Core

type reg = string

type line =
  { uses : reg list
  ; define : reg
  ; live_out : reg list
  ; move : bool
  ; line_number : int
  }

type program = line list

let line_of_json json =
  let open Yojson.Basic.Util in
  let uses = json |> member "Uses" |> to_list |> List.map ~f:to_string in
  let define = json |> member "Defines" |> to_list |> List.map ~f:to_string |> String.concat in
  let live_out = json |> member "Live_out" |> to_list |> List.map ~f:to_string in
  let move = json |> member "Move" |> to_bool in
  let line_number = json |> member "Line" |> to_int in
  { uses; define; live_out; move; line_number };
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
