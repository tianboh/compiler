open Core

type line =
  { gen : int list
  ; kill : int list
  ; succ : int list
  ; is_label : bool
  ; line_number : int
  }

type program = line list

let line_of_json json =
  let open Yojson.Basic.Util in
  let gen = json |> member "Gen" |> to_list |> List.map ~f:to_string |> List.map ~f:(fun x -> int_of_string x) in
  let kill = json |> member "Kill" |> to_list |> List.map ~f:to_string |> List.map ~f:(fun x -> int_of_string x) in
  let succ = json |> member "Successors" |> to_list |> List.map ~f:to_int in
  let is_label = json |> member "Is_label" |> to_bool in
  let line_number = json |> member "Line" |> to_int in
  { gen; kill; succ; is_label; line_number };
;;

let program_of_json (json : Yojson.Basic.t) =
  json |> Yojson.Basic.Util.to_list |> List.map ~f:line_of_json
;;

type dfline = (int list * int list * int)
type dflines = dfline list

let format_output_line in_ out_ lineno = 
  let in_str_list = List.map ~f:(fun x -> sprintf "\"%s\"" (string_of_int x)) in_ in 
  let out_str_list = List.map ~f:(fun x -> sprintf "\"%s\"" (string_of_int x)) out_ in 
  let in_str = String.concat ~sep:"," in_str_list in
  let out_str = String.concat ~sep:"," out_str_list in
  sprintf "
{
 \"In\": [%s],
 \"Out\": [%s],
 \"Line\": %d 
}" in_str out_str lineno
;;

let json_of_dflines dflines =
  let res_list = 
    List.map dflines ~f:(fun dfline -> 
        let (in_, out_, line_) = dfline in
        format_output_line in_ out_ line_
      ) in
  let res_str = String.concat ~sep:"," res_list in
  sprintf "[%s\n]" res_str
;;