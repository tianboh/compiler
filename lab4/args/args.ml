module Opt_level = struct
  type t = Opt_none

  let show = function Opt_none -> "O0"

  let parse = function
    | "0" -> Result.Ok Opt_none
    | "1" -> Result.Error (`Msg "Error: -O1 unimplemented (lab 2)")
    | "2" -> Result.Error (`Msg "Error: -O2 unimplemented (lab 5)")
    | arg -> Result.Error (`Msg ("Error: Unknown --opt arg: " ^ arg))

  let conv =
    let print ppf opt = Format.fprintf ppf "%s" (show opt) in
    Cmdliner.Arg.conv (parse, print)
end

module Emit = struct
  type t = X86_64 | Abstract_assem

  let show = function X86_64 -> "x86-64" | Abstract_assem -> "abs"

  let parse = function
    | "abs" -> Result.Ok Abstract_assem
    | "x86-64" -> Result.Ok X86_64
    | arg -> Result.Error (`Msg ("Unknown emit arg: " ^ arg))

  let conv =
    let print ppf emit = Format.fprintf ppf "%s" (show emit) in
    Cmdliner.Arg.conv (parse, print)
end

module Df_analysis = struct
  type t =
    | Forward_may
    | Forward_must
    | Backward_may
    | Backward_must
    | No_analysis

  let show = function
    | Forward_may -> "forward-may"
    | Forward_must -> "forward-must"
    | Backward_may -> "backward-may"
    | Backward_must -> "backward-must"
    | No_analysis -> "no-analysis"

  let parse = function
    | "forward-may" -> Result.Ok Forward_may
    | "forward-must" -> Result.Ok Forward_must
    | "backward-may" -> Result.Ok Backward_may
    | "backward-must" -> Result.Ok Backward_must
    | arg -> Result.Error (`Msg ("Error: Unknown --opt arg: " ^ arg))

  let conv =
    let print ppf opt = Format.fprintf ppf "%s" (show opt) in
    Cmdliner.Arg.conv (parse, print)
end
