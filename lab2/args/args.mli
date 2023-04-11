open Core

module Opt_level : sig
  type t = Opt_none

  val show : t -> string

  val parse : string -> (t, [> `Msg of string ]) result

  val conv : t Cmdliner.Arg.conv
end

module Emit : sig
  type t = X86_64 | Abstract_assem

  val show : t -> string

  val parse : string -> (t, [> `Msg of string ]) result

  val conv : t Cmdliner.Arg.conv
end

module Df_analysis : sig
  type t =
    | Forward_may
    | Forward_must
    | Backward_may
    | Backward_must
    | No_analysis

  val show : t -> string

  val parse : string -> (t, [> `Msg of string ]) result

  val conv : t Cmdliner.Arg.conv
end
