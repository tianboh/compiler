module Symbol = Util.Symbol
open Core

let env = ref Symbol.Set.empty
let add (var : Symbol.t) : unit = env := Symbol.Set.add !env var
let mem (var : Symbol.t) : bool = Symbol.Set.mem !env var
let is_header = ref true
