module Symbol = Util.Symbol
open Core

let types = ref Symbol.Set.empty
let add_type (var : Symbol.t) : unit = types := Symbol.Set.add !types var
let has_type (var : Symbol.t) : bool = Symbol.Set.mem !types var
let is_header = ref true
