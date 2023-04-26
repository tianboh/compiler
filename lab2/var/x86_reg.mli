open Layout

type t =
  | RAX
  | RBX
  | RCX
  | RDX
  | RSI
  | RDI
  | RBP
  | RSP
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
[@@deriving compare, sexp, hash]

val special_use : t -> bool

val reg_to_str : ?layout:layout -> t -> string

val reg_idx : t -> int

val str_to_reg : string -> t

val swap : t

val base_pointer : t

val callee_saved : t list

val caller_saved : t list

val num_reg : int

val idx_reg : int -> t