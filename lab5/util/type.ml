(* Type for L4
 * Used by CST and AST
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

(* data type, whole data type L4 support *)
type dtype =
  [ `Int
  | `Bool
  | `Void
  | `NULL
  | `Pointer of dtype
  | `Array of dtype
  | `Struct of Symbol.t
  ]

(* small type, which is stored on stack *)
type stype =
  [ `Int
  | `Bool
  | `Void
  | `NULL
  | `Pointer of dtype
  | `Array of dtype
  ]
