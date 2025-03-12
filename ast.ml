type var_type =
  | IntType
  | BoolType

type expr =
  | Int of int
  | Bool of bool
  | Var of string
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Le of expr * expr
  | Ge of expr * expr
  | Lt of expr * expr
  | Gt of expr * expr
  | Eq of expr * expr
  | Neq of expr * expr
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Forall of string * var_type * expr
  | Exists of string * var_type * expr

  (* NEW: Implication node. *)
  | Imp of expr * expr

  (* NEW: Uninterpreted function calls, e.g. f(e1, ..., en) *)
  | FunCall of string * expr list
