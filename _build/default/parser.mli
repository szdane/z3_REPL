
(* The type of tokens. *)

type token = 
  | VAR of (string)
  | TRUE
  | TIMES
  | RPAREN
  | PLUS
  | OR
  | NOT
  | NEQ
  | MINUS
  | LT
  | LPAREN
  | LE
  | INT_TYPE
  | INT of (int)
  | GT
  | GE
  | FORALL
  | FALSE
  | EXISTS
  | EQ
  | EOF
  | DIVIDE
  | COMMA
  | COLON
  | BOOL_TYPE
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
