open Z3
open Z3.Arithmetic
open Z3.Boolean
open Parser_lib.Ast
open Parser_lib.Lexer
open Parser_lib.Parser

let ctx = Z3.mk_context []

(* Convert the AST to a Z3 expression *)
(* let rec to_z3_expr ctx = function
  | Int i -> Integer.mk_numeral_i ctx i
  | Bool true -> Boolean.mk_true ctx
  | Bool false -> Boolean.mk_false ctx
  | Var v -> Expr.mk_const ctx (Symbol.mk_string ctx v) (Integer.mk_sort ctx)
    (* Assume a variable is boolean if it appears inside a boolean operation *)
    (* if String.contains v 'b' then
      Expr.mk_const ctx (Symbol.mk_string ctx v) (Boolean.mk_sort ctx)
    else
      Expr.mk_const ctx (Symbol.mk_string ctx v) (Integer.mk_sort ctx) *)
  | Add (e1, e2) -> mk_add ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Sub (e1, e2) -> mk_sub ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Mul (e1, e2) -> mk_mul ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Div (e1, e2) -> mk_div ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Le (e1, e2) -> mk_le ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Ge (e1, e2) -> mk_ge ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Lt (e1, e2) -> mk_lt ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Gt (e1, e2) -> mk_gt ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Eq (e1, e2) -> mk_eq ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Neq (e1, e2) -> mk_not ctx (mk_eq ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2))
  | And (e1, e2) -> mk_and ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Or (e1, e2) -> mk_or ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Not e -> mk_not ctx (to_z3_expr ctx e)
  | Forall (v, IntType, e) ->
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v) (Integer.mk_sort ctx) in
      Quantifier.expr_of_quantifier (Quantifier.mk_forall_const ctx [var] (to_z3_expr ctx e) None [] [] None None)
  | Forall (v, BoolType, e) ->
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v) (Boolean.mk_sort ctx) in
      Quantifier.expr_of_quantifier (Quantifier.mk_forall_const ctx [var] (to_z3_expr ctx e) None [] [] None None)
  | Exists (v, IntType, e) ->  
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v) (Integer.mk_sort ctx) in
      Quantifier.expr_of_quantifier (Quantifier.mk_exists_const ctx [var] (to_z3_expr ctx e) None [] [] None None)
  | Exists (v, BoolType, e) ->  
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v) (Boolean.mk_sort ctx) in
      Quantifier.expr_of_quantifier (Quantifier.mk_exists_const ctx [var] (to_z3_expr ctx e) None [] [] None None) *)

      let var_types = Hashtbl.create 100  (* ✅ Global table to track variable types *)

let rec to_z3_expr ctx = function
  | Int i -> Integer.mk_numeral_i ctx i
  | Bool true -> Boolean.mk_true ctx
  | Bool false -> Boolean.mk_false ctx
  | Var v -> 
      if Hashtbl.mem var_types v then
        let v_type = Hashtbl.find var_types v in
        if v_type = IntType then
          Expr.mk_const ctx (Symbol.mk_string ctx v) (Integer.mk_sort ctx)
        else
          Expr.mk_const ctx (Symbol.mk_string ctx v) (Boolean.mk_sort ctx)
      else
        failwith ("Variable " ^ v ^ " used without declaration")
  | Add (e1, e2) -> mk_add ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Sub (e1, e2) -> mk_sub ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Mul (e1, e2) -> mk_mul ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Div (e1, e2) -> mk_div ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Le (e1, e2) -> mk_le ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Ge (e1, e2) -> mk_ge ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Lt (e1, e2) -> mk_lt ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Gt (e1, e2) -> mk_gt ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Eq (e1, e2) -> mk_eq ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Neq (e1, e2) -> mk_not ctx (mk_eq ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2))
  | And (e1, e2) -> mk_and ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Or (e1, e2) -> mk_or ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Not e -> mk_not ctx (to_z3_expr ctx e)
  | Forall (v, typ, e) ->
      Hashtbl.add var_types v typ;  (* ✅ Store variable type *)
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v)
        (if typ = IntType then Integer.mk_sort ctx else Boolean.mk_sort ctx) in
      Quantifier.expr_of_quantifier (Quantifier.mk_forall_const ctx [var] (to_z3_expr ctx e) None [] [] None None)
  | Exists (v, typ, e) ->
      Hashtbl.add var_types v typ;  (* ✅ Store variable type *)
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v)
        (if typ = IntType then Integer.mk_sort ctx else Boolean.mk_sort ctx) in
      Quantifier.expr_of_quantifier (Quantifier.mk_exists_const ctx [var] (to_z3_expr ctx e) None [] [] None None)


(* Process an input line and return "SAT" or "UNSAT" *)
let process line =
  try
    let lexbuf = Lexing.from_string line in
    let expr = main token lexbuf in  (* Parse the expression *)

    (* Convert the parsed expression to a Z3 expression *)
    let z3_expr = to_z3_expr ctx expr in
    Printf.printf "Z3 Expression: %s\n" (Expr.to_string z3_expr);
    flush stdout;

    (* Create and use a solver *)
    let solver = Solver.mk_solver ctx None in
    Solver.add solver [z3_expr];

    (* Check satisfiability and print result *)
    match Solver.check solver [] with
    | Solver.SATISFIABLE -> Printf.printf "Result: SAT\n"; flush stdout
    | Solver.UNSATISFIABLE -> Printf.printf "Result: UNSAT\n"; flush stdout
    | Solver.UNKNOWN -> Printf.printf "Result: UNKNOWN\n"; flush stdout
  with _ ->
    Printf.printf "Fatal error: exception Failure(\"lexing: empty token\")\n";
    flush stdout  (* Ensure error message is printed immediately *)

(* Read lines continuously from stdin and process each *)
let rec repeat () =
  try
    Printf.printf "> ";  (* Display prompt for clarity *)
    flush stdout;
    let line = read_line () in
    process line;
    repeat ()  (* Continue reading next line *)
  with End_of_file -> ()  (* Stop on EOF *)

(* Start reading from stdin *)
let () = repeat ()
