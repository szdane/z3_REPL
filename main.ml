open Z3
open Z3.Arithmetic
open Z3.Boolean
open Parser_lib.Ast
open Parser_lib.Lexer
open Parser_lib.Parser

(* Create a single Z3 context. *)
let ctx = Z3.mk_context []

(* Keep track of variable types. *)
let var_types = Hashtbl.create 100

(* OPTIONAL: If you want to handle uninterpreted function declarations properly,
   you can keep a table from function-name -> (domain sorts, range sort).
   For the sake of a minimal example, we do not parse explicit function 
   declarations. Instead, we create new function declarations on the fly 
   assuming all arguments are Int and the range is Int. 
*)
let fun_decls = Hashtbl.create 100

(* Helper to convert our var_type to a Z3 sort. *)
let to_z3_sort ctx = function
  | IntType  -> Integer.mk_sort ctx
  | BoolType -> Boolean.mk_sort ctx

(* On-the-fly creation of an uninterpreted function if we haven't seen it yet.
   This example assumes:  domain = all Int, range = Int. 
   A real system would parse domain/range from user declarations. *)
let get_uninterpreted_fun ctx (fname : string) (arity : int) : FuncDecl.func_decl =
  if Hashtbl.mem fun_decls (fname, arity) then
    Hashtbl.find fun_decls (fname, arity)
  else
    let domain_sorts = List.init arity (fun _ -> Integer.mk_sort ctx) in
    let range_sort   = Integer.mk_sort ctx in
    let fd = FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx fname) domain_sorts range_sort in
    Hashtbl.add fun_decls (fname, arity) fd;
    fd

(* The core translator from our AST to a Z3 expression. *)
let rec to_z3_expr ctx = function
  | Int i -> Integer.mk_numeral_i ctx i
  | Bool true -> Boolean.mk_true ctx
  | Bool false -> Boolean.mk_false ctx
  | Var v ->
      if Hashtbl.mem var_types v then
        let v_type = Hashtbl.find var_types v in
        Expr.mk_const ctx (Symbol.mk_string ctx v) (to_z3_sort ctx v_type)
      else
        failwith ("Variable " ^ v ^ " used without declaration")

  | Add (e1, e2) -> mk_add ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Sub (e1, e2) -> mk_sub ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Mul (e1, e2) -> mk_mul ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Div (e1, e2) -> mk_div ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Le (e1, e2)  -> mk_le ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Ge (e1, e2)  -> mk_ge ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Lt (e1, e2)  -> mk_lt ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Gt (e1, e2)  -> mk_gt ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Eq (e1, e2)  -> mk_eq ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)
  | Neq (e1, e2) -> mk_not ctx (mk_eq ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2))
  | And (e1, e2) -> mk_and ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Or (e1, e2)  -> mk_or ctx [to_z3_expr ctx e1; to_z3_expr ctx e2]
  | Not e        -> mk_not ctx (to_z3_expr ctx e)

  | Forall (v, typ, e) ->
      Hashtbl.add var_types v typ;
      let var_sort = to_z3_sort ctx typ in
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v) var_sort in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [var] (to_z3_expr ctx e) None [] [] None None)

  | Exists (v, typ, e) ->
      Hashtbl.add var_types v typ;
      let var_sort = to_z3_sort ctx typ in
      let var = Expr.mk_const ctx (Symbol.mk_string ctx v) var_sort in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_exists_const ctx [var] (to_z3_expr ctx e) None [] [] None None)

  (* NEW: Implication => *)
  | Imp (e1, e2) ->
      mk_implies ctx (to_z3_expr ctx e1) (to_z3_expr ctx e2)

  (* NEW: Uninterpreted function call f(e1, ..., en) *)
  | FunCall (fname, args) ->
      let fd = get_uninterpreted_fun ctx fname (List.length args) in
      let z3_args = List.map (to_z3_expr ctx) args in
      FuncDecl.apply fd z3_args

(* Process an input line, parse it, and then feed to Z3 solver. *)
let process line =
  try
    let lexbuf = Lexing.from_string line in
    let expr = main token lexbuf in

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

  with
  | Failure msg ->
      Printf.eprintf "Fatal error: %s\n" msg;
      flush stderr
  | _ ->
      Printf.printf "Fatal error: exception Failure(\"lexing: empty token\")\n";
      flush stdout

(* Read lines continuously from stdin and process each. *)
let rec repeat () =
  try
    Printf.printf "> ";
    flush stdout;
    let line = read_line () in
    process line;
    repeat ()
  with End_of_file -> ()

let () = repeat ()
