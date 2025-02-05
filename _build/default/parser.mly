%{
  open Ast
%}

%token <int> INT
%token <string> VAR
%token TRUE FALSE  
%token INT_TYPE BOOL_TYPE  
%token COLON  COMMA
%token PLUS MINUS TIMES DIVIDE
%token LE GE LT GT EQ NEQ
%token AND OR NOT
%token FORALL EXISTS
%token LPAREN RPAREN EOF

%left OR
%left AND
%left EQ NEQ
%left LE GE LT GT
%left PLUS MINUS
%left TIMES DIVIDE
%right NOT  

%start <Ast.expr> main

%%

main:
| e = expr EOF { e }

expr:
| i = INT { Int i }
| TRUE { Bool true }  
| FALSE { Bool false }  
| v = VAR { Var v }
| NOT e = expr { Not e }  
| e1 = expr PLUS e2 = expr { Add (e1, e2) }
| e1 = expr MINUS e2 = expr { Sub (e1, e2) }
| e1 = expr TIMES e2 = expr { Mul (e1, e2) }
| e1 = expr DIVIDE e2 = expr { Div (e1, e2) }
| e1 = expr LE e2 = expr { Le (e1, e2) }
| e1 = expr GE e2 = expr { Ge (e1, e2) }
| e1 = expr LT e2 = expr { Lt (e1, e2) }
| e1 = expr GT e2 = expr { Gt (e1, e2) }
| e1 = expr EQ e2 = expr { Eq (e1, e2) }
| e1 = expr NEQ e2 = expr { Neq (e1, e2) }
| e1 = expr AND e2 = expr { And (e1, e2) }
| e1 = expr OR e2 = expr { Or (e1, e2) }
| quantifier_expr { $1 }

vars:
| v = VAR COLON t = var_type { [(v, t)] }
| v = VAR COLON t = var_type COMMA vs = vars { (v, t) :: vs }

quantifier_expr:
| FORALL vs = vars LPAREN e = expr RPAREN { List.fold_right (fun (v, t) acc -> Forall (v, t, acc)) vs e }
| EXISTS vs = vars LPAREN e = expr RPAREN { List.fold_right (fun (v, t) acc -> Exists (v, t, acc)) vs e }

var_type:
| INT_TYPE { IntType }
| BOOL_TYPE { BoolType }
