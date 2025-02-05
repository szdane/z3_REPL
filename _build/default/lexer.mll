{
  open Parser
}

rule token = parse
  | [' ' '\t' '\n'] { token lexbuf }   (* Ignore whitespace *)
  | ['0'-'9']+ as n { INT (int_of_string n) }  (* Match integers *)
  | ['a'-'z' 'A'-'Z' '_' '0'-'9']+ as v { 
      match v with
      | "forall" -> FORALL
      | "exists" -> EXISTS
      | "and" -> AND
      | "or" -> OR
      | "not" -> NOT  
      | "true" -> TRUE  
      | "false" -> FALSE  
      | "Int" -> INT_TYPE  
      | "Bool" -> BOOL_TYPE  
      | _ -> VAR v
    }
  | ':' { COLON }
  | ',' {COMMA}
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { TIMES }
  | '/' { DIVIDE }
  | "<=" { LE }
  | ">=" { GE }
  | '<' { LT }
  | '>' { GT }
  | '=' { EQ }
  | "!=" { NEQ }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | eof { EOF }
