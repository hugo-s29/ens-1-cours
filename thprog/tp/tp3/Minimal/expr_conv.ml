open Expr

let expr_of_string s = 
  let lex = Lexing.from_string s in 
  try
    Expr_parser.expr Expr_lexer.lexer lex
  with e ->
   flush stdout; 
   Printf.eprintf "Error : %s near '%s'.\n" (Printexc.to_string e) (Lexing.lexeme lex);
   flush stderr;
   failwith "term_of_string"

let problem_of_string s = 
  let lex = Lexing.from_string s in 
  try
    Expr_parser.problem Expr_lexer.lexer lex
  with e ->
   flush stdout; 
   Printf.eprintf "Error : %s near '%s'.\n" (Printexc.to_string e) (Lexing.lexeme lex);
   flush stderr;
   failwith "term_of_string"


let rec string_of_expr = function
  | Var s -> s
  | Op (f, args) -> 
      Printf.sprintf "%s(%s)" f (String.concat ", " 
        (List.map string_of_expr args))

let string_of_problem l =
  String.concat "\n" 
    (List.map (fun (x,y) -> 
      Printf.sprintf "%s = %s" (string_of_expr x)
                               (string_of_expr y)) l)
 
