open Term

let rec string_of_term = function 
  | TAdd (e1, e2) -> 
      Printf.sprintf "%s + %s"
         (string_of_complex_term e1) (string_of_complex_term e2)
  | TLet (x, e1, e2) -> 
      Printf.sprintf "let %s = %s in %s" x
         (string_of_term e1) (string_of_term e2)
  | TFun (x, e) -> 
      Printf.sprintf "fun %s -> %s" x (string_of_term e)
  | TApp (e1, e2) -> 
      Printf.sprintf "%s %s"
         (string_of_app e1) (string_of_complex_term e2)
  | TVar _ | TCst _ as e -> string_of_complex_term e

and string_of_complex_term = function 
  | TVar x -> x
  | TCst x -> string_of_int x
  | e -> Printf.sprintf "(%s)" (string_of_term e)

and string_of_app = function 
  | TApp (TApp (_,_) as t1, t2) -> 
      Printf.sprintf "%s %s" (string_of_app t1) (string_of_complex_term t2)
  | TApp (t1, t2) -> Printf.sprintf "%s %s" (string_of_complex_term t1) (string_of_complex_term t2)
  | TFun (_,_) as t1 -> Printf.sprintf "(%s)" (string_of_term t1)
  | t1 -> string_of_term t1

let term_of_string s = 
  let lex = Lexing.from_string s in 
  try
    Term_parser.term Term_lexer.lexer lex
  with e ->
   flush stdout; 
   Printf.eprintf "Error : %s near '%s'.\n" (Printexc.to_string e) (Lexing.lexeme lex);
   flush stderr;
   failwith "term_of_string"


