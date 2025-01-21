{
  open Term_parser
}

rule lexer = parse
| [' ' '\t' '\n'] 
  { lexer lexbuf }
| "(*"      
  { comments 0 lexbuf }
| "()" 
  { UNIT }
| "("	    
  { LPAR }
| ")"	    
  { RPAR }
| "let"     
  { LET  }
| "="       
  { EQUAL }
| "in"       
  { IN }
| "->"	    
  { ARROW }
| "<"	    
  { LEQ }
| "*" 
  { TIMES }
| "+" 
  { PLUS }
| "-" 
  { MINUS }
| "!" 
  { BANG }
| ";" 
  { SEQ }
| ":=" 
  { COLEQ }
| "ref" 
  { REF }
| "fun"	    
  { FUN }
| "true" 
  { BOOL true }
| "if" 
  { IF }
| "then" 
  { THEN }
| "else" 
  { ELSE }
| "false" 
  { BOOL false }
| ['_''a'-'z' 'A'-'Z'] ['_''a'-'z' 'A'-'Z' '0'-'9']*
  { IDENT (Lexing.lexeme lexbuf) }
| '-'?['0'-'9']+ 
  { INT (int_of_string (Lexing.lexeme lexbuf)) }
| eof			  
  { EOF }

and comments level = parse
| "*)" 
  { if level = 0 then lexer lexbuf
    else comments (level - 1) lexbuf }
| "(*"
  { comments (level + 1) lexbuf }
| eof            
  { EOF }
| _              
  { comments level lexbuf }
