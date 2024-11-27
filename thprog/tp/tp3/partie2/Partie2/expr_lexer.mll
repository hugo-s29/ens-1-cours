{
  open Expr_parser
  exception Error
}

let ident = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_' ''']*
let number = ['0'-'9']+

rule lexer = parse
| [' ' '\n'] { lexer lexbuf }
| ','        { COMMA }
| '='        { EQUAL }
| '('        { LPAR }
| ')'        { RPAR }
| ident as s { IDENT s }
| eof { EOF }
| _  { raise Error }

