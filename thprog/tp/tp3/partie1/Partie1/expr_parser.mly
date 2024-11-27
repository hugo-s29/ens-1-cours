%{
  open Expr
%}

%token <string> IDENT
%token LPAR RPAR COMMA EQUAL
%token EOF

%start expr problem
%type <Expr.t> expr
%type <Expr.problem> problem
%%

problem: 
  | {
    []
  }
  |problem expr EQUAL expr {
    ($2, $4)::$1
  }


expr:
  | IDENT {
      Var ($1)
  }
  | IDENT LPAR expr_list RPAR {
      Op ($1, $3)
  }

non_empty_list: 
  | expr {
    [$1]
  }
  | expr COMMA non_empty_list{
     $1 :: $3
  }

expr_list : 
  | { [] }
  | non_empty_list {
    $1
  }

%%
