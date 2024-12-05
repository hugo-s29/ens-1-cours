%{
  open Term
%}

%token LPAR RPAR LET IN EQUAL LEQ
%token <string> IDENT
%token <int> INT
%token <bool> BOOL
%token PLUS TIMES MINUS UNIT
%token IF THEN ELSE FUN ARROW
%token REF BANG COLEQ SEQ 
%token EOF

%left ELSE IN ARROW
%left SEQ
%left PLUS TIMES MINUS COLEQ
%nonassoc LPAR IDENT INT BOOL UNIT REF
%nonassoc BANG

%start term
%type <Term.t> term
%%

constant : 
  | INT {
     $1
  }

simple_term:
  | IDENT {
    TVar $1
  }
  | constant {
    TCst $1 
  }
  | LPAR term RPAR {
    $2
  }

term: 
  | simple_term {
    $1
  }
  | term simple_term {
    TApp ($1, $2)
  }
  | simple_term PLUS simple_term {
    TAdd ($1, $3)
  }
  | LET IDENT list_ident EQUAL term IN term {
    TLet ($2, 
      List.fold_left (fun acc y -> TFun (y, acc)) $5 $3, $7)
  }
  | FUN IDENT ARROW term {
    TFun ($2, $4)
  }

list_ident : 
  |  { [] }
  | list_ident IDENT {$2::$1}

%%
