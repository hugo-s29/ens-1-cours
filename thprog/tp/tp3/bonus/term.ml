type var = string

type t =
    | TVar of var                  
    | TCst of int
    | TApp of t * t        
    | TFun of var * t          
    | TAdd of t * t 
    | TLet of var * t * t     
    
