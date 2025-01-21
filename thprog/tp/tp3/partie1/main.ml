open Expr_conv
open Unif

(************************* *
 * Définition des exemples *
 * *************************)

let examples : string list = 
  ["x = x"; 
   "f(x,y) = f(x,x)"; 
   "succ(x) = succ(succ(zero()))";
   "succ(x) = succ(succ(y))";
   "g(x) = f(x,y)";
   "f(x,g(y,y),x) = f(z,z,g(w,f(t)))"; 
   "f(x,g(z,z),z) = f(g(y,y),y,g(w,w))";
   "succ(plus(x,succ(y))) = succ(plus(succ(t),z))";
   "x = y
    y = x";
   "z = t
    y = z
    x = y";
   "x = y
    y = z
    z = t";
]

let big n = 
  let rec rhs acc n =
    if n = 0 then acc
    else
      rhs ((Printf.sprintf "g(x%d, x%d)" n n):: acc) (n - 1)
  in 
  let rec lhs acc n = 
    if n = 0 then acc else
      lhs ((Printf.sprintf "x%d" (n - 1))::acc) (n - 1)
  in 
  Printf.sprintf "f(%s) = f(%s)" 
  (String.concat ", " (lhs [] n)) (String.concat ", " (rhs [] n))

let examples : string list = 
  examples@[big 10]

(* Les exemples qui feront probablement diverger vos solutions: *)
let examples : string list = examples@["x = f(x)"; "x = f(y) y = f(x)"]

(***************************************************** *
 * Transformation des exemples en instances à résoudre *
 * *****************************************************)

let examples : Expr.problem list = 
  List.map Expr_conv.problem_of_string examples

(************************* *
 * Procédure de résolution *
 * *************************)

(* affiche les solutions *)
let print_sub sub =
  List.iter (fun (var, r) -> 
      Printf.printf "%s -> %s\n" var  (string_of_expr r))
    sub

let solve (pb : Expr.problem ) = 
  Printf.printf "Solving : \n%s\n" (string_of_problem pb);
  try
    flush stdout;
    let sub = unify pb in
    Printf.printf "Solution : \n";
    print_sub sub;
    Printf.printf "\n"
  with Not_unifyable -> Printf.printf "Not unifyable.\n\n"

(************************** *
 * Application aux exemples *
 * **************************)

let _ = 
  List.iter solve examples
