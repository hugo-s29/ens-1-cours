open Sharing_conv

(************************* *
 * Définition des exemples *
 * *************************)

let examples : string list = 
  ["x = f(y)
    y = f(x)
    z = f(t)
    t = f(z)
    x = z";
  ]

let examples : string list =
  examples@
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
let examples : string list = examples@[
    "x = f(x)";
    "x = f(y)
    y=f(x)";
    "x=z
    x =f(y)
    y =f(x)
    z= f(t)
    t= f(z)";
    "x =f(y)
    y =f(x)
    z= f(t)
    t= f(z)
     x=z";
   "x=f(f(x))
    t=f(f(t))
    t=f(x)";]

(******************************************* *
 * Transformation des examples en type problem *
 * *******************************************)

let examples : Expr.problem list = 
  List.map Expr_conv.problem_of_string examples

let problem_of_expr_problem (p : Expr.problem) : Sharing_expr.problem =
  List.fold_left
  (fun (problem_sharing, defined) (x,y) ->
  let x, defined = Sharing_unif.sharing_of_expr defined x in
  let y, defined = Sharing_unif.sharing_of_expr defined y in
  ((x,y)::problem_sharing,defined))
  ([],[]) p

let examples : Sharing_expr.problem list =
  List.map problem_of_expr_problem examples

(************************* *
 * Procédure de résolution *
 * *************************)

let solve ((eqns, defined) as problem : Sharing_expr.problem) = 
  Printf.printf "Solving : \n%s\n" (string_of_problem problem);
  try
    flush stdout;
    List.iter (fun (x,y) -> Sharing_unif.unify x y) eqns;
    Printf.printf "Solution : \n";
    List.iter (fun (var, r) -> 
      Printf.printf "%s -> %s %s\n" var 
      (string_of_sharing_swapped defined r) 
      (Printf.printf "testing for cycles\n";if Sharing_unif.cyclic r then "(cyclic !)" else "")) defined;
    Printf.printf "\n"
  with Sharing_unif.Not_unifyable -> Printf.printf "Not unifyable.\n\n"

(************************** *
 * Application aux exemples *
 * **************************)

let _ = 
  List.iter solve examples
