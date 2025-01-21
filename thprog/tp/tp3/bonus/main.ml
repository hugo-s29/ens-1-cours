[@@@ocaml.warning "-33"]
open Term (* les programmes FUN *)
open Term_conv (* affichage des programmes FUN *)
open Infer
open Unif
(* ajoutez ici des "open" pour avoir acces au code pour mettre en oeuvre l'unification *)

let examples = [
  "let x = 2 in x";
  "2 + (3 + 4)";
  "(fun x -> x) 42";
  "fun x -> 2";
  "fun x -> x";
  "fun x -> fun y -> x";
  "let apply f x = f x in apply";
  "let compose f g x = f (g x) in 
   compose";
  "let compose f g x = f (g x) in 
   let id x = x in 
   compose id id";
  "let f x = 2 in f 3";
  "(fun f -> fun g -> fun x -> f (g x)) (fun y -> y) (fun z -> z)";
  "let s x y z = x z (y z) in s";
  "let s x y z = x z (y z) in 
   let k x y = x in 
   let i = s k k in 
   i";
   "let delta x = x x in delta";
]

let print_sub sub =
  List.iter (fun (var, r) -> 
      Printf.printf "%s -> %s\n" var  (Expr_conv.string_of_expr r))
    sub

let inference x =
  let t = term_of_string x in
  begin
    Printf.printf "# inférence sur %s\n" (string_of_term t);
    let v0 = fresh () in
    let pb_string = infer [] v0 t |> string_of_unif_pbm in
    let unif_pb = Expr_conv.problem_of_string pb_string in
    try
      flush stdout;
      let sub = unify unif_pb in
      let term = List.assoc v0 sub in
      Printf.printf "=> %s\n" (Expr_conv.string_of_expr term)
    with Not_unifyable -> Printf.printf "Not unifyable.\n\n"


    (* ici il faut : 
      * (1) fabriquer à partir de t un problème d'unification à l'aide de ce qui a été codé dans infer.ml ; 
      * (2) passer ce problème d'inférence à l'algorithme d'unification (vous pouvez convertir ce problème d'inférence en une chaîne de caractères, pour vous brancher sur le code qui était fourni pour l'unification) ;
      * (3) accepter ou refuser le programme FUN représenté par x/t ; 
      * (4) si le programme est typable, calculer et afficher un type
      *)
  end

let _ =
  List.iter inference  examples
