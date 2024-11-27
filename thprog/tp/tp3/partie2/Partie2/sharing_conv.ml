(* Ne vous occupez pas de ce fichier, les fonctions suivantes servent à afficher les termes pour les test du main *)
open Sharing_expr

(* Cette fonction ne boucle pas sur les termes infinis. *)
let string_of_sharing (defined : (t * var) list) (term : t) : string = 
 let rec aux (term : t) : string = 
    try 
      List.assq term defined 
    with Not_found -> begin
      match term with 
       | Op (f, args) -> Printf.sprintf "%s(%s)" f
           (String.concat ", " (List.map aux args))
       | Var p -> begin match !p with
                  | None -> failwith "string_of_sharing"
                  | Some r -> aux r end
    end
  in begin
      match term with 
       | Op (f, args) -> Printf.sprintf "%s(%s)" f
           (String.concat ", " (List.map aux args))
       | Var p -> begin match !p with
                  | None -> List.assq term defined 
                  | Some r -> aux r end
    end

(* string_of_sharing demande d'inverser les paires de defined *)
let string_of_sharing_swapped (defined : (var * t) list) (term : t) : string = 
  string_of_sharing (List.map (fun (x,y) -> (y,x)) defined) term

let string_of_problem ((eqns, defined) : problem) : string = 
    String.concat "\n" 
      (List.map (fun (x,y) -> 
        Printf.sprintf "%s = %s" 
         (string_of_sharing_swapped defined x)
         (string_of_sharing_swapped defined y)) eqns)
