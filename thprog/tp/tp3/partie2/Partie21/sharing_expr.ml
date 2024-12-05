type symbol = string (* les symboles de constantes pour construire les termes *)

(* représentation des termes avec partage des variables *)            
type t =
  | Var of (t option) ref (* un pointeur vers un terme, initialement ne pointant vers rien *)
  | Op of symbol  * t list

type var = string  (* les variables d'unification *)
type problem = ((t * t) list) * ((var * t) list)
