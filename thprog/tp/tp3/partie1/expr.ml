(* Dans ce fichier, on définit les types qui vont nous servir pour écrire des termes *)

(* Types des variables *)
type var = string

(* Types des opérateurs/fonctions dans la signature des termes *)
type symbol = string

(* Type des termes : Un terme est soit une variables, soit une fonction (opérateur) appliqué à une liste d'arguments *)
type t = 
  | Var of var
  | Op of symbol * t list

type problem = 
  (t * t) list
