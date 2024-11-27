open Expr
   
type subst = (var * t) list
           
exception Not_unifyable (*à "raise" si le problème n'a pas de solution*)

(*Renvoie true si x apparaît dans term*)
let rec appear (x : var): t -> bool = function
  | Var y -> x = y
  | Op(_, l) -> List.exists (appear x) l
      
(*Effectue la substitution sigma(term) = term[new_x/x] *)
let rec replace ((x, new_x) : var * t): t -> t = function
  | Var y when x = y -> new_x
  | Var y -> Var y
  | Op(s, l) -> Op(s, List.map (replace (x, new_x)) l)

let unify_step: (subst * problem) -> (subst * problem) = function
  | _, [] -> raise Not_unifyable
  | _, ((Op(a, _), Op(b, _)) :: _) when a <> b -> raise Not_unifyable
  | s, ((Op(_, l), Op(_, l')) :: p) ->
      begin
        try (s, List.fold_left2 (fun acc u x -> (u,x)::acc) p l l')
        with Invalid_argument _ -> raise Not_unifyable
      end
  | s, ((Var x, Var x') :: p) when x = x' -> (s, p)
  | _, ((Var x, t) :: _) when appear x t -> raise Not_unifyable
  | _, ((t, Var x) :: _) when appear x t -> raise Not_unifyable
  | s, ((Var x, t) :: p) | s, ((t, Var x) :: p) ->
      let s' = (x, t) :: (List.map (fun (y, t') -> (y, replace (x, t) t')) s)
      and p' = List.map (fun (u, v) -> (replace (x, t) u, replace (x, t) v)) p
      in (s', p')

(*Implémente l'unification de deux termes*)
let unify (pb : problem) : subst =
  let rec aux (p: problem) (s: subst): subst =
    match unify_step (s, p) with
    | (s', []) -> s'
    | (s', p') -> aux p' s'
  in aux pb []

