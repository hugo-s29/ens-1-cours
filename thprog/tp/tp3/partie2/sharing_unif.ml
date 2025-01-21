[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-39"]
open Sharing_expr

(* renvoie un terme où les variables sont remplacées par des pointeurs *)
(* afin d'obtenir une expression avec partage *)
(* Expr.t est le type des termes sans partage, t est le type des termes avec partage *)
(* on vous conseille de vous référer aux exemples en haut de la page 4 de l'énoncé *)
(* defined est l'ensemble des variables déjà définies *)
let rec sharing_of_expr (defined : (var * t) list) (e : Expr.t) : t * ((var * t) list)=
  match e with
  | Var x ->
      begin
        match List.assoc_opt x defined with
        | Some t -> (t, defined)
        | _ -> let vx = Var (ref None) in (vx, (x,vx)::defined)
      end
  | Op(s, l) ->
      let (def', l') = List.fold_right (fun t (def,acc) ->
        let (t', def') = sharing_of_expr def t in
        (def', t'::acc)
      ) l (defined, []) in
      (Op(s,l'), def')


(* algorithme d'unification travaillant sur les termes avec partage *)
(* comme écrit dans l'énoncé,
   "Lorsque l’on exécute l’algorithme d’unification, plutôt que
   d’étendre la substitution avec un couple (x, t), on fait pointer le
   ref de la variable x vers Some t."
 *)

let rec string_of_term: t -> string = function
  | Var r -> let addr = 2 * (Obj.magic r) in "Var " ^ (string_of_int addr)
  | Op(s, l) ->
      "Op(" ^ s ^ (List.fold_left (fun acc x -> acc ^ ", " ^ (string_of_term x)) "" l) ^ ")"

(* fonction auxiliaire renvoyant le représentant de la classe d'équivalence *)
(* d'un terme, suivant le principe d'union find *)
(* intuitivement, cette fonction suit les pointeurs ; ne peut pas rendre du (Var (Some _)) *)
(* question : que peut-on faire au passage pour améliorer les performances
   en exploitant la structure de données ? *)
let rec repr (term : t) : t =
  match term with
  | Var r ->
      begin
        match !r with
        | None -> term
        | Some term' -> repr term'
      end
  | _ -> term

exception Not_unifyable

(* Implémente la nouvelle version de l'algorithme d'unification:
  * unifie les termes t1 et t2 en mettant à jour les variables
  * si nécessaire *)
let rec unify (t1 : t) (t2 : t) : unit =
  match t1, t2 with
  | _ when t1 == t2 -> ()
  | _ when t1 != repr t1 -> unify (repr t1) t2
  | _ when t2 != repr t2 -> unify t1 (repr t2)
  | Op(f, _), Op(f', _) when f <> f' -> raise Not_unifyable
  | Op(_, l), Op(_, l') ->
      begin
        try List.iter2 (fun a b ->
          (match a, b with
          | Var x, Var y when x == y -> ()
          | Var x, b -> x := Some (repr b)
          | a, Var y -> y := Some (repr a)
          | _ -> ()
          );
          unify a b
        ) l l'
        with Invalid_argument _ -> raise Not_unifyable
      end
  | Var x, t2 -> x := Some t2
  | t1, Var x -> x := Some t1

(* Implémente le test de cyclicité *)
(* après avoir unifié, on peut récupérer une structure avec un cycle qui passe à travers
 * au moins un Op (par construction, pas possible d'avoir un cycle entre variables) *)
let cyclic (t : t) : bool =
  let exception Cyclic in
  let rec aux (l: t list) (t: t) =
    match t with
    | _ when List.memq t l -> raise Cyclic
    | Var x ->
        begin
          match !x with
          | None -> ()
          | Some t' -> aux (t::l) t'
        end
    | Op(_, l') -> List.iter (aux (t::l)) l'
    
  in
  try aux [] t; false
  with Cyclic -> true

(* Magie magie
let cyclic (t : t) : bool =
  let rec aux = function
    | Op(_, l) -> List.iter aux l
    | Var x ->
      begin
        match !x with
        | None -> ()
        | Some t -> aux t
      end
  in
  try aux t; false
  with Stack_overflow -> true
*)
