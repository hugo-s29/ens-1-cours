[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-39"]
open Sharing_expr
open Sharing_conv

(* defined est l'ensemble des variables déjà définies *)
(* renvoit une expression où les variables sont remplacées par des pointeurs *)
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


(* suit les pointeurs ; ne peut pas rendre du (Var (Some _)) *)
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
          (match a, b with Var x, Var y -> x := Some b | _ -> ());
          unify a b
        ) l l'
        with Invalid_argument _ -> raise Not_unifyable
      end
  | Var x, Var y -> x := Some t2
  | Var x, t2 -> x := Some t2
  | t1, Var x -> x := Some t1


(* Implémente le test de cyclicité *)
(* après avoir unifié, on peut récupérer une structure avec un cycle qui passe à travers
 * au moins un Op (par construction, pas possible d'avoir un cycle entre variables) *)
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



(*
  let exception Cycle in
  let rec aux (prev: t option ref list) (t: t) =
    match t with
    | Op(_, l) -> List.iter (aux prev) l
    | Var x when List.mem x prev -> raise Cycle
    | Var x -> 
        begin
          List.iter (fun x -> Printf.printf "%d " (2 * (Obj.magic x))) (x::prev);
          print_newline ();
          match !x with
          | None -> ()
          | Some t' -> aux (x::prev) t'
        end
  in
  try aux [] t; false
  with Cycle -> true
*)
