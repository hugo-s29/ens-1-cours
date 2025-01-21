open Term
open Term_type
open Type
open Unif

(* Il faudrait deja de quoi créer les variables "X1", "X2", etc *)
let fresh = 
  let n = ref 0 in
  fun () -> (incr n; "X" ^ (string_of_int !n))


type unif_pbm = (ty*ty) list

let string_of_unif_pbm = 
  List.fold_left
   (fun s (a,b) -> 
     Printf.sprintf "%s = %s\n%s" (string_of_ty a) (string_of_ty b) s) ""

(* infer env v t prend un terme t à typer dans l'environnement env ((str*ty) List), et
   crée le problème d'unification associé en prenant $v$ comme variable associée à t *)
let rec infer env v = function
  | TVar x -> [Tuvar v, List.assoc x env]
  | TCst _ -> [Tuvar v, Tint]
  | TAdd (t1, t2) -> let v1 = fresh () and v2 = fresh () in
      [Tuvar v,Tint; Tuvar v1,Tint; Tuvar v2,Tint] @ (infer env v1 t1) @ (infer env v2 t2)
  | TFun (x, t) -> let v1 = fresh () and v2 = fresh () in
      [Tuvar v,Tarr(Tuvar v1, Tuvar v2)] @ (infer ((x,Tuvar v1)::env) v2 t)
  | TApp (t1,t2) -> let v1 = fresh () and v2 = fresh () in 
      [Tuvar v1,Tarr(Tuvar v2, Tuvar v)] @ (infer env v1 t1) @ (infer env v2 t2)
  | TLet (x, t1, t2) -> let v' = fresh () in
      (infer env v' t1) @ (infer ((x,Tuvar v')::env) v t2)
