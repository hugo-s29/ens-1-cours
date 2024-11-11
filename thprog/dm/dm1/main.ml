
(* Le type `key` peut être remplacé par autre chose si besoin *)
type key = int

(*
  On représente le nœud avec pour clés k1, ..., kn et pour enfants a0, ... an
  par Node(a0, [(k1,a1), (k2, a2), ..., (kn, an)]).
*)
type btree =
  | Leaf of key list
  | Node of btree * ((key * btree) list)


(********************************************************)
(* QUELQUES EXEMPLES DE B-ARBRES...                     *)
(********************************************************)

(* [1; 2; 3] *)
let btree1 = Leaf [1; 2; 3]

(*
        4
       / \
    [1; 2] [5; 6]
*)
let btree2 =
  Node(Leaf [1; 2], [(4, Leaf [5; 6])])

(*
          5       10
        /   \    /   \
    [1; 2] [6; 7] [11; 12]
*)
let btree3 =
  Node(Leaf [1; 2], [(5, Leaf [6; 7]); (10, Leaf [11; 12])])

(*
              8
           /     \
      5         12
    /   \       /   \
 [1; 2] [6; 7] [9; 10] [13; 14]
*)
let btree4 =
  Node(
    Node(Leaf [1; 2], [(5, Leaf [6; 7])]),
    [(8, Node(Leaf [9; 10], [(12, Leaf [13; 14])]))]
  )

(*
             4       8      12
           /   \  /    \  /    \
      [1; 2] [5; 6] [9;10] [13; 14]
*)
let btree5 =
  Node(
    Leaf [1; 2],
    [(4, Leaf [5; 6]); (8, Leaf [9;10]); (12, Leaf [13; 14])]
  )
(*

                      [15]
                  /           \
         [5, 10]               [20, 25, 30]
        /   |    \             /  |    |    \
    [1, 3] [6, 9] [11, 13] [16, 18] [21, 23] [26, 28, 29] [31, 33, 34]
*)

let btree6 =
  Node(
    Node(Leaf [1; 3], 
         [(5, Leaf [6; 9]); 
          (10, Leaf [11; 13])]), 
    [(15, Node(Leaf [16; 18], 
               [(20, Leaf [21; 23]); 
                (25, Leaf [26; 28; 29]); 
                (30, Leaf [31; 33; 34])]))]
  )


(* Teste si `l` est une liste triée sans répétition *)
let rec is_unique_sorted: 'a list -> bool = function
  | _ :: [] | [] -> true
  | x :: y :: q  -> is_unique_sorted (y :: q) && x < y

(* Teste si la longueur d'une liste `l` est entre `a` et `b` (intervalle fermé) *)
let length_between (l: 'a list) (a: int) (b: int): bool =
  let n = List.length l in
  a <= n && n <= b

(* Calcule les profondeurs de toutes les feuilles d'un B-arbre *)
let rec all_leaves_depth (acc: int): btree -> int list = function
  | Leaf x -> [acc]
  | Node(a0, ka) ->
      a0 :: (List.map snd ka)
      |> List.map (all_leaves_depth (acc+1))
      |> List.fold_left (@) []

(* Vérifie qu'une liste est constante *)
(* On a la convention que la liste vide est constante *)
let rec is_constant: 'a list -> bool = function
  | [] -> true
  | x :: q -> List.for_all (fun y -> y = x) q

(* Vérifie que toutes les feuilles sont à la même profondeur *)
let all_same_depth (tl: btree list): bool =
  List.for_all (fun t -> is_constant (all_leaves_depth 0 t)) tl

(* Récupère toutes les clés d'un B-arbre  *)
let rec all_keys: btree -> key list = function
  | Leaf keys -> keys
  | Node (a0, ka) ->
      (* Découverte de `List.split` après avoir écrit cette fonction *)
      let children = a0 :: (List.map snd ka)
      and     keys =        List.map fst ka  in
      let children_keys = List.map all_keys children in
      List.fold_left (@) [] (keys :: children_keys)

(* Vérifie que tous les sous-arbres sont "triés et bornés" par les clés : *)
(*                    a0 < k1 < a1 < ... < kn < an                        *)
(* où on note a0 < k1 si toutes les clés de a0 sont inférieures strictes à k1 *)
let rec is_sorted_keys_subtrees (a0: btree) : (key * btree) list -> bool = function
  | [] -> true
  | (k1, a1) :: q -> 
         List.for_all (fun a0_key -> a0_key < k1) (all_keys a0)
      && List.for_all (fun a1_key -> k1 < a1_key) (all_keys a1)
      && is_sorted_keys_subtrees a1 q

(* Vérifie qu'un nœud est bien un nœud valide d'un B-arbre *)
(* On supposera ici ne pas être dans le cas de la racine *)
(* Beaucoup de calculs redondants ici, mais une approche simple à écrire *)
(* et à utiliser (dans des preuves notamment) en Rocq plus tard *)
let rec is_btree_valid_aux (order: int): btree -> bool = function
  | Leaf(keys) -> is_unique_sorted keys && length_between keys (order / 2) order
  | Node(a0, ka) ->
      (* Découverte de `List.split` après avoir écrit cette fonction *)
      let children = a0 :: (List.map snd ka)
      and     keys =        List.map fst ka  in
         length_between keys (order / 2) order              (* On vérifie que le nb de clés est entre ordre et ordre / 2    *)
      && is_sorted_keys_subtrees a0 ka                      (* On vérifie que clés de a_(i-1) < k_i < clés de a_i           *)
      && List.for_all (is_btree_valid_aux order) children   (* On vérifie que les enfants aussi sont valides                *)


(* Vérifie qu'un arbre est un B-arbre valide *)
(* Beaucoup de calculs redondants ici, mais une approche simple à écrire *)
(* et à utiliser (dans des preuves notamment) en Rocq plus tard *)
let is_btree_valid (order: int) (n: btree): bool =
  match n with
  | Leaf(keys) -> is_unique_sorted keys && length_between keys 1 (order)
  | Node(a0, ka) ->
      (* Découverte de `List.split` après avoir écrit cette fonction *)
      let children = a0 :: (List.map snd ka)
      and     keys =        List.map fst ka  in
         length_between keys 1 order                        (* On vérifie que le nb de clés est entre 0 et l'ordre              *)
      && all_same_depth children                            (* On vérifie que toutes les feuilles sont à la même profondeur     *)
      && is_sorted_keys_subtrees a0 ka                      (* On vérifie que clés de a_(i-1) < k_i < clés de a_i               *)
      && List.for_all (is_btree_valid_aux order) children   (* On vérifie que les enfants aussi sont valides (cas non racine)   *)

(* Recherche de la clé `x` dans un B-arbre *)
let rec search (x: key) (bt: btree): bool =
  match bt with
  | Leaf(keys) -> List.mem x keys
  | Node(a0, ka) ->
    let rec search_keys (a0: btree): (key * btree) list -> bool = function
      | [] -> search x a0
      | (k1, a1) :: ka ->
        if x < k1 then search x a0
        else if x = k1 then true
        else search_keys a1 ka
    in
    search_keys a0 ka

(* Insertion dans une liste triée de `x` *)
let rec insert_in_list (x: 'a): 'a list -> 'a list = function
  | a :: q when a < x -> a :: (insert_in_list x q)
  | a :: q when a = x -> a :: q
  | l                 -> x :: l

(* Séparation d'une liste `l` en `left`, `mid`, `right` *)
(* telle que `mid` soit la médiane de `l` et que        *)
(*           `l = left @ [mid] @ right`                 *) 
let split_list (l: 'a list): ('a list) * 'a * ('a list) =
  let half = (List.length l) / 2 in
  let x = List.fold_left (
    (* dans h1, on place la première partie *)
    (* dans h2, on place la seconde partie *)
    (* dans m, on place la médiane (type option) *)
    (* i représente l'indice dans la liste *)
      fun (h1,h2,m,i) x ->
        if i > half then (h1, x::h2, m, i+1)
        else if i = half then (h1, h2, Some x, i+1)
        else (x::h1, h2, m, i+1)
    ) ([], [], None, 0) l
  in
  match x with
  | (first_half, second_half, Some middle, _) -> (List.rev first_half, middle, List.rev second_half)
  | (_,_,None,_) -> failwith "Cannot split an empty sized list"

(* Trouve le bon sous-arbre pour la clé `x` dans un nœud `Node(a0, ka)` *)
let rec find_right_subtree (x: key) (a0: btree) (ka: (key * btree) list): btree =
  match ka with
  | [] -> a0
  | (k1, a1)::q  when k1 < x -> find_right_subtree x a1 q
  | (k1,  _)::_  when k1 = x -> failwith "Duplicate key"
  | (_,   _)::_              -> a0


(* On remplace le sous-arbre s par s' dans le nœud Node(a0, ka) *)
let rec put_inplace_replace (a0: btree) (ka: (key * btree) list) (s: btree) (s': btree): btree * ((key * btree) list) =
  match ka with
  | _ when a0 = s -> (s', ka)
  | (k1,a1)::q ->
      let (a1', q') = put_inplace_replace a1 q s s' in
      (a0, (k1,a1')::q')
  | [] -> (a0, ka)

(* Place la clé mid (avec à gauche left et à droite right) dans le nœud Node(a0,ka) *)
let rec put_inplace_between (a0: btree) (ka: (key * btree) list) (mid: key) (left: btree) (right: btree): btree * (key * btree) list =
  match ka with
  | [] -> (left, [(mid, right)])
  | (k1,a1)::rest when mid > k1 ->
      let (a1', rest') = put_inplace_between a1 rest mid left right in
      (a0, (k1,a1')::rest')
  | _ -> (left, (mid, right)::ka)



(* Un nœud est-il complet ? *)
let rec is_complete (order: int) (t: btree): bool =
  match t with
  | Node(_, ka) ->
      let keys = List.map snd ka in
      List.length keys >= order
  | Leaf(keys) ->
      List.length keys >= order

(* Récupère le nème élément et le (n+1)ème élément dans `l` *)
let rec get_nth_and_next (l: 'a list) (n: int): 'a * 'a =
  match l with
  |      []            -> failwith "No nth element"
  |       _ when n < 0 -> failwith "No nth element"
  | x::y::_ when n = 0 -> (x,y)
  |    x::q            -> get_nth_and_next q (n-1)

type insertion_result =
  | MoveUp of btree * key * btree (* On remonte la médiane au niveau du dessus : `MoveUp(left, mid, right)` *)
  | Okay of btree                 (* Plus besoin de remonter de médiane : `Stop(tree)` *)
(* J'aurai pu utiliser un type `btree * (key * btree)` option à la place (c'est équivalent) *)

(* On coupe un nœud `Node(a0, ka)` en trois parties : *)
(* la partie avant la médiane, la médiane, et la partie après la médiane *)
let rec split_node (a0: btree) (ka: (key * btree) list): btree * key * btree =
  let keys = List.map fst ka in

  let (mid, mid') = get_nth_and_next keys ((List.length keys) / 2) in

  let ka_prev = List.filter (fun (k, a) -> k < mid ) ka
  and ka_next = List.filter (fun (k, a) -> k > mid') ka
  and (_,asplit) = List.find (fun (k,a) -> k = mid') ka in

  let left = Node(a0, ka_prev) and right = Node(asplit, ka_next) in
  (left, mid, right)

(* Insère un élément `x` dans `t` *)
(* Renvoie un `insertion_result` qui peut demander de séparer la racine *)
(* (ce qui fait dans la fonction  `insert`, plus bas) *)
let rec insert_at_node (order: int) (x: key) (t: btree): insertion_result =
  match t with
  | Leaf keys ->
      let keys' = insert_in_list x keys in
      if is_complete order t then
        let (left, mid, right) = split_list keys' in
        MoveUp(Leaf left, mid, Leaf right)
      else
        Okay(Leaf keys')
  | Node(a0, ka) ->
      let s = find_right_subtree x a0 ka in
      begin
        match insert_at_node order x s with
        | Okay s' ->
            let (a0, ka) = put_inplace_replace a0 ka s s' in
            Okay(Node(a0, ka))
        | MoveUp(left, mid, right) ->
            let (a0, ka) = put_inplace_between a0 ka mid left right in
            if is_complete order t then
              let left, mid, right = split_node a0 ka in
              MoveUp(left, mid, right)
            else
              Okay(Node(a0, ka))
      end

(* Insère `x` dans le B-arbre `t` d'ordre `order` *)
(* appelé ici sur la racine du B-arbre *)
let insert (order: int) (x: key) (t: btree): btree =
  if search x t then t
  else
    match insert_at_node order x t with
    |                  Okay t' -> t'
    | MoveUp(left, mid, right) -> Node(left, [(mid, right)])


(********************************************************)
(* TEST DES FONCTIONS DÉFINIES                          *)
(********************************************************)

(* `assert` avec un joli message d'erreur *)
let custom_assert (cond: bool) (message: string) =
  if not cond then
    print_endline (message ^ "\n\n");
  assert cond

let test () =
  (* Quelques exemples de B-arbre et leur ordre *)
  let examples = [
    (btree1, 4);
    (btree2, 4);
    (btree3, 4);
    (btree4, 3);
    (btree5, 5);
    (btree6, 5)
  ] in

  (* On testera sur les entiers de l'intervalle [| 1, 40 |]*)
  let other_keys_to_check = List.init 40 (fun i -> i) in

  List.iteri (fun i (t, order) ->
    print_endline ("Test btree" ^ (string_of_int (i+1)));

    (* Teste que les arbres sont bien des arbres valides (avec l'ordre donné) *)
    custom_assert (is_btree_valid order t) ("=> [is_btree_valid] Current tree is not a valid order " ^ (string_of_int order) ^ " btree");

    (* Teste la correction de `search` sur les clés de l'arbre *)
    let keys = all_keys t in
    List.iter (fun k ->
      custom_assert (search k t) ("=> [search] Current tree does not contain key " ^ string_of_int k)
    ) keys;

    (* Teste la correction de `search` sur les clés qui ne sont pas dans l'arbre *)
    let other = List.filter (fun i -> not (List.mem i keys)) other_keys_to_check in
    List.iter (fun k ->
      custom_assert (not (search k t)) ("=> [search] Current tree does contain key " ^ string_of_int k)
    ) other;


    (* On essaie d'insérer 10 clés dans l'arbre (qui n'y sont pas déjà) *)
    let to_insert = List.filteri (fun i _ -> i < 10) other in
    let t' = List.fold_left (fun t k ->
      let t' = insert order k t in
      custom_assert (search k t') ("=> [insert] Current tree does not contain key " ^ string_of_int k);
      custom_assert (is_btree_valid order t') ("=> [insert] Current tree is not a valid order " ^ (string_of_int order) ^ " btree");
      t'
    ) t to_insert in

    (* On vérifie que toutes les clés sont toujours présentes *)
    List.iter (fun k ->
      custom_assert (search k t') ("=> [insert] Current tree does not contain key " ^ string_of_int k)
    ) (to_insert @ keys);

    print_endline "=> Test successful\n\n"
  ) examples


(********************************************************)
(* FONCTIONS D'AFFICHAGE                                *)
(********************************************************)

(* Affiche une liste (où `f` permet d'afficher un élément) *)
let rec print_list (f: 'a -> unit): 'a list -> unit = function
  | [] -> ()
  | x :: q -> (f x; print_string "; "; print_list f q)

(* Affiche un B-arbre (où `f` permet d'afficher une clé *)
(* (comme les clés sont des entiers, c'est `print_int`) *)
let rec print_btree (f: key -> unit) = function
  | Leaf k -> print_string "Leaf("; print_list f k; print_string ")"
  | Node(a0, ka) ->
      print_string "Node(";
      print_btree f a0;
      List.iter (fun (k, a) -> f k; print_string ";"; print_btree f a; print_string ";") ka;
      print_string ")"
