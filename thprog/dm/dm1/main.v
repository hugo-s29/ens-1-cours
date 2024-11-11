Require Export Datatypes.
Require Export Lists.List.
Require Export Bool.
Require Export Arith.
Require Export Lia.
Import ListNotations.

Definition key: Set := nat.

Inductive b: Set :=
  | Leaf1: key -> b
  | Leaf2: key -> key -> b
  | Node1: b -> key -> b -> b
  | Node2: b -> key -> b -> key -> b -> b
  .

(* Toutes les clés d'un B-arbre *)
Fixpoint all_keys (t: b): list key :=
  match t with
  |            Leaf1 x => [x]
  |          Leaf2 x y => [x; y]
  |       Node1 t x t' => (x :: all_keys t) ++ (all_keys t')
  | Node2 t x t' y t'' => (x :: y :: all_keys t) ++ (all_keys t') ++ (all_keys t'')
end.

(* Équivalent du `List.forall` en OCaml *)
Fixpoint list_forall {A: Type} (f: A -> bool) (l: list A): bool :=
  match l with
  | x :: q => (f x) && list_forall f q
  | nil => true
  end.

(* Récupère la profondeur sous forme d'un type option
   si elle n'est pas constante, renvoie None
   si elle l'est, renvoie cette constante
 *)

Fixpoint get_depth (t: b): option nat :=
  match t with
  | Leaf1 _ | Leaf2 _ _ => Some 0
  | Node1 t _ t' =>
      match get_depth t, get_depth t' with
      | None, _ => None
      | _, None => None
      | Some x, Some y => if x =? y then Some (S x) else None
      end
  | Node2 t _ t' _ t'' =>
      match get_depth t, get_depth t', get_depth t'' with
      | None, _, _ => None
      | _, None, _ => None
      | _, _, None => None
      | Some x, Some y, Some z =>
          if (x =? y) then (
            if (y =? z) then
              Some (S x)
            else
              None
          ) else
            None
      end
  end.

(* Un arbre a-t-il ses feuilles à la même profondeur ? *)
Definition all_same_depth (t: b): bool :=
  match get_depth t with
  | None => false
  | Some _ => true
  end.

(* Dit si `t0` est un B-arbre (fixpoint) *)
Fixpoint is_btree (t0: b): bool :=
  match t0 with
  | Leaf1 x => true
  | Leaf2 x y => x <? y
  | Node1 t x t' =>
      (is_btree t) && (is_btree t')
      && all_same_depth t0
      && list_forall (fun a  => a <? x ) (all_keys t )
      && list_forall (fun a' => x <? a') (all_keys t')
  | Node2 t x t' y t'' =>
      (is_btree t) && (is_btree t') && (is_btree t'')
      && (x <? y)
      && all_same_depth t0
      && list_forall (fun a  => a <? x ) (all_keys t )
      && list_forall (fun a' => x <? a') (all_keys t' ++ all_keys t'')
      && list_forall (fun a  => a <? y ) (all_keys t  ++ all_keys t' )
      && list_forall (fun a' => y <? a') (all_keys t'')
  end.

(* Une clé est-elle dans un arbre *)
Inductive is_key: key -> b -> Prop :=
  | Leaf1_key: forall k, is_key k (Leaf1 k)
  | Leaf2_key_left: forall k k', is_key k (Leaf2 k k')
  | Leaf2_key_right: forall k k', is_key k' (Leaf2 k k')
  | Node1_key_middle: forall k t t', is_key k (Node1 t k t')
  | Node1_key_left: forall k k' t t', is_key k t -> is_key k (Node1 t k' t')
  | Node1_key_right: forall k k' t t', is_key k t' -> is_key k (Node1 t k' t')
  | Node2_key1: forall k k' k'' t t' t'', is_key k t -> is_key k (Node2 t k' t' k'' t'')
  | Node2_key2: forall k k' t t' t'', is_key k (Node2 t k t' k' t'')
  | Node2_key3: forall k k' k'' t t' t'', is_key k t' -> is_key k (Node2 t k' t' k'' t'')
  | Node2_key4: forall k k' t t' t'', is_key k' (Node2 t k t' k' t'')
  | Node2_key5: forall k k' k'' t t' t'', is_key k t'' -> is_key k (Node2 t k' t' k'' t'')
  .

(* est-ce que x majore tout l'arbre t (strictement) *)
Inductive is_strict_maximal: b -> nat -> Prop :=
  | Leaf1_max: forall x k, k < x -> is_strict_maximal (Leaf1 k) x
  | Leaf2_max: forall x k k', k < x -> k' < x -> is_strict_maximal (Leaf2 k k') x
  | Node1_max: forall x k t t', k < x -> is_strict_maximal t x -> is_strict_maximal t' x -> is_strict_maximal (Node1 t k t') x
  | Node2_max: forall x k k' t t' t'', k < x -> k' < x -> is_strict_maximal t x -> is_strict_maximal t' x -> is_strict_maximal t'' x -> is_strict_maximal (Node2 t k t' k' t'') x
  .

(* est-ce que x minore tout l'arbre t (strictement) *)
Inductive is_strict_minimal: b -> nat -> Prop :=
  | Leaf1_min: forall x k, k > x -> is_strict_minimal (Leaf1 k) x
  | Leaf2_min: forall x k k', k > x -> k' > x -> is_strict_minimal (Leaf2 k k') x
  | Node1_min: forall x k t t', k > x -> is_strict_minimal t x -> is_strict_minimal t' x -> is_strict_minimal (Node1 t k t') x
  | Node2_min: forall x k k' t t' t'', k > x -> k' > x -> is_strict_minimal t x -> is_strict_minimal t' x -> is_strict_minimal t'' x -> is_strict_minimal (Node2 t k t' k' t'') x
  .

(* Les feuilles sont-elles à la même profondeur `k` ? *)
Inductive leaves_at_depth: b -> nat -> Prop :=
  | Leaf1_depth_zero: forall k, leaves_at_depth (Leaf1 k) 0
  | Leaf2_depth_zero: forall k k', leaves_at_depth (Leaf2 k k') 0
  | Node1_depth_succ: forall t t' k n, leaves_at_depth t n -> leaves_at_depth t' n -> leaves_at_depth (Node1 t k t') (S n)
  | Node2_depth_succ: forall t t' t'' k k' n, leaves_at_depth t n -> leaves_at_depth t' n -> leaves_at_depth t'' n -> leaves_at_depth (Node2 t k t' k' t'') (S n)
  .

(* Dit si `t` est un B-arbre (inductif) *)
Inductive btree: b -> Prop :=
  | Leaf1_btree: forall x, btree(Leaf1 x)
  | Leaf2_btree: forall x y, x < y -> btree(Leaf2 x y)
  | Node1_btree: forall k t t' x,
      btree t ->
      btree t' ->
      is_strict_maximal t  x ->
      is_strict_minimal t' x ->
      leaves_at_depth t   k ->
      leaves_at_depth t'  k ->
      btree(Node1 t x t')
  | Node2_btree: forall k t t' t'' x y,
      btree t ->
      btree t' ->
      btree t'' ->
      x < y ->
      is_strict_maximal t   x ->
      is_strict_minimal t'  x ->
      is_strict_maximal t'  y ->
      is_strict_minimal t'' y ->
      leaves_at_depth t   k ->
      leaves_at_depth t'  k ->
      leaves_at_depth t'' k ->
      btree(Node2 t x t' y t'')
  .

(* On démontre l'équivalence de définition entre all_keys (qui dit si un entier est une clé d'un B-arbre)
   et l'appartenance à la liste all_keys (qui contient toutes les clés d'un B- arbre) *)
Lemma all_keys_correct: forall t k, In k (all_keys t) <-> is_key k t.
Proof.
  intros; split.
  - induction t; intro H; simpl in H; repeat destruct H.
    * constructor.
    * constructor.
    * constructor.
    * constructor.
    * apply in_app_or in H; destruct H.
      + apply Node1_key_left; exact (IHt1 H).
      + apply Node1_key_right; exact (IHt2 H).
    * apply Node2_key2.
    * apply Node2_key4.
    * apply in_app_or in H; destruct H; [|apply in_app_or in H; destruct H].
      + apply Node2_key1; exact (IHt1 H).
      + apply Node2_key3; exact (IHt2 H).
      + apply Node2_key5; exact (IHt3 H).
  - induction t; intro H; simpl; inversion H.
    * left; reflexivity.
    * left; reflexivity.
    * right; left; reflexivity.
    * left; reflexivity.
    * clear H0 H1 H3 H4 t' t k' k1; right.
      apply in_or_app; left; exact (IHt1 H2).
    * clear H0 H1 H3 H4 t' t k' k1; right.
      apply in_or_app; right; exact (IHt2 H2).
    * clear H0 H1 H3 H4 H5 H6 t t' t'' k' k'' k2; right; right.
      apply in_or_app; left; exact (IHt1 H2).
    * left; reflexivity.
    * clear H0 H1 H3 H4 H5 H6 t t' t'' k' k'' k2; right; right.
      apply in_or_app; right; apply in_or_app; left; exact (IHt2 H2).
    * right; left; reflexivity.
    * clear H0 H1 H3 H4 H5 H6 t t' t'' k' k'' k2; right; right.
      apply in_or_app; right; apply in_or_app; right; exact (IHt3 H2).
Qed.

(* On démontre, en toute généralité, que `list_forall` retourne vrai si tous les éléments vérifie le prédicat donné. *)
Lemma forall_correct {A: Type}: forall (f: A -> bool),
  forall l: list A, (list_forall f l = true) <-> (forall x, In x l -> f x = true).
Proof.
  intros; split; intros.
  - induction l; inversion H0; inversion H; rewrite H3; apply andb_prop in H3; destruct H3.
    + rewrite H1 in H2. assumption.
    + apply IHl; assumption.
  - induction l; simpl; try reflexivity.
    apply andb_true_intro; split.
    + apply H. constructor. reflexivity.
    + apply IHl. intros. apply H. right; assumption.
Qed.

(* Un prédicat f est vrai sur l ++ l' ssi il est vrai sur l et sur l'. *)
Lemma forall_split {A: Type}: forall (f: A -> bool),
  forall l l': list A, (list_forall f (l++l') = true) <-> (list_forall f l = true /\ list_forall f l' = true).
Proof.
  intros; split; intros; try split; apply forall_correct; intros; repeat rewrite forall_correct in H.
  1,2:apply H; apply in_or_app.
  - left. assumption.
  - right. assumption.
  - destruct H. apply in_app_or in H0. destruct H0; [apply H|apply H1]; assumption.
Qed.

(* Tiers exclu sur les entiers *)
(* Pas si utilisé dans les premières preuves, mais l'est dans la suite *)
Lemma tiers_exclu: forall x y: nat, x = y \/ x <> y.
Proof.
  induction x; induction y.
  1: left; reflexivity.
  1-2: right; intro; inversion H.
  destruct (IHx y).
  - left. rewrite H. reflexivity.
  - right. intro. inversion H0. apply H. assumption.
Qed.

(* Quelques lemmes qui sont très probablement dans Nat *)
Lemma eqb_refl: forall x, x =? x = true.
Proof.
  induction x; simpl; [|apply IHx]; reflexivity.
Qed.

Lemma eqb_correct: forall x y, x =? y = true <-> x = y.
Proof.
  induction x; induction y; simpl in * |- *; split; intros; try reflexivity.
  1-4: inversion H.
  - assert (x = y) by (apply IHx; assumption).
    rewrite H0; reflexivity.
  - rewrite IHx. inversion H. reflexivity.
Qed.

Lemma eqb_correct_n: forall x y, x =? y = false <-> x <> y.
Proof.
  intros; destruct (tiers_exclu x y); split; intro.
  - rewrite H in * |- *; intro. rewrite <- not_true_iff_false in H0. apply H0. apply eqb_refl.
  - exfalso. apply H0. assumption.
  - assumption.
  - rewrite <- not_true_iff_false. intro. apply H. apply eqb_correct. assumption.
Qed.

(* On montre l'équivalence des définitions inductives/fixpoint pour trouver la hauteur d'un arbre *)
(* (et surtout montrer quelle est constante) *)
Lemma get_depth_correct: forall t h,
  get_depth t = Some h <-> leaves_at_depth t h.
Proof.
  induction t; simpl in * |- *; split; intros.
  - inversion H; constructor.
  - inversion H; reflexivity.
  - inversion H; constructor.
  - inversion H; reflexivity.
  - destruct (get_depth t1); [|inversion H].
    destruct (get_depth t2); [|inversion H].
    remember (n =? n0) as b.
    destruct b; inversion H.
    constructor.
    * apply IHt1. reflexivity.
    * apply IHt2. symmetry in Heqb. rewrite eqb_correct in Heqb.
      rewrite Heqb. reflexivity.
  - destruct (get_depth t1);
    destruct (get_depth t2).
    * remember (n =? n0) as b.
      destruct b; inversion H.
      all: rewrite H2; clear H1 H3 H0 t t' k0;
            assert(Some n = Some n1) by (apply IHt1; assumption);
            inversion H0.
            rewrite H2.
      + reflexivity.
      + assert(Some n0 = Some n1) by (apply IHt2; assumption).
        inversion H1.
        exfalso.
        symmetry in Heqb; rewrite eqb_correct_n in Heqb.
        apply Heqb.
        rewrite H3.
        symmetry.
        assumption.
    * inversion H.
      assert(None = Some n0) by (apply IHt2; assumption).
      inversion H6.
    * inversion H.
      assert(None = Some n0) by (apply IHt1; assumption).
      inversion H6.
    * inversion H.
      assert(None = Some n) by (apply IHt1; assumption).
      inversion H6.
  - destruct (get_depth t1);
    destruct (get_depth t2);
    destruct (get_depth t3);
    try inversion H.
    clear H1.
    remember (n =? n0) as b.
    remember (n0 =? n1) as b'.
    destruct b; destruct b'; inversion H.
    symmetry in Heqb, Heqb'.
    rewrite eqb_correct in Heqb, Heqb'.
    rewrite Heqb in * |- *; rewrite Heqb' in * |- *.
    clear Heqb Heqb'.
    constructor; [apply IHt1|apply IHt2|apply IHt3]; reflexivity.
  - destruct (get_depth t1);
    destruct (get_depth t2);
    destruct (get_depth t3).
    * remember (n =? n0) as b.
      remember (n0 =? n1) as b'.
      destruct b; destruct b'; symmetry in Heqb, Heqb';
      inversion H; clear H0 H1 H2 H4 H5 t t' t'' k1 k'.
      + rewrite eqb_correct in Heqb, Heqb'.
        assert(Some n = Some n2) by (apply IHt1; assumption).
        inversion H0.
        reflexivity.
      + rewrite eqb_correct in Heqb; rewrite eqb_correct_n in Heqb'.
        exfalso.
        apply Heqb'.
        assert(Some n0 = Some n2) by (apply IHt2; assumption).
        assert(Some n1 = Some n2) by (apply IHt3; assumption).
        inversion H0; inversion H1.
        reflexivity.
      + rewrite eqb_correct_n in Heqb; rewrite eqb_correct in Heqb'.
        exfalso.
        apply Heqb.
        assert(Some n  = Some n2) by (apply IHt1; assumption).
        assert(Some n0 = Some n2) by (apply IHt2; assumption).
        inversion H0; inversion H1.
        reflexivity.
      + rewrite eqb_correct_n in Heqb.
        exfalso.
        apply Heqb.
        assert(Some n  = Some n2) by (apply IHt1; assumption).
        assert(Some n0 = Some n2) by (apply IHt2; assumption).
        inversion H0; inversion H1.
        reflexivity.
    (* De multiples cas inintéressants (None = Some x avec les hypothèses) *)
    * inversion H.
      assert(None = Some n1) by (apply IHt3; assumption).
      inversion H9.
    * inversion H.
      assert(None = Some n1) by (apply IHt2; assumption).
      inversion H9.
    * inversion H.
      assert(None = Some n0) by (apply IHt2; assumption).
      inversion H9.
    * inversion H.
      assert(None = Some n1) by (apply IHt1; assumption).
      inversion H9.
    * inversion H.
      assert(None = Some n0) by (apply IHt1; assumption).
      inversion H9.
    * inversion H.
      assert(None = Some n0) by (apply IHt1; assumption).
      inversion H9.
    * inversion H.
      assert(None = Some n) by (apply IHt1; assumption).
      inversion H9.
Qed.

(* Équivalence des prédicats "feuilles à la même profondeur k" *)
Lemma all_same_depth_correct: forall t, all_same_depth t = true <-> exists k, leaves_at_depth t k.
Proof.
  split; intros.
  - unfold all_same_depth in H.
    remember (get_depth t) as h; destruct h; [|inversion H].
    exists n.
    apply get_depth_correct.
    symmetry.
    assumption.
  - destruct H.
    inversion H; try reflexivity.
    + unfold all_same_depth.
      assert(get_depth (Node1 t0 k t') = Some (S n))
      by (apply get_depth_correct; constructor; assumption).
      rewrite H4; reflexivity.
    + unfold all_same_depth.
      assert(get_depth (Node2 t0 k t' k' t'') = Some (S n))
      by (apply get_depth_correct; constructor; assumption).
      rewrite H5; reflexivity.
Qed.

(* Démontre que `is_strict_max` vérifie que tout t est inférieur à k (strictement) *)
Lemma strict_max_correct: forall t k, list_forall (fun a : nat => a <? k) (all_keys t) = true <-> is_strict_maximal t k.
Proof.
  intros; split; intros.
  + rewrite forall_correct in H.
    assert(forall x : nat, is_key x t -> (x <? k) = true)
    by (intros; apply all_keys_correct in H0; exact (H x H0)).
    induction t.
    1,2: constructor; apply leb_complete; apply H0; constructor.
    - constructor.
      * apply leb_complete. apply H0. constructor.
      * apply IHt1; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
      * apply IHt2; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
    - constructor.
      * apply leb_complete. apply H0. apply Node2_key2.
      * apply leb_complete. apply H0. apply Node2_key4.
      * apply IHt1; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
      * apply IHt2; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
      * apply IHt3; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
  + apply forall_correct. intros. apply leb_correct.
    induction H; rewrite all_keys_correct in H0; inversion H0; try assumption.
    - apply IHis_strict_maximal1; rewrite all_keys_correct; assumption.
    - apply IHis_strict_maximal2; rewrite all_keys_correct; assumption.
    - apply IHis_strict_maximal1; rewrite all_keys_correct; assumption.
    - apply IHis_strict_maximal2; rewrite all_keys_correct; assumption.
    - apply IHis_strict_maximal3; rewrite all_keys_correct; assumption.
Qed.

(* Démontre que `is_strict_min` vérifie que tout t est supérieur à k (strictement) *)
Lemma strict_min_correct: forall t k, list_forall (fun a : nat => k <? a) (all_keys t) = true <-> is_strict_minimal t k.
Proof.
  intros; split; intros.
  + rewrite forall_correct in H.
    assert(forall x : nat, is_key x t -> (k <? x) = true)
    by (intros; apply all_keys_correct in H0; exact (H x H0)).
    induction t.
    1,2: constructor; apply leb_complete; apply H0; constructor.
    - constructor.
      * apply leb_complete. apply H0. constructor.
      * apply IHt1; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
      * apply IHt2; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
    - constructor.
      * apply leb_complete. apply H0. apply Node2_key2.
      * apply leb_complete. apply H0. apply Node2_key4.
      * apply IHt1; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
      * apply IHt2; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
      * apply IHt3; intros; apply H0; [rewrite all_keys_correct in H1|]; constructor; assumption.
  + apply forall_correct. intros. apply leb_correct.
    induction H; rewrite all_keys_correct in H0; inversion H0; try assumption.
    - apply IHis_strict_minimal1; rewrite all_keys_correct; assumption.
    - apply IHis_strict_minimal2; rewrite all_keys_correct; assumption.
    - apply IHis_strict_minimal1; rewrite all_keys_correct; assumption.
    - apply IHis_strict_minimal2; rewrite all_keys_correct; assumption.
    - apply IHis_strict_minimal3; rewrite all_keys_correct; assumption.
Qed.

(* Démontre l'implication fonction => inductif *)
Proposition fonc_imp_ind: forall t, is_btree t = true -> btree t.
Proof.
  induction t; intro H.
  - constructor.
  - inversion H. constructor. apply leb_complete. exact H1.
  - inversion H. 
    apply andb_prop in H1; destruct H1.
    repeat (apply andb_prop in H0; destruct H0).
    rewrite strict_min_correct in H1.
    rewrite strict_max_correct in H2.
    rewrite all_same_depth_correct in H3; destruct H3; destruct x; inversion H3.
    apply (Node1_btree x).
    1:apply IHt1.
    2:apply IHt2.
    all:assumption.
  - inversion H. 
    apply andb_prop in H1; destruct H1.
    repeat (apply andb_prop in H0; destruct H0).
    rewrite forall_split in H2; destruct H2.
    rewrite forall_split in H3; destruct H3.
    rewrite strict_min_correct in H1.
    rewrite strict_min_correct in H10.
    rewrite strict_max_correct in H2.
    rewrite strict_min_correct in H3.
    rewrite strict_max_correct in H4.
    rewrite strict_max_correct in H9.
    apply leb_complete in H6.
    rewrite all_same_depth_correct in H5; destruct H5; destruct x; inversion H5.
    apply (Node2_btree x).
    1:apply IHt1.
    2:apply IHt2.
    3:apply IHt3.
    all:assumption.
Qed.

(* Démontre l'implication inductif => fonction *)
Proposition ind_imp_fonc: forall t, btree t -> is_btree t = true.
Proof.
  induction t; intro; simpl; inversion H.
  - reflexivity.
  - apply leb_correct. assumption.
  - repeat (rewrite andb_true_iff); repeat split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + rewrite all_same_depth_correct.
      rewrite <- get_depth_correct in H7, H8.
      exists (S k0).
      constructor; apply get_depth_correct; assumption.
    + rewrite forall_correct; intros.
      rewrite <- strict_max_correct in H5.
      rewrite forall_correct in H5.
      apply H5; assumption.
    + rewrite forall_correct; intros.
      rewrite <- strict_min_correct in H6.
      rewrite forall_correct in H6.
      apply H6; assumption.
  - repeat (rewrite andb_true_iff); repeat split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + apply IHt3; assumption.
    + apply leb_correct; assumption.
    + rewrite all_same_depth_correct.
      rewrite <- get_depth_correct in H13, H14, H15.
      exists (S k1).
      constructor; apply get_depth_correct; assumption.
    + rewrite forall_correct; intros.
      rewrite <- strict_max_correct in H9.
      rewrite forall_correct in H9.
      apply H9; assumption.
    + rewrite forall_correct; intros.
      rewrite in_app_iff in H16.
      destruct H16.
      * rewrite <- strict_min_correct in H10.
        rewrite forall_correct in H10.
        apply H10; assumption.
      * assert(k < x0).
        transitivity k0.
        assumption.
        rewrite <- strict_min_correct in H12.
        rewrite forall_correct in H12.
        apply leb_complete.
        apply H12; assumption.
        apply leb_correct; assumption.
    + rewrite forall_correct; intros.
      rewrite in_app_iff in H16.
      destruct H16.
      * assert(x0 < k0).
        transitivity k.
        rewrite <- strict_max_correct in H9.
        rewrite forall_correct in H9.
        apply leb_complete.
        apply H9; assumption.
        assumption.
        apply leb_correct; assumption.
      * rewrite <- strict_max_correct in H11.
        rewrite forall_correct in H11.
        apply H11; assumption.
    + rewrite forall_correct; intros.
      rewrite <- strict_min_correct in H12.
      rewrite forall_correct in H12.
      apply H12; assumption.
Qed.

(* L'équivalence des deux définitions *)
Theorem btree_equiv: forall t, is_btree t = true <-> btree t.
Proof.
  split; intro; [apply fonc_imp_ind|apply ind_imp_fonc]; assumption.
Qed.

(* mem t x indique si x est une clé de t *)
Fixpoint mem (t: b) (x: key): bool :=
  match t with
  | Leaf1 k => x =? k
  | Leaf2 k k' => (x =? k) || (x =? k')
  | Node1 t k t' => (x =? k) || mem t x || mem t' x
  | Node2 t k t' k' t'' => (x =? k) || (x =? k') || mem t x || mem t' x || mem t'' x
  end.

(* On détruit des \/ en cascade *)
Ltac destruct_ors :=
  match goal with
  | [ H: _ \/ _ |- _ ] => destruct H; destruct_ors
  | _ => idtac
  end.

(* On détruit des /\ en cascade *)
Ltac destruct_ands :=
  match goal with
  | [ H: _ /\ _ |- _ ] => destruct H; destruct_ands
  | _ => idtac
  end.

(* Inverse une hypothèse dans le cas d'égalité *)
Ltac if_eq_invert :=
  match goal with
  | [ G:_ |- _ = _ ] => inversion H
  | _ => idtac
  end.

(* `mem` est correct sur les instances positives *)
Lemma mem_correct: forall t x, mem t x = true <-> is_key x t.
Proof.
  induction t; split; simpl; intros;
  repeat try rewrite orb_true_iff in *;
  repeat try rewrite eqb_correct in *;
  destruct_ors;
  destruct_ands;
  if_eq_invert; try rewrite H; try reflexivity.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; [left|right]; reflexivity.
  - constructor.
  - apply Node1_key_left; apply IHt1; assumption.
  - apply Node1_key_right; apply IHt2; assumption.
  - inversion H; [left;left;reflexivity|left;right;apply IHt1|right;apply IHt2];assumption.
  - apply Node2_key2.
  - apply Node2_key4.
  - apply Node2_key1; apply IHt1; assumption.
  - apply Node2_key3; apply IHt2; assumption.
  - apply Node2_key5; apply IHt3; assumption.
  - inversion H.
    + left; left; right; apply IHt1; assumption.
    + left; left; left; left; reflexivity.
    + left; right; apply IHt2; assumption.
    + left; left; left; right; reflexivity.
    + right; apply IHt3; assumption.
Qed.

(* `mem` est correct sur les instances négatives *)
Lemma mem_correct_n: forall t x, mem t x = false <-> ~(is_key x t).
Proof.
  split; unfold not; intros.
  - rewrite <- mem_correct in H0.
    apply diff_true_false; rewrite <- H; symmetry; assumption.
  - remember (mem t x) as w. destruct w.
    + symmetry in Heqw. rewrite mem_correct in Heqw. exfalso. apply H. assumption.
    + reflexivity.
Qed.


(* Résultat d'une insertion 
  -> Okay t => on a réussi à insérer dans le sous arbre, et il devient t
  -> MoveUp t k t' => on fait remonter la racine `k` et les deux sous-arbres `t` et `t'`
 *)

Variant insertion_result: Type :=
  | MoveUp: b -> key -> b -> insertion_result
  | Okay: b -> insertion_result.

(* 
  L'insertion de x dans t au cas par cas
   (on renvoie un `Okay/MoveUp` mais on passera à un B-arbre dans `insert`...)
 *)
Fixpoint insert_aux (t: b) (x: key): insertion_result :=
  match t with
  | Leaf1 k => if x <? k then Okay(Leaf2 x k)
                else Okay(Leaf2 k x)
  | Leaf2 k k' =>
      if x <? k then MoveUp (Leaf1 x) k (Leaf1 k')
      else if x <? k' then MoveUp (Leaf1 k) x (Leaf1 k')
      else MoveUp (Leaf1 k) k' (Leaf1 x)
  | Node1 t k t' =>
      if x <? k then
        match insert_aux t x with
        | Okay t => Okay(Node1 t k t')
        | MoveUp t0 k0 t0' => Okay (Node2 t0 k0 t0' k t')
        end
      else
        match insert_aux t' x with
        | Okay t' => Okay(Node1 t k t')
        | MoveUp t1 k1 t1' => Okay (Node2 t k t1 k1 t1')
        end
  | Node2 t k t' k' t'' =>
      if x <? k then
        match insert_aux t x with
        | Okay t => Okay (Node2 t k t' k' t'')
        | MoveUp t0 k0 t0' => MoveUp (Node1 t0 k0 t0') k (Node1 t' k' t'')
        end
      else if x <? k' then
        match insert_aux t' x with
        | Okay t' => Okay (Node2 t k t' k' t'')
        | MoveUp t0 k0 t0' => MoveUp (Node1 t k t0) k0 (Node1 t0' k' t'')
        end
      else
        match insert_aux t'' x with
        | Okay t'' => Okay (Node2 t k t' k' t'')
        | MoveUp t0 k0 t0' => MoveUp (Node1 t k t') k' (Node1 t0 k0 t0')
        end
  end.

(* L'insertion de x dans un B-arbre t *)
Definition insert (t: b) (x: key): b :=
  if mem t x then t
  else match insert_aux t x with
       | Okay t => t
       | MoveUp t k t' => Node1 t k t'
       end.

Eval compute in insert (Leaf1 2) 3.
Eval compute in insert (Leaf2 2 4) 3.
Eval compute in insert (Node1 (Leaf2 1 2) 5 (Leaf2 7 8)) 6.
Eval compute in insert (Node1 (Leaf2 1 2) 5 (Leaf2 6 8)) 7.
Eval compute in insert (Node2 (Leaf2 1 2) 5 (Leaf2 6 7) 8 (Leaf2 10 11)) 9.
Eval compute in insert (Node2 (Leaf2 1 2) 5 (Leaf2 6 7) 9 (Leaf2 10 11)) 8.

(* On tente de tout ré-écrire *)
Ltac rewrite_everything :=
  repeat(
    try rewrite Nat.ltb_lt in *; 
    try rewrite Nat.ltb_ge in *;
    try rewrite orb_true_iff in *;
    try rewrite orb_false_iff in *;
    try rewrite eqb_correct in *;
    try rewrite eqb_correct_n in *
  ).

(*
  Pour l'insertion, on démontre deux lemmes principaux :
   1. les clés sont conservées (sauf qu'on ajoute `x` dans l'arbre avec insertion)
   2. la hauteur est conservée après insertion (sauf MoveUp, où elle est constante sur les deux sous-arbres)

  Puis, on prouve que `insert_aux` est correct et on conclut que `insert` l'est aussi.
*)

Lemma insertion_key: forall t x k t' t'', insert_aux t x = MoveUp t' k t'' -> (is_key k t \/ k = x).
Proof.
  induction t; simpl; intros.
  - remember (x <? k) as w; destruct w; inversion H.
  - remember (x <? k) as w; destruct w.
    + inversion H. left. constructor.
    + remember (x <? k0) as w; destruct w.
      * inversion H. right. reflexivity.
      * inversion H. left. constructor.
  - remember (x <? k) as w; destruct w.
    + remember (insert_aux t1 x) as w2; destruct w2; symmetry in Heqw2; inversion H.
    + remember (insert_aux t2 x) as w2; destruct w2; symmetry in Heqw2; inversion H.
  - remember (x <? k) as w; destruct w.
    + remember (insert_aux t1 x) as w2; destruct w2; symmetry in Heqw2; inversion H.
      left; apply Node2_key2.
    + remember (x <? k0) as w3; destruct w3.
      * remember (insert_aux t2 x) as w2; destruct w2; symmetry in Heqw2; inversion H.
        destruct (IHt2 x k2 b0 b1 Heqw2).
        -- left; apply Node2_key3; rewrite <- H2; assumption.
        -- right; rewrite <- H2; assumption.
      * remember (insert_aux t3 x) as w2; destruct w2; symmetry in Heqw2; inversion H.
        left; apply Node2_key4.
Qed.

(* On `destruct` une condition (ou un `insertion_result` par exemple) tout en se rappelant de la condition *)
(* Pourrait être renommé, mais pas d'idée de nom plus cohérent (destruct_remember ?) *)
Ltac destruct_cond c :=
  let x := fresh "cond" in
  remember c as x; destruct x.

(* Simplifie l'écriture du lemme sur la conservation des clés dans l'insertion *)
Inductive is_aux_key: insertion_result -> key -> Prop :=
  | Okay_key: forall k t, is_key k t -> is_aux_key (Okay t) k
  | MoveUp_key1: forall k t t' k', is_key k t -> is_aux_key (MoveUp t k' t') k
  | MoveUp_key2: forall k t t', is_aux_key (MoveUp t k t') k
  | MoveUp_key3: forall k t' t k', is_key k t' -> is_aux_key (MoveUp t k' t') k
  .

(* Dans plusieurs cas, on sait que la clé est dans un sous-arbre *)
(* On tente tout, jusqu'à trouver le bon *)
Ltac try_all_key_positions :=
  try (
      apply Leaf1_key
  ||  apply Leaf2_key_left
  ||  apply Leaf2_key_right
  ||  apply Node1_key_middle
  ||  apply Node2_key2
  ||  apply Node2_key4
  || (apply Node1_key_left; assumption)
  || (apply Node1_key_right; assumption)
  || (apply Node2_key1; assumption)
  || (apply Node2_key3; assumption)
  || (apply Node2_key5; assumption)
  ).

(* 1er lemme principal : l'insertion conserve les clés (plus x) *)
Lemma insertion_keys: forall t x k, x <> k -> is_aux_key (insert_aux t x) k <-> is_key k t.
Proof.
  intros; induction t; split; simpl in *; intros.
  * destruct(x <? k0); inversion H0; inversion H2; try constructor; exfalso; apply H; symmetry; assumption.
  * destruct(x <? k0); inversion H0; constructor; constructor.
  * destruct(x <? k0); [|destruct (x <? k1)]; inversion H0; try inversion H5; try constructor.
    all: exfalso; apply H; try assumption; symmetry; assumption.
  * destruct(x <? k0); [|destruct (x <? k1)]; inversion H0.
    all: try (apply MoveUp_key1; constructor).
    all: try apply MoveUp_key2.
    all: try (apply MoveUp_key3; constructor).
  * destruct (x <? k0); [destruct_cond (insert_aux t1 x)|destruct_cond (insert_aux t2 x)]; inversion H0; inversion H2.
    all: try apply Node1_key_middle.
    all: try (apply Node1_key_left; assumption).
    all: try (apply Node1_key_right; assumption).
    + apply Node1_key_left; apply IHt1; apply MoveUp_key1; assumption.
    + rewrite <- H7; apply Node1_key_left; apply IHt1; rewrite H7; apply MoveUp_key2.
    + apply Node1_key_left; apply IHt1; apply MoveUp_key3; assumption.
    + apply Node1_key_left; apply IHt1; constructor; assumption.
    + apply Node1_key_right; apply IHt2; apply MoveUp_key1; assumption.
    + rewrite <- H9; apply Node1_key_right; apply IHt2; rewrite H9; apply MoveUp_key2.
    + apply Node1_key_right; apply IHt2; apply MoveUp_key3; assumption.
    + apply Node1_key_right; apply IHt2; constructor; assumption.
  * destruct (x <? k0); [destruct_cond (insert_aux t1 x)|destruct_cond (insert_aux t2 x)];
    inversion H0; constructor.
    all: try_all_key_positions.
    + assert(is_aux_key (MoveUp b0 k1 b1) k) by (apply IHt1; assumption). inversion H6; try_all_key_positions.
    + assert(is_aux_key (Okay b0) k) by (apply IHt1; assumption); inversion H6; apply Node1_key_left; assumption.
    + assert(is_aux_key (MoveUp b0 k1 b1) k) by (apply IHt2; assumption). inversion H6; try_all_key_positions.
    + assert(is_aux_key (Okay b0) k) by (apply IHt2; assumption); inversion H6; apply Node1_key_right; assumption.
  * destruct_cond (x <? k0); [|destruct_cond (x <? k1)];
    [destruct_cond (insert_aux t1 x)|destruct_cond (insert_aux t2 x)|destruct_cond (insert_aux t3 x)];
    inversion H0.
    + apply Node2_key1; apply IHt1; inversion H5; [apply MoveUp_key2|apply MoveUp_key1|apply MoveUp_key3]; assumption.
    + apply Node2_key2.
    + inversion H5; try_all_key_positions.
    + inversion H2; try_all_key_positions. apply Node2_key1; apply IHt1; constructor; assumption.
    + inversion H5; try_all_key_positions. apply Node2_key3; apply IHt2; apply MoveUp_key1; assumption.
    + apply Node2_key3; apply IHt2; rewrite H1. apply MoveUp_key2.
    + inversion H5; try_all_key_positions. apply Node2_key3; apply IHt2; apply MoveUp_key3; assumption.
    + inversion H2; try_all_key_positions. apply Node2_key3; apply IHt2; constructor; assumption.
    + inversion H5; try_all_key_positions.
    + apply Node2_key4.
    + inversion H5; apply Node2_key5.
      - rewrite <- H9; apply IHt3; rewrite H9; apply MoveUp_key2.
      - apply IHt3; apply MoveUp_key1; assumption.
      - apply IHt3; apply MoveUp_key3; assumption.
    + inversion H2; try_all_key_positions. apply Node2_key5; apply IHt3; constructor; assumption.
  * destruct_cond (x <? k0); [|destruct_cond (x <? k1)];
    [destruct_cond (insert_aux t1 x)|destruct_cond (insert_aux t2 x)|destruct_cond (insert_aux t3 x)];
    inversion H0.
    all: try (constructor; destruct H0; try_all_key_positions; rewrite <- IHt1 in H3; inversion H3; try_all_key_positions; fail 1000).
    + assert(is_aux_key (MoveUp b0 k2 b1) k) by (apply IHt2; assumption). inversion H8;
      [apply MoveUp_key1|apply MoveUp_key2|apply MoveUp_key3]; try_all_key_positions.
    + constructor; destruct H0; try_all_key_positions; rewrite <- IHt2 in H3; inversion H3;try_all_key_positions.
    + assert(is_aux_key (MoveUp b0 k2 b1) k) by (apply IHt3; assumption). inversion H8; apply MoveUp_key3; try_all_key_positions.
    + constructor; destruct H0; try_all_key_positions; rewrite <- IHt3 in H3; inversion H3;try_all_key_positions.
Qed.

(* Utile dans la tactique d'après *)
Ltac invert_eq :=
  repeat progress (
    match goal with
    | H : true = _ |- _ => symmetry in H
    | H : false = _ |- _ => symmetry in H
    end
  ).

(* Disjonction de cas automatique x < y ou y < x *)
(* suppose que x <> y dans les hypothèses *)
(* Très utile pour traiter tous les cas de `insert_aux` correctement *)
Ltac destruct_lt x y :=
  let w := fresh "cond" in
  remember (x <? y) as w; destruct w; invert_eq;
  [assert (x < y) by (apply leb_complete; assumption)
  |assert (y < x) by (apply Nat.le_neq; split; [apply Nat.ltb_ge|symmetry]; assumption)]
      .

(* On donne une définition inductive de "ne pas être une clé" *)
(* pour simplifier le `inversion H` plus tard dans la preuve *)
Inductive neq: nat -> nat -> Prop :=
  | ZS_neq : forall n, neq 0 (S n)
  | SZ_neq : forall n, neq (S n) 0
  | SS_neq : forall n k, neq n k -> neq (S n) (S k).

Lemma neq_sym: forall n k, neq n k <-> neq k n.
Proof.
  split; intros; induction H; constructor; assumption.
Qed.

Lemma neq_irrefl: forall n, ~(neq n n).
Proof.
  intros; induction n; intro; inversion H.
  apply IHn; assumption.
Qed.

Lemma neq_correct: forall n k, neq n k <-> n <> k.
Proof.
  induction n; induction k; split; intros; try intro.
  - inversion H.
  - assert (0 = 0) by reflexivity; specialize (H H0); inversion H.
  - inversion H0.
  - constructor.
  - inversion H0.
  - constructor.
  - rewrite H0 in H. apply (neq_irrefl (S k)). assumption.
  - constructor. apply IHn. intro. rewrite H0 in H; apply H; reflexivity.
Qed.

Inductive is_not_key: key -> b -> Prop :=
  | Leaf1_not_key: forall k x, neq x k -> is_not_key x (Leaf1 k)
  | Leaf2_not_key: forall k k' x, neq x k -> neq x k' -> is_not_key x (Leaf2 k k')
  | Node1_not_key: forall k t t' x, neq x k -> is_not_key x t -> is_not_key x t' -> is_not_key x (Node1 t k t')
  | Node2_not_key: forall k k' t t' t'' x, neq x k -> neq x k' -> is_not_key x t -> is_not_key x t' -> is_not_key x t'' -> is_not_key x (Node2 t k t' k' t'')
  .

(* Preuve de la correction de `is_not_key` *)
Lemma is_not_key_correct: forall t x, is_not_key x t <-> ~(is_key x t).
Proof.
  unfold not.
  induction t; intros; split; intros.
  - inversion H0. inversion H. rewrite H3 in H5. apply (neq_irrefl k); assumption.
  - constructor; rewrite neq_correct; intro; rewrite H0 in H. apply H; constructor.
  - inversion H. inversion H0.
    + rewrite H8 in H4. apply (neq_irrefl k). assumption.
    + rewrite H9 in H5. apply (neq_irrefl k0). assumption.
  - constructor; apply neq_correct; intro; apply H; rewrite H0; constructor.
  - inversion H; inversion H0.
    + apply (neq_correct x k); assumption.
    + specialize (IHt1 x); apply IHt1; assumption.
    + specialize (IHt2 x); apply IHt2; assumption.
  - constructor.
    + apply neq_correct; intro. apply H; rewrite H0; apply Node1_key_middle.
    + apply IHt1; intro; apply H; apply Node1_key_left; assumption.
    + apply IHt2; intro; apply H; apply Node1_key_right; assumption.
  - inversion H; inversion H0.
    + specialize (IHt1 x); apply IHt1; assumption.
    + apply (neq_correct x k); assumption.
    + specialize (IHt2 x); apply IHt2; assumption.
    + apply (neq_correct x k0); assumption.
    + specialize (IHt3 x); apply IHt3; assumption.
  - constructor.
    + apply neq_correct; intro; apply H; rewrite H0; apply Node2_key2.
    + apply neq_correct; intro; apply H; rewrite H0; apply Node2_key4.
    + apply IHt1; intro; apply H; apply Node2_key1; assumption.
    + apply IHt2; intro; apply H; apply Node2_key3; assumption.
    + apply IHt3; intro; apply H; apply Node2_key5; assumption.
Qed.

(* 2nd lemme principal : on augmente la hauteur de 1 dans MoveUp, sinon conservée dans Okay *)
Lemma insert_depth_change: forall t x d, leaves_at_depth t d -> 
  (forall t', insert_aux t x = Okay t' -> leaves_at_depth t' d)
  /\ (forall k t' t'', insert_aux t x = MoveUp t' k t'' -> leaves_at_depth t' d /\ leaves_at_depth t'' d).
Proof.
  induction t; repeat (try intros; try split; try simpl).
  + inversion H. destruct_cond (x <? k); inversion H0; constructor.
  + destruct_cond (x <? k); inversion H0.
  + destruct_cond (x <? k); inversion H0.
  + destruct_cond (x <? k); [|destruct_cond (x <? k0)]; inversion H0.
  + destruct_cond (x <? k); [|destruct_cond (x <? k0)]; inversion H0; inversion H; constructor.
  + destruct_cond (x <? k); [|destruct_cond (x <? k0)]; inversion H0; inversion H; constructor.
  + destruct_cond (x <? k); [destruct_cond (insert_aux t1 x)| destruct_cond (insert_aux t2 x)];
    inversion H0; inversion H.
    - assert(leaves_at_depth b0 n /\ leaves_at_depth b1 n)
      by (specialize (IHt1 x n H6); destruct IHt1; apply (H9 k0); symmetry; assumption).
      destruct H8; constructor; assumption.
    - assert(leaves_at_depth b0 n)
      by (specialize (IHt1 x n H6); destruct IHt1; apply H8; symmetry; assumption).
      constructor; assumption.
    - assert(leaves_at_depth b0 n /\ leaves_at_depth b1 n)
      by (specialize (IHt2 x n H7); destruct IHt2; apply (H9 k0); symmetry; assumption).
      destruct H8; constructor; assumption.
    - assert(leaves_at_depth b0 n)
      by (specialize (IHt2 x n H7); destruct IHt2; apply H8; symmetry; assumption).
      constructor; assumption.
  + destruct_cond (x <? k); [destruct_cond (insert_aux t1 x)| destruct_cond (insert_aux t2 x)]; inversion H0.
  + destruct_cond (x <? k); [destruct_cond (insert_aux t1 x)| destruct_cond (insert_aux t2 x)]; inversion H0.
  + destruct_cond (x <? k); [|destruct_cond (x <? k0)];
    [destruct_cond (insert_aux t1 x)|destruct_cond (insert_aux t2 x)|destruct_cond (insert_aux t3 x)];
    inversion H0; inversion H; constructor; try assumption.
    * specialize (IHt1 x n H8); destruct IHt1 as [IHt1_okay IHt1_moveup]; apply IHt1_okay; symmetry; assumption.
    * specialize (IHt2 x n H9); destruct IHt2 as [IHt2_okay IHt2_moveup]; apply IHt2_okay; symmetry; assumption.
    * specialize (IHt3 x n H10); destruct IHt3 as [IHt3_okay IHt3_moveup]; apply IHt3_okay; symmetry; assumption.
  + destruct_cond (x <? k); [|destruct_cond (x <? k0)];
    [destruct_cond (insert_aux t1 x)|destruct_cond (insert_aux t2 x)|destruct_cond (insert_aux t3 x)];
    inversion H0; inversion H; constructor; try assumption.
    * specialize (IHt1 x n H10); destruct IHt1 as [IHt1_okay IHt1_moveup]; apply (IHt1_moveup k2 b0 b1); symmetry; assumption.
    * specialize (IHt1 x n H10); destruct IHt1 as [IHt1_okay IHt1_moveup]; apply (IHt1_moveup k2 b0 b1); symmetry; assumption.
    * specialize (IHt2 x n H11); destruct IHt2 as [IHt2_okay IHt2_moveup]; apply (IHt2_moveup k2 b0 b1); symmetry; assumption.
  + destruct_cond (x <? k); [|destruct_cond (x <? k0)];
    [destruct_cond (insert_aux t1 x)|destruct_cond (insert_aux t2 x)|destruct_cond (insert_aux t3 x)];
    inversion H0; inversion H; constructor; try assumption.
    * specialize (IHt2 x n H11); destruct IHt2 as [IHt2_okay IHt2_moveup]; apply (IHt2_moveup k2 b0 b1); symmetry; assumption.
    * specialize (IHt3 x n H12); destruct IHt3 as [IHt3_okay IHt3_moveup]; apply (IHt3_moveup k2 b0 b1); symmetry; assumption.
    * specialize (IHt3 x n H12); destruct IHt3 as [IHt3_okay IHt3_moveup]; apply (IHt3_moveup k2 b0 b1); symmetry; assumption.
Qed.

(* Tactique utile lorsque l'on a que t < k (où t est un arbre et k un entier) *)
(* et on veut montrer w < k pour w dans un sous-arbre obtenu après insertion dans t *)
Ltac ineq_solve t w x H H0 :=
  destruct (tiers_exclu w x) as [A|A]; [
    rewrite A; rewrite Nat.ltb_lt; assumption
  | apply H; rewrite all_keys_correct; destruct (insertion_keys t x w) as [B C];
    [symmetry; assumption|apply B]; rewrite <- H0;
    try(apply MoveUp_key1; assumption); try apply MoveUp_key2; try(apply MoveUp_key3; assumption)].

(* `insert_aux` donne bien un résultat correct *)
(* Beaucoup de cas à traiter mais des tactiques bien pensées pourrait probablement rassembler des cas similaires *)
Proposition insert_aux_correct: forall t x,is_not_key x t -> btree t ->
  (forall t', insert_aux t x = Okay t' -> btree t')
  /\ (forall t' k t'', insert_aux t x = MoveUp t' k t'' -> btree (Node1 t' k t'')).
Proof.
  intros t x Hkey H.
  induction H; split; simpl; inversion Hkey; rewrite neq_correct in *.
  + destruct_lt x x0; intros; inversion H3; constructor; assumption.
  + destruct_lt x x0; intros; inversion H3; constructor; assumption.
  + destruct_lt x x0; [|destruct_lt x y]; intros; [inversion H6|inversion H7|inversion H7].
  + destruct_lt x x0; [|destruct_lt x y]; intros; [inversion H6|inversion H7|inversion H7];
    apply (Node1_btree 0); try constructor; try assumption;
    try (rewrite <- H9 || rewrite <- H10); assumption.
  + destruct_lt x x0; [destruct_cond (insert_aux t x)| destruct_cond (insert_aux t' x)]; intros; inversion H13;
    specialize (IHbtree1 H10); specialize (IHbtree2 H11); destruct IHbtree1, IHbtree2.
    * assert(leaves_at_depth b0 k /\ leaves_at_depth b1 k)
      by (destruct (insert_depth_change t x k H3); apply (H20 k1); symmetry; assumption).
      destruct H19.
      assert(btree(Node1 b0 k1 b1)) by (specialize (H16 b0 k1 b1); apply H16; reflexivity).
      inversion H21.
      apply (Node2_btree k); try assumption.
      - destruct(insertion_key t x k1 b0 b1).
        ++ symmetry; assumption.
        ++ rewrite <- strict_max_correct, forall_correct in H1.
           assert(k1 <? x0 = true) by (apply H1; rewrite all_keys_correct; assumption).
           apply Nat.ltb_lt; assumption.
        ++ rewrite H31; assumption.
      - assert(k1 < x0).
        ** destruct(insertion_key t x k1 b0 b1).
          ++ symmetry; assumption.
          ++ rewrite <- strict_max_correct, forall_correct in H1.
             assert(k1 <? x0 = true) by (apply H1; rewrite all_keys_correct; assumption).
             apply Nat.ltb_lt; assumption.
          ++ rewrite H31; assumption.
        ** rewrite <- strict_max_correct, forall_correct; intros.
          destruct (tiers_exclu x3 x); rewrite all_keys_correct in H32.
          ++ rewrite H33; assumption.
          ++ assert(is_aux_key (insert_aux t x) x3) by (rewrite <- Heqcond0; apply MoveUp_key3; assumption).
             rewrite insertion_keys in H34;
             rewrite <- strict_max_correct, forall_correct in H1.
             apply H1; rewrite all_keys_correct; assumption.
             symmetry; assumption.
    * apply (Node1_btree k); try assumption.
      - apply H14; reflexivity.
      - rewrite <- strict_max_correct, forall_correct; intros.
        destruct (tiers_exclu x2 x); rewrite all_keys_correct in H19.
        ++ rewrite H20; assumption.
        ++ assert(is_aux_key (insert_aux t x) x2) by (rewrite <- Heqcond0; apply Okay_key; assumption).
           rewrite insertion_keys in H21;
           rewrite <- strict_max_correct, forall_correct in H1.
           apply H1; rewrite all_keys_correct; assumption.
           symmetry; assumption.
      - destruct (insert_depth_change t x k). assumption.
        apply H19.
        symmetry; assumption.
    * apply (Node2_btree k); try assumption;
      assert (W: btree (Node1 b0 k1 b1)) by (apply H18; reflexivity);
      inversion W; try assumption.
      - destruct(insertion_key t' x k1 b0 b1).
        ++ symmetry; assumption.
        ++ rewrite <- strict_min_correct, forall_correct in H2.
           rewrite <- Nat.ltb_lt.
           apply H2; rewrite all_keys_correct; assumption.
        ++ rewrite H28; assumption.
      - rewrite <- strict_min_correct, forall_correct; intros.
        rewrite all_keys_correct in H28.
        destruct (tiers_exclu x x3).
        ++ rewrite <- H29; rewrite Nat.ltb_lt; assumption.
        ++ assert(is_key x3 t').
           destruct (insertion_keys t' x x3).
           assumption.
           apply H30.
           rewrite <- Heqcond0; apply MoveUp_key1; assumption.
           rewrite <- strict_min_correct, forall_correct in H2.
           apply H2; rewrite all_keys_correct; assumption.
      - destruct (insert_depth_change t' x k). assumption.
        destruct (H29 k1 b0 b1); [symmetry|];assumption.
      - destruct (insert_depth_change t' x k). assumption.
        destruct (H29 k1 b0 b1); [symmetry|];assumption.
    * apply (Node1_btree k); try assumption.
      - apply H17; reflexivity.
      - rewrite <- strict_min_correct, forall_correct; intros.
        rewrite all_keys_correct in H19.
        destruct (tiers_exclu x x2).
        ++ rewrite <- H20; rewrite Nat.ltb_lt; assumption.
        ++ destruct (insertion_keys t' x x2). assumption.
           rewrite <- Heqcond0 in *.
           assert(is_key x2 t') by (apply H21; constructor; assumption).
           rewrite <- strict_min_correct, forall_correct in H2.
           apply H2; rewrite all_keys_correct; assumption.
      - destruct (insert_depth_change t' x k). assumption.
        apply H19; symmetry; assumption.
  + destruct_lt x x0; [destruct_cond (insert_aux t x)| destruct_cond (insert_aux t' x)]; intros; inversion H13.
  + intro. destruct_lt x x0; [|destruct_lt x y]; 
    [destruct_cond (insert_aux t x)|destruct_cond (insert_aux t' x)|destruct_cond (insert_aux t'' x)]; intro; inversion H22; try inversion H23.
    * apply (Node2_btree k); try assumption.
      - destruct IHbtree1. assumption. apply H23; reflexivity.
      - rewrite <- strict_max_correct, forall_correct; intros.
        rewrite all_keys_correct in *.
        destruct (tiers_exclu x2 x).
        ++ rewrite H25; assumption.
        ++ destruct (insertion_keys t x x2). symmetry; assumption.
           rewrite <- Heqcond0 in *.
           assert(is_key x2 t) by (apply H26; constructor; assumption).
           rewrite <- strict_max_correct, forall_correct in H3.
           apply H3; rewrite all_keys_correct; assumption.
      - destruct (insert_depth_change t x k). assumption.
        apply H23; symmetry; assumption.
    * apply (Node2_btree k); try assumption.
      - destruct IHbtree2. assumption.  apply H25; reflexivity.
      - rewrite <- strict_min_correct, forall_correct; intros.
        rewrite all_keys_correct in *.
        destruct (tiers_exclu x2 x).
        ++ rewrite H27; rewrite Nat.ltb_lt; assumption.
        ++ destruct (insertion_keys t' x x2). symmetry; assumption.
           rewrite <- Heqcond1 in *.
           assert(is_key x2 t') by (apply H28; constructor; assumption).
           rewrite <- strict_min_correct, forall_correct in H4.
           apply H4; rewrite all_keys_correct; assumption.
      - rewrite <- strict_max_correct, forall_correct; intros.
        rewrite all_keys_correct in *.
        destruct (tiers_exclu x2 x).
        ++ rewrite H27; assumption.
        ++ destruct (insertion_keys t' x x2). symmetry; assumption.
           rewrite <- Heqcond1 in *.
           assert(is_key x2 t') by (apply H28; constructor; assumption).
           rewrite <- strict_max_correct, forall_correct in H5.
           apply H5; rewrite all_keys_correct; assumption.
      - destruct (insert_depth_change t' x k). assumption.
        apply H25; symmetry; assumption.
    * apply (Node2_btree k); try assumption.
      - destruct IHbtree2. assumption.  apply H26; reflexivity.
      - rewrite <- strict_min_correct, forall_correct; intros.
        rewrite all_keys_correct in *.
        destruct (tiers_exclu x2 x).
        ++ rewrite H28; rewrite Nat.ltb_lt; assumption.
        ++ destruct (insertion_keys t' x x2). symmetry; assumption.
           rewrite <- Heqcond1 in *.
           assert(is_key x2 t') by (apply H29; constructor; assumption).
           rewrite <- strict_min_correct, forall_correct in H4.
           apply H4; rewrite all_keys_correct; assumption.
      - rewrite <- strict_max_correct, forall_correct; intros.
        rewrite all_keys_correct in *.
        destruct (tiers_exclu x2 x).
        ++ rewrite H28; assumption.
        ++ destruct (insertion_keys t' x x2). symmetry; assumption.
           rewrite <- Heqcond1 in *.
           assert(is_key x2 t') by (apply H29; constructor; assumption).
           rewrite <- strict_max_correct, forall_correct in H5.
           apply H5; rewrite all_keys_correct; assumption.
      - destruct (insert_depth_change t' x k). assumption.
        apply H26; symmetry; assumption.
    * apply (Node2_btree k); try assumption.
      - destruct IHbtree3. assumption. apply H25; reflexivity.
      - rewrite <- strict_min_correct, forall_correct; intros.
        rewrite all_keys_correct in *.
        destruct (tiers_exclu x2 x).
        ++ rewrite H27; rewrite Nat.ltb_lt; assumption.
        ++ destruct (insertion_keys t'' x x2). symmetry; assumption.
           rewrite <- Heqcond1 in *.
           assert(is_key x2 t'') by (apply H28; constructor; assumption).
           rewrite <- strict_min_correct, forall_correct in H6.
           apply H6; rewrite all_keys_correct; assumption.
      - destruct (insert_depth_change t'' x k). assumption.
        apply H25; symmetry; assumption.
    * apply (Node2_btree k); try assumption.
      - destruct IHbtree3. assumption. apply H26; reflexivity.
      - rewrite <- strict_min_correct, forall_correct; intros.
        rewrite all_keys_correct in *.
        destruct (tiers_exclu x2 x).
        ++ rewrite H28; rewrite Nat.ltb_lt; assumption.
        ++ destruct (insertion_keys t'' x x2). symmetry; assumption.
           rewrite <- Heqcond1 in *.
           assert(is_key x2 t'') by (apply H29; constructor; assumption).
           rewrite <- strict_min_correct, forall_correct in H6.
           apply H6; rewrite all_keys_correct; assumption.
      - destruct (insert_depth_change t'' x k). assumption.
        apply H26; symmetry; assumption.
  + intros. destruct_lt x x0; [|destruct_lt x y]; 
    [destruct_cond (insert_aux t x)|destruct_cond (insert_aux t' x)|destruct_cond (insert_aux t'' x)]; inversion H21; apply (Node1_btree (S k)); try constructor; try apply (Node1_btree k); try assumption.
    all: try(destruct IHbtree1; [assumption|]; assert(btree (Node1 b0 k2 b1)) by (apply H27; reflexivity); inversion H28).
    all: try(destruct IHbtree2; [assumption|]; assert(btree (Node1 b0 k2 b1)) by (apply H28; reflexivity); inversion H29).
    all: try(destruct IHbtree3; [assumption|]; assert(btree (Node1 b0 k2 b1)) by (apply H28; reflexivity); inversion H29).
    all: try(destruct (insert_depth_change t x k) as [D1 D2]; [|destruct (D2 k2 b0 b1); [symmetry|]]; assumption).
    all: try(destruct (insert_depth_change t' x k) as [D1 D2]; [|destruct (D2 k2 b0 b1); [symmetry|]]; assumption).
    all: try(destruct (insert_depth_change t'' x k) as [D1 D2]; [|destruct (D2 k2 b0 b1); [symmetry|]]; assumption).
    all: rewrite <- strict_max_correct, <- strict_min_correct, forall_correct in *.
    all: try intros w Hw; try rewrite all_keys_correct in *.
    all: try (assert (P: x0 = k1) by assumption; rewrite <- P).
    all: try (ineq_solve t w x H3 Heqcond0).
    all: try assumption.
    * destruct (tiers_exclu k2 x) as [A|A].
      - rewrite A; assumption.
      - rewrite <- Nat.ltb_lt; apply H3; rewrite all_keys_correct.
        destruct (insertion_keys t x k2) as [B C].
        symmetry; assumption.
        apply B; rewrite <- Heqcond0; apply MoveUp_key2.
    * apply H4; rewrite all_keys_correct; assumption.
    * rewrite Nat.ltb_lt; transitivity y. assumption. rewrite <- Nat.ltb_lt; apply H6; rewrite all_keys_correct; assumption.
    * ineq_solve t' w x H4 Heqcond1.
    * ineq_solve t' w x H5 Heqcond1.
    * rewrite <- H26; destruct (tiers_exclu k2 x) as [A|A].
      - rewrite A; assumption.
      - rewrite <- Nat.ltb_lt; apply H4; rewrite all_keys_correct.
        destruct (insertion_keys t' x k2) as [B C].
        symmetry; assumption.
        apply B; rewrite <- Heqcond1; apply MoveUp_key2.
    * rewrite <- H26; rewrite Nat.ltb_lt; transitivity x0; rewrite <- Nat.ltb_lt.
      - apply H3; rewrite all_keys_correct; assumption.
      - destruct (tiers_exclu x k2).
        ++ rewrite <- H51; apply Nat.ltb_lt; assumption.
        ++ destruct (insertion_keys t' x k2) as [B C]. assumption.
           assert(is_key k2 t') by (apply B; rewrite <- Heqcond1; apply MoveUp_key2).
           apply H4; rewrite all_keys_correct; assumption.
    * rewrite <- H26; apply H47; rewrite all_keys_correct; assumption.
    * unfold gt. destruct (tiers_exclu k2 x); rewrite <- H26.
      - rewrite H51; assumption.
      - destruct(insertion_keys t' x k2). symmetry; assumption.
        rewrite <- Nat.ltb_lt; apply H5; rewrite all_keys_correct; apply H52; rewrite <- Heqcond1; apply MoveUp_key2.
    * rewrite <- H26; apply H48; rewrite all_keys_correct; assumption.
    * rewrite Nat.ltb_lt; transitivity y.
      - rewrite <- H26. destruct (tiers_exclu x k2).
        ++ rewrite <- H51; assumption.
        ++ destruct(insertion_keys t' x k2). assumption.
           rewrite <- Nat.ltb_lt; apply H5; rewrite all_keys_correct; apply H52; rewrite <- Heqcond1; apply MoveUp_key2.
      - rewrite <- Nat.ltb_lt; apply H6; rewrite all_keys_correct; assumption.
    * rewrite <- H26; assumption.
    * rewrite <- H26; rewrite Nat.ltb_lt; transitivity x0.
      - rewrite <- Nat.ltb_lt; apply H3; rewrite all_keys_correct; assumption.
      - assumption.
    * rewrite <- H26; apply H5; rewrite all_keys_correct; assumption.
    * rewrite <- H26; unfold gt; destruct (tiers_exclu x k2).
      - rewrite <- H39; assumption.
      - rewrite <- Nat.ltb_lt; apply H6; rewrite all_keys_correct.
        destruct(insertion_keys t'' x k2). assumption. apply H40; rewrite <- Heqcond1; apply MoveUp_key2.
    * rewrite <- H26. ineq_solve t'' w x H6 Heqcond1.
    * rewrite <- H26. ineq_solve t'' w x H6 Heqcond1.
Qed.

(* Une fois x inséré dans t, (t+x) reste un B-arbre *)
Theorem insert_correct: forall t, btree t -> forall x, btree(insert t x).
Proof.
  intros; unfold insert.
  destruct_cond (mem t x); [assumption|destruct_cond (insert_aux t x)]; destruct (insert_aux_correct t x).
  1,4: rewrite is_not_key_correct; rewrite <- mem_correct_n; symmetry; assumption.
  1,3: try assumption.
  - apply H1; symmetry; assumption.
  - apply H0; symmetry; assumption.
Qed.
