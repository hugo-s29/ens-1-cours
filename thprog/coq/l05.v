Require Import ZArith.


Inductive EA : Set :=
  | Cst : Z -> EA
  | Add : EA -> EA -> EA
  .

Inductive big_steps_EA : EA -> Z -> Prop :=
  | Cst_bs : forall k, big_steps_EA (Cst k) k
  | Add_bs : forall k1 k2 a1 a2, big_steps_EA a1 k1 -> big_steps_EA a2 k2 -> big_steps_EA (Add a1 a2) (k1 + k2)
  .


Example example1 : big_steps_EA (Add (Cst 3) (Add (Cst 2) (Cst 5))) 10.
Proof.
  apply (Add_bs 3 7).
  - apply Cst_bs.
  - apply (Add_bs 2 5).
    * apply Cst_bs.
    * apply Cst_bs.
Qed.


Inductive small_steps_EA : EA -> EA -> Prop :=
  | A_ss : forall k1 k2, small_steps_EA (Add (Cst k1) (Cst k2)) (Cst (k1 + k2))
  | Cd_ss : forall a2 a2' a1, small_steps_EA a2 a2' -> small_steps_EA (Add a1 a2) (Add a1 a2')
  | Cg_ss : forall a1 a1' k, small_steps_EA a1 a1' -> small_steps_EA (Add a1 (Cst k)) (Add a1' (Cst k))
  .

Inductive refl_and_transitive_closure (A : Type) (R : A -> A -> Prop) : A -> A -> Prop :=
  | Refl : forall a, refl_and_transitive_closure A R a a
  | Tran : forall a b c, R a b -> refl_and_transitive_closure A R b c -> refl_and_transitive_closure A R a c
  .

Lemma refl_and_transitive_closure_is_transitive : forall (A: Type) (R: A -> A -> Prop) x y z, 
  (refl_and_transitive_closure A R x y) ->
  (refl_and_transitive_closure A R y z) ->
  (refl_and_transitive_closure A R x z).
Proof.
  intros A R x y.
  assert (refl_and_transitive_closure A R x y ->
          forall z,
          refl_and_transitive_closure A R y z ->
          refl_and_transitive_closure A R x z).
  - intro H. induction H; intros.
    * exact H.
    * apply (Tran A R a b z).
      + exact H.
      + exact (IHrefl_and_transitive_closure z H1).
  - intros.
    exact (H H0 z H1).
Qed.

Definition small_steps_EA_RTC: EA -> EA -> Prop :=
  refl_and_transitive_closure EA small_steps_EA.

Infix "-->" := small_steps_EA (at level 20).
Infix "-->*" := small_steps_EA_RTC (at level 20).
Infix "⇓" := big_steps_EA (at level 20).


(* RTC = Reflexive and Transitive Closure *)
Lemma small_steps_EA_rtc_add_left : forall a2 a2', 
  a2 -->* a2' -> forall a1, (Add a1 a2) -->* (Add a1 a2').
Proof.
  intros a2 a2' H.
  induction H.
  - intro a1. exact (Refl EA small_steps_EA (Add a1 a)).
  - intro a1. apply (Tran EA small_steps_EA (Add a1 a) (Add a1 b)).
    + apply Cd_ss. exact H.
    + exact (IHrefl_and_transitive_closure a1).
Qed.


Lemma small_steps_EA_rtc_add_right : forall a1 a1', 
  a1 -->* a1' -> forall k, (Add a1 (Cst k)) -->* (Add a1' (Cst k)).
Proof.
  intros a1 a1' H.
  induction H; intro a1.
  - apply Refl.
  - apply (Tran EA small_steps_EA (Add a (Cst a1)) (Add b (Cst a1))).
    + apply Cg_ss. exact H.
    + apply (IHrefl_and_transitive_closure a1).
Qed.

Proposition big_implies_small_EA : forall a k,
  a ⇓ k -> a -->* (Cst k).
Proof.
  intros a k H.
  induction H.
  - apply Refl.
  - apply (refl_and_transitive_closure_is_transitive EA small_steps_EA (Add a1 a2) (Add a1 (Cst k2))).
    + apply small_steps_EA_rtc_add_left. exact IHbig_steps_EA2.
    + apply (refl_and_transitive_closure_is_transitive EA small_steps_EA (Add a1 (Cst k2)) (Add (Cst k1) (Cst k2))).
      * apply small_steps_EA_rtc_add_right. exact IHbig_steps_EA1.
      * apply (Tran EA small_steps_EA (Add (Cst k1) (Cst k2)) (Cst (k1 + k2))).
        -- apply A_ss.
        -- apply Refl.
Qed.

Infix "-->" := small_steps_EA_RTC (at level 20).
Ltac test1 := split; intro H.

Lemma test : forall n k, n = k <-> S n = S k.
Proof.
  intros n k.
  split; intro H; try (rewrite H + inversion H); reflexivity.
Qed.


Example test2 : forall (n : nat), n = n.
Proof.
  intro n.
  test1.
Qed.


Proposition small_implies_big_EA : forall a k,
  small_steps_EA_RTC a (Cst k) -> big_steps_EA a k.
Proof.
  intros a k H.
