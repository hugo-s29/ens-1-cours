Inductive nlist : Set :=
  | Nil
  | Cons (k: nat) (n: nlist).

Inductive triee : nlist -> Prop :=
  | t_nil : triee Nil
  | t_singl : forall k, triee (Cons k Nil)
  | t_cons : forall k n l, triee (Cons n l) -> le k n -> triee (Cons k (Cons n l)).

Lemma example_ind :
  forall l, triee l ->
  forall a  b, le a b ->
  triee (Cons a (Cons b l)).
Proof.
  intros l Hl.
  induction Hl.

  - intros a b H.
    apply t_cons.
    apply t_singl.
    exact H.

  - intros.
    apply t_cons.
    apply t_cons.
    apply t_singl.
    admit.
    assumption.

  - intros.
    admit.

Admitted.



Lemma tautologie :
  forall A : Prop, A -> A.
Proof.
  intros.
  exact H.
Qed.


Lemma modus_ponens : forall A B: Prop, A -> (A -> B) -> B.
Proof.
  intros.
  apply H0.
  exact H.
Qed.

Lemma ratage : forall A B: Prop, A -> B.
Proof.
  intros.
Abort.


Lemma permut_hyp : forall A B C: Prop,
  (A -> (B -> C)) -> (B -> (A -> C)).
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.

Check permut_hyp.

Lemma exemple : forall X Y: Prop,
  (X -> (Y -> Y)) -> (Y -> X -> Y).
Proof.
  intros X Y H.
  apply permut_hyp.
  trivial.
Qed.


Definition trois := S (S (S 0)).

Check trois.
Check modus_ponens.
Check exemple.

Fixpoint addition (n k: nat) :=
  match n with
  | 0 => k
  | S n' => S (addition n' k)
  end.

Check addition.

Definition tauto := fun (A : Prop) => fun (x: A) => x.
Check tauto.


Lemma triee_le : forall a b l, triee (Cons a (Cons b l)) -> a <= b.
Proof.
  intros.
  inversion H.
  trivial.
Qed.


Require Export Arith.

Lemma le_S_n : forall n k, le (S n) (S k) -> le n k.
Proof.
  intros n k H.
  inversion H.
  apply le_n.

  apply Nat.le_trans with (S n).

  - apply le_S. apply le_n.

  - exact H1.
Qed.


Lemma impossible_le : forall A : Prop, le (S 0) 0 -> A.
Proof.
  intros.
  inversion H.
Qed.



Check False.
Check false.
Check True.

Print True.
Print False.
Print false.

Lemma boom : forall P: Prop, False -> P.
Proof.
  intros.
  inversion H.
Qed.


Lemma double_neg : forall P: Prop, P -> not (not P).
Proof.
  intros.
  unfold not.
  intro H0.
  apply H0.
  trivial.
Qed.

Lemma contrap : forall A B: Prop, (A -> B) -> ~B -> ~A.
Proof.
  unfold not.
  intros.
  apply H0.
  apply H.
  exact H1.
Qed.

Lemma non_triee : ~(triee (Cons 3 (Cons 4 (Cons 1 Nil)))).
Proof.
  unfold not.
  intro Htriee.
  inversion Htriee.
  inversion H1.
  inversion H8.
  inversion H10.
Qed.

Lemma non_le : ~(3 <= 1).
Proof.
  intro Hle.
  inversion Hle.
  inversion H0.
Qed.


Lemma zero_left : forall n, 0 + n = n.
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

Lemma zero_right : forall n, n + 0 = n.
Proof.
  intro.
  induction n.
  - rewrite -> zero_left.
    reflexivity.

  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.


Lemma plus_comm : forall n m, n + m = m + n.
Proof.
  induction n.
  - intro.
    simpl.
    rewrite -> zero_right.
    reflexivity.

  - intro.
    simpl.
    rewrite IHn.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.


Lemma abc : forall a b c, a = b + c -> S a = b + S c.
Proof.
  intros.
  rewrite -> H.
  auto with arith.
Qed.

Lemma Sn_n : forall n k, S n = S k -> n = k.
Proof.
  intros n k HS.
  inversion HS.
  reflexivity.
Qed.

Lemma modus_ponens_et : forall A B: Prop, (A /\ (A -> B)) -> B.
Proof.
  intros.
  destruct H.
  apply H0.
  trivial.
Qed.

Lemma and_comm : forall A B: Prop, A /\ B -> B /\ A.
Proof.
  intros.
  destruct H.
  split; trivial. (* équivalent à split. trivial. trivial. *)
Qed.


Lemma uncurry_crry : forall A B C : Prop,
  ((A /\ B) -> C) -> (A -> B -> C).
Proof.
  intros A B C H HA HB.
  apply H.
  split; trivial.
Qed.

(* L'autre sens ? *)

Lemma disjonction : forall A B: Prop, A -> (A \/ B).
Proof.
  intros.
  left.
  trivial.
Qed.

Lemma zero_ou_succ : forall n,
  (n = 0 \/ n = S 0) \/ (exists k : nat, n = S (S k)).
Proof.
  intro.
  destruct n.
  - left. left. reflexivity.
  - destruct n.
    * left. right. reflexivity.
    * right. exists n. reflexivity.
Qed.

Require Export Nat.
Require Export Init.
Require Export Arith.

Goal forall a b: nat, max a b = max b a.
Proof.
  intros.
  Check Nat.lt_ge_cases.
  destruct (Nat.lt_ge_cases a b).

  admit.
  admit.

Admitted.



Lemma reciproquement : forall P: Prop, ~~P -> P. 
Proof.
  unfold not.
  intros.
Abort.


Lemma zero_pas_zero : forall n : nat, n = 0 \/ ~(n = 0).
Proof.
  intro n.
  destruct n.
  - left. reflexivity.
  - right. auto.
Qed.

Lemma tiers_exclu : forall P: Prop, P \/ ~P.
Proof.
  intro P. unfold not.
Abort.

(*
  En Rocq, le tiers exclu, c'est non.
*)
