Require Import ZArith_base.
Open Scope Z_scope.

Section Expressions_arithmétiques_simples.

  Inductive EA: Set :=
    | Cst : Z -> EA
    | Add : EA -> EA -> EA.

  Inductive EA_Big_step: EA -> Z -> Prop :=
    | EA_Big_step_k: forall k, EA_Big_step (Cst k) k
    | EA_Big_step_a: forall a1 a2 k1 k2, EA_Big_step a1 k1 -> EA_Big_step a2 k2 -> EA_Big_step (Add a1 a2) (k1 + k2).

  Inductive EA_Small_step: EA -> EA -> Prop :=
    | EA_Small_step_A: forall k1 k2, EA_Small_step (Add (Cst k1) (Cst k2)) (Cst (k1 + k2))
    | EA_Small_step_Cd: forall a1 a2 a2', EA_Small_step a2 a2' -> EA_Small_step (Add a1 a2) (Add a1 a2')
    | EA_Small_step_Cg: forall a1 k a1', EA_Small_step a1 a1' -> EA_Small_step (Add a1 (Cst k)) (Add a1' (Cst k)).

  (* RTC : Reflexive and transitive closure *)
  Inductive RTC {A: Type} (R: A -> A -> Prop): A -> A -> Prop :=
    | RTC_Refl: forall x, RTC R x x
    | RTC_Trans: forall y x z, R x y -> RTC R y z -> RTC R x z.

  Definition transitive {A: Type} (R : A -> A -> Prop): Prop :=
    forall y x z, R x y -> R y z -> R x z.

  Definition reflexive {A: Type} (R : A -> A -> Prop): Prop :=
    forall x, R x x.

  Lemma RTC_transitive {A: Type}: forall (R : A -> A -> Prop), transitive (RTC R).
  Proof.
    intro; set (R' := RTC R).
    assert(forall x y, R' x y -> forall z, R' y z -> R' x z).
    - intros x y H; induction H; intros.
      * assumption.
      * apply (RTC_Trans R y); [|apply IHRTC]; assumption.
    - unfold transitive; intros; apply (H x y); assumption.
  Qed.

  Lemma RTC_reflexive {A : Type}: forall (R: A -> A -> Prop), reflexive (RTC R).
  Proof.
    unfold reflexive; intros; constructor.
  Qed.

  Lemma RTC_imply {A : Type}: forall (R: A -> A -> Prop), forall x y, R x y -> RTC R x y.
  Proof.
    intros; apply (RTC_Trans R y); [assumption|constructor].
  Qed.

  
  Infix "-->" := EA_Small_step (at level 20).
  Infix "-->*" := (RTC EA_Small_step) (at level 20).
  Infix "⇓" := EA_Big_step (at level 20).

  Lemma EA_RTC_Small_steps_add: forall a2 a2', a2 -->* a2' -> forall a1, (Add a1 a2) -->* (Add a1 a2').
  Proof.
    intros a2 a2' H; induction H.
    - intro; apply RTC_reflexive.
    - intro. assert( (Add a1 x) --> (Add a1 y) ) by (constructor; assumption).
      apply (RTC_Trans EA_Small_step (Add a1 y)); [assumption|apply IHRTC].
  Qed.

  Lemma EA_RTC_Small_steps_add': forall a1 a1', a1 -->* a1' -> forall k, (Add a1 (Cst k)) -->* (Add a1' (Cst k)).
  Proof.
    intros a1 a1' H; induction H.
    - intro; apply RTC_reflexive.
    - intro. assert( (Add x (Cst k)) --> (Add y (Cst k)) ) by (constructor; assumption).
      apply (RTC_Trans EA_Small_step (Add y (Cst k))); [assumption|apply IHRTC].
  Qed.

  Proposition EA_Small_steps_implies_Big_steps: forall a k,
    a ⇓ k -> a -->* (Cst k).
  Proof.
    intros; induction H.
    - apply RTC_reflexive.
    - assert( (Add a1 a2) -->* (Add a1 (Cst k2))) by (apply EA_RTC_Small_steps_add; assumption).
      assert( (Add a1 (Cst k2)) -->* (Add (Cst k1) (Cst k2))) by (apply EA_RTC_Small_steps_add'; assumption).
      apply (RTC_transitive EA_Small_step (Add a1 (Cst k2)) (Add a1 a2) (Cst (k1 + k2))); try assumption.
      apply (RTC_transitive EA_Small_step (Add (Cst k1) (Cst k2)) (Add a1 (Cst k2)) (Cst (k1 + k2))); try assumption.
      apply RTC_imply; constructor.
  Qed.

  Proposition EA_Big_steps_implies_Small_steps: forall k a,
    (a -->* (Cst k)) -> (a ⇓ k).
  Proof.
    intro k; induction a; intro; inversion_clear H.
    - constructor.
    - inversion H0.
    - induction H0.
      + inversion_clear H1.
        * constructor; constructor.
        * inversion H.
      +
      
