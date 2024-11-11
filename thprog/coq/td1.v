Inductive le : nat -> nat -> Prop :=
  | le_refl : forall n, le n n
  | le_S : forall n k, le n k -> le (S n) (S k).


Lemma le_transitive :
  forall b c,
  le b c -> (forall a, le a b -> le a c).
Proof.
  auto.
Qed.
