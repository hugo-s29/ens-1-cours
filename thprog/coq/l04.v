Lemma dec_eq: forall n k: nat, n = k \/ n <> k.
Proof.
  induction n; intros.
  - destruct k.
    * left. trivial.
    * right. auto.
  - destruct k.
    * right. auto.
    * destruct (IHn k).
      + left. rewrite H. reflexivity.
      + right. auto.
Qed.
