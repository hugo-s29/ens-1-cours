(*** TP5 : induction bien fondée ***)


(*** Partie 2 : Bonne fondation,
                accessibilité,
                définition de fonctions ***)

(* Nous allons travailler ici sur les relations bien fondées *)
Print well_founded.

(* En Coq, une relation de A*A est bien fondée si tous les éléments de
A sont accessibles pour cette relation *)

Print Acc.

(* Un élément est dit accessible si tous ses prédécesseurs sont
accessibles

   Notez que la définition d'Acc est similaire au PIBF.  Cependant,
par rapport au cours, la relation considérée est la relation
réciproque.  C'est-à-dire que la relation (nat, >) est terminante,
mais pour Coq, c'est < qui est bien-fondée. *)

(* Remarque : on peut avoir l'impression ici qu'il n'y a pas de cas de
base, et que donc Acc est toujours vide, mais il faut remarquer qu'un
élément minimal pour R satisfait toujours Acc_intro. *)

(* Pour résumer, une relation "R" est bien fondée, pour cette
définition Coq de bonne fondation, quand tous les élements sont
atteignables à partir des éléments minimaux, de façon inductive. *)

(* Pour commencer, montrez que la relation < est bien fondée *)

(* Indice : La preuve suivante est valide: *)
Lemma trivialité : forall x y, S x <= y -> x < y.
Proof.
  intros. apply H.
Qed.

Require Import Lia.

Theorem well_founded_lt : well_founded lt.
Proof.
  assert (forall n m, m < n -> Acc lt m).
  - induction n; induction m; intro.
    1,2:inversion H.
    * constructor; intros; inversion H0.
    * constructor; intros; apply IHn.
      unfold lt in *.
      assert (S m <= n) by lia.
      transitivity (S m); assumption.
  - constructor; apply H.
Qed.


(** Accessibilité et divergence **)
Require Import Lists.Streams.

(* Le type des listes infinies -- **uniquement** infinies : pas de
constructeur Nil. *)
Print Stream.

(* On souhaite donner la définition usuelle de relation bien fondée :
"il n'existe pas de chaine infinie décroissante".  Pour faire ça, il
faut d'abord définir la notion de chaine infinie décroissante en Coq,
et surprise, on a besoin de coinduction pour ça. *)

CoInductive infiniteDecreasingChain
  A (R : A -> A -> Prop) : Stream A -> Prop :=
| ChainCons : forall x y s, infiniteDecreasingChain A R (Cons y s) (* Si on a une chaine infinie décroissante
                                                                 de la forme y::s, avec s infinie
                                                                 décroissante *)
                       -> R y x (* Si en plus on sait que x est plus grand que y *)
                       -> infiniteDecreasingChain A R (Cons x (Cons y s)). (* Alors x::y::s est aussi une chaine
                                                                              infinie décroissante *)

(* Définissez maintenant une notion alternative de "être bien fondée"
en utilisant les chaines *)
Definition wf2 A (R : A -> A -> Prop) :=
  forall s, ~infiniteDecreasingChain A R s.


(* Maintenant, prouvez que si un élément est accessible, il ne peux
pas commencer de chaine infinie décroissante *)

Lemma noBadChains : forall A (R : A -> A -> Prop) x, Acc R x
  -> forall s, ~infiniteDecreasingChain A R (Cons x s).
Proof.
  intro; intro; intro; intro.
  induction H.
  intro; destruct s; intro.
  inversion_clear H1.
  assert (~infiniteDecreasingChain A R (Cons a s)) by (apply H0; assumption).
  apply H1; assumption.
Qed.

(* Prouvez maintenant le lemme suivant *)
Lemma well_founded_bad_chains :
  forall A (R: A -> A -> Prop), well_founded R -> wf2 A R.
Proof.
  intros; intro.
  unfold well_founded in H.
  destruct s.
  apply noBadChains.
  apply H.
Qed.


(** Donner des arguments de terminaison à Coq **)

Require Import ZArith.
Require Import Recdef.
Require Import List.
Import ListNotations.

(* Dans Coq, toutes les fonctions que vous donnez doivent
terminer. Sur des fonctions récursives simples, Coq va trouver
automatiquement qu'elles terminent en cherchant un objet qui décroit
strictement à chaque appel récursif. Cependant, Coq n'arrive parfois
pas à inférer ce qui décroit strictement, et il faut l'aider. *)

(* Essayez d'écrire une fonction "merge", qui prend en entrée deux
listes d'entiers triées et retourne la liste triée correspondant à la
fusion de ces deux listes. Vous pouvez utiliser la fonction "leb". *)
Check leb.


(*
Fixpoint merge_fail1 (p: list nat) (q: list nat) : list nat :=
  match (p, q) with
  | ([], q) => q
  | (p, []) => p
  | (x::p, y::q) =>
      if x <=? y then
        x :: (merge_fail1 p (y :: q))
      else
        y :: (merge_fail1 (x :: p) q)
  end.
*)

(* Essayons également en utilisant la forme non curryfiée... *)

(*

Fixpoint merge_fail2 (p:list nat * list nat) : list nat :=
  match p with
  | ([], l) => l
  | (l, []) => l
  | (x::l, y::l') =>
      if x <=? y then
        x :: (merge_fail2 (l, y::l'))
      else
        y :: (merge_fail2 (x::l, l'))
  end.

*)

(* Coq devrait vous donner une erreur dans les deux cas. On va alors
l'aider à comprendre pourquoi cette fonction termine. *)

(* Trouvez une fonction:

   mesure : (list nat * list nat) → nat

telle que "mesure" décroit strictement dans les appels récursifs de merge. *)

Definition mesure (p : list nat * list nat) :=
  match p with
  | (a,b) => length a + length b
  end.


(* On va maintenant pouvoir définir la fonction merge. On utilise
alors une autre syntaxe :

   [Function ... ]
     généralise Fixpoint en autorisant à faire autre chose qu'une
     récurrence sur la structure du premier argument de la fonction,
     on peut donc lui donner explicitement la mesure qui va décroitre.

   Coq va alors nous demander de prouver que cette mesure décroit
effectivement Allez-y, definissez merge et prouvez que "mesure"
décroit.  *)
Function merge (p:list nat * list nat) { measure mesure p } : list nat :=
  match p with
  | ([], l) => l
  | (l, []) => l
  | (x::l, y::l') =>
      if x <=? y then
        x :: (merge (l, y::l'))
      else
        y :: (merge (x::l, l'))
  end.
Proof.
  all: intros; simpl in *.
  * lia.
  * lia.
Defined.


(** Retour aux relations bien fondées **)

(*Donnez la définition de l'ordre lexicographique sur le type
bool*nat, en prenant false est plus petit que true *)
Inductive lexico : bool*nat -> bool*nat -> Prop :=
  | lexico_true : forall n n', n < n' -> lexico (true, n) (true, n')
  | lexico_false : forall n n', n < n' -> lexico (false, n) (false, n')
  | lexico_b : forall n n', lexico (false, n) (true, n').

(* Prouvez ensuite que cet ordre est bien fondé. *)



Theorem well_founded_lex : well_founded lexico.
Proof.
  assert (forall a b n m, lexico (a,n) (b,m) -> Acc lexico (b,m)).
  - intros; inversion_clear H; constructor; intros.
    + 
Qed.


Theorem well_founded_lt : well_founded lt.
Proof.
  assert (forall n m, m < n -> Acc lt m).
  - induction n; induction m; intro.
    1,2:inversion H.
    * constructor; intros; inversion H0.
    * constructor; intros; apply IHn.
      unfold lt in *.
      assert (S m <= n) by lia.
      transitivity (S m); assumption.
  - constructor; apply H.
Qed.
