
(* Chargées de TD : Lison Blondeau-Patissier / Emma Nardino *)

(* Notes :
   - si au bout d'une heure votre TP-woman oublie de le dire, passez à la partie sur les listes !!
   - si vous n'aviez pas fini le TP1 finissez au moins la partie sur les listes ! *)

(*** Logique "avancée" et Rocq : négation, booléens et Prop ***)

(** Négation **)

(* On peut voir le faux, noté False, comme un connecteur logique, qui
peut être inséré dans le "tableau" où figuraient la conjonction et
l'existentielle dans l'énoncé du TP 1 :

    connecteur    | pour utiliser |  pour construire
  ----------------|---------------|---------------------
      P /\ Q      |  destruct H.  |  split.
      P \/ Q      |  destruct H.  |  left. / right.
  exists x:nat, P |  destruct H.  |  exists 17.
      False       |  destruct H.  |

Devinez :
- pourquoi il n'y a pas de tactique correspondant à "False" dans la colonne "pour construire"
de ce tableau.
- ce que fait "destruct H." si H est une hypothèse qui dit False. *)

(* A vous de jouer : prouvez les lemmes suivants *)

Lemma ex_falso: forall P : Prop, False -> P.
Proof.
  intros.
  destruct H.
Qed.

(* Si l'on a A:Prop, alors ~A, la négation de A, est une notation pour "A -> False". *)
(* Si la notation vous perturbe, vous pouvez toujours utiliser la tactique [unfold not.] *)

Lemma not_not : forall P : Prop, P -> ~~P.
Proof.
  intros. unfold not. intros.
  apply H0. exact H.
Qed.

Lemma morgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros P Q H H'.
  destruct H'.
  destruct H; apply H; assumption.
Qed.

Lemma morgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros P Q H H'.
  destruct H.
  destruct H'.
  - apply H. exact H1.
  - apply H0. exact H1.
Qed.

(* Pour la prochaine preuve, vous aurez besoin d'une nouvelle tactique :
   [inversion H.]
     Formellement, lorsque l'on appelle [inversion H], Rocq essaye de
     trouver les conditions nécessaires pour que l'hypothèse H soit vérifiée.
     Rocq fait aussi quelques simplifications lorsque l'on utilise inversion : si H est fausse, alors
     il termine automatiquement la preuve, si H implique une égalité entre 2 expressions, il fait
     parfois automatiquement le remplacement.

   Essayez cette tactique sur les prochains lemmes pour comprendre comment elle marche en pratique  *)

Lemma zero_un : ~(0=1).
Proof.
  intro H.
  inversion H.
Qed.
(*Notez que "x <> y" est un raccourci de "x = y -> False".*)

(* Un autre exemple d'application de la tactique inversion, indépendamment de la négation *)
Lemma S_out :  forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

(* Dans le même style, les différents constructeurs d'un type inductif ne peuvent pas renvoyer
la même valeur.
   Considérons la tentative suivante de définition des entiers avec le successeur
   ET le prédécesseur. *)
Inductive t : Set :=
  Ze : t | Pr : t -> t | Su : t -> t.

Lemma S_et_P : forall x y, Su x = Pr y -> False.
Proof.
  intros x y H.
  inversion H.
Qed.

(** Food for thought : à méditer après ce TP, ou si par hasard vous avez fini
le reste avant la fin. Avec la syntaxe au-dessus, il est évident que le
"prédécesseur" du "successeur" de "zéro" et "zéro" ne définissent pas le même
 objet: *)

Lemma PSZ: Pr (Su Ze) = Ze -> False.
Proof.
  intros H.
  inversion H.
Qed.

Require Export ZArith.
Require Export Lia.

(** Sauriez-vous montrer la même chose en remplaçant "zéro" par un x (de type t)
quelconque ?
On insiste sur le fait que cette question est plutôt pour emmener à la maison
que pour pendant le TP. Nous serons par ailleurs ravi.es de recevoir des mails
ou des messages discord si vous avez des questions là-dessus.
Un indice : souvenez-vous de vos cours de maths, où vous avez sûrement été déjà
amené.es à prouver des résultats plus forts et plus généraux pour parvenir à
vos fins.
Si besoin, vous pourrez vous servir de la tactique [lia] (chargée avec la
librairie Lia au-dessus), pour résoudre des buts arithmétiques (notamment
obtenir faux à partir d'une hypothèse évidemment fausse comme x < x ou 2 < 0),
et vous pouvez aussi invoquer la tactique [Search bla] pour chercher des lemmes
contenant "bla", comme dans: *)

Search "<" "S".

Lemma inj_P: forall x y, Pr x = Pr y -> x = y.
Proof.
  intros x y H.
  inversion H.
  reflexivity.
Qed.

Lemma inj_S: forall x y, Su x = Su y -> x = y.
Proof.
  intros x y H.
  inversion H.
  reflexivity.
Qed.

Lemma diff_PS: forall x y, Pr x <> Su y.
Proof.
  intros x y H.
  inversion H.
Qed.


Lemma inj_PS_SP: forall x, Pr (Su x) <> x /\ Su (Pr x) <> x.
Proof.
  intros x.
  induction x; split; intro H; inversion H; destruct IHx.
  - apply H2. exact H1.
  - apply H0. exact H1.
Qed.

Lemma inj_PS: forall x, Pr (Su x) <> x.
Proof.
  intros x.
  apply inj_PS_SP.
Qed.


(*** Prédicats inductifs, listes et relations ***)

Require Import List.

(* On va définir des prédicats sur des listes. Pour simplifier, on
supposera qu'il s'agit de listes d'entiers.*)
Definition listn := list nat.

(* Inspirez vous de ce que vous avez vu en cours pour écrire le
prédicat inductif (is_size l n) qui signifie que l est de taille n *)
Inductive is_size : listn -> nat -> Prop :=
  | Zero : is_size nil 0
  | Cons : forall n l, is_size l n -> is_size l (S n)
  .

(* La tactique [inversion H] ne sert pas que dans les égalités, en
fait, elle fonctionne aussi sur tous les prédicats inductifs. Elle va
vérifier quels cas sont possibles. Cela se voit dans le lemme suivant:
*)
Lemma non_empty_size : forall p l n, is_size (p::l) n -> n <> 0.
Proof.
  intros p l n H H'.
  inversion H.
  assert (S n0 <> 0).
  - intro. inversion H3.
  - apply H3. rewrite H2. exact H'.
Qed.

(* Définissez un prédicat (mem l x) qui signifie que x ∈ l *)
Inductive mem : listn -> nat -> Prop :=
  | Found : forall k l, mem (cons k l) k
  | Next : forall x k l, mem l k -> mem (cons x l) k.

(* Le prédicat (update l x y l') signifie que l' est obtenu en
   remplaçant la première occurence de x dans l par y. *)

(* On vous donne un des cas :

  ──────────────────────────────── head
  update (x::l) x y (y::l)

*)

(* Ecrivez ce prédicat *)
Inductive update : listn -> nat -> nat -> listn -> Prop :=
  | U1 : forall x y z l l', update l x y l' -> z <> x -> update (z :: l) x y (z :: l')
  | U2 : forall x y l l', update (x :: l) x y (y :: l').

(* Pour montrer une cohérence entre les deux prédicats, prouvez le
lemme suivant *)
Lemma update_mem : forall l x y l', update l x y l' -> mem l x.
Proof.
  intros.
  induction H.
  - apply Next. exact IHupdate.
  - apply Found.
Qed.

(* On pourrait prouver de manière similaire "forall l' l x y, update l
x y l' -> mem l' y." *)

(* Petit bonus *)
(* Pour prouver une implication dans l'autre sens, vous pourrez avoir
besoin du lemme suivant.

   Notez que lorsque l'on veut utiliser une hypothèse [H] du type
"forall x ...", il arrive que Rocq n'arrive pas à inférer la valeur de
x. On peut alors utiliser la syntaxe [destruct (H n)] et Rocq
détruira l'hypothèse en prenant x=n : l'application instancie un [∀]. *)

Lemma inj_Succ : forall n m, S n = S m -> n = m.
Proof.
  intros.
  inversion H. 
  reflexivity.
Qed.


Lemma diff_eq : forall n, n <> S n.
Proof.
  induction n.
  - intro H. inversion H.
  - intro H. apply IHn. apply (inj_Succ). exact H.
Qed.

Lemma eq_dec : forall n m : nat, n = m \/ n <> m.
Proof.
  induction n; induction m.
  - left. reflexivity.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - destruct IHm.
    * right. rewrite H. apply diff_eq.
    * destruct (IHn m).
      + left. rewrite H0. reflexivity.
      + right. intro H'. apply H0. exact (inj_Succ n m H').
Qed.
(*
  intro n.
  induction n.
  - intro m. destruct m.
    * left. reflexivity.
    * right. intro H. inversion H.
  - intro m. destruct (IHn m).
    * rewrite H. right. exact (diff_eq m).
    * destruct (IHn (S m)).
*)

Lemma mem_update : forall l x, mem l x -> forall y, exists l', update l x y l'.
Proof.
  intros l x H.
  induction H.
  - intro y. exists (y :: l). apply U2.
  - intro y. destruct (eq_dec x k); destruct (IHmem y).
    * exists (y :: x0). rewrite H0. apply U2.
    * exists (x :: x0). apply U1; assumption.
Qed.

(* P.S : Si vous avez réussi à le prouver sans utiliser le lemme
au-dessus, votre définition de mem aurait probablement pu être plus
simple. *)

(* Fin du petit bonus *)

(* On considère les listes et on définit une relation binaire
inductive sur les listes. On note "perm l1 l2" cette relation, avec
l'idée que "perm l1 l2" représente le fait que l2 est une permutation
de l1.

   Cette définition inductive est donnée par les quatres règles
d'inférence suivantes :
                                       perm l₁ l₂      perm l₂ l₃
  ───────────── (refl)               ──────────────────────────── (trans)
    perm l l                                   perm l₁ l₃


        perm l₁ l₂
────────────────────── (tail)          ────────────────────────── (head)
  perm (x::l₁) (x::l₂)                  perm (x::y::l) (y::x::l)
*)

Inductive perm : listn -> listn -> Prop :=
  | refl : forall l, perm l l
  | trans : forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3
  | tail : forall x l1 l2, perm l1 l2 -> perm (x :: l1) (x :: l2)
  | head : forall x y l, perm (x :: y :: l) (y :: x :: l).

(* Petit bonus *)
(* Vous vous êtes peut être demandé pourquoi est-ce que l'on a pris cette règle-là pour head et pas une autre ?
  Notamment, on aurait pu penser à prendre cette règle-ci :

           perm l₁ l₂
   ─────────────────────────────(head')
     perm (x::y::l₁) (y::x::l₂)

On peut cependant prouver que l'on a pas besoin de cette règle.
Pour vous aider à comprendre pourquoi, montrez d'abord l'exemple suivant. *)

Lemma perm_example : perm (1::2::4::5::3::nil) (2::1::4::3::5::nil).
Proof.
  apply (trans (1::2::4::5::3::nil) (1::2::4::3::5::nil) (2::1::4::3::5::nil)).
  - apply tail. apply tail. apply tail. apply head.
  - apply head.
Qed.

(* Prouvez maintenant le lemme suivant, montrant que la règle donnée
 précédemment est vraie dans notre définition. *)

Lemma perm_head_alt : forall x y l1 l2, perm l1 l2 -> perm (x::y::l1) (y::x::l2).
Proof.
  intros x y l1 l2 H.
  induction H.
  - apply head.
  - apply (trans (x::y::l1) (y::x::l2)).
    * exact IHperm1.
    * apply (trans (y::x::l2) (x::y::l2)).
      + apply head.
      + exact IHperm2.
  - apply (trans (x::y::x0::l1) (y::x::x0::l1)).
    * apply head.
    * apply tail. apply tail. apply tail. exact H.
  - apply (trans (x::y::x0::y0::l) (y::x::y0::x0::l)).
    * apply (trans (x::y::x0::y0::l) (x::y::y0::x0::l)).
      + apply tail. apply tail. apply head.
      + apply head.
    * apply refl.
Qed.

(* Fin du petit bonus *)
