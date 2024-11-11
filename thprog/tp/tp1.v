(*** TP1 : Introduction à Rocq : formules, entiers et listes ***)

(* TDs : Lison Blondeau-Patissier / Emma Nardino

   Adresse email des TDwomen : [Prenom].[Nom]@ens-lyon.fr


----------- A METTRE A JOUR POUR VSCODE,

Lancez vscodium.
Ouvrez le fichier TP1.v, un coq sur fond de coucher de soleil devrait apparaître à côté du nom de fichier.




 RACCOURCIS CLAVIER POUR VSCOQ PAR DEFAUT :
 <Alt-↑> := [Step Backward]
 <Alt-↓> := [Step Forward]
 <Alt-→> := [Interpret to Point]

 pour ajouter un raccourci clavier :
 . clic droit dans un fichier .v > choisir "Command Palette"
   OU <Ctrl-Shift-p>
 . taper "Coq:<la commande qu'on veut>" dans le dialogue qui s'ouvre
 . éditer
 *)

(* Ci-dessous, du code Rocq à lire et compléter. N'hésitez pas, si vous
jugez cela nécessaire, à commencer par rejouer les preuves Rocq vues en
cours (le code est disponible depuis la page www du cours). N'hésitez pas également
à demander de l'aide à votre chargée de TP. *)

(*** Logique Simple ***)

(* Les deux tactiques centrales de Rocq sont :

   [intro]
     L'équivalent de "soit x" et de "supposons que..."  dans les maths
     informelles, [intro] introduit un nouvel objet (entité sur
     laquelle on raisonne, ou hypothèse) dans le contexte.
     On peut nommer l'objet que l'on introduit, avec [intro x] ou
     [intro H], par exemple.
     La variante [intros] fait [intro] autant que possible, en
     choisissant (plus ou moins arbitrairement) des noms pour les
     hypothèses ainsi créées.

   [apply H]
     Permet d'invoquer l'hypothèse nommée H. *)

Lemma trivial1 : forall P : Prop, P -> P.
Proof.
  intro P. intro H. exact H.
Qed.

(* À vous de jouer maintenant !
Prouvez les lemmes suivants en utilisant uniquement intro et apply*)

Lemma trivial2 : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
  intro P.
  intro Q.
  intro Himp.
  exact Himp.
Qed.

(* [intros H1 H2 H3] est un raccourci pour [intro H1. intro H2. intro H3.]. *)
(*   Vous pouvez maintenant l'utiliser. *)

Lemma trivial3 : forall P Q R : Prop,
    (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros P Q R Himp2 Himp1 HP.
  apply Himp2.
  - exact HP.
  - apply Himp1. exact HP.
Qed.

(* Une dernière chose à propose de apply. Observez la preuve suivante,
que vous pourriez avoir écrite sans difficulté. *)

Lemma trivial4: forall P, (forall x, P x) -> P 2.
Proof.
  intros P H.
  apply H.
Qed.

(* À la deuxième ligne, on a appliqué l'hypothèse (H: forall x, P x)
pour en déduire (P 2), qui ne coïncide pourtant pas avec l'hypothèse.
En réalité, ce que Rocq a fait pour vous, c'est qu'il a deviné que vous
vouliez appliquer l'hypothèse H dans le cas particulier où x vaut 2.
C'est à dire: *)

Lemma trivial4': forall P, (forall x, P x) -> P 2.
Proof.
  intros P H.
  Check (H 2).  (* Check n'est pas une tactique ; ça ne fait pas
                   avancer la preuve. C'est une commande de Rocq *)
  apply (H 2).
Qed.

(* Autrement dit, on peut (et même parfois on doit) préciser les arguments
d'une hypothèse quand on l'applique.

Après avoir médité sur cette idée, prouvez le lemme suivant: *)
Lemma apply1: forall (P : nat -> Prop), (forall x y, P x -> P y) -> P 2 -> P 3.
Proof.
  intros P H1 H2.
  apply (H1 2 3).
  exact H2.
Qed.


(* Pour chaque connecteur logique, Rocq fournit une tactique pour l'utiliser
quand il est en hypothèse et une tactique pour le "construire" quand
il est en but. Voici ce qui a été vu en cours pour la conjonction et
l'existentielle :

    connecteur    | pour utiliser |  pour construire
  ----------------|---------------|---------------------
      P /\ Q      |  destruct H.  |  split.
  exists x:nat, P |  destruct H.  |  exists 17.
 *)

(* La disjonction est notée \/ en Rocq.
Pour prouver un but de la forme A \/ B, on dispose des deux tactiques "left." et "right.".
Devinez ce qui se passe lorsque l'on a une hypothèse de la forme "H : A\/B"
dans le but courant, et que l'on fait [destruct H].
Vérifiez que vous avez deviné juste en prouvant les lemmes suivants. *)

Lemma conj1: forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H.
  exact H.
Qed.

Lemma conj2: forall P Q : Prop, P -> Q -> P /\ Q.
Proof.
  intros P Q H1 H2.
  split; assumption.
Qed.

Lemma or1 : forall P Q : Prop, P -> P \/ Q.
Proof.
  intros.
  left. assumption.
Qed.

Lemma or2 : forall P Q R : Prop,
    P \/ Q -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros.
  destruct H.
  - apply H0. assumption.
  - apply H1. assumption.
Qed.

(* Prouvez maintenant le lemme suivant.
   Vous aurez besoin pour cela des tactiques suivantes pour travailler sur les expressions entières :

   [reflexivity]
     Permet de prouver un but de la forme "a = a". Cette tactique peut aussi s'utiliser pour
     d'autres relations reflexive.

   [simpl]
     Permet de simplifier une expression dans le but. On verra plus formellement plus tard
     comment ça marche, mais pour l'instant vous pouvez voir ça comme une tactique permettant
     de réécrire par exemple "2*2" en "4".
 *)

Lemma echauffement_or : forall x, (x=2 \/ x=4) -> exists y, x=2*y /\ (y=1 \/ y=2).
Proof.
  intros x H.
  destruct H.
  - exists 1. split; simpl.
    * assumption.
    * left. reflexivity.
  - exists 2. split; simpl.
    * assumption.
    * right. reflexivity.
Qed.

(* Retour sur la curryfication *)
(* Devinez l'énoncé du lemme suivant, et prouvez-le *)
Lemma curry3 : forall A B C D, ((A/\B/\C) -> D) -> A -> B -> C -> D.
Proof.
  intros A B C D H HA HB HC.
  apply H.
  split.
  assumption.
  split; assumption.
Qed.


(*** Arithmétique Simple sur les Entiers ***)

(* Définissez la fonction prédecesseur [pred] : *)

Definition pred (n : nat) : nat :=
  match n with
   | 0 => 0
   | (S n) => n
  end.


(* Inspirez-vous de la définition de [plusnat] (vue en cours)
   pour définir la soustraction sur les naturels, qui satisfera la
   propriété n-(n+k)=0 *)


Fixpoint minus (n m:nat) : nat :=
  match m with
  | 0 => n
  | (S m') => minus (pred n) m'
  end.

(* Prouvez le lemme suivant. Vous aurez besoin de la tactique
    suivante:
   [destruct n] Permet de séparer une preuve sur n en
    deux : d'abord le cas "n = 0", puis le cas "n = S n0". *)

Lemma minus_zero : forall n, minus n 0 = n.
Proof.
  intro n.
  destruct n; simpl; reflexivity.
Qed.

(* Vous aurez besoin de la tactique suivante pour le prochain lemme :

   [induction n]
     Permet de faire une preuve par récurrence sur l'entier n (ou une
     induction sur n).  Il vous faudra alors, comme en maths, prouver
     le cas "n=0" puis le cas "S n" en supposant la propriété vraie
     pour n *)

(* Formellement, le principe d'induction est résumé par la formule suivante en Rocq : *)
Check nat_ind.

(* Notez la différence avec le raisonnement par cas. *)
Check nat_case.

(* Indice supplémentaire : Maintenant que vous avez prouvé le lemme
"minus_zero", vous pouvez maintenant écrire [apply minus_zero] pour
utiliser ce lemme. *)

Lemma plus_minus : forall n k, (minus (n + k) n) = k.
Proof.
  intros n k.
  induction n.
  - simpl. reflexivity.
  - simpl. assumption.
Qed.


(*** Fonctions sur les listes ***)

(* Une "incantation" pour avoir accès à la bibliothèque Rocq traitant des listes *)
Require Export List.

(* Rocq connaît les listes polymorphes : les "listes de A", pour un type A quelconque
  (liste de naturels, de booléens, de listes de naturels, de fonctions de type nat -> nat, ..) *)
Print list.

(* Pour faciliter les choses, on va fixer ici un type de listes *)
Parameter A : Set.

(* Ainsi, quand vous déclarez un type de listes, utilisez "list A" *)

(* Définissez une fonction "rev" qui renvoie le retournement de son argument,
en utilisant la fonction "++" qui permet de concatener deux listes,
puis prouvez que c'est une involution, en s'aidant de ces lemmes intermédiaires. *)

Fixpoint rev l : list A :=
  match l with
  | nil => nil
  | (cons x l') => (rev l') ++ (cons x nil)
  end.

(* Encore une fois, on peut utiliser le principe d'induction sur les listes [induction l] *)
Check list_ind.

(* On vous donne également quelques lemmes intérmédiaires en Rocq *)
Check app_nil_r.
Check app_assoc.

(* Prouvez maintenant les lemmes suivants. Vous aurez besoin encore d'une nouvelle tactique :

   [rewrite H]
     Si H est une hypothèse de la forme "a = b", [rewrite H] remplace dans le but toutes les
     occurences de "a" par "b".

   Inversement, nous avons aussi:

   [rewrite <- H]
     Si H est une hypothèse de la forme "a = b", [rewrite <- H] remplace dans le but toutes les
     occurences de "b" par "a". *)

Lemma rev_concat : forall xs ys, rev (xs ++ ys) = rev ys ++ rev xs.
Proof.
  intros xs ys.
  induction xs.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite app_assoc. rewrite IHxs. reflexivity.
Qed.

(* Un lemme technique qui intervient dans la preuve du lemme qui suit *)
Lemma rev_singleton : forall xs x, rev (xs ++ (x :: nil)) = x :: rev xs.
Proof.
  intros xs x.
  rewrite rev_concat.
  simpl. reflexivity.
Qed.

Lemma rev_involution : forall l, rev (rev l) = l.
Proof.
  intro l.
  induction l; simpl.
  - reflexivity.
  - rewrite rev_singleton. rewrite IHl. reflexivity.
Qed.

(* Ce n'est pas très économique de retourner des listes en appelant à
chaque fois "++". Trouver une meilleure definition de [revopt], vérifier
avec une chargée de TD, puis prouver l'équivalence des deux. *)

Fixpoint revopt2 (l: list A) (l': list A): list A :=
  match l with
  | nil      => l'
  | cons x l'' => revopt2 l'' (cons x l')
  end.

Definition revopt (l: list A): list A :=
  revopt2 l nil.


(* N'hésitez pas à prouver des lemmes intérmédiaires, surtout si vous utilisez des
fonctions auxiliaires... Par ailleurs, quand [simpl.] n'arrive pas à simplifier une
expression contenant une fonction auxiliaire [f_aux], vous pouvez utiliser [unfold f_aux.]
pour forcer Rocq à développer la définition de [f_aux]. *)

Lemma revopt2_correct : forall l l', revopt2 l l' = (rev l) ++ l'.
Proof.
  intros l.
  induction l; simpl.
  - reflexivity.
  - intro l'. rewrite (IHl (a::l')). rewrite <- app_assoc. simpl. reflexivity.
Qed.


Lemma revopt_correct : forall l, revopt l = rev l.
Proof.
  intro l.
  unfold revopt.
  rewrite (revopt2_correct l nil).
  rewrite app_nil_r.
  reflexivity.
Qed.



(* Utiliser List.fold_left pour donner une définition alternative de la fonction qui
calcule la longueur d'une liste. Ensuite vérifiez que ces définitions coïncident. *)
Check List.fold_left.

Definition fold_length (l : list A) : nat :=
  List.fold_left (fun x _ => S x) l 0.


Lemma fold_length_start_at_n : forall (l: list A) n, 
  List.fold_left (fun x _ => S x) l n = n + (length l).
Proof.
  intro l.
  induction l.
  - simpl. trivial.
  - simpl. intro. rewrite (IHl (S n)). simpl. auto.
Qed.

Lemma fold_length_correct : forall l, fold_length l = length l.
Proof.
  intro l.
  unfold fold_length.
  rewrite (fold_length_start_at_n l 0).
  reflexivity.
Qed.

(* Définissez une fonction perms : nat -> list (list nat) telle que
  perms k renvoie la liste de toutes les permutations de la liste
  [0;..;k]
  Prouvez ensuite des tas de propriétés intéressantes de perms.
 Par exemple, que toutes les sous-listes de [perms k] sont de taille
  [k+1], ou encore que l'ensemble des permutations de taile [k] est de
  taille factorielle [k].
 Bonne Chance ! *)

Fixpoint place_k_at_n_in_list (l: list nat) (k: nat) (n: nat): list nat :=
  match (l, n) with
  | (   nil, _  ) => k :: nil
  | (     l, 0  ) => k :: l
  | (x :: l, S n) => x :: (place_k_at_n_in_list l k n)
  end.

Check List.fold_left.

Fixpoint all_placements_of_k (l: list nat) (k: nat) : list (list nat) :=
  match l with
  | nil => (k::nil)::nil
  | x :: xs =>
      (k :: x :: xs) :: (map (fun l' => x :: l') (all_placements_of_k xs k))
  end.

Definition generate_all_placements (l: list nat) (k: nat) : list (list nat) :=
  all_placements_of_k l k.


Fixpoint perms (n: nat): list (list nat) :=
  match n with
  |     0  => (0 :: nil) :: nil
  | (S n') => List.fold_left (
      fun acc p => acc ++ (generate_all_placements p n)
    ) (perms n') nil
  end.

Lemma generate_all_placements_not_empty : forall k l, generate_all_placements l k <> nil.
Proof.
  intros.
  unfold generate_all_placements.
  unfold all_placements_of_k.
  induction l.
  - discriminate.
  - discriminate.
Qed.

Fixpoint all_size (ll : list (list nat)) (k: nat) :=
  match ll with
  |nil => True
  |a::rr => (length(a) = k) /\ (all_size rr k)
  end.

Lemma generate_all_placements : forall l n k, all_size l n -> all_size (generate_all_placements l k) (S n).

Lemma perms_sublists_S_k : forall k, all_size (perms k) (S k).
Proof.
  induction k.
  - simpl. split; reflexivity.
  - unfold all_size. unfold fold_left.
