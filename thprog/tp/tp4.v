(*** TP5 : Coinduction et induction bien fondée ***)

(* TD Women : Lison Blondeau-Patissier / Emma Nardino *)

(* =================================================================== *)

(*** Partie 0 : TD ***)

(* Ce TD-TP commence par une partie "TD" : référez-vous au document
correspondant avant de vous lancer dans la partie en Coq.
Il s'agit de traiter l'exercice 1 du sujet de TD. *)

(* =================================================================== *)

(*** Partie 1 : Divergence et coinduction ***)

(* Rappels de certaines tactiques de Coq :

   [constructor.]
     Permet d'utiliser directement le constructeur d'une définition
     inductive sans redonner son nom (Coq le cherchera de lui même).

   [apply H with v.]
     Parfois, en utilisant la tactique [apply] en Coq, vous aurez le
     message d'erreur suivant: "Error: Unable to find an instance for
     the variable x.".
     Dans ce cas là, Coq n'arrive pas à deviner tout seul quel choix
     il doit faire pour la variable x de la proposition H. En utilisant
     [apply H with v], vous pouvez indiquer à Coq qu'il faut prendre
     "v" comme valeur pour la variable "x".

   [assumption.]
     Si vous devez prouver "H" et que "H" est en hypothèse, assumption
     termine automatiquement la preuve.

   [inversion H.]
     Demande à Coq de trouver les conditions nécéssaires pour que
     l'hypothèse H soit vraie. Dans le cas ou H est fausse, inversion
     termine directement la preuve.

   [unfold f.]
     Lorsque "f" est une définition, unfold permet de remplacer le nom
     "f" par sa définition. La variante [unfold f in H] permet de
     remplacer "f" par sa définition dans l'hypothèse H.

   [simpl.]
     Demande à Coq de simplifier le but, en appliquant des fonctions
     par exemple.

   [destruct a.]
     Quand "a" est un objet défini par une définition inductive,
     "destruct a" permet de traiter les différents cas possibles de
     la définition.

   [subst.]
     Lorsque vous utilisez cette tactique, Coq simplifie vos hypothèses
     en utilisant des substitutions intelligentes, par exemple "a = b",
     "b = c", "c = d", et "a + b = c + d" seront remplacés par
     "d + d = d + d".
     Très pratique lorsque vous avez utilisé la tactique [inversion]
     juste avant, qui introduit souvent des noms de variables pas très
     utiles.

*)


(* En cours, vous avez vu il y a quelque temps la version duale de
Kanster-Tarski, où l'on prend un plus grand post-point fixe au lieu du
plus petit pré-point fixe: toute fonction monotone sur un treillis
complet admet un plus grand point fixe, qui est le plus grand
post-point fixe (un post-point fixe de f est un x tel que x <= f(x) ).

   On parle alors de définition coinductive. Cette notion a été
illustrée en définissant la relation de divergence sur IMP, qui est
une relation unaire sur les commandes IMP.

   Le principe de preuve correspondant, dit de "preuve par
coinduction" dit que pour montrer qu'un élément est en-dessous (pour
la relation d'ordre) du plus grand point fixe, il suffit de montrer
que c'est un post-point fixe. *)

(* Dans le contexte des relations coinductives, où la relation d'ordre
est l'inclusion, cela se reformule de la manière suivante: pour
montrer qu'un ensemble est inclus dans le grand point fixe, on montre
que c'est un post-point fixe.

   On va illustrer ce principe en Coq, pour cela on va travailler sur
la divergence dans un graphe orienté infini. Le graphe que l'on
considère est le suivant :

   Ensemble des sommets :

     { a ; b ; c ; d } ∪ { p n | n ∈ ℕ}

   Arêtes :

     { (a,b) ; (b,c) ; (b,d) ; (d,b) ; (c,p 0) }
     ∪
     { (p n,p (n+1)) | n ∈ ℕ }

   Tout d'abord, formalisez ce graphe en Coq. *)

Inductive state : Set :=
  | a : state
  | b : state
  | c : state
  | d : state
  | p : nat -> state.

Inductive step : state -> state -> Prop :=
  | ab : step a b
  | bc : step b c
  | bd : step b d
  | db : step d b
  | cp0 : step c (p 0)
  | pp1 : forall n, step (p n) (p (n+1)).


(* On définit la divergence comme un prédicat "coinductif" : on
applique le théorème de Knaster-Tarski, pour raisonner sur le plus
grand post-point fixe d'un opérateur f. On rappelle qu'un post-point
fixe pour f est un ensemble X tel que X ⊆ f(X).

   Pour rappel, l'utilisation "classique" de Knaster-Tarski consiste à
travailler sur le plus petit point fixe, qui est un ensemble X tel que
f(X) ⊆ X. *)

CoInductive diverges : state -> Prop :=
| div : forall s1 s2, step s1 s2 -> diverges s2 -> diverges s1.

(* Tout d'abord, des questions sur Knaster-Tarski:

1] Quelle est la définition de l'opérateur f correspondant à la
   définition de "diverges" ci-dessus ?

  f(A) = { s₁ | ∃ s₂ ∈ A, step s₁ s₂}

2] Que donnerait cette définition si on remplaçait "CoInductive" par
   "Inductive" ?
  
  On aurait diverges = ∅ par manque de cas de base.
*)

(* On veut d'abord montrer qu'il existe une divergence à partir de a,
en suivant la boucle b ⟳ d. Essayez de prouver ce lemme en utilisant
les tactiques que vous connaissez en Coq. Quel est le problème ? *)

Lemma div_abd_fail : diverges a.
Proof.
  (* [...] *)
Abort.

(* Pour résoudre ce problème, il vous faudra utiliser la "tactique
miraculeuse" [cofix.] ou [cofix H.], dont vous pourrez découvrir l'effet.

   L'idée de "cofix" est d'ajouter en hypothèse le but que vous
souhaitez prouvez... Mais ne croyez pas trop aux miracles : [cofix.]
suivi de [assumption.] engendrera une erreur au moment de sauvegarder
la preuve avec [Qed.] (ce que vous êtes invité.e.s à vérifier): il
faut faire au moins un tour de boucle !*)

Lemma div_abd : diverges a.
Proof.
  apply div with b. constructor.
  cofix H.
  apply div with d. constructor.
  apply div with b. constructor.
  assumption.
Qed.

(* Vous pouvez ensuite inspecter la preuve qui a été engendrée *)
Print div_abd.


(** Principe de preuve par coinduction **)

(* Un ensemble d'états est représenté par une fonction
   [g : state → bool]
correspondant à sa fonction indicatrice.  On définit un prédicat sur
les ensembles d'états, pour dire qu'un tel ensemble est un post-point
fixe (pour la fonction f donnée plus haut) *)

(* Donnez cette définition (il s'agit de ne pas utiliser "diverges"). *)
Definition post_fixpoint (g : state -> bool) : Prop :=
  forall x, g x = true -> exists y, step x y /\ g y = true.


(* Le théorème suivant exprime le principe de preuve par coinduction :
tout post-point fixe de notre opérateur est inclus dans le plus grand
post-point fixe.

   Prouvez-le, en ayant à l'esprit qu'il faudra utiliser un cofix
quelque part. *)

Theorem coinduction :
  forall g : state -> bool,
    post_fixpoint g ->
    forall s, g s = true -> diverges s.
Proof.
  intros g H.
  unfold post_fixpoint in H.
  cofix H''; intros s H'.
  specialize (H s H').
  destruct H; destruct H.
  apply div with x; [|apply H'']; assumption.
Qed.

(* On souhaite maintenant prouver que tous les sommets de la forme
(p n) sont aussi divergents. Pourquoi la preuve précédente avec la
boucle b ⟳ d pour a ne peut-elle pas marcher ? *)

(* Bah, `b` et `d` ne sont pas de la forme `p _`, donc difficile *)

(* Il faut donc utiliser plus en détail le principe de preuve par
coinduction, et notamment s'aider de post-point fixes. *)

(* Pour commencer, définissez l'ensemble gp des sommets de la forme
"p n". *)

Definition gp (s : state) : bool :=
  match s with
  | p _ => true
  | _ => false
  end.

(* Prouvez maintenant le lemme suivant *)

(* Si vous voulez, vous pouvez essayer ici la notation ";" de Coq:
lorsque vous lancez une preuve avec différents cas, le ";" permet
d'appliquer les même tactiques à tous les (sous-)cas sans faire de
copier/coller. Vous pouvez alors utiliser "try" pour essayer
d'appliquer une tactique sans que Coq ne s'arrête s'il n'y arrive pas.
   Observez par exemple la preuve suivante : *)

Lemma example_step : forall s, s = a \/ s = d -> step s b.
Proof.
  intro s.
  destruct s; intros; destruct H; try constructor; try inversion H.
Qed.

(* Tous les cas ont été traités d'un coup, on commence par un "intros",
on fait une analyse de cas sur le "ou", puis si il y a un step vers b
("try constructor") on le fait, sinon c'est qu'on n'est ni a ni d,
donc "try inversion H" doit finir la preuve.

   Comprendre cette syntaxe n'est pas obligatoire, mais elle peut
parfois accélerer les preuves, ce qui peut vous être utile. Vous
pouvez trouver plus d'infos en ligne si vous le voulez. *)

Lemma inv_gp : forall s, gp s = true -> exists n, s = p n.
Proof.
  intros.
  destruct s; try discriminate.
  exists n; reflexivity.
Qed.

(* Vous pouvez maintenant prouver la divergence des "p n" en vous
aidant du théoreme de coinduction.

   Vous aurez sûrement besoin des détails suivant sur "destruct":

   [destruct f.]
     si "f" est le nom d'un lemme f : A -> B, "destruct f" vous permet
     de récuperer "B" dans vos hypothèses, mais Coq vous demandera de
     prouver également "A". C'est utile pour utiliser un lemme que
     vous avez prouvé précedemment mais pour lequel vous ne pouvez pas
     utiliser directement [apply].

   Remarque : comme dans [apply with ...], on peut aussi utiliser :

   [destruct with ...]
     quand Coq n'arrive pas à deviner tout seul la valeur de certaines
     variables.

   On cherchera à passer par le lemme coinduction ci-dessus. Une preuve
plus directe passant par [cofix.] existe aussi. *)

Lemma post_fixpoint_gp : post_fixpoint gp.
Proof.
  unfold post_fixpoint; intros.
  assert (H' := inv_gp x H); destruct H'; subst.
  exists (p (x0 + 1)); split; [constructor|reflexivity].
Qed.

Lemma div_p : forall n, diverges (p n).
Proof.
  intro n.
  destruct coinduction with gp (p n).
  - apply post_fixpoint_gp.
  - reflexivity.
  - apply div with s2; assumption.
Qed.
