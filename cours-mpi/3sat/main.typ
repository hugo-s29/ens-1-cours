#import "../../../global.typ": *

#show: it => setup-layout(it)
#let NP = math.bold("NP")

#title(with-bars: false)[*NP*-complétude de 3-sat]

Dans ce document, on démontrer la $NP$-complétude du problème de satisfiabilité d'une formule sous 3-CNF, noté #pbm[3-sat] :

#pb-display(name: pbm[3-sat])[
  Une formule $phi$ sous forme 3-CNF
][
  La formule $phi$ est-elle satisfiable ?
]

= Quelques rappels.

#let True  = math.sans(math.bold[V])
#let False = math.sans(math.bold[F])

On se fixe un ensemble fini de variables $cal(Q)$. On notera $BB = {True, False}$ l'ensemble des booléens.

== Valuations & satisfiabilité.

Une _valuation_ (ou un _environnent propositionnel_) est une fonction de la forme $rho : cal(Q) -> BB$.
À une variable, on assigne vrai ou faux.

Pour une formule logique $phi$, on associe $[|phi|] : BB^cal(Q) -> BB$ une _fonction booléenne_.
À une valuation, on associe donc vrai ou faux.

Une formule $phi$ est satisfiable si on peut l'interpréter à vrai, _i.e._ s'il existe une valuation $rho$ telle que $[|phi|](rho) = True$.

Attention, il ne faut pas confondre _satisfiable_ ($exists rho$) et _tautologique/valide_ ($forall rho$).

== Formes normales conjonctives.

Une formule sous $n$-CNF (_conjunctive normal form_), c'est une formule de la forme 
$ dots.c and underbrace((ell_1 or ell_2 or dots.c or ell_k), k <= n) and dots.c, $
où chaque $ell_i$ est un _littéral_ donc soit $p in cal(Q)$ soit $not p$ avec $p in cal(Q)$.

Le terme dans l'accolade est appelé _clause_.
La taille (_i.e._ le nombre de littéraux) de chacune des clauses est inférieure à $n$.

On n'a pas de contraintes sur le nombre de clauses (_i.e._ on peut avoir autant de $and$ que l'on veut).

Le problème #pbm[$n$-sat], c'est, dans chaque clause, choisir (au moins) un littéral pour le valuer à vrai.

== Le problème SAT.

Le problème
#pb-display(name: pbm[sat])[
  Une formule $phi$
][
  La formule $phi$ est-elle satisfiable ?
]
est $NP$-complet. C'est le théorème de _Cook-Levin_ et il est admis en MP2I/MPI.

Dans ce théorème, il n'y a pas de contrainte sur la forme de $phi$.

Pour résoudre ce problème, on applique l'algorithme de Quine.
C'est un algorithme force brute légèrement optimisé.

#algo(name: [Algorithme de Quine])[
  On choisit $x in "vars"(phi)$ (par contrainte ou au hasard).

  _Première tentative : $x <- True$_\
  On tente de résoudre $phi$ avec $x <- True$.\
  Si on réussit, on s'arrête : la formule est satisfiable.

  _Seconde tentative : $x <- False$_\
  On tente de résoudre $phi$ avec $x <- False$.\
  Si on réussit, on s'arrête : la formule est satisfiable.

  _Dernier cas_\
  Si les deux tentatives ont raté, la formule n'est pas satisfiable.
]

== Réductions polynomiales.

On notera $cal(E)_P$ l'ensemble des entrées d'un problème $P$.
On notera~$P^+$ l'ensemble des _instantes positives_ de $P$, c'est-à-dire les solutions du problème.

On dit qu'un problème $Q$ _se réduit à_ $P$ dès lors qu'il existe une fonction $f : cal(E)_Q -> cal(E)_P$ _calculable en temps polynomial_ telle que :
$ w in Q^+ <==> f(w) in P^+. $
On notera alors $Q <=_upright(p) P$.

#[
  #figure(
    cetz.canvas({
      import cetz.draw: *

      scale(0.5)
      set-style(stroke: (cap: "round", join: "round"))

      rect((0,0), (10, 5), fill: green.lighten(90%), stroke: (paint: green))
      rect((5.5,2), (8, 3), fill: blue.lighten(90%), stroke: (paint: blue))

      content((0.75,4.25), text(1.5em, green, $ Q $))
      content((6, 2.5), text(blue, $ P $))

      let incolor(it, color: red) = text(color, it)

      let inpurple = incolor.with(color: purple)
      let inblue = incolor.with(color: blue)
      let ingreen = incolor.with(color: green)

      content((-2, 2.5), $ w $)
      content((4.2, 1.8), $ inpurple(f)(w) $)
      content((9.5, 4), $ inpurple(f)(w) in inblue(P)^+ <==> w in ingreen(Q)^+ $)
      content((2, 2.5), pad(text(white, $ f $), x: 0.5em, y: 0.5em), frame: "circle", fill: purple, stroke: none)

      set-style(mark: (fill: black, stroke: (paint: black), size: 0.4))

      line((-1.5, 2.5), (0.8, 2.5), mark: (end: ">"))
      line((3.2, 2.5), (5.2, 2.5), mark: (end: ">"))
      line((8.3, 2.5), (12, 2.5), mark: (end: ">"))
    }),
  )
]

Lorsqu'on a $Q <=_upright(p) P$, il faut le comprendre par $Q$ est _plus simple à résoudre_ que $P$.

== Problèmes NP-difficiles.

Les problèmes $NP$-difficiles sont les problèmes plus compliqués à résoudre que tous les problèmes dans $NP$ (_i.e._ plus compliqués que tous les problèmes vérifiables en temps polynomial).

Un problème $P$ est $NP$-difficile si, quel que soit $Q in NP$, on a la réduction polynomiale $Q <=_upright(p) P$.

Pour démontrer qu'un problème $P$ est $NP$-difficile, il suffit de trouver un problème $Q$ $NP$-difficile tel que $Q <=_upright(p) P$.

S'il existe un problème $NP$-difficile plus simple que le problème $P$ alors $P$ est $NP$-difficile.

== NP-complétude ?

Un problème est $NP$-complet s'il est $NP$-difficile et qu'il est dans la classe $NP$.

Les problèmes $NP$-complets sont les problèmes les plus difficiles de la classe $NP$.

= Le problème 3-SAT.


Pour démontrer la $NP$-complétude de #pbm[3-sat], on a deux propriétés à démontrer : 
+ le problème #pbm[3-sat] est dans #NP (la partie simple) ;
+ le problème #pbm[3-sat] est $NP$-difficile (la partie complexe).

== 3-SAT est dans NP.

Là, c'est la partie simple : vérifier qu'une formule est satisfiable.
Pour cela, on a le droit à des données, un _certificat_.

Dans notre cas, on peut choisir comme certificat $rho$ une valuation.
Pour vérifier que $[|phi|](rho) = True$, il suffit de calculer $[|phi|](rho)$.

Cette vérification se réalise en temps polynomial (en temps linéaire, même).
D'où, #pbm[3-sat] est dans $NP$.

== 3-SAT est NP-difficile.

On procède par réduction au problème #pbm[sat].
Pour cela, on commence par se donner une formule $phi$ et on va construire une formule $psi$ sous 3-CNF telle que $phi$ est satisfiable si, et seulement si, $psi$ l'est.

La difficulté vient du fait que $phi$ n'a pas de contrainte sur sa forme.
Par exemple, si on suppose que $phi$ est sous CNF, alors il faut réussir à transformer une clause de taille inconnue en une 3-clause.

L'idée de cette preuve, est qu'on va s'intéresser aux sous-formules de la formule $phi$.
Pour cela, pour chaque sous-formule $theta.alt subset.eq phi$,#footnote[On utilise cette notation ensembliste, même si une formule n'est pas un ensemble.] on construit deux objets 
- une variable propositionnelle $x_theta.alt$ ;
- une formule $K_theta.alt$.

L'idée est qu'on *ne peut pas* inclure une sous-formule (qui est plus qu'un littéral) directement dans $K_phi$.
On veut se limiter à des formules simples, pour pouvoir construire simplement la 3-CNF.

Ainsi, à la place de sous-formules directement, on donne des relations sur les $x_theta.alt$ pour $theta.alt subset.eq phi$.

En ajoutant les $x_theta.alt$, on définit un nouvel ensemble de variable 
$ cal(Q)' = cal(Q) union { x_theta.alt | theta.alt subset.eq phi }. $

=== Définition des $K_theta.alt$ puis de $Omega$.

On définit :
- pour $theta.alt = p$ avec $p in cal(Q)$, on pose $K_theta.alt = p$ ;
- pour $theta.alt = top$, on pose $K_theta.alt = p or not p$ ;
- pour $theta.alt = bot$, on pose $K_theta.alt = p and not p$ ;
- pour $theta.alt = not gamma$, on pose $K_theta.alt = not x_gamma$ ;
- pour $theta.alt = gamma and delta$, on pose $K_theta.alt = x_delta and x_gamma$ ;
- pour $theta.alt = gamma or delta$, on pose $K_theta.alt = x_delta or x_gamma$ ;
- pour $theta.alt = gamma -> delta$, on pose $K_theta.alt = x_delta or not x_gamma$.

Tous les $K_theta.alt$ sont des 2-CNF.

Posons la formule $Omega$, une formule sous 3-CNF équivalente à $
  Omega equiv and.big_(theta.alt subset.eq phi) (K_theta.alt <-> x_theta.alt)
, $
où les $K_theta.alt$ ne sont pas des variables, mais bien des morceaux de formules.

Justifions de la bonne définition de $Omega$.
On commence par développer le $<->$ en deux implications, puis en une 2-CNF.
Ensuite, on remplace $K_theta.alt$ dans cette définition.
On n'est pas garanti d'obtenir une 3-CNF à ce point, car il peut y avoir des $and$ dans une des futures clauses.
Pour cela, on utilise les loi de De Morgan.

Cette formule permet de conserver la "structure" de la formule originelle $phi$.
En effet, si elle est vraie, c'est que toutes les variables~$x_theta.alt$ coordonnent avec les valuations de $K_theta.alt$.

#block(
  stroke: blue,
  radius: 10pt,
  inset: 0.6cm,
)[
  On définit la formule $psi = Omega and x_phi$.
  Cette formule est sous forme normale conjonctive et même 3-CNF.
  De plus, notre construction est polynomiale en la taille de $phi$.#footnote[
    Justifions... Il ne faut pas voir les sous-formules $theta.alt$ de $phi$ comme des sous-ensembles.
    On n'en a pas $2^(|phi|)$, mais bien un nombre polynomial (en réalité, c'est même linéaire en nombre d'opérateurs#footnote[
      En réalité, pour une formule $phi$ avec $n$ connecteurs d'arité 2, il y en a exactement $2 n + 1$. Ceci se montre très bien par induction sur une formule à $n$ connecteurs. 
    ]) en la taille de $phi$.
    Ceci justifie bien que notre construction est polynomiale.
  ]

  Il ne reste qu'une propriété à démontrer :
  $ phi "satisifiable" <==> psi "satisifiable", $
  ce que l'on fait par double-implication.
]

=== Premier sens de l'implication.

On veut montrer le sens "$==>$".
On suppose $phi$ satisfiable, et on montre que $psi$ satisfiable.

Soit $rho in BB^cal(Q)$ tel que $[|phi|](rho) = True$.

Là, c'est pas trop compliqué, il suffit de construire une valuation $mu$ sur $cal(Q)'$ telle que $[|psi|]^mu = True$.

On pose $
  mu : cal(Q') = cal(Q) union.sq (cal(Q') without cal(Q)) & --> BB\
  p in cal(Q) &arrow.bar.long rho(p)\
  x_theta.alt in cal(Q') without cal(Q) &arrow.bar.long [|theta.alt|](rho). $

On peut démontrer aisément#footnote[On procède par induction sur la formule $theta.alt$, et on procède cas par cas.
Par exemple, pour le cas $theta.alt = gamma and delta$ : $ [|K_(gamma and delta)|](mu) = [|x_gamma and x_delta|](mu) = [| x_gamma |](mu) dot [|x_delta|](mu) = [|gamma|](mu) dot [|delta|](mu) = [|gamma and delta|](mu). $] que l'on a, quelle que soit $theta.alt subset.eq phi$, on ait $[|K_theta.alt|](mu) = [|x_theta.alt|](mu)$.
Ceci est vrai par la définition de $mu$.

Par conjonction $and$ et équivalence $<->$, on en déduit que $[|psi|](mu) = True$.
En effet, l'égalité des valuations de $K_theta.alt$ et de $x_theta.alt$ donne que l'équivalence $K_theta.alt <-> x_theta.alt$ est valué à vrai.
Ceci étant vrai pour toute formule, on peut conclure.

Aussi, on a $[|x_phi|](mu) = [|phi|](mu) = [|phi|](rho) = True$.

#block(
  stroke: blue,
  radius: 10pt,
  inset: 0.6cm,
)[
  On en déduit que ma formule $psi$ est satisfiable si $phi$ l'est.
  À présent, montrons l'autre implication.
]

=== Deuxième sens de l'implication.

On veut montrer le sens "$<==$".

On va commencer par montrer : quelles que soient $rho$ et $mu$, si on a~$[|Omega|](mu) = True$ alors $mu(x_phi) = [|phi|](rho)$.
Ce qu'on démontre ici, c'est que $Omega$ assure la "structure" de $phi$.

Pour démontrer cela, on commence par montrer que, toujours en supposant $[|Omega|](mu) = True$, pour toute sous-formule $theta.alt subset.eq phi$, on a $mu(x_theta.alt) = [|theta.alt|](rho)$.
Ceci se démontre simplement par induction sur la sous-formule $theta.alt$.#footnote[
  Un exemple de cas : si $theta.alt = gamma and delta$ alors 
  $ mu(x_theta.alt) =_((star)) [|K_theta.alt|](mu) = [|x_gamma and x_delta|](mu) = mu(x_gamma) dot mu(x_delta) =_((star star)) [|gamma|](mu) dot [|delta|](mu) = [|gamma and delta|](mu). $
  L'égalité $(star)$ est vraie car $[|K_theta.alt <-> x_theta.alt|] = True$ par hypothèse.
  L'égalité $(star star)$ est vraie par hypothèse d'induction.
]
Le résultat sur $phi$ se conclut de cette généralisation.

On suppose $psi$ satisfiable, et on montre que $phi$ satisfiable.
Soit une valuation $mu in BB^cal(Q)'$ telle que $[|psi|](mu) = True$.

Ceci implique deux résultats : 
- $[|Omega|](mu) = True$, on peut donc appliquer les remarques précédentes ;
- et $[|phi|](mu) = True$.

Il suffit de poser $rho = mu|_cal(Q)'$ et on a bien que $[|phi|](rho) = True$.

#block(
  stroke: blue,
  radius: 10pt,
  inset: 0.6cm,
)[
  Ainsi, la formule $phi$ est satisfiable.
  Ceci conclut la preuve de l'équivalence, et donc la réduction.
]

= Conclusion.

L'idée de la preuve, c'est qu'on peut ajouter autant de $and$ et de variables que l'on veut.
La seule contrainte que l'on a dans une 3-CNF, c'est la taille d'une clause.

Cette preuve est au programme de MP2I/MPI et c'est parfois un thème qui tombe à l'oral.
