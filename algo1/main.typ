#import "../global.typ": *

#show: it => setup-layout(it)

#title[Algorithmique]

Cours donné par Stephan #smallcaps[Thomassé] (Bureau dans l'aile Sud--Ouest).

*Qu'est ce qu'il y aura à l'exam ?* (MCC = Modalité de Contrôle de Connaissances) :
$ "2 devoirs" + "1 partiel" + "1 exam". $

*_Office hour(s)_ :* Lundi 15h30 -- 16h30

= Pré-introduction.

*Qu'est ce que l'algorithmique ?*
C'est résoudre des problèmes efficacement.
L'algorithmique, c'est le côté _clair_ de l'informatique.
On manipule des "bornes $sup$".

Le côté _sombre_, c'est la complexité, l'étude des classes de complexité (comme $bold(upright(P))$ et $bold("NP")$ par exemple).
Ici, on cherche à montrer que résoudre efficacement n'est pas possible.
On manipule des "bornes $inf$".

Dans ce cours, on se place à la bordure entre ces deux côtés.

== Problèmes.

Après les soutenances de stage de l'année dernière, le constat est simple : il est important de respecter une structure, où l'on donne
- nom du problème,
- entrée du problème et la taille de l'entrée,
- sortie du problème.

Par exemple, pour un entier $n$, la taille est de $log_2 n$ en le représentant en binaire.

La sortie, elle peut être de trois types :
- un mot sur un alphabet $cal(A)$, c'est un problème de *_construction_* ;
- un entier, c'est un problème d'*_optimisation_* ;
- un booléen, c'est un problème de *_décision_*.

Ces trois types ne sont pas les mêmes. Pour cela, on étudie le problème du "Voyageur de commerce" (noté _TSP_ par la suite).
Le but de ce problème est de se déplacer en un certain nombre de villes le plus rapidement possible.

En version constructif :

#pb-display(name: pbm[TSP_Constructif])[
  Un graphe $G = (V, E)$ et une fonction~$ell : E -> NN$ la longueur d'une arête.
][
  Un cycle qui passe une fois exactement par chaque sommet en minimisant la longueur totale, et #sc[Faux] sinon.
]


En version optimisation :

#pb-display(name: pbm[TSP_Optimisation])[
  Un graphe $G = (V, E)$ et une fonction~$ell : E -> NN$ la longueur d'une arête.
][
  La longueur minimale d'un cycle qui passe une fois exactement par chaque sommet, et $oo$ si un tel cycle n'existe pas.
]

En version décision :

#pb-display(name: pbm[TSP_Décision])[
  Un graphe $G = (V, E)$, une fonction~$ell : E -> NN$ la longueur d'une arête et un entier $t$.
][
  #sc[Vrai] s'il un cycle qui passe une fois exactement par chaque sommet de longueur inférieure ou égale à $t$ (et #sc[Faux] sinon).
]


On note $"Pb"_1 <= "Pb"_2$ si $"Pb"_1$ se réduit polynomialement à $"Pb"_2$.
Clairement, on a la chaîne de réductions : $ #pbm[TSP_Décision] <= #pbm[TSP_Optimisation] <= #pbm[TSP_Construction]. $

#proposition[
  On a $#pbm[TSP_Optimisation] <= #pbm[TSP_Décision]$.
]

#proof[
  On réalise une recherche dichotomique sur l'ensemble ${ 0, ..., sum_(e in E) ell(e) }$ en utilisant le problème #pbm[TSP_Décision].
  On trouve la longueur minimale en $bigO(log_2(sum_(e in E) ell(e)))$ étapes.
]

#proposition[
  On a $#pbm[TSP_Construction] <= #pbm[TSP_Optimisation]$.
]

#proof[
  On construit l'algorithme ci-dessous.

  #algo[
    $L <- #pbm[TSP_Optimisation] "" (G, ell)$\
    
    #algo-if[$L = oo$][
      #algo-return[ #sc[Faux] ]
    ][
      #algo-for[toute arête $e in E$][
        #algo-if[$#pbm[TSP_Optimisation] "" (G without e, ell) = L$][
          $G <- G without e$
        ]
      ]

      #algo-return[$E(G)$]
    ]
  ]

  Remarquons qu'à la fin, il ne peut rester que les arêtes d'un cycle optimal.

  En sortie, nous savons qu'il reste une solution $C$ de longueur $L$, et qu'il n'existe qu'un seul cycle.
]


Les trois versions sont équivalentes polyomialement.
*On va donc se restreindre au problème de décision.*
En effet, les problèmes de construction, d'optimisation et de décision sont généralement équivalents polynomialement.

Une exception notable : le problème "Collision Somme Tiroirs" (abrégé par "CST").

#pb-display(name: pbm[CST_décision])[
  $S = {x_1, ..., x_n}$ un ensemble de $n$ entiers strictement positifs tel que $sum_(i = 1)^n x_i < 2^n$.
][
  #sc[Vrai] s'il existe deux ensembles $X != Y subset.eq S$ tels que $sum_(x in X) x = sum_(y in Y) y$.
]

En effet, le problème a une solution en $bigO(1)$ :
#algo[
  #algo-return[#sc[Vrai]]
]


La validité de cet algorithme est assurée par deux faits :
- il existe $2^n$ sous-ensembles possibles ;
- le nombre de sommes possibles est inférieur à $2^n$.

Ces types de problèmes sont basés sur : le lemme des tiroirs, la parité, les points fixes.

#definition[
  Un problème peut-être assimilé à l'ensemble des mots en entrée qui admettent #sc[Vrai] en sortie.

  Un langage $L$ est une partie de $cal(A)^star$, l'ensemble des mots sur l'alphabet $cal(A)$.

  Il y a une équivalence entre 
  $ "Problème" <--> "Langage". $
  Il n'y a qu'un seul type de problème :

  #pb-display(name: pbm[$L$-décision])[
    un mot $M in cal(A)^star$
  ][
    #sc[Vrai] si $M in L$.
  ]
]

== Résoudre efficacement.

Il apparaît une question de _modèle de calcul_.
Le premier modèle est l'_automate_ auquel on rajoute de la mémoire pour obtenir une machine de #sc[Turing].
Cependant, dans la machine de #sc[Turing], il y a une distinction entre déterministe et non déterministe.
Ceci crée les classe de complexité $bold(upright(P))$ et $bold("NP")$ : ceci correspond aux machines qui s'exécutent en un nombre polynomial d'étapes.

On étudie quatre exemples types de problèmes de décisions :

#pb-display(name: pbm[CPB])[
  Un graphe $G = (V, E)$ biparti
][
  #sc[Vrai] s'il existe un couplage parfait
]

Quelques définitions : 
/ Biparti.: il existe une partition $A, B$ de $V$ telle que toute arête est entre $A$ et $B$ ;
/ Couplage.: ensemble d'arêtes deux à deux disjointes ;
/ Parfait.: couvre tous les sommets.

Le problème #pbm[CouplageParfaitBiparti] (qu'on notera #pbm[CPB]) est équivalent au problème #pbm[SousMatriceDePermutation] (qu'on notera #pbm[SSMP]).
#pb-display(name: pbm[SSMP])[
  Une matrice $n times n$ à coefficients dans ${0,1}$.
][
  #sc[Vrai] s'il existe une sous-matrice de permutation : $ exists sigma in frak(S)_n, forall i in [|1,n|], m_(i, sigma(i)) = 1 $
]
L'équivalence vient de l'analyse d'un couplage dans la matrice d'adjacence du graphe. Cela correspond à une permutation.

D'autres problèmes intéressants.

#pb-display(name: pbm[Premier])[
  Un entier $n$
][
  #sc[Vrai] si $n$ est premier.
]

#pb-display(name: pbm[Somme])[
  Ensemble d'entiers $S$ et un entier $t$
][
  #sc[Vrai] s'il existe $X subset.eq S$ tel que $sum X = t$.
]


#pb-display(name: pbm[Post])[
  Sept dominos, chacun avec deux mots binaires :
  $
    underbrace( #table(columns: (auto,), $mono(100)$, $mono(001)$), D_1) med,
    ...,
    underbrace( #table(columns: (auto,), $mono(110)$, $mono(111)$), D_7)
  $
][
  #sc[Vrai] si on peut trouver une suite de dominos avec répétition où le mot du haut est égal au mot du bas.
]


Par exemple, la suite ci-dessous est une solution de #pbm[Post] :
$
  #table(columns: (auto,), $mono(0)$, $mono(00)$) med
  #table(columns: (auto,), $mono(00)$, $mono(0)$) med.
$

Certains de ces problèmes sont difficiles, mais ils ne sont pas tous _aussi_ difficiles.
- le problème #pbm[CPB] est (facilement) dans $bold(upright(P))$ ;
- le problème #pbm[Premier] est dans $bold(upright(P))$ ;
- le problème #pbm[Somme] est $bold("NP")$-complet ;
- le problème #pbm[Post] est indécidable.

= Introduction : la science des arbres.

On se place dans une situation, un _toy problem_.
On veut faire un fondant au chocolat, et on essaie de découper une tablette au chocolat.
Comment de découpes pour une tablette de chocolat $6 times 4$ ?

#figure(
  caption: [Une tablette de chocolat],
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"))

    scale(0.5)

    grid((0,0), (6,4))

    for i in range(5) {
      line((i+1,-0.2), (i+1,4.2), stroke: (paint: red))
    }

    translate((8, 0))


    for i in range(6) {
      grid((i * 1.6, 0), (i * 1.6 + 1, 4))
      for j in range(3) {
        line((i*1.6 - 0.2, j + 1), (i * 1.6 + 1.2, j + 1), stroke: (paint:red))
      }
    }
  })
)

On a 23 découpes, qu'on commence ligne par ligne, ou colonne par colonne :
$ 5 + 3 times 6 quad "ou" quad 3 + 4 times 5. $

Une bonne pratique est de se placer dans une instance simple.


#figure(
  caption: [Arbre de découpe],
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"))

    scale(0.5)

    let grid_(tab) = {
      let x = tab.at(0)
      let y = tab.at(1)

      grid((-x/2,-y/2), (x/2,y/2))
    }

    let arrow(x0, y0, x1, y1, alpha0: 0.3, alpha1: 0.7) = {
      let a = (x0 * (1 - alpha0) + alpha0 * x1, y0 * (1 - alpha0) + alpha0 * y1)
      let b = (x0 * (1 - alpha1) + alpha1 * x1, y0 * (1 - alpha1) + alpha1 * y1)
      
      line(a, b, mark: (end: ">", fill: red), stroke: (paint: red))
    }

    grid_((3,2))
    line((-0.5, -1.2), (-0.5, 1.2), stroke: (paint: red))

    arrow(0, 0, -4, -4, alpha1: 0.75)

    group({
      translate((-4, -4))
      grid_((1,2))
      line((-0.7,0), (0.7,0), stroke: (paint: red))


      arrow(0, 0, -1.5, -4, alpha1: 0.8)

      group({
        translate((-1.5, -4))
        grid_((1,1))
      })


      arrow(0, 0, +1.5, -4, alpha1: 0.8)

      group({
        translate((+1.5, -4))
        grid_((1,1))
      })
    })


    arrow(0, 0, 4, -4)

    group({
      translate((4, -4))
      grid_((2,2))
      line((0, -1.2), (0, 1.2), stroke: (paint: red))

      arrow(0, 0, -3, -4)

      group({
        translate((-3, -4))
        grid_((1,2))
        line((-0.7,0), (0.7,0), stroke: (paint: red))

        arrow(0, 0, -1.5, -4, alpha1: 0.8)

        group({
          translate((-1.5, -4))
          grid_((1,1))
        })

        arrow(0, 0, +1.5, -4, alpha1: 0.8)

        group({
          translate((+1.5, -4))
          grid_((1,1))
        })
      })


      arrow(0, 0, 3, -4)

      group({
        translate((+3, -4))
        grid_((1,2))
        line((-0.7,0), (0.7,0), stroke: (paint: red))

        arrow(0, 0, -1.5, -4, alpha1: 0.8)

        group({
          translate((-1.5, -4))
          grid_((1,1))
        })

        arrow(0, 0, +1.5, -4, alpha1: 0.8)

        group({
          translate((+1.5, -4))
          grid_((1,1))
        })
      })
    })
  })
)

On représente la situation par un arbre de découpe :
- un nœud interne correspond à une découpe ;
- une feuille correspond à un carré $1 times 1$ de chocolat ;
- l'arbre est un arbre binaire.
Le nombre de feuilles est donc exactement égale au nombre de carrés de chocolat.

#proposition[
  Le nombre de feuilles dans un arbre binaire, c'est un de plus que le nombre de nœuds internes.
]

On peut le démontrer par induction, mais pour comprendre l'intuition, le mieux, c'est une bijection.
Une bijection serait par exemple : d'un nœud interne, on emprunte le chemin $mono(D) dot.c mono(G)^star$ sous forme d'expression régulière.
Il ne manque qu'un seul nœud, celui tout à gauche.

= Paradigmes  : _diviser pour régner_.


== Nombre de multiplications.

=== L'exponentiation.

#pb-display(name: pbm[Exponentiation])[
  Un réel $x$ et un entier $n > 0$
][
  Le calcul de $x^n$
]

On *ne fait pas* un calcul en $bigO(n)$.
On fait un algorithme diviser pour régner, l'_exponentiation rapide_.

#algo[
  #algo-if[$n = 1$][
    #algo-return[$x$]
  ][$n$ est pair][
    #algo-return[$(x^(n\/2))^2$]
  ][
    #algo-return[$(x^(n\/2))^2 dot x$]
  ]
]

On a une complexité en $bigTheta(log n)$ multiplications : il s'agit 
- du nombre de bits dans l'expression de $n$ moins 1 ;
- du nombre de "$mono(1)$" dans l'expression binaire de $n$ moins 1.

Par exemple, pour $5$, on a trois multiplications : $x^5 = (x^2)^2 dot x$.
Ceci correspond bien : $5 =_2 mono(101)$ et le nombre de multiplications est donné par la formule $3 - 1 + 2 - 1$.

Sujet intéressant à étudier : le _logarithme discret_.

=== Karatsuba & Strassen.

==== Algorithme de Karatsuba.

La multiplication d'entiers appris à l'école est en $bigTheta(n^2)$ en nombre de multiplications.

#figure(
  caption: [Algorithme de multiplication vu à l'école],
  cetz.canvas({
    import cetz.draw: *

    scale(0.3)

    merge-path(stroke: (paint: red, thickness: 1em, join: "round", cap: "round"),fill: red, {
      line((0, -1.6), (-7, -8.5))
      line((-7, -8.5), (0, -8.5))
      line((0, -8.5), (7, -1.6))
      line((7, -1.6), (0, -1.6))
    })


    for i in range(8) {
      content((i,0), $ dot.c $)
      content((i,1), $ dot.c $)
    }

    content((-1, 0), $ times $)

    line((-1.5, -0.8), (7.5, -0.8))


    for i in range(8) {
      for j in range(8) {
        content((i - j,-1.5 - j), $ dot.c $)
      }
    }

    content((-8.5, -0.7 - 8), $ + $)
    line((-9, -1.4 - 8), (7.5, -1.4 - 8))

    for i in range(15) {
      content((-7 + i, -1.4 - 9), $ dot.c $)
    }
  })
)

Dans un cours, #sc[Kolmogoroff] pense que l'algorithme qu'on utilise depuis plusieurs millénaires est optimale.
Mais, #sc[Karatsuba] lui donne tord.

Avant d'attaquer la multiplication d'entiers, on s'intéresse aux polynômes.
Étant donné deux polynômes $A(X) = a_n X^n + dots.c + a_1 X + a_0$ et $B(X) = b_n X^n + dots.c + b_1 X + b_0$.

Comment calculer $C(X) = A(X) times B(X)$ ?

#let makeblock(it, color: red) = context {
  let x = $ #it $
  let inset = 4pt
  let y = measure(x).height + inset / 2
  box(x, fill: color.lighten(70%), stroke: color, inset: inset, radius: 3pt, baseline: y/2)
}

#let redblock = makeblock.with(color: red)
#let orangeblock = makeblock.with(color: orange)
#let yellowblock = makeblock.with(color: yellow)

On s'intéresse à un problème plus simple pour commencer : 
$ (a X + b) times (c X + d) 
  &= a c X^2 + (a d + b c) X + b d\
  &= redblock(a c) X^2 + (redblock(a c) + orangeblock(b d) + yellowblock((a - b)(c - d))) X + orangeblock(b d).
$
On remarque qu'on peut faire ce calcul en n'utilisant que _trois_ multiplications.
Comment utiliser ce résultat pour généraliser ?

Il faut que le problème s'y prête : on verra des problèmes où une stratégie diviser pour régner ne s'y prête pas.
En effet, il faut qu'on puisse couper une instance ce qui fonctionne bien avec des polynômes.

Soient $P(X)$ et $Q(X)$ deux polynômes de degré $n$ (pair). On pose 
$ P(X) &= P_1 (X) X^(n/2) + P_0 (X), \
  Q(X) &= Q_1 (X) X^(n/2) + Q_0 (X).
$
Ainsi, pour calculer $P times Q$, on utilise :
$ P times Q = redblock(P_1 Q_1) X^n + (redblock(P_1 Q_1) + orangeblock(P_0 Q_0) + yellowblock((P_1 - P_0)(Q_1 - Q_0))) X^(n/2) + orangeblock(P_0 Q_0). $

Quel est le coût en multiplications ?
Pour cela, on peut utiliser le _master theorem_ (vu plus tard) ou dessiner l'arbre d'appels.

#figure(
  caption: [Arbre d'appels pour la multiplication de polynômes],
  cetz.canvas({
    import cetz.draw: *
    import cetz.tree: *
    import cetz.decorations: *

    set-style(stroke: (cap: "round", join: "round"))

    tree(
      ($ makeblock(P times Q, color: #gray) $,
        (
          $ redblock(P_0 Q_0) $,
          redblock[],
          orangeblock[],
          yellowblock[],
        ),
        (
          $ orangeblock((P_1 - P_0)(Q_1 - Q_0)) $,
          redblock[],
          orangeblock[],
          yellowblock[],
        ),
        (
          $ yellowblock(P_1 Q_1) $,
          redblock[],
          orangeblock[],
          yellowblock[],
        ),
      ),
      draw-node: (node, ..) => {
        circle((), radius: .35, fill: white, stroke: none)
       content((), node.content)
     },
     draw-edge: (from, to, prev, next, ..) => {
       let (a, b) = (from + ".center", to + ".center")

       line((a, 0.7, b), (b, 0.7, a), mark: (end: ">", scale: 0.5, fill: black))
     },
     grow: 2,
    )
  })
)

Dans l'arbre d'appels, il y a une multiplication par nœud.
L'arbre d'appel, vu qu'on divise par deux le degré du polynôme à chaque étape, a $log_2 n$ niveaux.

Au total, le nombre de nœuds est $bigO(3^(log_2 n)) = bigO(n^(log_2 3))$.

On effectue donc $bigO(n^(log_2 3))$ multiplications.

==== Algorithme de Strassen.

#sc[Strassen] utilise la même idée que #sc[Karatsuba] pour le calcul matriciel.
Il remarque que, pour multiplier de matrices $2 times 2$, seules _sept_ produits sont nécessaires.
En procédant au calcul de matrice par blocs, il peut calculer le produit de deux matrices $n times n$.
Par conséquent, pour calcule deux matrices $n times n$ en $ bigO(7^(log_2 n)) = bigO(n^(log_2 7)) = bigO(n^(2.80...)) . $

On peut pousser encore plus loin l'argument. On note $omega$ la meilleure complexité de produit de matrice (_i.e._ il existe un algorithme de complexité $bigO(n^omega)$, mais pas en $bigO(n^(omega - epsilon))$, quel que soit $epsilon > 0$).
On se situe $omega in [2,3]$.
Actuellement, on a $omega <= "2,38"$.

==== Multiplication d'entiers en $n log n$.

On travaille dans deux mondes : le monde des coefficients polynômiaux, et le monde des évaluations.

Au lieu de calculer $A times B = C$ directement, on évalue les polynômes à $2 n + 1$ valeurs différentes $v_1, ..., v_(2 n + 1)$.
On réalise le produit des valeurs évaluées, que l'on peut interpréter pour obtenir les coefficients de $C$ (opération linéaire).

Sujet intéressent à regarder : _FFT_ (_Fast Fourier Transform_).

==== Algorithme de Strassen (suite).

Strassen interprète l'opération produit comme un tenseur.
Son idée est la suivante : il faut construire un tenseur (une matrice $n$D, en l'occurrence ici 3D) qui représente le produit de matrices.

On peut l'illustrer avec Karatsuba :
on calcule $ (a_1 X + a_0) (b_1 X + b_0) = c_2 X^2 + c_1 X + c_0. $
On construit le tenseur $sans(bold(K)) = (p_(i,j,k))$ de dimension $2 times 2 times 3$, où l'on a $p_(i,j,k) = 1$ si le produit $a_i b_j$ est un terme de $c_k$.

Le tenseur s'écrit donc :
#let sp = 8mm
#{
  let n = table.cell.with(stroke: none)
  stack(
    dir: ltr,
    spacing: 1cm,
    h(1fr),
    stack(
      table(
        columns: (sp,) * 3,
        n[], n($ b_1 $), n($ b_0 $),
        n($ a_0 $), $ 1 $, $ 0 $,
        n($ a_1 $), $ 0 $, $ 0 $,
      ),
      $ c_0 $
    ),
    stack(
      table(
        columns: (sp,) * 3,
        n[], n($ b_1 $), n($ b_0 $),
        n($ a_0 $), $ 0 $, $ 1 $,
        n($ a_1 $), $ 1 $, $ 0 $,
      ),
      $ c_1 $
    ),
    stack(
      table(
        columns: (sp,) * 3,
        n[], n($ b_1 $), n($ b_0 $),
        n($ a_0 $), $ 0 $, $ 0 $,
        n($ a_1 $), $ 0 $, $ 1 $,
      ),
      $ c_2 $
    ),
    h(1fr)
  )
}

Étant donnés trois vecteurs $bold(arrow(U)) = mat(U_1, ..., U_ell)$, $bold(arrow(V)) = mat(V_1, ..., V_m)$ et $bold(arrow(W)) = mat(W_1, ..., W_n)$, on construit le tenseur $bold(sans(T))$ de dimension $ell times m times n$ en posant $bold(sans(T)) = bold(arrow(U)) times.circle bold(arrow(V)) times.circle bold(arrow(W)) = (t_(i,j,k))$, où $t_(i,j,k) = U_i V_j W_k$, idem que pour les matrices de rang 1.
Le tenseur $bold(sans(T))$ est de rang 1.

#definition[
  Le rang d'un tenseur $bold(sans(A))$ est le plus petit nombre de tenseurs de rang $1$ dont la somme vaut $bold(sans(A))$.
]

#theorem(name: [Strassen])[
  Le rang du tenseur de la multiplication de matrices $2 times 2$ est inférieur ou égal à $7$.
]

Par exemple, pour le tenseur de multiplication de polynômes $bold(sans(K))$, il est de rang 3.
En effet, c'est la somme des trois tenseurs :
+ #stack(
    dir: ltr,
    spacing: 1cm,
    h(1fr),
    table(
      columns: (sp,sp),
      $ 1 $, $ 0 $,
      $ 0 $, $ 0 $,
    ),
    table(
      columns: (sp,sp),
      $ 1 $, $ 0 $,
      $ 0 $, $ 0 $,
    ),
    table(
      columns: (sp,sp),
      $ 0 $, $ 0 $,
      $ 0 $, $ 0 $,
    ),
    h(1fr),
  )
+ #stack(
    dir: ltr,
    spacing: 1cm,
    h(1fr),
    table(
      columns: (sp,sp),
      $ 0 $, $ 0 $,
      $ 0 $, $ 0 $,
    ),
    table(
      columns: (sp,sp),
      $ 0 $, $ 0 $,
      $ 0 $, $ 1 $,
    ),
    table(
      columns: (sp,sp),
      $ 0 $, $ 0 $,
      $ 0 $, $ 1 $,
    ),
    h(1fr),
  )
+ #stack(
    dir: ltr,
    spacing: 1cm,
    h(1fr),
    table(
      columns: (sp,sp),
      $ 0 $, $ 0 $,
      $ 0 $, $ 0 $,
    ),
    table(
      columns: (sp,sp),
      $ -1 $, $ 1 $,
      $ 1 $, $ -1 $,
    ),
    table(
      columns: (sp,sp),
      $ 0 $, $ 0 $,
      $ 0 $, $ 0 $,
    ),
    h(1fr),
  )


Sujet intéressant à regarder : _Alpha Tensor_ dans _Nature_.

Quelques remarques sur les tenseurs :
- calculer le rang d'une matrice, c'est un problème dans $bold(upright(P))$, calculer le rang d'un tenseur, c'est un problème $bold("NP")$-dur ;
- si $(bold(M)_i)_(i in NN)$ converge vers $bold(M)$ une matrice $n times n$ de rang plein $n$, alors la suite est ultimement a rang plein#footnote[On dit qu'une matrice a un rang plein si, et seulement si, $det M != 0$. L'ensemble des matrices de rang plein est la pré-image par $det$ (continue) de $RR without { 0 }$. ] ;
- dans le cas général des matrices, la limite du rang d'une suite de matrice est supérieur ou égal au rang de la limite ;
- mais, avec les tenseurs, il est possible d'avoir une limite du rang strictement inférieur au rang de la limite#footnote[Un exemple : $ underbrace([mat(1, 0; 0, 0) quad mat(0,1;1,epsilon)], "tenseur de rang 2") arrow.long_(epsilon -> 0) underbrace([mat(1,0;0,0) quad mat(0,1;1,0)], "tenseur de rang 3") $] ;
- les rangs dans $CC$ et dans $RR$ d'un tenseur réel peuvent être différents ;
- pour discuter de tenseurs, parler avec Pascal #sc[Koiran].

=== Plus courts chemins.

On s'intéresse au problème #pbm[AllPathsShortestPaths], abrégé par APSP :
#pb-display(name: pbm[APSP])[
  Une matrice $bold(D)$ de taille $n times n$ à valeurs dans $NN union {+oo}$.
][
  La matrice des plus courtes distances.
]

Par exemple, dans le graphe ci-dessous, on note $bold(D)$ sa représentation matricielle.
On donne $bold(M)$ la matrice solution du problème APSP.

#figure(
  caption: [Exemple de graphe et solution de APSP],
  stack(
    dir: ltr,
    cetz.canvas({
      import cetz.draw: *

      set-style(stroke: (cap: "round", join: "round"))

      circle((0,0), radius: 0.5, fill: blue, stroke: none, name : "a")
      circle((0,2), radius: 0.5, fill: blue, stroke: none, name : "b")
      circle((2,0), radius: 0.5, fill: blue, stroke: none, name : "c")

      content("a.center", text(white, $ 2 $))
      content("b.center", text(white, $ 1 $))
      content("c.center", text(white, $ 3 $))

      line("a.north", "b.south", mark: (start: ">", fill: black), name: "A")
      bezier-through("a.north-east", (1,0.6), "c.north-west", mark: (end: ">", fill: black), name: "B")
      bezier-through("c.south-west", (1,-0.6), "a.south-east", mark: (end: ">", fill: black), name: "C")
      
      set-style(content: (frame: "rect", stroke: none, fill: white, padding: .05))

      content((name: "A", anchor: 75%), $ 1 $)
      content("B.mid", $ 2 $)
      content("C.mid", $ 4 $)

      content((3,2), $
        bold(D) = mat(
          0, 1, oo;
          oo, 0, 2;
          oo, 4, 0
        )
      $, name: "D")

      content((7,0), $
        bold(M) = mat(
          0, 1, 3;
          oo, 0, 2;
          oo, 4, 0
        )
      $, name: "M")

      bezier-through("D.east", (6, 2), "M.north", mark: (end: ">", fill: gray), stroke: (paint: gray))
    }),
  )
)

Calculons le "carré" de la matrice $bold(D)$. On a $bold(D)^2 = (d_(i,j)^((2)))$, où
$ d_(i,j)^((2)) = min_(k) (d_(i,k) + d_(k,j)) $
On obtient les plus courts chemins de longueur inférieur à 2.

La matrice cherchée cherchée peut être obtenir $ceil(log_2 n)$ itération du carrés, d'où la complexité en $bigO(n^3 log_2 n)$.

Si on peut franchir la barrière du $n^3$ pour le produit _tropical_, et on obtient un algorithme en $bigO(n^(3 - epsilon))$ pour APSP.

Quelle est la complexité du calcul en algèbre (en nombre d'opérations $min$, $times$, $+$) ?
Elle est conjecturée d'être cubique.

== Nombre de comparaisons.

On s'intéresse au tri d'un tableau $bold(T)[1..n]$ d'entiers.

=== Calcul du minimum d'un tableau.

On peut calcule le minimum d'un tableau en $n - 1$ comparaisons de la forme :
"$bold(T)[i] < bold(T)[j]$".

L'approche diviser pour régner permet de calculer le minimum en~$n-1$ comparaisons avec une technique de _tournoi_.

Un algorithme classique de calcul de minimum par tournois est celui ci-dessous.

#algo(name: [Algorithme $"Minimum"(bold(T), n)$])[
  Créer un tableau $bold(R)[1..2 n - 1]$\
  Copier $bold(T)$ sur $bold(R)[n..2 n - 1]$

  #algo-for[$i$ allant de $n-1$ à $1$][
    $bold(R)[i] <- min(bold(R)[2i], bold(R)[2i+1])$
  ]

  #algo-return[$bold(R)[1]$]
]

Par exemple, on trie le tableau $[ 3, 2, 6, 4, 1, 5 ]$.
Pour cela, on crée l'arbre tournoi représenté dans la figure ci-après.
Cet arbre est créé à partir du tableau ci-dessous :
$ [ 1, 1, 2, 4, 1, 3, 2, 6, 4, 1, 5 ]. $

#figure(
  caption: [Arbre tournoi pour le calcul du minimum de $[6, 4, 1, 5, 3, 2]$],
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"))

    let node(p, n, k, double: false) = {
      let u = str(k)
      if (double) {
        circle(p, radius: 0.7, fill: white, name: u, stroke: none)
        circle(p, radius: 0.57, fill: white, stroke: (paint: blue, thickness: 0.05))
        circle(p, radius: 0.5, fill: blue, stroke: none)
      } else {
        circle(p, radius: 0.63, fill: white, name: u, stroke: none)
        circle(p, radius: 0.5, fill: blue, stroke: none)
      }
      content(u+".center", text(white, $ #n $))
      content((name: u, anchor: 30deg), align(left, emph[~~#k]))
    }

    node((+0,5),  1, 1, double: true)
    node((-2,3),  1, 2, double: true)
    node((+2,3),  2, 3)
    node((-3,1),  4, 4)
    node((-1,1),  1, 5, double: true)
    node((+1,1),  3, 6)
    node((+3,1),  2, 7)
    node((-4,-1), 6, 8)
    node((-2.5,-1),4, 9)
    node((-1,-1),  1, 10, double: true)
    node((.5,-1),  5, 11)

    line("2.north-east", "1.south-west", mark: (end: ">", fill: black))
    line("3.north-west", "1.south-east", mark: (end: ">", fill: black))

    line("4.north", "2.south-west", mark: (end: ">", fill: black))
    line("5.north", "2.south-east", mark: (end: ">", fill: black))

    line("6.north", "3.south-west", mark: (end: ">", fill: black))
    line("7.north", "3.south-east", mark: (end: ">", fill: black))

    line("8.north", "4.south-west", mark: (end: ">", fill: black))
    line("9.north", (name: "4", anchor: -70deg), mark: (end: ">", fill: black))

    line("10.north", "5.south", mark: (end: ">", fill: black))
    line((name: "11", anchor: 120deg), "5.south-east", mark: (end: ">", fill: black))
  })
)

=== Algorithme de tri fusion.

On divise le tableau $bold(T)[1..n]$ en deux sous-tableaux de taille $floor(n \/ 2)$ et $ceil(n \/ 2)$.
On appelle récursivement l'algorithme de tri, et on _fusionne_.

Dans le pire cas (un tableau alternant grande valeur et petite valeur), la fusion implique $n - 1$ comparaison.

Au final, l'algorithme a une complexité en $bigO(n log n)$.
En effet, le "vrai" coût pire cas vérifie 
- $c(1) = 0$
- $c(n) = c(floor(n / 2)) + c(ceil(n / 2)) + n - 1$.
On peut montrer que $c(n) = sum_(i = 1)^n ceil(log_2 i)$.

#proposition[
  Le meilleur algorithme de tri dans le pire des cas effectue~$ceil(log_2 (n!)) = ceil(sum_(i=1)^n log_2 i)$ comparaisons.
]

#proof[
  On construit l'arbre ci-dessous.
  Dans les nœuds de l'arbre, on indique le nombre de permutations vérifiant les conditions (les questions).
  Ces permutations, on les appelles "solutions".

  #figure(
    caption: [Arbre d'appels pour la multiplication de polynômes],
    cetz.canvas({
      import cetz.draw: *
      import cetz.tree: *
      import cetz.decorations: *

      set-style(stroke: (cap: "round", join: "round"))

      tree(
        ($ n! $,
          ($ >= n!/2 $,
            [], $ >= n! / 4 $
          ), ([], [], []
          )
        ),
        draw-node: (node, ..) => {
          if node.content.func() == math.equation {
            circle((), radius: .45, fill: blue, stroke: none)
          } else {
            circle((), radius: .45, fill: gray.lighten(50%), stroke: none)
          }
         content((), text(white, node.content))
       },
       draw-edge: (from, to, prev, next, ..) => {
         let (a, b) = (from + ".center", to + ".center")

         line((a, 0.7, b), (b, 0.7, a), mark: (end: ">", scale: 0.5, fill: black))
       },
       grow: 2,
      )
    })
  )

  Une comparaison de la forme $bold(T)[i] < bold(T)[j]$ coupe l'espace des solutions en deux.
  Comme on se place dans le pire cas, on choisit la branche avec le nombre de solutions la plus élevée.

  On peut montrer que, à l'étape $k$, il reste $n! \/ 2^k$ solutions possibles.
  On ne peut conclure que lorsque le nombre de solutions est inférieur ou égale à $1$.

  On ne peut pas conclure avant :
  $ n! / 2^k <= 1 quad ==> quad n! <= 2^k quad ==> quad ceil(log_2 n!) <= k. $
]

=== Calcul de médiane.

Soit $bold(T)$ un tableau de $n$ valeurs, et on cherche la valeur médiane~$bold(T)_"triée" [floor(n \/ 2)]$.
On peut le faire en $bigO(n)$ avec l'algorithme nommé BFPRT.#footnote[Blum-Floyd-Pratt-Rivest-Tarjan]

Commençons par généraliser : on veut calculer la $k$-ième valeur du tableau $bold(T)_"triée"$.

Première idée : un algorithme randomisé. Oui, mais non. On préfèrerai un algorithme non probabiliste.

Deuxième idée : forcer la chance
(l'algorithme sera écrit proprement la prochaine fois)

#algo(name: [Algorithme BFPRT])[
  #algo-in[ $bold(T)[i..j]$ de taille $n$ et $k in [| 1, n|]$. ]
  #algo-out[Le $k$-ième élément de $bold(T)_"trié"$]

  On divise $bold(T)$ en $n\/5$ blocs de taille $5$.\
  On extrait $m_1, ..., m_(n \/ 5)$ les éléments médiants de chaque bloc.\
  On construit $bold(M) = [m_1, ..., m_(n\/5)]$.\
  On calcule le $(n\/10)$-ième élément de $bold(M)[1..n\/5])$.\
  On partitionne $bold(T)$ avec $m$ : $bold(T) = lr([underbrace(#[$t_1, ..., t_(ell - 1)$], <= m), underbrace(t_ell, = m), underbrace(#[$t_(ell + 1), ..., t_(n)$], >= m)], size: #20%)$.\

  #algo-if[
    $ell = k$
  ][
    #algo-return[$m$]
  ][
    $ell > k$
  ][
    #algo-return[le $k$-ième élément de $bold(T)[1..ell - 1]$ $(star)$]
  ][
    #algo-return[le $(k-ell)$-ième élément de $bold(T)[ell + 1..n]$ $(star thin star)$]
  ]
]

Pour trouver la complexité, il faut se demander ce quelle taille ont les tableaux aux appels $(star)$ et $(star thin star)$.

#figure(
  caption: [Les éléments médians des $n/5$ sous-tableaux de $5$ éléments],
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"))

    group({
      let i = 1

      circle((0,0), name: "m", radius: 0.15, stroke: blue, fill: blue)
      circle((-1,+1/2), name: "a", radius: 0.1, stroke: none, fill: blue)
      circle((-1,-1/2), name: "b", radius: 0.1, stroke: none, fill: blue)
      circle((+1,+1/2), name: "c", radius: 0.1, stroke: none, fill: blue)
      circle((+1,-1/2), name: "d", radius: 0.1, stroke: none, fill: blue)
      rect((-1.2, 1/2 + 0.2), (-0.8, -1/2 - 0.2), radius: 0.2, stroke: gray)
      rect((+1.2, 1/2 + 0.2), (+0.8, -1/2 - 0.2), radius: 0.2, stroke: gray)
      line(("a", 0.15, "m"), ("m", 0.2, "a"), mark: (end: ">", fill: black))
      line(("b", 0.15, "m"), ("m", 0.2, "b"), mark: (end: ">", fill: black))
      line(("c", 0.15, "m"), ("m", 0.22, "c"), mark: (start: ">", fill: black))
      line(("d", 0.15, "m"), ("m", 0.22, "d"), mark: (start: ">", fill: black))

      cetz.decorations.brace((+1, -0.85), (-1, -0.85))

      content((0,-1.75), $ bold(T)_#i $)
      content("m.south", v(-6mm) + $ m_#i $)
    })

    translate((3, 0))

    group({
      let i = 2

      circle((0,0), name: "m", radius: 0.15, stroke: blue, fill: blue)
      circle((-1,+1/2), name: "a", radius: 0.1, stroke: none, fill: blue)
      circle((-1,-1/2), name: "b", radius: 0.1, stroke: none, fill: blue)
      circle((+1,+1/2), name: "c", radius: 0.1, stroke: none, fill: blue)
      circle((+1,-1/2), name: "d", radius: 0.1, stroke: none, fill: blue)
      rect((-1.2, 1/2 + 0.2), (-0.8, -1/2 - 0.2), radius: 0.2, stroke: gray)
      rect((+1.2, 1/2 + 0.2), (+0.8, -1/2 - 0.2), radius: 0.2, stroke: gray)
      line(("a", 0.15, "m"), ("m", 0.2, "a"), mark: (end: ">", fill: black))
      line(("b", 0.15, "m"), ("m", 0.2, "b"), mark: (end: ">", fill: black))
      line(("c", 0.15, "m"), ("m", 0.22, "c"), mark: (start: ">", fill: black))
      line(("d", 0.15, "m"), ("m", 0.22, "d"), mark: (start: ">", fill: black))

      cetz.decorations.brace((+1, -0.85), (-1, -0.85))

      content((0,-1.75), $ bold(T)_#i $)
      content("m.south", v(-6mm) + $ m_#i $)
    })

    translate((2.5, 0))
    content((0,0), $ dots.c $)
    translate((2.5, 0))

    group({
      let i = $ n / 5 $

      circle((0,0), name: "m", radius: 0.15, stroke: blue, fill: blue)
      circle((-1,+1/2), name: "a", radius: 0.1, stroke: none, fill: blue)
      circle((-1,-1/2), name: "b", radius: 0.1, stroke: none, fill: blue)
      circle((+1,+1/2), name: "c", radius: 0.1, stroke: none, fill: blue)
      circle((+1,-1/2), name: "d", radius: 0.1, stroke: none, fill: blue)
      rect((-1.2, 1/2 + 0.2), (-0.8, -1/2 - 0.2), radius: 0.2, stroke: gray)
      rect((+1.2, 1/2 + 0.2), (+0.8, -1/2 - 0.2), radius: 0.2, stroke: gray)
      line(("a", 0.15, "m"), ("m", 0.2, "a"), mark: (end: ">", fill: black))
      line(("b", 0.15, "m"), ("m", 0.2, "b"), mark: (end: ">", fill: black))
      line(("c", 0.15, "m"), ("m", 0.22, "c"), mark: (start: ">", fill: black))
      line(("d", 0.15, "m"), ("m", 0.22, "d"), mark: (start: ">", fill: black))

      cetz.decorations.brace((+1, -0.85), (-1, -0.85))

      content((0,-1.75), $ bold(T)_#i $)
      content("m.south", v(-6mm) + $ m_#i $)
    })

  })
)

La moitié des médianes $m_1, ..., m_(n/5)$ est inférieure ou égale à la médiane $m$.
Et, dans chaque sous-tableau, trois éléments sur les cinq sont donc assurés d'être inférieurs strictement à $m$.
Ceci assure donc que $7/10 n$ éléments sont supérieurs ou égaux à $n$ ($7/10 = 1 - (1/2 dot 3/5)$).
On élimine $3/10 n$ éléments à chaque étape.

Dans les appels $(star)$ et $(star  thin star)$, on n'a donc que 70 % des éléments du tableau dans l'appel récursif.

Pour un nœud interne dans l'arbre des appels récursif, le coût est en $bigO(n)$.
La fonction de complexité $C(n)$ vérifie :
$ C(n) &<= C(n / 5) + C((7n) / 10) + c n\
&<= C(9/10 n) + c n, $
par "super additivité" de la fonction $C$.#footnote[L'hypothèse de la super additivité est faite dans un raisonnement par analyse--synthèse. On vérifie aisément cette hypothèse après.]
D'où, 
$ C(n) <= c n + (9/10) c n + (9/10)^2 c n + dots.c <= 10 c n. $

#remark(name: [Algorithme Las Vegas])[
  L'algorithme randomisé pour le calcul du $k$-ième plus petit élément peut se retrouver assez simplement en supprimant la division en 5 blocs.
  Il est presque sûrement en temps linéaire.

]

#block(breakable: false)[
  #algo(name: [Algorithme BFPRT Randomisé])[
    #algo-in[ $bold(T)[i..j]$ de taille $n$ et $k in [| 1, n|]$. ]
    #algo-out[Le $k$-ième élément de $bold(T)_"trié"$]

    On tire $m$ un élément de $bold(T)$ au hasard.\
    On partitionne $bold(T)$ avec $m$ : $bold(T) = lr([underbrace(#[$t_1, ..., t_(ell - 1)$], <= m), underbrace(t_ell, = m), underbrace(#[$t_(ell + 1), ..., t_(n)$], >= m)], size: #20%)$.\

    #algo-if[
      $ell = k$
    ][
      #algo-return[$m$]
    ][
      $ell > k$
    ][
      #algo-return[le $k$-ième élément de $bold(T)[1..ell - 1]$]
    ][
      #algo-return[le $(k-ell)$-ième élément de $bold(T)[ell + 1..n]$]
    ]
  ]
]

#remark(name: [Algorithme Monte-Carlo])[
  Avec un algorithme randomisé alternatif,  
  on tire $sqrt(n)$ valeurs du tableau $bold(T)$ au hasard, et on calcule la "vraie" médiane $m$.
  Il est donc important de se demander avec quelle probabilité le choix de $m$ est le bon.
]


#theorem(name: [Chernoff -- application à notre algorithme])[
  Quel que soit $epsilon > 0$, il existe une constante $c > 1$ et un rang~$n_0$ tels que, au delà de $n >= n_0$,
  $ upright(P)(M in.not [(""^1\/_3 - epsilon) sqrt(n), (""^1\/_3 + epsilon) sqrt(n)]) <= 1/(c^sqrt(n)), $
  où l'on a noté $P$ l'ensemble des valeurs $<= m$ tirées aléatoirement.

  "La probabilité d'échec du choix de valeurs est exponentiellement plus faible en la taille de l'échantillon."
]

Pourquoi ne pas faire avec des blocs de 3 dans l'algorithme BFPTR ?
Et bien, on calcule 
$ C(n) <= C(n/3) + C((1 - 1/6 - 1/6) n) + c n <= underbrace(C(n/3) + C(2/3 n), <= C(n)) + c n. $
Une complexité linéaire n'est donc pas assurée...

#theorem(name: [Théorème Maître/_Master Theorem_])[
  Lorsqu'on a une relation de récurrence sur $T(n)$ (par exemple, le nombre de multiplications/comparaisons) de la forme 
  $ T(n) = a T(n/b) + bigTheta(n^c log^d n), $
  alors, en posant $omega = log_b a$, on a 
  $ T(n) = cases(
    bigTheta(n^c log^d n) quad & "si" omega < c,
    bigTheta(n^c log^(d+1) n) quad & "si" omega = c,
    bigTheta(n^omega) quad & "si" omega > c.
  ) $
]

= Algorithmes gloutons.

== Introduction.

Avec un algorithme glouton, la stratégie est la suivante.
#quote[
  On construit une solution pas à pas, en ne _remettant pas en cause_ les choix précédents.
]

#example[
  On construit $S subset.eq { 0, ..., n } = [n] union {0}$ de cardinal maximal sans suite arithmétique de longueur trois ($x$, $x + a$, $x + 2a$).
  Par exemple, en commençant à zéro, on peut construire
  $ S = {0, 1, 3, 4, 9, ...}. $
  On laisse en exercice la caractérisation de l'ensemble.
]

#example[
  #pb-display(name: pbm[Flots], box[
    - Un graphe orienté $D = (V, A)$,
    - Une source $s$ et un terminal $t$ ;
  ])[
    Un ensemble $S$ maximum de $(s-t)$-chemins avec des arcs disjoints.
  ]

  On part d'un algorithme glouton.

]

#block(breakable: false)[
#algo(name: [Algorithme glouton])[
  $S <- emptyset$

  #algo-while[il existe un $(s-t)$-chemin $P$][
    $S <- S union { P }$\
    $A <- A without "arcs"(P)$
  ]
]
]

Ce glouton n'est pas optimal. Certaines arêtes le gène pour atteindre le flot optimal.

Et, on ajoute deux lignes _mystérieuses_.
Ces deux lignes permettent de filtrer les arêtes qui gênent l'algorithme glouton original.

Le fonctionnement de ces deux lignes apparaîtra plus clairement dans l'exemple après.

~


#algo(name: [Algorithme Floyd-Fulkerson])[
  #algo-while[il existe un $(s-t)$-chemin $P$][
    Inverser les arcs de $P$
  ]

  Effacer les arcs inversés un nombre pair de fois,\
  et inverser les autres. #algo-comment[$(star)$]

  $S <- emptyset$

  #algo-while[il existe un $(s-t)$-chemin $P$][
    $S <- S union { P }$\
    $A <- A without "arcs"(P)$
  ]
]

#pagebreak(weak: true)

#figure(
  caption: [Exécution de l'algorithme de Ford--Fulkerson],
  stack(
    dir: ttb,
    spacing: 1cm/2,
    cetz.canvas({
      import cetz.draw: *

      let rpoint = 0.1
      let pad = 1 + 7/10
      set-style(stroke: (cap: "round", join: "round"))

      circle((0,0),    name: "s", radius: rpoint*pad, stroke: none)
      circle((1.5,1),  name: "a", radius: rpoint*pad, stroke: none)
      circle((1,0),    name: "b", radius: rpoint*pad, stroke: none)
      circle((2,0),    name: "c", radius: rpoint*pad, stroke: none)
      circle((1.5,-1), name: "d", radius: rpoint*pad, stroke: none)
      circle((3,0),    name: "t", radius: rpoint*pad, stroke: none)

      circle((-5, 0),stroke: none)
      circle((+5, 0),stroke: none)

      line("s", "b", mark: (end: ">", fill: black))
      line("b", "c", mark: (end: ">", fill: black))
      line("c", "t", mark: (end: ">", fill: black))
      line("a", "b", mark: (end: ">", fill: black))
      line("c", "d", mark: (end: ">", fill: black))
      arc-through("s.south", (0.9, -0.9), "d.west", mark: (end: ">", fill: black))
      arc-through("s.north", (0.9, +0.9), "a.west", mark: (end: ">", fill: black))
      arc-through("d.east", (2.1, -0.9), "t.south", mark: (end: ">", fill: black))
      arc-through("a.east", (2.1, +0.9), "t.north", mark: (end: ">", fill: black))

      circle("s", radius: rpoint, stroke: blue, fill: blue)
      circle("a", radius: rpoint, stroke: blue)
      circle("b", radius: rpoint, stroke: blue)
      circle("c", radius: rpoint, stroke: blue)
      circle("d", radius: rpoint, stroke: blue)
      circle("t", radius: rpoint, stroke: blue, fill: blue)

      content("s.north-west", $s$ + h(0.3cm))
      content("t.north-east", h(0.3cm) + $t$)

      content((-2, 0))[Graphe initial]
    }),
    cetz.canvas({
      import cetz.draw: *

      let rpoint = 0.1
      let pad = 1 + 7/10
      set-style(stroke: (cap: "round", join: "round"))

      circle((0,0),    name: "s", radius: rpoint*pad, stroke: none)
      circle((1.5,1),  name: "a", radius: rpoint*pad, stroke: none)
      circle((1,0),    name: "b", radius: rpoint*pad, stroke: none)
      circle((2,0),    name: "c", radius: rpoint*pad, stroke: none)
      circle((1.5,-1), name: "d", radius: rpoint*pad, stroke: none)
      circle((3,0),    name: "t", radius: rpoint*pad, stroke: none)

      circle((-5, 0),stroke: none)
      circle((+5, 0),stroke: none)

      line("s", "b", mark: (end: ">", fill: black))
      line("b", "c", mark: (end: ">", fill: red), stroke: (paint: red))
      line("c", "t", mark: (end: ">", fill: black))
      line("a", "b", mark: (end: ">", fill: red), stroke: (paint: red))
      line("c", "d", mark: (end: ">", fill: red), stroke: (paint: red))
      arc-through("s.south", (0.9, -0.9), "d.west", mark: (end: ">", fill: black))
      arc-through("s.north", (0.9, +0.9), "a.west", mark: (end: ">", fill: red), stroke: (paint: red))
      arc-through("d.east", (2.1, -0.9), "t.south", mark: (end: ">", fill: red), stroke: (paint: red))
      arc-through("a.east", (2.1, +0.9), "t.north", mark: (end: ">", fill: black))

      circle("s", radius: rpoint, stroke: red, fill: red)
      circle("a", radius: rpoint, stroke: red)
      circle("b", radius: rpoint, stroke: red)
      circle("c", radius: rpoint, stroke: red)
      circle("d", radius: rpoint, stroke: red)
      circle("t", radius: rpoint, stroke: red, fill: red)

      content("s.north-west", $s$ + h(0.3cm))
      content("t.north-east", h(0.3cm) + $t$)

      content((-2, 0))[1ère itération]
    }),
    cetz.canvas({
      import cetz.draw: *

      let rpoint = 0.1
      let pad = 1 + 7/10
      set-style(stroke: (cap: "round", join: "round"))

      circle((0,0),    name: "s", radius: rpoint*pad, stroke: none)
      circle((1.5,1),  name: "a", radius: rpoint*pad, stroke: none)
      circle((1,0),    name: "b", radius: rpoint*pad, stroke: none)
      circle((2,0),    name: "c", radius: rpoint*pad, stroke: none)
      circle((1.5,-1), name: "d", radius: rpoint*pad, stroke: none)
      circle((3,0),    name: "t", radius: rpoint*pad, stroke: none)

      circle((-5, 0),stroke: none)
      circle((+5, 0),stroke: none)

      line("s", "b", mark: (end: ">", fill: red), stroke: (paint: red))
      line("b", "c", mark: (start: ">", fill: black))
      line("c", "t", mark: (end: ">", fill: black))
      line("a", "b", mark: (start: ">", fill: red), stroke: (paint: red))
      line("c", "d", mark: (start: ">", fill: black))
      arc-through("s.south", (0.9, -0.9), "d.west", mark: (end: ">", fill: black))
      arc-through("s.north", (0.9, +0.9), "a.west", mark: (start: ">", fill: black))
      arc-through("d.east", (2.1, -0.9), "t.south", mark: (start: ">", fill: black))
      arc-through("a.east", (2.1, +0.9), "t.north", mark: (end: ">", fill: red), stroke: (paint: red))

      circle("s", radius: rpoint, stroke: red, fill: red)
      circle("a", radius: rpoint, stroke: red)
      circle("b", radius: rpoint, stroke: red)
      circle("c", radius: rpoint, stroke: blue)
      circle("d", radius: rpoint, stroke: blue)
      circle("t", radius: rpoint, stroke: red, fill: red)

      content("s.north-west", $s$ + h(0.3cm))
      content("t.north-east", h(0.3cm) + $t$)

      content((-2, 0))[2nde itération]
    }),
    cetz.canvas({
      import cetz.draw: *

      let rpoint = 0.1
      let pad = 1 + 7/10
      set-style(stroke: (cap: "round", join: "round"))

      circle((0,0),    name: "s", radius: rpoint*pad, stroke: none)
      circle((1.5,1),  name: "a", radius: rpoint*pad, stroke: none)
      circle((1,0),    name: "b", radius: rpoint*pad, stroke: none)
      circle((2,0),    name: "c", radius: rpoint*pad, stroke: none)
      circle((1.5,-1), name: "d", radius: rpoint*pad, stroke: none)
      circle((3,0),    name: "t", radius: rpoint*pad, stroke: none)

      circle((-5, 0),stroke: none)
      circle((+5, 0),stroke: none)

      line("s", "b", mark: (start: ">", fill: black))
      line("b", "c", mark: (start: ">", fill: black))
      line("c", "t", mark: (end: ">", fill: red), stroke: (paint: red))
      line("a", "b", mark: (end: ">", fill: black))
      line("c", "d", mark: (start: ">", fill: red), stroke: (paint: red))
      arc-through("s.south", (0.9, -0.9), "d.west", mark: (end: ">", fill: red), stroke: (paint: red))
      arc-through("s.north", (0.9, +0.9), "a.west", mark: (start: ">", fill: black))
      arc-through("d.east", (2.1, -0.9), "t.south", mark: (start: ">", fill: black))
      arc-through("a.east", (2.1, +0.9), "t.north", mark: (start: ">", fill: black))

      circle("s", radius: rpoint, stroke: red, fill: red)
      circle("a", radius: rpoint, stroke: blue)
      circle("b", radius: rpoint, stroke: blue)
      circle("c", radius: rpoint, stroke: red)
      circle("d", radius: rpoint, stroke: red)
      circle("t", radius: rpoint, stroke: red, fill: red)

      content("s.north-west", $s$ + h(0.3cm))
      content("t.north-east", h(0.3cm) + $t$)

      content((-2, 0))[3ème itération]
    }),
    cetz.canvas({
      import cetz.draw: *

      let rpoint = 0.1
      let pad = 1 + 7/10
      set-style(stroke: (cap: "round", join: "round"))

      circle((0,0),    name: "s", radius: rpoint*pad, stroke: none)
      circle((1.5,1),  name: "a", radius: rpoint*pad, stroke: none)
      circle((1,0),    name: "b", radius: rpoint*pad, stroke: none)
      circle((2,0),    name: "c", radius: rpoint*pad, stroke: none)
      circle((1.5,-1), name: "d", radius: rpoint*pad, stroke: none)
      circle((3,0),    name: "t", radius: rpoint*pad, stroke: none)

      circle((-5, 0),stroke: none)
      circle((+5, 0),stroke: none)

      line("s", "b", mark: (start: ">", fill: black))
      line("b", "c", mark: (start: ">", fill: black))
      line("c", "t", mark: (start: ">", fill: black))
      line("a", "b", mark: (end: ">", fill: black))
      line("c", "d", mark: (end: ">", fill: black))
      arc-through("s.south", (0.9, -0.9), "d.west", mark: (start: ">", fill: black))
      arc-through("s.north", (0.9, +0.9), "a.west", mark: (start: ">", fill: black))
      arc-through("d.east", (2.1, -0.9), "t.south", mark: (start: ">", fill: black))
      arc-through("a.east", (2.1, +0.9), "t.north", mark: (start: ">", fill: black))

      circle("s", radius: rpoint, stroke: blue, fill: blue)
      circle("a", radius: rpoint, stroke: blue)
      circle("b", radius: rpoint, stroke: blue)
      circle("c", radius: rpoint, stroke: blue)
      circle("d", radius: rpoint, stroke: blue)
      circle("t", radius: rpoint, stroke: blue, fill: blue)

      content("s.north-west", $s$ + h(0.3cm))
      content("t.north-east", h(0.3cm) + $t$)

      content((-2, 0))[Graphe après\ la boucle]
    }),
    cetz.canvas({
      import cetz.draw: *

      let rpoint = 0.1
      let pad = 1 + 7/10
      set-style(stroke: (cap: "round", join: "round"))

      circle((0,0),    name: "s", radius: rpoint*pad, stroke: none)
      circle((1.5,1),  name: "a", radius: rpoint*pad, stroke: none)
      circle((1,0),    name: "b", radius: rpoint*pad, stroke: none)
      circle((2,0),    name: "c", radius: rpoint*pad, stroke: none)
      circle((1.5,-1), name: "d", radius: rpoint*pad, stroke: none)
      circle((3,0),    name: "t", radius: rpoint*pad, stroke: none)

      circle((-5, 0),stroke: none)
      circle((+5, 0),stroke: none)

      line("s", "b", mark: (end: ">", fill: black))
      line("b", "c", mark: (end: ">", fill: black))
      line("c", "t", mark: (end: ">", fill: black))
      arc-through("s.south", (0.9, -0.9), "d.west", mark: (end: ">", fill: black))
      arc-through("s.north", (0.9, +0.9), "a.west", mark: (end: ">", fill: black))
      arc-through("d.east", (2.1, -0.9), "t.south", mark: (end: ">", fill: black))
      arc-through("a.east", (2.1, +0.9), "t.north", mark: (end: ">", fill: black))

      circle("s", radius: rpoint, stroke: blue, fill: blue)
      circle("a", radius: rpoint, stroke: blue)
      circle("b", radius: rpoint, stroke: blue)
      circle("c", radius: rpoint, stroke: blue)
      circle("d", radius: rpoint, stroke: blue)
      circle("t", radius: rpoint, stroke: blue, fill: blue)

      content("s.north-west", $s$ + h(0.3cm))
      content("t.north-east", h(0.3cm) + $t$)

      content((-2, 0))[Graphe filtré]
    }),
    v(-1cm/2) + [~]
  )
)

#pagebreak(weak: true)

Justifions la validité de l'algorithme.

Commençons par la notion de coupe.
Une $(s-t)$-coupe est une partition $(S,T)$ de $V$ telle que $s in S$ et $t in T$.
La _valeur_ d'une coupe est le nombre d'arcs de $S$ à $T$.
Remarquons que la valeur d'une $(s-t)$-coupe est un majorant du nombre de chemins disjoints.

Une itération de la première boucle "*Tant que*" fait décroître la valeur de _toutes_ les coupe de $1$.
Le nombre d'itérations (dans la première boucle), qu'on notera $k$, est la valeur minimale d'une coupe.
En effet, une fois que l'on atteint une valeur de $0$ pour toutes les coupes, il n'y a donc plus d'arcs de $S$ à $T$.

Pour reconstruire les partitions $S$ et $T$, il suffit de trouver les sommets reliés à $s$.

Après l'exécution de la ligne $(star)$, 
le degré sortant (noté $d^+(s) = k$) de $s$ est $k$ et le degré entrant (noté $d^-(s) = k$) de $t$ est est $k$.
On a la propriété que tous les sommets $v in.not {s,t}$ ont le même degré entrant et sortant : 
$ forall v in.not {s,t}, d^+(v) = d^- (v), $
on appelle cela la condition de Kirchhoff.

Une marche gloutonne partant de $s$ arrive forcément en $t$. On en déduit que le calcul d'un chemin est glouton.

Après une itération de la seconde boucle "*Tant que*", la condition de  Kirchhoff  est conservée, et le degré sortant de $s$ décroît de $1$ exactement.
On a donc $k$ chemins dans $A$.

#example[
  On peut appliquer le problème de flot aux calcul d'un couplage maximal dans le cas d'un graphe biparti.
  Pour cela, il suffit d'ajouter deux sommets $s$ et $t$.

  #figure(
    cetz.canvas({
      import cetz.draw: *

      let lerp(value, start1, stop1, start2, stop2) = ((value - start1) / (stop1 - start1)) * (stop2 - start2) + start2

      let line-custom(a, b, mark: false, color: black) = {
        if mark {
          line(a,b, stroke: (paint: white, thickness: 0.09))
          line(a,b, mark: (end: ">", fill: color, scale: 0.3), stroke: (paint: color))
        } else {
          line(a,b, stroke: (paint: white, thickness: 0.09))
          line(a,b)
        }
      }
      set-style(stroke: (cap: "round", join: "round"))

      group({
        circle((0,lerp(1,1,4,-1.5,1.5)), name: "A1", radius: 0.2, fill: none, stroke: none)
        circle((0,lerp(2,1,4,-1.5,1.5)), name: "A2", radius: 0.2, fill: none, stroke: none)
        circle((0,lerp(3,1,4,-1.5,1.5)), name: "A3", radius: 0.2, fill: none, stroke: none)
        circle((0,lerp(4,1,4,-1.5,1.5)), name: "A4", radius: 0.2, fill: none, stroke: none)

        circle((1,lerp(1,1,5,-1.5,1.5)), name: "B1", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(2,1,5,-1.5,1.5)), name: "B2", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(3,1,5,-1.5,1.5)), name: "B3", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(4,1,5,-1.5,1.5)), name: "B4", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(5,1,5,-1.5,1.5)), name: "B5", radius: 0.2, fill: none, stroke: none)

        for x in ("A1","A2","A3","A4","B1","B2","B3","B4","B5") {
          circle(x, radius: 0.1, fill: blue, stroke: none)
        }


        line-custom("A1", "B2")
        line-custom("A1", "B3")
        line-custom("A2", "B1")
        line-custom("A2", "B4")
        line-custom("A2", "B5")
        line-custom("A3", "B1")
        line-custom("A3", "B4")
        line-custom("A4", "B2")
        line-custom("A4", "B4")
        line-custom("A4", "B5")

        content((0.5,-2))[Problème de couplage]
      })

      line((2, 0), (5, 0), mark: (end: ">", fill: black))

      translate((7,0))

      group({
        circle((-1,0), name: "S", radius: 0.2, fill: none, stroke: none)
        circle((2,0), name: "T", radius: 0.2, fill: none, stroke: none)

        circle((0,lerp(1,1,4,-1.5,1.5)), name: "A1", radius: 0.2, fill: none, stroke: none)
        circle((0,lerp(2,1,4,-1.5,1.5)), name: "A2", radius: 0.2, fill: none, stroke: none)
        circle((0,lerp(3,1,4,-1.5,1.5)), name: "A3", radius: 0.2, fill: none, stroke: none)
        circle((0,lerp(4,1,4,-1.5,1.5)), name: "A4", radius: 0.2, fill: none, stroke: none)

        circle((1,lerp(1,1,5,-1.5,1.5)), name: "B1", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(2,1,5,-1.5,1.5)), name: "B2", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(3,1,5,-1.5,1.5)), name: "B3", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(4,1,5,-1.5,1.5)), name: "B4", radius: 0.2, fill: none, stroke: none)
        circle((1,lerp(5,1,5,-1.5,1.5)), name: "B5", radius: 0.2, fill: none, stroke: none)

        for x in ("A1","A2","A3","A4","B1","B2","B3","B4","B5") {
          circle(x, radius: 0.1, fill: blue, stroke: none)
        }

        circle("S", radius: 0.1, fill: purple, stroke: none)
        circle("T", radius: 0.1, fill: purple, stroke: none)

        let line-custom = line-custom.with(mark: true)

        line-custom("S", "A1", color: purple)
        line-custom("S", "A2", color: purple)
        line-custom("S", "A3", color: purple)
        line-custom("S", "A4", color: purple)

        line-custom("B1", "T", color: purple)
        line-custom("B2", "T", color: purple)
        line-custom("B3", "T", color: purple)
        line-custom("B4", "T", color: purple)
        line-custom("B5", "T", color: purple)

        line-custom("A1", "B2")
        line-custom("A1", "B3")
        line-custom("A2", "B1")
        line-custom("A2", "B4")
        line-custom("A2", "B5")
        line-custom("A3", "B1")
        line-custom("A3", "B4")
        line-custom("A4", "B2")
        line-custom("A4", "B4")
        line-custom("A4", "B5")

        content("S.south-west", text(purple)[$ \ s $])
        content("T.south-east", text(purple)[$ \ t $])

        content((0.5,-2))[Problème de flots]
      })
    })
  )

  Ainsi, le calcul du nombre maximal de $(s-t)$-chemins disjoints correspond exactement au calcul du couplage maximal.
]

#theorem[
  Quel que soit $epsilon >0$, il existe un algorithme de calcul du flot maximum en $bigO((n+m)^(1 + epsilon))$ (complexité quasi-linéaire).
]

== Codage binaire.

On a un mot $M in cal(A)^star$  et on veut le transformer en mot binaire en replaçant chaque lettre par un mot de ${mono(0),mono(1)}$.
Idéalement, on veut pouvoir retrouver $M$ et compresser le mot binaire.

On veut un code préfixe optimal, c'est-à-dire, pour chaque lettre~$x$ dans $M$, ayant $m_x$ occurrences, on veut associer un mot $phi(x)  in {mono(0),mono(1)}^star$ tel que 
- _préfixe_ : pour deux lettres $x != y$, $phi(x)$ n'est pas préfixe de $phi(y)$ ;
- _optimal_ : $phi(M)$ est de longueur minimal, _i.e._, $sum_(x in cal(A)) m_x |phi(x)|$ est minimal parmi les codes préfixes.

#example[
  On considère le mot $M in {mono(a), ..., mono(g)}^star$ avec les occurrences :
  #figure(
    table(
      columns: (auto,) + (0.8cm,)*7,
      [Lettre], $mono(a) $, $mono(b) $, $mono(c) $, $mono(d) $, $mono(e) $, $mono(f) $, $mono(g) $,
      [Nb. occ.], $ 28 $, $ 7 $, $ 10 $, $ 6 $, $ 1 $, $ 4 $, $ 8 $
    )
  )
]

Une solution possible est le code ASCII.
Le mot $M$ a une longueur totale de $7 dot (28 + 7 + 10 + dots.c + 8) = 7 dot 64$.

Une autre idée est d'utiliser des codes binaires de longueur 3.
Ceci donne une longueur de l'encodage de $M$ valant $3 dot 64$.

Pourrait-on utiliser un code plus court pour $phi(x)$ ?
Oui, c'est possible.
Mais pour cela, il faut changer de perspective.

*Qu'est ce qu'un code préfixe ?* Le codage binaire (l'ensemble des $phi(x)$ pour $x in cal(A)$) correspond a des feuilles dans un arbre binaire.

#figure(
  caption: [Représentation en arbre d'un code préfixe binaire],
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"))
    set-style(content: (frame: "rect", stroke: none, fill: white, padding: .05))


    let node(name, x, y, leaf: false) = {
      if not leaf {
        circle((x,y), radius: 0.1, name: name, stroke: blue)
      } else {
        circle((x,y), radius: 0.1, name: name, stroke: blue, fill: blue)
      }
    }

    node("r", 0, 10)
    node("0", -1, 9)
    node("1", 1, 9)
    node("00", -1.5, 8, leaf: true)
    node("01", -0.5, 8, leaf: true)
    node("10", 0.5, 8, leaf: true)
    node("11", 1.5, 8)
    node("110", 1.25, 7, leaf: true)
    node("111", 1.75, 7, leaf: true)

    line("r", "0", name: "r-0"); content("r-0.mid", $ mono(0) $)
    line("r", "1", name: "r-1"); content("r-1.mid", $ mono(1) $)

    line("0", "00", name: "0-00"); content("0-00.mid", $ mono(0) $)
    line("0", "01", name: "0-01"); content("0-01.mid", $ mono(1) $)
    line("1", "10", name: "1-10"); content("1-10.mid", $ mono(0) $)
    line("1", "11", name: "1-11"); content("1-11.mid", $ mono(1) $)

    line("11", "110", name: "11-110"); content("11-110.mid", $ mono(0) $)
    line("11", "111", name: "11-111"); content("11-111.mid", $ mono(1) $)


    node("r", 0, 10)
    node("0", -1, 9)
    node("1", 1, 9)
    node("00", -1.5, 8, leaf: true)
    node("01", -0.5, 8, leaf: true)
    node("10", 0.5, 8, leaf: true)
    node("11", 1.5, 8)
    node("110", 1.25, 7, leaf: true)
    node("111", 1.75, 7, leaf: true)
  })
)


Ainsi, l'image de $phi$ est ${ mono(111), mono(110), mono(01), mono(00), mono(10) }$, c'est l'ensemble des chemins partant de la racine jusqu'aux feuilles.
Comme le code cherché est optimal, il n'y a pas de nœud interne de degré 1.

Le problème #pbm[CodagePréfixeBinaireOptimal], noté CPBO, est défini comme
#pb-display(name: pbm[CPBO])[
  L'ensemble $E = { m_x | x in cal(A) }$ d'entiers 
][
  L'arbre $A_phi$ où $phi$ est le codage optimal
]

Pour résoudre ce problème, on utilise l'algorithme de Huffman. C'est un algorithme glouton.

#block(breakable: false)[
  #algo(name: [Huffman])[
    #algo-while[$"card" E >= 2$][
      Calculer $m_x$ et $m_y$ les deux plus petites valeurs dans $E$.

      $E <- (E without {m_x,m_y}) union {m_x + m_y}$
    ]

    #algo-return[l'arbre $A_phi$.]#footnote[Avec l'exemple, ça devrait être plus clair sur ce qu'il se passe ici.]
  ]
]

On code l'algorithme de Huffman avec un _tas_.
En effet, sans tas, on a une complexité en $bigO(n^2)$ alors qu'avec un tas, on a une complexité en $bigO(n log n)$.

#v(1fr)

#figure(
  cetz.canvas({
    import cetz.draw: *
    import cetz.tree: *

    set-style(stroke: (cap: "round", join: "round"))

    tree(
      ($ 64 $,
        $ 28 $,
        ($ 36 $,
          ($ 15 $,
            $ 7 $,
            $ 8 $
          ),
          ($ 21 $,
            ($ 11 $,
              $ 6 $,
              ($ 5 $,
                $ 1 $,
                $ 4 $,
              )
            ),
            $ 10 $
          )
        )
      ),
      draw-node: (node, ..) => {
        circle((), radius: .3, fill: blue, stroke: none)
        content((), text(white, node.content))
      },
      draw-edge: (from, to, prev, next, ..) => {
        let (a, b) = (from + ".center", to + ".center")

        line((a, 0.5, b), (b, 0.5, a), mark: (end: ">", scale: 0.5, fill: black))
      },
      grow: 1.5,
    )
  })
)
#v(1fr)

#pagebreak(weak: true)

#v(1fr)

#figure(
  caption: [Arbre de Huffman pour l'exemple précédent],
  cetz.canvas({
    import cetz.draw: *
    import cetz.tree: *

    set-style(stroke: (cap: "round", join: "round"))

    tree(
      (none,
        $ mono(a) $,
        (none,
          (none,
            $ mono(b) $,
            $ mono(g) $
          ),
          (none,
            (none,
              $ mono(d) $,
              (none,
                $ mono(e) $,
                $ mono(f) $,
              )
            ),
            $ mono(c) $
          )
        )
      ),
      draw-node: (node, ..) => {
        if node.content == none {
          circle((), radius: .1, fill: blue, stroke: none)
        } else {
          circle((), radius: .3, fill: blue, stroke: none)
          content((), text(white, node.content))
        }
      },
      draw-edge: (from, to, prev, next) => {
        let (a, b) = (from + ".center", to + ".center")
        let alpha1 = if prev.content == none { 0.2 } else { 0.35 }
        let alpha2 = if next.content == none { 0.2 } else { 0.35 }

        line((a, alpha1, b), (b, alpha2, a), mark: (end: ">", scale: 0.5, fill: black), name: from+to)


        group({
          set-style(content: (frame: "rect", stroke: none, fill: white, padding: .05))

          if prev.x > next.x {
            content(from+to+".mid", $ mono(0) $)
          } else {
            content(from+to+".mid", $ mono(1) $)
          }
        })
      },
      grow: 1.5,
    )
  })
)

#v(1fr)

Pour justifier la validité, on utilise un argument classique.
On construit une solution avec l'algorithme $A_"HUF"$ et une solution optimale $A_"OPT"$.
On va rapprocher $A_"OPT"$ de $A_"HUF"$.

On procède par induction sur la taille de l'arbre.
- Dans le cas de base, il n'y a qu'un nœud. L'arbre optimal est donc l'arbre de Huffman.
- Dans le cas général, supposons inverser deux éléments $x$ et $z$ (en rouge dans la figure ci-dessous).
  Alors, l'arbre n'est plus optimal. Or, par construction, l'arbre de Huffman vérifie cette propriété.

  De plus, en remplaçant le nœud $u$ par une feuille de symbole~"$x+y$" (en un seul caractère de l'alphabet), alors on obtient un arbre de taille plus petite.
  On peut donc appliquer l'hypothèse de récurrence pour en déduire que l'arbre optimal peut être construit à l'aide de l'algorithme de Huffman.

#figure(
  caption: [ Démonstration de l'optimalité de l'arbre de Huffman
    + #align(left)[Inversion de deux éléments dans l'arbre optimal ;]
    + #align(left)[Fusion de deux éléments dans l'arbre optimal.]
  ],
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"), mark: (fill: black))

    group({
      circle((0,0), name: "w",radius: 0.2, fill: none, stroke: none)
      circle((-1,-1), name: "z",radius: 0.2, fill: none, stroke: none)
      circle((+1,-1), name: "u",radius: 0.2, fill: none, stroke: none)
      circle((+0.5,-2), name: "x",radius: 0.2, fill: none, stroke: none)
      circle((+1.5,-2), name: "y",radius: 0.2, fill: none, stroke: none)

      content((0,1.5), $ dots.v $ + v(0.1cm), name: "d")
      content("u.east", h(0.5cm) + $u$)
      content("x.south", v(0.5cm) + $ x $)
      content("y.south", v(0.5cm) + $ y $)
      content("z.west", v(0.5cm) + $ z $)
      bezier-through("d.south",(0.2,0.5),"w.north", mark: (end: ">"))

      line("w", "z", mark: (end: ">"))
      line("w", "u", mark: (end: ">"))
      line("u", "x", mark: (end: ">"))
      line("u", "y", mark: (end: ">"))

      bezier-through("z.south", (0, -2.3), "x.south-west", mark: (symbol: ">", fill: red), stroke: (paint: red))

      circle("w",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("z",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("u",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("x",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("y",radius: 0.1, fill: blue, stroke: (paint: blue))

      content((0, 2.25), text(blue, $ (1) $))
    })

    translate((5, 0))

    group({
      circle((0,0), name: "w",radius: 0.2, fill: none, stroke: none)
      circle((-1,-1), name: "z",radius: 0.2, fill: none, stroke: none)
      circle((+1,-1), name: "u",radius: 0.2, fill: none, stroke: none)
      circle((+0.5,-2), name: "x",radius: 0.2, fill: none, stroke: none)
      circle((+1.5,-2), name: "y",radius: 0.2, fill: none, stroke: none)

      content((0,1.5), $ dots.v $ + v(0.1cm), name: "d")
      content("u.east", h(0.5cm) + $u$)
      content("x.south", v(0.5cm) + $ x $, name: "xlabel")
      content("y.south", v(0.5cm) + $ y $ + v(0.2cm), name: "ylabel")
      content("z.west", v(0.5cm) + $ z $)
      bezier-through("d.south",(0.2,0.5),"w.north", mark: (end: ">"))

      rect((vertical: "u.north", horizontal: "x.west"), (vertical: "ylabel.south", horizontal: "y.east"), name: "xy")

      line("w", "z", mark: (end: ">"))
      line("w", ("xy.north", 0.1, "w"), mark: (end: ">"))
      line("u", "x", mark: (end: ">"))
      line("u", "y", mark: (end: ">"))

      content("xy.south", v(0.5cm) + ["$x+y$"])


      circle("w",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("z",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("u",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("x",radius: 0.1, fill: blue, stroke: (paint: blue))
      circle("y",radius: 0.1, fill: blue, stroke: (paint: blue))

      content((0, 2.25), text(blue, $ (2) $))
    })
  })
)


*Quelles sont les limites de la compression ?*
Une borne inférieure pour la longueur d'un codage binaire d'un mot $M$ de longueur $ell$ avec pour occurrences $(m_x)_(x in cal(A))$ est $ log_2 underbrace((ell! / (product_(x in cal(A)) m_x !)), "Nombre d'anagrammes" \ "de" M) $

Et asymptotiquement ?
On définit les fréquences des lettres $ f = ( f_x := m_x / ell mid(|) x in cal(A) ). $

Le nombre d'anagrammes de $M$ est donc $~ 2^(upright(H)(f) ell)$ (à un terme polynômial près), où $upright(H)(f) = sum_(x in cal(A)) - f_x log_2 f_x$ est le "coefficient d'allongement" de $M$ (vu comme une borne inférieure) : pour passer d'un mot à son encodé, la longueur est multiplié par $upright(H)(f)$.
On nomme~$upright(H)(f)$ l'_entropie de Shannon_.

Avec les fréquences $f = (1/2, 1/2)$, on a $upright(H)(f) = 1$.
"La masse des mots binaires est concentré sur équiréparti."

Avec un mot binaire de fréquences $f = (0.49, 0.51)$, on a $upright(H)(f) < 1$.
En effet, le nombre de mots binaires avec plus de $0.49$ fois "$mono(0)$" est équivalent à $2^(upright(H)(f) ell)$.
Ainsi, si on tire un mot binaire aléatoire, la probabilité que le nombre de $mono(0)$ est inférieur à $0.49 ell$ est équivalente à 
$ 2^(upright(H)(f) ell) / 2^ell = 1/(2^((1-upright(H)(f)) ell)), $
on retrouve le théorème de #sc[Chernoff].


== Arbre couvrant de poids minimum.

=== Arbre couvrant.

#definition[
  Soit $G = (V,E)$ un graphe connexe.
  On appelle _arbre couvrant_ un ensemble $A subset.eq E$ tel que $A$ est connexe et acyclique.
]

#proposition[
  Tout graphe connexe possède un arbre couvrant.
]

#proof[
  On se propose plusieurs preuves.
  + _Par induction._
    On considère un $(u-v)$-chemin $P$ glouton.
    Par construction, tous les voisins de $v$ sont dans $P$.
    Ainsi, $G without { v }$ est un graphe connexe.
    En effet, si $G without { v }$ n'est pas connexe, on a donc une partition en composantes connexes, et alors $P$ est totalement inclus dans une composante connexe.
    Mais, $G$ ne serait donc pas connexe, ce qui est absurde.

    Ainsi, par hypothèse d'indiction, il existe un arbre $A'$ couvrant $G without {v}$.
    On pose $A = A' union {v w}$, où $w$ est un voisin de $v$.
    L'ensemble $A$ est un arbre couvrant de $G$.
  + On considère un ensemble $A$ connexe minimal.
  + On considère un ensemble $A$ acyclique maximal. #label("acpm-proof1-c")
]

Remarquons que le nombre d'arêtes de $A$, un arbre couvrant, est~$n - 1$ où $n = |V|$.

Comment _calculer efficacement_ un arbre couvrant ?
- On peut utiliser un arbre de parcours, ceci aurait une complexité en $bigO(n+m)$.
- Dans le cas d'un algorithme _online_, où les arêtes sont reçues une à une, et la décision doit se faire à chaque arête, on doit utiliser une structure adaptée.

Comment décider si une arête $x y$ reçue forme un cycle ou pas ?
Comment mettre à jour les composantes déjà obtenues ?

Pour cela, on utilise une structure _union-find_ (_unir & trouver_) :
- $C(x)$ désigne le représentant de la composante de $x$ ;
- $"comp"(x)$ désigne l'ensemble des sommets de la composante de $x$, lorsque $x$ est le représentant.

#algo(name: [Arbre couvrant])[
  $A <- emptyset$

  #algo-for[*_tout_* $v in V$][
    $C(v) <- v$\
    $"comp"(v) <- v$)
  ]

  #algo-for([*_tout_* $x y in E$])[
    #algo-if($c(x) != c(y)$)[
      $A <- A union {x y}$\
      $"comp"(C(x)) <- "comp"(C(x)) union "comp"(C(y))$\
      $C <- "comp"(C(y))$\
      #algo-for[_*tout*_ $z in C$][
        $C(z) <- C(x)$
      ]
    ]
  ]

  #algo-return[$A$]
]

La validité de l'algorithme est assurée par la preuve #link(label("acpm-proof1-c"), text(blue)[(3)]) précédente.

La complexité de cet algorithme est, en pire cas, $bigO(m + n^2)$.
Ce pire cas arrive, par exemple, sur le graphe :
- avec pour sommets ${1,2,3,4,5,6}$,
- et pour arêtes ${21, 32, 43, 54, 65}$.
Ceci renomme $binom(n,2) = bigO(n^2)$ sommets.

Est-ce que le cas moyen est en $bigO(m+n^2)$ ?
Qu'en est-il si les arêtes de $E$ sont tirées aléatoirement ?

L'intuition est que, pour une étape intermédiaire, les composantes sont globalement de même taille.
Mais, on remarque que, dans la pratique, il y a une "composante géante".
On essaie d'optimiser l'algorithme pour éviter de recopier toute la composante géante dans une plus petite composante.

#algo(name: [Arbre couvrant, plus optimisé])[
  $A <- emptyset$

  #algo-for[*_tout_* $v in V$][
    $C(v) <- v$\
    $"comp"(v) <- v$)
  ]

  #algo-for([*_tout_* $x y in E$])[
    #algo-if($c(x) != c(y)$)[
      #algo-if[$|"comp"(C(x))| < |"comp"(C(y))|$][
        Échanger $x$ et $y$.
      ]

      $A <- A union {x y}$\
      $"comp"(C(x)) <- "comp"(C(x)) union "comp"(C(y))$\
      $C <- "comp"(C(y))$\
      #algo-for[_*tout*_ $z in C$][
        $C(z) <- C(x)$
      ]
    ]
  ]

  #algo-return[$A$]
]

La complexité devient $bigO(m + n log n)$ !
Ceci vient du fait qu'un sommet $z$ dans la boucle "*Pour tout*" intérieure n'est renommé qu'au plus $log_2 n$ fois.
Ainsi, la taille de sa composante double à chaque fois.

#remark[
  - La gestion des composantes peut se faire en $bigO(n log^star n)$ et même encore mieux (_$triangle.r$ structure Union-Find_).
  - Codez l'algorithme ! Et observez l'apparition de la composante géante (_$triangle.r$ Erdős–Rényi_). Commenter et décommenter la condition sur la taille des composantes (passage de $n^2$ à~$n log n$).
]

=== Arbre couvrant de poids minimal.

On considère le problème #pbm[Arbre Couvrant de Poids Minimal] (abrégé en ACPM) :
#pb-display(name: pbm[ACPM])[
  Un graphe $G = (V,E)$ et une fonction de pondération $w : E -> NN$
][
  Un arbre couvrant $A$ avec $w(A)$ minimal.
]

#figure(
  caption: [Un exemple d'arbre couvrant de poids minimal],
  cetz.canvas({
    import cetz.draw: *

    circle((0,0), radius: 0.2, name: "A", fill: none, stroke: none)
    circle((0,2), radius: 0.2, name: "B", fill: none, stroke: none)
    circle((2,0), radius: 0.2, name: "C", fill: none, stroke: none)
    circle((2,2), radius: 0.2, name: "D", fill: none, stroke: none)

    circle("A", radius: 0.1, fill: blue, stroke: none)
    circle("B", radius: 0.1, fill: blue, stroke: none)
    circle("C", radius: 0.1, fill: blue, stroke: none)
    circle("D", radius: 0.1, fill: blue, stroke: none)

    set-style(content: (frame: "rect", stroke: none, fill: white, padding: .05))
    set-style(stroke: (cap: "round", join: "round"), mark: (fill: black))

    line("A", "B", name: "AB"); content("AB.mid", $ 1 $)
    line("A", "C", name: "AC"); content("AC.mid", $ 3 $)
    line("A", "D", name: "AD"); content((name: "AD", anchor: 75%), $ 5 $)
    line("B", "C", name: "BC"); content((name: "BC", anchor: 25%), $ 2 $)
    line("B", "D", name: "BD"); content("BD.mid", $ 4 $)
    line("C", "D", name: "CD"); content("CD.mid", $ 6 $)

    content((1,-1/2))[Graphe initial]

    line((3,1), (4, 1), mark: (end: ">", fill: black))

    translate((5, 0))

    circle((0,0), radius: 0.2, name: "A", fill: none, stroke: none)
    circle((0,2), radius: 0.2, name: "B", fill: none, stroke: none)
    circle((2,0), radius: 0.2, name: "C", fill: none, stroke: none)
    circle((2,2), radius: 0.2, name: "D", fill: none, stroke: none)

    circle("A", radius: 0.1, fill: blue, stroke: none)
    circle("B", radius: 0.1, fill: blue, stroke: none)
    circle("C", radius: 0.1, fill: blue, stroke: none)
    circle("D", radius: 0.1, fill: blue, stroke: none)

    set-style(content: (frame: "rect", stroke: none, fill: white, padding: .05))
    set-style(stroke: (cap: "round", join: "round"), mark: (fill: black))

    line("A", "B", name: "AB"); content("AB.mid", $ 1 $)
    //line("A", "C", name: "AC"); content("AC.mid", $ 3 $)
    //line("A", "D", name: "AD"); content((name: "AD", anchor: 75%), $ 5 $)
    line("B", "C", name: "BC"); content((name: "BC", anchor: 50%), $ 2 $)
    line("B", "D", name: "BD"); content("BD.mid", $ 4 $)
    //line("C", "D", name: "CD"); content("CD.mid", $ 6 $)

    content((1,-1/2))[ACPM]
  })
)

On résout ce problème à l'aide de l'algorithme de Kruskal.

#algo(name: [Algorithme de Kruskal])[
  On trie les arêtes de $E$ par ordre croissant de pondération.\
  On calcule un arbre couvrant avec l'algorithme précédent.
]

Justifions de la validité de l'algorithme.
Soient $A$ et $A'$ deux arbres couvrants de $G$.

#proposition[
  Quel que soit l'arête $e in A without A'$, il existe $e' in A' without A$ tel que l'ensemble $(A without {e}) union {e'}$ soit un arbre couvrant.
  C'est un échange de $e$ par $e'$.
]

#proof[
  On ajoute l'arête $e$ à $A'$.
  Ceci, comme $A'$ était un arbre couvrant, implique qu'on crée un cycle $P union {e}$, avec $P subset.eq A'$.

  (La figure sera terminée plus tard...) // TODO(Hugo) : FINIR LA FIGURE (IMG_1608.HEIC) -> deux figures

  #figure(
    cetz.canvas({
      import cetz.draw: *

      let bezier-through-all(..args) = {
        let points = args.pos()
        let others = args.named()

        let a1 = points.slice(0)
        let a2 = points.slice(1)
        let a3 = points.slice(2)

        for (a,b,c) in a1.zip(a2, a3) {
          bezier-through(a,b,c, ..others)
        }
      }

      bezier-through-all((-1,1),(-1.2,0.5),(0,0),(1.2,0.5),(1,-1))
    })
  )

  Soient $V_1$ et $V_2$ les deux composantes connexes de $A without {e}$.
  Par le cycle $P$, on sait qu'il existe une arête $e'$ de $P$ qui va d'un sommet dans $V_1$ à un sommet dans $V_2$.

  Ainsi, $A_1 = (A without {e}) union {e'}$ est un arbre, et il est couvrant par construction.
]

Ainsi, $A_1 = (A without {e}) union {e'}$ et $A'_1 = (A without {e'}) union {e}$ sont deux arbres couvrants.
Une façon de le voir, c'est que $A_1$ et $A'_1$ sont plus proches que $A$ et $A'$ ne l'étaient.

En effet, on peut poser $"dist"(A,A') = (A symd A')/2 = d$ et remarquer que l'on a $"dist"(A_1,A') = d - 1$.

Ce que l'on construit est une _géodésique_ dans un certain espace.

Quel est l'espace ambiant ?
C'est l'ensemble des arbres couvrants.
Deux arbres sont voisins s'ils diffèrent de deux arêtes.
On veut minimiser $w$ dans cet espace.

Dans le cas continu, la globalité d'un minimum local est assurée par la _convexité_ de la fonction considérée.

#figure(
  caption: [Globalité (ou non) d'un minimum local],
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"), mark: (fill: black))

    plot.plot(size: (3,3), x-tick-step: none, y-tick-step: none, axis-style: "school-book", plot-style: (stroke: (paint: blue)), name: "plot-not-conv", {
      plot.add(domain: (-1.5, 1), t => (t + 2, t*t*t * (1 + 2 * t) - 2 * t * t))
      plot.add-anchor("min-glo", (2-0.9348,-1.0373))
      plot.add-anchor("min-loc", (2+0.5630,-0.2545))
    })

    circle("plot-not-conv.min-glo", radius: 0.07, fill: purple, stroke: none)
    content("plot-not-conv.min-glo", text(purple, align(center)[\ ~\ minimum\ _global_]))

    circle("plot-not-conv.min-loc", radius: 0.07, fill: purple, stroke: none)
    content("plot-not-conv.min-loc", text(purple, align(center)[\ ~\ minimum\ _local_]))

    content((3/2,-1.5))[Fonction #underline[non convexe]]

    translate((6, 0))

    plot.plot(size: (3,3), x-tick-step: none, y-tick-step: none, axis-style: "school-book", plot-style: (stroke: (paint: blue)), name: "plot-not-conv", {
      plot.add(domain: (-1, 0.7), t => (t + 2, t*t*t * (1 + 2 * t) + 0.5 * t))
      plot.add-anchor("min-glo", (2-0.5583,-0.2589))
    })

    circle("plot-not-conv.min-glo", radius: 0.07, fill: purple, stroke: none)
    content("plot-not-conv.min-glo", text(purple, align(center)[\ ~\ minimum\ _local_ = _global_]))

    content((3/2,-1.5))[Fonction #underline[convexe]]
  })
)


#proposition[
  Si l'arbre $A_"LOC"$ est un minimum local#footnote[
    Quel que soit $A'$ voisin de $A$ ($d(A,A') = 1$), on a $w(A') >= w(A)$.
  ]
  alors c'est un minimum global.
]

#proof[
  Considérons $A_"GLO"$ le minimum sur tous les arbres de $w$.
  Si $A_"GLO" != A_"LOC"$, alors il existe $e in A_"LOC"$ et $e' in A_"GLO"$ tels que 
  $ A_1 = (A_"LOC" without {e}) union {e'} quad quad "et" quad quad A_2 = (A_"GLO" without {e'}) union {e} $
  soient des arbres.

  Par propriétés de minimum local, $w(A_"LOC") <= w(A_1)$, d'où $w(e') >= w(e)$.
  D'où, $w(A_2) <= w(A_"GLO")$, on en déduit que $A_2$ est aussi un minimum global.
  Mais, $d(A_"GLO", A_"LOC")$ a diminuée.
  De proche en proche, on obtient que $w(A_"LOC")  = w(A_"GLO")$.
]

L'idée est la même que pour l'algorithme de Huffman : pour démontrer l'optimalité de la solution, on _rapproche_ la solution optimale au résultat de l'algorithme.

#proposition[
  L'algorithme de Kruskal retourne un minimum local.
]

#proof[
  Supposons que $A_"KRU"$ soit retourné et que $A' = (A_"KRU" without {e}) union {e'}$ soit un arbre voisin de $A_"KRU"$.
  C'est qu'au moment du choix possible de $e'$, l'arête a été rejetée.

  Ses extrémités étaient à cette étape dans la même composante connexe.
  Le chemin $P$ était déjà dans $A$, par le choix glouton (et le pré-traitement du tri des arêtes), on a $w(e) <=  w(e')$.

  Ceci permet d'en déduire que $w(A_"KRU") <= w(A')$.
]

On en déduit de la validité de l'algorithme de Kruskal.

== Algorithme GLOUTON.

Soit $H = (V, S)$ un _hypergraphe_, _i.e._ $S subset.eq 2^V$ où $S$ peut être vu comme l'ensemble des solutions admissibles d'un problème.
On suppose $S$ donné sous forme d'oracle : qui peut répondre en $bigO(1)$ à une question "$X in S$ ?" lorsque $X subset.eq V$.

#pb-display(name: pbm[Maximisation])[
  $H = (V,S)$ un oracle et $w : V -> NN$
][
  Un sous ensemble $X in S$ tel que $w(X)$ est maximal.
]

Cette définition est très (trop) générale !

#algo(name: [L'algorithme GLOUTON])[
  $A <- emptyset$

  Trier $V$ par ordre décroissant de $w$.

  #algo-for[_*tout*_ $v in V$][
    #algo-if[
      $A union {v} in S$
    ][
      $A <- A union {v}$
    ]
  ]

  #algo-return[
    $A$
  ]
]

- Pour l'algorithme de Kruskal, si $V$ est l'ensemble des arêtes d'un graphe et $S subset.eq 2^V$ est l'ensemble des parties acycliques, alors l'algorithme GLOUTON retourne bien un arbre de poids maximal.

#example(name: [Un autre exemple])[
  Considérons une matrice $bold(M)$ de taille $n times m$ sur un corps $KK$.
  On pose $V$ l'ensemble des vecterus colonnes, et 
  $ S = { X subset.eq V | X "est une famille libre" }. $
  Alors, quelle que soit la pondération $w : V -> NN$, l'algorithme GLOUTON retourne une famille libre maximisant $w$.

  On pourra démontrer cela en imitant la preuve de validité de l'algorithme Kruskal.
]

Dans l'exemple, l'algorithme Kruskal est un cas particulier : du graphe $G = (V,E)$ avec $n = |V|$ et $m = |E|$, on associe une matrice d'incidence $bold(I)_G = (i_(v,e))_(v in V, e in E)$ où $
  i_(v,e) = cases(
    0 quad &"si" v in.not e,
    1 quad &"si" v in e.
  )
$

Par exemple, pour le graphe ci-dessus// graphe 1--2--3--4 avec 1--3 et 2--4 // TODO(Hugo) : Ajouter la figure
on associe la matrice 
$ mat(
    1, 1, 1, 0, 0, 0;
    1, 0, 0, 1, 1, 0;
    0, 1, 0, 1, 0, 1;
    0, 0, 1, 0, 1, 1
  ), $
appelée _matrice d'incidence_.

Alors, on a l'équivalence ci-dessous.

#proposition[
  On a $S subset.eq E$ est acyclique si, et seulement si, $S$ (vu comme un ensemble de colonnes) est libre dans $FF_2$.
]

#proof[
  - "$<==$". Par contraposée, supposons $S$ non acyclique. Il existe donc un cycle $ x_1 x_2, x_2 x_3, ..., x_k x_1. $
    Mais, ceci implique que la somme des colonnes $x_1 x_2$, ..., $x_k, x_1$ vaut 0.
    D'où, la famille $S$ n'est pas libre.
  - "$==>$". Par induction sur le cardinal de $S$. Si $S$ est acyclique c'est donc une forêt. Alors il existe un arbre $A$ (le cas $S$ vide est trivial) et donc une feuille $x$ dans l'arbre acyclique $A$. On applique l'hypothèse d'induction sur $A without {x}$.
]

En fait, on peut même généraliser à un problème qui n'est pas ACPM.

#proposition[
  L'algorithme GLOUTON retourne toujours une base de poids minimal lorsque $w$ est une fonction de poids sur les colonnes d'une matrice.
]

#proof[
  Il suffit de démontrer que, pour toutes bases $cal(B) != cal(B')$, et pour tout $x in cal(B) without cal(B)'$, il existe~$x' in cal(B)' without cal(B)$ tel que $(cal(B) union {x'}) without {x}$ et $(cal(B)' union {x}) without {x'}$ soient deux bases.
]

#remark[
  On peut réaliser une même construction sur $RR$, *mais* on représente chaque arête par une arête orientée.
  // TODO(Hugo) : Voir ce qui se passe ici...
]

#remark(name: [Digression sur la simple connexité])[
  Le graphe $G$ est connexe si, et seulement si, $"rg"(bold(I)_G) = n - 1$.
]

=== Matroïdes.

#definition[
  On dit que $H = (V,S)$ est un matroïde si :
  + $S != emptyset$ ;
    #h(1fr) "non-vacuité"
  + $forall X in S, forall Y subset.eq X, Y in S$ ;
    #h(1fr) "clôture"
  + $forall X, Y in S, |Y| > |X| ==> exists y in Y without X, X union {y} in S$. \
    #h(1fr) "échange"
]

Par exemple, le point #text(blue)[(3)]) est vérifié par les familles libres.

#theorem[
  L'algorithme GLOUTON sur $H$ retourne une solution optimal (quel que soit $w$) si, et seulement si, $H$ est un matroïde.
]

Ce théorème est génial.
Pourquoi ?
Il lie la "structure" d'un ensemble (algébrique) à un "modèle de calcul" (combinatoire).

Un résultat qui a ce même lien est l'équivalence entre automates finis (modèle de calcul) et expressions régulières (structure).

#example[
  Voici quelques exemples de matroïdes :
  + le _matroïde graphique_ : les acycliques dans un graphe ;
  + le _matroïde vectoriel_ : les familles livres dans une matrice ;
  + le _matroïde uniforme_ : pour $k$ fixé, 
    $ S = { X subset.eq V mid(|) |X| <= k }. $
  + le _matroïde de partition_ :
    $ V  = V_1 union.dot V_2 union.dot dots.c union.dot V_ell\
      S = { X subset.eq V mid(|) |X inter V_i| <= t_i, forall i in [| 1, ell |] }. $
]

#remark[
  - Certains matroïdes sont _représentables_ comme matroïdes vectoriels mais il en existe des _non-représentables_.
  - Une étape de plus, l'intersection : le problème
    #pb-display(loose: true)[
      Deux matroïdes $S_1$ et $S_2$ sur $V$ et un poids~$w : V -> NN$
    ][
      Un sous-ensemble $X$ tel que $X in S_1 inter S_2$ et~$w(X)$ maximal
    ]
    est résolvable en temps polynomial.
]

#example[
  On considère un graphe biparti.
  Le problème du couplage maximal (aussi appelé Couplage Parfait Biparti) peut se résoudre en temps polynomial.
  En effet, $X subset.eq E$ s'exprime sous forme d'intersection de deux matroïdes de partitions sur $A$ et $B$.
  // TODO(Hugo) : Ajouter figure
]

Et si on ajoute une autre intersection ?
Le problème est $bold("NP")$-dur.

#example[
  // TODO(Hugo) : Faire le graphe biparti G' = G U. G (alpha-renommé)
  On se donne un graphe biparti $G'$ comme construit dans la figure ci-dessus.
  On se donne plusieurs contraintes :
  + le degré est inférieur à 2 à gauche ;
  + le degré est inférieur à 2 à droite ;
  + l'ensemble des arêtes est acyclique.

  Le couplage maximal du graphe $G'$ est un chemin de longueur maximal qui passe par tous les points.
  On se réduit donc au problème _Travelling Sales Person_ (TSP).
]

= $bold("NP")$-complétude.

== La classe $bold("NP")$, définition intuitive.


Un problème est dans $bold("NP")$ s'il existe un algorithme polyomial $cal(A)$ et une constante $d$ telle que $X$ est vrai _ssi_ il existe un certificat $C$ de taille au plus $|X|^d$ tel que $cal(A)(X,C)$ est vrai.

En pratique : on sait facilement vérifier qu'une instance est vrai si on peut en fournir la preuve (en taille polynomial).
La preuve, c'est la donnée de la "solution".

C'est en général très facile.
#let NP = math.bold("NP")
#let coNP = math.bold("co-NP")
#let PP = math.bold(math.upright[P])

Par exemple, le problème 
#pb-display(name: pbm[Somme])[
  $S$ et $n_1, ..., n_ell$.
][
  #sc[Vrai] s'il existe $I subset.eq [ell]$ telle que $sum_(i in I) n_i = S$.
]
est dans $NP$ car il suffit de donner $I$ comme certificat (ici l'algorithme $A$ est juste la somme et le teste d'égalité à $S$).


Le problème
#pb-display(name: pbm[CPB])[
  Un graphe $G = (V, E)$ biparti
][
  #sc[Vrai] s'il existe un couplage parfait
]
est dans $bold("NP")$. En effet, il suffit de donner le couplage comme certificat.

Le problème 
#pb-display(name: pbm[Premier])[
  Un entier $n$
][
  #sc[Vrai] si $n$ est premier.
]
est dans $bold("NP")$, mais c'est bien moins évident.
Pour ce problème, trouver un certificat de taille polynomial est bien plus complexe (la représentation de $n$ est en $log_2(n)$ donc un $bigO(n)$ est en réalité _exponentiel_ en la taille de $n$).

Pour trouver un certificat, on commence par analyser le _théorème de Lucas_ : un entier $n$ est premier si, et seulement s'il existe $a in NN$ tel que 
$ a^(n-1) equiv 1 med (mod n) quad "et" quad forall q "premier divisant" n - 1, a^((n-1)\/ q) equiv.not 1 med (mod n) $

(Justification plus tard...)

#remark[
  La classe $NP$ est biaisée vers #sc[Vrai].
  Mais, on aurait pu la biaiser vers #sc[Faux] et on obtiendrai la classe $bold("co-NP")$.
]

Par exemple, le problème 
#pb-display(name: pbm[sat])[
  Une formule $phi$ en forme normale conjonctive de variables $x_1, ..., x_n$.
][
  #sc[Vrai] si on peut affecter les $x_i$ afin de rentre $phi$ vraie (_*satisfaire*_ $phi$)
]
est clairement dans $NP$ car il suffit de donner la solution.
*Mais mais mais*, il semble difficile d'obtenir un certificat de #sc[Faux] de taille polynomiale (et même de taille $2^smallo(n)$).

== Les deux (vraies) définitions de $NP$.

On commence par les automates finis.
Ils sont puissants, mais restent assez limités : ${mono(0)^n mono(1)^n | n in NN}$ n'est pas rationnel.
Turing propose de donner un ruban mémoire à l'automate où il pourra lire, écrire et déplacer une tête de lecture.

Au début du calcul, un mot $M in { mono(0), mono(1) }^star$ est inscrit sur le ruban.
Le reste du ruban est rempli de caractères vides "$square$".
Et, au cours des changements d'états, si l'automate arrive dans $q_upright(A)$ un état acceptant, alors $M$ est accepté ; s'il arrive dans $q_upright(R)$ (état rejetant) alors $M$ est rejeté.

#example[
  Pour le langage ${mono(0)^n mono(1)^n | n in NN}$, on construit la machine de Turing $cal(M)$ :
  #figure(
    cetz.canvas({
      import cetz.draw: *

      circle((0, 0),  radius: 0.3, name: "q0", stroke: none)
      circle((4, 0),  radius: 0.3, name: "q1", stroke: none)
      circle((4, -4), radius: 0.3, name: "q2", stroke: none)
      circle((0, -4), radius: 0.3, name: "q3", stroke: none)
      circle((2, 2),  radius: 0.3, name: "qA", stroke: none)
      circle((2, -2), radius: 0.3, name: "qR", stroke: none)
      circle("q0", radius: 0.25, fill: blue, stroke: none)
      circle("q1", radius: 0.25, fill: blue, stroke: none)
      circle("q2", radius: 0.25, fill: blue, stroke: none)
      circle("q3", radius: 0.25, fill: blue, stroke: none)
      circle("qA", radius: 0.25, fill: blue, stroke: none)
      circle("qR", radius: 0.25, fill: blue, stroke: none)
      content("q0",$ q_0 $)
      content("q1",$ q_1 $)
      content("q2",$ q_2 $)
      content("q3",$ q_3 $)
      content("qA",$ q_upright(A) $)
      content("qR",$ q_upright(R) $)

      set-style(content: (frame: "rect", stroke: none, fill: white, padding: .05), mark: (fill: black))
      set-style(stroke: (cap: "round", join: "round"))

      line("q0", (rel: (-1, -1)), mark: (start: ">"))

      line("q0", "qA", mark: (end: ">"), name: "l0")
      content("l0.mid")[$square -> upright(D)$]

      line("q0", "q1", mark: (end: ">"), name: "l1")
      content("l1.mid")[$mono(0) -> square, upright(D)$]

      bezier-through("q1.north", (rel: (0.5, 0.5)), "q1.east", mark: (end: ">"), name: "l2")
      content("l2.mid")[$mono(0) -> square, upright(D)$]

      line("q1", "q2", mark: (end: ">"), name: "l3")
      content("l3.mid")[$square -> upright(G)$]

      line("q2", "qR", mark: (end: ">"), name: "l4")
      content("l4.mid")[$mono(0) -> upright(D)$]

      line("q0", "qR", mark: (end: ">"), name: "l5")
      content("l5.mid")[$mono(1) -> upright(D)$]

      line("q2", "q3", mark: (end: ">"), name: "l6")
      content("l6.mid")[$mono(1) -> square, upright(D)$]

      bezier-through("q3.south", (rel: (-0.5, -0.5)), "q3.west", mark: (end: ">"), name: "l7")
      content("l7.mid")[$mono(0),mono(1) -> upright(G)$]

      line("q3", "q0", mark: (end: ">"), name: "l8")
      content("l8.mid")[$square -> upright(D)$]
    })
  )

  Ainsi, $cal(M)$ décide $L$, qu'on note $cal(L)(cal(M)) = L$.
]

#definition[
  On dit que $cal(M)$ _décide_ $L$ si :
  - tous les calculs sur toutes les entrées terminent ;
  - $M$ _est accepté_ par $cal(M)$ si et seulement si $M in L$.
]

//#figure(
  // TODO(Hugo) : Figure "puits" des langages
//)


Si tous les calculs terminent en temps polynomial alors $cal(M)$ est une machine de Turing polynomiale.
Un langage $L$ est dans la classe $PP$ s'il existe une machine de Turing polynomiale qui décide $L$.

Dans les définitions suivantes, on simplifie avec $cal(A) = {mono(0), mono(1)}$ comme alphabet.

#definition(name: [version 1])[
  On a $L in NP$ s'il existe un polynôme $p$ et un langage $L' in PP$ tels que :
  $ L = { M in cal(A)^star mid(|) exists c in cal(A)^star, cases(|c| <= p(|M|), M dot C in L', delim: "[")  }. $
]

On ajoute le non déterministe aux machines de Turing : on autorise d'avoir deux transitions comme dans la figure ci-dessous.
#figure(
  cetz.canvas({
    import cetz.draw: *

    set-style(stroke: (cap: "round", join: "round"))

    circle((2, -1.5), radius: 0.3, name: "q0", stroke: none)
    circle((4,  0), radius: 0.3, name: "q1", stroke: none)
    circle((4, -3), radius: 0.3, name: "q2", stroke: none)
    circle("q0", radius: 0.25, fill: blue, stroke: none)
    content("q0",$ q_i $)

    set-style(content: (frame: "rect", stroke: none, fill: white, padding: .05), mark: (fill: black))

    line("q0", "q1", mark: (end: ">"), name: "l1")
    line("q0", "q2", mark: (end: ">"), name: "l2")
    
    content("l1.mid", $0 -> upright(D)$)
    content("l2.mid", $0 -> upright(G)$)
  })
)

On exige toujours que tous les calculs terminent.
Un mot $M$ est _accepté_ par une machine de Turing non déterministe s'il existe un chemin vers $q_upright(A)$.

De plus, si les chemins terminent en un nombre polynomial d'étapes en la taille de l'entrée, on parle de 
machine de Turing non déterministe polynomiale.



#definition(name: [version 2])[
  On a $L in NP$ s'il existe une machine de Turing non déterministe polynomiale qui décide $L$.
]

#theorem[
  Les deux définitions sont équivalentes.
]

#proof(name: [Esquisse de preuve...])[
  - On utilise le non déterminisme pour générer un certificat et on teste ce certificat sur la machine de vérification.
  - Le certificat correspond à une suite de choix qui mène à $q_upright(A)$.
]

#remark[
  On remarque que $L in coNP$ si et seulement si $cal(A)^star without L in NP$.
  Une classe intéressante est $coNP inter NP$.#footnote[Aller voir #link("https://upload.wikimedia.org/wikipedia/commons/0/0d/Jack.Edmonds.jpg")[la photo de Jack Edmonds] sur Wikipedia.]
]

== Réductions.

#definition[
  Un langage $L$ est dit polynomialement réductible à un langage~$L'$ s'il existe une fonction $f$ calculable en temps polynomial de $cal(A)^star -> cal(A)^star$, tel que 
  $ M in L "si, et seulement si" f(M) in L'. $
  C'est aussi appelé une _many-to-one reduction_ ou une _Karp reduction_.
]

Intuitivement, un problème $P$ se réduit à un problème $Q$ s'il existe un algorithme polynomial qui transforme les instances de $P$ en instances de $Q$ en respectant #sc[Vrai]/#sc[Faux].

#remark[
  Si $L' in PP$ alors $L in PP$. \
  Si $L' in NP$ alors $L in NP$.
]

Intuitivement, $Q$ est _au moins aussi difficile_ que $P$.

On note $L <= L'$ et cela correspond à un ordre partiel de difficultés des langages (au détail de l'anti-symétrie, par exemple tous les problèmes de $PP$ sont équivalents).#footnote[La composition est assurée en composant les deux algorithmes polynomiaux.]

On peut aussi définir les réductions Turing, où l'on peut utiliser plus d'une fois un oracle sur $L$.
Maison ne verra que des réductions Karp dans ce cours.

#theorem(name: [Cook-Levin])[
  Il existe $L' in NP$ tel que, pour tout $L in NP$, on a $L <= L'$.

  En particulier, Cook a montré que #pbm[sat] convient pour $L'$, un tel langage $L'$ est dit _$NP$-complet_.
]

L'intérêt est :
- si vous n'arrivez pas à trouver un algorithme polynomial pour un problème $P_L$ alors essayez de montrer qu'il est $NP$-complet ;
- pour ce faire, on cherche à réduire #pbm[sat] en $L$ en transformant les instantes.

== Quelques réductions classiques.

#h(1fr)#algo-comment[ Liste des $21$ problèmes $NP$-complets de Karp. ]

#pb-display(name: pbm[3sat])[
  Une formule $phi$ sous forme normale conjonctive dont toutes les clauses ont 3 littéraux.
][
  #sc[Vrai] si $phi$ est satisfiable.
]

#proposition[ #pbm[3-sat] est $NP$-complet. ]
#proof[
  On montre que $#pbm[sat] <= #pbm[3-sat]$.
  On se donne une formule $F = C_1 and dots.c and C_m$ de #pbm[sat] en variables $x_1, ..., x_n$.
  On veut transformer $F$ en une formule équivalente de #pbm[3-sat].

  On suppose $C_1 = ell_1 or dots.c or ell_t$ et on va exprimer $C_1$ comme une conjonction de taille inférieure à 3.
  - Si $t <= 3$, on ne change pas $C_1$ ;
  - Si $t > 3$, on va créer $t - 3$ nouvelles variables $y_1, ..., y_(t - 3)$ et on remplace la clause $C_1$ par :
    $ C'_1 := (ell_1 or ell_2 or y_1) and (not y_1 or y_2 or ell_3) and (not y_2 or y_3 or ell_4) and dots.c and (not y_(t-4) or y_(t-3) or ell_(t-1)) and (not y_(t-3) or y_(t-1) or ell_t). $

  On applique la même transformation pour tous les $C_i$ (à chaque fois avec des nouvelles variables).
  On obtient finalement une formule de #pbm[3-sat] notée $F'$.

  De plus $F$ est satisfiable si, et seulement si $F'$ est satisfiable.
  En effet, on ne peut  pas satisfaire~$C'_1$ avec uniquement les $y_i$, car on aurait $y_1 = #sc[Vrai]$ et $y_(t-3) = #sc[Faux]$ et donc il existerait $j$ tel que~$y_j = #sc[Vrai]$ mais $y_(j+1) = #sc[Faux]$.
  Or, pour satisfaire $ell_(j+2) = #sc[Vrai]$.
  On a donc prouvé la réciproque.
  Le sens direct se réalise bien plus simplement.
]

#pb-display(name: pbm[clique])[
  Un graphe $G = (V, E)$ et un entier $k$
][
  #sc[Vrai] si $G$ a une clique#footnote[_i.e._ possède $k$ sommets reliés deux à deux] de taille $k$
]

#proposition[ #pbm[clique] est $NP$-complet. ]
#proof[
  1. On vérifie que #pbm[clique] est dans $NP$ : le certificat, c'est la clique de taille $k$.
  2. On réduit un problème bien connu (ici, #pbm[sat]) $NP$-complet à #pbm[clique].

    Montrons que $#pbm[3-sat] <= #pbm[clique]$. Soit $phi = C_1 and C_2 and dots.c and C_n$ où chaque $C_i$ est composé de trois littéraux $x_i$ ou $not x_i$.
    On forme un graphe $G_phi$ sur $3 n$ sommets, un pour chaque littéral dans chaque clause.
    Les arêtes de $G_phi$ relient les littéraux $ell_i ell_j$ de clauses différentes et vérifiant $ell_i != ell_j$.

    Il est équivalent que : $G_phi$ a une clique de taille $n$ et que $phi$ est satisfiable.

    - "$==>$" Si $phi$ est satisfiable, il existe une affectation avec au moins un littéral vrai dans chaque clause, et 
]



#pb-display(name: pbm[somme])[
  Des entiers $s_1, ..., s_m$ et $S$
][
  #sc[Vrai] s'il existe $I subset.eq [n]$ tel que~$sum_(i in I) s_i = S$
]


La taille du codage est $sum ceil(log s_i) + ceil(log s)$.

#proposition[
  #pbm[somme] est $NP$-complet.
]
#proof[
  1. On vérifie que #pbm[somme] est dans $NP$ (on donne la solution).
  2. Montrons que $#pbm[3-sat] <= #pbm[somme]$.
     On va construire une fonction $f$ des instances de #pbm[3-sat] vers les instances de #pbm[somme] telle que $I$ est #sc[Vrai] _ssi_ $f(I)$ est #sc[vrai].
     On se donne $F = C_1 and C_2 and dots.c and C_m$ en les variables $x_1, ..., x_n$ et on lui associe des entiers.
     Le "truc", c'est d'utiliser des représentations de nombres en base 10 mais qui n'utilisent que des zéros et des uns.
     Ainsi, il n'y a pas de retenue et c'est un codage combinatoire.

     On forme $2n + 2m$ entiers dont les chiffres sont des zéros et des uns à l'aide de la matrice $bold(M)$ (les lignes sont des entiers).
     On crée $bold("LC")$ la matrice d'incidence clause/littéraux : $bold("LC")_(ell,c) = 1$ si le littéral $ell$ est da,s la clause $c$ et $0$ sinon.
     On se donne $S = underbrace(1 dots 1, n) underbrace(3 dots 3, m)$.

     La formule $F$ est satisfiable si, et seulement si, il existe $I subset.eq [2n+2m]$ tel que $sum_(i in I) s_i = S$.
     En effet, si $F$ satisfiable, il suffit de sélectionner les littéraux positifs, la somme donne bien~$S_1$ (la somme des littéraux).
     Et, comme chaque clause est satisfaite par les $m$ premiers chiffres, on a donc une valeur de 1, 2 ou 3, il suffit de compléter pour avoir 3.
]

#figure(
  cetz.canvas({
    import cetz.draw: *

    scale(0.6)
    
    content((1,0), $ x_1 $)
    content((2,0), $ x_2 $)
    content((3,0), $ x_3 $)
    content((4,0), $ dots.c $)
    content((5,0), $ x_n $)

    content((-0.2, -1), $ x_1 $)
    content((-0.2, -2), $ not x_1 $)
    content((-0.2, -3), $ x_2 $)
    content((-0.2, -4), $ not x_2 $)
    content((-0.2, -5), $ x_3 $)
    content((-0.2, -6), $ not x_3 $)
    content((-0.2, -7), $ dots.v $)
    content((-0.2, -8), $ dots.v $)
    content((-0.2, -9), $ x_n $)
    content((-0.2, -10), $ not x_n $)

    rect((+0.5,-0.5), (5.5,-10.5))
  })
)

// TODO(Hugo) : finir la figure...


#pb-display(name: pbm[sac-à-dos])[
  - un ensemble de couples $(p_i,v_i)_(i in [n])$ entiers ;
  - volume total $V$ ;
  - prix à atteindre $P$.
][
  #sc[vrai] s'il existe $I subset.eq [n]$ tel que 
  - $sum_(i in I) v_i <= V$ ;
  - $sum_(p in I) p_i >= P$.
]

#remark[
  Ce problème est dans $PP$ si codé en unaire (_i.e._ la taille d'une instance est en $sum p_i + sum v_i + V + P$) mais il est $NP$-complet s'il est codé en binaire.
]

#proposition[
  #pbm[sac-à-dos] (codé en binaire) est $NP$-complet.
]

#proof[
  On montre $#pbm[somme] <= #pbm[sac-à-dos]$.

  À une instance de #pbm[somme] $(s_1, ..., s_n, S)$, on construit l'instance de #pbm[sac-à-dos] en posant :
  - $p_i = s_i$ ;
  - $v_i = v_i$ ;
  - $V = S$ ;
  - $P = S$.

  On a immédiatement l'équivalence des instances vraies.
]

#pb-display(name: pbm[stable])[
  $G$ un graphe et $k$ un entier
][
  #sc[Vrai] s'il existe $k$ sommets deux-à-deux non reliés
]

#proposition[
  Le problème #pbm[stable] est $NP$-complet car $#pbm[clique] <= #pbm[stable]$.
  En effet, il suffit de remplacer les arêtes par des non-arêtes (et vice versa).
]

#pb-display(name: pbm[couverture])[
  $G$ un graphe et $k$ un entier
][
  #sc[Vrai] s'il existe $k$ sommets qui intersectent toutes les arêtes
]

#proposition[
  #pbm[couverture] (aussi appelé #pbm[vertex-set]) est $NP$-complet.
]

#proof[
  Par réduction de #pbm[stable], noter que $G$ a un stable de taille $n - k$ si et seulement si $G$ a une couverture de taille $k$ (il suffit de prendre $C = V without S$ où $S$ est un stable).
]

#pb-display(name: pbm[feedback-vertex-set])[
  $G$ un graphe et $k$ un entier
][
  #sc[Vrai] s'il existe un ensemble $X$ d'au plus $k$ sommets tel que $G without X$ est acyclique.
]

#proposition[
  FVS est $NP$-complet.
]

#proof[

]

On a la chaîne de réduction :
$ #pbm[sat] <= #pbm[3-sat] <= #pbm[clique] <= #pbm[stable] <= #pbm[couverture] <= #pbm[fvs]. $


#pb-display(name: pbm[couplage-3D])[
  Un tenseur $bold(sans(T)) = (t_(i,j,k))$ de taille $n times n times n$ de ${0,1}$
][
  #sc[Vrai] s'il existe un couplage 3D, _i.e._ la donnée de deux permutations $sigma$ et~$tau$ du groupe symétrique $frak(S)_n$ vérifiant que l'on ait $t_(i,sigma(i),tau(i)) = 1$ pour $i in [|1,n|]$.
]

C'est équivalent à trouver un ensemble d'entrées "$1$" tel que toutes les $3 n$ tranches contiennent exactement une de ces entrées.

Une autre façon de voir un couplage est la suivante.
- On considère trois ensembles $H$, $L$ et $C$ disjoints de taille $n$.
- On ajoute un triangle $(i,j,k)$ avec $i in H$ et $j in L$ et $k in C$ pour chaque $t_(i,j,k)$ = 1.
- Il existe un couplage 3D _ssi_ il existe $n$ triangles qui couvrent l'ensemble $V := H union.dot L union.dot C$.

#proposition[
  #pbm[couplage-3D] est $NP$-complet.
]

#proof[
  On montre $#pbm[3-sat] <= #pbm[couplage-3D]$.
  On se donne $F = C_1 and C_2 and dots.c and C_m$ une formule de #pbm[3-sat] en variables $x_1, ..., x_n$.
  On transforme $F$ en une instance de couverture par triangle (la variante équivalente de #pbm[couplage-3d] décrite ci-avant).

  Chaque variable $x_i$ donne un gadget.

  // TODO(Hugo) : faire le gadget 3DM
  Les $2m$ pointes sont les seuls éléments partagés avec les autres gadgets.
  Il n'y a que deux possibilités de faire une couverture par triangle, et ceci correspond à choisir $x_i$ ou $bar x_i$.

  Puis, pour chaque clause, comme par exemple $C_i = ell_1 or ell_2 or ell_3$, on crée deux sommets $a in C$ et $b in L$ (la "base" de $C_i$) et on relie $a$ et $b$ à $ell_1, ell_2, ell_3$ (à la $i$-ème pointe des gadgets) puis on relie $a$ et $b$.

  Si $F$ est satisfaite, on peut couvrir par des triangles : toutes les bases de clauses et couvrir toutes les bases de variables pour le littéral satisfait.
  
  *Mais*, il reste des pointes isolées. Précisément, il en reste $m n - m$ (on a $m n$ libérés par les gadgets variables et $m$ capturés par les clauses).

  On ajoute $m n - m$ gadgets "nettoyants" construit par : on crée deux sommets $a$ et $b$ reliés entre eux, et on les relie tous les deux à toutes les pointes.

  Ceci permet d'assurer l'équivalence.
]

#pb-display(name: pbm[max-cut])[
  Un graphe $G = (V, E)$ et un entier $k$.
][
  #sc[Vrai] s'il existe une coupe $V = A union.dot B$ tel que le nombre d'arêtes entre $A$ et $B$ (noté~$e(A,B)$) est au moins $k$.
]

#proposition[
  #pbm[max-cut] est $NP$-complet.
]

#proof[
  On montre $#sc[nae-3-sat]#footnote[Le problème #pbm[nae-3-sat], "_not all equal_" #pbm[3-sat], est le problème qui, à une formule, est vrai s'il existe une valuation qui value différemment les littéraux de chaque clause (valuation pas toute égale dans une clause).] <= #sc[max-cut]$.
  Soit $F$ une formule $C_1 and dots.c and C_m$.

  On construit le multigraphe $G_F$ en deux étapes :
  - on ajoute tous les littéraux $x_i$ et $not x_i$ pour $i in [|1,n|]$ ;
  - pour la variable $x_i$, on ajoute $N$ arêtes entre $x_i$ et $not x_i$ ;
  - on relie les littéraux d'une même clause.

  On a l'équivalence : $F$ est #pbm[nae-3-sat] satisfiable _ssi_ on peut trouver une coupe de $G_F$ avec au moins $n N - 2 m$ arêtes, en supposant que $N > 2 m$.
  ("Il y a plus intérêt à couper les arêtes d'une clause que ceux entre $x_i$ et $not x_i$").
]

#pb-display(name: pbm[circ.-ham.-orienté])[
  Un graphe orienté
][
  #sc[Vrai] s'il existe un cycle qui passe par tous les sommets
]

#proposition[
  #pbm[circ.-ham.-orienté] est $NP$-complet.
]

#proof[
  C'est une réduction classique depuis #pbm[3-sat].
]

== Aparté : $NP inter coNP$.

=== Quelques exemples.

Les problèmes de la classe $NP inter coNP$ sont les problèmes de décisions admettant un certificat de réponse #sc[Vrai] *et* de réponse #sc[Faux] polynomiaux à vérifier. On appelle cela les problèmes *bien caractérisés*.

==== Le problème #pbm[premier].

- C'est un problème de $coNP$ : le certificat de réponse #sc[Faux] est un diviseur de $n$.
- C'est un problème de $NP$ ($triangle.r$ Pratt en ‘75).
- *Finalement*, c'est un problème de $PP$ (Agraval, Kayal et Saxena en 2002).

==== Le problème #pbm[CouplageParfait].

#pb-display(name: pbm[CouplageParfait])[
  Un graphe $G$
][
  #sc[Vrai] s'il existe un couplage qui couvre tout les sommets.
]

Dans le cas d'un graphe biparti, l'algorithme polynomial (algorithme "hongrois") résout ce problème ($tilde$ ‘30).

Le problème est simplement dans $NP$ : il suffit de donner la solution en certificat.
Mais, pour l'appartenance à $coNP$, c'est plus subtil.

#theorem(name: [Tutte en ‘46])[
  Pour tout ensemble $X$ de sommets, le nombre de composantes connexes de taille impaire de $G without X$ (noté $"ci"(X)$) vérifie $"ci"(X) <= |X|$.
]

Par ce théorème, $X$ est bien un certificat pour l'appartenance de #pbm[CouplageParfait] à $coNP$.

*Finalement*, c'est un problème de $PP$ (Edmonds en ‘66).

==== Le problème #pbm[SystèmeInéquations].

#pb-display(name: pbm[SystèmeInéquations])[
  $m$ inéquations linéaires de la forme $ sum_(j = 1)^n a_(i,j) x_j <= b_i $
  pour $i = 1..m$.
][
  #sc[Vrai] s'il existe une solution.
]

Ici, la taille de l'entrée, c'est $sum_(i,j) ceil(log a_(i,j)) + sum_i ceil(log b_i)$.

C'est un problème de $NP$ : s'il existe une solution, elle peut être exprimée par un sous-sytème d'égalité et elles s'expriment (Krammer) comme un rapport de déterminants (qui est polynomial en la taille de l'entier).

C'est aussi un problème de $coNP$ (Furkas en 1902).

*Finalement*, c'est un problème de $PP$ à l'aide de l'algorithme de l'ellipsoïde (Khachyan en ‘75).

==== Le problème #pbm[Décomposition Nombre Premiers].

Le problème #pbm[DécompositionNombrePremiers] (abrégé en DNP) dans sa version problème de décision, est le problème ci-dessous.

#pb-display(name: pbm[DNP])[
  Deux entiers $n$ et $K$.
][
  #sc[Vrai] si $n$ admet un diviseur inférieur ou égal à $K$.
]


C'est un problème de $NP$, il suffit de fournir un diviseur inférieur ou égal à $K$.

C'est un problème de $coNP$, il suffit de fournir la décomposition en produit de facteurs premiers (Pratt en ‘75).

À partir de ce problème de décision, on peut construire la décomposition d'un nombre en produit de facteurs premiers.

/ Point négatif: la sécurité informatique est basée sur un problème de $NP inter coNP$ (sans parler de l'algorithmique quantique).
/ Point positif: il y a plein de travail en cryptographie post-quantique.

=== Dualité.

Les certificats de $coNP$ sont basés sur un problème dit _dual_.
L'exemple type est #pbm[MaxFlot] qui est exactement #pbm[MinCut].

==== Le problème #pbm[SystèmeÉquations].

#move(
  dx: -1em,
  pb-display(name: pbm[SystèmeÉquation])[
    Un système $bold(A) bold(x) = bold(b)$.
  ][
    #sc[Vrai] s'il existe une solution.
  ]
)

Pour le certificat $coNP$, il suffit de fournir un $bold(y)$ tel que $bold(A)^transp bold(y)$ et $bold(b)^transp bold(y) != 0$.
En effet, cela est équivalent à une combinaison linéaire des lignes du système qui donne $0 = 1$.

==== Le problème #pbm[SystèmeInéquations].

Pour le certificat $coNP$, on utilise le lemme ci-dessous.

#lemma(name: [Farkas en 1902])[
  Le système $bold(A x) <= bold(b)$ n'a pas de solutions si, et seulement si, il existe une combinaison linéaire positive (ou nulle) d'inéquations qui donne $0 <= -1$.
]

==== Le problème #pbm[SystèmePolynomiaux].

#pb-display(name: pbm[Sys.Poly])[
  $P_1, ..., P_m$ des polynômes en variables $x_1, ..., x_n$ à coefficients entiers.
][
  #sc[Vrai] s'il existe $bold(x)^star in CC^n$ tel que $P_i (bold(x)^star)$ quel que soit $i = 1.. m$.
]

Un cas particulier de ce problème, c'est #pbm[SystèmeÉquations] car il est équivalent à $bold(A x) - bold(b) = 0$.

En degré 2, on peut aisément coder #pbm[3-sat]. Soit $F = C_1 and C_2 and dots.c and C_m$ une formule sous 3-CNF en variables $x_1, ..., x_n$ et on considère le système suivant :
$ cases(
  P_1 &: x_1^2 - x_1 = 0\
  P_2 &: x_2^2 - x_2 = 0\
  med thin dots.v & quad dots.v\
  P_n &: x_n^2 - x_n = 0\
  Q_1\
  med thin dots.v\
  Q_m
) $
où, par exemple, on code la clause $C_1 = x_1 or not x_2 or x_3$ par le polynôme 
$ Q_1 : x_1 + (1 - x_2) + x_3 + redblock(y_(1,1) + y_(1,2)) = 3, $
où l'on ajoute, pour chaque clause $C_i$, deux variables $y_(i,1)$ et $y_(i,2)$ vérifiant $y_(i,1)^2  - y_(i,1) = 0$ et $y_(i,2)^2  - y_(i,2) = 0$ (variables _dummy_).

#theorem(name: [Hilbert's Nullstellensatz en 1893])[
  Le système ${P_i (bold(x)) = 0 | i = 1..m }$ n'a pas de solution dans $CC$ si, et seulement si, il existe $Q_1, ..., Q_m in CC[x_1, ..., x_n]$ tels que 
  $ sum_(j = 1)^m P_i Q_i = 1 $
  (et donc on récupère la contradiction $0 = 1$.)
]

Ce *n*'est *pas* un certificat $coNP$ car un polynôme $Q_i$ peut avoir une complexité en espace exponentielle.




= Programmation dynamique.

L'idée est de définir l'optimalité d'un problème à l'aide d'un nombre polynômial de sous-problèmes.

== Plus longue suite commute.

On considère le problème
#pb-display(name: pbm[plsc])[
  Un mot $A$ de longueur $n$ et $B$ de longueur~$m$ sur l'alphabet ${mono(0),mono(1)}$
][
  Un mot $C$ le plus long possible qui est un sous-mot de $A$ et de $B$
]

On rappelle que sous-mot signifie ici sous-suite : $mono(001)$ est un sous-mot de $mono(0101)$.

On s'intéresse aux sous-problèmes.
On note $m_(i,j)$ la longueur du plus long sous-mot commun de $A[1..i]$ et $B[1..j]$.
On cherche $m_(n,m)$.

On procède "par récurrence".
- pour initialiser, on a $m_(i,j) = 0$ si $i$ ou $j$ vaut $0$ ;
- pour l'hérédité, on a :
  + si $A[i] != B[j]$ alors $m_(i,j) = max(m_(i-1,j), m_(i,j-1))$ ;
  + si $A[i] = B[j]$ alors $m_(i,j) = 1 + m_(i-1,j-1)$.

On peut coder en _bottom up_ (avec deux boucles).
Ou, on peut aussi utiliser une technique _top down_, mais il faut éviter les appels multiples sur les sous-problèmes en _mémoïsant_ les résultats déjà calculés (par exemple avec un tableau $bold("memo")$ de taille $n times m$ initialisé à "$-1$").

#algo(name: [PLSC-mémoïsé])[
  #algo-if[
    $i = 0$ ou $j = 0$
  ][
    #algo-return[$0$]
  ][
    $bold("memo")[i,j] = -1$
  ][
    #algo-if[$A[i] != B[j]$][
      $bold("memo")[i,j] = max mat("PLSC-mémoïsé"(A,i-1, B,j); "PLSC-mémoïsé"(A,i, B,j-1))$
    ][
      $bold("memo")[i,j] = 1 + "PLSC-mémoïsé"(A, i-1, B, j-1)$
    ]
  ]

  #algo-return[$bold("memo")[i,j]$]
]

L'intérêt de la mémoïsation, c'est que ça peut être plus efficace (par exemple $A = B$ est en temps linéaire).

/ Complexité.:
  Le temps de calcul de chaque sous-problèmes est en~$bigO(1)$.
  Il y a $bigO(n m)$ sous problèmes.
  La complexité est donc en $bigO(n m)$.

#remark[
  - L'espérance de la longueur plus longue suite commune de deux suites aléatoires de longueur $n$ de $mono(0), mono(1)$ est dans l'intervalle $[0.76 n, 0.82 n]$.
  - Sous _SETH_ (expliqué ci-après), il n'existe pas d'algorithme en $bigO(n^(2 - epsilon))$ quel que soit $epsilon > 0$.
    / ETH (_Exponential Time Hypothesis_).: Il n'existe pas d'algorithme pour #pbm[3-sat] en $bigO(2^smallo(n))$.
    / SETH (_Strong Exponential Time Hypothesis_).: Pour tout $epsilon > 0$, il existe $k$ un entier tel qu'il n'existe pas d'algorithme pour #pbm[$k$-sat] en $bigO(2^((1 + epsilon) dot n))$.
]

== Produit en chaîne de matrices.

#remark[
  Le produit (naïf) de $bold(A)$ de taille $a times b$ avec une matrice $bold(B)$ de taille $b times c$ se fait en $a b c$ opérations.
]

#example(name: [L'ordre importe dans la complexité])[
  Soit $bold(A)$ de taille $2 times 4$, $bold(B)$ de taille $4 times 6$, et $bold(C)$ de taille $6 times 8$.
  Vaut-il mieux calculer $(bold(A B)) bold(C)$ ou $bold(A) (bold(B C))$ ?

  Dans le premier cas, on a $2 times 4 times 6 + 2 times 6 times 8 = 144$ opérations.

  Dans le second cas, on a $4 times 6 times 8 + 2 times 4 times 8 = 256$ opérations.

  Il faut donc bien mieux calculer $(bold(A B)) bold(C)$.
]

#pb-display(name: pbm[pcm])[
  Une suite de matrices $bold(M)_1, ..., bold(M)_n$ valide#footnote[où l'on peut réaliser le produit en chaîne (les dimensions des matrices permettent le produit)]
][
  Le produit effectué avec le moins d'opérations possibles.
]

On utilise la programmation dynamique avec le sous-problème : calculer le nombre $m_(i,j)$, défini comme le nombre minimal d'opérations pour calculer $bold(M)_i dot bold(M)_(i+1) dots.c bold(M)_j$.

Pour l'initialisation, on a $m_(i,i) = 0$ (la matrice $bold(M)_i$ est déjà calculée).
Pour l'hérédité, on a :
$ m_(i,j) = min_(i <= k < j) (m_(i,k) + m_(k+1,j) + ell_i ell_(k+1) ell_(j+1)), $
où l'on note $ell_i$ le nombre de lignes de $bold(M)_i$, pour $i = 1..n$ et on pose~$ell_(n+1)$ le nombre de colonnes de $bold(M)_n$.

/ Complexité.:
  On a $bigO(n^2)$ sous-problèmes, et chaque sous problème est en $bigO(n)$, d'où l'algorithme est en $bigO(n^3)$.

Il existe un algorithme en $bigO(n log n)$ (mais l'article original était~"faux").
Ceci est revenu dans la littérature.

/ 2019.: _*Abstract :* [...] We present an alternative proof for the correctness of the first two algorithms and show that a third algorithm by Nimbark, Gohel, and Doshi (2011) is beyond repair._

/ 2021.: _*Abstract :* [...] We believe that this exposition is simple enough for classroom use. [...]_
  #h(1fr) #sym.triangle.r Thong Le et Dan Gusfeld

On va étudier la solution du second papier.
Les parenthésages sont en bijection avec les triangulations de $n$-gones.

Avec l'exemple précédent, 
#figure(
  stack(
    dir: ltr,
    cetz.canvas({
        import cetz.draw: *

        set-style(stroke: (cap: "round", join: "round"))

        circle((0,0), radius: 0.3, fill: blue, stroke: none, name : "a")
        circle((0,2), radius: 0.3, fill: blue, stroke: none, name : "b")
        circle((2,0), radius: 0.3, fill: blue, stroke: none, name : "c")
        circle((2,2), radius: 0.3, fill: blue, stroke: none, name : "d")

        content("a", text(white)[8])
        content("d", text(white)[4])
        content("c", text(white)[6])
        content("b", text(white)[2])

        line("a", "b")
        line("b", "d")
        line("d", "c")
        line("a", "c")
        
        content((1, -1), [4-gone])
    }), h(2em),
    cetz.canvas({
        import cetz.draw: *

        set-style(stroke: (cap: "round", join: "round"))

        circle((0,0), radius: 0.3, fill: blue, stroke: none, name : "a")
        circle((0,2), radius: 0.3, fill: blue, stroke: none, name : "b")
        circle((2,0), radius: 0.3, fill: blue, stroke: none, name : "c")
        circle((2,2), radius: 0.3, fill: blue, stroke: none, name : "d")

        content("a", text(white)[8])
        content("d", text(white)[4])
        content("c", text(white)[6])
        content("b", text(white)[2])

        line("a", "b")
        line("b", "d")
        line("d", "c")
        line("a", "c")
        line("c", "b")

        content((1,-1), $omega(T) = 144$)
    }), h(2em),
    cetz.canvas({
        import cetz.draw: *

        set-style(stroke: (cap: "round", join: "round"))

        circle((0,0), radius: 0.3, fill: blue, stroke: none, name : "a")
        circle((0,2), radius: 0.3, fill: blue, stroke: none, name : "b")
        circle((2,0), radius: 0.3, fill: blue, stroke: none, name : "c")
        circle((2,2), radius: 0.3, fill: blue, stroke: none, name : "d")

        content("a", text(white)[8])
        content("d", text(white)[4])
        content("c", text(white)[6])
        content("b", text(white)[2])

        line("a", "b")
        line("b", "d")
        line("d", "c")
        line("a", "c")
        line("a", "d")

        content((1,-1), $omega(T) = 256$)
    })
  )
)

On procède par réduction : comment trianguler un $n$-gone pondéré en minimisant la somme des triangles (chacun étant le produit de ses éléments).

Une idée qui peut venir est de procéder une induction.
On sait déjà qu'il existe toujours au moins 2 éléments isolés dans la triangulation (de degré 2).
Ceci est vrai car le _dual_ d'une triangulation est un arbre ; s'il a au moins deux éléments, il a au moins deux feuilles.


L'algorithme de calcul d'une triangulation est le suivant :
- si $v_1 v_2$ ou $v_1 v_3$ n'est pas une arête du $n$-gone\
  #stack(dir: ltr)[
      appels sur les deux sous $n$-gones 
    ][
    #cetz.canvas({
      import cetz.draw: *
      circle((0,1/2), radius: 0.5)
      circle((0,0), radius: 0.1, fill: blue, stroke: none, name : "a")
      circle((0,1), radius: 0.1, fill: blue, stroke: none, name : "b")
      line("a","b")
    })
    ]
- #stack(dir: ltr)[
    retourner le minimum de 
  ][
  #cetz.canvas({
    import cetz.draw: *
    let r(angle) = {
      return (calc.cos(angle+90deg)/2, 1/2 + calc.sin(angle+90deg)/2)
    }
    circle((0,1/2), radius: 0.5)
    circle((0,0), radius: 0.1, fill: blue, stroke: none, name : "a")
    circle((0,1), radius: 0.1, fill: blue, stroke: none, name : "b")
    circle(r(-40deg), radius: 0.1, fill: blue, stroke: none, name : "c")
    circle(r(+40deg), radius: 0.1, fill: blue, stroke: none, name : "d")
    bezier-through("c", (0, 1/2), "d")
  })
  ][et][
  #cetz.canvas({
    import cetz.draw: *

    let r(angle) = {
      return (calc.cos(angle+90deg)/2, 1/2 + calc.sin(angle+90deg)/2)
    }
    circle((0,1/2), radius: 0.5)
    circle((0,0), radius: 0.1, fill: blue, stroke: none, name : "a")
    circle((0,1), radius: 0.1, fill: blue, stroke: none, name : "b")
    circle(r(-40deg), radius: 0.1, fill: blue, stroke: none, name : "c")
    circle(r(+40deg), radius: 0.1, fill: blue, stroke: none, name : "d")
    line("a","b")
  })
  ]

== Problème SWERC.

Un problème du SWERC sur de la programmation dynamique :
#pb-display(name: pbm[template])[
  Deux mots $A$ et $B$  en entrée
][
  Le plus petit _template_ qui satisfait $A$ mais pas $B$.
]

Par exemple, avec $A = mono(01101)$ et $B = mono(00111)$, la solution est $mono(01)"*"$.
Et, pour $A = mono(0)^10mono(101)^10$ et $B = mono(0)^10mono(011)^10$, la solution est $"*"mono(10)"*"$.

L'exercice, c'est de trouver un algorithme en programmation dynamique en $|A| dot |B|$.

=== Indépendant de poids max dans un arbre.

#pb-display(loose: true)[
  Un arbre sur un ensemble de nœuds $V$ où chaque nœud $v$ a un poids $p(v) >= 0$.
][
  Un indépendant $I subset.eq V$ (les nœuds dans $I$ sont deux à deux non adjacents) et tels que $p(I)$ est maximum.
]

Pour résoudre ce problème, on utilise de la programmation dynamique.

#algo[
  Enraciner l'arbre\
  #algo-for[*_tout_* nœud $v$][
    Calculer $a(v)$ et $b(v)$ où
    $a(v)$ est la valeur de poids maximale d'un indépendant de $B_v$ contenant $v$ (le sous-arbre enraciné en $v$)
    et $b(v)$ est la valeur de pods maximal d'un indépendant de $B_v$ ne contenant pas $v$.
  ]
]

Initialisation : si $v$ est une feuille on a $a(v) := p(v)$ et $b(v) := 0$.

Induction :
$ a(v) := p(v) + sum_(w "enfant de" v) b(w) quad quad quad b(v) := sum_(w "enfant de" v) max(a(w), b(w)) $


= Analyse amortie.


== Tableau dynamique.
#example[
  - On initialise un tableau $bold(T)$ de taille 1.
  - On écrit un nouvel élément ($bold(T)[1]$)
  - On écrit un nouvel élément, mais pas de place, on double donc la taille de $bold(T)$, et on réécrit $bold(T)[1]$ et $bold(T)[2]$
  - On écrit un nouvel élément, mais pas de place, on double donc la taille de $bold(T)$, et on réécrit $bold(T)[1]$, $bold(T)[2]$ et $bold(T)[3]$
  - On écrit un nouvel élément ($bold(T)[4]$) et on a la place.
  - Et ainsi de suite.
]

*Calcul direct.*
  On note $C_i$ le coût d'écriture du $i$-ème élément dans le tableau.
  Ainsi, on a $ C_1 = 1 quad C_2 = 2 quad C_3 = 3 quad C_4 = 1 quad C_5 = 5. $

  Quel est le coût amorti des $C_i$ ?
  On a $C_i = 1$ sauf si $i = 2^k + 1$ auquel cas $C_i = i$.

  Que vaut $sum_(i=1)^(2^n + 1) C_i$ ?
  $ sum_(i=1)^(2^n + 1) C_i = 2^n + 1 + sum_(j=0)^n 2^j = 2^n + 1 + 2^(n+1) - 1 = 3 dot 2^n $
  On a un coût d'environ 
  $ (3 dot 2^n) / (2^n + 1) approx 3. $

*Méthode des acomptes.*
Pourquoi le coût est-il de $3$ par opérations ?

- Chaque élément paye 1 pour s'inscrire.
- Chaque élément paye 1 pour sa duplication.
- Chaque élément $i$ paye la duplication de $j = i - 2^(ceil(log_2 i) - 1)$ (son homonyme dans le tableau avant qu'il soit dupliqué).

*Méthode du potentiel.*
Trouver une fonction potentiel~$phi_i >= 0$ telle que le cout amorti 
$ hat(C)_i = C_i + (phi_i - phi_(i-1)) <= 3 $

Ainsi, 
$ sum_(i=1)^k hat(C)_i = overbrace(sum_(i=1)^k C_i, C) + phi_k - phi_0 $
d'où $C = 3k - phi_k + phi_0$
(On a en général $phi_0 = 0$.)

Dans notre cas, on choisit la fonction de potentiel $phi_i = 2 i - n$, où l'entier $n$ est la taille du tableau dans lequel $i$ est inscrit.
On a bien $phi_i >= 0$ car un élément est toujours écrit dans la deuxième moitié du tableau.

Si $i != 2^k + 1$ alors 
$ hat(C)_i = 1 + (2_i - n) - (2(i-1) - n) = 3 $
et si $i = 2^k + 1$,
$ hat(C)_i = (2^k + 1) + 2(2^k + 1) - 2^(k+1) - (2 dot 2^k - 2^k) = 3. $

// Thomassé est d'albedo 1
// François est d'albedo 2

== Compteur et code de Gray

Peut-on énumérer tous les ${0, 1}^k$ en changeant à chaque étape $1$ bit entre un élément et son successeur.
Par exemple $00$, $01$, $10$, $11$.

L'idée est de parcourir un chemin dans l'hypercube de dimension $H^n$.
Pour cela, il suffit de parcourir un chemin dans $H^(n-1)$, de changer la dernière coordonnée, puis de parcourir le même chemin en sens inverse dans la 2ème copié de $H^(n-1)$.

Pour visualiser, passé la dimension 3, c'est compliqué.
Mais le calcul reste vrai.
- 0000
- 0001
- 0011
- 0010
- 0110
- 0111
- 0101
- 0100
- 1100
- 1101
- 1111
- 1110
- 1010
- 1011
- 1001
- 1000

Par contre, pour trouver le lien entre un élément et son successeur, c'est plus compliqué :
- si on contient un nombre pair de 1, on change le premier bit
- sinon on change le bit le plus à gauche du "1" le plus à droite.
(À démontrer.)


Le code de Gray est une façon compacte "en temps" de représenter ${0, 1}^n$.

La variante en espace : trouver le mot de ${0,1}^star$ le plus court qui contient tous les mots (comme facteur) de ${0,1}^k$.
Par exemple, le mot $00 11 0$ est une solution pour $k = 2$.

#theorem(name: [De Bruijn])[
  Il existe un mot cyclique de longueur $2^k$ tel que tous les mots de ${0,1}$ apparaissent comme facteurs (dans le sens direct).
]
#proof[
  On utilise l'_automate de De Bruijn_ : les états sont des mots de ${0,1}^k$ (ici on traite le cas $k = 3$) et les transitions sont $x -> y$ si $y$ est un décalage de $x$.

  La question est : existe-t-il un cycle qui passe par tous les sommets ?
  Oui ! Il existe un cycle hamiltonien $11101000$. Mieux encore, il existe un cycle un cycle eulérien (un cycle qui passe par tous les arcs exactement une fois) car les degrés entrants et sortants sont constants et égaux, et que le graphe est connexe.
  Ceci donne un mot pour ${0,1}^(k+1)$.
  Ici, on a $1001101011110000$.
]


= Approximation.

#let OPT = "OPT"
#let APX = $bold("APX")$

== Introduction.

On considère ici des problèmes d'optimisation où la solution doit maximiser ou minimiser une certaine fonction objectif. On notera en général $OPT$ la valeur optimale.
On dit qu'un problème est~$NP$-dur ou $NP$-difficile si son problème de décision associé (_e.g._ $OPT >= k$) est $NP$-complet.

Les problèmes d'optimisations sont souvent difficiles (voyageur du commerce, ou sac à dos) on aimerait trouver une solution approchée.
On se fixe une valeur $C > 1$.
On dira qu'un algorithme (polynomial) est une $C$-approximation si 
- pour un problème de maximisation, il retourne une solution de valeur au moins $OPT \/ C$ ;
- pour un problème de minimisation, il retourne une solution de valeur au plus $OPT dot C$.
(Mais vous verrez des $1/2$-approximations dans les problèmes de maximisation dans la littérature.)

S'il existe une valeur $C > 1$ telle qu'il existe un algorithme polynomial de $C$-approximation, on dit que le problème est dans~$APX$.

S'il existe une valeur $C$ telle que l'existence d'un algorithme de $C$-approximation implique $PP = NP$ alors le problème est $APX$-dur.

On parle de _schéma d'approximation polynomial_ si pour tout $epsilon > 0$ il existe un algorithme de $(1+epsilon)$-approximation polynomial si l'on est dans un des trois cas :
/ PTAS.:#footnote[_Polynomial time approximation scheme_] l'approximation est en $bigO(n^(f(1/epsilon)))$ ;
/ Efficient-PTAS.: l'approximation est en $bigO(f(1/epsilon)n^c)$ ;
/ Fully-PTAS.: l'approximation est polynomiale en $1/epsilon$ et en $n$.

== Illustration avec le problème du sac à dos.

On considère $cal(O) = {O_1, ..., O_n}$ les objets et $V$ un volume maximal.
Chaque $O_i$ a un prix $p_i$ et un volume $v_i$.
On veut $I subset.eq [n]$ tel que $sum_(i in I) v_i <= V$ et qui maximise $sum_(i in I) p_i$.

Ce problème est $NP$-dur en codage binaire et polynomiale en codage unaire (programmation dynamique).

On supoose que $v_i <= V$ pour tout $i$.

=== Algorithme de $2$-approximation.

On a intérêt à choisir les objets de meilleur qualité $q_i := p_i \/ v_i$. Pour simplifier, on suppose que les $q_i$ sont distincts deux à deux.

L'idée est qu'on trie les objets par ordre décroissant de qualité (On suppose que l'ordre donné est celui là).
On fait un algorithme glouton. *En $APX$, Glouton est votre ami.*

L'idée est de choisir le plus grand $t$ tel que $sum_(i <= t) v_i <= V$.
L'algorithme consiste à retourner le maximum entre ${O_1, ..., O_t}$ et ${O_(t+1)}$.

Pour le voir (et cela permet "l'intuition"), on pratique la "relaxation fractionnaire".
Pour cela, on sélectionne une fraction~$x_i$ de chaque objet $O_i$.
On considère le problème de maximisation sous-contrainte, noté $(P)$, suivant :
#quote[
  Maximiser $sum_(i = 1)^n p_i x_i$ sous la contrainte $sum_(i=1)^n v_i x_i <= V$ et $0 <= x_i <= 1$ pour $i in [|1,n|]$.
]

On peut résoudre en temps polynomial (avec votre solveur favori) et retourne une solution $(x_i^star)$ de valeur $p^star = sum_(i=1)^n p_i x^star_i$.
Noter que la solution optimale du problème initial $"OPT" subset.eq cal(O)$ de valeur $p$ vérifie $p <= p^star$ car $OPT$ est une solution de $(P)$ en posant $x_i = 1$ si $O_i in "OPT"$ et $0$ sinon.

Soit $i < j$. Si $x_j^star > 0$ alors $x_i^star = 1$.
En effet, sinon, on peut transférer une partie de $x_j^star$ sur $x_i^star$.
Supposons par l'absurde que $x_j^star > 0$  et $x_i^star < 1$.
On choisit $epsilon_i <= 1 - x_i^star$ et $epsilon_j <= x_j^star$ tels que $v_i epsilon_i = v_j epsilon_j$.
On ajoute $epsilon_i$ à $x_i^star$, on enlève $epsilon_j$ à $x_j^star$.
On trouve une nouvelle solution (valide par considération du volume) du prix total :
$ p + epsilon_i p_i - epsilon_j p_j = p + (epsilon_i p_i - (v_i epsilon_i) / v_j p_j) = p + epsilon_i v_i underbrace((p_i / v_i - p_j / v_j), > 0) $
une contradiction.

Résumons, on a 
$ p({ O_1, ..., O_(t+1) }) >= p^star >= p $
donc
$ p({ O_1, ..., O_t }) + p({O_(t+1)}) >= p $
l'un des deux est donc plus grand que $p \/ 2$.
On en conclut que l'on a bien une $2$-approximation.

=== _Polynomial time approximation scheme_.

On veut, pour tout $epsilon > 0$, construire en temps polynomial une solution de prix au moins $(1-epsilon) p$.

*Principe de dualité.*
On se base sur l'objectif aussi bien que sur les contraintes (ici, le prix).

Si l'élément $O_(t+1)$ a un prix $p_(t+1) <= epsilon p$ alors la solution gloutonne a un prix d'au moins $(1-epsilon)p$.
De plus, on sait que le nombre d'objets de prix supérieurs stricts à $epsilon p$ est au plus $1/epsilon$ dans $"OPT"$.


On note $cal(O)' subset.eq cal(O)$ l'ensemble des objets de prix supérieur strict à $epsilon p$.

#algo(name: [GUESS & GLOUTON])[
  #algo-for[tout ensemble $X subset.eq cal(O)'$ de taille $<= 1/epsilon$][
    Mettre $X$ dans la solution $S_x$.\
    Compléter $S_X$ avec un choix glouton sur $cal(O) without cal(O)'$.
  ]

  #algo-return[
    le meilleur $S_X$.
  ]
]

La complexité de cet algorithme est en $bigO(n^(1\/epsilon)) dot "comp(Glouton)"$.

On a cependant un problème : on ne connait pas $p$. La solution est de calculer $p'$ le prix du glouton (on a donc $p' >= p \/ epsilon$).
Au lieu du $cal(O)'$ précédent, on considère tous les $O_i$ de prix $> epsilon p'$.
On considère alors tous les sous ensembles de taille $<= 2 / epsilon$.

C'est un algorithme inefficace mais qui ouvre la voie.

=== FPTAS pour le problème du Sac à Dos.

Reprenons l'algorithme de programmation dynamique du sac à dos mais en se basant sur les prix (plutôt que sur les volumes).

Notons $s(i, p)$ le volume minimal d'une solution de prix $o$ incluse dans ${ O_1, ..., O_i }$ (ou $+oo$ si aucune solution n'existe).

/ Conditions initiales: on pose $s(i, 0) = 0$ pour tout $i in [|1,n|]$ et $s(0, p) = +oo$ pour $p != 0$.
/ Induction: $s(i,p) = min(s(i-1,p), s(i-1,p - p_i) + v_i)$
/ Fin: On retourne le $p$ maximal tel que $s(n,p) <= V$.

La complexité est en $bigO(n dot sum_(i=1)^n p_i)$.

L'idée est, comme on cherche une solution approchée, on n'a (peut-être) pas besoin de toute la précision des $p_i$.
Considérons $alpha > 0$ tel que l'algorithme de programmation dynamique, appliqué aux valeurs $p_i' = floor(alpha p_i)$ retourne une solution $"OPT"'$ telle que l'on ait $p("OPT"') >= (1-epsilon)p$.
Quelle contrainte a-t-on sur $alpha$ ?

Par partie entière, on sait que $alpha p_i - 1 <=_((1)) p_i' <=_((2)) alpha p_i$ et donc 
$ p("OPT"') = sum_(i in "OPT"') p_i &>= 1/alpha sum_(i in "OPT"') p'_i "par" (1)\
&>= 1/alpha sum_(i in "OPT") p'_i " par optimalité de OPT"'\
&>= 1/alpha sum_(i in "OPT") (alpha p_i - 1) " par" (2)\
&>= p - (|"OPT"|)/alpha\
&>= p - n / alpha
$
Pour avoir une solution de poids $>= (1-epsilon)p$, il faut nécessairement que $n / alpha <= epsilon p$.
On veut $alpha >= n / (epsilon p)$.
Il suffit de choisir $p'$ (la valeur de la solution gloutonne) au lieu de $p$ et de poser $alpha = n / (epsilon p')$.

*Remarque.* On peut aussi choisir $p_max$ au lieu de $p'$ où l'on a noté $p_max = max_(i in [|1,n|]) p_i$.

La complexité est alors en $bigO(n sum_(i = 1)^n p'_i) = bigO(n^3 / epsilon)$.
On a donc un~_FPTAS_.

En effet, 
$ sum_(i=1)^n p'_i <= alpha sum_(i=1)^n p_i = n/(epsilon p') sum_(i=1)^n p_i = n/epsilon sum_(i=1)^n underbrace(p_i/p', <=1) = bigO(n^2/epsilon). $

Ainsi, si $p'$ n'est pas une fraction positive des $sum_(i in [|1,n|]) p_i$ alors on a une complexité en $bigO(n^2 / epsilon)$.

== Transversaux de poids minimal (_aka_ #pbm[MinHittingSet]).

On considère le problème
#pb-display(name: pbm[$k$-transversal])[
  $E subset.eq binom([n], k)$ un ensemble de parties de taille $k$ et $omega : [n] -> RR^+$ une fonction de poids
][
  $T subset.eq [n]$ tel que $T inter e != emptyset$ pour toute arête $e in E$, et $omega(T)$ est minimal.
]

#example[
  Pour $k=2$ et $omega : n |-> 1$, c'est le problème de #pbm[MinimumVertexCover].
]

Aussi, pour $omega : n |-> 1$, on a un algorithme de $k$-approximation trivial : on construit (glouton) des éléments de $E$ deux à deux disjoints $e_1, ..., e_t$ tels que $forall e in E, exists i, e inter e_i != emptyset$.
On retourne ensuite $union_(i=1)^n e_i =: S$.

*Remarque.*
On a forcément $|"OPT"| >= t$ (car il doit toucher tous les $e_i$ et la solution $S$ vérifie $|S| = t k <= k |"OPT"|$).
On a donc bien obtenu une $k$-approximation.

Deux théorèmes intéressants :
#theorem[
  À moins que $PP = NP$, il n'existe pas de $(sqrt(2)-epsilon)$-approximation pour #pbm[VertexCover] quel que soit $epsilon > 0$.
]

#theorem[
  À moins que la "_Unique Game Conjecture_" soit fausse, il n'existe pas de $(2-epsilon)$-approximation pour #pbm[VertexCover].
]

Peut-on trouver une $k$-approximation pour une fonction de poids $omega$ arbitraire ?

=== Arrondi en relaxation fractionnaire.

On considère la relaxation fractionnaire $(P)$ du problème précédent :
#quote[
  Minimiser $sum_(i=1)^n omega(i) x_i$ sous les contraintes $sum_(i in e) x_i >= 1$ pour toute arête $e in E$, et $x_i >= 0$.
]
Dans le problème, le $x_i$ représente la fraction de l'élément $i$ choisi dans $T$.

Notions $"OPT"^star = (x_i^star)$ une solution optimale de $(P)$.

Remarquons que $omega("OPT") >= sum_(i=1)^n omega(i) x_i^star$, car $"OPT"$ est un élément du domaine de $(P)$ (en posant $x_i = 1$ si $i in "OPT"$ et $0$ sinon).

À présent, on calcule une solution $(x_i^star)$.
On construit une solution $0 \/ 1$ comme suit :
- si $x_i^star >= 1/k$, on pose $x_i' = 1$ ;
- sinon, on pose $x_i' = 0$.

On a que $omega("OPT"') <= k omega("OPT"^star) <= k omega("OPT")$ donc a bien construit une $k$-approximation.

Il y a cependant deux problèmes :
+ on doit résoudre $(P)$ ;
+ si $k = 10$, alors la taille de $E$ est (peut-être) en $Theta(n^10)$. Pourrait-on faire une $k$-approximation avec seulement un oracle pour $E$ ?

Un oracle est un algorithme résolvant le problème suivant :
#pb-display(loose: true)[
  $T$ (un potentiel transversal)
][
  VRAI si $T$ est un transversal \
  FAUX *et* $e in E$ tel que $e inter T = emptyset$.
]

On a ainsi "caché" $E$ (l'ensemble $E$ pourrait même être de taille exponentielle, du moment qu'on a un oracle).

On utilise un algorithme nommé _primal dual_ pour construire une $k$-approximation du problème de #pbm[$k$-transversal].

#algo(name: [PrimalDual])[
  Initialiser $T = emptyset$ et $y : E -> NN$ telle que $y(dot) = 0$.

  #algo-while[
    $exists e in E, e inter T = emptyset$ (*_oracle_*)
  ][
    Augmenter $y(e)$ jusqu'à atteindre, pour un certain $i in e$ l'égalité $sum_(f in.rev i) y(f) = omega(i)$.

    $T <- T union {i}$
  ]

  #algo-return[$T$]
]

À la fin de l'algorithme $T$ est bien transversal, mais de quelle~"qualité" ?
Calculons à présent $omega(T)$.

$
omega(T) = sum_(i in T) omega(i) &= sum_(i in T) sum_(e in.rev i) y(e)\
&= sum_(e in E) |e inter T| dot y(e)\
""_((star)) &<= k sum_(e in E) y(e)\
$
car $(star)$ toute les parties ont taille $<= k$;

On montre maintenant que si $T_"opt"$ est la solution optimale du problème #pbm[$k$-transversal], alors $sum_(e in E) y(e) <= omega(T_"opt")$ ; on aura alors que $omega(T) <= k med omega(T_"opt")$ et par conséquent que $T$ est une $k$-approximation de #pbm[$k$-transversal].

On a 
$ omega(T_"opt") = sum_(i in T_"opt") omega(i) >= sum_(i in T_"opt") sum_(e in.rev i) y(e) = sum_(e in E) underbrace(|T_"opt" inter e|, >= 1 \ "car" T_"opt" \ "transversal") y(e) >= sum_(e in E) y(e). $

L'algorithme Primal Dual est une généralisation de l'algorithme de Dijkstra.
L'algorithme de Dijkstra est un algorithme primal dual.
On rappelle que l'algorithme de Dijkstra résout le problème ci-dessous :
#pb-display(loose: true)[
  Graphe avec des longueurs sur les arêtes, et deux sommets $s$ et $t$ du graphe,
][
  Un plus court chemin de $s$ à $t$
]

*C'est un problème de transversal.*
Un chemin de $s$ à $t$ est un transversal de l'ensemble des coupes de $s$ à $t$, _i.e._ l'ensemble des arêtes entre $S$ et $T$ où $S union.dot T = V$ et $s in S$ et $t in T$.
Et un chemin de longueur minimale est précisément un transversal de longueur minimale des coupes de $s$ à $t$.

Il reste à définir l'_oracle_.
Si on se donne un ensemble $F$ qui n'est *pas* un transversal des coupes, on retourne une coupe $C_F$ telle que $C_F inter F = emptyset$.
Ainsi, on choisit $C_F$ la coupe, $S$ et $T$ avec $|S|$ minimal et où
$ S = { y | y "atteignable depuis" s "pour un certain chemin de" F }. $

Avec cet oracle, Primal Dual correspond exactement à Dijkstra.


#align(center, line())

Dans l'algorithme de Christofides, il est utilisé le fait que calculer un couplage de poids max (dans un graphe quelconque) est dans~$PP$ (algorithme d'Edmonds). On aurait juste besoin de pouvoir l'approximer.

$=>$ Est-il possible d'approximer le couplage de taille maximal dans un graphe arbitraire ?
*Oui* avec le paradigme de *_recherche locale_*.

== Paradigme de recherche locale.

Le but est d'obtenir un couplage de taille $(4\/5)|"OPT"|$.
#algo(name: [Recherche locale])[
  #algo-comment[On part d'une solution]\
  Soit $C$ le couplage vide.

  #algo-while[
    il existe un couplage $C'$ qui diffère de $C$ sur au plus~$7$ arêtes et tel que $|C'| > |C|$
  ][
    $C <- C'$
  ]
]

À la fin $C$ est une $4/5$ approximation de $"OPT"$.

Noter que $"OPT" union C$ est une union de cycles et de chemins.
Si on avait $|C| < 4/5 |"OPT"|$ il existe un cycle ou un chemin où cette inégalité est vérifiée :
- sur les cycles, c'est impossible car un cycle est nécessairement alternant ;
- sur les chemins, c'est possible s'il alterne entre arêtes dans $"OPT"$, puis dans $C$, puis dans $"OPT"$, puis dans $C$, _etc_.
  Pour avoir $|C| < 4/5 |"OPT"|$, on doit avoir que la longueur du chemin est au plus $7$, échanger les arêtes de $C$ sur ce chemin pour les arêtes de $|"OPT"|$ fournit une meilleur solution.

Autre algorithmes de recherche locale :
- 2-approximation pour #pbm[MaxCut] (précédent TD) ;
- descente de gradient (M1) ;
- algorithme du simplex (M1) ;
- réseaux de Hopfield (prochain TD).


== Paradigme de relaxation fractionnaire.

#quote[
En stage, en recherche, _etc_, pensez à la relaxation fractionnaire. Une fois faite, _dualisez_.
]

L'idée est qu'on part d'un problème $P$, et on écrit un problème linéaire appelé _primal_ $(P)$, où 
$(P)$ consiste à maximiser $bold(c)^sans(upright(T)) bold(x)$ sous les contraintes $bold(A) bold(x) <= bold(b)$ et $bold(x) >= bold(0)$.

#theorem(name: [dualité])[
  Le problème $(P)$ a une solution optimale de valeur $v$ si et seulement si $(D)$ a une solution optimale de valeur $v$ où le problème~_$(D)$ dual de $(P)$_ consiste à minimiser $bold(b)^sans(upright(T)) bold(y)$ sous les contraintes $bold(A)^upright(sans(T)) bold(y) >= bold(c)$ et $bold(y) >= bold(0)$.
]

Les problèmes viennent deux par deux : le primal est le dual.

#example(name: [Couplage dans un graphe])[
  Si $x$ est une distribution de poids sur les arêtes, alors la relaxation fractionnaire du couplage est de trouver une telle distribution qui vérifie que le poids des arêtes incidentes a un sommet est au plus $1$.
  Le problème s'écrit donc "maximiser $bold(1) bold(x)$ sous les contraintes $bold(A) bold(x) <= bold(1)$ et $bold(x) >= bold(0)$",
  où $bold(A)$ est la matrice d'incidence, en colonne les arêtes, et en ligne les sommets.

  Le problème dual est alors de "minimiser $bold(1) bold(y)$ sous les contraintes~$bold(A)^upright(sans(T)) bold(y) >= bold(1)$ et $bold(y) >= 0$". 
  Ainsi $y$ est une distribution de poids sur les sommets telle que pour chaque arête $u v$ on a $y(u) + y(v) >= 1$.
  C'est la relaxation fractionnaire de #pbm[vertex cover].

  #figure(
  cetz.canvas({
    import cetz.draw: *

    circle((0, 0), radius: 0.1, fill: blue, stroke: none, name: "a")
    circle((0, 1), radius: 0.1, fill: blue, stroke: none, name: "b")
    circle((1, 1/2), radius: 0.1, fill: blue, stroke: none, name: "c")

    line("a", "b")
    line("c", "b")
    line("a", "c")

    circle((0, 0), radius: 0.1, fill: blue, stroke: none, name: "a")
    circle((0, 1), radius: 0.1, fill: blue, stroke: none, name: "b")
    circle((1, 1/2), radius: 0.1, fill: blue, stroke: none, name: "c")
  })
  )

  Dans le triangle ci-dessous, on a 
  #[
    #set text(0.7em)
  $ mat("couplage max"; M quad  1) <= mat("couplage max frac."; M^* quad 3/2) = mat("vertex cover frac."; V C ^* quad 3/2) < mat("vertex cover min"; V C quad 2). $
  ]
]


== Paradigme d'algorithmes randomisés.

=== Calcul d'un couplage parfait.

Considérons $A union.dot B$ un graphe biparti.
Décider s'il existe un couplage parfait est dans $PP$.

On veut un algorithme qui
- s'il retourne VRAI, alors il existe un couplage parfait ;
- s'il retourne FAUX, avec une probabilité de $1/2$ il n'existe pas de couplage.

Soit $bold(M) = (m_(a,b))_(a in A, b in B)$ la matrice de $A union.dot B$, où 
$ m_(a,b) = cases(1 & "si" a-b, 0 & "sinon".) $
On peut supposer $A = B = [n]$.

Un couplage parfait est équivalent à l'existence d'une permutation~$sigma in frak(S)_n$ vérifiant $m_(i, sigma(i)) = 1$ pour $i in [n]$.
Ainsi, c'est équivalent à l'existence d'une permutation $sigma$ telle que $product_(i in [n]) m_(i,sigma(i)) = 1$.

*Rappel.*
Le _déterminant_ de $bold(M)$ est :
$ det bold(M) = sum_(sigma in frak(S)_n) (-1)^("sgn"(sigma)) product_(i in [n]) m_(i, sigma(i)) $
et le _permanent_ de $bold(M)$ 
$ "perm" bold(M) = sum_(sigma in frak(S)_n) product_(i in [n]) m_(i, sigma(i)). $

Le permanent calcule le nombre de couplages parfaits.
Dommage, calculer le permanent est un problème $sharp PP$-complet.

L'idée est qu'on calcule $det bold(M)$ si non nul alors on retourne vrai, en revanche on peut avoir $det bold(M) = 0$ par "simplification des termes".

#algo(name: [Tutte])[
  Remplacer chaque arête (_i.e._ "$1$" dans la matrice) par une valeur aléatoire entre $1$ et $2n$ pour obtenir $bold(M)$.

  Retourner VRAI si $det bold(M) != 0$ et FAUX sinon.
]

Avec une probabilité $>= 1/2$ s'il existe un couplage parfait, alors $det bold(M) != 0$ dans l'algorithme précédent.
On ajoute deux remarques.
- Cela marche pour les graphes généraux : étant donné un graphe $G$, poser $bold(M)$ comme sa matrice d'adjacence, où l'on remplace $m_(i,j)$ par $C$ et $m_(j,i)$ par $-C$ avec $C$ tiré aléatoirement dans $[|1,2n|]$. Avec la même conclusion, si le déterminant est non-nul alors couplage ; s'il nul, alors avec une probabilité $<= 1/2$ il y a un couplage.
- Ce qui sous-tend Tutte c'est la propriété suivante :
  si $P in RR[x_1, ..., x_n]$ est un polynôme de degré $d$ multivarié et non identiquement nul alors si on tire aléatoirement des $x_i$ dans ${1, ..., 2d}$ alors avec probabilité $>= 1/2$ l'évaluation est non nulle.
  On réalise l'application directe au déterminant.


= Algorithmes exacts exponentiels.

Dans cette section, on s'intéresse à résoudre des problèmes $NP$-difficiles sur des petites instances.
C'est-à-dire trouver $c$ le plus petit possible pour une complexité en $c^n$.

*Notation.* On notera $bigO^star (c^n) = bigO(c^n dot p(n))$ pour un polynôme $p$.

== Paradoxe des anniversaires.

*N'ayez pas plus de $sqrt(n)$ confiance !*

L'objectif est de signer un contrat pour une valeur $1000 med euro$.
Pour assurer que le contrat est valide, on utilise une fonction de _hash_ qui, à un contrat, associe un nombre $h in {1, ..., N}$.

On supPpose que $N$ est grand, plus grand que la capacité de calcul, qu'il est donc impossible de trouver (calculer) un texte lisible pour une valeur de hash $h$ donnée.

Ce que l'on souhaite éviter, c'est d'avoir un contrat pour $2000 med euro$ de même hash $h$.

L'idée est que l'on prépare $sqrt(N)$ bon contrats (ceux d'une valeur~$1000 med euro$) et l'autre prépare $sqrt(N)$ mauvais contrats (ceux d'une valeur $2000 med euro$).
On n'a qu'une probabilité $ (1 - 1/sqrt(N))^sqrt(N) -->_(n->+oo) 1/e $ d'avoir une collision.

Avec une probabilité supérieure à $1/2$, avec une puissance de calcul~$sqrt(N)$ (bien plus raisonnable), on peut calculer deux contrats de même hash.


== Meet in the middle.

On peut résoudre le problème #pbm[Somme] en $2^n$ par force brute.
Peut-on le faire en $sqrt(2^n) = 2^(n/2)$ ?
Oui, l'idée est de procéder comme ci-après.
- Partitionner $T$ en $T_1$ et $T_2$ de taille $n\/2$ ;
- Calculer toutes les sommes partielles $P_1$ de $T_1$ ($-> bigO^star (2^(n/2))$) ;
- Calculer toutes les sommes partielles $P_2$ de $T_2$ ($-> bigO^star (2^(n/2))$) ;
- Trier $P_1$ et $P_2$ (au moment de la construction).
Pour trouver $S$, on prend $x_a in P_1$ et $y_b in P_2$ (avec $a = 1$ et $b = (2^(n/2))$ au début) puis 
- si $x_a + y_b < S$ alors $a <- a + 1$ ;
- si $x_a + y_b > S$ alors $b <- b - 1$.

On obtient la solution en $bigO^star (2^(n/2))$.

== 3-SAT avec affectation partielle.

En force brute, on peut construire une affectation en $bigO^star (2^n)$.

Par _affectation partielle_ on entend une fonction partielle $a : {x_1, ..., x_n} harpoon {bold(sans(V)), bold(sans(F))}$, ou de manière équivalente une fonction totale $ a : {x_1, ..., x_n } -> {bold(sans(V)), bold(sans(F)), square}$.

On impose des règles :
+ Si une clause de $F$ possède un littéral $bold(sans(V))$, on la supprime ;
+ Si une clause de $F$ ne possède que des littéraux $bold(sans(F))$, on retourne FAUX ;
+ Si une clause de $F$ possède un littéral $bold(sans(F))$, on la supprime ;
+ Si une clause de $F$ possède un littéral, on l'affecte à $bold(sans(V))$ ;
+ Si $F$ est vide, on retourne VRAI.

#algo(name: [Premier algorithme $R$])[
  #algo-if[il existe une clause $(ell_1 or ell_2)$ dans $F$][
    #algo-return[ ] #h(1fr)~
      $ &R(F, a union {ell_1 = bold(sans(V)), ell_2 = bold(sans(V))}) or\ &R(F, a union {ell_1 = bold(sans(V)), ell_2 = bold(sans(F))}) or\ &R(F, a union {ell_1 = bold(sans(F)), ell_2 = bold(sans(V))}) $
  ][
    il existe une clause $(ell_1 or ell_2 or ell_3)$
  ][
    #algo-return[
      les 7 possibilités
    ]
  ]
  On traite aussi les cas "plus triviaux"
]

On obtient une complexité en $bigO^star (1.91^n)$.
Peut-on faire mieux ?


#algo(name: [Second algorithme $R'$])[
  #algo-if[il existe une clause $(ell_1 or ell_2)$ dans $F$][
    De même
  ][
    il existe une clause $(ell_1 or ell_2 or ell_3)$
  ][
    #algo-return[ ] #h(1fr)~
    $ &R(F, a union {ell_1 = bold(sans(V))}) or\ &R(F, a union {ell_1 = bold(sans(F)), ell_2 = bold(sans(V))}) or\ &R(F, a union {ell_1 = bold(sans(F)), ell_2 = bold(sans(F)), ell_3 = bold(sans(V))}) $
  ]
]

On obtient alors une complexité en $bigO^star (1.84^n)$.

Pour continuer, on utilise une méthode décrite par Monien & Speckenmeyer.
On dit qu'une affectation $a$ est _autarcique_ si toutes les clauses qui intersectent $a$ sont positives.
Si $a$ est une clause non autarcique, on a au moins une clause qui est réduite, et donc devient de taille 2.
On fait un branchement sur les clauses de taille 2.

On obtient une complexité en $bigO^star (1.618^n)$.

== 3-SAT en recherche locale.

Le but est, à partir d'une affectation totale $a$, on la modifie jusqu'à trouver une solution.

On notera $a plus.circle (ell_i = b)$ pour dire que l'on affecte $b$ à $ell_i$ dans la nouvelle affectation, et sinon on fait comme dans $a$.

#algo(name: [HAM$(F, a, h)$])[
  #algo-if[
    $a$ satisfait $F$
  ][
    #algo-return[VRAI (ou $a$)]
  ][
    $h = 0$
  ][
    #algo-return[FAUX]
  ][
    Il existe une clause $ell_1 or ell_2 or ell_3$ non satisfaite par $a$ dans $F$.
    #algo-return[ ] #h(1fr)~
    $ &"HAM"(F, a plus.circle {ell_1 = bold(sans(V))}, h-1) or\ &"HAM"(F, a plus.circle {ell_1 = bold(sans(F)), ell_2 = bold(sans(V))}, h-1) or\ &"HAM"(F, a plus.circle {ell_1 = bold(sans(F)), ell_2 = bold(sans(F)), ell_3 = bold(sans(V))}, h-1) $
  ]
]

Remarquons qu'exécuter $"HAM"(F, a = * |-> bold(sans(V)), h = n)$ résout 3-SAT.

De plus, la distance entre $a$ et une affectation (si elle existe) qui satisfait $F$ décroit de 1, d'où sa correction.
Mais, il a une complexité en $bigO^star (3^n)$...

On peut aussi exécuter 
$ "HAM"(F, a = * |-> bold(sans(V)), h = n\/2) or "HAM"(F, a = * |-> bold(sans(F)), h = n\/2), $
et on obtient une complexité en $bigO^star (3^(n/2)) = bigO^star (1.73^n)$.

On peut généraliser : on prend $s$-points qui couvrent avec leur $h$-voisinage tout hypercube de dimension $n$ (l'espace des valuations).
C'est un code-correcteur-_like_.
On obtient une complexité en~$bigO^star (s 3^t)$.

Tentons avec $t = n / 4$.
Combien faut-il de points sur l'hypercube de dimension $n$ pour que leur voisinage à distance $n/4$ couvre tout ?

On a une borne inf, appelée _borne de volume_, c'est $2^n / "“taille du voisinage”"$
où la “taille du voisinage” est 
$ 1 + n + binom(n, 2) + dots.c + binom(n, n\/4) tilde bigTheta^star binom(n, n \/ 4) tilde 2^(H(1/4) dot n). $
La borne inf est donc $2^((1 - H(1/4)) dot n)$.

La bonne nouvelle est qu'il suffit de choisir $2^((1 - H(1/4)) dot n) dot p(n)$ points choisis aléatoirement.
On a donc $s = bigO^star (2^((1 - H(1/4)) dot n))$ points pour~$t = 1/4$, ce qui donne un branchement de $3^(n/4)$.
La complexité est en $2^((1 - H(1/4)) dot n) dot 3^(n/4)$.

On rappelle que $H(p) = -p log_2 p - (1-p) log_2 (1-p)$.
On calcule donc $H(1/4) = 2 - 3/4 log 3$.
Ceci simplifie le calcul de la complexité en $2^((log 3 - 1) dot n) = (3/2)^n = 1.5^n$.
C'est bien mieux !

== Nombre chromatique.

On note $chi(G)$ le _nombre chromatique_ d'un graphe $G$, c'est-à-dire le plus petit nombre d'ensembles indépendants qui couvrent $V$.



Comment décider si, par exemple, $chi(G) <= sqrt(\# V)$ ? En force brute, on a $bigTheta^star (sqrt(n)^n)$.

#theorem(name: [Björklund & Husfeld, 2006])[
  On peut calculer $chi(G)$ en $bigO^star (2^n)$.
]

On note $C_k (G)$ le nombre de couvertures de $V$ par $I_1, ..., I_k$ (c'est bien un $k$-uplet et non un ensemble de taille $k$) indépendants de $G$, puis $S(X)$ pour $X subset.eq V$ le nombre d'indépendants disjoints de $X$.

#theorem[
  $ C_k (G) = sum_(X subset.eq V) (-1)^abs(X) dot s(X)^k $
]

Puis, pour calculer $s(X)$, il suffit de procéder par programmation dynamique :
- $s(V) = 1$ ;
- $forall X, forall v in.not X, s(X) = s(X union {v}) + s(X union {v} union N(v))$,
où $N(v)$ est le voisinage de $v$.

On peut calculer $s(X)$ en $bigO^star (2^n)$.
























#pagebreak(weak: true)
#pagebreak(weak: false)

#counter(heading).update(0)
#set heading(numbering: (..nums) => {
  if nums.pos().len() == 1 {
    return "Annexe " + numbering("A.", ..nums)
  }
  return numbering("A.1.a.i.", ..nums)
})

= Génération aléatoire uniforme.

Le but est double :
- tester des hypothèses ;
- générer des _benchmarks_.

== Nombre aléatoire dans $[N] = {1,...,N}$.

Pas grand chose de nouveau dans cette partie (voir la littérature), il n'y a qu'une remarque.

#remark[
  Éviter d'utiliser `rand() % N` !
  En effet, on a un biais vers les petites valeurs.
  // TODO(Hugo) : Faire la figure
]

== Permutation aléatoire uniforme.

Cette génération peut être utiliser en _pre-process_ de Quicksort par exemple.

#algo(name: [Génération de permutation])[
  #algo-for[$i$ *_de_* $n$ *_à_* $2$][
    $j <-$ un nombre aléatoire dans $[i]$\
    Échanger $T[i]$ et $T[j]$
  ]
]

Codez cet algorithme.
Puis, évaluez 
- la distribution des longueurs des cycles ;
- la probabilité que la permutation est un dérangement (_i.e._ n'a aucun point fixe).

== Matrice à coefficients $0$/$1$ et graphes aléatoires.

On peut tirer chaque arête d'un graphe avec une probabilité $p$.
On définit le modèle $cal(G)(n, p)$ par : $G in cal(G)(n, p)$ si $G$ à $n$ sommets avec une probabilité $p$ d'avoir une arête.

#remark[
  Tous les graphes aléatoires se ressemblent.
  En effet, ceci est une conséquence des théorèmes ci-après.
]

#theorem(name: emph[Loi 0-1])[
  Pour toute formule $F$ du premier ordre, on a 
  $ lim_(n -> oo) upright(P)(G tack.double F | G in cal(G)(n, p)) = 0 "ou" 1. $
]

Ce théorème est faux pour une formule du second ordre.

#example[
  La formule
  $ forall x, y in V, (x y in E) or (exists z in V, x z in E and y z in E) $
  est vrai si, et seulement si le diamètre $d$ du graphe vérifie $d <= 2$.
]

Si on tire chaque parie d'entiers $i,j in NN$ avec une probabilité $1 \/ 2$, on obtient presque sûrement le même graphe dénombrable $R$ _à isomorphisme près_.
La limite (dans la loi 0-1) vaut 1 _ssi_ $R tack.double F$.

== Arbre aléatoire uniforme sur $[N]$.


=== Première tentative.
Voici comment procéder :
- tirons une permutation aléatoire des arêtes possibles (il y en a $binom(n,2)$)
- appliquer l'algorithme de Kruskal.

L'espérance du diamètre n'est pas $sqrt(n)$. // TODO(Hugo) : Ajouter emoji snif

=== Deuxième tentative.


*Combien y a-t-il d'arbres sur $[n]$ ?*
- $n = 1$ : il y en a $1 = 1^(-1)$ ;
- $n = 2$ : il y en a $1 = 2^0$ ;
- $n = 3$ : il y en a $3 = 3^1$ ;
- $n = 4$ : il y en a $16 = 4^2$ ;
- $n = 5$ : il y en a $125 = 5^3$ ;
- $...$



#theorem[
  Il y a $n^(n-2)$ arbres sur ${1,...,n}$.
]

#proof[
  On applique le _codage de Prüfer_ qui réalise une bijection des arborescences#footnote[Une arborescence est un arbre auquel on indique clairement la racine.] enracinés sur ${1,...,n}$ avec les suites de longueur $n - 1$ sur ${1,...,n}$.
]

#algo(name: [Codage de Prüfer])[
  $C <- epsilon$

  #algo-while[$|A|>1$][
    Trier les feuilles par ordre croissant

    #algo-for[_*toute*_ feuille $f$][
      $C <- C dot "parent"(f)$
    ]
  ]

  Supprimer les feuilles de $A$

  #algo-return[$C$]
]

Ce codage admet une réciproque.

#example(name: [Codage de Prüfer])[
  // TODO(Hugo) : Faire l'arbre dont le codage est 1 3 9 8 8 7 7 1 7
]

#example(name: [Activité pratique])[
  - Prendre votre numéro de téléphone
  - Supprimer le zéro initial
  On obtient un mot de 9 lettres sur un alphabet ${ mono(0), ..., mono(9) }$.
  C'est le codage de Prüfer d'une arborescence.
  *Trouver cet arbre.*
]

Pour tirer un nombre aléatoire sur $[N]$, on procède donc par :
- tirer une suite aléatoire de $[N]^(N-1)$ ;
- appliquer le décodage de Prüfer ;
- oublier la racine (passage d'une arborescence à un arbre).


#proposition[
  Si $G$ est un graphe connexe et $x y$ une arête, alors la probabilité
  $ upright(P)("Arbre couvrant tiré uniformément contient" x y) $
  est égale à la résistance entre $x$ et $y$ si toutes les arêtes ont une résistance $1 med Omega$.
]

#proposition[
  Le nombre d'arbres couvrants dans un graphe connexe $G$ est égal, au signe près, au déterminant d'un mineur principal de la matrice Laplacienne de $G$, notée $L(G)$ où
  $ L(G) = A(G) D(G) $
  où
  - $A(G)$ est la matrice d'adjacence de $G$ ($a_(u v) = 1$ si $u v$ est une arête de $G$ et $0$ sinon) ;
  - $D(G)$ est la matrice diagonale où $d_(v v)$ est le degré de $v$.
]

#example[
  Pour le graphe complet $K_n$ à $n$ éléments, on a :
  $ L(K_n) = mat(
    -(n-1), quad 1, dots.c, 1;
    1, dots.down, dots.down, dots.v;
    dots.v, dots.down, dots.down, 1;
    1, dots.c, 1, -(n-1)
  ) $
  et donc le déterminant est :
  $
    det mat(
      -(n-1), quad 1, dots.c, 1;
      1, dots.down, dots.down, dots.v;
      dots.v, dots.down, dots.down, 1;
      1, dots.c, 1, -(n-1)
    ) = det mat(
      -1, quad 0, dots.c, 0;
      0, -n, dots.down, dots.v;
      dots.v, dots.down, dots.down, 0;
      0, dots.c, 0, -n
    ) = (-1)^(n-1) dot n^(n - 2).
  $
  On retrouve bien le nombre $n^(n-2)$.
]

=== Cas du couplage.

Comment tirer un couplage uniformément dans un graphe biparti ?
C'est dur à résoudre exactement...

En effet, le théorème ci-dessous l'explique.
#theorem(name: [Valient])[
  Compter le nombre de couplages dans un graphe biparti est un problème $sharp PP$-complet.#footnote[Analogue de $bold("NP")$-complet pour la complexité de comptage de solution d'un problème.]
]

Si on savait compter efficacement, alors on saurait tirer uniformément.
En effet, il suffit de compter le nombre de de couplages contenant une arête $e$ puis de compter le nombre total de couplages.
On peut calculer des probabilités donc tirer uniformément.






















#toc()
