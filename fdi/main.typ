#import "../global.typ": *

#show: it => setup-layout(it)

#title(with-bars: false)[Fondements de l'informatique]

#show math.Sigma: math.italic

Dans ce cours, nous nous intéresserons à des _modèles de calcul_, comme ceux ci-dessous :
1. les automates finis, qui engendrent les langages rationnels ;
2. les automates à pile, qui engendrent les langages algébriques ;
3. les machines de #sc[Turing], qui engendrent les langages décidables.

Comme vu dans la thèse de #sc[Church-Turing], la machine de #sc[Turing] est le modèle le plus complexe que l'on peut exécuter.
Mais, il existe des modèles équivalents : les fonctions récursives, le $lambda$-calcul.

On étudiera un peu de complexité : avec les classes $bold(upright(P))$ et $bold("NP")$, et le théorème de Cook-Levin.

= Automates finis.

On se place dans la situation suivante : on modélise une porte automatique, avec un capteur avant la porte et un capteur après la porte.
On peut modéliser le mécanisme de contrôle de la porte par un automate.

#definition[
  Un automate fini est un 5-uplet $(Q, Sigma, delta, q_0, F)$ avec
  + $Q$ est l'_ensemble_ fini _des états_ ;
  + $Sigma$ est l'_alphabet d'entrée_ ;
  + $delta : Q times Sigma -> Q$ est la _fonction de transition_ (totale) ;
  + $q_0 in Q$ est l'_état initial_ ;
  + $F subset.eq Q$ est l'_ensemble des états finaux_.
]



#example[
  #figure(
    automaton(
      (
        r0: (r0: "0", r1: "1"),
        r1: (r1: "1", r2: "0"),
        r2: (r1: ("0", "1")),
      ),
      labels: (r0 : $ r_0 $, r1 : $ r_1 $, r2 : $ r_2 $),
      final: "r1",
      input-format: (inputs) => inputs.sorted().map(math.mono).join($,$),
    )
  )
  Cet automate reconnaît l'ensemble des mots où il y a au moins un $mono(1)$, et le dernier $mono(1)$ est suivi d'un nombre pair de $mono(0)$.
]

#definition[
  Étant donné l'état initial $q_0$ et un mot $w_1 w_2 ... w_n in Sigma^star$, la _suite de transition_ d'un automate $M$ est défini par la suite :
  $ q_0 -> delta(q_0, w_1) -> delta(delta(q_0, w_1), w_2) -> dots.c $
  avec $q_i = delta(q_(i-1, w_i))$.

  On dit que $w$ est _accepté_ si $q_n in F$.

  Le langage reconnu est donc
  $ cal(L)(M) = { w in Sigma^star | w "est accepté par" M } $

  Un langage reconnu par un automate fini est dit _rationnel_.
]

On étend la fonction de transition $delta$ : pour $w in Sigma^star$, on note $delta(q, w)$ (ou $delta^star (q, w)$) par l'état obtenu après lecture du mot $w$ en partant de l'état $q_0$.
On l'appelle la fonction de transition étendue.

== Propriétés de clôture.


On définit les opérations ci-dessous :
1. Complément $macron(L) = { w in Sigma^star | w in.not L }$ ;
2. Union $L union M$ ;
3. Concaténation $L dot M = { x y | x in A "et" y in B }$ ;
4. Étoile $L^star = { x = x_1 x_2 ... x_k | x_i in L "et" k >= 0 }$


#theorem[
  L'ensemble des langages rationnels est clos par complément.
]

#proof[
  On réalise la construction suivante. Soit $L$ reconnu par $M = (Q, Sigma, delta, q_0, F)$, alors 
  $macron(L)$ est reconnu par $macron(M) = (Q, Sigma, delta, q_0, macron(F))$ avec $macron(F) = Q without F$.
]

#theorem[
  L'ensemble des langages rationnels est clos par union.
]

#proof[
  On réalise la construction suivante.
  Soit $L_1$ reconnu par $M_1 = (Q_1, Sigma, delta_1, q_1, F_1)$
  et $L_2$ reconnu par $M_2 = (Q_2, Sigma, delta_2, q_2, F_2)$.
  On veut construire $M$ qui reconnaît $L_1 union L_2$.
  On définit $M$ comme $M = (Q, Sigma, delta, q_0, F)$ par :
  - $Q = Q_1 times Q_2$ ;
  - $delta((r_1, r_2), a) = (delta_1 (r_1, a), delta_2 (r_2, a))$ ;
  - $q_0 = (q_1, q_2)$ ;
  - $F = { (q_1, q_2) in Q | q_1 in F_1 "ou" q_2 in F_2 } = (F_1 times Q_2) union (Q_1 times F_2)$.

  Avec cette construction, on a :
  $ delta^star (q_0, q) = (delta^star_1 (q_1, w), delta^star_2 (q_2, w)), $
  et au vue de la définition de $F$, on peut en conclure que $M$ reconnaît bien $L_1 union L_2$.
]


On souhaite démontrer la clôture par concaténation, mais pour cela, on va devoir utiliser des automates non déterministes.

#definition[
  Un _automate fini non déterministe_ (_NFA_) est un $5$-uplet $N = (Q, Sigma, delta, q_0, F)$ :
  + $Q$ est l'_ensemble_ fini _des états_ ;
  + $Sigma$ est l'_alphabet d'entrée_ ;
  + $delta : Q times (Sigma union {epsilon}) -> wp(Q)$ est la _fonction de transition_ ;
  + $q_0 in Q$ est l'_état initial_ ;
  + $F subset.eq Q$ est l'_ensemble des états finaux_.
]

Dans un automate non déterministe, il est possible de se trouver dans le cas $delta(q, a) = emptyset$.
Dans ce cas, la chaîne de transitions est rompue.

#definition[
  On dit qu'un mot $w$ est _accepté_ s'il existe un calcul acceptant sur l'entrée $w$.

  Formellement, $w$ est accepté si $w = y_1 y_2 dots.c y_m$ avec $y_i in Sigma union { epsilon }$
  de sorte qu'il existe une suite de $m$ états $r_1, r_2, ..., r_m in Q$ avec :
  1. $r_0 = q_0$ ;
  2. $r_i in delta(r_(i-1), y_i)$ pour $i in [|1, m|]$ ;
  3. $r_m in F$.
]

#example[
  #figure(
    automaton(
      (
        q1: (q1: ("0", "1"), q2: "1"),
        q2: (q3: ("0", "&")),
        q3: (q4: "1"),
        q4: (q4: ("0", "1"))
      ),
      labels: (q1: $ q_1 $, q2: $ q_2 $, q3: $ q_3 $, q4: $ q_4 $),
      input-format: (inputs) => inputs.sorted().map(inp => {
        if inp == "&" { return $epsilon$ }
        else { return $mono(inp)$ }
      }).join($,$),
    )
  )

  On lit le mot $mono(010110)$ avec l'automate ci-dessus, et on obtient l'arbre de calculs ci-dessous.
]

#figure(
  cetz.canvas({
    import cetz.draw: *
    import cetz.tree: *
    import cetz.decorations: *

    set-style(stroke: (cap: "round", join: "round"))

    tree(
      ($ q_1 $,
        ($ q_1 $,
          ($ q_1 $,
            ($ q_1 $,
              ($ q_1 $,
                ($ q_1 $,
                  $ q_1 $
                ),
                ($ q_2 $,
                  $ q_3 $,
                ),
                ($ q_3 $
                )
              ),
              ($ q_2 $,
              ),
              ($ q_3 $,
                ($ q_4 $, $ q_4 $)
              ),
            )
          ),
          ($ q_2 $,
            ($ q_3 $,($ q_4 $, ($ q_4 $, $ q_4 $)))
          ),
          ($ q_3 $
          ),
        )
      ),
      draw-node: (node, ..) => {
        if node.content == $ q_4 $ {
          circle((), radius: .4, stroke: blue, fill: white)
          circle((), radius: .35, fill: blue, stroke: none)
        } else {
          circle((), radius: .35, fill: blue, stroke: none)
        }
       content((), text(white, [#node.content]))
     },
     draw-edge: (from, to, prev, next, ..) => {
       let (a, b) = (from + ".center", to + ".center")
       let x1 = if prev.content == $ q_4 $ { .45 } else { .4 }
       let x2 = if next.content == $ q_4 $ { .45 } else { .4 }

       line((a, x1, b), (b, x2, a), mark: (end: ">", scale: 0.5, fill: black))
     },
     grow: 1.5,
    )

    for x in (0,1,0,1,1,0) {
      line((-1, -1.5/2), (7,-1.5/2), stroke: (dash: "dashed", paint: gray))
      content((-1.5,-1.5/2), text(gray, $ mono(#str(x)) $))
      translate((0,-1.5))
    }

    brace((5.5, -0.5), (3.5, -0.5))
    content((4.5, -1.5))[On arrive à\ l'état final.]
  })
)

#theorem[
  Un langage est reconnaissable par NFA si, et seulement s'il est rationnel.
]

#proof[
  Dans un sens, cela est évident : un automate fini déterministe est un NFA.
  L'autre sens demande une construction.

  Soit $N = (Q, Sigma, delta, q_0, F)$ un automate fini non déterministe reconnaissant $L subset.eq Sigma^star$.
  On construit $M = (Q', Sigma, delta', q_0', F')$ un automate fini déterministe reconnaissant $L$ :
  on pose 
  1. États : $Q' = wp(Q)$,
  2. États finaux : $F' = { R in Q | R sect F != emptyset }$,
  3. Fonction de transition :
    - si $N$ ne contient pas d'$epsilon$-transitions, alors on a $delta'(R, a) = union.big_(r in R) delta(r, a)$
    - sinon, on a $delta'(R, a) = union.big_(r in R) E(delta(r, a))$
  4. État initial : $q_0' = E({ q_0 })$.
  
  On définit la fonction $E$ comme :
  $ E(R) = { q in Q | q #rm[peut-être atteint à partir d'un état de $R$ en  prenant une suite finie d'$epsilon$-transitions] }. $
  On la nomme la _clôture_ par $epsilon$-transitions. (Dans l'exemple précédent, on a $E({q_2}) = {q_2, q_3})$.)

  On peut démontrer que l'on a $delta^star (q_0, w) = delta'^star (q_0', w)$ par récurrence pour conclure.
]

#theorem[
  L'ensemble des langages rationnels est clos par concaténation.
]

#proof[
  Soient deux NFA $N_1$ et $N_2$ reconnaissant $L_1$ et $L_2$. On construit un automate $N$ qui reconnaît $L_1 dot L_2$.
  L'_idée_ est la suivante : si $x in L_1 dot L_2$ alors $x = y_1 y_2$ avec $y_1 in L_1$ et $y_2 in L_2$.
  Il suffit donc d'enchaîner les états initiaux $N_2$ à la suite des états finaux de $N_1$, avec des $epsilon$-transitions.

  Posons $N_1 = (Q_1, Sigma, delta_1, q_1, F_1)$ et $N_2 = (Q_2, Sigma, delta_2, q_2, F_2)$ et on construit $N = (Q, Sigma, delta, q_0, F)$ par :
  1. États : $Q = Q_1 union.dot Q_2$ ;
  2. État initial : $q_0 = q_1$ ;
  3. États finaux : $F = F_2$ ;
  3. Fonction de transition :
  $ delta(q, a) = cases(
    delta_1 (q, a) &"si" q in Q_1 without F_1,
    delta_1 (q, a) &"si" q in F_1 "et" a != epsilon,
    delta_1 (q, epsilon) union { q_2 } quad &"si" q in F_1 "et" a = epsilon,
    delta_2 (q, a) &"si" q in Q_2
  ) $
]

#theorem[
  L'ensemble des langages rationnels est clos par étoile.
]

#proof[
  Soit un NFA $N$ reconnaissant $L$. On construit un automate $N^star$ qui reconnaît $L^star$.

  On construit un automate comme décrit ci-après :
  1. on ajoute un état initial final $q$ ;
  2. on ajoute une $epsilon$-transition de $q$ à l'état initial de $N$ ;
  3. on ajoute des $epsilon$-transitions entre les états finaux de $N$ et l'état initial de $N$.

  Cet automate reconnaît bien $L^star$.
]

= Expressions rationnelles.

Une expression rationnelle ("_regular expressions_" en anglais) est une expression de la forme $(0 union 1)^star 1 (0 0)^star$.

#definition[
  Les expressions rationnelles sont de la forme :
  + $a$ avec $a in Sigma$ ;
  + $epsilon$, le mot vide ;
  + $emptyset$, l'ensemble vide ;
  + $R_1 union R_2$ où $R_1$ et $R_2$ sont deux expressions rationnelles déjà construites ;
  + $R_1 dot R_2$ où $R_1$ et $R_2$ sont deux expressions rationnelles déjà construites ;
  + $R^star$ où $R$ est une expression rationnelle.

  On note $cal(R)(Sigma)$ l'ensemble des expressions rationnelles sur l'alphabet $Sigma$.
]

#definition[
  On définit $cal(L)(R) subset.eq Sigma^star$ le langage de l'expression $R$ :
  + $cal(L)(a) = { a }$ avec $a in Sigma$ ;
  + $cal(L)(epsilon) = { epsilon }$ ;
  + $cal(L)(emptyset) = emptyset$ ;
  + $cal(L)(R_1 union R_2) = cal(L)(R_1)  union cal(L)(R_2)$ ;
  + $cal(L)(R_1 dot R_2) = cal(L)(R_1)  dot cal(L)(R_2)$ ;
  + $cal(L)(R^star) = cal(L)(R)^star$.
]

#proposition[
  Si $L$ est décrit par une expression rationnelle, alors $L$ est reconnaissable par un automate.
]

#proof[
  On traîte les différents cas :
  + si $R = a$ avec $a in Sigma$, alors on construit l'automate ci-dessous ;
    #figure(
      automaton(
        (
          q0: (q1: "a", q2: "b"),
          q2: (q2: ("a", "b")),
          q1: (q2: ("a", "b")),
        ),
        layout: finite.layout.circular.with(radius: 1.5),
        labels: (q1: $ q_1 $, q2: $ q_2 $, q0: $ q_0 $),
        input-format: (inputs) => inputs.sorted().map(inp => {
          if inp == "&" { return $epsilon$ }
          else { return $mono(inp)$ }
        }).join($,$),
      )
    )
  + si $R = epsilon$, alors on construit l'automate ci-dessous ;
    #figure(
      automaton(
        (q0: (),),
        layout: finite.layout.circular.with(radius: 1.5),
        labels: (q1: $ q_1 $, q2: $ q_2 $, q0: $ q_0 $),
        input-format: (inputs) => inputs.sorted().map(inp => {
          if inp == "&" { return $epsilon$ }
          else { return $mono(inp)$ }
        }).join($,$),
      )
    )
  + si $R = emptyset$ alors on construit l'automate ci-dessous;
    #figure(
      automaton(
        (q0: (),),
        final: "",
        layout: finite.layout.circular.with(radius: 1.5),
        labels: (q1: $ q_1 $, q2: $ q_2 $, q0: $ q_0 $),
        input-format: (inputs) => inputs.sorted().map(inp => {
          if inp == "&" { return $epsilon$ }
          else { return $mono(inp)$ }
        }).join($,$),
      )
    )
  + propriétés de clôture des langages rationnels (réunion) ;
  + propriétés de clôture des langages rationnels (concaténation) ;
  + propriétés de clôture des langages rationnels (étoile).
]

Un _automate non déterministe généralisé_ (GNFA) est un automate où
- les transitions sont étiquetées par des expressions rationnelles ;
- de l'état initial, une flèche va vers chaque état, mais ne reçoit aucune autre flèche ;
- un unique état final, qui reçoit une flèche de chaque état, mais n'en émet aucune ;
- pour les autres états : une flèche vers tous les autres états, sauf l'état initial.

#definition(name: [GNFA, formellement])[
  Un _GNFA_ est un $5$-uplet $(Q, Sigma, delta, q_0, q_upright(f))$ avec :
  - $Q$ l'ensemble fini des états ;
  - $Sigma$ l'alphabet fini ;
  - $delta : (Q without { q_upright(f) }) times (Q without { q_0 }) -> cal(R)(Sigma)$ la fonction d'étiquetage de transition ;
  - $q_0$ l'état initial ;
  - $q_upright(f)$ l'état final.
]

#definition[
  On dit d'un mot $w in Sigma^star$ qu'il est _accepté_ s'il existe $k$ mots~$w_1, ..., w_k$ tels que $w = w_1 ... w_k$ et 
  des états $q_0, ..., q_k$ avec $q_0$ l'état initial, et $q_k = q_upright(f)$ l'état final, et que $w_i in cal(L)(delta(q_(i-1), q_i))$, quel que soit $i$.
]

#proposition[
  Si $L$ est reconnaissable par un automate fini, alors $L$ peut être décrit par une expression rationnelle.
]

#lemma(name: [1])[Tout GNFA avec $k>2$ états est équivalent à un GNFA avec~$k-1$ états.]
#lemma(name: [2])[Tout DFA admet un GNFA équivalent.]

#proof(name: [du lemme~(1)])[
  On veut supprimer $q_"sup"$ dans $G$, avec $q_"sup" in.not {q_0, q_upright(f)}$.
    #figure(
      automaton(
        (
          q0 : (q1 : "R_4", q2: "R_1"),
          q1 : (),
          q2 : (q2: "R_2", q1: "R_3"),
        ),
        final: "",
        initial: "",
        layout: finite.layout.circular.with(radius: 1.5),
        labels: (q1: $ q_i $, q2: $ q_j $, q0: $ q_"sup" $),
        input-format: (inputs) => inputs.sorted().map(inp => {
          eval("$ " + inp + " $")
        }).join($,$),
      )
    )

    On peut le remplacer par une unique transition $q_i -->^(R_4 union R_1 R_2^star R_3) q_j$.
    On fait cette transformation pour tous les couples $(i,j)$.

    On obtient un automate généralisé $G'$ équivalent à $G$. En effet, soit $w$ un mot accepté par $G$ et soit $q_0; ..., q_(k-1), q_upright(f)$ la suite des états dans un calcul acceptant de $G$ sur l'entrée $w$. On obtient une ou des états dans un calcul acceptant 
]

#proof(name: [du lemme~(2)])[
]

#proof(name: [de la proposition])[
  On passe d'un DFA à un GNFA puis à une expression rationnelle.

]

#theorem[
  Un langage peut être décrit par une expression rationnelle si et seulement s'il est rationnel.
]


*La suite du cours de Fondements de l'Informatique (FDI) ne sera pas tapé à l'ordinateur.
Regardez le livre _Introduction to the Theory of Computation_ de Michael Sipser.
Le cours de FDI est basé sur ce livre, et il contient bien plus de détails.*
