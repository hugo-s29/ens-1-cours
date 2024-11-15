#import "../../global.typ": *

#show: it => setup-layout(it)

#set page(header: [FDI/TD n°8 #h(1fr) Hugo #smallcaps[Salou] -- #smallcaps[ens l3]])

#set highlight(fill: blue, extent: 0.2pt)
#show highlight: set text(white)

#let underline = highlight

#align(center)[
  #set text(1.3em, font: "Latin Modern Sans")
  *-- Compléments pour l'exercice 4 --*
]

Considérons le langage $ L := { angle.l M_1, M_2 angle.r in Sigma^star | cal(L)(M_1) = cal(L)(M_2) }. $

*But.*
Montrons que $L$ n'est pas décidable, ni Turing-reconnaissable, ni co-Turing-reconnaissable.

On admet que les langages 
$ A_sans("TM") = { angle.l M, w angle.r in Sigma^star | M "accepte" w }\
  macron(A)_sans("TM") = { angle.l M, w angle.r in Sigma^star | M "n’accepte pas" w } = Sigma^star without A_sans("TM")
$ sont indécidables.
On admet également que $A_sans("TM")$ est Turing-reconnaissable mais pas co-Turing-reconnaissable.
Réciproquement, $macron(A)_sans("TM")$ est co-Turing-reconnaissable mais pas Turing-reconnaissable.

#let machine(it, moveby: -3em) = context {
  let prev-color = main-color.get()
  main-color.update(_ => purple)
  move(block(stroke: purple + 0.5pt, inset: 10pt, radius: 3pt, text(purple, it)), dx: moveby)
  main-color.update(_ => prev-color)
}

Par la suite, on considère deux machines :
- la machine $M_emptyset$ qui rejette toutes les entrées ;
- la machine $M_(w,N)$ dont l'implémentation est ci-dessous :
  #grid(
    columns: (auto, 1fr),
    machine[
      + On ignore l'entrée.
      + On simule $N$ sur $w$.
      + Si $N$ accepte $w$,\
        $quad$ alors on accepte.
      ],[
        Son langage est
        $ cal(L)(M_(w,N)) = cases(Sigma^star &"si" N "accepte" w, emptyset &"sinon".) $
      ]
  )

= Une première réduction.

On procède par réduction au langage $macron(A)_sans("TM")$.
On considère la fonction calculable 
$ f : quad quad Sigma^star &--> Sigma^star \
  angle.l N, w angle.r &arrow.long.bar angle.l M_(w,N), M_emptyset angle.r. $
et on a l'équivalence :
$ angle.l M_(w,N), M_emptyset angle.r in L 
  <==>& cal(L)(M_(w,N)) = cal(L)(M_emptyset) = emptyset\
  <==>& N "n’accepte pas" w\
  <==>& angle.l N, w angle.r in macron(A)_sans("TM"). $

De cette réduction,  par la question 2 de l'exercice 1, et parce que le langage $macron(A)_sans("TM")$ n'est pas décidable, #underline[_L_ n'est pas décidable].

Mais, on sait également que #underline[_L_ n'est pas Turing-reconnaissable] en appliquant le lemme ci-dessous.
#lemma[
  Si $A$ se réduit à $B$ alors :
  - si $B$ est Turing-reconnaissable, alors $A$ aussi ;
  - si $A$ n'est pas Turing-reconnaissable, alors $B$ non plus.
]
#proof(name: [C'est une preuve quasi-identique à celle de Q2 dans l'exercice 1])[
  - Supposons que $A$ se réduit (via une fonction $f$ calculable) à $B$ et que $B$ est Turing-reconnaissable par une machine $R$.
    On a donc l'équivalence $w in A <==> f(w) in B$.
    On construit la machine ci-dessous qui reconnait $A$.
    #align(center)[
    #machine(moveby: 0pt)[
      #set align(left)
      + On calcule $f(w)$.
      + On simule $R$ sur l'entrée $f(w)$.
      + Si $R$ accepte $f(w)$,\
        $quad$ alors on accepte.
    ]
    ]
  - Contraposée du premier point.
]


= Une seconde réduction.

On va démontrer que le langage $macron(A)_sans("TM")$ se réduit à 
$ macron(L) = { angle.l M_1, M_2 angle.r | cal(L)(M_1) != cal(L)(M_2) }. $

On considère la fonction calculable 
$ g : quad quad Sigma^star &--> Sigma^star \
  angle.l N, w angle.r &arrow.long.bar angle.l M_(w,N), M_(Sigma^star) angle.r. $
et on a l'équivalence :
$ angle.l M_(w,N), M_(Sigma^star) angle.r in macron(L)
  <==>& cal(L)(M_(w,N)) != cal(L)(M_(Sigma^star)) = Sigma^star\
  <==>& cal(L)(M_(w,N)) = emptyset\
  <==>& N "n’accepte pas" w\
  <==>& angle.l N, w angle.r in macron(A)_sans("TM"). $
Ainsi, parce que $macron(A)_sans("TM")$ n'est pas Turing-reconnaissable, que $macron(L)$ n'est pas Turing-reconnaissable (lemme précédent).
On en conclut que #underline[le langage _L_ n'est pas co-Turing-reconnaissable].
