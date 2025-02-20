#let colored(arr) = {
  for (i, x) in arr.enumerate() {
    if calc.rem(i, 2) == 0 {
      text(blue, x)
    } else {
      text(purple, x)
    }
  }
}

#show "fouine": _ => text(colored("fouine".clusters()), font: "Latin Modern Sans")

#set text(font: "Latin Modern Roman")

#let mmono(it) = text(it, font: "Latin Modern Mono")

#set list(marker: ([‣], [–], [•]))

#set page(width: auto, height: auto)

#show "…": ([], [.],[.],[.], []).join(h(2pt))
#show "⋯" : ([], [⋅],[⋅],[⋅], []).join(h(2pt))

#show math.bracket.double.l : set text(purple)
#show math.bracket.double.r : set text(purple)
#show math.lambda : math.bold
#show math.lambda : set text(blue)
#show math.colon : _ => text(blue, font: "Latin Modern Roman", strong[.])

#show "id": math.sans
#show "id": math.italic
#show "id": set text(red)
#show "fst": math.sans
#show "fst": math.italic
#show "fst": set text(red)
#show "snd": math.sans
#show "snd": math.italic
#show "snd": set text(red)

#let fst = "fst"
#let snd = "snd"
#let id = "id"

#let fr(x) = text(x, eastern)

= _Traduction d'un programme fouine en fouine CPS_

Dans la suite, on notera $lambda x: med e$ au lieu de $mmono("fun") x mmono(->) e$, pour abréger les notations...\
On notera en #fr[cyan] les variables fraîches.

- $[|n|] := lambda fr(k): med (fst fr(k)) med n$

- $[|b|] := lambda fr(k): med (fst fr(k)) med b$

- $[|mmono("()")|] := lambda fr(k): med (fst fr(k)) med mmono("()")$

- $[|x|] := lambda fr(k): med (fst fr(k)) med x$

- $[|lambda x: med e|] := lambda fr(k): med (fst fr(k)) med (lambda x: med [|e|])$

- $[|e_1 med e_2|] = lambda fr(k): med [|e_2|] med (lambda fr(v): med [|e_1|] med (lambda fr(f): med fr(f) med fr(v) med fr(k), snd fr(k)), snd fr(k))$

- $[|e_1 ast.circle e_2|] := lambda fr(k): med [|e_2|] med (lambda fr(v_2): med [|e_1|] med (lambda fr(v_1): med (fst fr(k)) med (fr(v_1) ast.circle fr(v_2)), snd fr(k)), snd fr(k))$

- $[|mmono("if") b mmono("then") e_1 mmono("else") e_2|] := lambda fr(k): med [|b|] med (lambda fr(v): med mmono("if") fr(v) mmono("then") [|e_1|] med fr(k) mmono("else") [|e_2|] med fr(k), snd fr(k))$

- $[|ast.circle e|] := lambda fr(k): med [|e|] med (lambda fr(v): med (fst fr(k)) med (ast.circle fr(v)), snd fr(k))$

- $[| e_1 mmono(";") e_2 |] := lambda fr(k): med [|e_1|] med (lambda \_: med [|e_2|] med fr(k), snd fr(k))$

- $[| upright(C)(e_1, ..., e_n)  |] := lambda fr(k): med [|e_n|] med (lambda fr(v_n): med ... med ([|e_1|] med (lambda fr(v_1): med (fst fr(k)) med med upright(C)(fr(v_1), ..., fr(v_n)), snd fr(k)) ...), snd fr(k))$

- $[| mmono("while") b mmono("do") e |] := & mmono("let") mmono("rec") fr(italic("boucle")) fr(k) mmono("=")\
  & quad [|b|] med (lambda fr(v): med\
  & quad quad mmono("if") fr(v) mmono("then") [|e|] med (lambda \_: med fr(italic("boucle")) fr(k), snd fr(k))\
  & quad quad mmono("else") (fst fr(k)) med mmono("()")\
  & mmono("in") fr(italic("boucle"))$

- $[|mmono("let rec") f mmono(=) e mmono("in") e'|] := lambda fr(k): mmono("let rec") f mmono("=") [|e|] mmono("in") [|e'|] med fr(k)$

- $[|mmono("for") i mmono(=) e_1 mmono("to") e_2 mmono("do") e_3 mmono("done")|] := lambda fr(k): med [|e_1|] med &(lambda fr(v_1): med [|e_2|] med (lambda fr(v_2): med \
    &mmono("let rec") fr(italic("boucle")) i med fr(k) mmono("=")\
    & quad quad mmono("if") i <= fr(v_2) mmono("then") [|e_3|] med (lambda \_ : fr(italic("boucle")) med (i+1) med fr(k), snd fr(k)) \
    & quad quad mmono("else") (fst fr(k)) med mmono("()") \
    & mmono("in") fr(italic("boucle")) fr(v_1) 
  ))$

- $[|mmono("for") i mmono(=) e_1 mmono("downto") e_2 mmono("do") e_3 mmono("done")|] := lambda fr(k): med [|e_1|] med &(lambda v_1: med [|e_2|] med (lambda v_2: med \
    &mmono("let rec") fr(italic("boucle")) i med fr(k) mmono("=")\
    & quad quad mmono("if") i >= fr(v_1) mmono("then") [|e_3|] med (lambda \_ : fr(italic("boucle")) med (i-1) med fr(k), snd fr(k)) \
    & quad quad mmono("else") (fst fr(k)) med mmono("()") \
    & mmono("in") fr(italic("boucle")) fr(v_2)
  ))$

- $[|mmono("match") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n |] := &lambda fr(k): med [|e|] med
( dots.c (lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_1 mmono(->) [|e'_1|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_1|] med fr(k)\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd k)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &quad snd fr(k))\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_2 mmono(->) [|e'_2|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_2|] med fr(k)\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd k)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &quad snd fr(k)
  )\
  & quad quad quad quad quad dots.v\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_n mmono(->) [|e'_n|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_n|] med fr(k)\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd k)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &quad snd fr(k))\
  &(lambda \_: (snd fr(k)) bold("MatchError")) dots.c )
  $

- $[|mmono("try") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n|] := &lambda fr(k): med [|e|] med (fst fr(k), lambda v:\
  &( dots.c (lambda fr(italic("match")_"next"): med lambda v:\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_1 mmono(->) [|e'_1|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_1|] med fr(k)\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd k)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &quad snd fr(k))\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_2 mmono(->) [|e'_2|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_2|] med fr(k)\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd k)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &quad snd fr(k)
  )\
  & quad quad quad quad quad dots.v\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_n mmono(->) [|e'_n|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_n|] med fr(k)\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd k)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &quad snd fr(k))\
  &(snd fr(k)) med ) dots.c )$

- $[|mmono("raise") e|] := lambda fr(k): med [|e|] med (snd fr(k), snd fr(k))$

On définit 
- $"id" := lambda x: x$
- $"fst" := lambda (x,y): x$
- $"snd" := lambda (x,y): y$
