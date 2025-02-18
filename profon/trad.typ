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

= _Traduction d'un programme fouine en fouine CPS_

Dans la suite, on notera $lambda x: med e$ au lieu de $mmono("fun") x mmono(->) e$, pour abréger les notations...

- $[|n|] := lambda k: med (fst k) med n$

- $[|b|] := lambda k: med (fst k) med b$

- $[|mmono("()")|] := lambda k: med (fst k) med mmono("()")$

- $[|x|] := lambda k: med (fst k) med x$

- $[|lambda x: med e|] := lambda k: med (fst k) med (lambda x: med [|e|])$

- $[|e_1 med e_2|] = lambda k: med [|e_2|] med (lambda v: med [|e_1|] med (lambda f: med f med v med k, snd k), snd k)$

- $[|e_1 ast.circle e_2|] := lambda k: med [|e_2|] med (lambda v_2: med [|e_1|] med (lambda v_1: med (fst k) med (v_1 ast.circle v_2), snd k), snd k)$

- $[|mmono("if") b mmono("then") e_1 mmono("else") e_2|] := lambda k: med [|b|] med (lambda v: med mmono("if") v mmono("then") [|e_1|] med k mmono("else") [|e_2|] med k, snd k)$

- $[|ast.circle e|] := lambda k: med [|e|] med (lambda v: med (fst k) med (ast.circle v), snd k)$

- $[| e_1 mmono(";") e_2 |] := lambda k: med [|e_1|] med (lambda \_: med [|e_2|] med k, snd k)$

- $[| upright(C)(e_1, ..., e_n)  |] := lambda k: med [|e_n|] med (lambda v_n: med ... med ([|v_1|] med (lambda v_1: med (fst k) med med upright(C)(v_1, ..., v_n), snd k) ...), snd k)$

- $[| mmono("while") b mmono("do") e |] := & mmono("let") mmono("rec") italic("boucle") k mmono("=")\
  & quad [|b|] med (lambda v: med\
  & quad quad mmono("if") v mmono("then") [|e|] med (lambda \_: med italic("boucle") k, snd k)\
  & quad quad mmono("else") (fst k) med mmono("()")\
  & mmono("in") italic("boucle")$

- $[|mmono("let rec") f mmono(=) e mmono("in") e'|] := lambda k: mmono("let rec") f mmono("=") [|e|] mmono("in") [|e'|] med k$

- $[|mmono("for") i mmono(=) e_1 mmono("to") e_2 mmono("do") e_3 mmono("done")|] := lambda k: med [|e_1|] med &(lambda v_1: med [|e_2|] med (lambda v_2: med \
    &mmono("let rec") italic("boucle") i med k mmono("=")\
    & quad quad mmono("if") i <= v_2 mmono("then") [|e_3|] med (lambda \_ : italic("boucle") med (i+1) med k, snd k) \
    & quad quad mmono("else") (fst k) med mmono("()") \
    & mmono("in") italic("boucle") v_1
  ))$

- $[|mmono("for") i mmono(=) e_1 mmono("downto") e_2 mmono("do") e_3 mmono("done")|] := lambda k: med [|e_1|] med &(lambda v_1: med [|e_2|] med (lambda v_2: med \
    &mmono("let rec") italic("boucle") i med k mmono("=")\
    & quad quad mmono("if") i >= v_1 mmono("then") [|e_3|] med (lambda \_ : italic("boucle") med (i-1) med k, snd k) \
    & quad quad mmono("else") (fst k) med mmono("()") \
    & mmono("in") italic("boucle") v_2
  ))$

- $[|mmono("match") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n |] := &lambda k: med [|e|] med (lambda v:\
  & quad mmono("match") v mmono("with")\
  & quad | p_1 mmono("when") [|e_1'|] med (id, snd k) mmono(->) [|e_1|] med k\
  & quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v\
  & quad | p_n mmono("when") [|e_n'|] med (id, snd k) mmono(->) [|e_n|] med k,\
  & snd k)$

- $[|mmono("try") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n|] := &lambda k: med [|e|] med (fst k, lambda v:\
  & quad mmono("match") v mmono("with")\
  & quad | p_1 mmono("when") [|e_1'|] med (id, snd k) mmono(->) [|e_1|] med k\
  & quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v quad dots.v\
  & quad | p_n mmono("when") [|e_n'|] med (id, snd k) mmono(->) [|e_n|] med k\
  & quad | \_ mmono(->) (snd k) med v\
  & )$

- $[|mmono("raise") e|] := lambda k: med [|e|] med (snd k, snd k)$

On définit 
- $"id" := lambda x: x$
- $"fst" := lambda (x,y): x$
- $"snd" := lambda (x,y): y$
