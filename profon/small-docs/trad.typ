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
#let smallcaps(it) = text(it, font: "Latin Modern Roman Caps")

#set list(marker: ([‣], [–], [•]))

#set page(width: auto, height: auto, header : [ Hugo #smallcaps[Salou], Thibaut #smallcaps[Blanc] #h(1fr) #smallcaps[ens l3 profon] ])

#show "…": ([], [.],[.],[.], []).join(h(2pt))
#show "⋯" : ([], [⋅],[⋅],[⋅], []).join(h(2pt))

#show math.bracket.double.l : set text(purple)
#show math.bracket.double.r : set text(purple)
#show math.lambda : _ => text(blue, mmono(strong("fun")))
#show math.colon : _ => text(blue, [~] + mmono(strong(sym.arrow)))

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

#let kk = text($ k $, blue)

#let inject(x) = $ text(#olive, paren.l.double) #x text(#olive, paren.r.double)^f $

#show heading: set align(center)

= _Traduction d'un programme fouine en fouine CPS_

On notera en #fr[cyan] les variables fraîches.
La continuation $kk$ est une variable fraîche mais qui
reste constante tout au long \ de la transformation.

- $[|n|] := lambda kk: med (fst kk) med n$

- $[|b|] := lambda kk: med (fst kk) med b$

- $[|mmono("()")|] := lambda kk: med (fst kk) med mmono("()")$

- $[|x|] := lambda kk: med (fst kk) med x$

- $[|lambda x: med e|] := lambda kk: med (fst kk) med (lambda x: med [|e|])$

- $[|e_1 med e_2|] := lambda kk: med [|e_2|] med (lambda fr(v): med [|e_1|] med (lambda fr(f): med fr(f) med fr(v) med kk, snd kk), snd kk)$

- $[|e_1 mmono("&&") e_2|] := [| mmono("if") e_1 mmono("then") e_2 mmono("else") mmono("false") |]$

- $[|e_1 mmono("||") e_2|] := [| mmono("if") e_1 mmono("then") mmono("true") mmono("else") e_2 |]$

- $[|e_1 ast.circle e_2|] := lambda kk: med [|e_2|] med (lambda fr(v_2): med [|e_1|] med (lambda fr(v_1): med (fst kk) med (fr(v_1) ast.circle fr(v_2)), snd kk), snd kk)$

- $[|mmono("if") b mmono("then") e_1 mmono("else") e_2|] := lambda kk: med [|b|] med (lambda fr(v): med mmono("if") fr(v) mmono("then") [|e_1|] med kk mmono("else") [|e_2|] med kk, snd kk)$

- $[|ast.circle e|] := lambda kk: med [|e|] med (lambda fr(v): med (fst kk) med (ast.circle fr(v)), snd kk)$

- $[| e_1 mmono(";") e_2 |] := lambda kk: med [|e_1|] med (lambda \_: med [|e_2|] med kk, snd kk)$

- $[| upright(C)(e_1, ..., e_n)  |] := lambda kk: med [|e_n|] med (lambda fr(v_n): med ... med ([|e_1|] med (lambda fr(v_1): med (fst kk) med med upright(C)(fr(v_1), ..., fr(v_n)), snd kk) ...), snd kk)$

- $[| mmono("while") b mmono("do") e |] := & mmono("let") mmono("rec") fr(italic("boucle")) kk mmono("=")\
  & quad [|b|] med (lambda fr(v): med\
  & quad quad mmono("if") fr(v) mmono("then") [|e|] med (lambda \_: med fr(italic("boucle")) kk, snd kk)\
  & quad quad mmono("else") (fst kk) med mmono("()")\
  & mmono("in") fr(italic("boucle"))$

- $[|mmono("for") i mmono(=) e_1 mmono("to") e_2 mmono("do") e_3 mmono("done")|] := lambda kk: med [|e_1|] med &(lambda fr(v_1): med [|e_2|] med (lambda fr(v_2): med \
    &mmono("let rec") fr(italic("boucle")) i med kk mmono("=")\
    & quad quad mmono("if") i <= fr(v_2) mmono("then") [|e_3|] med (lambda \_ : fr(italic("boucle")) med (i+1) med kk, snd kk) \
    & quad quad mmono("else") (fst kk) med mmono("()") \
    & mmono("in") fr(italic("boucle")) fr(v_1) 
  ))$

- $[|mmono("for") i mmono(=) e_1 mmono("downto") e_2 mmono("do") e_3 mmono("done")|] := lambda kk: med [|e_1|] med &(lambda v_1: med [|e_2|] med (lambda v_2: med \
    &mmono("let rec") fr(italic("boucle")) i med kk mmono("=")\
    & quad quad mmono("if") i >= fr(v_2) mmono("then") [|e_3|] med (lambda \_ : fr(italic("boucle")) med (i-1) med kk, snd kk) \
    & quad quad mmono("else") (fst kk) med mmono("()") \
    & mmono("in") fr(italic("boucle")) fr(v_1)
  ))$

- $[|mmono("match") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n |] := &lambda kk: med [|e|] med
( dots.c (lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_1 mmono(->) [|e'_1|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_1|] med kk\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd kk)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &)\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_2 mmono(->) [|e'_2|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_2|] med kk\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd kk)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &quad )\
  & quad quad quad quad quad dots.v\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_n mmono(->) [|e'_n|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_n|] med kk\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd kk)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &)\
  &(lambda \_: (snd kk) bold("MatchError"))) dots.c )
  $

- $[|mmono("try") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n|] := &lambda kk: med [|e|] med (fst kk, lambda v:\
  &( dots.c (lambda fr(italic("match")_"next"): med lambda v:\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_1 mmono(->) [|e'_1|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_1|] med kk\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd kk)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &)\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_2 mmono(->) [|e'_2|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_2|] med kk\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd kk)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &)\
  & quad quad quad quad quad dots.v\
  &(lambda fr(italic("match")_"next"): med lambda fr(v):\
  &quad mmono("match") fr(v) mmono("with")\
  &quad | p_n mmono(->) [|e'_n|] med (lambda fr(v'): med \
  &quad quad quad mmono("if") fr(v') mmono("then") [|e_n|] med kk\
  &quad quad quad mmono("else") fr(italic("match")_"next") med fr(v),\
  &quad quad snd kk)\
  &quad | \_ mmono(->) fr(italic("match")_"next") med fr(v), \
  &)\
  &(snd kk) med ) dots.c )$

- $[|mmono("raise")|] := lambda e: lambda kk: (snd kk) med e$

- $[|mmono("let rec") f mmono(=) e mmono("in") e'|] := lambda kk: [|inject(e_1) |] med (lambda fr(u): mmono("let rec") f med fr(x) mmono("=") fr(u) med (f, fr(x)) mmono("in") [|e_2|] med kk, snd kk) $

On définit 
- $"fst" := lambda (x,y): x$
- $"snd" := lambda (x,y): y$
et où $inject(e)$ est une fonction partielle définie par induction (_il y a 17 cas_)
- $inject(n)$ n'est pas défini
- $inject(x)$ n'est pas défini
- $inject(b)$ n'est pas défini
- $inject(mmono("()"))$ n'est pas défini
- $inject(e_1 med e_2)$ n'est pas défini
- $inject(e_1 ast.circle e_2)$ n'est pas défini
- $inject(ast.circle e)$ n'est pas défini
- $inject(mmono("for") i mmono("=") e_1 mmono("to") e_2 mmono("do") e_3 mmono("done"))$ n'est pas défini
- $inject(mmono("for") i mmono("=") e_1 mmono("downto") e_2 mmono("do") e_3 mmono("done"))$ n'est pas défini
- $inject(mmono("while") b mmono("do") e mmono("done"))$ n'est pas défini
- $inject(upright(C)(e_1, ..., e_n))$ n'est pas défini
- $inject(e_1 mmono(";") e_2) := e_1 mmono(";") inject(e_2)$
- $inject(mmono("if") e mmono("then") e_1 mmono("else") e_2) := mmono("if") e mmono("then") inject(e_1) mmono("else") inject(e_2)$
- $inject(mmono("match") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n) := mmono("match") e mmono("with") p_1 mmono("when") e'_1 mmono(->) inject(e_1) | dots.c | p_n mmono("when") e'_n mmono(->) inject(e_n)$
- $inject(mmono("try") e mmono("with") p_1 mmono("when") e'_1 mmono(->) e_1 | dots.c | p_n mmono("when") e'_n mmono(->) e_n) := mmono("try") inject(e) mmono("with") p_1 mmono("when") e'_1 mmono(->) inject(e_1) | dots.c | p_n mmono("when") e'_n mmono(->) inject(e_n)$
- $inject(mmono("let rec") f mmono("=") e mmono("in") e') := mmono("let rec") f mmono("=") e mmono("in") inject(e')$
- $inject(lambda x: e) := lambda (f, x) : e$
L'unique cas de base dans la définition de $inject(e)$ est une fonction.

