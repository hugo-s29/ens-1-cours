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

#show raw: set text(font: "Latin Modern Mono")

#set list(marker: ([‣], [–], [•]))

#set page("a5", header : [ Hugo #smallcaps[Salou], Thibaut #smallcaps[Blanc] #h(1fr) #smallcaps[ens l3 profon] ])

#show "…": ([], [.],[.],[.], []).join(h(2pt))
#show "⋯" : ([], [⋅],[⋅],[⋅], []).join(h(2pt))

#show "@" : _ => text(blue, [~] + mmono(strong(sym.arrow)))
#show math.bracket.double.l : set text(purple)
#show math.bracket.double.r : set text(purple)
#show math.lambda : _ => text(blue, mmono(strong("fun")))

#show heading: set align(center)

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

#set par(justify: true)

#show raw.where(block: true): set align(center)

= _Optimisations de la traduction en CPS_

Dans ce document, on décrit les optimisations réalisées dans~fouine, notamment au niveau de la traduction d'un code fouine en code~fouine CPS-ifié.

Dans fouine, nous avons implémenté deux optimisations :
+ précalcul lorsque cela est possible ;
+ optimisation concernant l'application de fonctions.

== I. $quad$ Précalcul.

On définit une relation $~~>$ entre une expression fouine et un résultat précalculé.
C'est une fonction partielle.

Dans le cas de la somme d'entiers, on a :
- $n_1 plus.circle n_2 ~~> n$ où $n = n_1 + n_2$.
On peut faire de même avec les autres opérations arithmétiques simples ($minus.circle$, $times.circle$).
Pour la division d'entiers $div.circle$ (et le modulo), on s'assure que $n_2$ n'est pas toujours nul :
- $n_1 div.circle n_2 ~~> n$ où $n_2 != 0$ et $n = n_1 \/ n_2$.

On fait de même pour les opérations unaires.

Lorsqu'on a une fonction, c'est une valeur et on s'arrête donc de précalculer.
Il faut cependant se rappeler de traduire par continuation la suite de $e$, noté $[|e|]$ :
- $lambda x @ e ~~> lambda x @ [|e|]$.

Lorsqu'on a une variable $x$, un entier, un flottant, une chaîne de caractères, un caractère, un _unit_ `()`, ou un booléen, ces objets se réduisent en eux-mêmes :
- $x ~~> x$.

Lorsqu'on a une application, on ne réduit plus :
- $e_1 med e_2 "" cancel(~~>) "" dots.c$.
En effet, on pourrait engendrer des _effets de bord_ : par exemple, le code `prInt 3` est sous forme de deux expressions précalculées mais pré-effectuer le calcul engendrerait une absence des effets de bords lors de l'exécution.


Si l'on a un type algébrique $upright(C)(e_1, ..., e_n)$, alors on a la forme précalculé en précalculant chacun des éléments :
- $upright(C)(e_1, ..., e_n) ~~> upright(C)(e'_1, ..., e'_n)$ si, pour tout $1 <= i <= n$, $e_i ~~> e'_i$.
Il suffit qu'un des $e_i$ ne soit pas pré-calculable pour que l'on ne puisse pas calculer le type algébrique.

Lorsqu'on a une séquence, on a :
- $e_1 mmono(";") e_2 ~~> e'_2$ si $e_1 ~~> e'_1$ et $e_2 ~~> e'_2$.
Comme c'est une séquence, on s'en fiche du résultat de $e'_1$, on sait juste qu'il n'est pas utile. En passant, s'il ne génère pas d'effets de bords, pourquoi avait-on une séquence alors ? C'est exactement équivalent d'écrire $e_2$.

Lorsqu'on a un `if`, et qu'on précalcule que la condition est `true` ou `false`, alors on élimine le `if` (peu importe si $e_1$ et $e_2$ sont réductibles) et on tente de réduire la branche correspondante.

Dans les autres cas, on ne se réduit pas.


Avant de commencer à traduire, on parcours l'arbre de syntaxe nœud par nœud en commençant par les feuilles et en tentant de précalculer toutes les expressions possibles.
Ceci a pour but de simplifier l'expression finale
```ocaml
1 + 2 * (if 4 > 2 then 4 * 3 * 2 * 1 else 34 mod 17)
```
en 
```ocaml
49
```
directement.

== II. $quad$ Application.

Comme expliqué dans le document `CPS-transformation.pdf`,
on décrit la transformation classique de l'application :
- $[| e_1 med e_2 |] := lambda kk @ med [|e_2|] med (lambda v @ med [|e_1|] med (lambda f @  med f med v med kk))$.
Dans ce document, on ne s'intéresse pas aux variables libres, ni à la 2nde continuation (la continuation _boom_ ne demande que d'ajouter~$snd kk$ à dans les définitions de continuations).

Lorsqu'on peut précalculer (au sens de la section précédente) un terme, $e_1$ ou $e_2$, il n'est pas nécessaire de le traduire, puis de l'évaluer, et d'attendre que la continuation nous rappelle.
Il suffit d'intercaler le résultat précalculé au moment de la traduction.

On a donc la disjonction de cas suivante :

- si $e_1 ~~> e'_1$ et $e_2 ~~> e'_2$ alors\
  #h(1fr) $[| e_1 med e_2 |]_"opt" := lambda kk @ med e'_1 med e'_2 med kk$ ;

- si $e_1 ~~> e'_1$ et $e_2 "" cancel(~~>) "" dots.c$ alors\
  #h(1fr) $[| e_1 med e_2 |]_"opt" := lambda kk @ med [|e_2|]_"opt" med (lambda v @ med e'_1 med v med kk)$ ;

- si $e_1 "" cancel(~~>) "" dots.c$ et $e_2 ~~> e'_2$ alors\
  #h(1fr) $[| e_1 med e_2 |]_"opt" := lambda kk @ med [|e_1|]_"opt" med (lambda f @ med f med e'_2 med kk)$ ;

- si $e_1 "" cancel(~~>) "" dots.c$ et $e_2 "" cancel(~~>) "" dots.c$ alors\
  #h(1fr) $[| e_1 med e_2 |]_"opt" := lambda kk @ med [|e_2|]_"opt" med (lambda v @ med [|e_1|]_"opt" med (lambda f @ med f med v med kk))$.

#v(1fr)

#show raw: set block(fill: gray.darken(70%), inset: 2em, radius: 5pt)
#show raw: set text(white, font: "Noto Sans Symbols 2", 0.8em, stretch: 200%)
#show raw: set par(leading: 0.2em)
```
⣿⡿⠛⠻⣿⣿⣿⣿⣿⠿⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿
⣿⡇⠘⣠⣶⣾⣶⡆⡁⣴⠀⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿
⣿⠇⠘⣿⣿⣿⠿⠿⣦⠘⠠⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿
⣿⠘⠰⣿⣿⣿⣄⣠⣿⣷⠀⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠟⣫⡭⢠⣼
⣯⣄⠀⠠⡿⢃⣛⠷⢏⣡⣷⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡟⣡⣿⡟⣰⣿⣿
⣿⣿⣷⡍⣭⣭⣶⣿⣏⣿⡏⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡟⢰⣿⣿⢡⣿⣿⣿
⣿⣿⣿⣷⢸⣿⣿⣿⣿⣿⢳⣌⠻⣿⠿⠿⠿⠿⠿⢿⣿⣿⣿⣿⣿⢑⢸⣿⣿⢸⣿⣿⣿
⣿⣿⣿⣿⢸⣿⣿⣿⣿⢣⣿⣿⣷⣶⣶⣿⣿⣿⣿⣶⣦⣙⠻⣿⣿⢸⢸⣿⣿⢸⣿⣿⣿
⣿⣿⣿⣿⢸⣿⣿⣿⣏⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣷⡙⢿⡜⣏⣿⣿⡆⢿⣿⣿
⣿⣿⣿⣿⡜⣿⣿⣿⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⣛⣭⣭⣛⣿⡌⢧⢹⣞⣿⣿⡘⣿⣿
⣿⣿⣿⣿⣷⡘⢿⣿⡼⣿⣿⣿⣿⡹⣿⣿⣿⢟⣾⣿⣿⣿⣿⣿⣿⡸⣇⢻⡼⣿⣧⢹⣿
⣿⣿⣿⣿⣿⣿⣆⠻⣷⡹⣿⣿⣿⣷⢻⣿⣿⣼⣿⣿⣿⣿⣿⣿⣿⡇⣿⡜⡇⣿⣿⢸⣿
⣿⣿⣿⣿⣿⣿⣿⡌⣦⣅⢹⣿⣿⡟⢾⣿⣿⢸⣿⣿⣿⣿⣿⣿⣿⠇⣿⢣⣇⣿⣿⢸⣿
⣿⣿⣿⣿⣿⣿⣿⣧⢸⣿⠀⣿⣿⢰⣷⠈⢙⠃⢿⣿⣿⣿⣿⣿⠏⡴⢋⢞⣼⣿⡟⣸⣿
⣿⣿⣿⣿⣿⡿⠛⠡⣾⠏⢁⣿⡇⡞⠁⢰⠶⠒⢂⣙⡿⢿⣿⢵⣤⣤⣶⣿⣿⡟⣰⣿⣿
⣿⣿⣿⣿⣿⣷⣬⣬⣅⠰⠫⠟⣰⣿⣷⣦⢀⠂⠾⠛⢛⣻⣭⣾⣿⣿⡿⠟⣋⣴⣿⣿⣿
⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣶⣦⣭⣭⣭⣥⣶⣾⣿⣿⣿⣿⣿
```
