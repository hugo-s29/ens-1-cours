#import "../global.typ": *

#show heading.where(level: 1): it => context [
  #pagebreak()
  #set text(font: "Latin Modern Sans")
  #h(-1em)
  #counter(heading).display()
  #h(0.2em)
  #box(width: 2.4pt, height: 1.1em, fill: main-color.get(), baseline: 20%, radius: 50%)
  #h(0.2em)
  #it.body
]

#show heading.where(level: 2): it => context [
  #set text(font: "Latin Modern Sans", 0.8em)
  #it.body
  #counter(heading).display()
]

#show outline.entry.where(level: 2): it => link(
  it.element.location(),
  it.indented(it.prefix(),
    box(
      stack(
        dir: ltr,
        [Question~],
        it.prefix(),
        h(1fr),
        it.page()
      )
    )
  )
)


#title[ Révisions de Logique ]

Ce document contient des réponses pour les questions de cours pour le partiel/examen de Logique.
Je m'excuse pour le format douteux du document.

#outline()


#let questions = counter("questions")
#questions.step()

#let question(body) = context block(
  definition-style(
    [== Question],
    body
  ),
  breakable: false,
  above: 5em
)

= Cours I.

#question[
  Énoncer et prouver le lemme de lecture unique.
]

/ Énoncé.:
  Toute formule $F in cal(F)$ vérifie une et une seule de ces propriétés :
  + $F in cal(P)$ ;
  + il existe $G$ telle que $F = not G$ ;
  + il existe $G,H$ telles que $F = (G and H)$ ;
  + il existe $G,H$ telles que $F = (G or H)$ ;
  + il existe $G,H$ telles que $F = (G -> H)$ ;
  + il existe $G,H$ telles que $F = (G <-> H)$.

/ Preuve.:
  On commence par montrer que les formules de $cal(F)$ sont bien parenthésées.
  Ensuite, pour un mot $F in cal(F)$, on est dans un des cas suivants (uniquement un cas) :
  - soit $|F| = 0$ absurde car $epsilon in.not cal(F)$
  - soit $|F| = 1$ alors nécessairement $F in cal(P)$, cas (1)
  - soit $|F| >= 2$ et $F$ commence par $not$, alors soit $G$ le mot $F$ sans sa première lettre, par construction $G in cal(F)$ et donc on est dans le cas (2)
  - soit $|F| >= 2$ et $F$ commence par $($ et termine par $)$ alors, on retire ces deux lettres et on décompose ce mot en deux composantes bien parenthésées $F$ et $G$ séparées nécessairement par une lettre $and, or, ->, <->$.

#question[
  Montrer qu'il y a une bijection entre les formules du calcul propositionnel et les arbres tels que :
  - les feuilles sont étiquetées par des variables ;
  - les nœuds internes sont étiquetés par des connecteurs ;
  - ceux étiquetés par $not$ ont un fils, les autres $2$.
]

On construit la fonction par récurrence (forte) sur la taille de la formule considérée :
- on applique le lemme de lecture unique ;
- on applique l'hypothèse de récurrence aux 0/1/2 sous-formules ;
- on construit l'arbre actuel.


#question[
  Montrer que toute fonction $nu : cal(P) -> {0,1}$ peut s'étendre de manière unique en une fonction $mu : cal(F) -> {0,1}$ telle que :
  - pour tout $p in cal(P)$, $nu(p) = mu(p)$ ;
  - si $F, G in cal(F)$ alors 
    - $mu(not F) = 1 - mu(F)$,
    - $mu(F or G) = 1$ ssi $mu(F) = 1$ ou $mu(G) = 1$,
    - $mu(F and G) = 1$ ssi $mu(F) = 1$ et $mu(G) = 1$,
    - $mu(F -> G) = 1$ ssi $mu(F) = 0$ et $mu(G) = 1$,
    - $mu(F <-> G) = 1$ ssi $mu(F) = mu(G)$.
]

Soit $nu : cal(P) -> {0,1}$ fixée.
On montre l'existence et l'unicité de la définition de $mu(F)$ par induction sur l'arbre de $F$.
Ceci est possible par la bijection arbres étiquetés et formules.

- Pour une variable $p in cal(P)$, on a nécessairement $mu(p) := nu(p)$.
- Pour un nœud de label $not$, on a nécessairement $mu(not F) := 1- mu(F)$.
- Pour un nœud de label $and$, on a nécessairement $mu(F and G) := 1$ si on a $mu(F) = mu(G) = 1$ et on pose $mu(F and G) := 0$ sinon.
- De même pour les autres cas.

#question[
  Énoncer le théorème de compacité du calcul propositionnel.
]

Un ensemble de formules est satisfiable ssi toute sous-partie finie de cet ensemble est satisfiable.

#question[
  Prouver le théorème de compacité du calcul propositionnel dans le cas où l’ensemble des variables est au plus dénombrable.
]

Soit $cal(E)$ un ensemble de formules du calcul propositionnel.
Montrons que $cal(E)$ est satisfiable ssi toute partie finie de $E$ est satisfiable.


/ "$==>$".: Si $cal(E)$ est satisfiable, alors soit une certaine valuation satisfaisant $cal(E)$. Cette valuation satisfait toute partie finie de $cal(E)$.
/ "$<==$".:
  Soit $cal(P) = { x_1, x_2, ... }$. On procède en deux étapes.

  / Étape 1.:
    Par récurrence, on construit $(epsilon_n) ""_(n in NN^*)$ qui satisfait : pour toute partie finie $F$ de $cal(E)$, il existe une valuation $nu$ satisfaisant $F$ et qui vérifie $forall i <= n, nu(x_i) = epsilon_i$.
    - Au rang $n = 0$, on a directement que toute partie finie est satisfiable (sans contraintes).
    - Au rang $n$, on a deux cas :
      + soit, pour toute partie finie $F$ de $cal(E)$, il existe $nu$ satisfaisant $nu(x_i) = epsilon_i$ pour tout $i <= n$ et $nu(x_(n+1)) = 0$, alors on pose $epsilon_(n+1) := 0$.
      + soit, il existe une partie finie $F$ de $cal(E)$ telle que toute valuation $nu$ satisfaisant $F$ avec $nu(x_i) = epsilon_i$ pour tout~$i <= n$, et $nu(x_(n+1)) = 1$.
        On pose alors $epsilon_(n+1) := 1$.

        Soit $F'$ une partie finie de $cal(E)$.
        Par hypothèse de récurrence, il existe une valuation $nu$ satisfaisant le sous-ensemble fini $F' union F$  et telle que $nu(x_i) = epsilon_i$ pour tout~$i <= n$.
        D'où, $nu$ satisfait $F$ et donc, $nu(x_(n+1)) = 1 = epsilon_(n+1)$ par l'hypothèse de la disjonction de cas.
        Donc, $nu$ satisfait $F$ et donc on a la propriété au rang~$n+1$.

  / Étape 2.: On pose $mu(x_i) := epsilon_i$. Montrons que $mu$ satisfait $cal(E)$.
    Pour tout $F in cal(E)$, on a $mu(F) = 1$ car :
    - on pose $k$ tel que $"vars"(F) subset.eq { x_1, ..., x_k }$ ;
    - l'ensemble ${F}$ est fini, donc par la propriété au rang~$k$, il existe $nu$ coïncidant avec $mu$ sur les $k$ premières variables, donc sur les variables de $F$, et donc $mu(F) = nu(F) = 1$.

= Cours II.


#question[
  Énoncer et prouver un lemme de lecture unique pour les termes de la logique du premier ordre dans un langage donné $cal(L)$.
]

/ Énoncé.:
  Tout terme $t in cal(T)$ vérifie une et une seule des propriétés ci-dessous :
  - $t in cal(V)$ ;
  - il existe un symbole de constante $c in cal(L)$ tel que $t = c$ ;
  - il existe un symbole de fonction $n$-aire $f in cal(L)$ et $n$ termes~$t_1, ..., t_n$ tels que $t = f(t_1, ..., t_n)$

/ Preuve.:
  On commence par montrer que tout terme est bien parenthésé.
  Ensuite, soit $t in cal(T)$. On a un des trois cas suivants :
  - soit $|t| = 1$ et $t in cal(V)$, c'est une variable
  - soit $|t| = 1$ et $t in cal(L)$, c'est un symbole de constante
  - soit $|t| >= 2$ et alors on a la première lettre de $t$ qui est un symbole de fonction $n$-aire, on retire les deux premières lettres et la dernière et on décompose selon les virgules de "dernier niveau" (par rapport au parenthésage). Il y a nécessairement $n$ termes, et chacun représente un terme.

#question[
  Énoncer et prouver un lemme de bijection entre certains arbres étiquetés et les termes de la logique du premier ordre dans un langage donné $cal(L)$.
]

On construit la fonction par récurrence (forte) sur la taille du terme considéré :
- on applique le lemme de lecture unique ;
- on applique l'hypothèse de récurrence aux sous-formules ;
- on construit l'arbre actuel.

#question[
  Énoncer et prouver un lemme de lecture unique pour les formules de la logique du premier ordre dans un langage donné $cal(L)$.
]

/ Énoncé.:
  Toute formule $F in cal(F)$ vérifie une et une seule des propriétés ci-dessous :
  - il existe un symbole de relation $n$-aire $R in cal(L)$  et $n$ termes $t_1, ..., t_n$ tels que $F = R(t_1, ..., t_n)$ ;
  - il existe $G$ telle que $F = not G$
  - il existe $G$ et $x in cal(V)$ telles que $F = forall x med G$
  - il existe $G$ et $x in cal(V)$ telles que $F = exists x med G$
  - il existe $G, H$ telles que $F = (G or H)$
  - il existe $G, H$ telles que $F = (G and H)$
  - il existe $G, H$ telles que $F = (G -> H)$

/ Preuve.:
  On commence par montrer que toute formule est bien parenthésée.
  Ensuite, soit $F in cal(F)$. On a un des trois cas suivants :
  - soit $F$ commence par un symbole de relation, on peut lire de manière unique les termes entre les virgules du "dernier niveau" (par rapport au parenthésage)
  - soit $F$ commence par un $forall$ ou $exists$, la lettre suivante est $x in cal(V)$ et la suite est une formule
  - soit $F$ commence par une parenthèse ouvrante (et termine nécessairement par une parenthèse fermante) et alors on peut décomposer ce qu'il y a entre les parenthèses en deux formules séparées par $and, or$ ou $->$.


#question[
  Donner une preuve de 
  $ tack not A <-> (A -> bot) $
]

#let rule = curryst.rule
#let prooftree = curryst.prooftree
#let su(it) = math.sans(math.upright(it))

#align(center,
  prooftree(
    rule(
      name: $and_su(i)$,
      $ tack not A <-> (A -> bot) $,
      rule(
        name: $->""_su(i)$,
        $ tack not A -> (A -> bot) $,
        rule(
          name: $->""_su(i)$,
          $ not A tack A -> bot $,
          rule(
            name: $not_su(e)$,
            $ not A, A tack  bot $,
            rule(name: $su("ax")$, $not A, A tack not A$),
            rule(name: $su("ax")$, $not A, A tack A$)
          )
        )
      ),
      rule(
        name: $->""_su(i)$,
        $ tack (A -> bot) -> not A $,
        rule(
          name: $not_su(i)$,
          $ A -> bot tack not A $,
          rule(
            name: $->""_su(e)$,
            $ A -> bot, A tack  bot $,
            rule(name: $su("ax")$, $A -> bot, A tack A-> bot$),
            rule(name: $su("ax")$, $A -> bot, A tack A$)
          )
        )
      )
    )
  )
)

= Cours III.

#let Val = $cal(V)#h(-2.5pt)a ell$


#question[
  Montrer que, pour toute interprétation $cal(M)$ sur le langage $cal(L)$, tout environnement $e$ et toute formule $F$, $Val_cal(M) (F, e)$ ne dépend que de la valeur de $e$ sur les variables libres de $F$.
]

On commence par montrer le résultat similaire sur les termes (qui se prouve de la même manière).

Par induction sur $F$, on montre le résultat.
- Si $F = R(t_1, ..., t_n)$ alors $Val_cal(M) (F, e)$ ne dépend que de $(Val_cal(M) (t_i, e))_(i in [|1, n|])$ qui ne dépendent que des valeurs de $e$ sur les variables libres des $t_i$, et donc $Val_cal(M) (F, e)$ ne dépend que des valeurs de $e$ sur les variables libres de $F$.
- Si $F = G or H$ alors on applique le résultat à $G$ et $H$ et comme $Val_cal(M) (G, e)$ (_resp._ $Val_cal(M) (H, e)$) ne dépend que des valeurs de $e$ sur variables libres de $G$ (_resp._ $H$) alors la valeur de $F$ ne dépend que des valeurs de $e$ sur les variables libres de $F$.
- Si $F = forall x med G$ alors on applique le résultat à $G$ et comme $Val_cal(M) (G, e[x := a])$ ne dépend que des valeurs de $e[x:= a]$ sur variables libres de $G$ alors la valeur de $F$ ne dépend que des valeurs de $e$ sur les variables libres de $F$.
- Les autres cas sont similaires.

#question[
  Montrer que pour toute interprétation $cal(M)$ sur le langage $cal(L)$, tout environnement $e$ et toute formule close $F$, $Val_cal(M) (F, e)$ ne dépend pas de $e$.
]

La valeur $Val_cal(M) (F, e)$ ne dépend que des valeurs de $e$ sur les variables libres de $F$. La formule $F$ est close donc n'a pas de variables libres.
D'où, la valeur de $F$ ne dépend pas de $e$.

#question[
  Montrer la proposition suivante. Soient $cal(L)$ et $cal(L)'$ deux langages, $cal(M)$ (_resp._ $cal(M)'$) une interprétation de $cal(L)$ (resp $cal(L)'$) et $cal(M)'$ un enrichissement de $cal(M)$, $e$ un environnement, alors :
  +  si $t$ est un terme de $cal(L)$, $Val_cal(M) (t, e) = Val_(cal(M)') (t, e)$ ;
  +  si $F$ est une formule de $cal(L)$, alors $(cal(M), e)$ satisfait $F$ ssi $(cal(M)', e)$ satisfait $F$.
]

+ Par induction sur $t$, on montre le résultat demandé : l'interprétation des symboles dans $cal(M)$ et dans $cal(M)'$ est la même.
+ Par induction sur $F$, on montre le résultat demandé : l'interprétation des symboles dans $cal(M)$ et dans $cal(M)'$ est la même.

#question[
  On dit que deux formules $F$ et $G$ du premier ordre sont équivalentes si $F <-> G$ est un théorème, c’est à dire si $tack F <-> G$.
  Montrer que toute formule est équivalente à une formule n’utilisant que les connecteurs logiques $not$, $or$ et $exists$.
]

Idée de la preuve :
- on montre que $tack (F -> G) <-> (not F or G)$
- on montre que $tack (F and G) <-> not (not F or not G)$
- on montre que $tack (forall x med F) <-> not (exists x med not F)$ :

#align(center,
  prooftree(
    rule(name: $->""_su(i)$,
      $tack (forall x med F) -> not (exists x med not F) $,
      rule(name: $not_su(i)$,
        $forall x med F tack not (exists x med not F) $,
        rule(name: $exists_su(e)$,
          $forall x med F, exists x med not F tack bot$,
          rule(name: $su("ax")$, $forall x med F, exists x med not F tack exists y med not F[y]$),
          rule(name: $not_su(e)$, 
            $forall x med F, exists x med not F, not F[y] tack bot$,
            rule(name: $forall_su(e)$, 
              $forall x med F, exists x med not F, not F[y] tack F[y]$,
              rule(name: $su("ax")$, $forall x med F, exists x med not F, not F[y] tack forall x med F$),
            )
          )
        )
      )
    )
  ) +
  prooftree(
    rule(name: $->""_su(i)$,
      $tack not (exists x med not F) -> forall x med F $,
      rule(name: $forall_su(i)$,
        $not (exists x med not F) tack forall x med F $,
        rule(name: $bot_su(c)$,
          $not (exists x med not F) tack F $,
          rule(name: $not_su(e)$,
            $not (exists x med not F), not F tack bot$,
            rule(name: $su("ax")$, $not (exists x med not F), not F tack not (exists x med not F)$),
            rule(name: $exists_su(i)$,
              $not (exists x med not F), not F tack exists x med not F$,
              rule(name: $su("ax")$, $not (exists x med not F), not F tack not F$),
            )
          )
        )
      )
    )
  )
)

- on applique ces réécritures récursivement.

#question[
  Montrer que si $cal(M)$ et $cal(N)$ sont deux interprétations de $cal(L)$ et $phi$ un morphisme de $cal(M)$ dans $cal(N)$, alors pour tout terme $t$ et tout environnement $e$ dans $cal(M)$ on a 
  $ phi(Val_cal(M) (t,e)) = Val_cal(N) (t, phi(e)). $
]

Par induction sur $t$ : 
- si $t$ est symbole de constante, alors sa valeur est $phi(c_cal(M))$ d'une part et $c_cal(N)$ de l'autre ;
- si $t$ est variable, alors sa valeur est celle $phi(e(x))$ d'une part et $phi compose e (x)$ de l'autre ;
- si $t$ est l'application d'un une fonction $n$-aire $f(t_1, ..., t_n)$ alors on applique l'hypothèse d'induction sur tous les sous-termes et on conclut.

#question[
  Montrer que si $cal(M)$ et $cal(N)$ sont deux interprétations de $cal(L)$ et $phi$ un morphisme _injectif_ de $cal(M)$ dans $cal(N)$, alors pour toue formule atomique $F$ et tout environnement $e$ dans $cal(M)$ on a 
  $ cal(M), e tack.double F quad #text[ssi] quad cal(N), phi(e) tack.double F. $
]

D'une part, si $cal(M), e tack.double R(t_1, ..., t_n)$ alors $R_cal(M)(v_1, ..., v_n)$ où l'on note~$v_i := Val_cal(M) (t_i, e)$.
D'où, par morphisme et le point précédent, on a que $R_cal(N)(phi(v_1), ..., phi(v_n))$ et donc que $cal(N), phi(e) tack.double R(t_1, ..., t_n)$.

D'autre part part, si $cal(N), phi(e) tack.double R(t_1, ..., t_n)$ alors $R_cal(N)(v'_1, ..., v'_n)$ où l'on note~$v'_i := Val_cal(N) (t_i, phi(e))$.
D'où, par morphisme injectif et le point précédent, on a que $R_cal(N)(phi(v_1), ..., phi(v_n))$ pour certains $(v_i)""_(i in [| 1,n |])$ et donc que $cal(M), e tack.double R(t_1, ..., t_n)$.

#question[
  Montrer que si $cal(M)$ et $cal(N)$ sont deux interprétations de $cal(L)$ et $phi$ un isomorphisme de $cal(M)$ dans $cal(N)$, alors pour toue formule $F$ et tout environnement $e$ dans $cal(M)$ on a 
  $ cal(M), e tack.double F quad #text[ssi] quad cal(N), phi(e) tack.double F. $
]

Par induction sur $F$.
- Pour les formules closes, c'est vrai par le point précédent.
- Pour le $and$, le $or$ et le $->$, on applique directement l'hypothèse d'induction à chaque point.
- Pour le $forall$ et $exists$, on a directement le résultat car $phi(|cal(M)|) = |cal(N)|$, donc le "pour tout" et le "il existe" dans la définition de la valeur se fait sur le même ensemble.

#question[
  Montrer que deux interprétations isomorphes satisfont les mêmes formules closes.
]

D'une part, on sait que l'interprétation d'une formule close ne dépend pas de l'environnement considéré.
D'autre part, on considère le point précédent et on a $cal(M) tack.double F$ ssi $cal(N) tack.double F$.

= Cours IV.

#question[
  Énoncer les deux versions vues en cours du théorème de complétude (au sens de règle-complétude) de Gödel de la logique du premier ordre. Indiquer quel est le sens "correction" et quel est le sens "complétude".
]

/ Version 1.: Soit $T$ une théorie et $F$ une formule close. On a $T tack F$ ssi $T tack.double F$.
/ Version 2.: Une théorie $T$ est consistante ssi elle est non-contradictoire.

Sens correction : "$==>$". Sens complétude : "$<==$".

#question[
  Montrer que les deux versions sont équivalentes (montrer chaque version en utilisant l'autre).
]

*Pour la partie correction.*

D'une part, on montre non V2 implique non V1 (par contraposée).
Soit $T$ non-contradictoire et inconsistante. Il existe donc un modèle $cal(M)$ tel que $cal(M) tack.double T$ et $T tack bot$.
Or, par définition $cal(M) tack.double.not bot$ et donc $T tack.double.not bot$.

D'autre part, on montre V2 implique V1. Soit $T$ et $F$ tels que $T tack F$. Ainsi, $T union { not F } tack bot$ et donc $T union {not F}$ est consistante d'où (par hypothèse V2) $T union { not F }$ contradictoire, donc on n'a pas de modèle. On a alors que tous les modèles de $T$ sont des modèles de $F$, autrement dit $T tack.double F$.

*Pour la partie complétude.*

D'une part, soit $T$ contradictoire. Elle n'a pas de modèle. Ainsi $T tack.double bot$ et donc $T tack bot$ par V1, d'où l'inconsistance de $T$.

D'autre part, soit $T tack.double F$. La théorie $T union { not F }$ n'a pas de modèle, elle est donc contradictoire, donc inconsistante, donc $T union {not F} tack bot$ d'où $T tack F$ par $bot_su("c")$.


#question[
  Énoncer le théorème de compacité (sémantique) de la logique du premier ordre
]

Une théorie est contradictoire ssi elle est finiment contradictoire, c'est-à-dire qu'il existe un sous-ensemble fini contradictoire.

#question[
  Admettre le théorème de complétude et montrer le théorème de compacité de la logique du premier ordre (on énoncera les deux théorèmes en question).
]

*Théorème de compacité sémantique.* 
Une théorie est contradictoire ssi elle est finiment contradictoire, c'est-à-dire qu'il existe un sous-ensemble fini contradictoire.

*Théorème de complétude.* Une théorie est consistante ssi elle est non-contradictoire.

On se munit aussi du théorème suivant.

*Théorème de compacité syntaxique.* 
Une théorie est inconsistante ssi elle est finiment inconsistante.

Il est évident car toute preuve de $bot$ est nécessairement finie, donc n'utilise qu'un sous-ensemble fini de la théorie.

Soit $T$ contradictoire. Alors, $T$ est inconsistante (complétude).
Alors $T$ est finiment inconsistante (compacité syntaxique).
Donc $T$ est finiment contradictoire (complétude encore).

= Cours V.

#question[
  Donner la définition de théorie complète (au sens d'axiome-complète) en logique du premier ordre.
]

Une théorie $T$ est _axiome-complète_ si $T tack.not bot$ et pour tout formule $F$ on a $T tack F$ ou $T tack not F$.

#question[
  Montrer sans utiliser le théorème de complétude (au sens de règle-complétude) :
  Si $T$ est une théorie consistante (qui ne prouve pas l’absurde) dans un langage au plus dénombrable $cal(L)$, alors il existe une théorie $T'$ contenant $T$ et complète.

  Y a t-il une preuve plus simple en utilisant le théorème de complétude ?
]

Soit $T'_0 := T$.
Au rang $i$,
- soit $T'_i$ est complète et alors $T'_(i+1) := T'_i$.
- soit $T'_i$ n'est pas complète, alors il existe une formule $F$ ("la plus petite possible" obtenue à l'aide d'une énumération) telle que $T'_i tack.not F$ et $T'_i tack.not not F$, et on pose $T'_(i+1) := T'_i union { F }$.

La théorie $T' := union.big_(i in NN) T'_i$ est complète.

Avec le théorème de complétude, on construit directement la théorie $T'$ dans la construction du modèle $"Th"$ de $T$.

= Cours VI.

#question[
  Montrer que $cal(P) tack forall x  med forall y med x + y = y + x$.
]

On procède à l'aide du schéma inductif sur $x$ : $F(x) := forall y med x + y = y + x$.
- Avec le schéma inductif sur $x$, on montre $cal(P) tack forall x med 0 + x = x$ : le cas $0 + 0 = 0$ se traite par A4 et le cas $0 + x = x -> 0 + (bold(S) med x) = bold(S) med x$ avec A5.
- Avec le schéma inductif sur $y$, on montre $cal(P) tack forall x med forall y med bold(S)(x + y) = (bold(S) med x) + y$.


#question[
  Montrer que $cal(P) tack forall x  med forall y med x times y = y times x$.
]

Par double schéma inductif, comme la question précédente.

= Cours VII.


#question[
  Énoncer le théorème de représentation.
]

Toute fonction récursive totale est représentable.
Autrement dit : l'ensemble des fonctions représentables contient les projections, la fonction successeur, les fonctions constantes, et cet ensemble est stable par composition, récursion primitive et minimisation.


#question[
Étant données des formules $F_1, ..., F_p, G$ qui représentent des fonctions totales $f_1(x_1, ..., x_n)$, ..., $f_p (x_1, ..., x_n)$, $g(x_1, ..., x_p)$ donner une formule qui représente la fonction composée $g(f_1, ..., f_p)$.
]

Soient $F_i (x_0, x_1, ..., x_n)$ représentant $f_i$ pour tout $i$ et soit la formule $G(x_0, ..., x_p)$ représentant $g$.
On pose $ H(x_0, ..., x_n) := exists y_0 med dots.c med exists y_p med G(x_0, y_1, ..., y_p) and and.big_(1 <= i <= p) F_i (y_i, x_1, ..., x_n). $


= Cours VIII.

On pose :
- $alpha_2(n,m) := (n + m) (n+m+1) \/ 2 + n$
- $alpha_3(x,y,z) := alpha_2(x, alpha_2(y, z))$ 
- $sharp 0 := alpha_3(0, 0, 0)$
- $sharp x_n := alpha_3(n+1, 0, 0)$
- $sharp (bold(S) med t_1) := alpha_3(sharp t_1, 0, 1)$
- $sharp (t_1 + t_2) := alpha_3(sharp t_1, sharp t_2, 2)$
- $sharp (t_1 times t_2) := alpha_3(sharp t_1, sharp t_2, 3)$.

#question[
  Montrer que l’ensemble des numéros de termes est un ensemble primitif récursif.
]

Il suffit de montrer que l'on peut décider si un entier $x$ est un numéro de terme à l'aide de fonctions primitives récursives.
On notera $T(x)$ la fonction indicatrice de ${ sharp t | t #text[est un terme de] cal(L)_0}$.
Pour cela, on utilise un lemme de définition par cas et récursion.
- Si $beta_3^3(x) = 0$ et $beta_3^2(x) = 0$ alors $T(x) := 1$ (c'est soit zéro, soit une variable).
- Si $beta_3^3(x) = 1$ et $beta_3^2(x) = 0$ alors $T(x) := T(beta_3^1(x))$ (c'est un successeur).
- Si $beta_3^3(x) = 2$ ou $3$ alors $T(x) := T(beta_3^1(x)) times T(beta_3^2(x))$ (c'est un $times$ ou $+$).
- Sinon, $T(x) := 0$.

#question[
  Montrer que l’ensemble des couples $(sharp t,n)$ où $t$ est un terme et $x_n$ n’a pas d’occurrence dans $t$ est récursif primitif.
]

On définit la fonction caractéristique de cet ensemble, noté $g_0(x, y)$.
On utilise pour cela la définition par cas et récursion.

- Si $beta_3^3(x) = beta_3^2(x) = 0$ et $beta_3^1(x) - 1 != y$ alors $g_0(x, y) := 1$.
- Si $beta_3^3(x) = 1$ et $beta_3^2(x) = 0$ alors $g_0(x,y) := g_0(beta_3^2(x), y)$.
- Si $beta_3^3(x) = 2$ ou 3 alors $g_0(x,y) := g_0(beta_3^1(x), y) times g_0(beta_3^2(x), y)$.
- Sinon, $g_0(x,y) := 0$.

= Cours IX.

#question[
  Montrer qu'une théorie $T$ cohérente qui contient $cal(P)_0$ est indécidable.
]

Par l'absurde, on procède par diagonalisation.
Considérons l'ensemble $ theta := { (m,n) | m = sharp F(n) " et " T tack F(underline(n)) }. $
Comme $T$ décidable alors $theta$ aussi. On pose l'ensemble récursif 
$ B := { n in NN | (n, n) in.not theta }. $

D'après le théorème de représentation, il existe une formule $G(x)$ représentant $B$ :
- si $n in B$ alors $cal(P)_0 tack G(underline(n))$ et donc $T tack G(underline(n))$ ;
- si $n in.not B$ alors $cal(P)_0 tack not G(underline(n))$ et donc $T tack not G(underline(n))$.

Soit $a = sharp G(x)$. A-t-on $a in B$ ?

- D'une part, si $a in B$ alors $(a,a) in.not theta$ et donc $T tack.not G(underline(a))$.
  Mais si $a in B$ alors, par définition de $G$, on a $T tack G(underline(a))$. *_Absurde !_*
- D'autre part, si $a in.not B$ alors $(a,a) in theta$ et donc $T tack G(underline(a))$.
  Mais si $a in.not B$ alors, par définition de $G$, on a $T tack not G(underline(a))$, d'où $T$ est non consistante. *_Absurde !_*

On en conclut que $T$ est indécidable.

#question[
  Quel que soit un langage $cal(L)$ contenant au moins deux constantes, un symbole de fonction unaire et deux symboles de fonctions binaires, l'ensemble des théorèmes logiques $T$ sur $cal(L)$ n'est pas récursif.
]

Quitte à renommer les symboles, considérons $cal(L) supset.eq cal(L)_0$.
Soit $G$ la conjonction des axiomes de Peano $cal(P)_0$.
Pour toute formule $F$, on a $cal(P)_0 tack F$ ssi $T_0 tack (G -> F)$ où $T_0 subset.eq T$ est l'ensemble des théorèmes logiques sur $cal(L)_0$.
Si $T_0$ est récursif alors $cal(P)_0$ est décidable. Et, si $T$ est récursif alors $T_0$ l'est aussi.
D'où on aurait que $cal(P)_0$ décidable, _*absurde*_ (par question précédente).

#question[
  Énoncer et montrer le 1er théorème d'incomplétude de Gödel. En déduire que $cal(P)$ n'est pas complète.
]

/ Énoncé.:
  Soit $T$ une théorie consistante contenant $cal(P)_0$ et avec un ensemble d'axiomes récursifs.
  Alors $T$ n'est pas complète.

/ Preuve.:
  Une théorie avec un ensemble d'axiomes récursif et qui est complète, est décidable.
  Et c'est faux pour $T$ par le théorème précédent.

  En effet,  pour $F$ donné, il suffit d'énumérer les preuves jusqu'à avoir $T tack F$ ou $T tack not F$.

/ Corollaire.:
  La théorie $cal(P)$ est consistante, contient $cal(P)_0$ et a un ensemble d'axiomes récursif, elle n'est donc pas complète.


= Cours X.

#question[
  Montrer que dans tout modèle de ZF1--4, il existe un unique ensemble sans éléments.
]

Par ZF1, on a l'unicité de cet ensemble (les deux n'ont aucun éléments, ils sont donc égaux).
Pour montrer l'existence, on considère un ensemble $x in cal(U)$ où $cal(U)$ est le modèle que l'on considère (qui est nécessairement non vide par définition de modèle).
On considère la formule $phi(w_0, w_1) := bot$ qui est une relation fonctionnelle. Par ZF4 (avec $phi$ et $x$) on obtient un ensemble qui est vide.

#question[
  Montrer que ZF1, 3 et 4 impliquent l'axiome de la paire.
]

On a $emptyset$ et $wp(emptyset)$ sont dans $cal(U)$ par la preuve précédente (et ZF3).

On considère deux ensembles $a$ et $b$ et on veut construire ${a,b}$.
On utilise la formule $ phi(w_0, w_1, a, b) := (w_0 = emptyset and w_1 = a) or (w_0 = {emptyset} and w_2 = b). $
Comme $phi$ est bien une relation fonctionnelle, alors ${a,b}$ est l'image de ${emptyset, {emptyset}} = wp({emptyset})$.

#question[
  Montrer que ZF4 implique ZF4'.
]

On a une formule $phi(y, macron(v))$ et on veut montrer :
$ cal(U) models forall macron(v) forall u exists x forall y med (y in x <-> (y in u and phi(y, macron(v)))). $
On considère la formule $psi(w_0, w_1, macron(v)) := w_0 = w_1 and phi(w_0, macron(v))$ qui est bien une relation fonctionnelle en $w_0$.
On applique ZF4 à l'ensemble ambiant $u$ et la formule $psi$.


#question[
  Dans tout modèle de ZF, le produit ensembliste de deux ensembles est un ensemble.
]

Avec ZF4, on considère 
$ phi(z, v_1, v_2) := exists x exists y med (z = {{x}, {x,y}} and x in v_1 and y in v_2) $
que l'on construit dans l'ensemble ambiant $wp(wp(v_1 union v_2))$.

En effet, on code $(x, y)$ comme l'ensemble ${{x}, {x,y}}$.

#question[
  Montrer que dans tout modèle de ZF, si $a$ et $b$ sont des ensembles alors la collection $b^a$ des fonctions de $a$ dans $b$ est un ensemble.
]

Avec quelques abus de notations, on utilise ZF4 avec la formule 
$ phi(f, a, b) := mat(f subset.eq a times b; and; forall x forall y forall y' med (x, y) in f and (x, y') in f -> y = y') $
dans l'ensemble ambiant $a times b$.

#question[
  Montrer que dans tout modèle de ZF, si $a$ est une famille d’ensembles indexée par l’ensemble $I$, alors l’union (_resp_. l’intersection, le produit des $a_i$ pour $i in I$ est un ensemble.
]

/ Union.:
  On pose $b := { a_i | i in I }$ qui est bien un ensemble car on peut écrire $b$ avec ZF4, avec la relation fonctionnelle : $ phi(w_0, w_1, a) := (w_0, w_1) in a. $
  Puis, par ZF2, on a $union.big_(i in I) a_i = union.big_(z in b) z$ qui est bien un ensemble.

/ Intersection.:
  On pose $c := union.big_(i in I) a_i$ qui est un ensemble par la propriété précédente.
  On considère, par ZF4', la formule $ phi(x, a, I) := forall i med i in I -> x in a_i $
  dans l'ensemble ambiant $c$ pour construit $inter.big_(i in I) a_i$.

/ Produit.:
  La collection $product_(i in I) a_i$ est l'ensemble des fonctions de $I$ dans $union.big_(i in I) a_i$ telles que $f(i) in a_i$ pour tout $i$.
  On peut l'exprimer avec ZF4' : $ phi(f, a, I) := f "est une relation fonctionnelle"  and forall i med f(i) in a_i $
  dans l'ensemble ambiant $I times union.big_(i in I) a_i$.


= Cours XI.

#question[
  Montrer que $RR$ et $wp(NN)$ sont équipotents.
]

Avec la fonction $arctan$ (et modulo une transformation affine), on a que $(0,1)$ et $RR$ sont équipotents.
Ensuite, on a que $(0,1)$ est en bijection avec les mots binaires infinis sur l'alphabet ${mono(0), mono(1)}$ (par écriture binaire, on peut négliger les cas des écritures binaires non-uniques car on n'en a qu'un nombre dénombrable).
Et ce dernier ensemble est équipotent à $wp(NN)$ (on regarde les indices des $mono(1)$ pour construire une partie, et réciproquement).

#question[
  Montrer qu'un ordinal $lambda$ est limite ssi $lambda = union.big_(alpha < lambda) alpha$.
]

/ "$<==$".: Par contraposée, si $lambda$ n'est pas limite, c'est le successeur d'un certain ordinal $beta$.
    D'où $lambda = beta union { beta }$ et donc 
    $ union.big_(alpha in lambda) alpha = beta union union.big_(alpha in beta) alpha = beta != lambda. $

/ "$==>$".: Soit $lambda$. Montrons qu'il n'a pas de plus grand élément $beta$. Sinon, on aurait $lambda = beta union { beta }$.
    Ainsi, pour tout $alpha in lambda$, il existe $gamma in lambda$ tel que $alpha < gamma$, d'où $lambda = union.big_(gamma in lambda) gamma$.


#question[
  Montrer le théorème d'induction transfinie.
]

Si, par l'absurde, $cal(P)$ n'était pas vraie pour un certain $alpha$, soit $beta$ le plus petit ordinal de $alpha union { alpha }$ qui ne satisfait pas $cal(P)$.
Tous les ordinaux plus petits satisfont $cal(P)$, d'où $cal(P)(beta)$.
On en conclut qu'un tel $alpha$ n'existe pas.

#question[
  Montrer que $omega$ est l'ensemble des ordinaux finis et que c'est le plus petit ordinal limite.
]

1. Les éléments de $omega$ sont finis (par récurrence normale).
  Réciproquement, tout ordinal fini est soit $emptyset$ soit successeur d'un ordinal fini.
  Par récurrence (normale), on a que les ordinaux finis sont des entiers.
  On en conclut que $omega$ est l'ensemble des ordinaux finis.

2. Si $omega$ n'était pas limite, ce serait un ordinal fini (car tous ses éléments sont finis).
  D'où $omega in omega$, qui est impossible.

3. Tout élément plus petit appartient à $omega$ et les éléments de $omega$ sont les successeurs de finis et $emptyset$.
  Il n'y a donc pas d'ordinal limite plus petit que $omega$.

#question[
  Montrer que si $f$ est strictement croissante entre $alpha$ et $alpha'$ alors
  1. pour tout $beta in alpha$, on a $f(beta) >= beta$ ;
  2. $alpha' >= alpha$ ;
  3. si $f$ est un isomorphisme alors $alpha = alpha'$ et $f$ est l'identité.
]

1. Soit $beta$ le plus petit ordinal tel que $f(beta) < beta$.
   Alors, on a $f(f(beta)) < f(beta) < beta$ ce qui est absurde car $beta$ est choisi comme plus petit.

2. Soit $beta in alpha$. On a $f(beta) in alpha'$ et $beta <= f(beta)$ implique que $beta in alpha'$, d'où $alpha subset.eq alpha'$ et donc $alpha <= alpha'$.

3. On procède en deux temps.
  - La réciproque $f^(-1) : alpha' -> alpha$ est strictement croissante d'où, par le point précédent, $alpha = alpha'$.
  - Pour tout $beta in alpha$ on a que $f_(|beta)$ est strictement croissante et bijective de $beta$ dans $f(beta)$ d'où $beta = f(beta)$ par le point précédent.


= Cours XII.

#question[ Montrer que AC1 implique AC2. ]

Soit $a$ non vide. On considère $product_(emptyset != x subset.eq a) x$ qui est non vide par AC1.
Soit $f$ un de ces éléments, on a bien une fonction de choix. En effet, pour tout sous-ensemble $x$ non vide de $a$, on a $f(x) in x$.

#question[ Montrer que AC2 implique AC3. ]

Soit $a$ un ensemble dont les éléments sont non vides et deux à deux disjoints.
On considère $b = union.big_(x in a) x$ qui est un ensemble. Par AC2, on a une fonction de choix $f$ sur $wp(b)$.
On prend $c = { f(x) | x in a }$ et on a bien la propriété recherchée (car les $x$ sont disjoints).

#question[ Montrer que AC3 implique AC1. ]

Soit $X = product_(i in I) a_i$ un produit d'ensembles non vides.
On considère l'ensemble~$A := { {i} times a_i | i in I }$. Par AC3, il existe $c$ tel que, pour tout élément~$x in A$, $x inter c$ a un seul élément.
Ainsi, 
$ c =: { (i, d_i) | i in I "et" d_i "fixé" in a_i }. $
On a donc $c in product_(i in I) a_i$ (c'est le graphe d'une fonction) et donc cet ensemble est non vide.

#question[ Montrer que AC2 implique Zermelo. ]

Soit $a$ un ensemble non vide. Soit $f : wp(a) -> a$ la fonction de choix.
Considérons $theta in.not a$.

On définit par induction transfinie,
$ F(alpha) := cases( f(a without {F(beta) | beta < alpha}) & " si " a without { F(beta) | beta < alpha } != emptyset,
                      theta & " sinon".
                    ) $
Il existe un ordinal $alpha$ tel que $F(alpha) = theta$ (car sinon $F$ est une injection de $cal(O)$ dans $a$, _*absurde*_).
Le sous-ensemble ${ beta in alpha | F(beta) = theta }$ est non vide donc a un plus petit sous ensemble $beta$.
Montrons que $F_(|beta) : beta -> alpha$ est une bijection.
1. D'une part, c'est une injection par construction.
2. D'autre part, on a $F(beta) = theta$  donc ${ F(gamma) | gamma < beta } = a$ et ainsi $F_(|beta)$ est une surjection.

On conclut en définissant le bon ordre $x prec y$ ssi $F^(-1)(x) < F^(-1)(y)$.

#question[
  Montrer que Zermelo implique AC2.
]

Soit $a$ non vide. Il admet un bon ordre. On choisit $f(x) := min x$ pour le bon ordre donné, c'est bien une fonction de choix.

#question[
  Montrer que AC2 implique Zorn.
]

Soit $a$ un ensemble inductif.
Soit $f : wp(a) -> a$ une fonction de choix donnée par AC2.
On définit $C := { x subset.eq a | x "a un majorant strict dans" a }$, qui est non vide car $emptyset in C$.
On définit $m(x) := f({ y in a | y "est un majorant strict de" x "dans" a })$ sur $C$.

Soit $theta in.not a$.

Puis, par induction transfinie, on définit :
$ F(alpha) := cases(
  m({ F(beta) | beta < alpha }) & "si" { F(beta) | beta < alpha } in C ,
  theta & "sinon".
) $
Ce n'est pas une injection de $cal(O)$ dans $a$ donc il existe un ordinal $alpha$ tel que $F(alpha) = theta$.
Comme $alpha+1$ est un ordinal, l'ensemble ${ beta in alpha union { alpha } | F(beta) = theta }$ a un plus petit élément $alpha_0$.
D'où l'ensemble ${ F(beta) | beta < alpha_0 }$ n'a pas de majorant strict mais a un majorant $M$ car $a$ est inductif.
Et, $a$ n'a pas d'éléments plus grand que $a$, donc $M$ est maximal dans $a$.

#question[
  Montrer que Zorn implique AC3.
]

Soit $a$ un ensemble dont les éléments sont dijsoints et non vides.
On pose $b := union.big_(x in a) x$ et $X := { c subset.eq b | forall x in a, |c inter x| <= 1 }$.

Montrons que l'ensemble $(X, subset.neq)$ est inductif.
Soit $Y subset.eq X$ est totalement ordonné. Montrons que $Y$ a un majorant dans $X$. On pose l'ensemble $z = union.big_(y in Y) y$ qui majore $Y$.
On a bien $z in X$ (on en duplique pas d'éléments).

Comme $X$ est bien inductif, il existe $d$ un élément maximal de $X$ (par Zorn).

S'il existe $x in a$ tel que $x inter d = emptyset$ alors prenons $u in x$ et posons ainsi~$d_1 := d union {u}$ d'où $d_1 in X$ et $d subset.neq d_1$ qui implique $d$ non maximal, *_absurde_*.

D'où, pour tout $x in a$, on a $|d inter x| = 1$, ce qui montre bien AC3.


= Cours XIII.

#question[
  Montrer qu'une théorie $T$ élimine les quantificateurs ssi pour toute formule $phi(x, macron(y))$ sans quantificateur, il existe $psi(macron(y))$ sans quantificateur telle que 
  $ T tack forall macron(y) med (exists x med phi(x, macron(y)) <-> psi(macron(y))). $
]

L'implication directe est un cas particulier.
La réciproque, on montre que que c'est vrai pour une formule sous forme prénexe.
- On peut éliminer un "$exists$" le plus à l'intérieur.
- On peut éliminer un "$forall$" le plus à l'intérieur également car $ forall macron(y) med (forall x phi(x, macron(y)) <-> not (exists x not phi(x, macron(y))). $

En itérant "du plus intérieur au plus extérieur", on élimine les quantificateurs petit à petit, jusqu'à obtenir $psi(macron(y))$ sans quantificateurs.


= Cours XIV.

#question[
  Montrer que si $phi$ admet comme modèle un corps algébriquement clos de caractéristique arbitrairement grande, alors $phi$ admet comme modèle un corps de caractéristique nulle.
]

On rappelle que :
$ "ACF"_0 := "Axiomes corps" union { "Clos"_n | n in NN } union lr({ underbrace(1 + dots.c + 1, n) != 0 | n in NN }, size: #50%). $


Soit $T := "ACF"_0 union { phi }$. Montrons que $T$ a un modèle.
Pour cela, on montre que $T$ est finement satisfiable.

Soit $T' scripts(subset.eq)_"finie" T$ et soit $n$ le plus grand entier tel que $ lr((underbrace(1 + dots.c + 1, n) != 0), size: #50%) in T'. $
Soit $p > n$ un nombre premier tel que $phi$ admet comme modèle un corps algébrique clos $bb(k)$ de caractéristique $p$ (qui existe par hypothèse).
Ainsi, on a : $bb(k) models phi$ et $bb(k) models "ACF"_p$.
D'où $bb(k) models T'$.

Ainsi $T$ est finiment satisfiable donc satisfiable.
On en déduit que $phi$ admet un modèle de caractéristique $0$.


