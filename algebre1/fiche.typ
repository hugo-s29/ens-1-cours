#set page(columns: 2, margin: 2cm)
#set text(lang: "fr")
#show math.equation: set text(font: "Latin Modern Math")
#set heading(numbering: "I.1.A.")

#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#place(top + center, scope: "parent", float: true)[
  #[
  #set text(3em)
  #show: strong
  Algèbre 1.
  ]\
  #text(1.7em, emph[Fiche de synthèse])\
  #text(1.5em)[Hugo #smallcaps[Salou]]
]

= Sous-groupes.

- Centre d'un groupe :
  $ Z(G) := { g in G | forall x in G, g x = x g } $
  C'est un sous-groupe de $G$.

- Sous-groupe engendré par $X$ :
  $  angle.l X angle.r := inter.big_(X subset.eq H prec.eq G) H. $
  C'est un sous-groupe de $G$ et il contient $X$.

- Index de $H$ dans $G$ :
  $ [G : H] :=& \# { a H | a in G }\ =& \# { H a | a in G } $
  Pour $H = { e } =: 1$, on a $[G : 1] = |G|$.

- *Théorème de Lagrange* :
  $ [G : 1] = [G : H] dot [H : 1] $
  _Mieux_ : si $H succ.eq K$ alors 
  $ [G : K] = [G : H] dot [H : K] $

#let dist = sym.lt.tri

- Sous-groupe distingué $N dist G$ :
  $ forall g in G, quad g N g^(-1) = N $
  _Mieux_ : on n'a que l'inclusion $g N g^(-1) subset.eq N$ à démontrer quel que soit $g in G$.

- Sous groupe simple $S$ : avoir $X dist S$ implique alors $X = 1$ ou $X = G$.

- $ "distingué" times "sous-groupe" = "sous-groupe" $
- $ "distingué" times "distingué" = "distingué" $

- Sous-groupe distingué engendré par $X$ :
  $  angle.l X angle.r_"distingué" := lr(angle.l union.big_(g in G) g X g^(-1) angle.r, size: #50%). $
  C'est un sous-groupe distingué de $G$ et il contient $X$.

- $ker u dist G$ où $u : G -> H$ est un morphisme.
  _Mieux_ : c'est une équivalence
  $ "noyau" <--> "sg. distingué". $

= Quotient & isomorphisme.

- Quotient : si $N dist G$ alors $ G \/ N := { a N | a in G } $ est un groupe.
  On ajoute la _projection canonique_ :
  $ pi : G &--> G \/ N\
    g &arrow.bar.long g N $
  On a $ker(pi) = N$.

- *Factorisation d'un morp. par le quotient* :
  si $u : G -> G'$ et $u(N) = 1$ (_i.e._ $ker u = 1$)
  alors il existe un unique $macron(u) : G\/ N -> G'$.
  #diagram($
    G edge(u, ->) edge("d", pi, ->) & G' \
    G \/ N edge("ur", macron(u), -->)
  $)

#let isom = sym.tilde.equiv

- *Premier théorème d'isomorphisme*.
  #align(center, emph["factorisation de morphismes"])
  $ G \/ (ker u) isom im u $

  #diagram($
    G edge(u, ->) edge("d", pi, ->>) & G' \
    G \/ (ker u) edge("hook->>") & im u edge("u", iota, "hook->")
  $)

- *Second théorème d'isomorphisme*.\
  #align(center, emph["théorème d'isomorphisme"])
  Pour $H prec.eq G$ et $N dist G$, 
  $ H \/ (H inter N) isom H N \/ N $

- *Troisième théorème d'isomorphisme.*
  #align(center, emph["quotient de quotient par quotient"])
  
  Pour $H dist G$ et $N dist G$,
  $ G \/ H isom (G \/ N) \/ (H \/ N) $

= Actions de groupes.

- Action de groupe : $alpha : G -> "Bij"(X)$
- Orbite : $G dot x = { g dot x | g in G } subset.eq X$.
- #box(width: 110%)[Stabilisateur : $"Stab"(x) = { g in G | g dot x = x} prec.eq G$] et
  $"Stab"(g dot x) = g ("Stab" x) g^(-1)$
- Points fixes de $g in G$ : 
  $ "Fix"(g) = { x in X | g dot x = x } subset.eq X $
  et, l'ensemble des points fixes de l'action :
  $ X^G = inter.big_(g in G) "Fix"(g) $

On dit qu'une action est :
- _fidèle_ si $ker alpha = { id }$
  _"la seule action qui fixe tout le monde est l'identité"_
  (en passant au quotient, on résout ce problème) ;
- _libre_ si $forall g != 1_G, "Fix"(g) = emptyset$ ;
- _transitive_ s'il n'y a qu'une orbite : 
   $ forall x, y in X, exists g in G, y = g dot x med ; $
- _simplement transitive_ : libre et transitive (_i.e._ unicité de $g$ au dessus).

Actions classiques de $G$ sur $G$ :
- _translation gauche_ : $g dot x := g x$.\
  $->$ libre et transitive
- _conjugaison_ : $g dot x := g x g^(-1)$.

*Théorème de Caylay.*
Pour $G$ un groupe d'ordre fini $n in NN^*$, on a 
que $G$ est isomorphe à un sous-groupe de $frak(S)_n$.\
_Idée_ : $G arrow.hook frak(S)_n$ et 1er théorème d'isomorphisme.

- Classe de conjugaison : $G dot x$ pour la conjugaison
- Centralisateur : $"Stab" x$ pour la conjugaison 


Normalisateur : $ N_G (H) := { g in G | g H g^(-1) = H } dist G $
C'est le plus grand s.g.dist. contenant $H$.


