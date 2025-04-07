#import "@preview/minitoc:0.1.0": *
#import "@preview/cetz:0.3.4"
#import "@preview/cetz-plot:0.1.1": plot
#import "@preview/lemmify:0.1.8": *
#import "@preview/numblex:0.2.0": numblex
#import "@preview/curryst:0.5.0"

#let purple = rgb("#81559b")
#let blue = rgb("#5aa9e6")
#let red = rgb("#f87060")
#let yellow = rgb("#ffcb47")
#let green = rgb("#8cd867")

#let main-color = state("main-color", blue)

#set block(breakable: true)
#show figure: set block(breakable: true)

#let algo-block(it, color: none, tack: true) = context {
  let c = main-color.get()
  let color_ = if color == none and c != blue { c } else { color }
  return [
    #linebreak()
    #box(
      pad(
        left: 10pt,
        stack(
          dir: ttb,
          box(
            stroke: (left: 1pt + color_),
            inset: (left: 10pt),
            outset: (y: 5pt),
            it,
          ),
          if tack {
            box(
              stroke: (top: 1pt + color_),
              width: 5pt,
              outset: (left: 0.5pt, y: -5pt),
            )
          },
        )
      ),
    )
    #linebreak()
  ]
}

#let proof-tree(..t) = [
  #set align(center)
  #curryst.proof-tree(..t)
]

#let algo(it, name: none, color: none) = {
  set align(left)
  set par(spacing: 1.5em)

  if name == none {
    v(-1em)
  } else {
    let color_ = if color == none { black } else { color }
    box(text(white, strong(name)), fill: color_, inset: 2mm)
    v(-2.5em)
  }

  algo-block(it, color: color)
  v(1em)
}


// Places a white rectangle to remove the tack
// Useful when you can't directly predict if there's a block after the tack (i.e. if the tack is needed)
// May cause issues when
// - a tack isn't there before
// - the background color isn't white
// - spacing has been changed in the code
#let algo-removetack() = {
  move(
    dy: -1.5em+5pt-1pt,
    dx: 10pt + 0.5pt,
    block(
      fill: white,
      width: 5pt,
      height: 2pt,
    )
  )

  v(-1.5em - 1em)
}

#let algo-in(text) = strong(smallcaps[Entrée. ]) + text + linebreak()
#let algo-out(text) = strong(smallcaps[Sortie. ]) + text + linebreak()
#let algo-return(text) = strong[Retourner ] + text
#let algo-while(cond, inside) = strong([Tant que ]) + emph(cond) + strong([ faire]) + algo-block(inside)
#let algo-for(cond, inside) = strong([Pour ]) + emph(cond) + strong([ faire]) + algo-block(inside)

#let algo-if-if(cond, inside, tack) = strong([Si ]) + emph(cond) + strong([ alors]) + algo-block(inside, tack: tack)
#let algo-if-elseif(cond, inside, tack) = strong([Sinon si ]) + emph(cond) + strong([ alors]) + algo-block(inside, tack: tack)
#let algo-if-else(inside, tack) = strong([Sinon]) + algo-block(inside, tack: tack)

#let algo-if(..args) = {
  let parts = args.pos()
  let n = parts.len()

  if n == 0 { return [] }
  if n == 1 { parts.push([]); n = n + 1 }

  for i in range(calc.ceil(n / 2)) {
    if i == 0 {
      algo-if-if(parts.at(0), parts.at(1), n == 2)
    } else if 2*i + 1 < n {
      algo-if-elseif(parts.at(2*i), parts.at(2*i+1), 2*(i+1) == n)
    } else {
      algo-if-else(parts.at(2*i), true)
    }
  }
}

#let algo-comment(it, color: rgb("#888"), oneline: true) = [
  #set text(0.8em, color)
  #show: emph
  #text($triangle.r$, 0.7em) #it
  #if not oneline { linebreak() }
]

#let page-ref(label) = locate(loc => {
  let page = query(selector(label), loc)
      .first()
      .location()
      .page()

  return link((page: page, x: 0pt, y: 0pt))[page #page]
})


#let definition-style(
  title,
  fill-color: white,
  stroke-color: blue,
  title-color: blue,  
  title-text-color: white,
  width: 100%,
  radius: 4pt,
  body,
) = {
  return block(
    fill: fill-color,
    stroke: 2pt + stroke-color,
    radius: radius,
    width: width,
    above: 26pt,
  )[
    #place(top + center, dy: -12pt)[
      #block(fill: title-color, inset: 8pt, radius: radius)[
        #text(fill: title-text-color)[*#title*]
      ]
    ]

    #block(width: 100%, inset: (top: 18pt, x: 10pt, bottom: 10pt))[
      #set align(left)
      #body
    ]
  ]
}


#let remark-style(
  title,
  fill-color: white,
  stroke-color: blue,
  title-color: blue,  
  title-text-color: white,
  width: 100%,
  radius: 4pt,
  body,
) = {
  return block(
    fill: fill-color,
    stroke: (left: 1.5pt + stroke-color),
    width: width,
    above: 26pt,
  )[
    #place(top + start, dy: -12pt, dx: -12pt)[
      #block(stroke: title-color + 1.5pt, fill: title-text-color, inset: 8pt, radius: radius)[
        #text(fill: title-color)[*#title*]
      ]
    ]

    #block(width: 100%, inset: (top: 18pt, x: 10pt, bottom: 10pt))[
      #set align(left)
      #body
    ]
  ]
}


#let theorem-style(
  title,
  fill-color: white,
  stroke-color: blue,
  title-color: blue,  
  title-text-color: white,
  additional-title: none,
  width: 100%,
  radius: 4pt,
  body,
) = {
  return block(
    fill: fill-color,
    stroke: (left: 1.5pt + stroke-color),
    width: width,
    above: 26pt,
  )[
    #place(top + start, dy: -12pt, dx: -12pt)[
      #box(stroke: title-color + 1.5pt, fill: title-color, inset: 8pt, radius: radius, baseline: 30%)[
        #text(fill: title-text-color)[*#title*]
      ]
      #h(0.5em)
      #text(fill: title-color, additional-title)
    ]

    #block(width: 100%, inset: (top: 18pt, x: 10pt, bottom: 10pt))[
      #set align(left)
      #body
    ]
  ]
}

#let example-style(
  title,
  fill-color: white,
  stroke-color: blue,
  title-color: blue,  
  title-text-color: white,
  width: 100%,
  radius: 4pt,
  body,
) = {
  return block(
    fill: fill-color,
    width: width,
    above: 26pt,
  )[
    #place(top + start, dy: -12pt, dx: -12pt)[
      #block(fill: title-text-color, inset: 8pt, radius: radius)[
        #text(fill: title-color)[_*#title*_]
      ]
    ]

    #block(width: 100%, inset: (top: 10pt, x: 10pt, bottom: 10pt))[
      #set align(left)
      #body
    ]
  ]
}

#let my-thm-style(
  thm-type, name, number, body
) = context {
  if thm-type == "Définition" {
    definition-style({
      set text(font: "Latin Modern Sans")

      if name != none [
        #thm-type (#name)
      ] else [
        #thm-type
      ]
    }, [
      #show emph: set text(main-color.get())
      #body
    ])
  } else if thm-type == "Remarque" {
    remark-style({
      set text(font: "Latin Modern Sans")

      if name != none [
        #thm-type (#name)
      ] else [
        #thm-type
      ]
    }, [
      #show emph: set text(main-color.get())
      #body
    ])
  } else if thm-type == "Exemple" {
    example-style({
      set text(font: "Latin Modern Sans")

      if name != none [
        #thm-type (#name)
      ] else [
        #thm-type
      ]
    }, [
      #show emph: set text(main-color.get())
      #body
    ])
  } else if thm-type == "Proposition" or thm-type == "Théorème" or thm-type == "Lemme" {
    theorem-style({
      set text(font: "Latin Modern Sans")

      if name != none [
        #thm-type (#name)
      ] else [
        #thm-type
      ]
    }, [
      #show emph: set text(main-color.get())
      #body
    ])
  } else {text(red, weight: "bold")[
    Bah je sais pas là... je sais pas faire un #thm-type.
  ]}
}

#let my-proof-style(
  thm-type, name, number, body
) = {
  set text(0.7em, black.lighten(50%))
  let prev-color = main-color.get()
  main-color.update(_ => gray)
  set align(left)

  {
    set text(font: "Latin Modern Sans")
    show: emph
    
    if name != none [
      #thm-type (#name).
    ] else [
      #thm-type.
    ]
  }
  

  body

  h(1fr)

  math.square

  main-color.update(_ => prev-color)
}


#let my-styling = (
  thm-styling: my-thm-style,
  proof-styling: my-proof-style,
)

#let (
  theorem, lemma, corollary,
  remark, proposition, example,
  proof, definition,
  rules: thm-rules
) = default-theorems("thm-group", lang: "fr", ..my-styling)



#let wp = [℘]
#let symd = math.class("relation", math.triangle.t)
#let withblue(it) = context text(it, main-color.get())
#let smallcaps(it) = text(font: "Latin Modern Roman Caps", it)

#let setup-layout(doc) = {
  set list(marker: (withblue[‣], withblue[–], withblue[•]))
  set enum(numbering: i => withblue(numbering("(1)", i)))
  set text(lang: "fr")
  set heading(numbering: "I.1.a.i.")
  set footnote(numbering: "[1]")
  set par(justify: true)
  set page("a5", numbering: "1 / 1", header: [#h(1fr) Hugo #smallcaps[Salou] -- #smallcaps[ens l3]])
  set outline(indent: auto, title: none)
  show outline.entry.where(
    level: 1
  ): it => {
    v(12pt, weak: true)
    strong(it)
  }
  
  show emph: set text(top-edge: "bounds")
  show strong: set text(top-edge: "bounds")
  show math.equation : set text(font: "Latin Modern Math")
  
  show quote: set align(center)
  show quote: withblue
  show quote: it => box(width: 60%, it)

  show: thm-rules
  
  set text(font: "Latin Modern Roman")

  show figure.caption: it => context [
    #text(font: "Latin Modern Sans", main-color.get())[*#it.supplement #context it.counter.display(it.numbering)*]
    --
    #it.body
  ]

  show figure.where(supplement: [Fig.]): set figure(supplement: "Figure")
  show figure.where(kind: raw): set figure(supplement: "Code")

  show math.class.where(class: "relation"): math.scripts
  show math.prec.eq: it => math.class("relation", it)
  show math.succ.eq: it => math.class("relation", it)
  show math.prec: it => math.class("relation", it)
  show math.succ: it => math.class("relation", it)
  show math.lt.eq: it => math.class("relation", math.lt.eq.slant)
  show math.gt.eq: it => math.class("relation", math.gt.eq.slant)

  show "…": ([], [.],[.],[.], []).join(h(2pt)) // show "..." with more spacing between dots
  show "⋯" : ([], [⋅],[⋅],[⋅], []).join(h(2pt)) // show "dots.c" with more spacing between dots

  show "OCaml": smallcaps
  show "?!": _ => sym.interrobang


  show heading: it => context [
    #set text(font: "Latin Modern Sans")
    #h(-1em)
    #counter(heading).display()
    #h(0.2em)
    #box(width: 2.4pt, height: 1.1em, fill: main-color.get(), baseline: 20%, radius: 50%)
    #h(0.2em)
    #it.body
  ]

  show heading.where(level: 2): emph

  doc
}

#let title(it, with-bars: true) = {
  if with-bars {
    align(center, text([---] + h(1em) + it + h(1em) + [---], 1.7em, font: "Playwrite TZ"))
  } else {
    align(center, text(it, 1.7em, font: "Playwrite TZ"))
  }
}


#let italics(x) = text(x, style: "italic")
#let colorize(it) = context text(it, main-color.get())
#let titleize(it) = context align(center, text(24pt, it, main-color.get(), font: "Latin Modern Sans", weight: "bold")) + v(2em, weak: true)
#let rm(it) = text(it, font: "Latin Modern Roman")




#let exercise-counter = counter("exercise")
#let question-counter = counter("question")

#let exercise(it, name: none, reset-question: true) = context {
  set text(purple)
  let prev-color = main-color.get()
  main-color.update(_ => purple)

  if reset-question {
    question-counter.update(_ => 0)
  }
  exercise-counter.step()

  theorem-style(
    text(font: "Latin Modern Sans")[Exercice],
    it,
    stroke-color: purple,
    title-color: purple,
    additional-title: [ *#name*],
  )

  main-color.update(_ => prev-color)
}

#let question(it) = {
  question-counter.step()
  grid(
    columns: (1cm, 1fr),
    gutter: 0.2cm,
    align(top+right)[*Q#context question-counter.display().*],
    align(top+left, it)
  )
}

#let numbered-eq(content) = math.equation(
  block: true,
  numbering: it => rm[(] + ((sym.star,) * it).join("") + rm[)],
  content,
  supplement: h(-0.35em),
)


#let bigO = math.upright[O]
#let smallo = math.upright[o]
#let bigTheta = math.upright(math.Theta)

#let sc = smallcaps
#let pbm(it) = sc(it)

#let pb-display(input, output, name: none, loose: false) = context figure(
  v(1em) +
  block(inset: (x: -10pt, y: -8.5pt))[
    #grid(columns: (
      if loose { (1.5cm, auto) }
      else { (3cm, auto) }
    ), gutter: 0.5em)[
      #set align(right + horizon)
      #if name != none { box(name, width: 10cm) + [ :] }
    ][
      #show: it => box(it, stroke: (left: main-color.get()), inset: 5pt)
      #grid(columns: 2, rows: 2, gutter: 0.5em)[
        #set align(right)
        #move(dy:-0.2em)[*Entrée.*]
      ][
        #set align(left)
        #input
      ][
        #set align(right)
        #move(dy:-0.2em)[*Sortie.*]
      ][
        #set align(left)
        #output
      ]
    ]
  ] + v(1em),
  kind: "Problem",
  supplement: "Problème"
)

#let pbm-link(ref, it) = link(ref, pbm(it))


#let toc() = {
  pagebreak(weak: true)
  pagebreak(weak: false)
  align(center,
    text(1.5em, font: "Playwrite TZ")[---#h(1em)Sommaire#h(1em)---]
  )
  outline()
}

#let transp = $ sans(upright(T)) $
