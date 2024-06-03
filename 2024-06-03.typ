#import "theorem.typ": thmplain, thmrules
#import "prooftree.typ": *

#set page(margin: 1in, numbering: "1")
#set par(leading: 0.55em, first-line-indent: 1.8em, justify: true)
#set text(font: "New Computer Modern")
#set heading(numbering: "1.1  ")
#show raw: set text(font: "New Computer Modern Mono")
#show par: set block(spacing: 0.55em)
#show heading: set block(above: 1.4em, below: 1em)

#let title = [OPLSS 1: Adjoint Functional Programming]

#set document(
  title: title,
  author: "Cameron Wong",
)

#align(center, text(17pt)[#title])
#linebreak()

#grid(
  stroke: none,
  columns: (2fr),
  align(center)[
    Lecturer: \
    Frank Pfenning
  ],
)
#linebreak()

#let unitty = $bold(1)$
#let unitval = "()"

= Lecture 1: Linear Functional Programming

Today, we will be describing the design and implementation of a language SNAX,
featuring linearity, and overloading. We'll be building towards what we call a
"proof-theoretic compiler" that is strongly based in an underlying type theory,
where we keep our typing discipline through to the end, until we reach our final
target (C).

== Basic type system

We begin with the most basic type, $unitty$.

#prooftree(axiom[], rule[$unitval : unitty$])

#linebreak()

#prooftree(
  axiom[$k in L$],
  axiom[$e : A_k$],
  rule(n:2)[$k(e) : +{l : A_l}_(l in L)$]
)
