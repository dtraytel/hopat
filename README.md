# Towards Formalizing Higher-Order Pattern Unification in Isabelle/HOL

Isabelle/HOL formalization accompanying Roman Angehrn's thesis
(`thesis/thesis.pdf`). It works towards a correctness proof of Nipkow's
unification algorithm for higher-order patterns, following Grobauer's
pen-and-paper development. The lambda-calculus theories start from
`HOL/Proofs/Lambda` in the Isabelle distribution.

## Layout

- `thys/`: the Isabelle theories and the `ROOT` file (session `HOPAT`)
- `thesis/`: LaTeX sources of the thesis
- `literature/`: background material

## Checking the theories

The theories check with Isabelle2026 and the matching AFP release (needed for
`Nominal2_Substitution_Lemma`):

    isabelle build -d thys -v HOPAT

The session has `HOL` as its parent and loads `HOL-Library`, `HOL-Nominal`,
`HOL-Proofs-Lambda` (for `Commutation` and `ListOrder`) and the AFP entry
`Nominal2` from source, so it does not need a prebuilt `HOL-Proofs` heap.

To work on the theories interactively:

    isabelle jedit -d thys -l HOL thys/Unification.thy

The original development targeted an older Isabelle release (Bitbucket
`traytel/hopat`, commit `7e1efe571684`).
