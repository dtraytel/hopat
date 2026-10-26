# Higher-Order Pattern Unification in Isabelle/HOL

Isabelle/HOL formalization of Nipkow's unification algorithm for higher-order
patterns, on de Bruijn lambda-terms. It started from Roman Angehrn's thesis
(`thesis/thesis.pdf`) and now has full termination and correctness proofs,
following Grobauer's pen-and-paper development (Chapter 2). The
lambda-calculus theories start from `HOL/Proofs/Lambda` in the Isabelle
distribution.

## Main results

The algorithm is `unify` (in `thys/Unification.thy`). It is a functional
version of Grobauer's `unif₁`, with on-the-fly η-conversion and the marker
of Section 2.2.1.

- **Termination** (`Unif_Termination.thy`, `unify_terminates`):
  `unify s t` terminates for all patterns `s` and `t`. The proof uses a
  lexicographic measure and an invariant that generalizes Grobauer's
  observations to nested markers.
- **Correctness** (`Unif_Correctness.thy`, `unify_None` and `unify_Some`):
  let `s` and `t` be patterns of the same type.
  - If `unify s t = None`, then no closed, well-typed substitution unifies
    `s` and `t` modulo βη.
  - If `unify s t = Some φ`, then `φ` is a closed unifier of `s` and `t`.
    Every closed, well-typed unifier `σ` factors through `φ`: there is a `γ`
    with `γ(φ F) ≡βη σ F` for every free variable `F` of `s` and `t`.

The single-step results follow Grobauer's Propositions 1–4:

- `otfη_unifies`: on-the-fly η-conversion.
- `cases_more_general`: the computed substitution is more general.
- `cases_same_unifiers`: the new problems have the same unifiers.
- `cases_None`: a failing step has no unifier.

The main induction is `unif_correct` (Propositions 5–7).

The occurs check (Grobauer's Fact 9, `Unif_Occurs.thy`, `occurs_check`)
needs simple types, because it fails for untyped terms. It is proven with a
type-directed measure: the depth of the η-long form of β-normal terms. This
measure is invariant under βη-equivalence and grows strictly below a rigid
head.

Where Grobauer renames bound variables, the formalization instead
instantiates the new variables with abstractions of βη-normal forms of the
given unifier.

## Layout

- `thys/`: the Isabelle theories and the `ROOT` file (session `HOPAT`):
  - `Lemmas.thy`: Facts 5–14 and Lemmas 15–23 on de Bruijn terms.
  - `Unif_Prelims.thy`, `Unif_Normal.thy`: substitutions, patterns,
    β-normal forms, normal forms and typing.
  - `Unification.thy`: the algorithm.
  - `Unif_Termination.thy`: the termination proof.
  - `Unif_Occurs.thy`: the occurs check.
  - `Unif_Correctness.thy`: the correctness proof.
  - The substitution lemma in three styles (de Bruijn, Nominal, Nominal2),
    for comparison.
- `thesis/`: LaTeX sources of the thesis
- `literature/`: background material

## Checking the theories

The theories check with Isabelle2026 and the matching AFP release (needed for
`Nominal2_Substitution_Lemma`):

    isabelle build -d thys -v HOPAT

The session has `HOL` as its parent and loads `HOL-Library`, `HOL-Nominal`,
`HOL-Proofs-Lambda` (for `Commutation` and `ListOrder`) and the AFP entry
`Nominal2` from source, so it does not need a prebuilt `HOL-Proofs` heap.
The session contains no `sorry`.

To work on the theories interactively:

    isabelle jedit -d thys -l HOL thys/Unif_Correctness.thy

The original development targeted an older Isabelle release (Bitbucket
`traytel/hopat`, commit `7e1efe571684`).
