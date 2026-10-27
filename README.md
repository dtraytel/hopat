# Higher-Order Pattern Unification in Isabelle/HOL

Isabelle/HOL formalization of Nipkow's unification algorithm for higher-order
patterns, on de Bruijn lambda-terms. It started from Roman Angehrn's thesis
(`thesis/thesis.pdf`) and now has full termination and correctness proofs,
following Grobauer's pen-and-paper development (Chapter 2). The
lambda-calculus theories start from `HOL/Proofs/Lambda` in the Isabelle
distribution.

## Main results

The algorithm is `unify` (in `thys/Nipkow_Grobauer_Pattern/Unification.thy`). It is a functional
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

## A generated replacement for `pattern.ML`

The session `Pure_Pattern` (directory `thys/Pure_Pattern`) is separate from the
de Bruijn development above. It formalizes the full algorithm of Isabelle's
`src/Pure/pattern.ML`, with all its extensions and shortcuts, as HOL functions:

- **`Pure_Term.thy`:** Pure's `typ`/`term`, `Vartab` and `Envir.env`, plus the
  term operations of `term.ML`. ML exceptions are modelled as an exception
  monad; possible divergence uses `partial_function (option)`.
- **`Pure_Envir.thy`:** the sort algebra operations of `sorts.ML` (`sort_le`,
  `inter_sort`, `mg_domain`, `of_sort`), order-sorted type unification and
  matching (`Type.unify`, `Type.typ_match`), and the environment operations
  (`Envir.lookup`, `head_norm`, `genvar`, `norm_type`, …).
- **`Pure_Pattern.thy`:** a literal model of `pattern.ML`, with one fix (see
  below).
  - `unify`, with projections, the two flex-flex cases, on-the-fly
    η-expansion, the occurs check and failure tracing.
  - `match`, with fallback to `first_order_match`, and `pattern`.
- **`Pure_Pattern_Code.thy`:** `code_printing` maps the model onto Pure's own
  ML types, so the generated code works directly on Isabelle's terms and
  environments. Tables map onto `Vartab`, the class algebra onto
  `Sorts.algebra`.
- **`pattern_wrapper.ML`:** a thin functor implementing signature `PATTERN`.
  It translates the modelled exceptions into Pure's exceptions and reproduces
  the `unify_trace_failure` tracing.
- **`Pure_Pattern_Test.thy`:** loads the generated code with `code_reflect`
  and compares it with Pure's `Pattern`. The problems are about 190,000
  unification and 110,000 matching problems taken from the theorems of HOL
  (resolution-like premise/conclusion pairs, flexible premises, rules against
  variants of themselves, equations against subterms). Results, including the
  exceptions raised, must agree exactly. Regression tests check the
  outcomes of the fixed occurs check (see below).
- **`make_pattern_ML`:** assembles `generated/pattern.ML`, a drop-in
  replacement for `src/Pure/pattern.ML` (generated code plus wrapper).

The only unverified parts are the `code_printing` of the abstract operations
(tables, class relation, arities, `Name.aT`) and the wrapper.

**The occurs check fix.** In Isabelle2026, the occurs check of `flexrigid`
(`pattern.ML` L270) raises `Unif` whenever `?F` occurs in the rigid side.
`Unify.unifiers` treats `Unif` as "no unifier", but the occurrence may vanish
in instances. For example, `?p =?= ¬ (?f ?p)` has the unifier
`?p := ¬ False, ?f := λ_. False`, yet `rule refl` fails on `?p = (¬ ?f ?p)`.
The model raises `Unif` only for a *rigid* occurrence (`rigid_occurs`): `?F`
applied to distinct bound variables, reached through abstractions and
arguments of rigid heads, modulo head normalisation. Otherwise it raises
`Pattern`, and `Unify.unifiers` falls back to Huet's procedure. The occurs
check itself remains, because it prevents cyclic bindings. On the HOL test
problems, the outcomes do not change.

### Correctness of the model

The session `Pure_Pattern_Correctness` (directory
`thys/Pure_Pattern_Correctness`) proves the model's `unify` correct by
translating Pure terms into the de Bruijn terms of `Nipkow_Grobauer_Pattern`. Constants and free
variables become free variables of `dB` that every unifier must fix.
Schematic variables become the variables of the substitution. An environment
denotes the substitutions that satisfy its bindings modulo βη.

The main theorems assume well-typed `s` and `t` (monomorphic types: the type
environment of `env` is empty), and a well-formed, well-typed environment
`env` whose variables are no newer than `maxidx env`. Patterns or β-normality
are not assumed unless stated.

- **Soundness** (`Pattern_Soundness.thy`, `unify_sound`): every possible
  result of `unify alg s t env` is characterised.
  - `Ok env'`: `env'` extends `env`, and every closed substitution satisfying
    `env'` satisfies `env` and unifies `s` and `t` modulo βη. `env'` is again
    well-formed, well-typed (for an extension of the typing of the variables)
    and fresh. If `s`, `t` and the bindings of `env` are β-normal patterns
    and `env` is finite and acyclic, then the same holds for `env'`, so that
    problems can be chained as in `Unify.unifiers`.
  - `Unif`: no solution of `env` unifies `s` and `t`. This is what
    `Unify.unifiers` relies on. It is false for Isabelle2026's occurs check
    (see above).
  - `Pattern` (give up): `s`, `t` or a binding of `env` is not a pattern.
  - No other exception is raised.
- **Completeness** (`Pattern_Completeness.thy`): let σ solve `env` and unify
  `s` and `t`.
  - `unify_complete`: the result of `unify` is `Pattern` or an `env'` such
    that σ extends, changing only the new variables, to a solution of `env'`.
    Together with soundness, `env'` is a most general unifier relative to
    `env`.
  - `unify_complete_pattern`: if `s`, `t` and the bindings of `env` are
    β-normal patterns and `env` is finite and acyclic, then `unify` returns
    such an `env'`.
- **Termination** (`Pattern_Termination.thy`, `unify_term`): let `s` and `t`
  be β-normal patterns whose variables are no newer than `env`, and let `env`
  be finite, acyclic and well-formed, with β-normal patterns as bindings
  (`Pattern_Patterns.thy`). Then `unify alg s t env ≠ None`: `unify` returns
  a result or raises an exception. No typing is needed. The measure is
  lexicographic: first the number of unbound variables reachable from the
  problem through the bindings, then an η-expanded size of the problem.

The proofs are structured as follows:
- `Pattern_Step_Soundness.thy`: soundness of `Ok` results, by induction
  over `unif`, without types.
- `Pattern_Step_Completeness.thy` and `Pattern_Unif_Complete.thy`:
  completeness relative to a given solution σ, which also shows soundness of
  `Unif`.
- `Pattern_Exceptions.thy`: without a solution, `unif` on well-typed inputs
  raises only `Unif` and `Pattern`, never `Pattern` on patterns, and returns
  well-typed environments. On patterns, an occurrence of the flexible head in
  the rigid side found by `occurs` is rigid, so `rigid_occurs` confirms it.

The completeness proof follows Grobauer's proof as formalized in
`Nipkow_Grobauer_Pattern`:
- *Restriction:* a flexible term that depends only on some of its arguments
  is an abstraction of a term applied to those arguments
  (`Pattern_Rigid.thy`).
- *Rigid heads:* rigid heads survive βη-normalization, by confluence.
- *Occurs check:* the measure `ld` from `Unif_Occurs.thy`. A rigid occurrence
  survives in every βη-normal instance (`rigid_occurs_ld`); head
  normalisation follows the bindings of the environment.

Unlike Grobauer's algorithm, `pattern.ML` projects the whole rigid side at
once (`proj`); its completeness (`pr_complete`) is a separate induction.

Not covered: polymorphic types and `match`. On cyclic environments `unify`
may diverge.

To use the generated code, replace Isabelle's `src/Pure/pattern.ML` by
`thys/Pure_Pattern/generated/pattern.ML` and rebuild. Regenerate the file with
`thys/Pure_Pattern/make_pattern_ML`. Before the occurs check fix, Pure and
the full HOL session of Isabelle2026 built successfully with the replacement.
HOL took 450 s elapsed and 783 s CPU time with 2 threads; the original
`pattern.ML` took 447 s and 777 s on the same machine. This has not yet been
repeated with the fixed version.

## Layout

- `thys/`: the Isabelle theories and the `ROOT` file:
  - `Nipkow_Grobauer_Pattern/`: Nipkow's algorithm and Grobauer's proofs
    (session `Nipkow_Grobauer_Pattern`):
    - `Lemmas.thy`: Facts 5–14 and Lemmas 15–23 on de Bruijn terms.
    - `Unif_Prelims.thy`, `Unif_Normal.thy`: substitutions, patterns,
      β-normal forms, normal forms and typing.
    - `Unification.thy`: the algorithm.
    - `Unif_Termination.thy`: the termination proof.
    - `Unif_Occurs.thy`: the occurs check.
    - `Unif_Correctness.thy`: the correctness proof.
  - `Pure_Pattern/`: the formalization of `src/Pure/pattern.ML`
    (session `Pure_Pattern`).
  - `Pure_Pattern_Correctness/`: its soundness, completeness and
    termination proofs (session `Pure_Pattern_Correctness`).
- `thesis/`: LaTeX sources of the thesis
- `literature/`: background material

## Checking the theories

The theories check with Isabelle2026:

    isabelle build -d thys -v Nipkow_Grobauer_Pattern Pure_Pattern Pure_Pattern_Correctness

`Pure_Pattern_Correctness` builds on `Nipkow_Grobauer_Pattern`; the other
sessions have `HOL` as their parent. `Nipkow_Grobauer_Pattern` loads `HOL-Library` and
`HOL-Proofs-Lambda` (for `Commutation` and `ListOrder`) from source, so it
does not need a prebuilt `HOL-Proofs` heap. The sessions contain no `sorry`.

To work on the theories interactively:

    isabelle jedit -d thys -l HOL thys/Nipkow_Grobauer_Pattern/Unif_Correctness.thy

The original development targeted an older Isabelle release (Bitbucket
`traytel/hopat`, commit `7e1efe571684`).
