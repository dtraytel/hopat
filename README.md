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

All results are stated in `Pattern_Correctness.thy`, in the locale
`unif_problem ar V env s t T`. Its assumptions are:
- `env_inv ar V env`: `env` is acyclic, well-formed, typed by `V`, and its
  variables and bindings are no newer than `maxidx env`;
- `s` and `t` are well-formed closed terms of type `T` (monomorphic: the type
  environment of `env` is empty) whose variables are no newer than
  `maxidx env`.

Neither `s`, `t` nor the bindings of `env` need to be patterns or β-normal.
The problem is *unifiable* if some solution of `env` unifies `s` and `t`
modulo βη. A solution is a closed, well-typed substitution that fixes
constants and free variables and satisfies the bindings of `env`.

- **Termination** (`terminates`, `result`): `unify alg s t env` returns an
  environment, fails with `Unif`, or gives up with `Pattern`. It never
  diverges and raises no other exception.
- **Success** (`Ok_inv`, `Ok_sound`, `Ok_most_general`, `Ok_unifiable`,
  `Ok_patterns`): a returned `env'` extends `env` and satisfies the invariant
  again, so problems can be chained as in `Unify.unifiers`. It is a most
  general unifier relative to `env`: its solutions unify `s` and `t`, and
  every solution of `env` that unifies them extends to a solution of `env'`.
  Bindings that are patterns stay patterns.
- **Failure** (`Unif_not_unifiable`, `Pattern_not_pattern`): `Unif` means the
  problem is not unifiable. `Unify.unifiers` relies on this, and it is false
  for Isabelle2026's occurs check (see above). `Pattern` is raised only if
  `s`, `t` or a binding of `env` is not a pattern.
- **Decidability** (`decides`): on β-normal patterns in an environment of
  patterns, `unify` returns an environment iff the problem is unifiable and
  fails with `Unif` otherwise. On other problems it may give up both on
  unifiable problems (`?F =?= c ((λx. d) ?F)`) and on non-unifiable ones
  (`f (?F a) (?F a) =?= f b c`).

`Pattern_Example.thy` interprets the locale for three problems in the empty
environment:
- `λx. ?F x =?= λx. f x x`: a unifiable pattern problem. By `decides` and the
  `Ok_*` theorems, `unify` returns a most general unifier.
- `?X =?= g ?X`: a pattern problem that is not unifiable (occurs check). By
  `decides`, `unify` fails with `Unif`.
- `?F a =?= b`: not a pattern problem, although it is unifiable by
  `?F := λx. b`. Evaluating `unify` shows that it gives up with `Pattern`. The
  theorems alone cannot force this outcome.

The proofs:
- `Pattern_Semantics.thy`, `Pattern_Typing.thy`: the translation into de
  Bruijn terms, the semantics of environments, and typing.
- `Pattern_Step_Soundness.thy`: soundness of returned environments, by
  induction over `unif`, without types.
- `Pattern_Rigid.thy`, `Pattern_Step_Completeness.thy`,
  `Pattern_Unif_Complete.thy`: completeness relative to a given solution σ,
  which also shows that `Unif` is correct.
- `Pattern_Patterns.thy`, `Pattern_Exceptions.thy`: without a solution, `unif`
  on well-typed inputs raises only `Unif` and `Pattern`, never `Pattern` on
  patterns, and returns well-typed environments.
- `Pattern_Acyclic.thy`: dependencies between the variables of an
  environment.
- `Pattern_Solutions.thy`: every acyclic, well-typed environment has a
  solution.
- `Pattern_Size.thy`, `Pattern_Termination.thy`: termination. The measure is
  lexicographic: first the number of unbound variables reachable from the
  problem through the bindings, then the size of the β-normal form of the
  problem instantiated by the environment. Flexible terms count by their
  missing η-expansions, so this size does not change under the pruning
  bindings that `unify` adds. Head normalisation terminates by strong
  normalisation of the simply typed λ-calculus.

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
`thys/Pure_Pattern/make_pattern_ML`. With this replacement, Pure and the full
HOL session of Isabelle2026 build successfully. For the version before the
occurs check fix, HOL took 450 s elapsed and 783 s CPU time with 2 threads;
the original `pattern.ML` took 447 s and 777 s on the same machine.

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
