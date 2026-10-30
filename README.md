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
`unif_problem alg ar W env s t T`, which extends `wf_algebra alg ar` (a
well-formed order-sorted algebra). Problems may contain schematic type
variables with sorts, and the type environment `θ = tyenv env` may contain
bindings. The assumptions are:
- `penv_inv alg ar W env`: θ satisfies the invariant of type unification
  (`tinv`: acyclic, well-formed bindings, one sort per type variable, indices
  no newer than `maxidx env`) and respects sorts (`tsorted`); `env` is
  acyclic, well-formed, typed in itself (`wt_env`), and its variables and
  bindings are no newer than `maxidx env`;
- `tinv` also holds for the type variables of `s` and `t` (`ptvars`);
- `s` and `t` are well-formed closed terms of type `T` in `env`
  (`typed env W [] s T`: bound variables have the types of their bindings,
  the others the types given by `W`, and types are compared modulo θ), whose
  variables are no newer than `maxidx env`.

Neither `s`, `t` nor the bindings of `env` need to be patterns or β-normal.
A solution of `env` is a pair `(ρ, σ)` (`solves`). `ρ` is a well-sorted ground
instantiation of the type variables that solves θ (`gsol`). `σ` is a closed
substitution for the term variables that fixes constants and free variables
and satisfies the bindings of the instance of `env` modulo βη. The problem is
*unifiable* if some solution, with `σ` well-typed, unifies the instances of `s`
and `t` modulo βη.

- **Termination** (`terminates`, `result`): `unify alg s t env` returns an
  environment, fails with `Unif`, or gives up with `Pattern`. It never
  diverges and raises no other exception.
- **Success** (`Ok_inv`, `Ok_sound`, `Ok_most_general`, `Ok_unifiable`,
  `Ok_patterns`): a returned `env'` extends `env`, its type environment
  extends θ, and the problem is well-formed again relative to `env'` (for a
  new typing `W'` of the unbound variables), so problems can be chained as in
  `Unify.unifiers`. `env'` is a most general unifier: its solutions are
  solutions of `env` that unify `s` and `t`. Every well-typed solution of `env`
  that unifies them extends to a solution of `env'`, the type instantiation on
  the new type variables and the substitution on the new variables. Bindings
  that are patterns stay patterns.
- **Soundness in the polymorphic semantics** (`Ok_psound`): `env'` is sound
  without instantiating type variables. Every closed substitution that
  satisfies `env'` and respects its type environment (`psat`: it identifies
  the constants and free variables whose types are equal in all solutions of
  the type environment) satisfies `env` and unifies `s` and `t`. The other
  results stay about ground instances, since such a substitution is untyped and
  may unify problems without a well-typed unifier.
- **Failure** (`Unif_not_unifiable`, `Pattern_not_pattern`): `Unif` means the
  problem is not unifiable, also when the failure comes from a clash of types
  or sorts. `Unify.unifiers` relies on this, and it is false for
  Isabelle2026's occurs check (see above). `Pattern` is raised only if `s`,
  `t` or a binding of `env` is not a pattern.
- **Decidability** (`decides`): on β-normal patterns in an environment of
  patterns, `unify` returns an environment iff the problem is unifiable and
  fails with `Unif` otherwise. On other problems it may give up both on
  unifiable problems (`?F =?= c ((λx. d) ?F)`) and on non-unifiable ones
  (`f (?F a) (?F a) =?= f b c`).

`Pattern_Example.thy` interprets the locale for five problems in the empty
environment, for an arbitrary well-formed algebra:
- `λx. ?F x =?= λx. f x x`: a unifiable pattern problem. By `decides` and the
  `Ok_*` theorems, `unify` returns a most general unifier.
- `P ?X =?= P c`, where `P` is used at the types `'a ⇒ o` and `i ⇒ o`:
  `unify` returns an environment, and every solution of its type environment
  instantiates `'a` to `i`.
- `?Z =?= g ?Z`: a pattern problem that is not unifiable (occurs check). By
  `decides`, `unify` fails with `Unif`.
- `Q ?Y =?= Q c`, where `?Y` has type `'b::{cls}` and `c` has a type without
  that sort: `unify` fails with `Unif`.
- `?F a =?= b`: not a pattern problem, although it is unifiable by
  `?F := λx. b`. Evaluating `unify` shows that it gives up with `Pattern`. The
  theorems alone cannot force this outcome.

The proofs have two layers. The core treats problems without type variables,
where the type environment is empty and all types are ground (`Pattern_*`).
Problems with type variables are then reduced to their ground instances
(`Type_*`, `Poly_*`).

The core:
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

Type variables:
- `Type_Unify.thy`, `Type_Mgu.thy`: type unification with sorts
  (`Type.unify`) terminates, returns most general well-sorted unifiers, and
  fails only with `TUnify` on non-unifiable types.
- `Poly_Inst.thy`: instantiating type variables commutes with the steps of
  `unif` (head normalisation, projection, the flexible cases) on consistently
  typed problems, up to failures.
- `Poly_Unif.thy`: the types of a problem, ground and *faithful* instances
  (which map the unbound type variables to distinct new fixed type variables),
  and well-formed problems with type variables.
- `Poly_Unif_Correct.thy`: partial correctness (`unif_post`), by induction
  over `unif`. The flexible cases follow from the core theorems on all ground
  instances. Abstractions and rigid heads are decomposed through the steps on
  the type environment.
- `Poly_Unif_Term.thy`: termination (`unif_terminates`). As long as its type
  environment does not change, `unif` runs in lockstep with its run on a
  faithful instance, which terminates by the core result. Each change of the
  type environment reduces the number of unbound type variables reachable
  from the problem.
- `Poly_Typing.thy`: typing in an environment and the invariant `penv_inv`.
  Its ground instances satisfy the invariant of the core, and `unify`
  preserves it (`postok_penv_inv`). The correctness proof only yields typings
  of the ground instances of the returned environment. A faithful instance
  identifies types only if they are equal modulo the type environment, so its
  typing reflects back to a typing in the environment (`has_type_reflect`).
- `Poly_Semantics.thy`: the polymorphic semantics (`psat`, `⊨p`).
  Equivalence in all ground instances implies equivalence in the polymorphic
  semantics (`penv_equiv_gsol`): on the atoms of the problem, a substitution
  that respects the type environment factors through a faithful instance.

Matching (`Match_*`). A matching environment `(tye, te)` instantiates the
type variables of the pattern by `tye` (applied once) and its term variables
by the bindings of `te`; the object is not instantiated (`minst`):
- `Match_Types.thy`: `Type.typ_match` is sound, complete (it binds exactly the
  type variables of the pattern, as any matcher does) and, on well-formed
  types with consistent sorts, fails only with `Type_Match`.
- `Match_Pattern.thy`: the predicate `pattern` agrees with the inductive
  characterization of patterns on proper terms without β-redexes.
- `Match_Sound.thy`: if `match` or `first_order_match` returns an
  environment, it extends the given one, binds closed terms, and instantiates
  the pattern to a term βη-equivalent to the object.
- `Match_Termination.thy`: both terminate. First-order matching recurses on
  subterms of the object; higher-order matching η-expands one side only while
  removing an abstraction from the other, so the number of abstractions
  decreases, and otherwise both sides shrink.
- `Match_Exceptions.thy`: on well-typed inputs, higher-order matching fails
  only with `Match`, or with `Pattern` if the pattern is not a pattern or the
  object has a β-redex; first-order matching fails only with `Match`.
- `Match_Complete.thy`: if some matching environment instantiates a
  higher-order pattern to a term βη-equivalent to an object without
  β-redexes, higher-order matching succeeds; repeated variables are allowed.
  The proof uses the untyped rigid decomposition and restriction lemmas of the
  unification proof. A repeated variable is compared with `aeconv`
  (α-equivalence after η-contraction), which also compares the types of bound
  variables: its binding is unique up to βη-conversion, η-contraction yields
  the βη-normal form, and typing determines the types of bound variables in
  terms without β-redexes. If the first-order instance of a pattern
  (`finst`, without βη-conversion) is the object up to α-equivalence,
  first-order matching succeeds.
- `Match_Correctness.thy`: the results for `match` (`match_terminates`,
  `match_sound`, `match_exn`: only `Match` on well-typed inputs, and
  `match_complete`) and `first_order_match_complete`.

Not covered: on cyclic environments `unify` may diverge.

To use the generated code, replace Isabelle's `src/Pure/pattern.ML` by
`thys/Pure_Pattern/generated/pattern.ML` and rebuild. Regenerate the file with
`thys/Pure_Pattern/make_pattern_ML`. With this replacement, Pure and the full
HOL session of Isabelle2026 build successfully. For the version before the
occurs check fix, HOL took 450 s elapsed and 783 s CPU time with 2 threads;
the original `pattern.ML` took 447 s and 777 s on the same machine.

## Minimal patches

The fixes of the models as patches of Isabelle2026's `src/Pure`, in the format of
Mercurial queues (with commit messages, for `hg qimport` in that order), which
also apply with `patch -p1` in the root of the Isabelle distribution:
- `patches/pattern.ML.patch`: the occurs check fix of `pattern.ML` (above).
- `patches/unify-flexflex.ML.patch`, `patches/unify-rigid-occurs.ML.patch`,
  `patches/unify-cyclic.ML.patch`, `patches/unify-saturate.ML.patch`: fixes 1–4
  of `unify.ML` (below). Each applies on its own, and they can be combined.
- `patches/thm-rename.ML.patch`: the renaming of variables in the new premises
  of `bicompose_aux` of `thm.ML`. The model of session `Pure_Thm` and its
  soundness proof (`Bicompose_Correct.thy`, `bicompose_aux_valid`) are for the
  patched function. For a lifted rule, `rename_bvars` renames variables of the
  new premises after bound variables of the subgoal, but it must keep every
  variable that occurs elsewhere in the result (`newAs_ren` in
  `Bicompose_Sound.thy`). Isabelle2026 does not keep them all, for two reasons:
  - It passes only the flex-flex pairs that the unifier returns. A variable
    from the flex-flex pairs of the rule that the unifier assigned is no longer
    in them, so it can be renamed in the new premises and escape its
    assignment.
  - It strips the lifting with the conclusion `B` of the rule rather than the
    subgoal `Bi`. If the unlifted conclusion begins with `⋀x. A x ⟹ …`, a
    premise of the same shape loses its own assumptions as well: their
    variables count as unused, and only the rest of the premise is renamed.

## A generated replacement for `unify.ML`

The session `Pure_Unify` (directory `thys/Pure_Unify`) does for Isabelle's
general higher-order unification what `Pure_Pattern` does for pattern
unification: it is a HOL model of `src/Pure/unify.ML` (Paulson's
implementation of Huet's procedure), from which a replacement for `unify.ML` is
generated. The model is faithful except for deliberate fixes (below). It builds on `Pure_Pattern` and reuses its model of
Pure's terms, types, tables (`Vartab`) and environments (`Envir.env`), and its
order-sorted type unification.

- **`Unify_Base.thy`:** the exceptions of `unify.ML` (`CANTUNIFY`, `ASSIGN`,
  `CHANGE_FAIL`) and its tracing messages, modelled by a writer/exception monad
  (`'a W`): a computation emits a list of trace events and then returns a value
  or raises an exception, with possible divergence via `partial_function
  (option)`. Also the further operations of `envir.ML`, `term.ML` and
  `logic.ML` that `unify.ML` uses (`vupdate`, `norm_term`, `fastype`,
  `body_type`, `genvars`, `rlist_abs`, …).
- **`Pure_Unify.thy`:** a literal model of `unify.ML`:
  - `eta_norm` (on-the-fly η-normalization), the occurs checks (`occurs_terms`
    and the rigid `rigid_occurs_term` with its `NoOcc`/`Nonrigid`/`Rigid`
    result), `assignment`, and `SIMPL`/`SIMPL0` (Huet's simplification of
    disagreement pairs).
  - `MATCH`/`matchcopy` (projection and imitation), the flex-flex machinery
    (`clean_ffpair`, `add_ffpair`) and `smash_flexflex`.
  - the lazy sequences of unifiers. `unify.ML` builds them from `Seq.seq`
    closures; here each closure that occurs is represented by its data
    (defunctionalization, datatype `seq`), and a function `pull` evaluates one,
    exactly as `Seq.pull` evaluates the closure. The exported entry points are
    `hounifiers`, `unifiers` and `smash_flexflex`.
- **`Pure_Unify_Code.thy`, `unify_wrapper.ML`:** as for `pattern.ML`,
  `code_printing` maps the model onto Pure's own ML types, and a thin functor
  turns the modelled exceptions and the `seq`/`pull` representation back into
  Pure's exceptions, tracing and `Seq.seq`, yielding a structure with signature
  `UNIFY`.
- **`Pure_Unify_Test.thy`:** loads the generated code with `code_reflect` and
  compares `hounifiers`, `unifiers` and `smash_unifiers` with
  `unify_reference.ML` (Pure's `unify.ML` with the same fixes) on
  about 1,700 unification problems taken from the theorems of HOL
  (resolution-style premise/conclusion pairs, flexible premises, propositions
  against variants of themselves, and flex-rigid problems). The first few
  unifiers of each, and the exceptions raised, agree exactly. The interpreted
  generated code is slower than the compiled original, so the test runs with a
  small `unify_search_bound` (read by both implementations, so the comparison
  stays faithful).
- **`make_unify_ML`:** assembles `generated/unify.ML`, a replacement for
  `src/Pure/unify.ML` (generated code plus wrapper).

**The fixes.** `unify.ML` loses unifiers in three places, and the model fixes
them:

1. *Flex-flex pairs.* `clean_term` deletes an argument of the flexible head if
   a *banned* bound variable (one that does not occur on the other side)
   occurs rigidly in it. A unifier can still use such an argument and get rid
   of the banned variable, by passing it to another argument that discards it.
   For `λj. ?F (λz. z j) =?= λj. ?G`, Pure's `Unify.hounifiers` returns only
   `?F := λx. ?G`, which does not cover the unifier `?F := λx. x (λw. c)`,
   `?G := c`. The model deletes such an argument only if every argument has a
   rigid head (constant, free or bound variable), since such arguments cannot
   discard what they are applied to. It also does not treat the arguments of a
   β-redex as rigid positions in `rigid_bound`.
2. *Rigid occurs check.* `rigid_occurs_term` rejects an assignment
   `?v := u` whenever `?v` occurs in `u` on a rigid path, whatever arguments
   it is applied to. But the arguments may let a unifier discard the
   occurrence. For `λy. ?v y =?= λy. y (?v (λz. d))`, Pure's `Unify` finds no
   unifier at all, although `?v := λy. y d` is one. (The comment in `unify.ML`
   says that completeness is sacrificed there.) In the model, an occurrence
   applied to arguments is rigid only if all arguments are bound variables, as
   in `Pattern.unify`; otherwise the pair is kept for `MATCH`.
3. *Cyclic environments.* `MATCH` copies the rigid side `u` of a flex-rigid
   pair `?v targs =?= u` into `?v`. A projection simplifies the new pairs
   before `?v` is updated, and may assign its new variables to terms that
   contain `?v`; the update of `?v` then closes a cycle in the environment, on
   which normalization diverges. For `λx. ?v x =?= λx. x (c (?F ?v))`, the
   projection `?v := λx. x (?G x)` assigns `?G := λx. c (?F ?v)`; with a further
   flex-flex pair mentioning `?v`, `Unify.hounifiers` diverges, although
   `?v := λy. y (c ?H)`, `?F := λz. ?H` is a unifier. If `?v` occurs in `u`, in
   `targs` or in the other pairs, the model takes a single step of Huet's
   procedure instead (`match1`): the projections and the imitation with new
   variables for the arguments, keeping the pair.
4. *Unsaturated flex-rigid pairs.* `SIMPL` η-expands a pair according to the
   type environment at the time it treats the pair, but a later pair may bind
   its type to a function type. `MATCH` then abstracts the copy over all
   argument types of the flexible head, although it is applied to fewer
   arguments, and returns ill-typed and wrong unifiers: for
   `k (c₁ :: ?'b) =?= k (c₁ :: 'n ⇒ 'n)` and `?v c =?= f c` (with
   `?v, f :: 'a ⇒ ?'b`), it returns `?v := λa b. f c`. The model first
   η-expands the pair until its flexible side is saturated in the current type
   environment (`match_sat`).

**An extension: guessing arities.** `unify.ML` treats an unbound type variable
like a base type, and so loses unifiers that instantiate it with a function
type: for `?F ?G =?= c` with `?F :: ?'a ⇒ 'b`, it misses
`?'a := 'd ⇒ 'b, ?F := λx. x e, ?G := λy. c`. With the new option
`unify_arity_bound` (an integer `k`, default `0`), the model guesses up to `k`
missing argument types at three places of `MATCH`: the type of the pair, the
result type of the argument of a projection, and the type of an argument of
the rigid side that ends in an unbound type variable (which then becomes a new
flex-rigid pair instead of being copied). The guess `0` comes first and is the
step of `unify.ML`; with `k = 0` nothing is guessed, and on problems without
type variables the search is that of `unify.ML` for every `k`.

Otherwise the result agrees with Pure's `Unify` (the test also reports how
often the two differ).

The only unverified parts are the `code_printing` of the abstract operations
and the wrapper, as for `pattern.ML`.

### Soundness and completeness of the search

The session `Pure_Unify_Correctness` (directory `thys/Pure_Unify_Correctness`)
proves `unify.ML` sound, from the individual steps up to the lazy enumeration
of unifiers. It reuses the de Bruijn semantics of `Pure_Pattern_Correctness`:
a Pure term is translated into the `dB` terms of `Nipkow_Grobauer_Pattern`, and
an environment denotes the closed substitutions that satisfy its bindings
modulo βη. A disagreement pair `(rb, t, u)` is *solved* by such a substitution
if it makes the abstractions of `t` and `u` over the binder `rb` βη-equal.

- **`Unify_Semantics.thy`:** reasoning about the writer monad, and soundness of
  η-normalization (`eta_norm_equiv`, `env_equiv_eta_norm`): `eta_norm` only
  η-expands, so its result is proper and βη-equivalent to the input.
- **`Unify_Soundness.thy`:** the eta-long form of a flexible term
  (`get_eta_var`) is βη-equivalent to its head variable, type unification keeps
  the term environment, and hence `assignment` is sound (`assignment_sound`).
- **`Unify_Simpl.thy`:** well-formedness (proper, ground types, no loose bound
  variables) is preserved by head normalization, `eta_norm` and assignment;
  `SIMPL0` and `SIMPL` are sound (`SIMPL0_sound`, `SIMPL_sound`): every
  solution of the resulting environment and pairs solves the input pairs.
- **`Unify_Occurs.thy`:** the occurs checks `occurs_terms` and
  `rigid_occurs_term` are sound, and complete for acyclic environments, with
  respect to reachability through the bindings (`occurs_terms_correct`,
  `rigid_occurs_term_sound`, `rigid_occurs_term_complete`); assignments keep
  the environment acyclic (`assignment_acyc`).
- **`Unify_Beta.thy`:** parallel β-reduction of `(λx̄. b) t̄` and the meaning of a
  copy `cpy targs u'`, i.e. `(λx̄. u') targs`, for projections, imitations and
  abstractions.
- **`Unify_Shape.thy`:** the flex-rigid pairs that `SIMPL` returns have a
  saturated flexible side and a rigid side in head normal form (`SIMPL_frs`);
  hence `binder_types` of the flexible head has as many arguments as the head
  is applied to (`satT_binder_types`), which `MATCH` relies on.
- **`Unify_Match.thy`:** the lazy sequences of `unify.ML` are modelled as
  defunctionalized closures (`seq`). An inductive invariant `sinv` states, with
  one rule per closure, which elements a sequence may produce for its goal
  (unifiers, reduced pair sets, copies of terms and of argument lists).
  `matchcopy` (`mc_sound`), `MATCH` (`MATCH_sound`) and `new_dset`
  (`new_dset_sound`) establish it.
- **`Unify_Flexflex.thy`:** soundness of `norm_term`, `vupdate`, `ff_assign`,
  and of the deletion of bound variables in flex-flex pairs (`change_bnos` as
  a renaming of loose bound variables, `clean_term`, `clean_ffpair`), hence of
  `add_ffpair` (`add_ffpair_sound`, `foldrW_add_ffpair_sound`).
- **`Unify_Pull.thy`:** pulling a sequence that satisfies the invariant yields
  an element for its goal and a rest that satisfies it again (`pull_sound`).
  The sequence of `hounifiers` satisfies it (`hounifiers_sinv`), so every
  element of the enumeration is a unifier (`pull_unifier`,
  `hounifiers_unifier`): it extends the input environment, and every closed
  substitution that satisfies it and solves its remaining flex-flex pairs
  solves the input pairs.
- **`Unify_Correctness.thy`:** collects the results (`eta_norm_sound`,
  `assignment_sound'`, `SIMPL_sound''`, `hounifiers_sound`).

The same session proves the search complete up to the search bound
(`Unify_Complete.hounifiers_complete`). Take a closed, well-typed solution σ
of a well-typed problem whose environment is acyclic, and suppose σ's size
(the sum of the sizes of the η-long β-normal forms of the values of the
unbound variables reachable from the pairs) is at most `unify_search_bound`.
Then every terminating enumeration of `hounifiers` contains a unifier
`(env', tps)` such that some extension σ' of σ (agreeing with σ on the
variables up to `maxidx env`) satisfies `env'` and solves the flex-flex
pairs `tps`. So σ is an instance of an enumerated unifier. The proof is
Huet's argument, adapted to `unify.ML`:

- **`Unify_Simpl_Complete.thy`:** `SIMPL0` and `SIMPL` terminate without an
  exception on well-typed pairs that σ solves; σ remains a solution, and no
  unbound variable becomes reachable (`SIMPL0_complete`, `SIMPL_complete`).
  Termination is by induction on the size of the η-long β-normal form of the
  instance under σ.
- **`Unify_Match_Complete.thy`:** Huet's lemma. For a flex-rigid pair that σ
  solves, the sequence of `MATCH` has an element that an extension of σ
  solves. The measure decreases, because the value of the flexible head is
  replaced by the values of the new variables, which are proper subterms of
  it (`mc_complete`, `MATCH_complete`).
- **`Unify_Flexflex_Complete.thy`:** `norm_term` terminates on well-typed
  terms of an acyclic environment. `add_ffpair` keeps σ, extended to the new
  variables, a solution (`clean_term_complete`, `ff_assign_complete`,
  `clean_ffpair_complete`, `add_ffpair_complete`,
  `foldrW_add_ffpair_complete`). Deleting arguments in `clean_term` loses no
  solution: a banned bound variable that occurs rigidly in an argument with
  rigid-headed siblings persists in every instance, so the solution's value
  cannot use that argument.
- **`Unify_Dfs.thy`:** the depth-first search of `pull` is adequate. A finite
  enumeration of a sequence contains all its elements (`evals_ev`), and no
  `CANTUNIFY` escapes from pulling a sequence.
- **`Unify_Complete.thy`:** induction on the measure (`search_complete`,
  `hounifiers_complete`).

The entry point `unifiers` is covered as well:

- **`Unify_Unifiers.thy`:** the pattern-unification fast path of `unifiers`
  (`unify` from `Pure_Pattern`, folded over the input pairs) terminates on
  well-typed problems (`unifiers_terminates`), and `unifiers` is sound
  (`unifiers_sound`) and complete up to the search bound
  (`unifiers_complete`).

The enumeration terminates. For every well-typed problem and every
configuration, pulling the sequence of `hounifiers` or `unifiers` repeatedly
yields finitely many unifiers and then the end of the sequence, without an
exception (`Unify_Match_Fin.hounifiers_fin`, `unifiers_fin`):

- **`Unify_Simpl_Term.thy`:** `SIMPL` terminates on well-typed pairs, without
  a solution.
- **`Unify_Fin.thy`:** the search composes finite enumerations; the search
  depth bounds the nesting of `MATCH`. The flex-flex phase always terminates
  normally, because flex-flex pairs with unbound heads are solvable: map each
  unbound variable to a constant function whose body is a free variable of
  its result type (`smash_sol`).
- **`Unify_Dead.thy`, `Unify_Match_Fin.thy`:** the sequence of `MATCH` is
  finite (`MATCH_fin`). The copy of the rigid side (`matchcopy`) terminates by
  well-founded induction on a lexicographic measure: the number of unbound
  old variables, then the size of the instance of the term to copy under the
  canonical solution. The new variables of a copy never get bound to terms
  that would increase it: if an argument of the flexible side is not a bound
  variable, they only occur applied to it and stay unbound ("dead");
  otherwise they occur only at heads and never enter the values of old
  variables. `SIMPL` preserves both shapes.

**Problems with type variables.** The `Unify_Poly_*` theories extend soundness
and completeness to problems whose types contain schematic type variables.
They work on ground instances: a solution of a problem is a ground,
well-sorted instantiation ρ of the type variables that solves the type
environment, with a closed, well-typed solution σ of the ground instance of
the problem. Typing is modulo the type environment, and the type environment
grows during the search.

- **`Unify_Poly_Semantics.thy`, `Unify_Poly_Types.thy`, `Unify_Poly_Simpl.thy`,
  `Unify_Poly_Occurs.thy`, `Unify_Poly_Shape.thy`, `Unify_Poly_Match.thy`,
  `Unify_Poly_Flexflex.thy`, `Unify_Poly_Pull.thy`:** soundness of the steps and
  of the search (`pull_psound`, `pull_punifier`): every substitution that
  respects the type environment of an enumerated unifier, satisfies it and
  solves its flex-flex pairs solves the input pairs. With `Ok_psound` of the
  pattern unifier, this also holds for the pattern fast path of `unifiers`
  (`Unify_Poly_Smash.unifiers_psound`).
- **`Unify_Poly_Typing.thy`, `Unify_Poly_Simpl_Complete.thy`:** the invariant
  `pcinv` (typing modulo the type environment, ground instances under ρ) and
  completeness of `SIMPL` (`SIMPL_pcomplete`). `SIMPL` also records the type
  environment in which it classified each flex-flex pair (`fch`).
- **`Unify_Poly_Copy.thy`, `Unify_Poly_Match_Complete.thy`:** completeness of
  `matchcopy` and `MATCH` with the arity guesses (`pmc_complete`,
  `MATCH_pcomplete`), for solutions that satisfy the *arity bound*: every
  instance under ρ of a type variable of the problem has at most `k` argument
  types in each chain of arrows (`kokA`).
- **`Unify_Poly_Flexflex_Complete.thy`:** completeness of the flex-flex phase
  (`foldrW_padd_ffpair_complete`). A type variable may become a function type
  after a flex-flex pair was classified, so the pair need not be saturated in
  the final type environment. Its heads are still saturated in the type
  environment of its classification, and the bindings of the flex-flex phase
  keep them so (`ffgood`); hence `norm_term` never turns a flexible side into
  an abstraction, and `add_ffpair` does not raise an exception.
- **`Unify_Poly_Complete.thy`:** completeness up to the search bound
  (`psearch_complete`, `hounifiers_pcomplete`). For a solution (ρ, σ) that
  satisfies the arity bound `unify_arity_bound` and whose ground measure is at
  most `unify_search_bound`, every terminating enumeration of `hounifiers`
  contains a unifier `(env', tps)` such that an extension of ρ solves the type
  environment of `env'` and an extension of σ satisfies the ground instance of
  `env'` and solves that of `tps`.

The enumeration also terminates for problems with type variables, for every
configuration and in particular every arity bound
(`Unify_Poly_Match_Fin.hounifiers_pfin`):

- **`Unify_Poly_Simpl_Term.thy`, `Unify_Poly_Fin.thy`:** `SIMPL` terminates on
  problems in the invariant `pinv`, and the search composes finite
  enumerations, as without type variables.
- **`Unify_Poly_Match_Fin.thy`:** the sequence of `MATCH` is finite
  (`MATCH_pfin`). Arity guesses introduce new type variables, so the measure
  of the copy does not use types: the number of unbound old variables, then
  the number of rigid atoms of the β-normal form of the ground instance of
  the term to copy, which is the same for every ground instance and every
  typing (`rsz`). Reachability of variables through the environment ignores
  types (`vreach`).
- **`Unify_Poly_Unifiers.thy`:** `unifiers` terminates without an exception
  and enumerates finitely many unifiers (`unifiers_pfin`); its pattern fast
  path keeps the invariant.

Finally, `smash_flexflex` (`Unify_Smash.thy`) terminates normally on every
unifier that the enumeration yields and solves its remaining flex-flex pairs
(`smash_flexflex_rres`): it binds the two heads of each pair to constant
functions with a common new body variable. The flex-flex phase keeps the heads
of the remaining pairs unbound variables after normalization (`tpok`), and the
solution `smash_sol` satisfies the new bindings, so they keep the environment
acyclic. Hence every element of the enumeration of `unifiers` smashes to a
unifier without flex-flex pairs (`unifiers_smash`).

The same holds with type variables (`Unify_Poly_Smash.thy`,
`psmash_flexflex_prres`, `unifiers_psmash`, `hounifiers_psmash`): the smashed
unifiers are unifiers of the input in the polymorphic semantics. The type of
a remaining pair may have become a function type after the pair was
classified, so the heads, normalized with their types, may take fewer
arguments than their arity; binding them to constant functions over all their
argument types still solves the pair, since both sides have the same type.

To use the generated code, replace Isabelle's `src/Pure/unify.ML` by
`thys/Pure_Unify/generated/unify.ML` and rebuild; regenerate it with
`thys/Pure_Unify/make_unify_ML`.

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
  - `Pure_Unify/`: the formalization of `src/Pure/unify.ML`
    (session `Pure_Unify`).
  - `Pure_Unify_Correctness/`: soundness of its steps and of the
    enumeration of unifiers, completeness of the search up to the search
    bound, termination of the enumeration, and correctness of
    `smash_flexflex`; soundness, completeness and termination also for
    problems with type variables (session `Pure_Unify_Correctness`).
  - `Pure_Thm/`: the formalization of `bicompose_aux` of `src/Pure/thm.ML`
    (session `Pure_Thm`), on top of the models of `pattern.ML` and `unify.ML`.
  - `Pure_Thm_Correctness/`: its soundness (`Bicompose_Correct.thy`,
    `bicompose_aux_valid`: every result is valid if the proof state and the
    rule are) and termination (`Bicompose_Fin.thy`, `bicompose_aux_terminates`:
    for a well-typed proof state and rule, neither `bicompose_aux` nor pulling
    its sequence of results raises an exception, and the sequence is finite)
    and completeness (`Bicompose_Complete.thy`, `bicompose_aux_complete`: if
    instantiations of the proof state are allowed, every element of the
    enumeration of the unifiers of every problem of the call yields a result;
    so every well-typed solution of a problem that the search bound admits,
    with the environment after the unification of the types of the variables,
    is an instance of the unifier of one of the finitely many results;
    elim-resolution skips only assumptions without solutions, as the quick
    test `could_unify` is sound) (session `Pure_Thm_Correctness`).
- `thesis/`: LaTeX sources of the thesis
- `literature/`: background material

## Checking the theories

The theories check with Isabelle2026:

    isabelle build -d thys -v Nipkow_Grobauer_Pattern Pure_Pattern Pure_Pattern_Correctness \
      Pure_Unify Pure_Unify_Correctness

`Pure_Pattern_Correctness` and `Pure_Unify_Correctness` build on
`Nipkow_Grobauer_Pattern`; `Pure_Unify` builds on `Pure_Pattern`; the remaining
sessions have `HOL` as their parent. `Nipkow_Grobauer_Pattern` loads `HOL-Library` and
`HOL-Proofs-Lambda` (for `Commutation` and `ListOrder`) from source, so it
does not need a prebuilt `HOL-Proofs` heap. The sessions contain no `sorry`.

To work on the theories interactively:

    isabelle jedit -d thys -l HOL thys/Nipkow_Grobauer_Pattern/Unif_Correctness.thy

The original development targeted an older Isabelle release (Bitbucket
`traytel/hopat`, commit `7e1efe571684`).
