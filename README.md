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
  monad, generic in the type of exceptions (`('a, 'e) xres option`; `'a M`
  for the exceptions of `pattern.ML`); possible divergence uses
  `partial_function (option)`.
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
applied to arguments with rigid heads (constants, free or bound variables,
modulo head normalisation; `rigid_head`), reached through abstractions and
arguments of rigid heads, modulo head normalisation. Substituting such
arguments creates no β-redex, so the instance of the occurrence is at least
as large as the value of `?F` (the measure `ld`, `ld_flex_ge`), and lies
strictly inside the instance of the rigid side. Otherwise it raises
`Pattern`, and `Unify.unifiers` falls back to Huet's procedure. The occurs
check itself remains, because it prevents cyclic bindings. On the HOL test
problems, the outcomes do not change.

## Minimal patches

The fixes of the models as patches of the `src/Pure` of the Isabelle2026 release
(`ISABELLE_ID` 096842708b28), in the format of Mercurial queues (with commit
messages). They are numbered in the order of application, and each applies
cleanly after its predecessors, with `hg qimport` or with `patch -p1` in the root
of the Isabelle distribution. `patches/apply ISABELLE_HOME` applies them all;
`patches/apply -c ISABELLE_HOME` prints them as one combined patch.
They come in three groups: pattern and higher-order unification (01–05, with
the adaptation 06 of ZF to 04), the kernel `thm.ML` with its classic proofs
(07–12), and tight proofs (13–24: `zterm.ML`, and the parts of `thm.ML` and
`proofterm.ML` that build tight proofs).
- `patches/01-pattern-rigid-occurs.patch`: the occurs check fix of `pattern.ML` (above).
- `patches/02-unify-rigid-occurs.patch`, `patches/03-unify-flexflex.patch`,
  `patches/04-unify-cyclic.patch`, `patches/05-unify-saturate.patch`: fixes 1–4
  of `unify.ML` (below). The reference of the differential test of session
  `Pure_Unify` is the release's `unify.ML` with these patches applied
  (`thys/Pure_Unify/make_unify_reference`).
- `patches/06-zf-unity-indices.patch`: not a fix, but an adaptation of
  `src/ZF/UNITY/Follows.thy` to `unify-cyclic` (04). Bind-first matching creates
  intermediate variables, so the indices of the schematic variables of results
  such as `bspec [THEN bspec]` change (`?P2` becomes `?P4`), and `drule_tac`
  must name them accordingly.
- `patches/07-thm-rename-flexflex.patch`, `patches/08-thm-rename-lifting.patch`:
  the renaming of variables in the new premises
  of `bicompose_aux` of `thm.ML`. The model of session `Pure_Thm` and its
  soundness proof (`Bicompose_Correct.thy`, `bicompose_aux_valid`) are for the
  patched function. For a lifted rule, `rename_bvars` renames variables of the
  new premises after bound variables of the subgoal, but it must keep every
  variable that occurs elsewhere in the result (`newAs_ren` in
  `Bicompose_Sound.thy`). Isabelle2026 does not keep them all, for two reasons:
  - (07) It passes only the flex-flex pairs that the unifier returns. A variable
    from the flex-flex pairs of the rule that the unifier assigned is no longer
    in them, so it can be renamed in the new premises and escape its
    assignment.
  - (08) It strips the lifting with the conclusion `B` of the rule rather than the
    subgoal `Bi`. If the unlifted conclusion begins with `⋀x. A x ⟹ …`, a
    premise of the same shape loses its own assumptions as well: their
    variables count as unused, and only the rest of the premise is renamed.
- `patches/09-thm-quick-eres.patch`: the quick test of `Thm.biresolution`
  (`could_bires`), which skips rules that cannot resolve with the subgoal.
  For elim-resolution, it requires that the first premise of the rule unify
  with some assumption of the subgoal (`could_unify`). But elim-resolution
  (`Logic.assum_problems`) unifies the assumptions before the first parameter
  that follows an assumption with the rest of the lifted premise, which is
  quantified over the later parameters and assumptions: on the subgoal
  `⋀x. (⋀z. S ⟹ R) ⟹ (⋀y. S ⟹ C)`, `erule` with `R ⟹ C` fails, although
  elim-resolution solves the premise `⋀y. S ⟹ R` by the assumption
  `⋀z. S ⟹ R` (session `Unpatched_Examples`); with the tracing of unification
  failures, which disables the quick test, it succeeds. The patch compares the
  premise with the assumptions only if no parameters follow them; rules
  without premises are still skipped. The model (`test_hyps` and
  `could_bires` in `Pure_Biresolution.thy`) is for the patched function, and
  with it, the quick test skips only rules without results
  (`compose_result_could_bires` in `Biresolution_Correct.thy`). The fix
  affects completeness only.
- `patches/10-thm-assumption.patch`: the classic proof of `Thm.assumption`.
  The unifier considers the assumptions of the subgoal before normalisation
  (`Logic.assum_problems (~1, Bi)`), but the proof proves the normalised
  subgoal by `mk_asm_prf (normt Bi) n ~1`, which abstracts over all
  assumptions of the normalised subgoal. If the unifier instantiates the
  conclusion by an implication, the proof abstracts over its premises as well
  and fails the proof checker (session `Unpatched_Examples`: the subgoal
  `(A ⟹ B) ⟹ ?P`, solved with `?P := A ⟹ B`, is proved by
  `λH:A ⟹ B. λH':A. H`). The patch builds the proof from the subgoal before
  normalisation (as `Proofterm.bicompose_proof` does). The model
  (`ares_proof` in `Pure_Assumption.thy`) is for the patched function.
- `patches/11-thm-flexflex-trivial.patch`: `Thm.flexflex_rule` removes the
  trivial flex-flex pairs (`t ≡ t`) of the instances of a theorem, but returns
  the theorem unchanged if the unifier is empty. A theorem whose pairs are
  already trivial (for instance after `Thm.instantiate_beta`) keeps them, and
  `Thm.plain_prop_of` rejects the result (session `Unpatched_Examples`;
  counterexample by Kevin Kappelmann and Fabian Huch). The patch takes the
  shortcut only if no pair is trivial; the model (`fnewth` in
  `Pure_Assumption.thy`) is for the patched function.
- `patches/12-thm-generalize-tpairs.patch`: `Thm.generalize` generalizes the
  free variables of the flex-flex pairs, but its classic proof
  (`Proofterm.generalize_proof`, which gets only the proposition) abstracts only
  the variables of the proposition. A free variable that occurs only in a pair
  stays fixed in the proof, and an instance of the theorem has a proof that does
  not reconstruct (session `Unpatched_Examples`; counterexample by Kevin Kappelmann and
  Fabian Huch).
  Abstracting the variables of the pairs would not help, since the pairs
  constrain them; the patch substitutes them in the proof instead (as
  `ZTerm.generalize_proof` does for all variables). The model
  (`generalize_thm_proof` in `Pure_Subst_Rules.thy`) is for the patched
  function.
- `patches/13-zterm-ofclass.patch`: the conversion of terms to tight terms
  (`ZTerm.zterm_of`). `Logic.match_of_class` only checks that the name of the
  constant ends with `_class`, so that any term `c TYPE(T)` with such a
  constant becomes `OFCLASS`, and `ZTerm.term_of` turns it into a class
  membership proposition of type `prop`, which for a constant of another type
  is neither the original term nor well-typed (session `Unpatched_Examples`). The
  patch converts only proper class membership propositions; the model
  (`zterm_of` in `Pure_ZTerm.thy`) is for the patched function.
- `patches/14-zterm-norm-ofclass.patch`: the normalisation of tight terms with
  respect to an environment (`ZTerm.norm_term`) does not normalise the types of
  class memberships `OFCLASS(T, c)`, which `Envir.norm_term` normalises in the
  propositions of the theorems. The tight proof of a composition then
  annotates a new subgoal `OFCLASS(?'a, c)` with the uninstantiated type
  (session `Unpatched_Examples`: resolution with `OFCLASS(?'a, d_class) ⟹ P ?x` on
  `P y` for `y :: i` gives the subgoal `OFCLASS(i, d_class)`, but the tight
  proof assumes `OFCLASS(?'a, d_class)`). The model (`znorm_term_aux` in
  `Pure_ZTerm.thy`) is for the patched function.
- `patches/15-zterm-lift-frees.patch`: `ZTerm.lift_proof` increments the type
  variables of the types of schematic variables, constants and abstractions,
  but not those of free variables, which `Logic.incr_indexes` (and hence the
  lifted rule) increments. The lifted proof of a rule with a free variable of a
  schematic type then does not fit the lifted rule; it is not even well-typed
  (session `Unpatched_Examples`). The model (`zlift_term`) is for the patched function.
- `patches/16-zterm-lift-hyps.patch`: the annotations of the tight proof of a
  lifted rule (`ZTerm.lift_proof` of `zterm.ML`). Lifting keeps the assumptions
  of the subgoal unchanged in the lifted rule (`Logic.lift_all`), but
  `ZTerm.lift_proof` annotates the abstractions over them like the terms of
  the rule: the indices of their schematic variables are incremented and the
  variables are applied to the parameters. If an assumption of the subgoal
  has schematic variables, the tight proof assumes a different proposition,
  possibly with a variable of the rule (session `Unpatched_Examples`). The model of
  session `Pure_Thm` (`zlift_prems` in `Pure_ZTerm.thy`) is for the patched
  function; the classic `Proofterm.lift_proof` has no annotations there.
- `patches/17-zterm-flatten.patch`: the tight proofs of the flattened premises
  of the rule in composition (`ZTerm.bicompose_proof`). The new subgoals are the
  premises of the rule, flattened (`Logic.flatten_params`) and then normalised,
  but `ZTerm.bicompose_proof` builds the proofs of the premises from the new
  subgoals by flattening the normalised premises. If the environment
  instantiates the conclusion of a premise by a proposition with parameters
  after an assumption, the proof applies the subgoal to the parameters before
  the assumption, which is ill-typed (session `Unpatched_Examples`: resolution with
  `(⋀x. H x ⟹ ?P x) ⟹ C ?P` on `C (λx. ⋀y. K x y)`). The patch flattens the
  premises before normalisation and normalises the resulting proofs like the
  proofs of the theorems; the model (`zbicompose_core` in `Pure_ZTerm.thy`) is
  for the patched function. The classic `Proofterm.bicompose_proof` flattens
  the premises before normalisation.
- `patches/18-zterm-asm.patch` (after `zterm-flatten`): the tight proof of the
  premise of the rule that elim-resolution solves by an assumption
  (`ZTerm.mk_asm_prf` in `ZTerm.bicompose_proof`). The unifier considers the
  assumptions of the premise before normalisation (`Logic.assum_problems`, up
  to the number `m` of assumptions of the subgoal), but the tight proof
  abstracts over up to `m` assumptions of the normalised premise. If the
  premise has fewer assumptions (an unlifted rule) and the environment
  instantiates its conclusion by an implication, the proof abstracts over one
  assumption too many and is ill-typed (session `Unpatched_Examples`:
  `Thm.bicompose` with `eres_flg` and the rule `((A ⟹ B) ⟹ ?Q) ⟹ ?R` on the
  subgoal `H1 ⟹ H2 ⟹ K` proves the premise by `λH:A ⟹ B. λH':A. H`). The patch
  strips as many assumptions as `Logic.assum_problems` found; the model
  (`zasm_count` in `zbicompose_core`, `Pure_ZTerm.thy`) is for the patched
  function. The classic `Proofterm.bicompose_proof` builds this proof from the
  premise before normalisation. Biresolution lifts the rule over the subgoal,
  so that the premise has at least `m` assumptions and the fix changes
  nothing there.
- `patches/19-zterm-assumption.patch`: the tight proof of `Thm.assumption`
  (`ZTerm.assumption_proof`) has the problem of the classic one (patch 10): it
  abstracts over all assumptions of the normalised subgoal and is ill-typed
  if the unifier instantiates the conclusion by an implication (session
  `Unpatched_Examples`). The patch strips as many assumptions from the
  normalised subgoal as `Logic.assum_problems` found (as patch 18 does for
  elim-resolution). The model (`zassumption_proof` in `Pure_Assumption.thy`)
  is for the patched function. The proofs of `Thm.eq_assumption` use the
  subgoal without an environment; the tight proof normalises it, so a
  subgoal that is not `β`-normal can be affected as well.
- `patches/20-zterm-hidden.patch`: the normalisation of tight proofs
  (`ZTerm.norm_proof`) instantiates only the variables of the visible
  propositions. A variable that occurs only in the proof stays as it is, even if
  the environment binds its name (for instance after the renaming of the
  variables of the rule, when a variable of its proof already has the target
  name, possibly at another type); the normalised proof then need not fit the
  instantiated propositions. The patch raises `TERM` for such a variable
  instead. The model (`znorm_proof` in `Pure_ZTerm.thy`) is for the patched
  function, and with it the tight proofs of compositions are valid
  (`zbicompose_proof_valid` in `ZProof_Bicompose.thy`).
- `patches/21-thm-zterm-rename.patch` (after 07 and 08): when `rename_bvars`
  renames variables of the new premises of a lifted rule, `bicompose_aux`
  renames them in the classic proof of the rule as well, but not in its tight
  proof (`deriv_rule1 I proof rder`). The composed tight proof then applies a
  proof of the rule's premises with the old variables to proofs of the
  renamed ones, which is ill-typed (session `Unpatched_Examples`: resolution with
  `G ?x ⟹ F (λx. x)` on `F (λy. y)` gives the subgoal `G ?y`, but the tight
  proof of the rule still assumes `G ?x`). The patch renames the variables of
  the tight proof likewise, but only those with indices above the maximal
  index of the proof state: the premises are renamed after their lifting over
  the subgoal (`strip_apply`), so the variables of the subgoal's assumptions,
  which the lifting adds to the rule and its tight proof, keep their names
  (resolution with `G ?x ⟹ F (λx. x)` on `K ?x ⟹ F (λy. y)` gives the subgoal
  `K ?x ⟹ G ?y1`). The model (`zren_proof` in `Pure_ZTerm.thy`, used by
  `bicompose_wrapper.ML`) is for the patched function.
- `patches/22-zterm-generalize-clean.patch`: `Thm.generalize` names the new
  schematic variables with `Name.clean_index`, which strips the suffixes of
  internal names (such as skolem constants `x__`) and raises the index, but
  `ZTerm.generalize_proof` keeps the names: generalizing `x__` in `x__ ≡ x__`
  gives `?x3 ≡ ?x3` with a tight proof of `?x__1 ≡ ?x__1` (session
  `Unpatched_Examples`). Skolem constants are generalized whenever a result is
  exported from a context with fixed variables. The patch cleans the names in
  the tight proof; the model (`zgeneralize_proof`) is for the patched function.
- `patches/23-zterm-forall-intr-const.patch`: `ZTerm.forall_intr_proof` abstracts
  the variable in the terms of the proof, but not in the instances of proof
  constants, which list the free variables of their propositions. The tight
  proof of `⋀x. x ≡ x` by `forall_intr` from `x ≡ x` then proves `⋀y. x ≡ x`,
  and `abstract_rule` (as in `Conv.abs_conv`) from `Suc x ≡ Suc x` applies the
  axiom, whose premise is `⋀x. Suc x ≡ Suc x`, to a proof of `⋀y. Suc x ≡ Suc x`
  (session `Unpatched_Examples`). The patch abstracts the instances too, and
  then the instances may contain loose bound variables: the substitution and
  incrementation of bound variables in proofs (`subst_proof_bound`, used by
  the normalisation of proofs, and `incr_proof_bv`) descend into them as
  well. The models (`zabstract_proof` in `Pure_Rules.thy`,
  `zsubst_proof_bound` in `Pure_ZTerm.thy`) are for the patched functions.
- `patches/24-zterm-unconstrain.patch`: `Thm.unconstrainT` gives the
  proposition with the type variables unconstrained and the premises
  `OFCLASS` of its sort hypotheses (`Logic.unconstrainT shyps`), and a
  classic proof box of it. Its tight proof box
  (`ZTerm.add_box_proof {unconstrain = true}`) has only the premises of the
  present type variables, and is applied to class proofs `OFCLASSp` of the
  unconstrained type variables: it proves the conclusion, relying on class
  proofs for type variables without sort, and without the premise of a sort
  hypothesis without type variable (session `Unpatched_Examples`). The patch
  gives the box the sort hypotheses and applies it to no class proofs, so it
  proves the proposition of the theorem.
- `patches/afp/AutoCorres2-maxidx.patch` (for the AFP, `patch -p1` in its root):
  AutoCorres2 calls `Unify.unifiers` with `Envir.init` (maxidx −1) on terms with
  schematic variables of index 0, against the precondition of the unifier
  (`vinv`: the maxidx of the environment bounds the indices of the input). New
  variables are created at index maxidx + 1 and may then clash with variables
  of the input. The release does so only for projections and flex-flex pairs,
  `unify-cyclic` also for imitations, which makes AutoCorres2 fail with
  "Variable has two distinct types".

**Consequences without the patches.** The session `Unpatched_Examples` (`thys/Unpatched_Examples`, one theory
`Unpatched_NN_…` per patch, checked against the unpatched Isabelle2026) shows
them with ordinary proof commands:
- `unify-cyclic` is soundness-critical: `apply (rule False_aux) apply (rule refl)
  apply (rule refl) done` proves `False`, where `False_aux` is a valid rule. The
  first `rule refl` "solves" `?v = λx. x (¬ ?F ?v)` by a cyclic environment
  and leaves `?F` open; the second instantiates `?F := λw. w id`, for which the
  equation has no solution. With the fixes (`thys/Pure_Unify/unify_reference.ML`),
  the unifier is acyclic and keeps the flex-flex pair
  `?v5 ≡ ?F (λx. x (¬ ?v5))`, which then becomes unsolvable.
- `unify-saturate` is soundness-critical as well. Without it, `MATCH` binds
  the flexible head of an unsaturated flex-rigid pair to a term with a function
  arrow too many: `?v True =?= id ?x` yields `?v True` ↦ `λb. id (?x' b)`, but
  `?w := id (?x' True)` for the other side of the equation `?v True = ?w`. The
  binding is caught by type checks wherever `?v` is unified again, but not in
  the other subgoals: resolution of `¬ ?Q ?w` with
  `¬ (id (λn. n) 0 = id (λn. n) 1)` yields `?Q := λf. f 0 = f 1` and
  `?x' := λt n. n`, so that `?Q (?v True)` becomes `id (λn. n) = id (λn. n)`,
  which `refl` closes (resolution does not check the types of the terms that
  `Pattern.unify` assigns). Four proof steps prove `False`, with three
  auxiliary lemmas proved by `simp`, without overloading or type classes.
  Without such later steps, `rule` just returns proof states that are not
  well-typed (`Sign.cert_term` rejects them), and the correct unifier is lost.
- `pattern.ML`, `unify-rigid-occurs` and `unify-flexflex` affect completeness
  only: there are provable goals on which `rule refl` fails, or commits to a
  unifier that does not cover the solution. So does `thm-quick-eres`: `erule`
  fails on a goal that elim-resolution with the rule solves.

The theorems of the correctness sessions are about the patched code: soundness
of the unifier (and hence of `bicompose_aux` and `biresolution`) relies on
acyclic environments and well-typed unifiers (fixes 3 and 4), completeness on
fixes 1 and 2 and the `pattern.ML` fix, and completeness of `biresolution` also
on `thm-quick-eres`. `thm-rename` is needed for soundness of `bicompose_aux`.

With `incremented = true`, `Thm.bicompose` identifies the schematic variables
of the proof state and the rule by their names, as Metis's `resolve_inc_tyvars`
relies on. The theorems on `bicompose_aux` assume that shared variables have the
same type. If they have different types and one of them gets bound,
normalization raises `TYPE` ("Variable has two distinct types", see
session `Unpatched_Examples`); if their types are unified, both theorems are instantiated
alike, which is sound.

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
  (option)`. The monad is generic in the log and the exceptions (`WE`); the
  monads of `bicompose_aux` (`'a T`) and of the proof functions (`'a P`) are
  instances, and the tight proof functions use the exception monad (`'a Z`). Also the further operations of `envir.ML`, `term.ML` and
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
   rigid head (constant, free or bound variable) after η-contraction, since
   such arguments cannot discard what they are applied to. The η-contraction
   matters: unification η-expands bound variables of function type, and
   without it the argument `λb. a b` of `λa. ?x (λb. a b) =?= λa. ?y` is not
   deleted. The pair then stays unsolved, and the resulting theorem has a
   flex-flex pair, which `Method.insert_tac` (`Thm.forall_intr_vars`) rejects
   (`THM forall_intr` in AFP `Simplicial_complexes_and_boolean_functions`).
2. *Rigid occurs check.* `rigid_occurs_term` rejects an assignment
   `?v := u` whenever `?v` occurs in `u` on a rigid path, whatever arguments
   it is applied to. But the arguments may let a unifier discard the
   occurrence. For `λy. ?v y =?= λy. y (?v (λz. d))`, Pure's `Unify` finds no
   unifier at all, although `?v := λy. y d` is one. (The comment in `unify.ML`
   says that completeness is sacrificed there.) In the model, an occurrence
   applied to arguments is rigid only if all arguments have rigid heads, with
   the same `rigid_head` as `Pattern` (patch 02 calls `Pattern.rigid_head`);
   otherwise the pair is kept for `MATCH`. Only arguments that may become
   abstractions can let an occurrence vanish. Requiring bound variables
   instead would make Huet's procedure search up to the search bound on
   problems that the release rejects at once (AFP `FOL_Compactness`).
3. *Cyclic environments.* `MATCH` copies the rigid side `u` of a flex-rigid
   pair `?v targs =?= u` into `?v`. A projection simplifies the new pairs
   before `?v` is updated, and may assign its new variables to terms that
   contain `?v`; the update of `?v` then closes a cycle in the environment, on
   which normalization diverges. For `λx. ?v x =?= λx. x (c (?F ?v))`, the
   projection `?v := λx. x (?G x)` assigns `?G := λx. c (?F ?v)`; with a further
   flex-flex pair mentioning `?v`, `Unify.hounifiers` diverges, although
   `?v := λy. y (c ?H)`, `?F := λz. ?H` is a unifier. Divergence is not the
   worst outcome: if the variables of the cycle do not occur in the rest of
   the proof state, normalization terminates and the cyclic environment is
   taken for a unifier, although it stands for a solution only if the
   remaining variable (`?F`) discards its argument. A later step may
   instantiate it otherwise, which proves `False` (session
   `Unpatched_Examples`). As in Huet's procedure, the model assigns each
   variable before `SIMPL` is called (`mc`): a projection or the imitation
   binds `?v` to a term over new variables, and the arguments of `u` are then
   copied into those variables (`copycons`), each again bound before its
   pairs are simplified. The occurs check of `SIMPL` then rejects assignments
   such as `?G := λx. c (?F ?v)`. Only the outer abstractions of `u` are
   copied eagerly, into a new variable. The arguments are normalized in the
   environment of `MATCH`: unfolding the new assignments would not terminate,
   as for `?P ?y =?= c (?P ?y)`. A variable that is already assigned when its
   copy begins keeps its pair.
4. *Unsaturated flex-rigid pairs.* `SIMPL` η-expands a pair according to the
   type environment at the time it treats the pair, but a later pair may bind
   its type to a function type. `MATCH` then abstracts the copy over all
   argument types of the flexible head, although it is applied to fewer
   arguments, and returns ill-typed and wrong unifiers: for
   `k (c₁ :: ?'b) =?= k (c₁ :: 'n ⇒ 'n)` and `?v c =?= f c` (with
   `?v, f :: 'a ⇒ ?'b`), it returns `?v := λa b. f c`. The model first
   η-expands the pair until its flexible side is saturated in the current type
   environment (`match_sat`). In Isabelle, `rule` then yields proof states
   that are not well-typed, and from them a proof of `False`
   (session `Unpatched_Examples`).

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
  - `Pure_Lambda/`: the λ-calculus on the terms of Pure: β, η and α,
    well-typed terms in a signature, confluence of βη on well-typed terms
    modulo α, strong normalization, normal forms, and substitutions of
    schematic variables (session `Pure_Lambda`).
  - `Pure_Pattern/`: the formalization of `src/Pure/pattern.ML`
    (session `Pure_Pattern`).
  - `Pure_Unify/`: the formalization of `src/Pure/unify.ML`
    (session `Pure_Unify`).
  - `Pattern_Correctness/`: soundness, completeness and termination of
    the model of `pattern.ML` (unification and matching), for problems with
    schematic type variables and sorts (session `Pattern_Correctness`).
  - `Unify_Correctness/`: soundness of the enumeration of `unify.ML`,
    completeness up to the search bound, and termination
    (session `Unify_Correctness`).
  - `Pure_Thm/`: the formalization of the inference rules of
    `src/Pure/thm.ML` (session `Pure_Thm`), on top of the models of
    `pattern.ML` and `unify.ML`: the primitive rules (`assume`, `implies_intr`,
    `implies_elim`, `forall_intr`, `forall_elim`, `reflexive`, `symmetric`,
    `transitive`, `beta_conversion`, `eta_conversion`, `eta_long_conversion`,
    `abstract_rule`, `combination`, `equal_intr`, `equal_elim`; theory
    `Pure_Rules.thy`, also `trivial`, `weaken`, `renamed_prop`,
    `adjust_maxidx_thm`), the derived rules (`generalize`, `instantiate`,
    `instantiate_beta`, `incr_indexes`, `rotate_rule`, `permute_prems`,
    `varifyT_global'`, `legacy_freezeT`, `of_class`; `Pure_Subst_Rules.thy`),
    the axiom rule (`axiom`, with `Proofterm.axiom_proof`, `Proofterm.prop_args`,
    `Logic.unconstrainT` and `ZTerm.axiom_proof`; `Pure_Axiom.thy`), the
    stripping of sort hypotheses (`strip_shyps`, with `Sorts.witness_sorts`,
    `Sorts.minimize_sort`, `Logic.present_sorts` and the mapping of the
    types of the classic and tight proofs; `Pure_Sorts.thy`), the operations
    on certified terms (`dest_comb`, `dest_fun`, `dest_arg`, `dest_fun2`,
    `dest_arg1`, `dest_abs_fresh`, `dest_abs_global`, `free`, `var`, `apply`,
    `lambda_name`, `lambda`, `incr_indexes_cterm`, `generalize_cterm`,
    `instantiate_cterm`, `instantiate_beta_cterm`, with
    `Term.argument_type_of`; `Pure_Cterm.thy`),
    `unconstrainT` after `strip_shyps` (with `Logic.unconstrainT shyps`, the
    classic proof box of `Proofterm.unconstrain_thm_proof` and the tight
    proof box with patch `zterm-unconstrain`; `Pure_Unconstrain.thy`),
    proof by assumption and flex-flex pairs (`assumption`, `eq_assumption`,
    `flexflex_rule`; `Pure_Assumption.thy`), lifting and the composition of
    theorems (`lift_rule`, `bicompose_aux`, `biresolution`;
    `Pure_Bicompose.thy`, `Pure_Biresolution.thy`). Of the functions of
    `thm.ML` that return theorems, only the
    functions that only change the derivation, the certificate, the tags or
    the sort hypotheses (`transfer`, `name_derivation`,
    `solve_constraints`, ...) are not modelled; of `strip_shyps`, the new
    sort hypotheses and the proofs are modelled, while its constraints are
    computed by the wrapper from the data of the model. The model covers the logical
    part of a theorem (`thm_rep`: maximal index, flex-flex pairs,
    proposition); the hypotheses are an argument where a rule inspects them
    (the eigenvariable conditions), and `bicompose_wrapper.ML` builds the
    theorems (derivations, hypotheses, sort hypotheses, constraints,
    certificates, error messages that need the pretty printer) around the
    generated code, one section per part of `thm.ML` that it replaces;
    `make_thm_ML` splices them into `generated/thm.ML`. The proofs of the new
    theorems are also built by generated code: `Pure_Proofterm.thy` models
    `Proofterm.lift_proof`, `Proofterm.bicompose_proof` (with
    `norm_proof_remove_types`, including its fallback on type conflicts and
    its warnings) and `Proofterm.map_proof_terms`, on Pure's proofs directly;
    `Pure_ZTerm.thy` models the tight proofs of `zterm.ML` with
    `ZTerm.lift_proof` and `ZTerm.bicompose_proof` (the conversion of terms,
    with the type arguments of constants as a parameter, the normalisation of
    the variables visible in the propositions of the theorems, and the
    `β`-normalisation of term arguments); the proofs of the other rules are
    modelled next to the rules (including the proof constants of the equality
    axioms of `zterm.ML`).
    With `generated/thm.ML` in place of `src/Pure/thm.ML`, Pure and HOL
    build (with the default level of proofs, so that the classic and tight
    proofs of the generated code are built too); HOL takes about 1.8 times as
    long as with the original. The current version (with the sections
    `axiom`, `strip_shyps`, `unconstrainT`, `generalize_cterm` and the
    instantiation of certified terms) builds HOL with the 64-bit Poly/ML
    (`-o ML_system_64=true`, 14 minutes with 2 threads); with the default
    `x86_64_32` Poly/ML 5.9.2 the build of HOL aborts in its garbage
    collector (`quick_gc.cpp`: assertion `space != 0`), in different theories
    from run to run, while every subset of the new sections without `axiom`,
    and `axiom` without the others, builds HOL there too. `make_thm_ML` takes the generated code from
    the build of session `Pure_Thm`, or from the file `$GEN_FILE`, and
    replaces only the sections listed in `$THM_SECTIONS` if that is set (for
    bisection). A wrapper that evaluated two functions of the generated code
    on the same arguments (`combination`) made Poly/ML 5.9.2 (x86_64_32)
    crash in its garbage collector while building HOL, depending on the order
    of the two calls; the wrappers now evaluate one function that returns the
    theorem together with the data of its proofs.
  - `Pure_Thm_Test/`: differential tests of the generated code against
    `Thm`, `Proofterm` and `ZTerm` on problems taken from the theorems of HOL
    (session `Pure_Thm_Test`): the logical content of the new theorems and the
    exceptions raised must agree exactly, and so must the classic and tight
    proofs of synthetic proofs of the theorems. The axiom rule is compared on
    all axioms of HOL and on variants of them with sorts, free variables and
    renamed type variables (`Pure_Axiom_Test`); `strip_shyps` on theorems
    with hidden type variables of various sorts, with and without
    witnesses (`Pure_Strip_Shyps_Test`); the operations on certified terms
    on the closed subterms of theorems of HOL, the generalization and
    instantiation also with schematic variables, instances not of their
    sort and of the wrong type (`Pure_Cterm_Test`);
    `unconstrainT` on theorems of HOL, also with hidden type variables and an
    extra sort hypothesis, and on theorems it rejects, with the header and
    body of the proof box of Isabelle (`Pure_Unconstrain_Test`).
  - `Thm_Correctness/`: soundness, termination and completeness of
    `bicompose_aux` and `biresolution`, the abstract type of theorems, and
    the validity of the classic and tight proofs of the results
    (session `Thm_Correctness`, theory `Thm_Type`). The results are also
    described without the internals of `bicompose_aux`, as those of
    `Unify.unifiers` are (`bicompose_aux_results` in `Bicompose_Results.thy`,
    `biresolution_thms_shape` in `Thm_Type.thy`): the new theorem is
    `⟦Bs; As'⟧ ⟹ C` with a unifier of the problem of the composition and the
    flex-flex pairs of both theorems applied, up to β-reduction, modulo its own
    flex-flex pairs; `As'` are the remaining premises of the rule, with
    variables that occur only in them renamed, and flattened.
    The invariant of the theorems (`thm_wf`) does not require the schematic
    variables of a theorem to have the same type wherever their names occur,
    since the rules that combine two theorems do not keep this; biresolution
    assumes it of its arguments (`thm_cons`).
    The other inference rules of `thm.ML` map valid theorems to valid
    theorems (`Rules_Correct.thy`, `Generalize_Correct.thy`,
    `Instantiate_Correct.thy`, `Equality_Correct.thy`,
    `Generalize_Rule_Correct.thy`, `Assumption_Correct.thy`,
    `Eta_Long_Correct.thy`, `Freeze_Correct.thy`, `Varify_Correct.thy`):
    `assume`, `implies_intr`, `implies_elim`, `forall_intr`, `forall_elim`,
    `trivial`, `weaken`, `adjust_maxidx_thm`, `renamed_prop`,
    `incr_indexes`, `rotate_rule`, `permute_prems`, `instantiate`,
    `instantiate_beta`, `of_class`, `eq_assumption`, the results of
    `assumption` and `flexflex_rule` for unifiers whose solutions solve the
    problem and whose flex-flex pairs are well typed once the type
    environment is applied (Unify keeps the pairs under binders whose types
    are not normalized, so they need not be well typed as they stand), and, if the signature declares `Pure.eq` with its polymorphic
    type (the semantics then interprets it as equality), `reflexive`,
    `symmetric`, `transitive`, `equal_intr`, `equal_elim`, `combination`,
    `abstract_rule`, `beta_conversion`, `eta_conversion` and
    `eta_long_conversion`, as well as `generalize`, `varifyT_global` and
    `legacy_freezeT`, without side conditions beyond the checks of the rules:
    the flex-flex pairs are equations (both sides have the same value), so
    `generalize` and `varifyT_global` generalize the variables in the pairs
    as Isabelle does. Generalizing free type variables is sound for every
    instance because the free type variables that the instance introduces
    can be renamed apart from the generalized ones first (`valid_gen_tfrees`).
    The classic proofs of these rules are valid in every signature, without a
    model (`Rule_Proofs.thy`, `prf_valid`: every instance of the schematic
    variables turns the proof into one of the instantiated proposition in the
    proof judgment `prf_ok`, which identifies propositions modulo αβη and lets
    the argument of an implication elimination prove the premise modulo the
    instantiated flex-flex pairs as equations, where unification matched a
    rule or an assumption with a premise): for all of the rules above,
    with the classic proof of `assumption` as patched by
    `patches/10-thm-assumption.patch`, and for the equality rules if the
    equality axioms of `Pure` are the closures of the rules (locale
    `prf_eq`); for `forall_intr` and `abstract_rule`, the names of their
    variables must not occur in the axioms of the proof. For `generalize` and `varifyT_global` with free type
    variables (`prf_valid_gen_tfrees`), the generalized type variables must
    not occur in the propositions of the axioms, oracles and theorems of the
    proof (Isabelle replaces all type variables of these propositions by
    schematic ones with `Logic.unconstrainT`), and the terms of the proof
    must not refer to bound variables outside the proof (`prf_nolb`; the
    proof judgment depends on the types of such variables).
    The tight proofs (`ZRule_Proofs.thy`, `zvalid`: valid up to the types of
    the class proofs) are valid for `assume`, `trivial`, `implies_intr`,
    `implies_elim`, `forall_intr`, `forall_elim`, `incr_indexes`,
    `varifyT_global`, `legacy_freezeT`, `of_class`, `weaken`, `renamed_prop`,
    `adjust_maxidx_thm`, `permute_prems`, `rotate_rule`, `flexflex_rule`,
    `eq_assumption`, `assumption` (`ZRule_Proofs.thy`), `instantiate` and
    `generalize` (`ZSubst_Proofs.thy`), with side conditions on the encoding
    of the tight terms: the hypotheses of the proof are encoded as `zterm_of`
    encodes them (`implies_intr`), the variables of the proof that decode
    to the variable of `forall_intr` have its type in the encoding of
    `ztyp_of`, and so do all variables of the proof for `instantiate`; the
    instantiations of `instantiate` and the variables of `forall_intr` have
    no index `-1` (which tight terms reserve for free variables). The tight
    proof of `generalize` is valid with patch 22.
    The translation `zprf_tr` to classic proofs maps the proof constants of
    the equality axioms (`ZConstp`) to the classic axioms applied to their
    instances, looked up by the names of the variables (`zconst_tr`), and
    those of the other axioms (`ZTerm.axiom_proof`) to the classic axioms
    with their propositions, without type arguments, applied to the
    instances of their variables in the order of
    `Proofterm.forall_intr_variables_term` (`zax_tr`), and the tight proof
    boxes of theorems (`ZThm`) like the classic ones, to classic proof boxes
    of their propositions, without type arguments, applied in the same way
    (`zthm_tr`), so that the proof judgment admits them as atoms of the
    signature exactly as it admits classic boxes; with it,
    the tight proofs of the equality rules are valid (`ZEq_Proofs.thy`:
    `reflexive`, `beta_conversion`, `eta_conversion`, `eta_long_conversion`,
    `symmetric`, `transitive`, `equal_intr`, `equal_elim`, `abstract_rule`
    and `combination`, in locale `prf_eq`), with the reflexivity shortcuts of
    `symmetric` and `transitive`. The rules that map, normalise or lift tight
    proofs need the names of the variables of each proof constant to be
    distinct (`zconsts_ok`, which the constants of the equality axioms satisfy
    and the maps of instances keep; lifting and composition, hence
    biresolution, support such proof constants: the invariant `zinv` of the
    tight proofs of `Thm_Type` allows them), and those whose classic counterparts need
    facts about the closures of the axioms of a proof (`forall_intr`,
    `generalize`, `varifyT_global`, and the tight proof of `abstract_rule`)
    need the closures of the axioms to have no free (type) variables
    (`zeq_close_ok`, as `sign_closed` ensures). The reflexivity shortcuts of
    the tight proofs use that a valid proof uses the name `Pure.reflexive`
    only for the reflexivity axiom (`zrefl_witness`, `not_refl_witness`). The
    classic theorems of the equality rules are stated for the annotations of
    the axiom applications that the tight proofs carry.
    `Thm_Rules.thy` lifts the rules to the abstract type of theorems: an
    operation on `pure_thm` computes the logical part with the model of the
    rule and the proofs with the proof constructors applied to the proofs of
    the premises, as the wrappers of `thm.ML` do, and returns `None` if the
    rule raises an exception or the signatures of the premises differ.
    Theorems also carry their sort constraints (`th_constraints`,
    `Thm.constraints`: pairs of a type with atomic types replaced by `'a` and
    a sort, as a set; Isabelle keeps an ordered list tagged with the theory),
    computed as in `thm.ML`: kept or joined by the rules on theorems, emptied
    where Isabelle calls `Thm.solve_constraints` (`instantiate`, `of_class`,
    `strip_shyps`, before `flexflex_rule`; `solve_constraints_thm`, which
    also `β`-normalizes the tight proof as Isabelle does), and extended by the type bindings
    of the unifiers of `assumption`, `flexflex_rule`, `bicompose` and
    biresolution (`env_constraints`, `Thm.insert_constraints_env`). The type
    of theorems requires them to hold in the algebra of the signature
    (`cons_ok`), so `Thm.solve_constraints` never fails on sorts: the
    environments of the unifiers are well sorted (`tsorted`, part of the
    environment invariant `einv` of the unifiers and now of `bres_inv`).
    Certified terms form the abstract type `pure_cterm` (closed, well-typed,
    with non-negative indices bounded by the maximal index, as
    `Sign.certify_term` ensures). So far: `implies_elim`, `symmetric`,
    `transitive`, `equal_intr`, `equal_elim`, `combination`, `assume`,
    `trivial`, `weaken`, `forall_elim`, `reflexive`, `beta_conversion` and
    `eta_conversion`. `Thm_Rules2.thy` continues with `adjust_maxidx_thm`,
    `renamed_prop`, `incr_indexes`, `implies_intr`, `eta_long_conversion`,
    `permute_prems`, `rotate_rule`, `forall_intr`, `abstract_rule`,
    `generalize`, `varifyT_global`, `legacy_freezeT`, `of_class`, and
    `instantiate` and `instantiate_beta` with certified types (`pure_ctyp`)
    and terms (the instance is well formed and its proofs are valid up to the
    \<beta>-reduction of `instantiate_beta`); the rules
    that abstract over or generalize free variables require the closures of
    the axioms to have no free (type) variables (`sign_closed`, as
    `Logic.varify_global` and `Logic.unconstrainT` ensure).
    `Thm_Rules3.thy` completes the rules with `eq_assumption`, `assumption`
    and `flexflex_rule`. The lazy result sequences of the latter two are
    evaluated to the lists of their results (`aevals`, `fevals`), which
    exist for every theorem (`assumption_thms_terminates`,
    `flexflex_rule_thms_terminates`); every result is a theorem
    (`assumption_thms_results`, `flexflex_rule_thms_results`): the instance
    of the proof state, or of the theorem, by a unifier of the model of
    `Unify` (`assumption_thms_shape`, `flexflex_rule_thms_shape`). As in
    `Thm.flexflex_rule`, the flex-flex pairs of the unifiers are smashed
    (`Unify.smash_unifiers`). `Thm_Rules4.thy` adds `weaken_sorts` on
    certified terms, `lift_rule` (the rule lifted over a certified
    proposition, with its classic and tight proofs; the sort hypotheses
    include the sorts of the goal) and `varifyT_global'` (with the renaming
    of the free type variables). `Thm_Axiom.thy` adds `axiom`: the signature
    has a table of axioms (`sg_axioms`, `Theory.axiom_table`), the models of
    a signature satisfy its axioms whenever the sorts of their type
    variables are inhabited (`is_model`), and the theorem of an axiom has
    these sorts as sort hypotheses (`Sorts.insert_term`). Its classic proof
    (the proof constant of the unconstrained axiom, applied to the
    variables that `Proofterm.prop_args` keeps) and its tight proof are
    valid if the axioms are, as `Theory.add_axiom` makes them, certified
    propositions without free (type) variables and sort constraints whose
    unconstrained versions may be used in proofs under their names with the
    closures of `Proofterm` (`sign_axioms`). `Strip_Shyps_Correct.thy`
    shows that `strip_shyps` keeps the theorems valid: in every model, the
    sorts witnessed by `Sorts.witness_sorts` are inhabited if the sorts of
    the present type variables are (`witness_sorts_sound`), the remaining
    sorts are inhabited if their minimal forms are, and so the old sort
    hypotheses are inhabited if the new ones are (`strip_shyps_sinh`); the
    witnesses are also of their sorts in the algebra
    (`witness_sorts_has_sort`). For `Sorts.minimize_sort`, the class
    relation of a well-formed algebra is now required to be irreflexive
    (`wf_algebra`), as the acyclic class graph of `Sorts` makes it.
    `Thm_Cterm.thy` lifts the operations on certified terms to the abstract
    type of certified terms (also `free` and `var` on certified types,
    `lambda`, `adjust_maxidx_cterm`, `generalize_cterm` and
    `instantiate_cterm`/`instantiate_beta_cterm`, whose instances must have
    the signature of the certified term): `Term.argument_type_of` computes the type of the
    argument of a well-typed closed term, and the results are well-formed
    (closed, well-typed, with their indices bounded by the maximal index). `Thm_Bicompose.thy` lifts `Thm.bicompose` with arbitrary flags
    (`flatten`, `match`, `eres_flg`, `incremented`; the proof state is not
    lifted): without incremented variables, `Thm.unify_var_types` leaves the
    environment unchanged when the variables of both theorems have
    consistent types (`unify_var_types_vtcons`), so the results are those
    of the incremented case, which are theorems with valid classic and
    tight proofs and the sorts of the unifier as additional sort hypotheses
    (`bicompose_thms`, `bicompose_thms_results`). `Thm_Strip_Shyps.thy` lifts
    `strip_shyps` to theorems (`strip_shyps_thm`; the sort hypotheses are
    ordered by `Term_Ord.sort_ord`, so their set determines them): the
    proofs replace the type variables that do not occur in the theorem by
    present type variables, witnesses or dummy types of their sorts, which
    keeps classic proofs valid (a generalization of the hidden free type
    variables followed by an instantiation, `prf_valid_strip_atyps`) and
    tight proofs valid, whose hypotheses are kept since valid proofs have
    only hypotheses of the theorem (`zvalid_hyps`, `zstrip_proof_valid`). `Thm_Unconstrain.thy` shows that
    `unconstrainT` keeps theorems valid (`unconstrainT_valid`): the
    premises `OFCLASS` make the values of the unconstrained type variables
    values of the sorts of the old ones and of the sort hypotheses, which are
    then inhabited. `unconstrainT_thm` lifts it to theorems (after
    `strip_shyps`): its classic proof box, applied to the arguments of
    `Proofterm.prop_args` with unconstrained types, and its tight proof box
    (with patch 24, of the β-normal form of the new proposition, which
    `zthm_tr` translates) are valid if the signature admits the
    propositions of the boxes with the closures of `Proofterm`
    (`unc_box_ok`), declares the constants of the classes (`sign_ofclass`),
    the invented names are distinct, and the variables of the proposition
    have unique types (`vars_consistent`; `thm_ok_unconstrainT`). Isabelle
    does not check the last condition; without it the table of instances of
    the tight box has two keys of the same name, which a type instantiation
    of the proof (`ZTerm.map_insts`) may merge, so that the box no longer
    has an instance for each variable of its proposition; the invariant of
    tight proofs (`zconsts_ok`) excludes such tables. The equality rules require the signature to declare
    `Pure.eq` with its polymorphic type and `prop` without arguments and,
    for the proofs, the equality axioms of `Pure` (`sign_eq`). The proof judgment checks that an axiom
    named `Pure.reflexive` has the proposition of reflexivity
    (`axm_name_ok`), so the reflexivity shortcuts of `symmetric` and
    `transitive` are sound for all valid proofs.
    The proofs of theorems satisfy invariants that the rules on certified
    terms need: the types of tight proofs are canonical encodings
    (`zcanon`, part of `ztyp_ok` and hence of `zinv`; `forall_intr`,
    `abstract_rule` and `instantiate` abstract or look up variables by their
    encoded type), the hypotheses of tight proofs are encodings of
    propositions (`zhyps_ok`; `implies_intr` discharges them syntactically),
    and the terms of both proofs refer only to bound variables of
    abstractions of the proofs (`prf_nolb`, `znolb`; needed to generalize
    type variables). Biresolution keeps them (`ZProof_Closed.thy`,
    `Proof_Closed.thy`).
  - `Thm_Model_ZFC/`: a model of the axioms of the semantics of
    `Thm_Correctness` in the sets of ZFC_in_HOL; needs the AFP
    (session `Thm_Model_ZFC`).
  - `Unpatched_Examples/`: what the fixes of `unify.ML` and `pattern.ML`
    prevent, shown in the unpatched Isabelle2026, with ordinary proof commands: proofs of
    `False`, ill-typed proof states, lost unifiers (session `Unpatched_Examples`).
- `thesis/`: LaTeX sources of the thesis
- `literature/`: background material

Conventions: relations between an environment and its extension take the
original first (`extends env env'`, `textends θ θ'`, `tstep`), and their transitivity lemmas take
the premises in the same order (`extends_trans`: `extends env1 env2 ⟹
extends env2 env3 ⟹ extends env1 env3`).

## Checking the theories

The theories check with Isabelle2026:

    isabelle build -d thys -v Nipkow_Grobauer_Pattern Pure_Lambda Pure_Pattern \
      Pattern_Correctness Pure_Unify Unify_Correctness Pure_Thm Pure_Thm_Test \
      Thm_Correctness Unpatched_Examples

`Pure_Unify` and `Pure_Thm` build on `Pure_Pattern`; the remaining sessions
have `HOL` as their parent. `Nipkow_Grobauer_Pattern` is independent of the
others; it loads `HOL-Library` and `HOL-Proofs-Lambda` (for `Commutation` and
`ListOrder`) from source, so it does not need a prebuilt `HOL-Proofs` heap.
`Thm_Model_ZFC` needs the AFP (`-d AFP/thys`). The sessions contain no `sorry`.

To work on the theories interactively:

    isabelle jedit -d thys -l HOL thys/Nipkow_Grobauer_Pattern/Unif_Correctness.thy

The original development targeted an older Isabelle release (Bitbucket
`traytel/hopat`, commit `7e1efe571684`).
