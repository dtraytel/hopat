# Audit of the kernel formalization (2026-11-13)

Scope: sessions `Pure_Pattern`, `Pure_Unify`, `Pure_Thm`, `Pure_Thm_Test`, `Thm_Correctness`,
`Thm_Model_ZFC`, `Unpatched_Examples`, the 24 patches, and `generated/thm.ML` with its wrapper.
Question: are the main results the right statements, are they all that is needed, and do they
justify "with the patches there is no proof of `False` from `thm.ML` and friends"?

Method: comments, README and CLEANUP_PLAN were not taken as evidence. Definitions and theorem
statements were read; the models were compared with the patched ML sources function by function;
claims were tested in Isabelle (PIDE) on the installed system and on a copy with all 24 patches
applied. Section 6 lists what was run and what was not.

## 1. Bottom line

1. **The theories check.** `Thm_Correctness` (141 theories) builds in 11 minutes without errors;
   no `sorry`, `oops`, `axiomatization` or oracle; `thm_oracles` on 21 main theorems is empty.
2. **The semantic core is the right one.** Validity is ordinary Tarski validity for well-formed
   theorems (`valid_svalid`), the proof judgment is sound for it (`prf_ok_sound`,
   `prf_valid_sound`), and ZFC gives a model of every signature (`zfc_is_model`).
3. **The models agree with the patched ML wherever they were compared.** Four independent
   line-by-line readings (primitive rules; derived rules, axiom, `strip_shyps`, `unconstrainT`,
   cterms; resolution, assumption, flex-flex; `unify.ML`, `pattern.ML`, `envir.ML`, `type.ML`,
   `sorts.ML`) found no input on which a model computes another theorem or accepts what ML
   rejects. The differences found are fail-safe (3.2).
4. **"No proof of `False` with the patches" is nevertheless not a theorem here**, and does not
   follow from the theorems that are here. Three gaps separate them, in this order of importance:
   - *Coverage.* The theorems speak about lifted operations that return `None` in situations where
     the real kernel returns a theorem (Section 2). The most important case: resolution,
     assumption and `flexflex_rule` are covered only for theorems in which each schematic variable
     name has one type, which the kernel neither checks nor preserves.
   - *Model ↔ ML.* Nothing formal connects the patched ML to the models. The evidence is
     transcription plus differential tests, and the tests are much weaker than described: they
     compare printouts truncated at depth 20 without sorts, never run the patched ML, and never
     run the wrapper (Section 3).
   - *Scope.* Certification of terms, theory extension, class relations and arities, `Thm.match`,
     oracles and futures are outside the model (Section 4).
5. **The patches themselves hold up under the tests I could run.** Pure and HOL build with all 24
   patches (5 minutes). Both proofs of `False` are genuine in the installed system and fail with
   the patches. 19 of the 20 patch examples change behaviour as described. The exception is the
   example for patch 10, which is vacuous as written; the patch does fix the bug (3.4).
6. **One more bug of the same family is not patched**: the tight proof of `Thm.combination`
   instantiates the type variable of its axiom wrongly. The model copies it and the correctness
   theory proves the result "valid", because validity of tight proofs ignores type instances
   (2.7).

So: I can vouch that the patched unifier and kernel rules are what the models describe, as far
as careful reading goes, and that the models are sound inside their guards. I cannot vouch for
the unqualified claim, and the README currently states more than is proved.

## 2. Are these the right statements?

### 2.1 Shape of the soundness result

`'u pure_thm` (`Thm_Type.thy:207`) is the type of records that are well-formed, valid in every
model over `'u`, and carry valid proofs. `pure_thm_valid`, `pure_thm_holds` and
`pure_thm_consistent` then hold by unfolding the type definition. The content is in about 60
lifted operations (`implies_elim_thm`, …, `biresolution_thms`), each of the form

    if <guards> then map_option (λr. Abs_thm …) (resT (<model rule> …)) else None

with a lemma that the argument of `Abs_thm` satisfies the invariant. This is a legitimate way to
state soundness, but it has two consequences:

- There is no single statement to read. What is covered is the union of the guards of 60
  definitions in 12 theories.
- A guard that the kernel does not enforce is silently a hole: the real kernel proceeds, the
  formal operation is `None`, and no theorem applies.

### 2.2 Guards that the real kernel does not enforce

All of these were read from the definitions; file:line refers to `thys/Thm_Correctness`.

| # | Guard | Where | Real kernel |
|---|---|---|---|
| G1 | `thm_cons` (one type per variable name, one sort per type variable name); `bc_cons` across state and rule | `biresolution_thms` Thm_Type:498, `assumption_thms` Thm_Rules3:1506, `flexflex_rule_thms` Thm_Rules3:1696, `bicompose_thms` Thm_Bicompose:556 | never checked; not preserved by `implies_elim`, `forall_elim`, `instantiate`, … |
| G2 | equal signatures of all arguments | every binary rule, e.g. Thm_Rules:108, Thm_Rules2:3294 | `join_certificate` accepts sub/super theories |
| G3 | `transfer_ok`: `sign_le` and `zprf_decl` of the tight proof | Thm_Transfer:528, 612 | `Thm.transfer` checks neither; `zprf_decl` is not an invariant of `pure_thm`, and no rule is shown to preserve it; no transfer for `pure_cterm`/`pure_ctyp` |
| G4 | whole lazy sequence evaluates without exception (`∃xs. R xs`, then `THE`) | the four sequence operations | results are handed out one pull at a time |
| G5 | instantiated variables have index ≠ −1 | `instantiate_thm` Thm_Rules2:3294 | not inspected |
| G6 | `sign_axioms`: every axiom of the signature satisfies `ax_ok`, including `vtcons (vars A)` | `axiom_thm` Thm_Axiom:475–500 | `Theory.add_axiom` does not ensure `vtcons`; one such axiom disables all |
| G7 | `finite (shyps_of th)`, all sort hypotheses `sort_ok` | `strip_shyps_thm` Thm_Strip_Shyps:834, `unconstrainT_thm'` | true in ML, but not an invariant here: `cterm_ok` (Thm_Rules:1538) leaves `cd_sorts` unconstrained |
| G8 | `vars_consistent`, `sign_ofclass`, `unc_box_ok` | `unconstrainT` Thm_Unconstrain:717–941 | not checked (the theory text says so) |
| G9 | `sign_eq`, `sign_closed`, `is_prf_sig`, `cfg_alg cfg = sg_alg c`, `length (vl xs) = length xs` | equality rules, `forall_intr`, `generalize`, sequence operations | properties of Pure's theory and of `Name.variant_list`; assumed, with no instance exhibited |

G1 is the one that matters most. Checked on the real kernel (PIDE, session HOL):

- `Thm.instantiate` turns `?x = 0 ⟹ ?y = True ⟹ …` into a theorem with `?x::nat` and `?x::bool`.
  The kernel accepts it.
- Five resolution and assumption steps that bind `?x` raise `TYPE "Variable has two distinct
  types"` (`envir.ML:116`). This is the informal argument of the README, and it seems right:
  `Envir.lookup` checks the type at every use.
- A resolution step on an unrelated subgoal of the same theorem **succeeds** in ML and returns a
  theorem that again has `?x` at two types. `biresolution_thms` is `None` here.

I could not construct an unsound result, and I do not expect one. But the formal statement
excludes the case rather than covering it, and it is reachable with ordinary rules.

Two smaller points about G1:

- `thm_inv` of each result is proved internally (`biresolution_thm_inv`), but no exported lemma
  says that a result of `biresolution_thms`, `assumption_thms`, `axiom_thm`, … satisfies
  `thm_cons`. As exported, two consecutive resolution steps are not covered.
- `bc_cons` makes the model of `unify_var_types` (non-incremented `Thm.bicompose`) vacuous: the
  case where ML really unifies the types of same-named variables is `None`.

### 2.3 A specification that differs from the code

`env_sorts` (Thm_Type:470) adds the sorts of the *term* bindings of the environment to the sort
hypotheses of resolution results. `Envir.insert_sorts` (`envir.ML:97`, marked `FIXME tenv!?`),
the model `Pure_Extra` and the wrapper use the type bindings only. The lifted theorems therefore
describe a theorem with more sort hypotheses than ML produces, that is, a weaker one. The
stronger fact is proved internally and then weakened by `valid_mono`, so this is not a soundness
problem, but `rep_thm th = thm_of_bres …` does not describe the record that ML builds, and the
README's "exactly" is wrong for this field.

### 2.4 Non-vacuity is not shown

- `algebra` is a `typedecl` with unspecified constants `class_less`, `arities`
  (`Pure_Envir.thy:22`) and `classes` (`Type_Unify.thy:58`). Every result lives in
  `pure_sig = wf_algebra + ctab`, which is never interpreted and cannot be: `∃alg. wf_algebra alg
  ar` is not provable for unspecified constants. Nitpick finds a model of `wf_algebra`, so the
  locale is not contradictory; but the development contains no signature at all.
- `thm_ok` is vacuous for a signature that is not `pure_sig`.
- No theorem shows that the guards of G9 hold together for some signature (for instance Pure's),
  and no derivation is carried out with the lifted operations, not even `A ⟹ A`. The only
  inhabitant constructed is `thm0`, with proofs `None`.

### 2.5 Consistency

`pure_thm_consistent` needs a model; `zfc_consistent` supplies one only if every axiom of the
signature is an equality axiom of Pure. This is consistency of the inference rules over bare
Pure, which is the right thing to claim for `thm.ML`. It says nothing about HOL, and should not
be advertised beyond that.

### 2.6 Termination and completeness

Stated as they should be, with these limits: `biresolution_thms_terminates` assumes that
elim-rules have premises; `bicompose_thms` has no termination or completeness theorem;
completeness of the unifier is up to the search bound and, at arity bound 0, excludes solutions
whose type instantiation contains a function type.

### 2.7 Proofs, and a bug that the statements cannot see

- `prf_valid` is relative to the predicate `sg_ax`; `PThm` bodies are not checked (as in
  Isabelle). The judgment is declarative: it is not shown that `Proof_Checker` accepts a proof
  that `prf_ok` accepts.
- `zvalid ax H tps p φ ⟷ ∃w. pcerase w = pcerase (zprf_tr p) ∧ prf_valid ax H tps w φ`, and
  `zconst_tr` (`ZProof_Decode.thy:319`) drops the type instantiation of a proof constant. So
  `zvalid` holds for proof constants with arbitrary type instances.
- This hides a real defect. `thm.ML:1704` calls `ZTerm.combination_proof thy fT U f g t u`, and
  `zterm.ML:1203` uses that first type as `'a` of the axiom `f ≡ g ⟹ x ≡ y ⟹ f x ≡ g y`, where
  `'a` is the type of `x`. Checked on the real kernel with tight proofs on: for
  `f :: nat ⇒ bool`, `x :: nat` the proof constant has `'a := nat ⇒ bool` and the instance table
  maps `x :: nat ⇒ bool` to `x :: nat`. No patch addresses it; `zcombination_proof`
  (`Pure_Rules.thy:715`) copies it; `zcombination_proof_valid` (`ZEq_Proofs.thy:671`) proves it
  valid.

The classic proofs do not have this weakness. For tight proofs, the present theorems say less
than "the tight proof proves the theorem".

## 3. Is the model the code?

### 3.1 What connects them

Two artifacts come out of the models:

- `generated/thm.ML`: code generated from the models plus 1207 lines of hand-written wrapper.
  The wrapper builds every `Thm`, `Cterm` and `Ctyp` record; the generated code computes
  `(maxidx, tpairs, prop)`, the proof terms and the list operations for hyps, shyps and
  constraints. The unifier that runs is ML's `Unify.unifiers`, not the generated one. By the
  README's own account the result is 1.8 times slower and crashes the default Poly/ML in its
  garbage collector. It is a test vehicle, not a deliverable.
- The 24 patches. Nothing formal links "release + patches" to the models.

So for the patches the whole argument is: the models were transcribed carefully, and the tests
would notice a mistake.

### 3.2 Transcription: what the reading found

No logical discrepancy. Differences, all fail-safe or cosmetic:

- `String.literal` is 7-bit. With a non-ASCII name the generated code raises `Fail` where ML
  succeeds (`Thm.generalize` of `ä`, `zterm_of`, `Thm.lambda`). The models and theorems do not
  cover such names.
- Wrapper: `biresolution` evaluates `make_context` before `dest_state` and for empty rule lists
  (raises `CONTEXT` where ML returns the empty sequence); `insert_constraints_env` turns a `TYPE`
  into `Fail`; exception order differs when two things fail.
- `pointer_eq` is *defined* as `False` (`Pure_Extra.thy:75`) and *printed* as ML `pointer_eq`.
  All 18 uses have the shape `if pointer_eq a b then shortcut else full` and the shortcut is
  right, but that is an argument in prose: the generated code is not the code of the definition.
- `vt_dest`, `zv_dest`, `zt_dest` are `SOME`-specifications printed as `Vartab.dest` etc.

### 3.3 Tests: weaker than described

Checked in a batch build, which is how the tests run:

- **Results are compared as strings of `\<^make_string>` at print depth 20.** A wrong conclusion
  of a rule with 6 premises is invisible; so is a wrong subterm under 9 applications. 16,495 of
  the 29,151 facts of HOL print with an ellipsis. Sorts are not printed, so `?'a::{}` and
  `?'a::order` compare equal. Only `Pure_Extra_Test` and part of `Pure_Axiom_Test` use `=`.
- **No test runs the patched ML.** For patches 09–24 the reference is an emulation of the patch
  written inside the test theory. Patches 13 and 20 have no test. The exception is
  `unify_reference.ML`, which is the patched `unify.ML` up to renaming.
- **The wrapper is never executed by a test.** The tests use a separate `code_reflect` and their
  own glue returning `(prop, tpairs, maxidx)`. Hyps, shyps, constraints, certificates and
  derivations of `bicompose_wrapper.ML` are exercised only by a full build of HOL, which no
  script or session performs.
- Proof tests feed both sides with arguments computed by the model and use one synthetic proof
  skeleton per theorem.
- A test passes with zero cases: no count is asserted; timeouts and cases where the model raises
  while preparing arguments are dropped.
- Rules and states in the resolution tests never have flex-flex pairs or hypotheses; sequences
  are compared on their first 2–5 elements, with search bound 10.
- The installed Isabelle is not the release: `src/Pure/thm.ML` was edited in place and equals
  release + patches 07 and 08.

What is good: exceptions are compared with message, index and theorems; error paths are
targeted; bound-variable names are compared; every replaced rule has a test of its logical part
against the real `Thm.*`.

### 3.4 What I ran on a fully patched Isabelle

- All 24 patches apply in order to the release (07 and 08 are already in the installed tree).
  Pure and HOL build: 5 min 8 s.
- `Unpatched_04` and `Unpatched_05` are genuine proofs of `False` in the installed system
  (no oracle, no hypotheses). On the patched system both fail at the unsound step.
- Examples 01–05, 09, 11–19, 21–24 change behaviour as described. `Unpatched_Box_Instances` and
  `Unpatched_Incremented` do not, as documented.
- **`Unpatched_10_Thm_Assumption` passes on both systems.** Its goal state is built before
  `Proofterm.proofs := 2`, at the default level 0, so the proof is partial and `checks th` fails
  for that reason. With the state built at level 2, the unpatched system gives
  `Non-unifiable terms` (the bug) and the patched one checks. The bug and the fix are real; the
  example shows neither.

### 3.5 The differential tests on both systems

- Installed system (release + 07 + 08), as shipped: `Pure_Thm_Test` passes (12 min 31 s).
- Fully patched system, as shipped: the suite cannot run. It stops at three places that encode
  the unpatched reference, not at disagreements:
  - `Pure_Pattern_Test.thy:198` expects `Unif` from the system's `Pattern` on C1–C4; with patch
    01 both sides give `Pattern`.
  - `Pure_Rules_Test.thy:348` and `Pure_Unify_Test.thy:263` assert that the system still has the
    old behaviour.
  - `Pure_Proofterm_Test` applies the emulated fixes 15/16 on top of the output of
    `ZTerm.lift_proof`. On patched output the emulation is not idempotent (27 of 1015 differ).
- Fully patched system, with those places adjusted in a scratch copy (expectation of C1–C4
  changed; patched `ZTerm.lift_proof` and `ZTerm.bicompose_proof` compared directly with the
  generated code, without emulation):
  - `Pure_Pattern`: about 20,000 unification and matching problems each, no mismatch.
  - `Pure_Bicompose_Test`, `Pure_Assumption_Test`, `Pure_Axiom_Test`, `Pure_Cterm_Test`,
    `Pure_Extra_Test`, `Pure_Strip_Shyps_Test`, `Pure_Unconstrain_Test`: pass.
  - Tight `lift_proof`: 1015 cases, 0 mismatches. Tight `bicompose_proof`: 314 + 54 + 11 + 16
    cases, 0 mismatches. Classic proofs: 0 mismatches.
  - `Pure_Rules_Test` and `Pure_Unify_Test` were not adjusted beyond their first assertion and
    did not run to the end.

This is the first direct evidence that the patched ML agrees with the models, and it is
favourable. It is subject to the limits of 3.3: equality of printouts at depth 20, without
sorts. One line of the report also shows the zero-case problem in practice:
`bicompose_proof (composition, no flattening): 0 tests, 0 mismatches`.

## 4. Are these all the statements needed?

Missing for the claim as the README makes it:

1. Soundness of the sequence rules without `thm_cons`/`bc_cons` (G1), or a proof that the model
   raises there.
2. Rules over related, not equal, signatures (G2, G3), including cterms.
3. Statements per pull for lazy sequences (G4).
4. The invariants that ML maintains and the guards merely assume (G5–G8).
5. A signature for which everything holds, and one derivation through the lifted operations
   (2.4).
6. A validity notion for tight proofs that checks type instances (2.7).
7. Anything about the parts of the kernel that are not modelled:
   `cterm_of`/`ctyp_of` (`Sign.certify`; every `pure_cterm` is assumed certified),
   `Thm.match`/`first_order_match` (build cterms from `Pattern.match`),
   `add_classrel`, `add_arity`, `complete_classrels`, `complete_arities` (they change the algebra
   the rules consult, and build class proofs), `solve_constraints` (ML can fail; the model
   cannot), `future`, `name_derivation`/`close_derivation`, `add_oracle`, the ctyp operations,
   `renamed_term`, `trim_context`. Most are harmless bookkeeping; `certify`, `match` and the
   class machinery are logically relevant.

## 5. Is it too complicated?

About 146,000 lines, 55,000 of them in `Thm_Correctness`, for about 2,500 lines of `thm.ML`.
The models themselves (5,600 lines for `thm.ML`) read like the ML and are fine. The weight is
elsewhere:

- Three descriptions of every rule: the model on `thm_rep`, the lifted operation on `thm_data`,
  and the wrapper on `Thm`. Only the first is tested, only the second is proved, only the third
  runs.
- Soundness is interleaved with two kinds of proof terms, lazy sequences, exception messages and
  constraints. A reader who only wants "the rules are sound" must read through `zinv`, `znolb`,
  `zhyps_ok`, `prf_nolb`.
- `sign` has seven fields, four of them free parameters (`sg_close`, `sg_tyargs`, `sg_ax`,
  `sg_ar`) with no link to a theory.
- Side conditions are spread over 12 theories as boolean guards rather than visible premises.

The semantics, the proof judgment and the unifier results are not over-complicated for what they
do. The lifting layer is.

## 6. What was run, and what was not

Run and confirmed:

- Build of `Thm_Correctness` (11:05); `thm_oracles` of 21 main theorems; axioms of the session
  are definitional only; Nitpick model of `wf_algebra`.
- Real kernel: two types for one variable (G1); tight proof of `combination` (2.7); proofs of
  `False` in examples 04 and 05.
- Batch build: truncation and missing sorts in `\<^make_string>` (3.3).
- Patched Isabelle: build of Pure and HOL; all example theories; patch 10 with a repaired
  example (3.4); the differential tests, partly adjusted (3.5).
- Installed Isabelle: the differential tests as shipped (3.5).
- `generated/thm.ML` is reproduced byte for byte by the splice of `make_thm_ML` from the release
  and the generated part of the checked-in file (run by a sub-agent; whether that generated part
  is current with the theories was not checked).

Not done:

- The comparison of models with ML is by reading (by sub-agents, with the main claims re-checked
  by me), not by execution. Parts of `Pure_ZTerm` (`map_insts`, `beta_norm_prooft`) and the
  code printing of tables were not compared.
- `Thm_Model_ZFC` was read, not built. HOL was not built with `generated/thm.ML`.
- No run of the tests with a stronger comparison. With `ML_print_depth=100000` the suite
  exhausts the ML heap, so strings are not a workable way to compare in full; this needs C1.
- `Pure_Rules_Test` and `Pure_Unify_Test` on the patched system beyond their first assertion.
- No mutation of a model to measure what the tests detect (C6).

## 7. Plan

Ordered by what most improves the right to make the claim.

### A. Say exactly what is proved (small, first)

- A1. One inductive predicate `derivable c th` on `thm_data`, with one introduction rule per
  kernel rule, whose premises are the model's `okT` and nothing the kernel does not check; one
  theorem `derivable c th ⟹ thm_ok th`. Every guard of 2.2 then appears as a visible premise or
  disappears. Keep `pure_thm` as an implementation device if convenient.
- A2. Rewrite the README claims from that theorem: list the assumptions on the signature, the
  scope (Section 4, item 7), and the three kinds of evidence (proved / tested / read).
- A3. Fix `env_sorts` to the type environment, so that the lifted record is the ML record.
- A4. Export `thm_cons` (indeed `thm_inv`) of the results of the sequence rules and of `axiom`.

### B. Close the coverage gaps

- B1 (G1). Prove the sequence rules without name consistency. The model of `Envir.lookup`
  already raises on a type clash; replace `vcons` in `sinv` by "a clash raises", and show that a
  result, when there is one, is an instance. If that stalls, propose a kernel patch that makes
  the invariant true, and say so in the README until then.
- B2 (G2, G3). Binary rules over signatures related by `sign_le`, as `join_certificate` does;
  transfer for cterms and ctyps; make `zprf_decl` an invariant of the tight proof or remove the
  need for it.
- B3 (G4). State soundness per result (`brresult`, `aresult`, `fresult` are already there) and
  derive the list versions from it.
- B4 (G5–G8). Put finiteness and `sort_ok` of sorts into the invariants of `pure_cterm` and
  `pure_thm`; drop or justify the index condition of `instantiate`; make `ax_ok` per axiom and
  without `vtcons`; decide for `unconstrainT` whether `vars_consistent` becomes a kernel check
  (the present failure is `BAD_INST`, not unsoundness).
- B5. Termination and completeness for `bicompose_thms`, or state that they are not claimed.

### C. Make the tests carry the weight put on them

- C1. Compare with `=` on terms, types (with sorts) and proofs. Assert the number of cases run
  and the number with results.
- C2. Build the fully patched Isabelle in a script (it takes 5 minutes) and run the suite with
  `Thm`, `Proofterm`, `ZTerm`, `Unify`, `Pattern` of that system as the reference, without
  emulations. This is item H1 of CLEANUP_PLAN; it should come first, not last. Section 3.5 lists
  the four places that have to change; the assertions that the release has the old behaviour
  belong in a separate session that runs on the release.
- C3. One example per patch that fails on the release and passes with the patch, run on both.
  Repair `Unpatched_10` (build the state at proof level 2). Add tests for patches 13 and 20.
- C4. Test the artifact: run the wrapper sections, compare hyps, shyps, constraints and both
  proofs of real inferences (`Thm.proof_of`, `Thm.zproof_of`).
- C5. Inputs with flex-flex pairs, hypotheses, sort constraints, non-normal terms; whole
  sequences where they are finite.
- C6. Mutation check: change one condition in a model (an eigenvariable check, an `aconv`) and
  confirm that a test fails. This measures the suite instead of trusting it.

### D. Tight proofs

- D1. Patch 25: `ZTerm.combination_proof` with the argument type. Example theory for it.
- D2. Strengthen `zvalid` so that the type instances of proof constants are checked
  (`zconst_tr` must use them), then re-prove the tight rules. D1 must fall out as a failing
  proof before the patch.
- D3. Non-ASCII names: either model strings as ML strings or state the restriction.

### E. Non-vacuity

- E1. Replace `typedecl algebra` and its constants by a record (class relation, arities,
  classes); interpret `pure_sig` for the algebra of Pure.
- E2. A concrete signature for Pure with `sign_eq`, `sign_closed`, `sign_axioms`, `is_prf_sig`
  proved, and a few derivations through the lifted operations (`A ⟹ A`, one resolution step, one
  equality chain) as a smoke test of the statements.

### F. Trusted base of the generated code

- F1. `pointer_eq`: specify it (for instance `pointer_eq x y ⟹ x = y`, as an unspecified
  constant with that one property) so that the generated code is the code of the definition.
- F2. Give `vt_dest` and friends a specification that the code printing can meet (sorted by
  key), or prove independence of the order where it is used.
- F3. Decide the status of `generated/thm.ML`. If it stays a test vehicle, say so; if it is
  meant to run, the garbage-collector crashes need an explanation first.

### G. Scope (later, and only if the claim is to include them)

- G1. Model `Sign.certify_term`/`certify_typ` and derive the invariant of `pure_cterm` from it.
- G2. `Thm.match`, `first_order_match`.
- G3. Class relations and arities: extension of the algebra and the proofs of `of_sort`.

### H. Simplification

Agrees with CLEANUP_PLAN where they overlap; two additions from this audit:

- H1. Separate the soundness core from proof terms: a small development (models, semantics,
  `derivable`, validity) that can be read on its own, and a second one for classic and tight
  proofs on top. Today a reader cannot check the first without the second.
- H2. One description per rule that is tested, proved and run. With A1 the lifted layer shrinks
  to the inductive definition; with C4 the wrapper is what is tested.

## 8. Execution of the plan

Status of each item of Section 7 after the execution. "Checked" means: processed by Isabelle in
this run, on the installed system unless stated otherwise.

Test runs with the new comparison (C1), installed system (release + 07 + 08):

- `Pure_Pattern`: 189,749 unification and 112,369 matching problems, no mismatch.
- `Pure_Unify`: 1,698 problems, no mismatch with the reference.
- `Pure_Thm_Test` (8 min 24 s): 126 comparisons, 266,848 problems, 266,800 run (48 timeouts of the
  original), 208,456 with results, 28,709 with exceptions, no mismatch; 208 outcomes above 2 MB
  were compared on their first 1000 characters only (198 of them in `elim-resolution`).
  Two comparisons of Isabelle2026 with the emulated fixes report the expected differences (51 of
  969 and 8 of 348) and are not part of the check on the release.
- The first run of the new checks found two tests without content: `composition (match, no
  flattening)` had no problem with a result, and `bicompose_proof (composition, no flattening)`
  had no problem at all (the zero-case line of 3.5). Both now get problems that match (a
  theorem against the proof state of its own proposition): 300 and 100 with results.
- The exact comparison needs a bound: the text of a few terms of HOL is larger than the heap
  (shared types), and two resolution problems make the unifier of both sides run into the
  timeout while allocating at a rate that exhausted the heap of the session. The text is
  therefore hashed above 64 KB and cut above 2 MB, and a problem on which the original times out
  is not given to the generated code.

Fully patched system (`patches/test_patched`: copy of the installed system, all 25 patches, Pure
and HOL rebuilt in 5 min 51 s), the same sources, no emulation of fixes:

- `Pure_Pattern`, `Pure_Unify` and `Pure_Thm_Test` (7 min 36 s) pass: 914,840 problems in 138
  comparisons over the three sessions, no mismatch in any comparison that is checked.
- The patched `Unify.hounifiers` agrees with the model on all 1,698 problems (on the release:
  484 differences, as intended by patches 02–05).
- `Thm.biresolution` with patch 09 skips no rule with results (0 of 5,985 problems).
- The tight proof of the inference `Thm.combination` agrees with the model (2,844 problems;
  on the release the test asserts that they differ, which is patch 25).
- 23 example theories (01–05, 07–19, 21–25) fail on the patched system as they should;
  `Unpatched_Box_Instances` and `Unpatched_Incremented` pass on both, as documented. There was
  no example for patches 06 (an adaptation of ZF) and 20 in that run.

`patches/apply` now recognizes the patches that a tree already has by reverting them from the
last to the first on a copy (a patch does not revert cleanly while later patches of the same
file are in place), so the script works on the release, on the installed system and on a
patched tree.

### A. Say exactly what is proved

- **A1 — done.** `Thm_Correctness/Thm_Derivable.thy`: `inductive derivable :: thm_data ⇒ bool`
  with 38 rules, one per result of a kernel rule; the conclusion of each rule is the record
  that the lifted operation builds (proved equal through `rep_thm` of the lifted operation, not
  restated by hand); `theorem derivable_sound: derivable d ⟹ dok TYPE('u) d`, and the
  corollaries `derivable_valid`, `derivable_proofs`, `derivable_consistent`. All guards of
  Section 2.2 are now premises of rules or gone. `pure_thm` remains underneath as the device
  of the proofs.
- **A2 — done.** README, section "The rules of `thm.ML`: what is proved, what is tested, what
  is read".
- **A3 — done.** `env_sorts env = tyenv_sorts (tyenv env)` (`Thm_Type.thy`), as
  `Envir.insert_sorts`.
- **A4 — done on data.** `data_cons_assumption`, `data_cons_flexflex_rule`,
  `data_cons_bicompose`, `data_cons_biresolution`, `data_cons_axiom` in `Thm_Derivable.thy`:
  the results of the rules that unify, and axioms, have consistent variable names again.

### B. Coverage gaps

- **B1 — not done.** The sequence rules still assume name consistency (`data_cons`); it is a
  visible premise of four rules of `derivable`, and the README says that Isabelle does not
  maintain it. This remains the largest gap between the statement and the kernel.
- **B2 — not done.** Binary rules require equal signatures; `transfer` has the side condition
  `transfer_ok`.
- **B3 — done** with A1: `derivable` has one rule per result (`aresult`, `fresult`, `bresult`,
  `brresult`), not per list of results.
- **B4 — not done.** `strip_shyps` and `unconstrainT` take finiteness and `sort_ok` of the sort
  hypotheses as premises; `instantiate` keeps the index condition; `ax_ok` is unchanged.
- **B5 — stated as not claimed** (README): termination and completeness are proved for
  `bicompose_aux` and `biresolution`, not for `derivable`.

### C. Tests

- **C1 — done.** `Pure_Pattern/Pure_Test_Support.thy`: outcomes are written in full (all types
  and sorts, bound names, both proofs); above 64 KB a 64-bit hash of the text stands for it,
  above 2 MB its first 1000 characters (counted as `large` in the reports). A test fails on a
  mismatch, on zero problems run, and on zero results other than exceptions (except tests of
  error cases, which are listed). All test theories use it.
- **C2 — done.** `Test_System.patched` probes patches 01, 03, 10 and 25 and fails if they
  disagree; the test theories select expectations with it and emulate fixes only on the
  release. `patches/test_patched` builds the patched system and runs the suite and the
  examples on it.
- **C3 — partly.** `Unpatched_10` repaired (state built at proof level 2). New example
  `Unpatched_25_ZTerm_Combination`. `patches/test_patched` runs each example on the patched
  system and expects failure. `Unpatched_20_ZTerm_Hidden` (added later) shows patch 20 on
  `ZTerm.norm_proof` itself, not through an inference; it passes on the installed system and
  raises `TERM` on the patched one. No new differential tests for patches 13 and 20.
- **C4 — partly.** `Pure_Rules_Test` compares the tight proof of the whole inference
  `Thm.combination` (the wrapper, not only `ZTerm.combination_proof`). No general comparison of
  hyps, shyps and constraints of wrappers.
- **C5 — not done.**
- **C6 — done, once.** Four conditions of the models were changed together and the suite was
  run against the changed code (then the change was reverted): the eigenvariable check of
  `forall_intr` removed (791 mismatches in the test `forall_intr`), the comparison of the
  premise in `implies_elim` removed (150 mismatches), `aeconv` replaced by `aconv` in
  `eq_assumption` (118 mismatches), the test that matching does not instantiate the proof
  state in `bicompose_aux` removed (2157, 176 and 929 mismatches in the three tests with
  matching). All four were detected. This is a sample, not a measure of coverage.

### D. Tight proofs

- **D1 — done.** `patches/25-zterm-combination.patch`; model `combination_data` returns the
  argument type; proofs adapted; `Unpatched_25_ZTerm_Combination.thy`.
- **D2 — not done.** `zvalid` still does not look at the type instances of the proof constants
  of the equality axioms. D1 was therefore not found by a failing proof, and other defects of
  this kind would not be either.
- **D3 — not done** (non-ASCII names).

### E. Non-vacuity

- **E1 — done.** `datatype algebra = Algebra (class_less) (arities) (classes)` in
  `Pure_Envir.thy` replaces the `typedecl` and its unspecified constants.
- **E2 — done except for resolution and axioms.** `Thm_Correctness/Thm_Example.thy`: the
  signature `pure0` with proofs of `pure_sig`, `is_prf_sig`, `sign_eq`, `sign_closed`;
  derivations of `A ⟹ A` and `f A ≡ f A` with explicit classic proofs, existing tight proofs,
  and the proof judgments for them (`thAA_proofs`, `th_comb_proofs`). `Thm_Model_ZFC`:
  `zfc_model_pure0`, `pure0_consistent`. No derivation with a resolution step; `pure0` has no
  axioms in `sg_axioms`, so `sign_axioms` is not exhibited.

### F. Trusted base

- **F1 — done.** `pointer_eq x y ⟷ x = y ∧ same_object x y` with an unspecified `same_object`;
  the proofs use only `pointer_eq x y ⟹ x = y`.
- **F2, F3 — not done.**

### G. Scope, H. Simplification

- Not done. H2 is partly achieved by A1 (the statement is one inductive definition).

### What the claim is now, and what is still open

The claim that can be made: the 38 results of kernel rules covered by `derivable` are valid in
every model of the signature and carry valid proofs, for the models of the rules in HOL, under
side conditions that are all visible in one inductive definition and that are satisfiable
together (`Thm_Example`, `Thm_Model_ZFC`); and the models agree with the patched ML functions on
about 915,000 test problems under a comparison of complete outcomes, by a suite that detected
four of four seeded errors.

Still open, in the order in which they limit the claim "no proof of `False` from `thm.ML`":

1. B1: the rules that unify are covered only for arguments with consistent variable names.
2. The link between models and ML is testing and reading, not proof; D2 (the judgment of tight
   proofs ignores the type instances of the equality axioms) shows that a model and its proof
   can both be wrong in the same way.
3. Scope (Section 4): certification, `Thm.match`, extension of signatures, oracles, the
   derivation bookkeeping.
4. B2, B4: signatures of binary rules; side conditions on sort hypotheses and on `instantiate`.
5. C4, C5: the wrappers of `thm.ML` are compared only through the rules that the tests call;
   no tests on inputs with sort constraints, hypotheses and flex-flex pairs beyond those that
   the theorems of HOL and the few synthetic states provide.

Final state of this run, installed system: all eleven sessions (`Nipkow_Grobauer_Pattern`,
`Pure_Lambda`, `Pure_Pattern`, `Pattern_Correctness`, `Pure_Unify`, `Unify_Correctness`,
`Pure_Thm`, `Pure_Thm_Test`, `Thm_Correctness`, `Unpatched_Examples`, `Thm_Model_ZFC`) build from
the committed sources (`Thm_Correctness` in 8 min 50 s, `Pure_Thm_Test` in 8 min 32 s).
`generated/thm.ML` was regenerated; it differs from the previous file only in the argument of
`zcombination_proof` (D1). `generated/pattern.ML` and `generated/unify.ML` are unchanged. HOL was
not built with the generated files in this run.

### Additions after the first execution

- **C4 — done for the logical content.** `patches/test_generated` builds Pure and HOL with the
  generated `pattern.ML`, `unify.ML` and `thm.ML` (64-bit Poly/ML, two threads, 11 min 26 s)
  and compares a hash value of every theorem of HOL in full (session `Kernel_Digest`: 29,151
  facts; proposition with types and sorts, flex-flex pairs, hypotheses, sort hypotheses,
  maximal index) with the patched system: all equal. The installed system has the same values
  too, so the comparison says that the generated kernel reproduces HOL, not that it tells the
  patches apart; that is what the examples do (all 24 fail with the generated kernel). This
  also settles the open question of Section 6: HOL builds with `generated/thm.ML`. The first
  two attempts were killed for lack of memory (64-bit Poly/ML with a 10 GB heap, and then a
  second build started by me in parallel); the build that ran alone with an 8 GB heap went
  through. No crash of Poly/ML was seen, but the default 32-bit platform was not tried (F3).
- **D2 — not done in the proofs, covered by a test.** Session `Pure_Kernel_Check`: a checker of
  tight proofs in ML that is independent of the models and uses the type instances of proof
  constants. On about 10,250 theorems derived by 30 kernel rules from oracle copies of
  propositions of HOL: 1,328 tight proofs fail on the release (all of `forall_intr`, `forall_elim`,
  `abstract_rule`, `combination`; 20 of 300 of `lift_rule`, 14 of 191 of resolution, 50 of 180
  of elim-resolution), none on the patched system, none with the generated kernel. The failure
  of `combination` is reported as "instance of a variable of a proof constant of another
  type", which is the defect of patch 25. Changing `zvalid` itself so that the old model fails
  its proof would touch every lemma on the translation of proof constants (49 uses of
  `zconst_tr` in 12 theories) and was not attempted.
- **C3.** `Unpatched_20_ZTerm_Hidden` added (the function on its own).
- **E2, resolution step — dropped.** The premises of the unifying rules that concern the
  signature are satisfied by `pure0` trivially (`cfg_alg`, `data_cons` of theorems without
  variables); that the models have results is what the differential tests show (5,884
  resolution problems with results). An evaluation of the unifier inside HOL for one example
  would add little.
- **B1 — probed by the checker.** `Pure_Kernel_Check` also applies resolution and `assumption`
  to 156 theorems with a schematic variable at two types (made by `Thm.instantiate`), as
  states and as rules: on the patched system and with the generated kernel, the 225 results
  (78 + 17 + 130) all have tight proofs that the independent checker accepts. So in these
  cases the result follows from the premises, as the informal argument says; the statement
  about the models still excludes them.
- **B1 — assessed, not done.** Dropping name consistency means redoing the invariants of the
  unifier (`Pattern_Correctness`, `Unify_Correctness`) and of `bicompose_aux`, where
  environments are keyed by names and the correspondence with substitutions keyed by name and
  type rests on consistency. A reduction by renaming needs the same invariance of every
  function. It stays the largest gap.

- **G2 — done.** `Thm.match` and `Thm.first_order_match` are kernel code: `gen_match` builds
  `Ctyp` and `Cterm` records from the bindings of `Pattern.match` with the maximal index of the
  object and the union of the sorts, and `Thm.instantiate` trusts them.
  `Thm_Correctness/Match_Range.thy` proves a range invariant of the bindings by two inductions
  over `fo_mtch` and `mtch` (`match_range`), and `Thm_Match.thy` derives `match_cterms_ok`:
  the records are `ctyp_ok` and `cterm_ok`, and the instantiated variables have indices other
  than `-1`. Assumptions: a well-formed signature, two `cterm_ok` terms of the same signature
  (the ML code joins the certificates), and that each of the two records the sorts of its term
  (`tm_sorts t ⊆ cd_sorts`), which `cterm_ok` does not include (B4). The records of `gen_match`
  are written out in the statement; there is no model of the wrapper and no generated code
  for it. `Pure_Kernel_Check/Match_Check.thy` checks the same properties at run time on the
  running kernel: 15,747 problems, 6,386 matches, no defect.

### Additions after the second execution

- **A new defect, from B4 (patch 26).** The rule `instantiate` of `derivable` had the premise
  that no instantiated variable has index `-1`. Nothing in `thm.ML` checks this, so I tried
  it on the kernel: `Thm.instantiate` with the key `(("x", ~1), nat)` and the term `0` on the
  theorem `x ≡ x` (free `x`) returns the theorem unchanged, and its tight proof now proves
  `0 ≡ 0`, because tight terms write the free variable `x` as the variable `x` of index `-1`
  and `ZTerm.instantiate_proof` instantiates it; likewise for a free type variable. The
  theorem and its tight proof then disagree. `patches/26-thm-instantiate-index.patch` rejects
  keys of negative index in `prep_insts` (`THM`, and `CTERM` for `instantiate_cterm`); such
  variables do not occur in certified terms (`Certify_Check`, below). The models have the
  check (`check_inst_idx`), the premise is removed from `derivable.instantiate`
  (`instantiate_shape` derives the indices from the success of the model), and
  `Unpatched_26_Thm_Instantiate_Index` shows the defect. Differential tests: 440 + 8
  instantiations with such keys; on the release every one is a mismatch (Isabelle returns the
  theorem, the model raises), with the patch none.
- **B4 — finiteness done, `sort_ok` not.** The rules of `derivable` that take certified terms
  and types now require that these record finitely many sorts (they are lists in ML), and
  `derivable_finite_shyps` proves by induction over `derivable` that derivable data over a
  well-formed signature have finitely many sort hypotheses. `strip_shyps` and `unconstrainT`
  lost their finiteness premise. The premise of `strip_shyps` that the sort hypotheses are
  sorts over the classes of the signature remains: as an invariant it needs that the unifiers
  put only such sorts into their type environments, which is not among the proved properties
  of `Type.unify` in `Pattern_Correctness`.
- **F2 — done.** `vt_dest`, `zv_dest` and `zt_dest` were defined with `SOME`, as some list with
  distinct keys and the entries of the table, while the generated code calls `Vartab.dest`,
  `ZVars.dest` and `ZTVars.dest`. They are now constants introduced by `specification` with
  exactly that property (existence proved), so nothing can be proved of them that the ML
  functions do not satisfy, such as a relation between the lists of two equal tables written
  differently. No proof needed more than the specification.
- **G1 — tested, not modelled.** A model of `Sign.certify_term` (expansion of abbreviations,
  type checking, the checks of `Type.cert_typ`) with a proof that its results satisfy
  `cterm_ok` was not written. `Pure_Kernel_Check/Certify_Check.thy` tests that statement on
  the running system with a checker that follows the definition of `cterm_ok`: 6,000
  propositions, 11,617 closed subterms and 2,878 types of theorems of HOL are certified
  unchanged and pass; 15 groups of 1,500 terms or types with one violation each are rejected
  by certification and by the checker alike (none is certified); a sort with redundant
  classes is certified as it is, a type abbreviation is expanded, and a constant at an
  instance outside the sorts of its declared type is certified, all with results that pass
  the checker. The last point is as in the model (`const_typ_ok` asks for an instance, not
  for a well-sorted one). No term was accepted by the checker and rejected by certification.
- **B1 — measured; a check in the kernel is ruled out.** A copy of the patched kernel with a
  probe in `bicompose_aux`, `assumption` and `flexflex_rule` logged, while building HOL
  (between 30 and 40 million calls), the arguments in which a schematic variable name has two
  types or a type variable name two sorts: between 2,048 and 4,095 compositions with an
  incremented rule where state and rule clash, between 32 and 63 compositions whose rule
  clashes by itself (a rule with `?P1` at two types), between 8 and 15 resolutions whose
  lifted state clashes (`?k0` at two types); none in `assumption` and `flexflex_rule`, and
  none in rules lifted by `biresolution`. So HOL itself leaves the fragment that
  `derivable_sound` covers, a patch that raises an exception on such arguments would break
  the build, and only a proof without `data_cons` closes the gap. I counted what that
  touches: the consistency predicates are used about 170 times in 36 theories, down to the
  correctness of the unifier. Not attempted. The evidence for the excluded case is now:
  5,445 differential problems with a variable at two types and 1,597 compositions with
  identified names, without a mismatch, and the 225 tight proofs that the independent
  checker accepts.
- **C5, D3 — done as tests.** Nine groups in `Pure_Bicompose_Test` (17,049 problems, no
  mismatch on the release): a variable at two types (resolution 3,634, elim-resolution 1,811),
  composition with an incremented rule (1,597), terms with β-redexes (2,603), states with
  flex-flex pairs (695) and with hypotheses (1,146), names with bytes above 127 (3,039 and
  1,024), and sequences of up to 30 results (1,500).
- **B2 — not done.** The binary rules of `derivable` still require equal signatures, and
  `transfer` still has the premise that the tight proof mentions only declared constants
  (`zprf_decl`). The invariant of tight proofs (`zinv`) is about indices and canonical types
  and does not say that constants are declared; making it say so means a new clause in the
  proof of each of the 38 rules.
- **D2 — unchanged.** The judgment `zvalid` still ignores the type instances of proof
  constants; the independent checker of `Pure_Kernel_Check` is what looks at them.
- **G3, H — not done.** No model of the extension of signatures; no restructuring. With the
  premises removed in this round, `derivable` has these premises that the code does not
  check: equal signatures, `sign_eq`/`sign_closed`/`sign_axioms`, `data_cons`/`data_cons2`,
  `transfer_ok`, `unc_ok`, `sort_ok` for `strip_shyps`, finite sorts of certified terms.

State after this round, from the committed sources.

- Installed system (release with patches 07 and 08): the 13 sessions build
  (`Thm_Correctness` in 7 min 57 s, `Pure_Thm_Test` in 8 min 55 s, `Thm_Model_ZFC` with the
  AFP). Differential tests: 933,922 problems over `Pure_Pattern`, `Pure_Unify` and
  `Pure_Thm_Test`; no mismatch in a checked comparison, and the 448 instantiations with a key
  of index `-1` all differ, as asserted for the release.
- Fully patched system (all 26 patches; Pure and HOL rebuilt, HOL in 5 min 2 s, so nothing in
  HOL instantiates a variable of negative index): 933,581 problems in 150 comparisons, no
  mismatch in a checked comparison (the two comparisons that report differences compare the
  release with emulated fixes and two settings of the unifier, by design); the 448
  instantiations raise the same exception on both sides. `Pure_Kernel_Check`: 10,244 tight
  proofs, no failure; `Thm.match` and the certification check without defects. All 25 example
  theories that show a defect fail; the two others pass, as documented.
- Generated kernel (`patches/test_generated`: the generated `pattern.ML`, `unify.ML`, `thm.ML`
  in the patched system, 64-bit Poly/ML, two threads): HOL builds in 11 min 35 s, and the
  digests of its 29,151 theorems are those of the patched and of the installed system. The 25
  examples fail, the 10,244 tight proofs check, and the checks of `Thm.match` and of
  certification have no defect. **F3 stays open, and got worse:** the first run of this round
  used the default four threads and Poly/ML died with a segmentation fault 13 minutes into the
  build of HOL (a read of an unmapped address, according to the kernel log, which has no
  out-of-memory kill at that time). With two threads, as in the earlier round, the
  build goes through. The script now fixes two threads. I have no explanation: the generated
  code and the wrapper use no unsafe primitive, so this points at the runtime system under the
  allocation pattern of the generated code (deep recursion on the stack, no sharing), but
  that is a guess. Until it is explained, `generated/thm.ML` is a test vehicle and not a
  kernel to run.

### Additions after the third execution

- **G1 — modelled and proved, with two parts left out.** `Pure_Thm/Pure_Certify.thy` models
  what stands behind `Thm.global_cterm_of` and `Thm.global_ctyp_of`: `Type.certify_typ` in the
  default mode (declared type constructors with their number of arguments, expansion of type
  abbreviations by `inst_typ`, nonterminals and syntactic types rejected, classes of sorts
  declared, no type variable of negative index), `check_vars` and `type_check` of `sign.ML`,
  `Type.raw_match` for `Type.raw_instance` in `Consts.certify`, and the maximal index and
  sorts that `thm.ML` records. `Thm_Correctness/Certify_Correct.thy` proves
  `global_cterm_of_ok` and `global_ctyp_of_ok`: the results satisfy `cterm_ok` and `ctyp_ok`,
  their sorts are finite and are the sorts of the term. So the premises of `derivable` on
  certified terms and types are now derived from a model of the code and no longer assumed
  outright. What is assumed instead is about the signature: `tsig_ok` (the declared number of
  arguments is the arity; the right-hand side of a type abbreviation is a certified type
  without schematic type variables) and `consts_ok` (type schemes without free type
  variables). The example signature satisfies both, and the certified term of the example
  derivations is the result of the model (`global_cterm_of_A0`).
  Not modelled: the expansion of term abbreviations in `Consts.certify` (`expand_term` with
  `Envir.expand_atom` and `Term.betapplys`; the model returns no result for a term that has
  an abbreviation), and `Soft_Type_System.global_purge` (the identity unless a theory installs
  a soft type system; no file of the Isabelle2026 distribution outside `Pure` calls
  `Soft_Type_System.setup`, the AFP was not searched).
  Read, not proved: that `could_match` in `raw_instance` is a filter for `raw_match`, and
  that the second certification of the types in `Consts.certify` changes nothing.
- **Its differential test, and what a mutation check found.** `Pure_Certify_Test` compares the
  generated code with `Sign.certify_term`, `Thm.global_cterm_of` and `Thm.global_ctyp_of`
  (result with types, maximal index and sorts; an exception against no result). Five errors
  seeded into the model: no index check for type variables, no check of the argument type in
  `typ_of`, a type variable matched against two types in `raw_match`, qualified names of free
  variables accepted, and parameters of type abbreviations replaced at any sort. The first,
  third and fourth were reported at once. The second passed: my group "an argument of another
  type" applied a term that is no function, so no input had a function applied to an argument
  of the wrong type. I added that group (to this test and to `Certify_Check`), and the error
  is reported. The fifth cannot be seen on a signature of Isabelle, where the right-hand
  sides of type abbreviations have their sorts stripped; the model keeps the condition
  because the code has it.
- **B2 — looked at again, still open.** I checked whether the premise of `transfer` on the
  tight proof (its terms mention only declared constants) follows from the validity of the
  proof, which would need one lemma instead of one per rule. It does not: the proof judgment
  relates the term annotations of a proof to the well-typed terms of the derivation only up
  to conversion of erased terms (`ann_ok`), so an annotation may contain a constant that the
  well-typed term does not. The premise needs an invariant of its own over all 38 rules.

State after the third round, from the committed sources: the 13 sessions build on the
installed system (`Thm_Correctness` with `Certify_Correct` in 8 min 11 s). Differential tests:
1,039,670 problems on the installed system and 1,039,695 on the system with all 26 patches, of
which 106,114 are for certification (50 comparisons, no mismatch on either system). On the patched
system no checked comparison has a mismatch, all 25 defect examples fail, and
`Pure_Kernel_Check` has no failure. With the generated kernel (two threads) the theorems of HOL
are again those of the patched system, the examples fail and the kernel checks pass.

- **B4 — done.** The premise of `strip_shyps` that the sort hypotheses are sorts over the
  classes of the signature is gone. The rules of `derivable` that take certified terms and
  types now require `csorts_ok` of their sorts (finitely many, over the classes of the
  signature), which `global_cterm_of_ok` and `global_ctyp_of_ok` prove of the results of the
  model of certification. `derivable_inv` proves soundness and `shyps_ok` (the same property
  of the sort hypotheses) by one induction, since each needs the other: `strip_shyps` needs
  the sorts for its soundness, and the rules that unify need the well-formedness of their
  arguments for their sorts. For those four rules the fact was already in the unifier proofs:
  the invariant `einv` of `Pattern_Correctness` contains `scert` (the types bound in the type
  environment have certified sorts). It is now exported (`sorts_ok_thm_of_ares`,
  `sorts_ok_thm_of_fres`, `sorts_ok_thm_of_bc`, and through `bres_inv` for `biresolution`).
  For `strip_shyps`, `sorts_ok_strip_shyps` shows that the remaining sorts are sorts of the
  atomic types of the theorem or minimized sorts of the old hypotheses. With this and the
  earlier rounds, the premises of `derivable` that the code does not check are: equal
  signatures of the arguments, `sign_eq`/`sign_closed`/`sign_axioms`, `data_cons`/`data_cons2`,
  `transfer_ok` and `unc_ok`; `cterm_ok`, `ctyp_ok` and `csorts_ok` of the certified inputs
  follow from the model of certification under `tsig_ok` and `consts_ok`.

### Additions after the fourth execution (proofs)

- **B2 — done.** `derivable.transfer` has the premise `sign_le (th_sign th) c'` only; the
  condition that the tight proof mentions only declared constants (`transfer_ok`, `zprf_decl`)
  is gone. The earlier attempt to derive that condition from validity failed for a good
  reason (annotations are compared up to erasure), and the same fact is what makes the
  condition unnecessary: `zvalid_ext` shows that a valid tight proof stays valid in an
  extension. The two decodings of a tight proof differ only in the types of constants that
  the smaller signature does not declare. In hypotheses there are none, because the hypotheses
  of a valid proof are hypotheses of the theorem, which are well-typed (`prf_valid_hyps`). In
  the propositions of proof constants there are none, because these are atoms of the proof
  judgment (`prf_valid_atoms`), and `sign_le` now requires that the propositions of atoms
  mention only declared constants. That is one new assumption on the signature in place of
  one on every theorem; Isabelle certifies the propositions of axioms and of theorems before
  they become proof constants. In annotations (`AbsP`, `PAppt`) they may occur, and there the
  proof judgment erases the types of constants (`prf_teq`, `prf_teq_aeq`, with the existing
  `prf_valid_aeq`). The witness of validity keeps its class proofs (`prf_teq_reclass`).
  Premises of `derivable` that the code does not check, now: equal signatures of the arguments
  of binary rules (or `transfer` to a common extension), `sign_eq`/`sign_closed`/`sign_axioms`,
  `data_cons`/`data_cons2`, and `unc_ok`.
- **`unconstrainT`.** Its condition had a clause that the sort hypotheses are sorts over the
  classes of the signature. With `derivable_inv` this is an invariant, and the rule now has
  `unc_sig_ok` without it.
- **Extensions keep the conditions on the signature.** `sign_eq_transfer` and
  `sign_closed_transfer`: after `transfer`, the rules that need `sign_eq` or `sign_closed`
  need no new assumption.
- **B1 — what the proofs already cover, and a patch that does not work.** Reading the
  low-level theorem again (`bicompose_aux_rchar`, `call_env` in `Bicompose_Correct.thy`): it
  needs one type per variable name only for `incremented = True`. Without that flag the kernel
  first unifies the types of the variables of the same name (`unify_var_types`), and the proof
  works with consistency under the solutions of the type environment (`vcons`). Only the
  layers above (`bicompose_aux_thm_inv`, `thm_ok_thm_of_bc`, `derivable`) ask for syntactic
  consistency throughout, and reduce the case without the flag to the case with it. So the
  natural patch is to call `unify_var_types` always, also in `assumption` and
  `flexflex_rule`: then the kernel itself would establish what the proofs need, and an
  argument whose types of a name do not unify would give no result. I tried it on a copy of
  the patched kernel. HOL does not build: `code_reflect` in `Code_Numeral.thy` resolves on a
  proof state in which `?k` occurs at the types `num` and `integer`, which do not unify, and
  with the change that resolution has no result. Before that point the build went through
  more than 1,024 compositions with the flag `incremented` in which a name had two types, and
  in all of them the types unified. So Isabelle uses both readings of a name at two types:
  one variable whose types are to be unified (composition without the flag; Metis), and two
  variables (the code generator). A patch that enforces one of them breaks the other. What
  remains is the proof for the kernel as it is, in which a lookup at another type than the
  bound one raises `TYPE`; its invariant has to say that the environment, extended by retyped
  copies of its bindings for the variables that the unifier has treated as one, is a typed
  unifier. That is the refactoring counted before, not a patch.

### Additions after the fifth execution (proofs)

- **G1 — term abbreviations modelled and proved.** `Pure_Certify.thy` now has all of
  `Consts.certify {normalize = true}`: `need_expand`, `expand_term` (the recursion over
  `strip_comb` as a function with the expanded arguments as accumulator), `Envir.expand_atom`
  with `Envir.subst_term_types` and the sort check of `Type.lookup`, `Term.betapplys` for the
  right-hand side of an abbreviation, and the function `term` for terms without abbreviations
  (`certify_plain`), which certifies the types a second time. `raw_instance` has its filter
  `could_match`. `certify_term` no longer returns nothing for a term with an abbreviation.
  `Certify_Correct.thy`: the result of the expansion is closed (`expand_term_loose`), has the
  type of the term before the expansion (`expand_term_typing`, by subject reduction for the
  beta steps of `betapplys` and by the typing of type instances for `expand_atom`), has no
  variables but those of the term and only certified types with indices from 0
  (`expand_term_vars`); with that, `certify_term_wf` and `global_cterm_of_ok` hold for all
  terms. The two statements that I had only read are proved: `raw_instance_iff` (the filter
  `could_match` never rejects what `raw_match` accepts) and `certify_typ_idem` with
  `certify_plain_fix` (the second certification returns the term as it is).
- **What is assumed for it.** `abbrs_ok`: the right-hand side that the table has for an
  abbreviation is closed, has the type of the constant in every environment, and has no
  schematic variables and no type variable of negative index. The table of the model holds
  `normal_rhs`, which `Consts.abbreviate` computes by `Consts.certify` from a certified term
  without schematic variables. `abbrs_ok_update` shows that a table extended in this way
  satisfies `abbrs_ok` again, for a fresh constant; that `Consts.abbreviate` and
  `Sign.add_abbrev` extend it in this way is read from the code, they are not modelled.
  `tsig_ok` changed: the right-hand side of a type abbreviation that is not syntactic is a
  type that certification returns as it is (`typ_logical`: logical type constructors with
  their numbers of arguments, declared classes, indices from 0). `Type.add_abbrev` certifies
  the right-hand side and strips its sorts; this again is read, not modelled.
- **Its test.** `Pure_Certify_Test` on the installed system: 64 comparisons, 110,722 problems,
  no mismatch. New: abbreviations with and without arguments, with a bound variable as
  argument, nested, each of the 504 abbreviations of HOL at its declared type (all expanded to
  the same term by Isabelle and the model), and two groups that both reject (an abbreviation
  at a type that is no instance). The table of the right-hand sides is made with
  `Consts.certify` itself, because `consts.ML` does not export `normal_rhs`; so the test
  compares the expansion for a term, given the expansions of the right-hand sides.
  Not rerun: the patched system and the generated kernel (no patch and no generated file
  changed).
- **B1 — one more case that a proof would have to cover.** Reading `pattern.ML` for the
  layers that assume one type for each name: `Pattern.cases` compares the heads of a
  flex-flex pair by name only (`if F = G then flexflex1 …`) and binds the variable at the
  type of the left occurrence. A lookup at another type raises `TYPE`, but here no lookup
  happens. I ran this on the kernel (`Unpatched_Incremented.thy`, three assertions): for the
  state `?x ≡ (λu v. ?x v u) ⟹ ?x ≡ ?x` with `?x` at `'a ⇒ 'b ⇒ 'r` on the left of the premise
  and in the conclusion, and at `'b ⇒ 'a ⇒ 'r` on its right, resolution with reflexivity returns
  `(λu v. ?x') ≡ (λu v. ?x')`. The environment binds only the variable at the first type; the
  occurrence at the second type vanishes with the solved subgoal. The result is a consequence
  of the state (choose the same constant function for the variable at the second type; it
  occurs nowhere else), so this is no proof of anything false. But it is a result of the
  kernel for which the environment is not a unifier of the subgoal and the rule in the sense
  of the correctness proofs, and `derivable` excludes the state by `data_cons`. With the
  second occurrence also in the conclusion the kernel raises `TYPE`; with different numbers
  of arguments `Pattern.mk_ff_list` raises `Fail`, which leaves the kernel as an internal
  exception (the model has the same exception). So a proof without `data_cons` has to give
  the vanished occurrence a value of its own (a copy of the binding at the other type); it
  cannot be the existing proof with a weaker invariant. My argument that the kernel is sound
  on such states is this reading and the experiment, not a theorem.
- **B1 — done for `bicompose` without the flag `incremented`.** In that mode the code calls
  `unify_var_types` before it unifies: the types of the variables of one name in the state and
  the rule are unified, and there is no result if they do not unify. The theorem on the
  results (`bicompose_aux_rchar`) and the semantic theorem (`bicompose_aux_valid`) already
  took the consistency of the names only for `incremented = True`; the theorem that the
  results are theorems again (`bicompose_aux_thm_inv`) and the layers above it reduced the
  other case to it by assuming that the names are consistent, so that `unify_var_types` is
  the identity. Now `bicompose_aux_thm_inv_gen` (`Bicompose_Thm.thy`) is proved for both
  values of the flag, for arguments that satisfy the invariant without the condition on the
  names (`thm_inv0`); what it needed in addition is that the type variables that
  `unify_var_types` makes are new (`unify_var_types_einv`, fifth statement, `call_env_tvars`).
  The results have one type for each name in both cases. `Thm_Bicompose.thy` and the rule
  `bicompose` of `derivable` follow: its premises on names are now
  `data_scons2 st rule` (one sort for each name of a type variable of the two theorems) and
  `incremented ⟶ data_vcons2 st rule`. So for composition as `compose_tac` and `COMP` use it,
  a variable at two types is no longer outside the statement. What stays outside: the sorts
  of type variables for all four rules, and the types of variables for `assumption`,
  `flexflex_rule`, `biresolution` and `bicompose` with the flag, where the code does not unify
  the types and the case of the previous item occurs.
- **G3 — class relations and arities: the extension keeps the models.** `Thm.add_classrel` and
  `Thm.add_arity` are in `thm.ML`: they take a theorem `OFCLASS(?'a::c1, c2)` or
  `OFCLASS((?'a1::S1, …) t, c)`, check it with `plain_prop_of` (no hypotheses, no flex-flex
  pairs, no sort hypotheses beyond the sorts of the proposition) and add the class relation or
  arity to the algebra of the theory. After that every theorem has more type instances, and
  `derivable_sound` speaks of the models of the extended signature, so it needs that there
  still is one. New theory `Thm_Correctness/Thm_Classes.thy`:
  `classrel_sound` and `arity_sound` (the class relation or arity of such a theorem, if the
  theorem is valid in a model, holds in the model for all nonempty sets), `model_ext` and
  `is_model_alg` (a model is a model of a signature that differs in the algebra only, if the
  class relations and arities of that algebra hold in it), and from these
  `add_classrel_model` and `add_arity_model`: for a theorem that satisfies the invariant of
  theorems (`dok`, which `derivable_sound` gives) and the checks of `plain_prop_of`, a model of
  the signature is a model of the signature with the extended algebra, and the latter is an
  extension in the sense of `transfer` (`sign_le`).
- **Two statements had to change for it.** (1) The locale of models required class relations
  and arities to hold for every set of the universe, the empty one included. A theorem
  `OFCLASS(?'a::c1, c2)` says nothing about the empty set, since types are not empty, so no
  model in which `c1` contains the empty set and `c2` does not could ever be shown to remain a
  model. The assumptions `cls_le` and `cls_arity` of `pure_model` are now for nonempty sets.
  This weakens the assumptions of every theorem about models; seven proof steps needed the
  fact that the value of a type is not empty. (2) `alg_le` required that the extension has
  the arities of the algebra as they are. `Sorts.add_arities` replaces an arity `t :: (Ss') c`
  by `t :: (Ss) c` if `Ss'` is below `Ss` (function `insert` in `sorts.ML`), so the extension by
  an arity is not an extension in that sense. `alg_le` now asks for an arity with sorts that
  are not smaller; `has_sort_mono` needs the extended algebra to be well formed for that.
- **What is assumed.** `sorts.ML` is not modelled. `classrel_ext` and `arity_ext` say what I
  read in `Sorts.add_classrel` (with `rebuild_arities`) and `Sorts.add_arities` (with
  `complete` and `insert`): the classes stay; the class relation of the result is generated by
  the old one and the new pair, or is the old one; each arity of the result is an old arity,
  or has the sorts of an old or of the new arity at a class above. That the result is well
  formed (`pure_sig alg' ar`: no cycle, coregular arities) is an assumption too; the
  functions raise an error otherwise, but that is not proved. The class of the conclusion is
  assumed to be declared with its constant (`class_const`), and the axioms of the signature
  to be well-typed. The declaration of new classes, type constructors and constants is still
  outside.
- **One statement for the extensions.** `extends_by c0 c` (inductive, `Thm_Classes.thy`): `c` is
  reached from `c0` by declarations of constants (an extension with the same algebra and
  axioms) and by class relations and arities that derivable theorems of the current signature
  state. `extends_by_model`: a model of `c0` is a model of `c`. With `derivable_valid` and
  `derivable_consistent`: the derivable theorems of `c` are valid in the models of `c0`, and
  none of them is `⋀P. P` (without hypotheses and flex-flex pairs, sort hypotheses inhabited).
  This is the form in which the soundness theorem now covers a development that adds class
  relations and arities; before, it spoke about one fixed signature and its extensions by
  `transfer`, with the existence of a model of the extension as an assumption.
