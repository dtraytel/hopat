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
  `Unpatched_Box_Instances` and `Unpatched_Incremented` pass on both, as documented. There is
  no example for patches 06 (an adaptation of ZF) and 20.

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
  system and expects failure. No new tests for patches 13 and 20.
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
