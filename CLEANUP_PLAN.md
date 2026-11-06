# Cleanup plan (proposal for approval)

Guiding principle (Hoare): prefer the design that is so simple that there are
*obviously* no deficiencies, even if getting there is a large refactoring.
Size of the change is not a criterion; simplicity of the result is.

Every item below has an identifier (D = decision on the overall design,
S = streamlining, M = ML patch, T = Thm/proof layer, H = hygiene of models and
tests). Please mark each item *approve* / *reject* / *modify*. Items marked
**(rec.)** are my recommendation where there is a choice.

Numbers are measured on the current branch (`grep`, line counts). Counts of
uses are approximate.

---------------------------------------------------------------------------

## Decisions (from the discussion, 2026-11-02)

These override the recommendations further below where they differ.

* **Order.** Port rather than refactor:
  1. Build a new λ-library.
  2. Port Pattern, then Unify, then Thm, each polymorphic from the start and
     streamlined as it is written. The S-items happen during the port.
  3. Delete the dead monomorphic Unify chain first, to shrink the port.
  4. Patch work comes last: the patch text is written and tested at the end.
* **The model drives the patches.**
  * The current transcription standard is good enough.
  * If a patch changes shape (e.g. M1 `head_norm_dpair`, M2), the model of
    the patched function changes accordingly, when that function is ported.
  * The final patches must be exactly what the model says, and they target
    the **Isabelle2026 release**, so `thm-rename` stays a patch.
  * The differential tests run the release with the patches applied (H1).
* **`Seq` as data** stays for now. A codatatype of sequences (towards
  modelling tactics) may be reconsidered later.
* **Term layer: β/η directly on `pterm`** (D1′ replaces D1).
  * Bound-variable names and `Abs` types are inert labels; one α-rule
    matches `aconv`.
  * Side conditions should mostly be `0 ≤ lev` / `0 ≤ inc`, since Pure's
    operations already treat negative indices as inert. Switching `pterm` to
    `nat` is not planned: η-contraction needs negative increments, and
    mapping `nat` to ML `int` adds trusted `code_printing`.
  * **First step: a prototype** on `pterm` (the substitution and lifting
    lemmas, then CR of βη). I report back before the full port.
* **Prototype result (`thys/Pure_Lambda/Pure_Lambda.thy`).**
  * Confluence of β and confluence of η hold on all Pure terms. The side
    conditions are only `0 ≤ level`; no `proper` is needed.
  * βη is **not** confluent on Pure terms: the labels of abstractions block
    the critical pair `λa:T. (λb:U. b) a` (`beta_eta_not_confluent`).
  * Decision (option A): confluence of βη for well-typed terms, up to the
    names of bound variables (`confluent_beta_eta_unname`).
    * Church-style typing with an environment `integer ⇒ ptyp`.
    * Subject reduction for β and for η (via strengthening).
    * Confluence of the relations restricted to well-typed terms with empty
      binder names.
    * `unname`, with `aconv_term s t ⟷ unname s = unname t`.
* **Semantics.**
  * Unifiers are polymorphic: an arbitrary well-sorted type substitution and
    a term substitution, compared modulo βη on typed `pterm`.
  * Validity of theorems (ground versus polymorphic `holds`): **decided later**,
    when the Thm layer is ported.
* **Variables are identified by name and type** everywhere: terms,
  substitutions and the proof judgment (T1). That `Envir` looks variables up
  by name alone is an invariant of well-formed environments.
* **Scope.**
  * The monomorphic end theorems are dropped (no corollaries).
  * The arity-guessing extension stays **in the model only**: no patch, and
    model = patched code for bound 0.
  * `Nipkow_Grobauer_Pattern` stays as an independent session, no longer a
    dependency.
  * The classic proof terms stay in scope.
* **Risk.** If the polymorphic pattern core stalls, I stop and report the
  obstacle before any fallback.
* **README** is rewritten from scratch for the end state.

---------------------------------------------------------------------------

## 0. Target architecture in one paragraph

One typed, nameless λ-calculus library replaces the dependency on
`Nipkow_Grobauer_Pattern`. Pure terms are interpreted in it type-faithfully,
so that type instantiation commutes with β, η, substitution and `≡βη` by
construction, and unifiers are pairs (type substitution, term substitution)
compared modulo βη directly. Ground instances are no longer needed. On top
of it there is one polymorphic development per algorithm (no
monomorphic/polymorphic duplicates). There is one notion of environment
extension, one invariant per layer, one monad library, one proof judgment that
identifies variables by name *and* type, as Isabelle does, and one abstract
type of theorems carrying both kinds of proofs. The ML patches are the
smallest changes that express the verified models, use existing Pure
functions wherever possible, and are exactly what the differential tests run.

---------------------------------------------------------------------------

## 1. The term layer: drop the dependency on Nipkow–Grobauer terms (question 1)

### Findings

* **Nipkow's algorithm is not used at all.** No correctness session refers to
  `Unification.unify`, `unif_correct`, `cases_*`, `otfη_unifies`,
  `unify_None/Some` or anything in `Unif_Termination`. About 3k of the 10.7k
  lines of `Nipkow_Grobauer_Pattern` are therefore dead weight for the Pure
  developments. The rest is used as a λ-calculus library:
  * dB syntax, `Abs_m` and `°°`;
  * `lift`/`subst`, `mk_subst`, `closed_on`, `no_loose_bound`;
  * `≡βη` (about 900 sites), β and β-normal forms, and CR (`closure_confluent`,
    `normal_form_unique`, Facts 5, 6 and 8);
  * SN (`type_implies_termi*`) and typing (`⊢`, `typing`, `typed_on`);
  * `loose_BVars`/`map_BVars`;
  * the measure `ld` and `no_redex` from `Unif_Occurs`;
  * a few helpers (`idx`, `abst`, `unifies`).
* **The translation forces ground semantics.** `tr` (`Pattern_Semantics.thy:68`)
  turns constants and free variables into dB variables with an injective
  *code that includes the type* (`AConst a T`). Instantiating a type variable
  therefore renames atoms, so βη on dB cannot be "modulo θ".

  Everything else follows from that:
  * the ground core (`wf_env` demands `vt_is_empty (tyenv env)`, and
    `unify_types_ground` turns type unification into equality);
  * the machinery of ground, faithful and instance problems (`inst`/`instE`,
    `gsol`, `faithful_exists`, `hyp_faithful`, `has_type_reflect`, `cren`,
    `tresp`, `psat`, `penv_equiv_gsol`, `rigid_subst`);
  * the separate polymorphic soundness theorems (`Ok_psound`,
    `unifiers_psound`);
  * in the Thm layer, `gtinst`/`iext`/`sm ρ σ t = mk_subst σ (tr (inst ρ t))`.
* **Encoding overhead in the proofs:** `tr` about 2450 uses, `tau` about 1730,
  `proper` about 630, `code` about 550, `trty` about 550, `AVar` about 450,
  `rigid_subst` 134 and `cren` 79.
* The Thm layer uses only the basic layer (`≡βη`, `mk_subst`, `lift`,
  `subst`, `Abs_m`) and no Grobauer facts.

### D1. New library session `Typed_Lambda` (name to be chosen) **(rec.)**

* **The datatype.** One nameless datatype with natural-number indices and
  typed atoms and binders:

      datatype ('a, 'l) lt = BV nat | At 'a | Ap "('a,'l) lt" "('a,'l) lt" | Lm 'l "('a,'l) lt"

* **Its metatheory, with labels inert:**
  * `lift`, `subst`, untyped β, η, `≡βη` and CR;
  * β-normal and η-long forms;
  * the facts that are actually used (from `Lemmas`, `Unif_Prelims`,
    `Unif_Normal`, `Unif_Occurs`);
  * `ld`.

  Ported from HOL-Proofs-Lambda and NG, these proofs carry over almost
  verbatim because the labels play no role in reduction.
* **Typing.** A Church-style judgment, parameterised by the types of atoms
  (`At a` has type `ty a`).
* **SN.** It is obtained by erasure to Nipkow's simple types, so it is not
  re-proved.
* **A generic `map_lt`.** It acts on atoms and labels and commutes with
  `lift`, `subst`, β, η, `≡βη`, `mk_subst` and typing. This one lemma family
  replaces the faithful-instance arguments.
* **The instance for Pure.**
  * Atoms are `Const name typ | Free name typ | Var indexname typ`: Vars are
    keyed by name *and* type, see D4.
  * Labels are `typ`.
  * Substitutions act on `Var` atoms only, so constants and free variables are
    no longer substitutable dB variables, and `rigid_subst`, `cren` and
    `tresp` disappear.
* **The translation.** `tr` becomes a type-preserving bijection between proper
  Pure terms modulo bound-variable names (`aconv`) and `lt`, with
  `tr (inst θ t) = map_lt … (tr t)`.

  All semantic notions are *defined on Pure terms* (`s ≡βη t ⟷ tr s ≡βη tr t`,
  satisfaction and unifiers on `pterm`). Statements then read as
  statements about Pure terms, and `tr` appears only in the library-bridge
  theory.

* `Nipkow_Grobauer_Pattern` stops being a parent of any Pure session. Whether
  it stays in the repository as the standalone formalization of the thesis is
  your call: **D1a** keep it as an independent session, or **D1b** remove it.

**Alternative D1′:** develop β/η directly on `pterm`, with no carrier and no
`tr`.
* **Pro:** the model's own `subst_bound`/`incr_boundvars` are the
  metatheory's operations.
* **Con:** integer indices put `proper` side conditions everywhere, and CR and
  normal forms hold only up to `aconv`, so everything about bound names has
  to be redone.

I recommend D1 with the definitions stated on `pterm`, which gives the
reader-level simplicity of D1′ without its proof burden.

### Effect on the models and proofs

* **Removed:**
  * `atom`/`code`/`atom_of` and the countable instances;
  * `trty`, and `tau` as a decoder of codes;
  * `cren`, `tresp`, `rigid_subst`, `mk_subst_tr_agree`;
  * the `typed_on (range code)` plumbing;
  * faithful instances, `psat`, `penv_equiv_gsol`, `hyp_faithful`, probably
    `has_type_reflect`;
  * most `tr_*` lemmas (the about 2.4k use sites are rewritten once, during the
    migration).
* **The semantics of unification becomes polymorphic.** A solution is
  `(θ, σ)` with an arbitrary well-sorted type substitution `θ`, not
  necessarily ground. Soundness is a single theorem; the separate `p`-sound
  theorems disappear.
* **The semantics of theorems** (`valid`, `valid_s`, locale `pure_sem` with
  `holds`/`inhab`) keeps ground well-sorted instantiation of type variables.
  That is the standard semantics of type variables (non-empty carriers, empty
  sorts via `inh`). It simplifies only through `sm` (no `cren`/`rigid_subst`).
  * **D1c** Keep ground models for theorem validity **(rec.)**.
  * **D1c′** Also make `holds` polymorphic. I do not see a gain; please say if
    you meant this by "polymorphic models".
* **Models are unchanged.** `Pure_Pattern`, `Pure_Unify` and `Pure_Thm` do not
  depend on the semantics.

---------------------------------------------------------------------------

## 2. One polymorphic development (question 2)

### Findings

* **Pure_Unify_Correctness duplicates.** The 17 `Unify_Poly_X` theories
  (about 23k lines) re-prove the chain of the mono `Unify_X` theories (about
  18.5k lines) in parallel:
  * 172 lemma pairs have parallel names;
  * soundness proofs are near copies (`pull_psound` and `pull_sound`: 199
    against 200 lines, 70% identical lines);
  * completeness proofs keep the skeleton and grow (`SIMPL0_step_pcomplete`
    319 lines against 177).

  **No monomorphic end theorem is used** anywhere: not by the Poly theories,
  and not by Pure_Thm_Correctness (`hounifiers_complete`, `MATCH_sound`,
  `pull_sound`, `unifiers_fin`, … are all unused). About 7k lines of mono
  proofs serve only the mono end theorems. Every mono end theorem is a short
  corollary of its poly twin (θ = ∅, A = {}; `kokA` is trivial).
* **Pure_Pattern_Correctness reduces.** Here the split is a genuine
  reduction: the poly layer applies the ground core to ground and faithful
  instances (`post_inst`, and the lockstep termination in `Poly_Unif_Term`).
  About 3k of the 6.2k Poly_* lines are reduction machinery: `Poly_Inst`, the
  ground and consistent-type parts of `Poly_Unif`, the lockstep, and
  `has_type_reflect`.
* **Why the development went mono first, and how intrinsic each reason is:**
  * The atom codes contain types (artefact of the dB encoding).
  * The termination measures are type-dependent: `vsz` on η-long forms and
    `reach` over (name, type). This is an artefact: the poly development
    already has type-independent measures (`rsz`, `vreach`) that also work on
    ground problems.
  * The type environment grows. This is intrinsic, but the poly proofs
    handle it already (`fch`, `ffgood`, `match_sat`).
  * Head normalisation needs SN. This is intrinsic, but SN with type
    variables as base types is just as easy.

### D2. Polymorphic only, everywhere **(rec.)**

* **D2a (Unify; independent of D1, can start immediately).**
  1. Merge each `Unify_X`/`Unify_Poly_X` pair into one theory.
  2. Keep only the polymorphic invariants and theorems.
  3. Adopt the type-independent measures (`rsz`, `vreach`) as the only ones.
  4. Delete the mono-only chain.
  5. State the mono end theorems as corollaries only if you want them in the
     README (**D2a′**); otherwise drop them.

  Pure_Thm_Correctness consumes only the poly results plus helpers that stay.
  Expected size: about 41.5k lines down to about 30–34k.
* **D2b (Pattern; do together with D1).**
  * State the core `Pattern_*` theories with a type environment from the start,
    on the new term layer.
  * `Poly_Inst`, the faithful and ground-instance part of `Poly_Unif`, the
    lockstep of `Poly_Unif_Term`, and `post_inst` disappear.
  * The `Type_*` theories (type unification) stay as they are.

  This is the riskiest item, because head normalisation and the termination
  measure must cope with a growing θ. The poly unify development shows how:
  type-independent measures, and SN of terms with type variables as atoms.
  * **D2b′ (fallback):** if it turns out too costly, keep the ground core for
    pattern unification only, but on the new term layer, where the reduction
    becomes `map_lt` commutation instead of faithful instances.

---------------------------------------------------------------------------

## 3. Structural streamlining (question 3)

### S1. `extends` checks all three components of `env` **(as you proposed)**

* **Now:** `extends env env'` (`Pattern_Semantics.thy:321`) compares `tenv`
  only.
  * About 155 of its about 349 uses have a hand-written
    `maxidx env ≤ maxidx env'` next to them.
  * `pextends` (`Poly_Semantics.thy:104`) adds `textends`.
  * `textends (tyenv …)` is spelled out 53 more times.
* **Accreted copies of the same bundle:**
  * `postok`/`postokl` (`Poly_Unif_Correct.thy:341,401`) inline
    `textends ∧ maxidx ≤ ∧ extends`, because `pextends` is defined in a later
    theory;
  * `ext e' e` (`Poly_Unif_Correct.thy:165`) takes the extension first,
    against the README convention, and `ext_trans` has its premises
    reversed;
  * `ty_ext`, `prunes`, `uq`, `new_ok`, `estep` and `mextends` inline variants;
  * `sol_ext` has `maxidx ≤` but no `extends`.
* **New:**

      extends env env' ⟷ textends (tyenv env) (tyenv env') ∧ tenv-extension ∧ maxidx env ≤ maxidx env'

  Delete `pextends` and `ext`. Keep explicit equalities only where they are
  really meant (`tenv env' = tenv env` in `estep`).
* **Result:** about 250 explicit `maxidx` conjuncts disappear, and the only
  violation of the argument-order convention goes.

### S2. One invariant of type environments

* **Now:**
  * `tinv` occurs twice in `unif_problem`: once in `penv_inv` and once for
    `ptvars`, which subsumes `etvars`. The same holds for `pinv`.
  * `tinv ∧ tsorted` appear together 44 times.
  * The conditional certification `tcert … A ⟶ tcert … θ'` is copied 9 times,
    although every top-level theorem assumes `tcert alg A`.
* **New:** `tyenv_ok alg ar n θ A ≡ tinv ar n θ A ∧ tsorted alg θ ∧ tcert alg (tvars θ ∪ A)`,
  with unconditional certification. `penv_inv` keeps only the term part.

### S3. One signature locale, used consistently

* **Now:**
  * `csig` fixes only `ctab`, and `wf_csig` adds `alg ar`. Definitions made in
    `csig` take `alg ar` explicitly: `" alg ar "` occurs about 1600 times,
    also inside `wf_csig`.
  * `gtinst ρ` uses the locale's `alg ar`, while `gsol alg ar θ ρ` takes them
    explicitly, and `gtinst ρ = gsol … vt_empty ρ`.
  * `mfin` fixes its own `ar`, but `pmfin` does not.
  * The hypotheses `cfg_alg cfg = alg` (71 times) and
    `length (vl xs) = length xs` (38 times) are boilerplate.
* **New:**
  * a locale `sig` that fixes `ctab alg ar` and assumes well-formedness;
  * all definitions inside it;
  * a sublocale `unif_cfg` that fixes `cfg vl` and assumes the two equations;
  * `gtinst` deleted.
* Also fix the README drift: it says `unif_problem` extends `wf_algebra`, but
  it actually extends `wf_csig`.

### S4. One notion of satisfying an environment

* **Now:**
  * `solves` is used only 5 times, all in `Pattern_Correctness.thy`.
    Elsewhere `gsol ∧ closed_on UNIV σ ∧ sat σ (instE ρ env)` is written out,
    and `closed_on UNIV σ ∧ sat σ env` appears 51 times.
  * `psat` and `solution` are further variants.
* **New:** a single `solves (θ, σ) env` on the new term layer (D1). Its
  variants become conjunctions with typing, and it is used everywhere.

### S5. No single and list twins; one well-typedness bundle

* `pre`/`prel`, `inst_ok`/`inst_okl`, `post`/`postl` and `postok`/`postokl`:
  keep the list versions. The single versions become abbreviations at `[(s,t)]`.
* `env_wt ≡ wf_env ∧ env_typed ∧ fresh_env`, and `env_inv = acyc ∧ env_wt`.
  `inst_ok`, `ty_ext` and `sol_ext` use it. `tyinv` is `cinv` without the
  solution, so define one from the other.
* One family of well-formed terms, parameterised by the admissible types,
  instead of all of these:
  * `wf_term`/`wf_tm`/`pwf_term`/`swf_tm`;
  * `wf_env`/`pwf_env`/`swf_env`;
  * `typs_ok`/`twft`/`∀T∈tys t. wft ar T`;
  * `binders_ok`/`sbinders`;
  * `env_typed`/`env_typed_mod`/`wt_env`;
  * `tyA`, which is `tyw` with empty θ.

  After D2, most of these pairs disappear anyway.

### S6. One monad library

* **Now:** there are five copies of the monad.
  * `M` (Pure_Term) and `Z` (Pure_ZTerm) are option-exception monads.
  * `W` (Unify_Base), `T` (Pure_Bicompose) and `P` (Pure_Proofterm) are
    option-writer-exception monads.

  Each copy has its own reasoning layer: 52 `ok_*`, 29 `okW_*` and 20 `okT_*`
  lemmas, plus binds and congruences. `P` and `Z` lack `ok`. `bindZ_returnZ`
  is defined twice, with different statements (`Pure_ZTerm.thy:135`,
  `ZTerm_Thm.thy:786`).
* **New:** one generic writer-exception monad over the log and exception
  types, with one `ok` and one simp set, and the five monads as instances.
  This must be checked against `code_printing`; if needed, keep the type
  names as abbreviations.

### S7. Lemma library; delete duplicates; names by role

* **Duplicates:**
  * 85 lemma names are defined twice or more.
  * About 47 statements are proved twice under different names, e.g.
    `Abs_equiv_Abs`/`equiv_Abs_reflect`/`equiv_Abs_inj`,
    `tsubst_ground`/`tsubst_no_tvars`/`tsubst_no_tvars'`,
    `code_eq_iff`/`code_inj`, `match_terminates`/`match_term`,
    `okW_det` ×2 and `pinv_text` ×2.
  * There are three copies each of `tr_combound`, `has_type_combound` and
    `foldr_fun_type_inj`.

  Put one library theory per layer directly after the definitions it is
  about, and delete the copies.
* **Names that show accretion:**
  * The exported theorems `assignment_sound'` and `SIMPL_sound''` (there is no
    `SIMPL_sound'`) get unprimed names.
  * The `*_inst2` family becomes `*_inst_rev`.
  * Overloaded `inst` names get disambiguated (Pattern_Size against
    Poly_Inst).
  * After D2, the `p`/`s` prefixes go away; keep `z` for tight proofs.
* **Stale text:** the README and `ZTerm_BicomposeMain.thy:300–305` still
  describe `zenv_ok` as an assumption, although it is now proved.

### S8. One statement shape for the bicompose theorems

* **Now:** six theorems repeat a block of about 13 hypotheses (cfg, finite A,
  state, rule, `scons`/index bound/`tyA`/`tcert` for A, ns, er, fl, vl):
  * `zbicompose_proof_valid`: 29 hypotheses;
  * `bicompose_proof_valid`: 26;
  * `bicompose_aux_thm_typed`: 21;
  * `bicompose_aux_complete`: 19;
  * `bicompose_aux_valid` and `bicompose_aux_terminates`: 17 each.

  The conclusion of `zbicompose_proof_valid` restates `thm_typeds` by hand.
* **New:**
  * a locale `bicompose_call` that fixes the call and assumes the shared
    block;
  * one predicate `thm_typing A W lo m tps P`, used in `thm_typeds`,
    `thm_prf_inv`, `zthm_prf_inv` and in all the statements;
  * `bicompose_aux_valid` uses the same common-typing bundle. The
    non-incremented case is derived through `pinv_all_unify_var_types`.

---------------------------------------------------------------------------

## 4. ML patches (question 4)

General rules I propose:
* Every patch is the smallest change that expresses the model, in the style of
  the surrounding code, using existing Pure functions.
* The model is a literal transcription of the patched ML.
* The differential tests run exactly Isabelle2026 + the patches (see H1).

| Patch | Assessment | Proposal |
|---|---|---|
| `unify-saturate` (+16 lines: new `eta_expand_dpair`, two `strip_comb`s) | Re-implements what `head_norm_dpair` (already in `unify.ML`, used by `SIMPL0`) does: `eta_norm` η-expands both sides according to their types in the *current* type environment, and `new_dpair` moves the new binders into `rbinder`. | **M1 (rec.)** Replace the whole patch by one changed line plus one new line in `MATCH`: `fun MATCH context (env, dp, dpairs) = let val ((rbinder, t, u), env) = head_norm_dpair context (env, dp); …`. The model's `match_sat`/`eta_expand_dpair` become `head_norm_dpair`, whose lemmas already exist for `SIMPL0`. Checked in Isabelle2026 (PIDE, both variants on top of all four unify patches), comparing the first 4 unifiers and the exceptions. On the README counterexample, in both pair orders, the results are identical, and both fix Isabelle2026's wrong result. On 5000 single-pair resolution problems with type variables from HOL's theorems, there are 0 differences (11 time out in both). On 2000 two-pair problems there are also 0 differences. |
| `zterm-flatten` + `zterm-asm` (helper `asm_prf` with `Logic.assum_problems`) | Two fixes of the same mistake: proofs of premises built from the *normalised* premises. The flatten fix already applies the principle "build from the unnormalised premise, as the classic `Proofterm.bicompose_proof` does, then normalise the proof (`normp`)". | **M2 (rec.)** Apply the same principle to the assumption proof: `[normp (mk_asm_prf (zterm (the A)) n m)]` instead of `asm_prf` and `Logic.assum_problems`. The two patches merge into one patch of 3 changed lines and no new function. The model's `zasm_count` disappears. To be validated: `normp` of `mk_asm_prf` of the unnormalised premise equals the current proof; it should, since `mk_asm_prf` creates no redexes and the premise's variables are visible. |
| `unify-flexflex` | Two hunks: `del` in `clean_term`, and the `Abs` case of `rigid_bound`. `clean_term` only receives `Envir.norm_term` output (`add_ffpair`), which is β-normal, so the `rigid_bound` hunk (no rigid positions in the arguments of a β-redex) never fires. | **M3** Drop the `rigid_bound` hunk and revert the model, using β-normality of `norm_term` in the completeness proof; needs checking whether that lemma exists or is cheap. Nit: write `del` with the model's name and shape (`rigid_headed`), since the reference already does. |
| `unify-cyclic` (+28 lines, `matchone`) | Huet's single step is the right fix, but `matchone` duplicates the projection and type-unification code of `matchcopy` (the `unify_trace_types` choice, `make_args`, the order of projections). The `fn (_, t, u)` in `MATCH` shadows the pair's `t`, `u`. | **M4** Either (a) **(rec.)** keep `matchone` but make it the minimal transcription of the model's `match1` and rename the shadowed variables, or (b) add a flag to `matchcopy` so that both share `projenv`. (b) duplicates less but touches more existing lines. Please choose. |
| `unify-rigid-occurs` | Correct and minimal. The leading `Term.eq_ix (v, w) andalso` is implied by the `case` only while `v` is unassigned, which every caller guarantees. | **M5** Keep as it is (removing the conjunct would need an extra invariant). |
| `pattern.ML` | Minimal and in the style of `pattern.ML`. But the model `rigid_occurs` (`Pure_Pattern.thy:87`) is not a literal transcription: it recurses on `Abs` instead of `strip_abs_body`, and has an extra `Abs` head case. | **M6** Make the model literal. Keep `(… ; true) handle Pattern => false` rather than `can`, because `can` would also swallow `TYPE` from `Envir.head_norm`. |
| `thm-zterm-rename` | Works, but uses the classic `term` function on a dummy `Var ((x, i), dummyT)` to look up a name. It also has a dead `| _ => raise Same.SAME` branch, relies on `ZTerm.map_vars` accepting a function that raises `Same.SAME` (not part of its signature), converts back with `Same.function_eq (op =)`, and needs `i <= smax`. | **M7** Investigate expressing the renaming as `ZTerm.instantiate_proof` on the renamed variables of the new premises (from `strip_lifted Bi`), i.e. by name *and* type, as Isabelle identifies variables. That needs no index test and no dummy terms, and fits T1. Otherwise keep the patch. |
| `zterm-ofclass` | Fine; the duplicated `ZApp (zterm t, zterm u)` is unavoidable without changing `Logic.match_of_class`. | Keep. |
| `zterm-norm-ofclass`, `zterm-lift-frees`, `zterm-lift-hyps` | One line each, in the style of the code around them. | Keep. |
| `thm-quick-eres` | Minimal given that rules without premises must still be skipped. | Keep. |
| `thm-rename` | Already in the installed tree (`/opt/thm.patch`, with your message "more robust renaming of schematics wrt flex-flex pairs and lifted assumptions"). The repository's copy has a different, long message. | **M8** Use one commit message (yours), and record the base revision the patches apply to. |

**M9. The patch set itself.**
* Provide either the individual `zterm-*` patches or the combined
  `zterm.ML.patch`, not both (**rec.**: individual patches plus a script that
  combines them).
* Use the short lowercase commit messages of Isabelle's history
  (e.g. "proper occurs check for non-pattern occurrences").

---------------------------------------------------------------------------

## 5. Thm and proof layer

### T1. The proof judgment identifies variables by name and type **(rec.)**

* **Why `ZTerm_Hidden.thy` exists** (3720 lines, plus `zren_ok`, `sepz`,
  `zrel`, `hid_ok`, `zsyn`, `zthm_hinv`, and the `hid` premise and the
  `znorm_hyps`/`znorm_pok` conjunct of `zbicompose_proof_valid`):
  * `prf_ok` types variables by `V :: indexname ⇒ ptyp`, and `prf_valid`
    instantiates them by name;
  * Isabelle identifies the variables of tight terms by name and type.
* **New:**
  * variables are self-typed (`Var x T : T`);
  * instantiations are keyed by (name, *original* type), so that they compose.

  Renaming and merging hidden variables then becomes an instance, and
  instances of valid proofs are valid.
* **What goes away:** `ZTerm_Hidden`, `zren_ok`, the second conjuncts of the
  main theorems, the 450 lines on renaming chains inside
  `zbicompose_proof_valid`, and the parameter `W` of `zann`/`zinv`.
* **Bridge:** on terms typed by a `W`, keying by (name, type) agrees with
  keying by name, so one lemma connects the judgment to the semantics and to
  `Envir`.
* This is the same choice as the `Var indexname typ` atoms of D1. The
  same-type assumption for variables shared between state and rule in
  `bicompose_aux` remains: it is a real precondition of `Envir`.

### T2. Prove the instance argument once

* **Now:** the semantic proof (`rchar_valid`), the classic proof
  (`bicompose_proof_valid`) and the tight proof (`zbicompose_proof_valid`) all
  re-establish "instance of the state, instance of the renamed rule,
  conclusion ≡ subgoal, premise by assumption, new premises". 714 of the 1046
  proof lines of the classic theorem reappear verbatim in the 3621-line
  single proof of the tight one.
* **New:**
  * one lemma `bresult_inst`;
  * one skeleton lemma for `mk_AbsPs Ns (q' %% (p %% asm @ fs))`,
    parameterised by annotations;
  * the 3.6k-line proof split into named lemmas.

### T3. Keep only the annotated proof constructions

* **Now:** the tight track has annotated copies of the classic constructions:
  `flatten_params_proof_a`, `imp_prf_a_ok`, `mk_asm_prf_a_ok`,
  `prf_ok_abst_chain_a` and `lift_proof_a`.
* **New:** keep the annotated versions only, and obtain the classic ones by
  erasing the annotations. `prf_ok` of an erasure is a trivial induction,
  since missing annotations are always fine.

### T4. One abstract type of theorems with both proofs

* As in Isabelle's `deriv`, a theorem carries both kinds of proofs.
* Merge `Thm_Proof` and `ZTerm_Thm_Model`: one invariant, one
  `biresolution_*_thms`, one results theorem.
* Merge `biresolution_prf_inv` and `zbiresolution_prf_inv` through their
  shared prologue.

### T5. Consolidate the invariants of tight proofs

* Fold `zlb` into `zinv`, by typing annotations in their actual binder context.
* Bundle `zconst_free ∧ zno_class ∧ zrf`, which is repeated four times.
* Replace `zenv_ok`/`tenv_zok`/`tyenv_zok`/`cts`/`zetys` by one lemma derived
  from `ctok_env`.

### T6. Decide the scope asymmetry of the proof translations

* The tight translation maps `ZConstp`/`ZNop` to `MinProof`, which proves
  anything; this is harmless only because of `zconst_free`. Make the
  translation partial.
* With T1, the classic restriction `prf_vars = {}` may become unnecessary.
* Please decide whether constants of proofs (`PThm`/`ZConstp`) should be
  covered.

---------------------------------------------------------------------------

## 6. Hygiene of models and tests

### H1. The differential test must test the patches

* `thys/Pure_Unify/unify_reference.ML` is not Isabelle2026's `unify.ML` with
  the four patches. Its `matchone` is a third variant, structured like
  `matchcopy` with `projenv`/`make_projs`/`matchfun`, and its `clean_term`
  differs as well. So the patched code is never run against the model.
* **New:** generate the reference by applying `patches/unify-*.patch` to the
  distribution's `unify.ML` (and do the same for `pattern.ML` and
  `zterm.ML`/`thm.ML` where tests exist), renaming only the structure. The
  patch then *is* the tested reference.

### H2. Move the wrapper's logic into the model

* **Now:** `bicompose_wrapper.ML` does work that the theorems then re-encode:
  * it renames the rule's proofs;
  * it recomputes `nlift`, which the model has as `bc_nlift`;
  * it builds `visible` with `full_prop_of`;
  * it lifts premises with `Logic.lift_all` instead of the model's
    `lift_all`.

  As a consequence, the theorems carry `∃vS vR`, and Pure_Thm_Correctness
  defines its own `bres_proof`/`zbres_proof`, which are not the generated
  code.
* **New:** export `bres_proofs`/`zbres_proofs` and `lift_rule_proofs` from the
  model. The wrapper keeps only the lazy `deriv_rule` closures.

### H3. The arity-guessing extension of `unify.ML`

* The model contains an extension, `unify_arity_bound`, with
  `arity_guesses`/`match_eta`/`kokA`/`gentvars` in about 8 theories. It is not
  part of any patch: the verified model equals the patched code only for
  `k = 0`. It also complicates `match1`, `matchcopy`, `MATCH` and the
  completeness invariants.
* **H3a (rec.)** Remove it from this development, so that model and patches
  coincide exactly; keep it on a separate branch as a proposal for Isabelle.
* **H3b** Keep it, and add it as an (optional) patch.

---------------------------------------------------------------------------

## 7. Order of work (revised after the discussion)

1. **Prototype of the term layer on `pterm`:**
   * `incr_bv`/`subst_bound` commutation lemmas with minimal side conditions;
   * β, η and the α-rule;
   * CR of βη;
   * typing and the commutation with type instantiation.

   Then report back: how many side conditions remain, and whether SN is ported
   or obtained by erasure.
2. **Delete the dead monomorphic Unify chain** and the monomorphic end
   theorems.
3. **The λ-library on `pterm`:** the metatheory now taken from
   `Nipkow_Grobauer_Pattern` and HOL-Proofs-Lambda (CR, normal forms, the
   facts used, `ld`, SN).
4. **Port Pattern correctness, polymorphic from the start.** Here S1 (one
   `extends`), S2–S5 and the shared lemma library are done. Models of patched
   functions change where the intended patch shape requires it (M3, M6).
   Report if the polymorphic core stalls.
5. **Port Unify correctness:** polymorphic only (D2a merged into the port),
   S6 (the monad library), and the intended patch shapes in the model (M1,
   M4, M5).
6. **Port Thm correctness:**
   * T1 (variables by name and type), T2–T6, H2 (the wrapper's logic into
     the model), M2, M7;
   * the decision on the validity of theorems is taken here.
7. **Patches last:**
   * patch texts against the Isabelle2026 release, exactly as the model;
   * commit messages (M8, M9);
   * the differential tests on the release with the patches applied (H1);
   * `Unpatched_Examples` re-checked.
8. **README** rewritten from scratch.

## 8. Progress (2026-11-03)

* **One type substitution.** `tsubst` (with `tvars`) lives in
  `Pure_Lambda.Type_Subst`, shared by the λ-library and `Type_Unify`; the
  library's duplicate `tinst` is gone.
* **Soundness of pattern unification, polymorphic, on `pterm`** (session
  `Pattern_Correctness`, no `sorry`): `Pattern_Sound.unify_sound`. If
  `unify alg s t env` returns `env'`, then `env'` extends `env`, and every
  solution `(ρ, σ)` of `env'` makes `s` and `t` αβη-equivalent, provided
  * `s` and `t` are closed and well-typed with the same type after
    instantiation by `ρ`;
  * the bindings of `env` are closed and well-typed (`wt_env ρ env`);
  * every variable name occurs with one type after `ρ`, and variable indices
    are at most `maxidx` (`vinv`).

  `env'` keeps these invariants. The algebra passed to `unify` is arbitrary.
* **Findings.**
  * The type operations (`devar`, `unified`, `norm_type`, `type_unify`) are
    sound for every solution of the type environment without invariants
    (`Pattern_Types`).
  * Variables are identified by name and type, but `Envir` and `flexflex1`
    compare names only. So soundness needs Isabelle's own assumption that a
    name has one type; new variables keep it because they are fresh above
    `maxidx`.
  * flexrigid's `downto0` shortcut binds `F := λbs. t` unchanged. That is
    sound only if the loose bound variables of `t` are below the binders, so
    the soundness statement carries this bound, and the bindings must be
    closed for head normalization to keep it.
* **Completeness of pattern unification** (same session, no `sorry`):
  `Pattern_Complete.unify_complete`. If `(ρ, σ)` solves `env` and unifies
  closed `s` and `t` (well-typed with the same type after `ρ`, under the
  soundness invariants), then `unify alg s t env` (`alg` the signature's
  algebra) never raises `Unif`. Every result `env'` has a solution
  `(ρ', σ')` agreeing with `(ρ, σ)` on the variables of index at most
  `maxidx env`. Corollary `unify_Unif`: a `Unif` failure means no solution.
  * The extra invariant `tvinv A env` is `Type_Mgu`'s `tinv` plus "the type
    variables of the bindings are known". `Type_Mgu.unify_aux_ok` needs it
    for completeness of type unification.
  * Theories:
    * `Pattern_Normal`: renaming, normal forms, canonical bodies of closed
      terms, strengthening, the semantic flex-flex lemmas, and `nf_bounds`
      for projection.
    * `Pattern_Complete_Base`, `_Steps`, `_Flex`, `_Proj`: the invariant
      `cinv`, the step predicate `step_cp`, and one lemma per step.
    * `Pattern_Occurs`: the η-long depth measure `ld` (after Grobauer),
      ported to `pterm`/`ptyp`. It gives soundness of the occurs check
      (`rocc_ok_rigid`).
    * `Pattern_Complete`: the fixpoint induction and the end theorems.
* **Soundness, refactored:** the typing invariants (`wt_env`, `vinv`) now
  need only a type instantiation solving the type environment (`tsol`), not a
  full solution; only the equivalence needs `solution`. New end theorem
  `Pattern_Sound.unify_typed`. Termination needs this, because intermediate
  environments need not have solutions.
* **Termination and exceptions of pattern unification** (no `sorry`):
  `Pattern_Term_Unif.unify_terminates`.
  * **Hypotheses:** `unify alg s t env` is called on closed problems that
    are well-typed for every certified solution of the type environment. The
    environment must be acyclic (`acyc`), satisfy `winv` (soundness's
    `wt_env`/`vinv` for every certified type solution), satisfy `tvinv A`,
    and have certified binding sorts.
  * **Conclusion:** it returns `Ok env'` (with the same invariants again, so
    calls can be chained) or fails with `Unif` or `Pattern`. No other
    exception occurs (`Type_Error`, `Dup`, `Failure`, `Subscript`,
    `Unequal_Lengths`, `TUnify`, ...).
  * **Proof:** induction on a lexicographic measure:
    1. the unbound type variables reachable from a fixed finite covering set;
    2. the unbound term variables of the problem and the environment;
    3. the size of the β-normal form of the unfolded instance at the most
       general type instantiation `tnorm_inst θ`, where flexible terms count
       as their η-expansion. Pruning keeps this size.
  * **Theories:**
    * `Pattern_Acyclic`: name-level dependencies, unfolding `unf`, ranks, the
      occurs check, new bindings.
    * `Pattern_Size`: β-normal forms, `msz`, the measure `M`, pruning.
    * `Pattern_Type_Reach`: type unification keeps known type variables
      covered and binding sorts certified.
    * `Pattern_Termination`: SN with subterms, termination of `head_norm`,
      `ints_of'`, `rigid_occurs`; invariants `einv`/`winv`; pruning and
      fresh extensions; `unify_types`.
    * `Pattern_Term_Flex`, `Pattern_Term_Proj`, `Pattern_Term_Unif`: the flex
      cases, `pr`/`proj`, and `unif`.
* **End theorems of pattern unification** (no `sorry`):
  * `Type_Unify` and `Type_Mgu` moved into `Pattern_Correctness`, which no
    longer depends on `Pure_Pattern_Correctness`.
  * One `rigid` (in `Pattern_Terms`) replaces `rigid_atom` and
    `Pattern_Size.rigid`.
  * The termination invariant `einv` also keeps the type environment sorted
    (`tsorted`), so results have well-sorted solutions.
  * `Pattern_Unify_Correctness`: `uinv` bundles the hypotheses of
    termination; `terminates`; `Ok_unifiable` (the witness is `tsol0`, the
    normal form of the type environment at the binding sorts, with `esol`,
    the instantiated unfoldings of the bindings); `Unif_not_unifiable`;
    `Pattern_not_pattern`; `decides` on patterns. Most generality is
    `unify_complete`.
  * `Pattern_Patterns`: β-normal patterns `ppat`, `env_ppat`.
    `Pattern_Unify_Patterns.unify_ppat`: on closed patterns in a closed
    environment of patterns, `unify` never raises `Pattern` and binds only
    patterns. It needs non-negative bound indices (`bnds_nonneg`), which
    typing gives: `closed` allows negative `Bound`s.
* **Examples** (`Pattern_Example`): five problems in the empty environment
  satisfy `uinv`; `decides` gives `Ok` for two unifiable pattern problems and
  `Unif` for an occurs-check and a sort failure; `?F a =?= b` gives up with
  `Pattern` although unifiable.
* **Matching** (`Match_Types` ... `Match_Correctness`, no `sorry`), on `pterm`:
  `match_terminates`, `first_order_match_terminates`; `match_sound`,
  `first_order_match_sound` (the instance `minst env' pt =
  ap (mtinst tye) (msubst tye te) pt` is αβη-equivalent to the object);
  `match_exn` (only `Ok` or `Match` on well-typed inputs); `match_complete`
  (patterns `ppat` against objects without β-redexes, given a certified
  `(ρ, σ)` instantiating the pattern to the object),
  `first_order_match_complete`; `pattern_iff_ppat` (with `no_redex`).
  * Soundness chains: `match_sound` and `first_order_match_sound` also give
    `bstable env'` (the type variables of the binding types are bound). For
    higher-order matching this needs the binder-type invariant `abs_bound`
    to cover the heads of flexible patterns (`fty`).
* **Lemma placement:** general lemmas of `Pattern_Unify_Patterns` moved:
  term lemmas (applications, lifting, substitution, `strip_comb`) to
  `Pattern_Terms` (with `strip_comb_App`, `incr_bv_apps`, `loose_bvar1_apps`
  from `Pattern_Complete`/`Pattern_Normal`, and one duplicate of
  `strip_comb_atom_apps` in `Match_Complete` dropped); `vars_subst_ge` to
  `Pattern_Vars`; the `ppat` lemmas to `Pattern_Patterns`; the
  `bnds_nonneg` lemmas to `Pattern_Occurs`; the `pok` monad lemmas to
  `Pattern_Monad`; distinctness lemmas to `Pattern_Flex`/`Pattern_Proj`.
* **Next:**
  * Then Unify and Thm.

## 9. Unify port (started 2026-11-03)

* **M1 rejected (reverted).** Normalising the pair by `head_norm_dpair` in
  `MATCH` is unsound: `new_dpair` unifies the binder types of the
  η-expanded sides, which can bind the body type of the flexible variable to
  a function type, so `binder_types env' T` becomes longer than its
  arguments, and `new_dset` builds an ill-typed binding that is no unifier.
  Example (arity bound 0): `?α := ?ε ⇒ ?ε`, `?ζ := (c ⇒ c) ⇒ ?γ`, pair
  `?v c =?= k` with `?v :: d ⇒ ?α`, `k :: ?ζ` (reachable from `SIMPL`, which
  defers the pair before two rigid pairs bind `?α` and `?ζ`). The HOL-based
  differential tests did not hit this case. The model keeps the
  `unify-saturate` shape (`match_sat`, `eta_expand_dpair`), which saturates
  in the current type environment without further type unification.
* **No type unification in `MATCH` (rejected deviation).** A first version
  unified the types of the two sides at the start of `MATCH`, to keep
  soundness unconditional (with sides of different types, `?v c =?= f`,
  `?v :: d' ⇒ ?β`, `f :: ?γ`, a later `?γ := d ⇒ e` gives an ill-typed
  imitation). Rejected: an extra computation in a hot operation, and
  `unify.ML` assumes that both sides of a pair have the same type. The
  model follows `unify.ML`; the assumption is explicit as the invariant
  `sinv` (its `pok` requires a common type at every certified type
  solution), which is now a hypothesis of the soundness theorems as well
  (`hounifiers_sound`, `unifiers_sound`, `unifiers_smash_sound`) and is
  preserved by `SIMPL` and `MATCH`. In Isabelle the kernel's calls
  (`thm.ML`) satisfy it; `Unify.matchers` may pass pairs of different types
  (an ML experiment shows the ill-typed binding there), which is outside
  `unify.ML`'s contract. The `unify-saturate` patch needs no extra line.
* **S6 (one monad library)** is deferred to the Thm port: the Unify layer
  only has `W`; the generic monad needs `W`, `T` and `P` together and a
  check against `code_printing`.
* **Session `Unify_Correctness`** (on `Pattern_Correctness`):
  * `Unify_Monad`: `okW`, `resW`.
  * `Unify_Semantics`: pairs `(rb, t, u)` under binders; `dsolved`,
    `dtyped`, `dvars`; the step relation `dstep env dps env' dps'`
    (extension, typing invariants for every solution of the final type
    environment, and solutions of `dps'` solve `dps`), generalising
    `step_ok`.
* **Done (2026-11-04), all in `context pure_sig`, no locale assumptions:**
  * *Soundness* (`Unify_Sound`, `Unify_Smash_Sound`): `hounifiers_sound`,
    `unifiers_sound`, `smash_flexflex_sound`, for inputs in the invariant
    `sinv`; every enumerated element is a `dstep` from the input to its
    flex-flex pairs. The soundness of the search is proved together with its
    finiteness (`hounifiers_fin_sound` in `Unify_Pull_Fin`).
  * *Termination and finiteness* (`Unify_Simpl_Term`, `Unify_Flexflex_Term`,
    `Unify_Ffeta`, `Unify_Match_Fin`, `Unify_Mc_Fin`, `Unify_Pull_Fin`):
    `SIMPL_term` under the invariant `sinv`, `mc_fin`, `MATCH_fin`,
    `hounifiers_fin`. The flex-flex pairs of `SIMPL` need not be of a base
    type (`ffeta`); `add_ffpair` still raises no exception on them, since
    the number of arguments of a head never decreases from older to newer
    pairs (`hmono`, `SIMPL_add_ffpair_ok`).
  * *Completeness* (`Unify_Simpl_Complete`, `Unify_Flexflex_Complete`,
    `Unify_Match_Complete`, `Unify_Complete`): `SIMPL_complete`,
    `SIMPL_meas` (SIMPL does not increase the measure), `MATCH_complete`
    (a strictly smaller measure, both for `mc` and for `match1`),
    `search_complete`, `hounifiers_complete(_fin)`, `unifiers_complete`,
    for solutions within the arity bound (`mcp_kokK`) and the search bound.
  * *Results for Thm* (`Unify_Results`): `unifiers_fin` (termination and a
    result invariant `uresult`), `unifiers_smash` (no side conditions),
    `unifiers_rs` (further terms keep their types), `unifiers_fresh(_unbound)`,
    `unifiers_maxidx`.
  * `gtyped` quantifies over certified type solutions only: typing checks
    `cert_typ`, so the version over all solutions was false for every
    problem with type variables (and `unifiers_smash_sound` was vacuous).
  * `smash_flexflex_term` and `unifiers_smash` (smashing a result succeeds and
    gives a unifier without flex-flex pairs, in the invariant again);
    `unifiers_tvars`, `unifiers_fresh_tvar`, `unifiers_smash_tvars`;
    `unifiers_complete_fin`
    (`Unify_Results2`: completeness without the termination hypothesis).
    The input type variables `A` are threaded through `mres`, `copy_ok` and
    `rres` (`A ⊆ A'`).
* **New type variables** (`tnew`, `Pattern_Termination`): every step
  introduces only type variables that are known (`tvars_env ∪ A`) or fresh
  above the current `maxidx` (sort intersection in type unification and
  `gentvars` create them at `maxidx + 1`). It is a conjunct of `tstep`,
  `upost`, `sstep`, `cres`, `mres`, `copy_ok`, `rres` and `uresult`. Hence
  `unifiers_tvars`: the type variables of a result are known or above the
  input's `maxidx`, and `unifiers_fresh_tvar` holds without a hypothesis on
  the classes (the old sort-conflict argument needed a second certified
  sort).

## 10. Patches (2026-11-04)

Aims: minimal, readable, reusing Isabelle's functions, and semantically the
model (the model need not mirror the code's structure).

* **Numbered** in the order of application (`patches/01-…` to `15-…`: pattern, unify, then the thm layer; `thm-rename` split into 06 flex-flex pairs and 07 lifting), each a
  clean diff (no offset or fuzz) against the Isabelle2026 release
  (`ISABELLE_ID` 096842708b28) with its predecessors applied.
  `patches/apply ISABELLE_HOME` applies them; `apply -c` prints one combined
  patch (M9: the separate combined `zterm.ML.patch` is gone). Commit
  messages are short and lowercase; 06 and 07 split the message of the
  installed tree's `thm.patch` (M8).
* **H1 (unify):** `thys/Pure_Unify/unify_reference.ML` is generated from the
  release's `unify.ML` and patches 02–05 (`make_unify_reference`), so the
  differential test runs the patched code: 0 mismatches against the model on
  1698 problems (`hounifiers`, `unifiers`, `smash_unifiers`).
* **M4 (a):** `matchone` (04) is a self-contained single step: a `fold` over
  the argument types, sharing `make_args` with `matchcopy`, semantically
  `match1` of the model; the shadowed `t`, `u` in `MATCH` are renamed.
* **04 narrowed (2026-11-06).** With the occurs check of `MATCH` against all
  other pairs, `matchone` was taken whenever `?v` occurred in any unrelated
  pair, and the search depth grew with the size of the copied term: the weak
  case congruence rule of a datatype with ≥14 constructors (`etac arg_cong`)
  exceeded `unify_search_bound` 60 (`HOL-Datatype_Examples.Misc_Codatatype`,
  AFP datatypes); least bounds in a scratch test 7/22/35/66 vs. 1 for
  Isabelle2026. Now `connected` (new in `unify.ML`, `add_env_vars` and
  `connected`, ~25 lines) splits the pairs into those sharing variables with
  `u`/`targs` (modulo `env`, transitively) and the others; the occurs check
  and `matchcopy` see only the connected ones, and the others are appended to
  each copy (`S_MapNewDset … others`). Least bounds now 1/1/2/1. Model,
  reference, differential test (0 mismatches on 1698) and all proofs
  (`connected_set`, `connected_term`, `copy_ok … others`, `match_pair_split`)
  updated.
* **04 narrowed further (2026-11-06, after a full AFP build).** Two causes of
  single steps that exceed `unify_search_bound` remained:
  * *Assigned variables connected pairs.* In the construction of codatatype
    `wit3_F1` (`HOL-Datatype_Examples.Misc_Codatatype`; worked with bound 63),
    the arguments of all pairs contain `?p` bound to `λx. (fst x, snd x)`, so
    each pair `?f … (fst x, snd x) =?= u` was connected to the pair
    `?f … x x =?= u`, and `?f` "occurred". `connected` now compares only
    unassigned variables (`unassigned`, ML `filter_out (Vartab.defined …)`).
    The proofs only use that the split covers all pairs (`connected_set`).
  * *`?v` in its own arguments.* For `rule someI_ex`
    (`?P (SOME x. ?P x) =?= u`; AFP `Relational_Method`, `Package_logic`) the
    occurs check always failed, and the single steps grew with `u`. Now
    `match1` is taken only if all `targs` are bound variables (`occ_check`,
    ML `forall is_Bound targs andalso …`): otherwise the new variables of the
    copy, applied to `targs`, are never assigned (the `Fd` regime of
    `mc_fin`, `vgood`), so the update cannot close a cycle; `?v` may itself be
    bound while copying (`new_dset` then adds the pair of its binding and the
    copy). Proofs: `copy_ok` allows a bound `?v` (and records
    `vtvars X`), `bound_copy_pair`, `new_dset_ok` and `mcp_new_dset_bound`
    (completeness) cover that branch.
  * Checked with the patched Isabelle: `wit3_F1` (default bound),
    `HOL-Datatype_Examples`, AFP `Relational_Method`, `Package_logic`,
    `CommCSL`. Not checked here: `Eval_FO`, `Padic_Field`,
    `Simplicial_complexes_and_boolean_functions` (the latter raised
    `THM forall_intr`, which needs separate analysis).
* **M1** rejected; `unify-saturate` (05) needs no type unification (§9).
* **03:** the flex-flex patch is unchanged in substance (comment added).
* **Not done, each needs a change of the model first:** M3 (drop the
  `rigid_bound` hunk), M6 (see below); M2
  and M7 belong to the Thm port, whose model changes with them.
* **Counterexamples** (session `Unpatched_Examples`): one theory
  `Unpatched_NN_…` per patch, checked against Isabelle2026 without the
  patches. Failed proof steps are stated with the Isar method `fails`
  (`Unpatched_Base`), so that 01–05 and 15 need no ML except one assertion of
  ill-typedness in 05; the tight-proof defects (08–14) are only visible in the
  tight proofs and need short ML checks (shared `zprop` in `Unpatched_Base`).
  06 and 07 are the proofs of `False` of Kappelmann and Huch (isabelle-users,
  27 October 2026, "Soundness-critical issues in thm.ML"), without ML; they are
  outside the session (the installed Isabelle contains these patches), and with
  the patched kernel the decisive step leaves an unprovable subgoal.
* **M6 rejected (2026-11-06).** Tried: replace the patch's `rigid_occurs` by
  Pure's `Pattern.pattern` on `Envir.norm_term env t`, plus a second occurs
  check on the normal form (needed: normalisation can erase the occurrence,
  `?F =?= c (?G ?F)` with `?G := λx. d` normalises to the pattern `c d` and
  has the unifier `?F := c d`). Model and proofs were completed (c3ef456),
  then reverted: `norm_term` normalises the whole term, including types,
  whereas `rigid_occurs` head-normalises lazily along rigid paths only, and
  occurs-check failures are frequent in proof search; `rigid_occurs` is also
  more precise (it raises `Unif` for rigid occurrences in non-patterns). The
  patch stays `01-pattern-rigid-occurs`; `norm_term` stays in `Pure_Envir`.

## 11. Thm port (started 2026-11-06)

* **Decisions (2026-11-06):**
  * *Validity is polymorphic.* A model is a predicate `holds` on closed
    propositions (no loose bound variables, no schematic term variables;
    type variables allowed) that respects typed βη-conversion, reads `⟹` as
    implication and `⋀x::T` as quantification over the closed terms of type
    `T`, and is closed under certified type instantiation. A theorem
    (shyps, hyps, tpairs, prop) is valid if for every certified type
    instantiation `ρ` and every closed well-typed term substitution `σ` that
    equates its flex-flex pairs modulo βη, `holds (ap ρ σ h)` for all hyps
    implies `holds (ap ρ σ prop)` (sort hypotheses: as before, under
    inhabited sorts). No ground instances.
  * *Proof constants are covered* (T6): `PThm`/`ZConstp` are axioms with
    their stated propositions, from a context of named theorems; the proof
    judgments check their instances. The tight translation becomes partial
    only for `ZNop`.
* **Phases:** A semantics and soundness of `bicompose_aux`; B termination,
  completeness, lifting and biresolution, the abstract type of theorems;
  C classic proof terms (T1–T3, T6); D tight proofs (T1, T3, T5, M2, M7);
  E H2 (wrapper logic into the model) and T4 (one type with both proofs).
* **Phase A done (2026-11-06)**, session `Thm_Correctness`: `pure_model`
  (`holds` on closed, Var-free propositions; typed βη, `⟹`, `⋀`, closure
  under certified well-sorted type instantiation), `valid`, and
  `bicompose_aux_valid` (results of `bicompose_aux` for valid, well-typed
  state and rule are valid; preconditions: `scons` of the type variables,
  and `vtcons` of the variables when incremented). One instance lemma
  `bresult_inst` (T2); renaming as substitution `rsubst`; the unifier's
  results via `unifiers_fin`/`uresult`. Open for later phases: sort
  hypotheses, typing of the results, a `holds`-free interface for the new
  premises (needed by the proof layers).
* **Semantics revised (2026-11-06, option B).** The phase-A `holds` with
  closure under instantiation had only degenerate models (closure plus
  `holds_imp` on propositions with type variables excludes the intended
  set-theoretic models; `holds_inst` was unused). After comparing the
  approaches of Kunčar–Popescu (ground semantics, JAR 2019), Åman
  Pohjola–Gengelbach (lazy ground semantics, LPAR 2020) and HOLC (ESOP
  2017), the Thm layer now uses a Tarski semantics over an abstract
  universe (Hoare-style axioms, `Thm_Model.thy`):
  * locale `universe` (membership, extensional function space with
    application and abstraction, two truth values); locale `pure_model`
    (type constructors on nonempty sets, classes as predicates compatible
    with the class algebra, constants in their types; `⟹`, `⋀` built in);
  * `tsem`/`sem` under valuations `η` of all type variables (schematic and
    fixed, by nonempty sets of their sorts) and `ξ` of all term variables,
    indexed by name and type as they occur (lazy, no capture);
  * theorems: typing soundness, substitution lemmas, soundness of
    αβη-conversion (`sem_conv`, via Church–Rosser), instances (`sem_ap`,
    `good_ap`).
  * `valid hs tps P` (`Thm_Semantics.thy`): for every instance `(ρ, σ)`
    solving the flex-flex pairs up to αβη (constraints, as unification
    solves them) and every model and good valuation, the hypotheses imply
    the proposition. Spine lemmas are semantic (values of parameters
    instead of closed terms); `pure_valuation` fixes one valuation.
    `bicompose_aux_valid` is unchanged.
  * Witness: session `Thm_Model_ZFC` (`sublocale pure_sig ⊆ zfc_model`,
    ZFC_in_HOL from the AFP).

* **Termination (B1, 2026-11-06).** `Bicompose_Fin.thy`:
  `bicompose_aux_terminates` under the assumptions of
  `bicompose_aux_valid` minus validity, plus `nsubgoal` bounds and
  `eres_flg ⟹ flatten ⟹ lifted`; pulling the results yields a finite
  list (`bevals`). Key steps: `ures` now holds for every well-formedness
  witness of a problem (so the call's type variables `A` are available);
  normalization terminates via `norm_term_term` (`norm_term_ok`,
  `norm_term_skip_ok`); the renaming of `rename_bvs` is injective on the
  names of the premises and its targets avoid the unknowns
  (`rename_bvs_inj`, `rename_bvs_target`), so an index-preserving map undoes
  it (`newAs_props`) and the variables of the new premises stay consistent
  (`winv_reindex`, `uresult_winv`). Environment invariants of a call are
  shared with soundness (`call_env`).
* **Completeness (B2, 2026-11-06).** `Bicompose_Complete.thy`:
  `bicompose_aux_complete`. For a well-typed proof state and rule, with
  `match` off: if `ρ` solves the type environment `env` of the call (after
  `unify_var_types`) and `(ρ, σ)` solves a problem of the call
  (`bicompose_problem`: conclusion against subgoal, plus an assumption for
  elim-resolution) and both flex-flex lists, within the configured bounds
  (`mcp_kokK`, `mcp_meas` relative to `env`), then some result `r` has an
  instance `(ρ', σ')` solving `br_tpairs r` with
  `ap ρ' σ' (env_apply (br_env r) X) ≡ ap ρ σ X` for every component `X` of
  the proof state and the rule. Ingredients: pending results (`pend`,
  `bevals_pend`), the quick test of elim-resolution is complete
  (`could_unify_complete`, via `conv_atom_apps_inv`), and
  `unifiers_most_general_terms` (Unify_Results2, most generality on every
  term over the variables of the problem).
