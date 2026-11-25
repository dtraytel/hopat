section \<open>A Signature That Satisfies the Assumptions, and Derivations in It\<close>

theory Thm_Example
  imports Thm_Derivable
begin

text \<open>
  The statements about theorems assume properties of the signature: a well-formed class algebra
  (\<^locale>\<open>pure_sig\<close>), proof constants whose propositions are closed (\<^const>\<open>is_prf_sig\<close>),
  equality and its axioms (\<^const>\<open>sign_eq\<close>) and closures without free variables
  (\<^const>\<open>sign_closed\<close>). This theory shows that the assumptions can be met together: the
  signature \<open>pure0\<close> below, a fragment of the theory \<open>Pure\<close> with \<open>prop\<close>, \<open>fun\<close>, the logical
  constants and the equality axioms as proof constants, has all of them. Derivations in it show
  that the rules compute theorems; theory \<open>Thm_Example_Proofs\<close> (session \<open>Thm_Proofs\<close>) shows
  that their proofs are valid.
\<close>


subsection \<open>The signature\<close>

text \<open>No classes, no arities:\<close>

definition alg0 :: algebra where
  "alg0 = Algebra (\<lambda>_ _. False) (\<lambda>_. []) {}"

lemma wf_algebra0: "wf_algebra alg0 ar"
  by unfold_locales (simp_all add: alg0_def class_le_def)

lemma pure_sig0: "pure_sig alg0 ar"
  by (simp add: pure_sig_iff wf_algebra0)

text \<open>
  The proof constants are the equality axioms; their propositions are closed over their term
  variables (\<^const>\<open>eq_closure\<close>), their type arguments are \<open>?'a\<close> and \<open>?'b\<close>. Any other
  proposition is no proof constant; its closure is a closed proposition without type variables.
\<close>

definition eq_list :: "name list" where
  "eq_list = [STR ''reflexive'', STR ''symmetric'', STR ''transitive'', STR ''equal_intr'', STR ''equal_elim'',
    STR ''abstract_rule'', STR ''combination'']"

lemma set_eq_list: "set eq_list = eq_names"
  by (auto simp: eq_list_def eq_names_def)

definition triv_prop :: pterm where
  "triv_prop = eq_all propT (mk_implies (Bound 0) (Bound 0))"

definition close0 :: "pterm \<Rightarrow> pterm" where
  "close0 A = (case find (\<lambda>a. A = equality_axiom a) eq_list of Some a \<Rightarrow> eq_closure a | None \<Rightarrow> triv_prop)"

definition tyargs0 :: "pterm \<Rightarrow> (indexname \<times> psort) list" where
  "tyargs0 A = (if \<exists>a\<in>eq_names. A = equality_axiom a then [((tvar_a, 0), []), ((tvar_b, 0), [])] else [])"

definition ax0 :: "pterm \<Rightarrow> bool" where
  "ax0 A \<longleftrightarrow> (\<exists>a\<in>eq_names. A = equality_axiom a)"

definition ctab0 :: "name \<Rightarrow> ptyp option" where
  "ctab0 = (\<lambda>c. if c = STR ''Pure.eq'' then Some (ax_aT \<rightarrow>\<^sub>T ax_aT \<rightarrow>\<^sub>T propT) else None)"

definition pure0 :: sign where
  "pure0 = \<lparr>sg_alg = alg0, sg_ar = \<lambda>_. 0,
    sg_consts = ctab0,
    sg_close = close0, sg_tyargs = tyargs0, sg_ax = ax0, sg_axioms = \<lambda>_. None\<rparr>"

lemma pure0_sel [simp]:
  "sg_alg pure0 = alg0" "sg_ar pure0 = (\<lambda>_. 0)"
  "sg_consts pure0 = ctab0"
  "sg_close pure0 = close0" "sg_tyargs pure0 = tyargs0" "sg_ax pure0 = ax0" "sg_axioms pure0 = (\<lambda>_. None)"
  by (simp_all add: pure0_def)

lemma equality_axiom_inj: "a \<in> eq_names \<Longrightarrow> b \<in> eq_names \<Longrightarrow> equality_axiom a = equality_axiom b \<Longrightarrow> a = b"
  by (auto simp: eq_names_def equality_axiom_def Let_def ax_eq_def ax_var_def mk_implies_def
      implies_def all_const_def ax_aT_def ax_bT_def propT_def)

lemma close0_eq: "a \<in> eq_names \<Longrightarrow> close0 (equality_axiom a) = eq_closure a"
proof -
  assume a: "a \<in> eq_names"
  then obtain b where b: "find (\<lambda>a'. equality_axiom a = equality_axiom a') eq_list = Some b"
    by (cases "find (\<lambda>a'. equality_axiom a = equality_axiom a') eq_list") (auto simp: find_None_iff set_eq_list)
  then have "b \<in> eq_names" "equality_axiom a = equality_axiom b"
    by (auto simp: find_Some_iff set_eq_list[symmetric])
  with a have "b = a" by (auto dest: equality_axiom_inj)
  with b show ?thesis by (simp add: close0_def)
qed

lemma close0_cases:
  obtains a where "a \<in> eq_names" "close0 A = eq_closure a" "tyargs0 A = [((tvar_a, 0), []), ((tvar_b, 0), [])]"
  | "close0 A = triv_prop"
proof (cases "find (\<lambda>a. A = equality_axiom a) eq_list")
  case None
  then show ?thesis by (intro that(2)) (simp add: close0_def)
next
  case (Some a)
  then have "a \<in> eq_names" "A = equality_axiom a" by (auto simp: find_Some_iff set_eq_list[symmetric])
  then show ?thesis using Some by (intro that(1)[of a]) (auto simp: close0_def tyargs0_def)
qed

lemma eq_closure_closed:
  assumes "a \<in> eq_names"
  shows "closed (eq_closure a)" "vars (eq_closure a) = {}" "fnames (eq_closure a) = {}"
    "ttvars (eq_closure a) \<subseteq> {((tvar_a, 0), []), ((tvar_b, 0), [])}"
    "TFree b S \<notin> tatoms (eq_closure a)"
  using assms
  by (auto simp: eq_names_def eq_closure_def eq_all_def Let_def ax_eq_def mk_implies_def
      implies_def all_const_def ax_aT_def ax_bT_def propT_def closed_def)

lemma triv_prop_closed:
  "closed triv_prop" "vars triv_prop = {}" "fnames triv_prop = {}" "ttvars triv_prop = {}"
  "TFree b S \<notin> tatoms triv_prop"
  by (auto simp: triv_prop_def eq_all_def mk_implies_def implies_def all_const_def propT_def closed_def)

lemma is_prf_sig0: "is_prf_sig pure0"
  unfolding is_prf_sig_def pure0_sel
proof (rule prf_sig.intro[OF pure_sig0], unfold_locales)
  fix A
  show "closed (close0 A)" "vars (close0 A) = {}" "ttvars (close0 A) \<subseteq> set (tyargs0 A)"
    by (rule close0_cases[of A]; use eq_closure_closed triv_prop_closed in auto)+
qed simp

lemma sign_eq0: "sign_eq pure0"
  unfolding sign_eq_def pure0_sel
proof (intro conjI impI)
  show "pure_sig_gen.eq_ok ctab0"
    by (auto simp: pure_sig_gen.eq_ok_def[OF pure_sig0[unfolded pure_sig_def]] ctab0_def ax_aT_def)
  then show "prf_eq alg0 (\<lambda>_. 0) ctab0
    close0 tyargs0 ax0"
    using is_prf_sig0 unfolding is_prf_sig_def pure0_sel
    by (intro prf_eq.intro prf_eq_axioms.intro) (auto simp: close0_eq tyargs0_def ax0_def)
qed simp

lemma sign_closed0: "sign_closed pure0"
  unfolding sign_closed_def pure0_sel
proof (intro allI conjI)
  fix A b S
  show "fnames (close0 A) = {}" "TFree b S \<notin> tatoms (close0 A)"
    by (rule close0_cases[of A]; use eq_closure_closed triv_prop_closed in auto)+
qed


subsection \<open>Derivations\<close>

abbreviation "typing0 \<equiv> signature.typing (cert_typ alg0 (\<lambda>_. 0)) (const_typ_ok ctab0)"
abbreviation "ztargs0 \<equiv> pure_sig_gen.ztargs ctab0"

lemmas typing0_intros = signature.typing.intros[where ty_ok = "cert_typ alg0 (\<lambda>_. 0)" and const_ok = "const_typ_ok ctab0"]
lemmas cterm_wf0 = pure_sig.cterm_wf_def[OF pure_sig0[of "\<lambda>_. 0"], where ctab = ctab0]
lemmas ibelow0 = pure_sig_gen.ibelow_def[OF pure_sig0[of "\<lambda>_. 0", unfolded pure_sig_def]]
lemmas ztargs0 = pure_sig_gen.ztargs_def[OF pure_sig0[of "\<lambda>_. 0", unfolded pure_sig_def], where ctab = ctab0]

definition A0 :: pterm where "A0 = Free STR ''A'' propT"

definition ctA :: cterm_data where
  "ctA = \<lparr>cd_rep = CTerm A0 propT (-1), cd_sorts = {}, cd_sign = pure0\<rparr>"

lemma cert_propT0 [simp]: "cert_typ alg0 (\<lambda>_. 0) propT"
  by (simp add: cert_typ_def propT_def tarity_def)

lemma cterm_ok_ctA: "cterm_ok ctA"
  by (auto simp: cterm_ok_def ctA_def cterm_wf0 A0_def closed_def ibelow0 propT_def cert_typ_def tarity_def
      intro!: typing0_intros)

definition thA :: thm_data where
  "thA = mk_thm (mk_rep (-1) [] A0) {} [A0] pure0 (returnW (Hyp A0)) (return (ZHyp (ZVar (STR ''A'', -1) ZProp)))"

lemma derivable_thA: "derivable thA"
  using derivable_gen.assumeI[OF cterm_ok_ctA, of "mk_rep (-1) [] A0"]
  by (simp add: thA_def ctA_def assume_rule_def adjust_maxidx_cterm_def zassume_proof_def A0_def propT_def)

definition thAA :: thm_data where
  "thAA = with_cons {} (mk_thm (mk_rep (-1) [] (mk_implies A0 A0)) {} [] pure0
    (returnW (AbsP STR ''H'' None (PBound 0)))
    (return (ZAbsp STR ''H'' (ZVar (STR ''A'', -1) ZProp) (ZBoundp 0))))"

lemma derivable_thAA: "derivable thAA"
  using derivable_gen.implies_intr[OF cterm_ok_ctA _ derivable_thA, of "mk_rep (-1) [] (mk_implies A0 A0)"]
  by (simp add: thAA_def implies_intr_def implies_intr_proof_def zimplies_intr_proof_def ctA_def thA_def
      mk_rep_def A0_def propT_def)

definition F0 :: pterm where "F0 = Free STR ''f'' (propT \<rightarrow>\<^sub>T propT)"

definition ctF :: cterm_data where
  "ctF = \<lparr>cd_rep = CTerm F0 (propT \<rightarrow>\<^sub>T propT) (-1), cd_sorts = {}, cd_sign = pure0\<rparr>"

lemma cterm_ok_ctF: "cterm_ok ctF"
  by (auto simp: cterm_ok_def ctF_def cterm_wf0 F0_def closed_def ibelow0 propT_def cert_typ_def tarity_def
      intro!: typing0_intros)

definition th_reflA :: thm_data where
  "th_reflA = conv_datar ctA (mk_rep (-1) [] (eq_const propT $ A0 $ A0))"

definition th_reflF :: thm_data where
  "th_reflF = conv_datar ctF (mk_rep (-1) [] (eq_const (propT \<rightarrow>\<^sub>T propT) $ F0 $ F0))"

lemma derivable_th_reflA: "derivable th_reflA"
  unfolding th_reflA_def
  by (rule derivable_gen.reflexive[OF cterm_ok_ctA])
    (simp_all add: sign_eq0 ctA_def reflexive_def mk_rep_def A0_def mk_equals_def fastype_of_def)

lemma derivable_th_reflF: "derivable th_reflF"
  unfolding th_reflF_def
  by (rule derivable_gen.reflexive[OF cterm_ok_ctF])
    (simp_all add: sign_eq0 ctF_def reflexive_def mk_rep_def F0_def mk_equals_def fastype_of_def)

definition th_comb :: thm_data where
  "th_comb = with_cons {} (mk_thm (mk_rep (-1) [] (eq_const propT $ (F0 $ A0) $ (F0 $ A0))) {} [] pure0
    (bindW (th_proof th_reflF) (\<lambda>p. bindW (th_proof th_reflA) (\<lambda>q. combination_proof F0 F0 A0 A0 p q)))
    (bindM (th_zproof th_reflF) (\<lambda>p. bindM (th_zproof th_reflA) (\<lambda>q.
      zcombination_proof ztargs0 propT propT F0 F0 A0 A0 p q))))"

lemma derivable_th_comb: "derivable th_comb"
  using derivable_gen.combination[OF derivable_th_reflF derivable_th_reflA,
    of "mk_rep (-1) [] (eq_const propT $ (F0 $ A0) $ (F0 $ A0))" propT propT F0 F0 A0 A0]
  by (simp add: th_comb_def th_reflF_def th_reflA_def conv_datar_def ctA_def ctF_def sign_eq0 combination_res_def
      combination_data_def mk_rep_def F0_def A0_def mk_equals_def fastype_of_def union_tpairs_def)

end
