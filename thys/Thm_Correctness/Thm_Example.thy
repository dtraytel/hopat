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
  that the rules compute theorems with proofs, and that the proofs are valid.
\<close>


subsection \<open>The signature\<close>

text \<open>No classes, no arities:\<close>

definition alg0 :: algebra where
  "alg0 = Algebra (\<lambda>_ _. False) (\<lambda>_. []) {}"

lemma wf_algebra0: "wf_algebra alg0 ar"
  by unfold_locales (simp_all add: alg0_def class_le_def)

lemma pure_sig0: "pure_sig alg0 ar"
  by (simp add: pure_sig_def wf_algebra0)

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
  show "pure_sig.eq_ok ctab0"
    by (auto simp: pure_sig.eq_ok_def[OF pure_sig0] ctab0_def ax_aT_def)
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
abbreviation "ztargs0 \<equiv> pure_sig.ztargs ctab0"

lemmas typing0_intros = signature.typing.intros[where ty_ok = "cert_typ alg0 (\<lambda>_. 0)" and const_ok = "const_typ_ok ctab0"]
lemmas cterm_wf0 = pure_sig.cterm_wf_def[OF pure_sig0[of "\<lambda>_. 0"], where ctab = ctab0]
lemmas ibelow0 = pure_sig.ibelow_def[OF pure_sig0[of "\<lambda>_. 0"]]
lemmas ztargs0 = pure_sig.ztargs_def[OF pure_sig0[of "\<lambda>_. 0"], where ctab = ctab0]

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
  using derivable.assumeI[OF cterm_ok_ctA, of "mk_rep (-1) [] A0"]
  by (simp add: thA_def ctA_def assume_rule_def adjust_maxidx_cterm_def zassume_proof_def A0_def propT_def)

definition thAA :: thm_data where
  "thAA = with_cons {} (mk_thm (mk_rep (-1) [] (mk_implies A0 A0)) {} [] pure0
    (returnW (AbsP STR ''H'' None (PBound 0)))
    (return (ZAbsp STR ''H'' (ZVar (STR ''A'', -1) ZProp) (ZBoundp 0))))"

lemma derivable_thAA: "derivable thAA"
  using derivable.implies_intr[OF cterm_ok_ctA derivable_thA, of "mk_rep (-1) [] (mk_implies A0 A0)"]
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
  by (rule derivable.reflexive[OF cterm_ok_ctA])
    (simp_all add: sign_eq0 ctA_def reflexive_def mk_rep_def A0_def mk_equals_def fastype_of_def)

lemma derivable_th_reflF: "derivable th_reflF"
  unfolding th_reflF_def
  by (rule derivable.reflexive[OF cterm_ok_ctF])
    (simp_all add: sign_eq0 ctF_def reflexive_def mk_rep_def F0_def mk_equals_def fastype_of_def)

definition th_comb :: thm_data where
  "th_comb = with_cons {} (mk_thm (mk_rep (-1) [] (eq_const propT $ (F0 $ A0) $ (F0 $ A0))) {} [] pure0
    (bindW (th_proof th_reflF) (\<lambda>p. bindW (th_proof th_reflA) (\<lambda>q. combination_proof F0 F0 A0 A0 p q)))
    (bindM (th_zproof th_reflF) (\<lambda>p. bindM (th_zproof th_reflA) (\<lambda>q.
      zcombination_proof ztargs0 propT propT F0 F0 A0 A0 p q))))"

lemma derivable_th_comb: "derivable th_comb"
  using derivable.combination[OF derivable_th_reflF derivable_th_reflA,
    of "mk_rep (-1) [] (eq_const propT $ (F0 $ A0) $ (F0 $ A0))" propT propT F0 F0 A0 A0]
  by (simp add: th_comb_def th_reflF_def th_reflA_def conv_datar_def ctA_def ctF_def sign_eq0 combination_res_def
      combination_data_def mk_rep_def F0_def A0_def mk_equals_def fastype_of_def union_tpairs_def)

text \<open>
  The proofs of this theorem are defined: the classic one applies the axiom \<open>combination\<close> to
  the two reflexivity proofs, the tight one is an instance of the proof constant of the axiom
  with \<open>?'a\<close> and \<open>?'b\<close> both \<open>prop\<close>.
\<close>

lemma zaxiom_proof_return:
  assumes a: "a \<in> fst ` set zeq_vars"
  shows "\<exists>p. zaxiom_proof a Ts ts = return p"
proof -
  let ?vs = "snd (snd (zequality_axiom a))"
  let ?tab = "fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) ?vs zv_empty"
  let ?instT = "fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) (fst (snd (zequality_axiom a))) zt_empty"
  have e: "zequality_axm a = ((ZAxiom (STR ''Pure.'' + a), fst (zequality_axiom a)), (?instT, ?tab))"
    by (simp add: zequality_axm_def split: prod.splits)
  have l: "zv_lookup ?tab k = (if k \<in> set ?vs then Some (ZVar (fst k) (snd k)) else None)" for k
    by (simp add: zv_lookup_fold_update)
  from a have "a \<in> {STR ''reflexive'', STR ''symmetric'', STR ''transitive'', STR ''equal_intr'',
      STR ''equal_elim'', STR ''abstract_rule'', STR ''combination''}"
    by (simp add: zeq_vars_def)
  then have d: "distinct (map fst ?vs)"
    by (auto simp: zequality_axiom_def Let_def)
  have nok: "ztab_names_ok ?tab"
    unfolding ztab_names_ok_def
  proof (intro allI impI)
    fix k1 k2 assume "zv_lookup ?tab k1 \<noteq> None" "zv_lookup ?tab k2 \<noteq> None" "fst k1 = fst k2"
    then have "k1 \<in> set ?vs" "k2 \<in> set ?vs" "fst k1 = fst k2" by (simp_all add: l split: if_splits)
    with d show "k1 = k2" by (metis distinct_map inj_onD)
  qed
  let ?term = "\<lambda>t. case t of ZVar (x, _) _ \<Rightarrow> (case map_of ts x of Some u \<Rightarrow> u | None \<Rightarrow> t) | _ \<Rightarrow> t"
  from map_insts_return[OF nok, of "zsubst_tvar_names (map_of Ts)" ?term ?instT]
  obtain tab' where "map_insts (zsubst_tvar_names (map_of Ts)) (\<lambda>t. return (?term t)) (?instT, ?tab) =
    return (zt_map (zsubst_tvar_names (map_of Ts)) ?instT, tab')" by blast
  then show ?thesis by (simp add: zaxiom_proof_def make_const_proof_def e)
qed

lemma th_comb_proof:
  "th_proof th_comb = returnW (PAppp (PAppp (PAppt (PAppt (PAppt (PAppt (equality_axm STR ''combination'')
    (Some F0)) None) None) None) reflexive_proof) reflexive_proof)"
  by (simp add: th_comb_def th_reflF_def th_reflA_def conv_datar_def combination_proof_def beta_norm_def
      norm_term_def env_is_empty_def empty_env_def F0_def A0_def reflexive_proof_def equality_axm_def comb_arg_def
      Pure_reflexive vt_is_empty.rep_eq vt_empty.rep_eq)

lemma th_comb_zproof: "\<exists>z. th_zproof th_comb = return z"
proof -
  have "\<exists>p. zaxiom_proof a Ts ts = return p" if "a \<in> {STR ''reflexive'', STR ''combination''}" for a Ts ts
    by (rule zaxiom_proof_return) (use that in \<open>auto simp: zeq_vars_def\<close>)
  note r = this[of "STR ''reflexive''"] this[of "STR ''combination''"]
  obtain p where p: "zaxiom_proof STR ''reflexive'' [(tvar_a, ZFun ZProp ZProp)]
    [(STR ''x'', ZVar (STR ''f'', - 1) (ZFun ZProp ZProp))] = return p" using r(1) by blast
  obtain q where q: "zaxiom_proof STR ''reflexive'' [(tvar_a, ZProp)] [(STR ''x'', ZVar (STR ''A'', - 1) ZProp)] = return q"
    using r(1) by blast
  obtain ax where ax: "zaxiom_proof STR ''combination'' [(tvar_a, ZProp), (tvar_b, ZProp)]
    [(STR ''f'', ZVar (STR ''f'', - 1) (ZFun ZProp ZProp)), (STR ''g'', ZVar (STR ''f'', - 1) (ZFun ZProp ZProp)),
     (STR ''x'', ZVar (STR ''A'', - 1) ZProp), (STR ''y'', ZVar (STR ''A'', - 1) ZProp)] = return ax"
    using r(2) by blast
  show ?thesis
    by (simp add: th_comb_def th_reflF_def th_reflA_def conv_datar_def ctA_def ctF_def zreflexive_proof_def
      zcombination_proof_def A0_def F0_def propT_def p q ax)
qed

text \<open>So the judgments of proofs hold of them, in a signature that has all assumed properties:\<close>

theorem th_comb_proofs:
  obtains p z where "th_proof th_comb = returnW p" "th_zproof th_comb = return z"
    "prf_sig.prf_valid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] p (eq_const propT $ (F0 $ A0) $ (F0 $ A0))"
    "prf_sig.zvalid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] z (eq_const propT $ (F0 $ A0) $ (F0 $ A0))"
proof -
  obtain z where z: "th_zproof th_comb = return z" using th_comb_zproof by blast
  have "proofs_ok th_comb"
    by (rule derivable_proofs[OF derivable_th_comb]) (simp add: th_comb_def is_prf_sig0)
  then show thesis using that[OF th_comb_proof z]
    by (simp add: proofs_ok_def Let_def th_comb_proof z) (simp add: th_comb_def mk_rep_def)
qed

theorem thAA_proofs:
  "prf_sig.prf_valid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (AbsP STR ''H'' None (PBound 0)) (mk_implies A0 A0)"
  "prf_sig.zvalid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (ZAbsp STR ''H'' (ZVar (STR ''A'', -1) ZProp) (ZBoundp 0))
    (mk_implies A0 A0)"
proof -
  have "proofs_ok thAA"
    by (rule derivable_proofs[OF derivable_thAA]) (simp add: thAA_def is_prf_sig0)
  then show
    "prf_sig.prf_valid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (AbsP STR ''H'' None (PBound 0)) (mk_implies A0 A0)"
    "prf_sig.zvalid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (ZAbsp STR ''H'' (ZVar (STR ''A'', -1) ZProp) (ZBoundp 0))
      (mk_implies A0 A0)"
    by (simp_all add: proofs_ok_def Let_def thAA_def mk_rep_def)
qed

end
