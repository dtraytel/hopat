section \<open>The Proofs of the Example Derivations\<close>

theory Thm_Example_Proofs
  imports Thm_Derivable_Proofs "Thm_Soundness.Thm_Clash_Example"
begin

text \<open>
  The proofs of the derivations of theories \<open>Thm_Example\<close> and \<open>Thm_Clash_Example\<close> (session
  \<open>Thm_Soundness\<close>) are valid.
\<close>

subsection \<open>The derivations with their proofs\<close>

text \<open>
  The derivations of theory \<open>Thm_Example\<close> and the proof by assumption of theory
  \<open>Thm_Clash_Example\<close> again, by the rules of \<^const>\<open>pderivable\<close>: the data of these theorems
  have the proofs that the rules construct.
\<close>

lemma pderivable_thA: "pderivable thA"
  using pderivable.assumeI[OF cterm_ok_ctA, of "mk_rep (-1) [] A0"]
  by (simp add: thA_def ctA_def assume_rule_def adjust_maxidx_cterm_def zassume_proof_def A0_def propT_def)

lemma pderivable_thAA: "pderivable thAA"
  using pderivable.implies_intr[OF cterm_ok_ctA _ pderivable_thA, of "mk_rep (-1) [] (mk_implies A0 A0)"]
  by (simp add: thAA_def implies_intr_def implies_intr_proof_def zimplies_intr_proof_def ctA_def thA_def
      mk_rep_def A0_def propT_def)

lemma pderivable_th_reflA: "pderivable th_reflA"
  unfolding th_reflA_def
  by (rule pderivable.reflexive[OF cterm_ok_ctA])
    (simp_all add: sign_eq0 ctA_def reflexive_def mk_rep_def A0_def mk_equals_def fastype_of_def)

lemma pderivable_th_reflF: "pderivable th_reflF"
  unfolding th_reflF_def
  by (rule pderivable.reflexive[OF cterm_ok_ctF])
    (simp_all add: sign_eq0 ctF_def reflexive_def mk_rep_def F0_def mk_equals_def fastype_of_def)

lemma pderivable_th_comb: "pderivable th_comb"
  using pderivable.combination[OF pderivable_th_reflF pderivable_th_reflA,
    of "mk_rep (-1) [] (eq_const propT $ (F0 $ A0) $ (F0 $ A0))" propT propT F0 F0 A0 A0]
  by (simp add: th_comb_def th_reflF_def th_reflA_def conv_datar_def ctA_def ctF_def sign_eq0 combination_res_def
      combination_data_def mk_rep_def F0_def A0_def mk_equals_def fastype_of_def union_tpairs_def)

lemma pderivable_st1: "pderivable st1"
  using pderivable.trivial[OF cterm_ok_ct1, of "mk_rep 0 [] (mk_implies (mk_implies H1 Vy) (mk_implies H1 Vy))"]
  by (simp add: st1_def ct1_def trivial_def)

lemma pderivable_clash: "pderivable (ares_data st1 (aseq_ctx s1) r1)"
  by (rule pderivable.assumption[OF pderivable_st1 _ scons_st1 assumption1 aresult.First[OF a1]])
    (simp_all add: cfg1_def st1_def)


subsection \<open>The example signature\<close>

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
    "prf_sig_gen.prf_valid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] p (eq_const propT $ (F0 $ A0) $ (F0 $ A0))"
    "prf_sig_gen.zvalid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] z (eq_const propT $ (F0 $ A0) $ (F0 $ A0))"
proof -
  obtain z where z: "th_zproof th_comb = return z" using th_comb_zproof by blast
  have "proofs_ok th_comb"
    by (rule derivable_proofs[OF pderivable_th_comb]) (simp add: th_comb_def is_prf_sig0)
  then show thesis using that[OF th_comb_proof z]
    by (simp add: proofs_ok_def Let_def th_comb_proof z) (simp add: th_comb_def mk_rep_def)
qed

theorem thAA_proofs:
  "prf_sig_gen.prf_valid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (AbsP STR ''H'' None (PBound 0)) (mk_implies A0 A0)"
  "prf_sig_gen.zvalid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (ZAbsp STR ''H'' (ZVar (STR ''A'', -1) ZProp) (ZBoundp 0))
    (mk_implies A0 A0)"
proof -
  have "proofs_ok thAA"
    by (rule derivable_proofs[OF pderivable_thAA]) (simp add: thAA_def is_prf_sig0)
  then show
    "prf_sig_gen.prf_valid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (AbsP STR ''H'' None (PBound 0)) (mk_implies A0 A0)"
    "prf_sig_gen.zvalid alg0 (\<lambda>_. 0) ctab0 close0 tyargs0 ax0 {} [] (ZAbsp STR ''H'' (ZVar (STR ''A'', -1) ZProp) (ZBoundp 0))
      (mk_implies A0 A0)"
    by (simp_all add: proofs_ok_def Let_def thAA_def mk_rep_def)
qed

subsection \<open>A theorem with a variable name at two types\<close>

text \<open>Hence it satisfies the invariant of theorems:\<close>

corollary dok_clash: "dok TYPE('u) (ares_data st1 (aseq_ctx s1) r1)"
  by (rule derivable_sound[OF pderivable_clash])

end
