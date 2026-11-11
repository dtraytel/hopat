section \<open>Lifting of rules and type variables on the abstract type of theorems\<close>

theory Thm_Rules4
  imports Thm_Rules3
begin

text \<open>
  \<open>Thm.lift_rule\<close> on \<^typ>\<open>'u pure_thm\<close>: the rule is lifted over the parameters and assumptions of
  a certified proposition (the goal), as biresolution does with a subgoal of the proof state;
  \<open>Thm.varifyT_global'\<close> with the renaming of its free type variables.
\<close>


subsection \<open>Additional sorts of a certified term\<close>

text \<open>
  \<open>Thm.weaken_sorts raw_sorts ct\<close> adds sorts to those of a certified term; \<open>Sign.certify_sort\<close>
  raises an exception unless their classes are declared (it returns the sort unchanged).
\<close>

definition weaken_sorts_cterm :: "psort list \<Rightarrow> pure_cterm \<Rightarrow> pure_cterm option" where
  "weaken_sorts_cterm Ss ct =
    (if \<forall>S\<in>set Ss. sort_ok (sg_alg (csign_of ct)) S
     then Some (Abs_cterm (rep_cterm ct\<lparr>cd_sorts := csorts_of ct \<union> set Ss\<rparr>)) else None)"

theorem weaken_sorts_cterm:
  assumes "weaken_sorts_cterm Ss ct = Some ct'"
  shows "crep_of ct' = crep_of ct" "csign_of ct' = csign_of ct" "csorts_of ct' = csorts_of ct \<union> set Ss"
    "\<forall>S\<in>set Ss. sort_ok (sg_alg (csign_of ct)) S"
proof -
  have ok: "cterm_ok (rep_cterm ct\<lparr>cd_sorts := csorts_of ct \<union> set Ss\<rparr>)"
    using rep_cterm[of ct] by (simp add: cterm_ok_def)
  have S: "\<forall>S\<in>set Ss. sort_ok (sg_alg (csign_of ct)) S"
    and ct': "ct' = Abs_cterm (rep_cterm ct\<lparr>cd_sorts := csorts_of ct \<union> set Ss\<rparr>)"
    using assms by (simp_all add: weaken_sorts_cterm_def split: if_splits)
  have r: "rep_cterm ct' = rep_cterm ct\<lparr>cd_sorts := csorts_of ct \<union> set Ss\<rparr>"
    unfolding ct' by (rule Abs_cterm_inverse) (use ok in simp)
  show "crep_of ct' = crep_of ct" "csign_of ct' = csign_of ct" "csorts_of ct' = csorts_of ct \<union> set Ss"
    by (simp_all add: r)
  show "\<forall>S\<in>set Ss. sort_ok (sg_alg (csign_of ct)) S" by (rule S)
qed

lemma weaken_sorts_cterm_defined:
  "(\<forall>S\<in>set Ss. sort_ok (sg_alg (csign_of ct)) S) \<Longrightarrow> weaken_sorts_cterm Ss ct \<noteq> None"
  by (simp add: weaken_sorts_cterm_def)


subsection \<open>Lifting a rule over a goal\<close>

context pure_sig
begin

lemma lift_rule_thm_wf:
  assumes G: "wtp G" "ibelow smax G" and sm: "-1 \<le> smax"
    and rule: "thm_wf (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and nnG: "\<forall>v\<in>vars G. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars G. 0 \<le> snd (fst v)"
  shows "thm_wf (th_maxidx (lift_rule G smax rule)) hr (th_tpairs (lift_rule G smax rule))
    (th_prop (lift_rule G smax rule))"
proof -
  let ?lr = "lift_rule G smax rule"
  obtain p G0 where sp: "lsplit G = (p, G0)" by (cases "lsplit G")
  have wr: "wt_thm (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)" and rm: "-1 \<le> th_maxidx rule"
    and nn: "\<forall>v\<in>vars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd (fst v)"
      "\<forall>v\<in>tvars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd (fst v)"
    using rule by (simp_all add: thm_wf_def)
  have P: "e \<turnstile> th_prop rule : propT" for e using wr by (simp add: wt_thm_def wtpD(2))
  have "wt_thm (th_maxidx ?lr) hr (th_tpairs ?lr) (th_prop ?lr)" by (rule lift_rule_wt_thm[OF wr G rm])
  moreover have "-1 \<le> th_maxidx ?lr" using rm sm by (simp add: lift_rule_maxidx)
  moreover have "\<forall>v\<in>vars_thm (th_tpairs ?lr) (th_prop ?lr). 0 \<le> snd (fst v)"
  proof
    fix v assume v: "v \<in> vars_thm (th_tpairs ?lr) (th_prop ?lr)"
    obtain x i T where vT: "v = ((x, i), T)" by (cases v) auto
    from lift_rule_vars[OF sp v[unfolded vT]] show "0 \<le> snd (fst v)"
    proof
      assume "((x, i), T) \<in> vars G"
      with nnG(1) show ?thesis by (force simp: vT)
    next
      assume "\<exists>T0. ((x, i - (smax + 1)), T0) \<in> vars_thm (th_tpairs rule) (th_prop rule) \<and>
        T = foldr fun_type (ptys p) (incr_tvar (smax + 1) T0)"
      then obtain T0 where "((x, i - (smax + 1)), T0) \<in> vars_thm (th_tpairs rule) (th_prop rule)" by blast
      with nn(1) have "0 \<le> i - (smax + 1)" by force
      with sm show ?thesis by (simp add: vT)
    qed
  qed
  moreover have "\<forall>v\<in>tvars_thm (th_tpairs ?lr) (th_prop ?lr). 0 \<le> snd (fst v)"
  proof
    fix v assume v: "v \<in> tvars_thm (th_tpairs ?lr) (th_prop ?lr)"
    obtain a i S where vS: "v = ((a, i), S)" by (cases v) auto
    from lift_rule_tvars[OF sp P v[unfolded vS]] show "0 \<le> snd (fst v)"
    proof
      assume "((a, i), S) \<in> ttvars G"
      with nnG(2) show ?thesis by (force simp: vS)
    next
      assume "((a, i - (smax + 1)), S) \<in> tvars_thm (th_tpairs rule) (th_prop rule)"
      with nn(2) have "0 \<le> i - (smax + 1)" by force
      with sm show ?thesis by (simp add: vS)
    qed
  qed
  ultimately show ?thesis by (simp add: thm_wf_def)
qed

text \<open>A certified proposition can be lifted over:\<close>

lemma cterm_wf_goal:
  assumes "cterm_wf ct" "ct_T ct = propT"
  shows "wtp (ct_t ct)" "ibelow (ct_maxidx ct) (ct_t ct)" "-1 \<le> ct_maxidx ct" "pnn (ct_t ct)"
    "\<forall>v\<in>vars (ct_t ct). 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars (ct_t ct). 0 \<le> snd (fst v)"
  using assms by (auto simp: cterm_wf_def pnn_iff' intro: wtpI[of _ "\<lambda>_. propT"])

end

text \<open>
  \<open>lift_rule_thm goal orule\<close> (\<open>Thm.lift_rule\<close> of the wrapper): \<open>None\<close> if the goal does not have
  type \<open>prop\<close> or the signatures differ. The sort hypotheses of the result include the sorts of
  the goal.
\<close>

definition lift_rule_data :: "pure_cterm \<Rightarrow> 'u pure_thm \<Rightarrow> thm_data" where
  "lift_rule_data ct th =
    (let G = ct_t (crep_of ct); gmax = ct_maxidx (crep_of ct)
     in with_cons (cons_of th) (mk_thm (lift_rule G gmax (rep_of th)) (shyps_of th \<union> csorts_of ct) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (lift_rule_proof G gmax (rep_of th) p)))
      (bindM (zproof_of th) (lift_rule_zproof (pure_sig.ztargs (sg_consts (sign_of th))) G gmax (rep_of th)))))"

definition lift_rule_thm :: "pure_cterm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "lift_rule_thm ct th =
    (if ct_T (crep_of ct) = propT \<and> csign_of ct = sign_of th then Some (Abs_thm (lift_rule_data ct th))
     else None)"

lemma lift_rule_data_sel [simp]:
  "th_maxidx (lift_rule_data ct th) = th_maxidx (lift_rule (ct_t (crep_of ct)) (ct_maxidx (crep_of ct)) (rep_of th))"
  "th_tpairs (lift_rule_data ct th) = th_tpairs (lift_rule (ct_t (crep_of ct)) (ct_maxidx (crep_of ct)) (rep_of th))"
  "th_prop (lift_rule_data ct th) = th_prop (lift_rule (ct_t (crep_of ct)) (ct_maxidx (crep_of ct)) (rep_of th))"
  "th_shyps (lift_rule_data ct th) = shyps_of th \<union> csorts_of ct"
  "th_hyps (lift_rule_data ct th) = hyps_of th" "th_sign (lift_rule_data ct th) = sign_of th"
  by (simp_all add: lift_rule_data_def Let_def)

lemma thm_ok_lift_rule:
  fixes th :: "'u pure_thm"
  assumes T: "ct_T (crep_of ct) = propT" and c: "csign_of ct = sign_of th"
  shows "thm_ok TYPE('u) (lift_rule_data ct th)"
proof -
  let ?c = "sign_of th" and ?G = "ct_t (crep_of ct)" and ?gmax = "ct_maxidx (crep_of ct)"
  let ?r = "rep_of th"
  let ?lr = "lift_rule ?G ?gmax ?r"
  have rs: "th_maxidx ?r = th_maxidx (rep_thm th)" "th_tpairs ?r = th_tpairs (rep_thm th)"
    "th_prop ?r = th_prop (rep_thm th)" by simp_all
  have common: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (crep_of ct) \<and>
      pure_sig.thm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (th_maxidx ?r) (hyps_of th) (th_tpairs ?r) (th_prop ?r)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
    using pure_cterm_wf[of ct] pure_thm_wf[of th] ps c by simp
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign (lift_rule_data ct th))) (sg_ar (th_sign (lift_rule_data ct th)))"
    then have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps')
    note cm = cterm_wf_goal[OF conjunct1[OF common[OF ps']] T] conjunct2[OF common[OF ps']]
    have "thm_wf (th_maxidx ?lr) (hyps_of th) (th_tpairs ?lr) (th_prop ?lr)"
      by (rule lift_rule_thm_wf) (use cm in simp_all)
    then show "pure_sig.thm_wf (sg_alg (th_sign (lift_rule_data ct th))) (sg_ar (th_sign (lift_rule_data ct th)))
        (sg_consts (th_sign (lift_rule_data ct th))) (th_maxidx (lift_rule_data ct th)) (th_hyps (lift_rule_data ct th))
        (th_tpairs (lift_rule_data ct th)) (th_prop (lift_rule_data ct th))"
      by simp
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign (lift_rule_data ct th))) (sg_ar (th_sign (lift_rule_data ct th)))"
      and M: "is_model (th_sign (lift_rule_data ct th)) M"
    then have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" and M': "is_model ?c M" by simp_all
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD[OF M'])
    note cm = cterm_wf_goal[OF conjunct1[OF common[OF ps']] T] conjunct2[OF common[OF ps']]
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs ?r) (th_prop ?r)"
      using pure_thm_valid[OF M'] by (simp add: valid_in_def)
    have w: "wt_thm (th_maxidx ?r) (hyps_of th) (th_tpairs ?r) (th_prop ?r)"
      using cm by (simp add: thm_wf_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs ?lr) (th_prop ?lr)"
      by (rule lift_rule_valid[OF v w]) (use cm in simp)
    then have "valid (shyps_of th \<union> csorts_of ct) (hyps_of th) (th_tpairs ?lr) (th_prop ?lr)"
      by (rule valid_mono) blast
    then show "valid_in (th_sign (lift_rule_data ct th)) M (th_shyps (lift_rule_data ct th))
        (th_hyps (lift_rule_data ct th)) (th_tpairs (lift_rule_data ct th)) (th_prop (lift_rule_data ct th))"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign (lift_rule_data ct th))"
    then have psig': "is_prf_sig ?c" by simp
    interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      using psig' by (simp add: is_prf_sig_def)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig' by (simp add: is_prf_sig_def prf_sig_def)
    note cm = cterm_wf_goal[OF conjunct1[OF common[OF ps']] T] conjunct2[OF common[OF ps']]
    have wG: "wtp ?G" and sm: "-1 \<le> ?gmax" and pG: "pnn ?G" using cm by simp_all
    have wfr: "thm_wf (th_maxidx ?r) (hyps_of th) (th_tpairs ?r) (th_prop ?r)" using cm by simp
    have w: "wt_thm (th_maxidx ?r) (hyps_of th) (th_tpairs ?r) (th_prop ?r)" using wfr by (simp add: thm_wf_def)
    have wfl: "thm_wf (th_maxidx ?lr) (hyps_of th) (th_tpairs ?lr) (th_prop ?lr)"
      by (rule lift_rule_thm_wf) (use cm in simp_all)
    have lw: "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)" if "(t, u) \<in> set (th_tpairs ?lr)" for t u
      using wfl that by (fastforce simp: thm_wf_def wt_thm_def)
    have pok: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok[OF psig'])
    let ?prems = "map (lift_all (?gmax + 1) ?G) (strip_imp_prems (th_prop ?r))"
    have lrP: "th_prop ?lr = list_implies ?prems (lift_all (?gmax + 1) ?G (strip_imp_concl (th_prop ?r)))"
      by (simp add: lift_rule_def Let_def)
    have wP: "wtp (th_prop ?lr)" using wfl by (simp add: thm_wf_def wt_thm_def)
    have pP: "pnn (th_prop ?lr)" using wfl by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
    have prem: "wtp A \<and> pnn A" if "A \<in> set ?prems" for A
      using wtp_list_implies_mem[OF wP[unfolded lrP] that] pP[unfolded lrP pnn_list_implies] that by blast
    show "proofs_ok (lift_rule_data ct th)" unfolding proofs_ok_def Let_def lift_rule_data_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "th_proof (lift_rule_data ct th) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = lift_rule_proof ?G ?gmax ?r q"
        by (auto simp: lift_rule_data_def Let_def bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs ?r) q (th_prop ?r)"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using pok q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs ?lr) pf (th_prop ?lr)"
        unfolding pf lift_rule_proof_def lift_rule_prems_def
        by (rule prf_valid_lift_proof[OF vq(1) w wG lw])
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
        unfolding pf lift_rule_proof_def by (rule prf_nonneg_lift_proof[OF vq(2) sm])
      moreover have "prf_nolb 0 pf"
        unfolding pf lift_rule_proof_def by (rule prf_nolb_lift_proof[OF vq(3)])
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs ?lr) pf (th_prop ?lr) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
        by blast
    next
      fix z assume "th_zproof (lift_rule_data ct th) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "lift_rule_zproof ztargs ?G ?gmax ?r q = return z"
        by (auto simp: lift_rule_data_def Let_def bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs ?r) q (th_prop ?r)" "zinv q" "znolb 0 q"
        "zhyps_ok q"
        using pok q by (simp_all add: proofs_ok_def Let_def)
      have zl: "zlift_proof ztargs ?G (?gmax + 1) ?prems q = return z"
        using z by (simp add: lift_rule_zproof_def lift_rule_prems_def)
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs ?lr) z (th_prop ?lr)"
      proof (rule zvalid_zlift_proof[OF vq(1) w wG lw _ _ _ _ _ zl])
        show "zconsts_ok q" "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp_all add: zinv_def)
        show "0 \<le> ?gmax + 1" using sm by simp
        show "zlift_ok ?G" by (rule zlift_ok_typed[OF wtpD(2)[OF wG] pG])
        show "\<forall>A\<in>set ?prems. \<exists>z. zterm_of ztargs A = return z \<and> zdec z = A"
          using prem zterm_of_zdec_pnn wtpD(2) by blast
      qed
      moreover have "zinv z" by (rule zinv_zlift_proof[OF zl vq(2) _ pG]) (use sm prem in auto)
      moreover have zc: "znolb 0 z \<and> zhyps z \<subseteq> zhyps q"
        using zlift_proof_closed[OF zl _ vq(3) wtpD(1)[OF wG]] vq(2) prem wtpD(1) by (simp add: zinv_def)
      moreover have "zhyps_ok z" using zc vq(4) by (auto simp: zhyps_ok_def)
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs ?lr) z (th_prop ?lr) \<and> zinv z \<and>
          znolb 0 z \<and> zhyps_ok z"
        by blast
    qed
  qed
qed

theorem lift_rule_thm:
  assumes "lift_rule_thm ct th = Some th'"
  shows "ct_T (crep_of ct) = propT" "csign_of ct = sign_of th" "rep_thm th' = lift_rule_data ct th"
proof -
  show T: "ct_T (crep_of ct) = propT" and c: "csign_of ct = sign_of th"
    using assms by (simp_all add: lift_rule_thm_def split: if_splits)
  have "th' = Abs_thm (lift_rule_data ct th)" using assms T c by (simp add: lift_rule_thm_def)
  then show "rep_thm th' = lift_rule_data ct th"
    using rep_Abs_thm[OF thm_ok_lift_rule[OF T c]] by (simp add: lift_rule_data_def Let_def)
qed

text \<open>The lifted rule is defined for every goal of type \<open>prop\<close> of the signature of the rule:\<close>

lemma lift_rule_thm_defined:
  "ct_T (crep_of ct) = propT \<Longrightarrow> csign_of ct = sign_of th \<Longrightarrow> lift_rule_thm ct th \<noteq> None"
  by (simp add: lift_rule_thm_def)


subsection \<open>Generalization of type variables with their renaming\<close>

text \<open>
  \<open>Thm.varifyT_global' fixed\<close> returns, besides the theorem of \<^const>\<open>varifyT_global_thm\<close>, the
  renaming of the free type variables (not fixed, not in the hypotheses) to the schematic ones.
\<close>

definition varifyT_global'_thm :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> (name \<times> psort) list \<Rightarrow>
    'u pure_thm \<Rightarrow> (((name \<times> psort) \<times> (indexname \<times> psort)) list \<times> 'u pure_thm) option" where
  "varifyT_global'_thm vl fixed th =
    (if sign_closed (sign_of th) then
      map_option (\<lambda>(names, r). (names, Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names))))))
        (resT (varifyT_global vl fixed (hyps_of th) (rep_of th)))
     else None)"

lemma varifyT_global_thm_snd: "varifyT_global_thm vl fixed th = map_option snd (varifyT_global'_thm vl fixed th)"
  by (simp add: varifyT_global_thm_def varifyT_global'_thm_def option.map_comp comp_def case_prod_unfold)

theorem varifyT_global'_thm:
  assumes "varifyT_global'_thm vl fixed th = Some (names, th')"
  obtains r where "okT (varifyT_global vl fixed (hyps_of th) (rep_of th)) (names, r)" "sign_closed (sign_of th)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names)))"
proof -
  from assms obtain r where sc: "sign_closed (sign_of th)"
    and ok: "okT (varifyT_global vl fixed (hyps_of th) (rep_of th)) (names, r)"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names))))"
    by (auto simp: varifyT_global'_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok sc]) (use thm_ok_varifyT_global[OF ok sc] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed

end
