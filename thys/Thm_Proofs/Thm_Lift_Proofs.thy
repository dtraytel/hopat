section \<open>Proofs: Thm_Lift\<close>

theory Thm_Lift_Proofs
  imports "Thm_Soundness.Thm_Lift" Thm_Assumption_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Lift\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

lemma proofs_ok_lift_rule:
  fixes th :: "'u pure_thm"
  assumes T: "ct_T (crep_of ct) = propT" and c: "csign_of ct = sign_of th"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (lift_rule_data ct th)) \<Longrightarrow>
    proofs_ok (lift_rule_data ct th)"
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
  have pok: "proofs_ok (rep_thm th)" by (rule po_th[OF psig'])
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

end
