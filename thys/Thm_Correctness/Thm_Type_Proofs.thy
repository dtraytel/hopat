section \<open>The proofs of theorems\<close>

theory Thm_Type_Proofs
  imports "Thm_Soundness.Thm_Type" Proof_Closed
begin

text \<open>
  The proofs of a theorem are valid, the classic one with non-negative indices of its schematic
  variables, the tight one with non-negative indices, canonical types and distinct names of the
  variables of the instances of its proof constants; their terms refer only to bound variables of
  abstractions of the proofs, and the hypotheses of the tight proof are encodings of propositions:
\<close>

definition proofs_ok :: "thm_data \<Rightarrow> bool" where
  "proofs_ok th \<longleftrightarrow> (let c = th_sign th in
    (\<forall>p. th_proof th = returnW p \<longrightarrow>
      prf_sig_gen.prf_valid (sg_alg c) (sg_ar c) (sg_consts c) (sg_close c) (sg_tyargs c) (sg_ax c)
        (set (th_hyps th)) (th_tpairs th) p (th_prop th) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p) \<and>
    (\<forall>z. th_zproof th = return z \<longrightarrow>
      prf_sig_gen.zvalid (sg_alg c) (sg_ar c) (sg_consts c) (sg_close c) (sg_tyargs c) (sg_ax c)
        (set (th_hyps th)) (th_tpairs th) z (th_prop th) \<and> zinv z \<and> znolb 0 z \<and>
      pure_sig_gen.zhyps_ok (sg_consts c) z))"

text \<open>
  The full invariant of theorems: the invariant \<^const>\<open>thm_sem\<close> of session \<open>Thm_Soundness\<close>
  (well-formed and valid in every model), and valid proofs if the signature is one for proofs:
\<close>

definition thm_ok :: "'u itself \<Rightarrow> thm_data \<Rightarrow> bool" where
  "thm_ok U th \<longleftrightarrow> thm_sem U th \<and> (is_prf_sig (th_sign th) \<longrightarrow> proofs_ok th)"

lemma thm_ok_sem: "thm_ok U th \<Longrightarrow> thm_sem U th"
  by (simp add: thm_ok_def)

lemma thm_ok_proofs: "thm_ok U th \<Longrightarrow> is_prf_sig (th_sign th) \<Longrightarrow> proofs_ok th"
  by (simp add: thm_ok_def)

lemma proofs_ok_with_cons [simp]: "proofs_ok (with_cons C d) \<longleftrightarrow> proofs_ok d"
  by (simp add: proofs_ok_def Let_def)

lemma thm_ok_with_cons [simp]: "thm_ok U (with_cons C d) \<longleftrightarrow> thm_ok U d"
  by (simp add: thm_ok_def)

context prf_sig
begin

text \<open>The \<open>\<beta>\<close>-normalization of a valid tight proof is valid:\<close>

lemma zvalid_beta_norm:
  assumes p: "zvalid ax H tps p \<phi>" and bn: "beta_norm_prooft p = Some p'" and H: "\<forall>h\<in>H. closed h"
  shows "zvalid ax H tps p' \<phi>"
proof -
  obtain w where w: "pcerase w = pcerase (zprf_tr p)" "prf_valid ax H tps w \<phi>" using p by (rule zvalidE)
  from beta_norm_prooft_wit[OF bn H w(1)] obtain w' where w': "pcerase w' = pcerase (zprf_tr p')"
    "prf_transfer ax H w w'" by blast
  have "prf_valid ax H tps w' \<phi>"
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    have "prf_ok ax H (pmap (ap \<rho> \<sigma>) (set tps)) e [] (prf_ap \<rho> \<sigma> w) (ap \<rho> \<sigma> \<phi>)"
      by (rule prf_validD[OF w(2) \<rho> \<sigma>])
    with w'(2) \<sigma> show "prf_ok ax H (pmap (ap \<rho> \<sigma>) (set tps)) e [] (prf_ap \<rho> \<sigma> w') (ap \<rho> \<sigma> \<phi>)" by blast
  qed
  with w'(1) show ?thesis by (rule zvalidI)
qed

lemma zsolve_ok:
  assumes z: "zsolve m = return z"
    and q: "\<And>q. m = return q \<Longrightarrow> zvalid ax H tps q \<phi> \<and> zinv q \<and> znolb 0 q \<and> zhyps_ok q"
    and H: "\<forall>h\<in>H. closed h"
  shows "zvalid ax H tps z \<phi> \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
proof -
  from z obtain p where m: "m = return p" and bn: "beta_norm_prooft p = Some z"
    by (auto simp: zsolve_def bindZ_eq_returnZ liftOZ_eq_returnZ)
  note v = q[OF m]
  have "zvalid ax H tps z \<phi>" by (rule zvalid_beta_norm[OF conjunct1[OF v] bn H])
  moreover have "zinv z" by (rule zinv_beta_norm_prooft[OF bn]) (use v in blast)
  moreover have "znolb 0 z" "zhyps z \<subseteq> zhyps p" using beta_norm_prooft_closed[OF bn, of 0] v by simp_all
  moreover have "zhyps_ok z" by (rule zhyps_ok_mono[OF _ \<open>zhyps z \<subseteq> zhyps p\<close>]) (use v in blast)
  ultimately show ?thesis by blast
qed

end

text \<open>Solving the sort constraints keeps the proofs valid:\<close>

lemma proofs_ok_solve_data:
  assumes sem: "thm_sem U d" and po: "proofs_ok d" and psig: "is_prf_sig (th_sign d)"
  shows "proofs_ok (solve_data d)"
proof -
  let ?c = "th_sign d"
  interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have "thm_wf (th_maxidx d) (th_hyps d) (th_tpairs d) (th_prop d)" using sem ps by (simp add: thm_sem_def)
  then have H: "\<forall>h\<in>set (th_hyps d). closed h" by (auto simp: thm_wf_def wt_thm_def dest: wtpD(1))
  show ?thesis unfolding proofs_ok_def Let_def solve_data_sel
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof d = returnW p"
    then show "prf_valid (sg_ax ?c) (set (th_hyps d)) (th_tpairs d) p (th_prop d) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      using po by (simp add: proofs_ok_def Let_def)
  next
    fix z assume z: "zsolve (th_zproof d) = return z"
    show "zvalid (sg_ax ?c) (set (th_hyps d)) (th_tpairs d) z (th_prop d) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (rule zsolve_ok[OF z _ H]) (use po in \<open>simp add: proofs_ok_def Let_def\<close>)
  qed
qed

lemma thm_ok_solve_data:
  assumes ok: "thm_ok U d"
  shows "thm_ok U (solve_data d)"
  using ok proofs_ok_solve_data[of U d] by (auto simp: thm_ok_def)

text \<open>The proofs of the new theorems of biresolution are valid:\<close>

lemma proofs_ok_thm_of_bres:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sg: "\<forall>r\<in>set brules. sign_of (snd r) = sign_of state"
    and cs: "thm_cons state" "\<forall>r\<in>set brules. thm_cons (snd r)"
    and br: "okT (biresolution trace match_flg rep_of brules i (rep_of state)) s0"
    and res: "pure_sig_gen.brresult (sg_alg (sign_of state)) (unify_ops cfg vl) rep_of s0 (x, (e, rule))"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
    and po_rule: "is_prf_sig (sign_of rule) \<Longrightarrow> proofs_ok (rep_thm rule)"
  shows "proofs_ok (thm_of_bres (sign_of state) i (state :: 'u pure_thm) e rule x)"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv[OF ps cs(1)] by simp
  have ru: "thm_inv (th_maxidx (rep_of r)) (hyps_of r) (th_tpairs (rep_of r)) (th_prop (rep_of r))"
    if "(e', r) \<in> set brules" for e' r
    using pure_thm_inv[of r] sg cs(2) that ps by fastforce
  interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def)
  have r: "(e, rule) \<in> set brules" by (rule biresolution_result[OF br res]) blast
  then have sr: "sign_of rule = ?c" using sg by fastforce
  have ps: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have pr: "proofs_ok (rep_thm rule)" by (rule po_rule) (simp add: sr psig)
  have sg_eq: "th_sign (thm_of_bres ?c i state e rule x) = ?c" by (simp add: thm_of_bres_def)
  show ?thesis unfolding proofs_ok_def Let_def sg_eq
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof (thm_of_bres ?c i state e rule x) = returnW p"
    then obtain rp sp where rp: "proof_of rule = returnW rp" and sp: "proof_of state = returnW sp"
      and p: "bires_proof (rep_of state) i e (rep_of rule) x rp sp = returnW p"
      by (auto simp: thm_of_bres_def bindP_eq_returnP)
    have "prf_valid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) p (br_prop x) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) p"
      by (rule biresolution_proof_valid[OF br res cfg vl st ru _ _ _ _ p])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    moreover have "prf_nolb 0 p"
      by (rule biresolution_proof_closed[OF br res cfg vl st ru _ _ p])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    ultimately show "prf_valid (sg_ax ?c)
        (set (th_hyps (thm_of_bres ?c i state e rule x))) (th_tpairs (thm_of_bres ?c i state e rule x)) p
        (th_prop (thm_of_bres ?c i state e rule x)) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_bres_def)
  next
    fix z assume "th_zproof (thm_of_bres ?c i state e rule x) = return z"
    then obtain rp sp where rp: "zproof_of rule = return rp" and sp: "zproof_of state = return sp"
      and z: "bires_zproof ztargs (rep_of state) i e (rep_of rule) x rp sp = return z"
      by (auto simp: thm_of_bres_def bindZ_eq_returnZ)
    have "zvalid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) z (br_prop x) \<and> zinv z"
      by (rule biresolution_zproof_valid[OF br res cfg vl st ru _ _ _ _ z])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    moreover have zs: "zinv sp" "znolb 0 sp" "zhyps_ok sp" "zinv rp" "znolb 0 rp" "zhyps_ok rp"
      using ps sp pr rp sr by (simp_all add: proofs_ok_def Let_def)
    note zc = biresolution_zproof_closed[OF br res cfg vl st ru zs(1) zs(4) zs(2) zs(5) z]
    have "znolb 0 z" by (rule zc(1))
    moreover have "zhyps z \<subseteq> zhyps sp \<union> zhyps rp" by (rule zc(2))
    then have "zhyps_ok z" using zs(3,6) by (auto simp: zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c)
        (set (th_hyps (thm_of_bres ?c i state e rule x))) (th_tpairs (thm_of_bres ?c i state e rule x)) z
        (th_prop (thm_of_bres ?c i state e rule x)) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: thm_of_bres_def)
  qed
qed

end
