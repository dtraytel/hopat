section \<open>Problems with Type Variables: Completeness of Copying\<close>

theory Unify_Poly_Copy
  imports Unify_Poly_Simpl_Complete
begin

text \<open>
  The completeness of \<open>matchcopy\<close> for problems with type variables. The solution \<open>(\<rho>, \<sigma>)\<close> and the
  typing \<open>W\<close> are extended by the new variables; the semantic arguments are those of the
  monomorphic case on the ground instance (theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Match_Complete\<close>).
\<close>


subsection \<open>Extending the solution and the typing\<close>

lemma has_type_vars_cong: "has_type V Ts t T \<Longrightarrow> (\<And>x. x \<in> vars t \<Longrightarrow> V' x = V x) \<Longrightarrow> has_type V' Ts t T"
  by (induction rule: has_type.induct) (auto intro: has_type.intros)

lemma typed_tctx_cong:
  assumes "typed env W Ts t T" "tyenv env' = tyenv env" "\<And>x. x \<in> vars t \<Longrightarrow> tctx env' W' x = tctx env W x"
  shows "typed env' W' Ts t T"
  using has_type_vars_cong[OF assms(1)[unfolded typed_def], of "tctx env' W'"] assms(2,3)
  by (simp add: typed_def)

abbreviation imap :: "tinst \<Rightarrow> (indexname \<times> ptyp \<times> dB) list \<Rightarrow> (indexname \<times> ptyp \<times> dB) list" where
  "imap \<rho> ys \<equiv> map (\<lambda>(x, G, w). (x, tsubst \<rho> G, w)) ys"

lemma map_of_imap: "map_of (imap \<rho> ys) y = map_option (\<lambda>(G, w). (tsubst \<rho> G, w)) (map_of ys y)"
  by (induction ys) auto

lemma ext_subst_imap: "ext_subst \<sigma> (imap \<rho> ys) = ext_subst \<sigma> ys"
proof
  fix n
  have "map (\<lambda>(x, T, w). (code (AVar x), w)) (imap \<rho> ys) = map (\<lambda>(x, T, w). (code (AVar x), w)) ys"
    by (induction ys) auto
  then show "ext_subst \<sigma> (imap \<rho> ys) n = ext_subst \<sigma> ys n" by (simp only: ext_subst_def)
qed

text \<open>
  New variables \<open>x\<close> of types \<open>G\<close> with values \<open>w\<close>, all newer than the environment, extend the
  solution \<open>\<sigma>\<close> and the typing \<open>W\<close>.
\<close>

lemma pcinv_extend_vars:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and e1: "tenv env1 = tenv env" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1"
    and ys: "\<And>x G w. (x, G, w) \<in> set ys \<Longrightarrow> maxidx env < snd x \<and> tyw ar (tyenv env) A G \<and>
      no_loose_bound w 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> w : trty (tsubst \<rho> G))"
  shows "pcinv alg ar A (ext_typ W ys) \<rho> \<tau>' (ext_subst \<sigma> ys) env1 dps"
    "agree (maxidx env) \<sigma> (ext_subst \<sigma> ys)" "agreeV (maxidx env) W (ext_typ W ys)"
    "ityp \<rho> env1 (ext_typ W ys) = ext_typ (ityp \<rho> env W) (imap \<rho> ys)"
proof -
  let ?\<theta> = "tyenv env" and ?W1 = "ext_typ W ys" and ?\<sigma>1 = "ext_subst \<sigma> ys"
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have yi: "maxidx (instE \<rho> env) < snd x \<and> no_loose_bound w 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> w : trty G)"
    if "(x, G, w) \<in> set (imap \<rho> ys)" for x G w
    using that ys by auto
  have frI: "fresh_env (instE \<rho> env)" using ei(6) by simp
  note se = solution_extend[of "ityp \<rho> env W" \<tau>' \<sigma> "instE \<rho> env" "imap \<rho> ys", OF pc0(3) frI yi,
    unfolded ext_subst_imap]
  show ag: "agree (maxidx env) \<sigma> ?\<sigma>1" using se(2) by simp
  have nb: "map_of ys y = None" if "snd y \<le> maxidx env" for y
  proof (rule ccontr)
    assume "map_of ys y \<noteq> None"
    then obtain G w where "map_of ys y = Some (G, w)" by auto
    then have "(y, G, w) \<in> set ys" by (rule map_of_SomeD)
    from ys[OF this] that show False by simp
  qed
  show agV: "agreeV (maxidx env) W ?W1" unfolding agreeV_def using nb by (simp add: ext_typ_simp)
  have bnd: "snd y \<le> maxidx env" if "vt_lookup (tenv env) y = Some (U, u)" for y U u
    using fresh_envD[OF ei(6) that] by simp
  have W1old: "?W1 y = W y" if "snd y \<le> maxidx env" for y using nb[OF that] by (simp add: ext_typ_simp)
  have tw1: "tyw ar ?\<theta> A (?W1 y)" for y
  proof (cases "map_of ys y")
    case (Some p)
    then obtain G w where "map_of ys y = Some (G, w)" by (cases p) auto
    moreover from map_of_SomeD[OF this] have "tyw ar ?\<theta> A G" using ys by blast
    ultimately show ?thesis by (simp add: ext_typ_simp)
  qed (simp add: ext_typ_simp pi(5))
  have wc1: "wcons ?W1 env1"
    using pi(6) e1(1,2) bnd W1old unfolding wcons_def by (metis (no_types, lifting))
  have tctx1: "tctx env1 ?W1 y = tctx env W y" if "snd y \<le> maxidx env" for y
    using wcons_tctx[OF wc1] wcons_tctx[OF pi(6)] W1old[OF that] e1(2) by simp
  have typed1: "typed env1 ?W1 Ts t T" if "typed env W Ts t T" "below (maxidx env) t" for Ts t T
    by (rule typed_tctx_cong[OF that(1) e1(2)]) (use that(2) tctx1 in \<open>auto simp: below_def\<close>)
  show "ityp \<rho> env1 ?W1 = ext_typ (ityp \<rho> env W) (imap \<rho> ys)"
  proof
    fix y
    show "ityp \<rho> env1 ?W1 y = ext_typ (ityp \<rho> env W) (imap \<rho> ys) y"
    proof (cases "map_of ys y")
      case None
      then have "?W1 y = W y" by (simp add: ext_typ_simp)
      moreover have "tctx env1 ?W1 y = tnorm ?\<theta> (?W1 y)" "tctx env W y = tnorm ?\<theta> (W y)"
        using wcons_tctx[OF wc1] wcons_tctx[OF pi(6)] e1(2) by simp_all
      ultimately show ?thesis using None by (simp add: ext_typ_simp map_of_imap)
    next
      case (Some p)
      then obtain G w where m: "map_of ys y = Some (G, w)" by (cases p) auto
      from map_of_SomeD[OF m] ys have tG: "tyw ar ?\<theta> A G" by blast
      have "tctx env1 ?W1 y = tnorm ?\<theta> G" using wcons_tctx[OF wc1] m e1(2) by (simp add: ext_typ_simp)
      then show ?thesis using m tsubst_tnorm[OF ac sol tyw_tcons[OF pi(2) tG]]
        by (simp add: ext_typ_simp map_of_imap)
    qed
  qed
  note it1 = this
  have "penv_inv alg ar ?W1 env1"
    unfolding penv_inv_def
  proof (intro conjI)
    show "tinv ar (maxidx env1) (tyenv env1) (etvars env1)"
      using tinv_mono[OF ei(1) e1(3)] e1 etys_same_tenv[OF e1(1)] by (simp add: etvars_def)
    show "tsorted alg (tyenv env1)" using ei(2) e1(2) by simp
    show "nacyc env1" using ei(3) nacyc_same_tenv[OF e1(1)] by simp
    show "pwf_env ar env1" using ei(4) e1(1) by (simp add: pwf_env_def)
    show "wt_env ?W1 env1"
      using pi(1) e1(1) fresh_envD[OF ei(6)] typed1 by (auto simp: penv_inv_def wt_env_def)
    show "fresh_env env1" by (rule fresh_env_same[OF e1(1,3) ei(6)])
  qed
  moreover have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar (tyenv env1) A T) \<and> ptyped env1 ?W1 dp \<and>
      dp_below (maxidx env1) dp \<and> dsolved ?\<sigma>1 (instd \<rho> dp)" if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from pi(4)[OF dp] dpe obtain T where w: "swf_dp ar dp" "\<forall>T\<in>dtys dp. tyw ar ?\<theta> A T"
      and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T"
      and bl: "below (maxidx env) t" "below (maxidx env) u" by auto
    have "dsolved ?\<sigma>1 (instd \<rho> dp)"
      using pc0(4)[OF dp] dpe mk_subst_agree[OF _ ag, of "inst \<rho> (rlist_abs rb t)"]
        mk_subst_agree[OF _ ag, of "inst \<rho> (rlist_abs rb u)"] bl
      by (simp add: dsolved_def below_rlist_abs inst_rlist_abs[symmetric])
    then show ?thesis using w e1 typed1[OF ty(1) bl(1)] typed1[OF ty(2) bl(2)] bl below_mono[OF _ e1(3)] dpe
      by auto
  qed
  moreover have "solution (ityp \<rho> env1 ?W1) \<tau>' ?\<sigma>1 (instE \<rho> env1)"
    using se(1) instE_same_tenv[OF e1(1), of \<rho>] it1 by (simp add: solution_def sat_def)
  ultimately show "pcinv alg ar A ?W1 \<rho> \<tau>' ?\<sigma>1 env1 dps"
    using pi(2,3) tw1 wc1 pc0(2) e1 tinv_mono[OF pi(2) e1(3)] etys_same_tenv[OF e1(1)]
    by (auto simp: pcinv_def pinv_def simp del: split_paired_All)
qed

end
