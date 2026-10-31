section \<open>Problems with Type Variables: Termination of the Simplification Phase\<close>

theory Unify_Poly_Simpl_Term
  imports Unify_Poly_Complete Unify_Simpl_Term
begin

context wf_csig
begin

text \<open>
  \<^const>\<open>SIMPL0\<close> and \<^const>\<open>SIMPL\<close> terminate on every problem with type variables in the
  invariant \<^const>\<open>pinv\<close>, solvable or not: they return a state or raise \<open>CANTUNIFY\<close>. This is the
  analogue of theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Simpl_Term\<close>. The measure works on a
  ground instance, under a ground solution of the type environment and the canonical solution of
  the instance of the environment; it is lexicographic in the number of unbound type variables
  of the problem, which decreases whenever the type environment changes, the number of unbound
  variables of the instance reachable from the pair, and the size \<^const>\<open>dsz\<close> of the instance of
  the pair.
\<close>

subsection \<open>Ground instances\<close>

lemma pinv_gsol_exists:
  assumes "pinv alg ar A W env dps"
  obtains \<rho> where "gsol alg ar (tyenv env) \<rho>"
  using gsol_exists[OF pinvD(2)[OF assms] penv_invD(2)[OF pinvD(1)[OF assms]]] by blast

text \<open>The canonical solution of the ground instance of the environment.\<close>

lemma pinv_env_sol:
  assumes "pinv alg ar A W env dps" "gsol alg ar (tyenv env) \<rho>"
  shows "solution (ityp \<rho> env W) (tau (ityp \<rho> env W)) (env_sol (instE \<rho> env) (ityp \<rho> env W)) (instE \<rho> env)"
proof -
  note ei = env_invD[OF penv_inv_inst[OF pinvD(1)[OF assms(1)] assms(2)]]
  show ?thesis by (rule env_solution(1)[OF ei(1,2,3)])
qed

subsection \<open>Assignments\<close>

text \<open>The analogue of @{thm [source] assignment_term}: an assignment fails or binds the head variable.\<close>

lemma passignment_term:
  assumes pi0: "pinv alg ar A W env [(rb, t, u)]"
    and ty: "typed env W (map snd rb) t B" "typed env W (map snd rb) u B" "tnorm (tyenv env) B = B"
      "\<not> is_funT B"
    and xu: "\<And>x T. head_of t = Var x T \<Longrightarrow> vt_lookup (tenv env) x = None"
  shows "(\<exists>evs. assignment alg rb t u env = Some (evs, UErr ASSIGN)) \<or>
    (\<exists>evs. assignment alg rb t u env = Some (evs, UErr CANTUNIFY)) \<or>
    (\<exists>env' v T. okW (assignment alg rb t u env) env' \<and> pinv alg ar A W env' [] \<and> pextends env' env \<and>
      tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and> head_of t = Var v T \<and>
      (\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v) \<and>
      (\<forall>\<rho> X. gsol alg ar (tyenv env) \<rho> \<longrightarrow> reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> u))))"
proof -
  let ?\<theta> = "tyenv env"
  note pi = pinvD[OF pi0]
  note ei = penv_invD[OF pi(1)]
  obtain \<rho> where g: "gsol alg ar ?\<theta> \<rho>" by (rule pinv_gsol_exists[OF pi0])
  let ?V = "ityp \<rho> env W"
  have sol: "tsol ?\<theta> \<rho>" using g by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  from pi(4)[of "(rb, t, u)"] have swd: "swf_dp ar (rb, t, u)"
    and twd: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A U"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  note eii = env_invD[OF penv_inv_inst[OF pi(1) g]]
  have tcB: "tcons ?\<theta> B" using tcons_tnorm[OF ac(1), of B] ty(3) by simp
  have tct: "\<forall>U\<in>set (map snd rb) \<union> tys t. tcons ?\<theta> U" and tcu: "\<forall>U\<in>set (map snd rb) \<union> tys u. tcons ?\<theta> U"
    using twd tcU by auto
  have tyi: "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> t) (tsubst \<rho> B)"
    "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> u) (tsubst \<rho> B)"
    using typed_inst[OF ac sol tct tcB ty(1)] typed_inst[OF ac sol tcu tcB ty(2)] by (simp_all add: map_snd_instb)
  consider "get_eta_var rb 0 t = raiseW ASSIGN" | v T where "get_eta_var rb 0 t = returnW (v, T)"
    using get_eta_var_cases by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: assignment_def bindW_def raiseW_def)
  next
    case 2
    have gevn: "okW (get_eta_var (tnormb ?\<theta> rb) 0 (tnormt ?\<theta> t)) (v, tnorm ?\<theta> T)"
      using get_eta_var_ptnorm[OF 2] by (simp add: returnW_def)
    have nt: "has_type (tctx env W) (map snd (tnormb ?\<theta> rb)) (tnormt ?\<theta> t) B"
      and nu: "has_type (tctx env W) (map snd (tnormb ?\<theta> rb)) (tnormt ?\<theta> u) B"
      using ty(1-3) by (simp_all add: typed_def)
    from get_eta_var_type[OF gevn _ nt] have Tn: "tnorm ?\<theta> T = foldr fun_type (rev (map snd (tnormb ?\<theta> rb))) B"
      and Vv: "tctx env W v = tnorm ?\<theta> T"
      by simp_all
    have ht: "head_of t = Var v T" by (rule get_eta_var_head[OF 2])
    have vu: "vt_lookup (tenv env) v = None" by (rule xu[OF ht])
    have tT: "T \<in> tys t" using vps_tys[OF vps_head_of[OF ht]] by simp
    have twT: "tyw ar ?\<theta> A T" and tcT: "tcons ?\<theta> T" using twd tT tcU by auto
    have Vvi: "?V v = tsubst \<rho> T" using Vv tsubst_tnorm[OF ac sol tcT] by simp
    have tyok: "tyok env" by (rule tyok_tinv[OF pi(2)])
    have lkd: "lkdec \<rho> env (vps u \<union> bvps env)"
      by (rule hyp_lkdec[OF typed_hyp[OF pi(1) sol ty(2) _ bl(2)]]) (use tcu in auto)
    from rigid_occurs_term_terminates[OF eii(1,2,3) has_type_vtyped[OF tyi(2)], of v] obtain oci
      where oci: "rigid_occurs_term (instE \<rho> env) v (inst \<rho> u) = return oci" by blast
    from rigid_occurs_term_pinst[OF oci[unfolded return_def] tyok lkd] obtain r
      where "rigid_occurs_term env v u = Some r" "Ok oci = instr \<rho> id r" by blast
    then have oc: "rigid_occurs_term env v u = return oci" by (cases r) (auto simp: return_def)
    show ?thesis
    proof (cases oci)
      case Rigid
      then show ?thesis using 2 oc by (simp add: assignment_def returnW_def return_def raiseW_def bindW_def)
    next
      case Nonrigid
      then show ?thesis using 2 oc by (simp add: assignment_def returnW_def return_def raiseW_def bindW_def)
    next
      case NoOcc
      from body_type_ptnorm[OF ac tcT Tn ty(4)] obtain B1 where bt: "body_type env T = return B1"
        and B1: "tnorm ?\<theta> B1 = B" "tcons ?\<theta> B1" by blast
      from env_fastype_pterm[OF ac tcu] nu obtain T2 where
        ft0: "ok (env_fastype env (map snd rb) u) T2" "tnorm ?\<theta> T2 = B" by auto
      have ft: "ok (fastype env rb u) T2" using ft0 by (simp add: fastype_def)
      have tcT2: "tcons ?\<theta> T2" using fastype_tnorm[OF ac ft] tcu by auto
      have cu: "cunify_types alg B1 T2 env = returnW env"
        by (rule cunify_types_same_mod[OF ac B1(2) tcT2]) (simp add: B1(1) ft0(2))
      from update_unbound_ok[OF vu, of T "rlist_abs rb u"] obtain env' where
        upd: "update (v, T) (rlist_abs rb u) env = Some (Ok env')" by blast
      have ok: "okW (assignment alg rb t u env) env'"
        using 2 oc NoOcc bt ft cu upd by (simp add: assignment_def return_def)
      note up = ok_update[OF upd]
      have updr: "ok (update (v, tsubst \<rho>' T) (inst \<rho>' (rlist_abs rb u)) (instE \<rho>' env)) (instE \<rho>' env')"
        for \<rho>' using update_inst[of v \<rho>' T "rlist_abs rb u" env] upd by simp
      have tyrl: "typed env W [] (rlist_abs rb u) T"
      proof -
        have "has_type (tctx env W) (map snd (tnormb ?\<theta> rb) @ []) (tnormt ?\<theta> u) B" using nu by simp
        from has_type_rlist_abs[OF this] Tn show ?thesis by (simp add: typed_def tnormt_rlist_abs)
      qed
      have twr: "\<forall>U\<in>tys (rlist_abs rb u). tyw ar ?\<theta> A U" using twd by (auto simp: tys_rlist_abs)
      have tcr: "\<forall>U\<in>set [] \<union> tys (rlist_abs rb u). tcons ?\<theta> U" using twr tcU by auto
      have tyr: "has_type ?V [] (inst \<rho> (rlist_abs rb u)) (tsubst \<rho> T)"
        using typed_inst[OF ac sol tcr tcT tyrl] by simp
      have Fm: "snd v \<le> maxidx (instE \<rho> env)" using below_vps[OF bl(1) vps_head_of[OF ht]] by simp
      have tm: "below (maxidx (instE \<rho> env)) (inst \<rho> (rlist_abs rb u))" using bl(2) by (simp add: below_rlist_abs)
      note ut = update_typed[OF eii(4) eii(3) updr[of \<rho>] Vvi tyr Fm tm]
      have acy: "acyc (instE \<rho> env')"
      proof -
        note upi = ok_update[OF updr[of \<rho>]]
        have d: "dep (instE \<rho> env') = dep (instE \<rho> env) \<union>
            (\<lambda>y. (y, (v, tsubst \<rho> T))) ` vps (inst \<rho> (rlist_abs rb u))"
          by (rule dep_update[OF upi(2,1)])
        have "ok (rigid_occurs_term (instE \<rho> env) v (inst \<rho> u)) NoOcc" using oci NoOcc by (simp add: return_def)
        from rigid_occurs_term_complete[OF this _ eii(1)]
        have "(v, tsubst \<rho> T) \<notin> reach (instE \<rho> env) (vps (inst \<rho> (rlist_abs rb u)))"
          by (auto simp: occ_in_def vps_rlist_abs inst_rlist_abs)
        from acyclic_update[OF d this] eii(1) show ?thesis by (simp add: acyc_def)
      qed
      have lk': "vt_lookup (tenv env') x = (if x = v then Some (T, rlist_abs rb u) else vt_lookup (tenv env) x)"
        for x using up(2) by simp
      have te': "tyenv env' = tyenv env" "maxidx env' = maxidx env" using up(3,4) by simp_all
      have wc': "wcons W env'"
        using pi(6) Vv wcons_tctx[OF pi(6), of v] te'(1) unfolding wcons_def
        by (auto simp: lk' simp del: split_paired_All)
      have tctx': "tctx env' W x = tctx env W x" for x
        using wcons_tctx[OF wc'] wcons_tctx[OF pi(6)] te'(1) by simp
      have ityp': "ityp \<rho> env' W = ?V" using tctx' by simp
      have typed': "typed env' W Ts s S \<longleftrightarrow> typed env W Ts s S" for Ts s S
        using tctx' te'(1) by (simp add: typed_def)
      have etys': "etys env' \<subseteq> insert T (tys (rlist_abs rb u) \<union> etys env)" by (rule etys_update[OF upd])
      have twe': "\<forall>U\<in>etys env'. tyw ar ?\<theta> A U" using etys' twr twT pi(3) by blast
      have etv': "etvars env' \<subseteq> tvars_env ?\<theta> \<union> A" using twe' by (fastforce simp: etvars_def tyw_def)
      have "penv_inv alg ar W env'"
        unfolding penv_inv_def
      proof (intro conjI)
        show "tinv ar (maxidx env') (tyenv env') (etvars env')" using tinv_subset[OF pi(2) etv'] te' by simp
        show "tsorted alg (tyenv env')" using ei(2) te' by simp
        show "nacyc env'" using acyc_instE[of ?V \<rho> env'] ut(1) acy by (simp add: ityp')
        show "pwf_env ar env'"
        proof -
          have "pwf_term ar 0 (rlist_abs rb u)"
            using swf_tm_binding[of ar rb u] swd by (simp add: pwf_term_def twft_tys)
          moreover have "wft ar T" using twT by (simp add: tyw_def)
          ultimately show ?thesis using ei(4) by (auto simp: pwf_env_def lk')
        qed
        show "wt_env W env'" using pi(1) tyrl by (auto simp: penv_inv_def wt_env_def lk' typed')
        show "fresh_env env'" using ut(2) by simp
      qed
      then have "pinv alg ar A W env' []"
        using pi(2,5,7) twe' wc' te' by (auto simp: pinv_def simp del: split_paired_All)
      moreover have "pextends env' env" using ok_update_extends[OF upd] te' by (simp add: pextends_def)
      moreover have "reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho>' env) (X \<union> vps (inst \<rho>' u))" for \<rho>' X
        using reach_update[OF updr[of \<rho>']] by (simp add: inst_rlist_abs vps_rlist_abs)
      moreover have "\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v"
        using lk' by auto
      ultimately show ?thesis using ok te' ht by blast
    qed
  qed
qed

end

context csig
begin

subsection \<open>Steps on ground instances\<close>

text \<open>
  As \<^const>\<open>Unify_Simpl_Term.csig.tstep\<close>, without fixing the index bound, which type unification may
  increase:
\<close>

definition istep :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "istep V D env env' \<longleftrightarrow> extends env' env \<and> (\<forall>X. reach env' X \<subseteq> reach env (X \<union> D)) \<and>
    (\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> (x, V x) \<in> reach env D)"

lemma istepD:
  assumes "istep V D env env'"
  shows "extends env' env" "reach env' X \<subseteq> reach env (X \<union> D)"
    "vt_lookup (tenv env') x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> (x, V x) \<in> reach env D"
  using assms unfolding istep_def by blast+

lemma istep_refl[simp]: "istep V D env env"
  unfolding istep_def by (auto simp: reach_Un)

lemma istep_trans:
  assumes "istep V D1 env env1" "istep V D2 env1 env2"
  shows "istep V (D1 \<union> D2) env env2"
  unfolding istep_def
proof (intro conjI allI impI)
  show "extends env2 env" using assms by (auto simp: istep_def intro: extends_trans)
  fix X
  have "reach env2 X \<subseteq> reach env1 (X \<union> D2)" using assms(2) by (simp add: istep_def)
  also have "\<dots> \<subseteq> reach env (X \<union> D2 \<union> D1)" using assms(1) by (simp add: istep_def)
  finally show "reach env2 X \<subseteq> reach env (X \<union> (D1 \<union> D2))" by (simp add: Un_ac)
next
  fix x assume b: "vt_lookup (tenv env2) x \<noteq> None" and u: "vt_lookup (tenv env) x = None"
  show "(x, V x) \<in> reach env (D1 \<union> D2)"
  proof (cases "vt_lookup (tenv env1) x = None")
    case True
    with istepD(3)[OF assms(2) b] have "(x, V x) \<in> reach env1 D2" by simp
    also have "\<dots> \<subseteq> reach env (D2 \<union> D1)" using assms(1) by (simp add: istep_def)
    finally show ?thesis by (simp add: Un_ac)
  next
    case False
    with istepD(3)[OF assms(1) _ u] have "(x, V x) \<in> reach env D1" by simp
    then show ?thesis using reach_subset[of D1 "D1 \<union> D2" env] by blast
  qed
qed

lemma istep_mono: "istep V D env env' \<Longrightarrow> D \<subseteq> reach env D' \<Longrightarrow> istep V D' env env'"
proof -
  assume s: "istep V D env env'" and D: "D \<subseteq> reach env D'"
  have m: "reach env (X \<union> D) \<subseteq> reach env (X \<union> D')" for X
    using D by (intro reach_mono) (auto intro: set_mp[OF reach_incl] set_mp[OF reach_subset])
  have m': "reach env D \<subseteq> reach env D'" using D by (rule reach_mono)
  from s m m' show ?thesis by (fastforce simp: istep_def)
qed

lemma istep_unb:
  assumes s: "istep V D env env'" and Y: "Y \<subseteq> reach env D"
  shows "unb env' Y \<subseteq> unb env D"
proof
  fix y assume y: "y \<in> unb env' Y"
  then have "y \<in> reach env (Y \<union> D)" using s by (auto simp: unb_def istep_def)
  also have "\<dots> = reach env D" using reach_absorb[OF Y, of "{}"] by simp
  finally have "y \<in> reach env D" .
  moreover have "lk env (fst y) (snd y) = None"
    using y extends_lk[of env' env] s by (cases "lk env (fst y) (snd y)") (auto simp: unb_def istep_def)
  ultimately show "y \<in> unb env D" by (simp add: unb_def)
qed

lemma istep_unb_less:
  assumes s: "istep V D env env'" and Y: "Y \<subseteq> reach env D" and fin: "finite D"
    and ty: "env_typed V env'" and new: "\<not> same_lk env env'"
  shows "card (unb env' Y) < card (unb env D)"
proof -
  from new obtain x where x: "vt_lookup (tenv env') x \<noteq> vt_lookup (tenv env) x"
    by (auto simp: same_lk_def)
  have u: "vt_lookup (tenv env) x = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env) x \<noteq> None"
    then obtain b where "vt_lookup (tenv env) x = Some b" by blast
    with istepD(1)[OF s] x show False unfolding extends_def by metis
  qed
  with x obtain U w where b: "vt_lookup (tenv env') x = Some (U, w)" by auto
  have r: "(x, V x) \<in> reach env D" using istepD(3)[OF s _ u] b by simp
  have "(x, V x) \<in> unb env D" using r u by (simp add: unb_def lk_def)
  moreover have "(x, V x) \<notin> unb env' Y"
    using env_typedD[OF ty b] b by (simp add: unb_def lk_def)
  moreover have "finite (unb env D)"
    by (rule finite_subset[OF _ finite_reach[OF fin]]) (auto simp: unb_def)
  ultimately show ?thesis using istep_unb[OF s Y] by (intro psubset_card_mono) blast+
qed

subsection \<open>Transfer of the invariant\<close>

lemma pinv_transfer:
  assumes pi0: "pinv alg ar A W env dps" and pi1: "pinv alg ar A W env' []"
    and ext: "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
  shows "pinv alg ar A W env' dps"
proof -
  note pi = pinvD[OF pi0] and pi' = pinvD[OF pi1]
  have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
  have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar (tyenv env') A T) \<and> ptyped env' W dp \<and>
      dp_below (maxidx env') dp" if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from pi(4)[OF dp] dpe obtain T where w: "swf_dp ar dp" and tw: "\<forall>T\<in>dtys dp. tyw ar (tyenv env) A T"
      and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T"
      and bl: "below (maxidx env) t" "below (maxidx env) u"
      by auto
    have "ptyped env' W dp"
      using typed_wcons[OF ac' ext(1) pi(6) pi'(6) ty(1)] typed_wcons[OF ac' ext(1) pi(6) pi'(6) ty(2)] dpe
      by auto
    moreover have "\<forall>T\<in>dtys dp. tyw ar (tyenv env') A T" using tw tyw_textends[OF ac' ext(1)] by blast
    moreover have "dp_below (maxidx env') dp" using bl below_mono[OF _ ext(2)] dpe by simp
    ultimately show ?thesis using w by blast
  qed
  with pi1 show ?thesis by (auto simp: pinv_def)
qed

text \<open>An extension of the type environment that keeps the bindings of the terms:\<close>

lemma pinv_text:
  assumes pi0: "pinv alg ar A W env dps"
    and te: "tenv env' = tenv env" "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
    and ti: "tinv ar (maxidx env') (tyenv env') A" "tsorted alg (tyenv env')"
  shows "pinv alg ar A W env' dps"
proof (rule pinv_transfer[OF pi0 _ te(2,3)])
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'"
  note pi = pinvD[OF pi0]
  note ei = penv_invD[OF pi(1)]
  have ac': "tacyc ?\<theta>'" using tinv_tacyc[OF ti(1)] by simp
  have ety: "etys env' = etys env" by (rule etys_same_tenv[OF te(1)])
  have twe: "tyw ar ?\<theta>' A T" if "T \<in> etys env'" for T
    using that ety pi(3) tyw_textends[OF ac' te(2)] by blast
  have twW: "tyw ar ?\<theta>' A (W x)" for x using pi(5) tyw_textends[OF ac' te(2)] by blast
  have wc: "wcons W env'"
    using pi(6) te(1) by (auto simp: wcons_def simp del: split_paired_All dest: arg_cong[of _ _ "tnorm ?\<theta>'"])
      (metis ac' te(2) tnorm_textends)
  have etv: "etvars env' \<subseteq> tvars_env ?\<theta>' \<union> A"
    using pi(3) tvars_env_textends[OF te(2)] ety by (fastforce simp: etvars_def tyw_def)
  have "penv_inv alg ar W env'"
    unfolding penv_inv_def
  proof (intro conjI)
    show "tinv ar (maxidx env') ?\<theta>' (etvars env')" by (rule tinv_subset[OF ti(1) etv])
    show "tsorted alg ?\<theta>'" by (rule ti(2))
    show "nacyc env'" using ei(3) nacyc_same_tenv[OF te(1)] by simp
    show "pwf_env ar env'" using ei(4) te(1) by (simp add: pwf_env_def)
    show "wt_env W env'"
      using pi(1) wt_env_textends[OF ac' te(2,1)] by (simp add: penv_inv_def)
    show "fresh_env env'" by (rule fresh_env_same[OF te(1,3) ei(6)])
  qed
  then show "pinv alg ar A W env' []"
    using ti(1) twe twW wc pi(7) by (auto simp: pinv_def simp del: split_paired_All)
qed

text \<open>The typing of a ground instance does not depend on the environment:\<close>

lemma pinv_ityp:
  assumes pi0: "pinv alg ar A W env dps" and g: "gsol alg ar (tyenv env) \<rho>"
  shows "ityp \<rho> env W = (\<lambda>x. tsubst \<rho> (W x))"
proof
  fix x
  note pi = pinvD[OF pi0]
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  show "ityp \<rho> env W x = tsubst \<rho> (W x)"
    using wcons_tctx[OF pi(6)] tsubst_tnorm[OF ac sol tyw_tcons[OF pi(2) pi(5)]] by simp
qed

subsection \<open>Composing simplification steps\<close>

text \<open>
  A step from \<open>env\<close> to \<open>env'\<close> on the pairs \<open>dps\<close>, adding the pairs \<open>dps'\<close>: either it keeps the
  type environment, and then it is a step on all ground instances, or it reduces the number of
  unbound type variables of the problem.
\<close>

definition pstep :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    dpair list \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "pstep alg ar A W dps dps' env env' \<longleftrightarrow>
    (tyenv env' = tyenv env \<and> (\<forall>\<rho>. gsol alg ar (tyenv env) \<rho> \<longrightarrow>
      istep (\<lambda>x. tsubst \<rho> (W x)) (ivps \<rho> dps) (instE \<rho> env) (instE \<rho> env') \<and>
      ivps \<rho> dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps))) \<or>
    card (uvarsA (tyenv env') A) < card (uvarsA (tyenv env) A)"

lemma pstep_Nil[simp]: "pstep alg ar A W dps [] env env"
  by (simp add: pstep_def)

lemma pstep_set:
  "set dps = set dps2 \<Longrightarrow> set n = set n2 \<Longrightarrow> pstep alg ar A W dps n env env' = pstep alg ar A W dps2 n2 env env'"
  by (simp add: pstep_def image_image)

lemma pstep_trans:
  assumes "pstep alg ar A W dps1 n1 env env1" "pstep alg ar A W dps2 n2 env1 env2"
  shows "pstep alg ar A W (dps1 @ dps2) (n2 @ n1) env env2"
proof (cases "tyenv env1 = tyenv env \<and> tyenv env2 = tyenv env1")
  case True
  let ?V = "\<lambda>\<rho> x. tsubst \<rho> (W x)"
  have "istep (?V \<rho>) (ivps \<rho> (dps1 @ dps2)) (instE \<rho> env) (instE \<rho> env2) \<and>
      ivps \<rho> (n2 @ n1) \<subseteq> reach (instE \<rho> env) (ivps \<rho> (dps1 @ dps2))" if g: "gsol alg ar (tyenv env) \<rho>" for \<rho>
  proof -
    from assms(1) True g have s1: "istep (?V \<rho>) (ivps \<rho> dps1) (instE \<rho> env) (instE \<rho> env1)"
      "ivps \<rho> n1 \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps1)"
      by (auto simp: pstep_def)
    from assms(2) True g have s2: "istep (?V \<rho>) (ivps \<rho> dps2) (instE \<rho> env1) (instE \<rho> env2)"
      "ivps \<rho> n2 \<subseteq> reach (instE \<rho> env1) (ivps \<rho> dps2)"
      by (auto simp: pstep_def)
    have "istep (?V \<rho>) (ivps \<rho> dps1 \<union> ivps \<rho> dps2) (instE \<rho> env) (instE \<rho> env2)"
      by (rule istep_trans[OF s1(1) s2(1)])
    moreover have "ivps \<rho> n2 \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps2 \<union> ivps \<rho> dps1)"
      using s2(2) istepD(2)[OF s1(1), of "ivps \<rho> dps2"] by blast
    moreover have "ivps \<rho> n1 \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps2 \<union> ivps \<rho> dps1)"
      using s1(2) reach_subset[of "ivps \<rho> dps1" "ivps \<rho> dps2 \<union> ivps \<rho> dps1" "instE \<rho> env"] by blast
    ultimately show ?thesis by (auto simp: Un_ac)
  qed
  then show ?thesis using True by (simp add: pstep_def)
next
  case False
  with assms have "card (uvarsA (tyenv env2) A) < card (uvarsA (tyenv env) A)"
    unfolding pstep_def by auto
  then show ?thesis by (simp add: pstep_def)
qed

lemma pstep_mono_dps:
  assumes "pstep alg ar A W dps' n env env'"
    and sub: "\<And>\<rho>. gsol alg ar (tyenv env) \<rho> \<Longrightarrow> ivps \<rho> dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
  shows "pstep alg ar A W dps n env env'"
proof (cases "card (uvarsA (tyenv env') A) < card (uvarsA (tyenv env) A)")
  case True
  then show ?thesis by (simp add: pstep_def)
next
  case False
  with assms(1) have te: "tyenv env' = tyenv env" and s: "\<forall>\<rho>. gsol alg ar (tyenv env) \<rho> \<longrightarrow>
      istep (\<lambda>x. tsubst \<rho> (W x)) (ivps \<rho> dps') (instE \<rho> env) (instE \<rho> env') \<and>
      ivps \<rho> n \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps')"
    by (auto simp: pstep_def)
  have "istep (\<lambda>x. tsubst \<rho> (W x)) (ivps \<rho> dps) (instE \<rho> env) (instE \<rho> env') \<and>
      ivps \<rho> n \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)" if g: "gsol alg ar (tyenv env) \<rho>" for \<rho>
    using s g istep_mono[OF _ sub[OF g]] reach_mono[OF sub[OF g]] by blast
  then show ?thesis using te by (simp add: pstep_def)
qed

text \<open>The counterpart of \<^const>\<open>psres\<close> without a solution:\<close>

definition ptsres :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    dpair list \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "ptsres alg ar A W dps st st' \<longleftrightarrow> (case (st, st') of ((env, ffs, frs), (env', ffs', frs')) \<Rightarrow>
    \<exists>ffn frn. ffs' = ffn @ ffs \<and> frs' = frn @ frs \<and> pinv alg ar A W env' (ffn @ frn) \<and>
      pextends env' env \<and> maxidx env \<le> maxidx env' \<and> pstep alg ar A W dps (ffn @ frn) env env' \<and>
      (\<forall>dp\<in>set ffn. pff_shape env' W dp) \<and> (\<forall>dp\<in>set frn. pfr_shape env' W dp) \<and>
      (\<forall>dp\<in>set (ffn @ frn). heads_unb env dp) \<and> fch W (tyenv env') (tyenv env) ffn)"

lemma ptsresD:
  assumes "ptsres alg ar A W dps (env, ffs, frs) st'"
  obtains env' ffn frn where "st' = (env', ffn @ ffs, frn @ frs)" "pinv alg ar A W env' (ffn @ frn)"
    "pextends env' env" "maxidx env \<le> maxidx env'" "pstep alg ar A W dps (ffn @ frn) env env'"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env') (tyenv env) ffn"
  using assms by (cases st') (auto simp: ptsres_def)

lemma ptsresI:
  assumes "pinv alg ar A W env' (ffn @ frn)" "pextends env' env" "maxidx env \<le> maxidx env'"
    "pstep alg ar A W dps (ffn @ frn) env env'"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env') (tyenv env) ffn"
  shows "ptsres alg ar A W dps (env, ffs, frs) (env', ffn @ ffs, frn @ frs)"
  using assms by (auto simp: ptsres_def)

lemma pinv_Nil: "pinv alg ar A W env dps \<Longrightarrow> pinv alg ar A W env []"
  by (simp add: pinv_def)

lemma ptsres_refl: "pinv alg ar A W env [] \<Longrightarrow> ptsres alg ar A W dps (env, ffs, frs) (env, ffs, frs)"
  using ptsresI[of alg ar A W env "[]" "[]" env dps ffs frs] by simp

lemma ptsres_trans:
  assumes "ptsres alg ar A W dps1 (env, ffs, frs) st1" "ptsres alg ar A W dps2 st1 st2"
  shows "ptsres alg ar A W (dps1 @ dps2) (env, ffs, frs) st2"
proof -
  from ptsresD[OF assms(1)] obtain env1 ffn1 frn1 where s1: "st1 = (env1, ffn1 @ ffs, frn1 @ frs)"
    "pinv alg ar A W env1 (ffn1 @ frn1)" "pextends env1 env" "maxidx env \<le> maxidx env1"
    "pstep alg ar A W dps1 (ffn1 @ frn1) env env1"
    "\<And>dp. dp \<in> set ffn1 \<Longrightarrow> pff_shape env1 W dp" "\<And>dp. dp \<in> set frn1 \<Longrightarrow> pfr_shape env1 W dp"
    "\<And>dp. dp \<in> set (ffn1 @ frn1) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env1) (tyenv env) ffn1"
    by blast
  from ptsresD[OF assms(2)[unfolded s1(1)]] obtain env2 ffn2 frn2 where
    s2: "st2 = (env2, ffn2 @ ffn1 @ ffs, frn2 @ frn1 @ frs)"
    "pinv alg ar A W env2 (ffn2 @ frn2)" "pextends env2 env1" "maxidx env1 \<le> maxidx env2"
    "pstep alg ar A W dps2 (ffn2 @ frn2) env1 env2"
    "\<And>dp. dp \<in> set ffn2 \<Longrightarrow> pff_shape env2 W dp" "\<And>dp. dp \<in> set frn2 \<Longrightarrow> pfr_shape env2 W dp"
    "\<And>dp. dp \<in> set (ffn2 @ frn2) \<Longrightarrow> heads_unb env1 dp" "fch W (tyenv env2) (tyenv env1) ffn2"
    by blast
  note pi1 = pinvD[OF s1(2)] and pi2 = pinvD[OF s2(2)]
  have ac2: "tacyc (tyenv env2)" by (rule tinv_tacyc[OF pi2(2)])
  have te: "textends (tyenv env1) (tyenv env2)" using s2(3) by (simp add: pextends_def)
  have c1: "pinv alg ar A W env2 (ffn1 @ frn1)" by (rule pinv_transfer[OF s1(2) pinv_Nil[OF s2(2)] te s2(4)])
  have c: "pinv alg ar A W env2 ((ffn2 @ ffn1) @ frn2 @ frn1)" using c1 s2(2) by (auto simp: pinv_def)
  have eqs: "set ((ffn2 @ frn2) @ ffn1 @ frn1) = set ((ffn2 @ ffn1) @ frn2 @ frn1)" by auto
  have st: "pstep alg ar A W (dps1 @ dps2) ((ffn2 @ ffn1) @ frn2 @ frn1) env env2"
    by (rule iffD1[OF pstep_set[OF refl eqs] pstep_trans[OF s1(5) s2(5)]])
  have ex: "pextends env2 env" using s2(3) s1(3) by (rule pextends_trans)
  have mx: "maxidx env \<le> maxidx env2" using s1(4) s2(4) by simp
  have ffh: "pff_shape env2 W dp" if "dp \<in> set (ffn2 @ ffn1)" for dp
    using that s2(6) s1(6) pff_shape_wcons[OF _ ac2 te pi1(6) pi2(6)] by (metis Un_iff set_append)
  have frh: "pfr_shape env2 W dp" if "dp \<in> set (frn2 @ frn1)" for dp
    using that s2(7) s1(7) pfr_shape_wcons[OF _ ac2 te pi1(6) pi2(6)] by (metis Un_iff set_append)
  have hh: "heads_unb env dp" if "dp \<in> set ((ffn2 @ ffn1) @ frn2 @ frn1)" for dp
    using that s1(8) s2(8) heads_unb_extends[OF _ pextendsD(1)[OF s1(3)]] by (metis Un_iff set_append)
  have "ptsres alg ar A W (dps1 @ dps2) (env, ffs, frs) (env2, (ffn2 @ ffn1) @ ffs, (frn2 @ frn1) @ frs)"
    by (rule ptsresI[OF c ex mx st ffh frh hh fch_append[OF s2(9) s1(9)]])
  then show ?thesis using s2(1) by simp
qed

lemma ptsres_mono_dps:
  assumes "ptsres alg ar A W dps' (env, ffs, frs) st'"
    and sub: "\<And>\<rho>. gsol alg ar (tyenv env) \<rho> \<Longrightarrow> ivps \<rho> dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
  shows "ptsres alg ar A W dps (env, ffs, frs) st'"
proof -
  from ptsresD[OF assms(1)] obtain env' ffn frn where s: "st' = (env', ffn @ ffs, frn @ frs)"
    "pinv alg ar A W env' (ffn @ frn)" "pextends env' env" "maxidx env \<le> maxidx env'"
    "pstep alg ar A W dps' (ffn @ frn) env env'"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env') (tyenv env) ffn"
    by blast
  have "ptsres alg ar A W dps (env, ffs, frs) (env', ffn @ ffs, frn @ frs)"
    by (rule ptsresI[OF s(2-4) pstep_mono_dps[OF s(5) sub] s(6-9)])
  with s(1) show ?thesis by simp
qed

lemma pstep_weaken: "pstep alg ar A W dps n env env' \<Longrightarrow> set n' \<subseteq> set n \<Longrightarrow> pstep alg ar A W dps n' env env'"
proof -
  assume p: "pstep alg ar A W dps n env env'" and s: "set n' \<subseteq> set n"
  have "ivps \<rho> n' \<subseteq> ivps \<rho> n" for \<rho> using s by auto
  then show ?thesis using p unfolding pstep_def by (meson order.trans)
qed

text \<open>The arguments of rigid-rigid pairs with equal heads.\<close>

lemma psimrands_term:
  assumes F: "\<And>i st. i < length as \<Longrightarrow> pinv alg ar A W (fst st) [] \<Longrightarrow> pextends (fst st) eo \<Longrightarrow>
      maxidx eo \<le> maxidx (fst st) \<Longrightarrow> pstep alg ar A W D [] eo (fst st) \<Longrightarrow>
      cuok (F (rb, as ! i, bs ! i) st) (ptsres alg ar A W [(rb, as ! i, bs ! i)] st)"
    and h: "\<nexists>f u. h = f $ u" "\<nexists>f u. h' = f $ u"
    and sub: "\<And>\<rho>. gsol alg ar (tyenv eo) \<rho> \<Longrightarrow>
      ivps \<rho> (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) \<subseteq> reach (instE \<rho> eo) (ivps \<rho> D)"
  shows "length as = length bs \<Longrightarrow> pinv alg ar A W (fst st) [] \<Longrightarrow> pextends (fst st) eo \<Longrightarrow>
    maxidx eo \<le> maxidx (fst st) \<Longrightarrow> pstep alg ar A W D [] eo (fst st) \<Longrightarrow>
    cuok (simrands F rb u0 (list_comb h as) (list_comb h' bs) st)
      (ptsres alg ar A W (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) st)"
  using F sub
proof (induction as arbitrary: bs st rule: rev_induct)
  case Nil
  then have "bs = []" by simp
  moreover have "simrands F rb u0 h h' st = returnW st" using h by (cases h; cases h') simp_all
  ultimately show ?case using ptsres_refl[OF Nil.prems(2)] by (cases st) simp
next
  case (snoc a as)
  obtain env0 ffs0 frs0 where st: "st = (env0, ffs0, frs0)" by (cases st)
  from snoc.prems(1) obtain b bs' where bs: "bs = bs' @ [b]" "length as = length bs'"
    by (metis length_Suc_conv_rev)
  have zs: "map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs) =
      map (\<lambda>(a, b). (rb, a, b)) (zip as bs') @ [(rb, a, b)]"
    using bs by simp
  have F': "cuok (F (rb, as ! i, bs' ! i) st) (ptsres alg ar A W [(rb, as ! i, bs' ! i)] st)"
    if "i < length as" "pinv alg ar A W (fst st) []" "pextends (fst st) eo" "maxidx eo \<le> maxidx (fst st)"
      "pstep alg ar A W D [] eo (fst st)" for i st
    using snoc.prems(6)[of i st] that bs by (simp add: nth_append)
  have sub': "ivps \<rho> (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) \<subseteq> reach (instE \<rho> eo) (ivps \<rho> D)"
    if "gsol alg ar (tyenv eo) \<rho>" for \<rho>
    using snoc.prems(7)[OF that, unfolded zs] by auto
  have "simrands F rb u0 (list_comb h (as @ [a])) (list_comb h' bs) st =
      bindW (simrands F rb u0 (list_comb h as) (list_comb h' bs') st) (F (rb, a, b))"
    using bs by (simp add: list_comb_snoc)
  moreover have "cuok (bindW (simrands F rb u0 (list_comb h as) (list_comb h' bs') st) (F (rb, a, b)))
      (ptsres alg ar A W (map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs)) st)"
  proof (rule cuok_bindW[OF snoc.IH[OF bs(2) snoc.prems(2-5) F' sub']])
    fix st1 assume r1: "ptsres alg ar A W (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) st st1"
    obtain env1 ffn frn where s1: "st1 = (env1, ffn @ ffs0, frn @ frs0)" "pinv alg ar A W env1 (ffn @ frn)"
      "pextends env1 env0" "maxidx env0 \<le> maxidx env1"
      "pstep alg ar A W (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) (ffn @ frn) env0 env1"
      by (rule ptsresD[OF r1[unfolded st]])
    have c1: "pinv alg ar A W (fst st1) []" using pinv_Nil[OF s1(2)] s1(1) by simp
    have e1: "pextends (fst st1) eo" using pextends_trans[OF s1(3)] snoc.prems(3) st s1(1) by simp
    have m1: "maxidx eo \<le> maxidx (fst st1)" using snoc.prems(4) s1(1,4) st by simp
    have "pstep alg ar A W (D @ map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) ((ffn @ frn) @ []) eo env1"
      by (rule pstep_trans[OF snoc.prems(5)[unfolded st, simplified] s1(5)])
    then have "pstep alg ar A W D ((ffn @ frn) @ []) eo env1"
      by (rule pstep_mono_dps) (use sub' reach_incl in auto)
    then have t1: "pstep alg ar A W D [] eo (fst st1)" using s1(1) by (auto intro: pstep_weaken)
    from snoc.prems(6)[of "length as" st1] c1 e1 m1 t1 bs
    have "cuok (F (rb, a, b) st1) (ptsres alg ar A W [(rb, a, b)] st1)" by (simp add: nth_append)
    then show "cuok (F (rb, a, b) st1) (ptsres alg ar A W (map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs)) st)"
      by (rule cuok_mono) (use ptsres_trans[OF r1[unfolded st]] zs st in simp)
  qed
  ultimately show ?case by simp
qed

subsection \<open>One simplification step\<close>

lemma size_foldr_fun_type: "size B < size (foldr fun_type (U # Us) B)"
proof -
  have "size B \<le> size (foldr fun_type Us B)" by (induction Us) auto
  then show ?thesis by simp
qed

lemma foldr_fun_type_same_base: "foldr fun_type Us B = foldr fun_type Us' B \<Longrightarrow> Us = Us'"
proof (induction Us arbitrary: Us')
  case Nil
  show ?case
  proof (cases Us')
    case (Cons U Us'')
    with Nil have "B = foldr fun_type (U # Us'') B" by simp
    then show ?thesis using size_foldr_fun_type[of B U Us''] by (metis less_irrefl)
  qed simp
next
  case (Cons U Us)
  note p = Cons.prems and ih = Cons.IH
  show ?case
  proof (cases Us')
    case Nil
    with p have "foldr fun_type (U # Us) B = B" by simp
    then show ?thesis using size_foldr_fun_type[of B U Us] by (metis less_irrefl)
  next
    case (Cons U' Us'')
    with p ih show ?thesis by simp
  qed
qed

lemma typed_head_Var_tctx:
  assumes "typed env W Ts t B" "head_of t = Var x X"
  shows "tnorm (tyenv env) X = tctx env W x"
proof -
  let ?\<theta> = "tyenv env"
  obtain as where t: "t = list_comb (Var x X) as" using head_of_list_comb[of t] assms(2) by metis
  have "has_type (tctx env W) (map (tnorm ?\<theta>) Ts) (list_comb (Var x (tnorm ?\<theta> X)) (map (tnormt ?\<theta>) as))
      (tnorm ?\<theta> B)"
    using assms(1) t by (simp add: typed_def)
  then obtain Us where "has_type (tctx env W) (map (tnorm ?\<theta>) Ts) (Var x (tnorm ?\<theta> X))
      (foldr fun_type Us (tnorm ?\<theta> B))"
    by (auto simp: has_type_list_comb)
  then show ?thesis by (auto elim: has_type_elims)
qed

lemma istep_same:
  assumes te: "tenv env' = tenv env"
  shows "istep V D (instE \<rho> env) (instE \<rho> env')"
  unfolding istep_def
proof (intro conjI allI impI)
  show "extends (instE \<rho> env') (instE \<rho> env)" using te by (simp add: extends_def)
  fix X
  have "reach (instE \<rho> env') X = reach (instE \<rho> env) X" by (rule reach_lookup_eq) (simp add: te)
  then show "reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> D)"
    using reach_subset[of X "X \<union> D" "instE \<rho> env"] by simp
next
  fix x assume "vt_lookup (tenv (instE \<rho> env')) x \<noteq> None" "vt_lookup (tenv (instE \<rho> env)) x = None"
  then show "(x, V x) \<in> reach (instE \<rho> env) D" using te by simp
qed

lemma pinv_swap: "pinv alg ar A W env [(rb, t, u)] \<Longrightarrow> pinv alg ar A W env [(rb, u, t)]"
  by (auto simp: pinv_def)

end

context wf_csig
begin

text \<open>Type unification fails or keeps the invariant, as @{thm [source] cunify_types_pcomplete}.\<close>

lemma cunify_types_pterm:
  assumes fin: "finite A" and pi0: "pinv alg ar A W env dps"
    and tw: "tyw ar (tyenv env) A T" "tyw ar (tyenv env) A U"
  shows "(\<exists>evs. cunify_types alg T U env = Some (evs, UErr CANTUNIFY)) \<or>
    (\<exists>env'. cunify_types alg T U env = returnW env' \<and> pinv alg ar A W env' dps \<and> tenv env' = tenv env \<and>
      pextends env' env \<and> maxidx env \<le> maxidx env' \<and> pstep alg ar A W dps' [] env env' \<and>
      tnorm (tyenv env') T = tnorm (tyenv env') U)"
proof -
  note pi = pinvD[OF pi0]
  note ei = penv_invD[OF pi(1)]
  from unify_types_poly[OF pi(2) ei(2) tw pi(7)] show ?thesis
  proof (elim disjE exE conjE)
    fix u assume "unify_types alg T U env = Some (Err (Unif u))"
    then show ?thesis by (simp add: cunify_types_def emit_def bindW_def raiseW_def)
  next
    fix env' assume u: "unify_types alg T U env = Some (Ok env')" and te: "tenv env' = tenv env"
      and ts0: "Type_Mgu.tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) (tyenv env) (maxidx env) (tyenv env') (maxidx env')"
      and eq: "\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U" and srt: "tsorted alg (tyenv env')"
    note ts = Type_Mgu.tstepD[OF ts0]
    have "pinv alg ar A W env' dps" by (rule pinv_text[OF pi0 te ts(1,2,3) srt])
    moreover have "pextends env' env" using te ts(1) by (simp add: pextends_def extends_def)
    moreover have "pstep alg ar A W dps' [] env env'"
      using unify_types_card[OF fin pi(2) ei(2) tw pi(7) u] istep_same[OF te] by (auto simp: pstep_def)
    moreover have "tnorm (tyenv env') T = tnorm (tyenv env') U"
      by (rule tnorm_eq_tsol[OF tinv_tacyc[OF ts(3)]]) (use eq in blast)
    moreover have "cunify_types alg T U env = returnW env'" using u by (simp add: cunify_types_def)
    ultimately show ?thesis using te ts(2) by blast
  qed
qed

lemma ivps_vps: "ivps \<rho> dps = (\<lambda>(x, T). (x, tsubst \<rho> T)) ` vps_dps dps"
  by (force simp: instd_def vps_inst split: prod.splits)

text \<open>One step of \<^const>\<open>SIMPL0\<close> on a head-normalized pair, as @{thm [source] SIMPL0_step_term}.\<close>

lemma SIMPL0_step_pterm:
  assumes fin: "finite A" and pi0: "pinv alg ar A W env [(rb, t, u)]"
    and ty: "typed env W (map snd rb) t B" "typed env W (map snd rb) u B" "tnorm (tyenv env) B = B"
      "\<not> is_funT B"
    and nAt: "\<not> is_Abs t" "\<not> is_Abs u"
    and nA: "\<not> is_Abs (head_of t)" "\<not> is_Abs (head_of u)"
    and ut: "\<And>F U. head_of t = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and IH: "\<And>i st as bs. is_rigid (head_of t) \<Longrightarrow> t = list_comb (head_of t) as \<Longrightarrow>
      u = list_comb (head_of u) bs \<Longrightarrow> length as = length bs \<Longrightarrow> i < length as \<Longrightarrow>
      pinv alg ar A W (fst st) [(rb, as ! i, bs ! i)] \<Longrightarrow>
      pextends (fst st) env \<Longrightarrow> maxidx env \<le> maxidx (fst st) \<Longrightarrow>
      pstep alg ar A W [(rb, t, u)] [] env (fst st) \<Longrightarrow>
      cuok (F (rb, as ! i, bs ! i) st) (ptsres alg ar A W [(rb, as ! i, bs ! i)] st)"
  shows "cuok (SIMPL0_step alg F (rb, t, u) env ffs frs) (ptsres alg ar A W [(rb, t, u)] (env, ffs, frs))"
proof -
  let ?\<theta> = "tyenv env" and ?dp = "(rb, t, u)"
  note pi = pinvD[OF pi0]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  from pi(4)[of ?dp] have swd: "swf_dp ar ?dp"
    and twd: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A U"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  have tct: "\<forall>U\<in>set (map snd rb) \<union> tys t. tcons ?\<theta> U" and tcu: "\<forall>U\<in>set (map snd rb) \<union> tys u. tcons ?\<theta> U"
    using twd tcU by auto
  have hb: "heads_unb env (rb, t, u)" "heads_unb env (rb, u, t)" using ut uu by (auto simp: heads_unb_def)
  have ps: "pstep alg ar A W [?dp] [dp] env env" if "dp = ?dp \<or> dp = (rb, u, t)" for dp
  proof -
    have "ivps \<rho> [dp] = ivps \<rho> [?dp]" for \<rho> using that by auto
    then show ?thesis by (simp add: pstep_def reach_incl)
  qed
  have keep: "ptsres alg ar A W [?dp] (env, ffs, frs) (env, ffs, dp # frs)"
    if "pfr_shape env W dp" "pinv alg ar A W env [dp]" "heads_unb env dp" "dp = ?dp \<or> dp = (rb, u, t)" for dp
    using ptsresI[of alg ar A W env "[]" "[dp]" env "[?dp]" ffs frs] that ps[OF that(4)] by simp
  have asg: "ptsres alg ar A W [?dp] (env, ffs, frs) (env', ffs, frs)"
    if a: "pinv alg ar A W env' []" "pextends env' env" "tyenv env' = tyenv env" "maxidx env' = maxidx env"
      "\<forall>\<rho> X. gsol alg ar ?\<theta> \<rho> \<longrightarrow> reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> s))"
      "\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v"
      and hv: "head_of s' = Var v T" and ss: "(s = u \<and> s' = t) \<or> (s = t \<and> s' = u)" for env' s s' v T
  proof -
    have tys': "typed env W (map snd rb) s' B" using ss ty by auto
    have tcT: "tcons ?\<theta> T" using ss vps_tys[OF vps_head_of[OF hv]] tct tcu by auto
    have Tv: "tnorm ?\<theta> T = tctx env W v" by (rule typed_head_Var_tctx[OF tys' hv])
    have st: "istep (\<lambda>x. tsubst \<rho> (W x)) (ivps \<rho> [?dp]) (instE \<rho> env) (instE \<rho> env') \<and>
        ivps \<rho> [] \<subseteq> reach (instE \<rho> env) (ivps \<rho> [?dp])"
      if g: "gsol alg ar ?\<theta> \<rho>" for \<rho>
    proof -
      have sol: "tsol ?\<theta> \<rho>" using g by (simp add: gsol_def)
      have "tsubst \<rho> (W v) = tsubst \<rho> T"
        using fun_cong[OF pinv_ityp[OF pi0 g], of v] Tv tsubst_tnorm[OF ac sol tcT] by simp
      then have vin: "(v, tsubst \<rho> (W v)) \<in> ivps \<rho> [?dp]"
        using ss vps_head_of[OF hv] by (force simp: vps_inst)
      have sub: "vps (inst \<rho> s) \<subseteq> ivps \<rho> [?dp]" using ss by auto
      show ?thesis
        unfolding istep_def
      proof (intro conjI allI impI)
        show "extends (instE \<rho> env') (instE \<rho> env)" using pextendsD(1)[OF a(2)] by (auto simp: extends_def)
        show "reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> [?dp])" for X
          using a(5) g reach_subset[of "X \<union> vps (inst \<rho> s)" "X \<union> ivps \<rho> [?dp]" "instE \<rho> env"] sub by blast
        fix x assume x: "vt_lookup (tenv (instE \<rho> env')) x \<noteq> None" "vt_lookup (tenv (instE \<rho> env)) x = None"
        have "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None" using x by simp_all
        then have "x = v" using a(6) by blast
        then show "(x, tsubst \<rho> (W x)) \<in> reach (instE \<rho> env) (ivps \<rho> [?dp])" using vin reach_incl by blast
      qed simp
    qed
    have "pstep alg ar A W [?dp] ([] @ []) env env'" using st a(3) by (simp add: pstep_def)
    moreover have "textends ?\<theta> (tyenv env')" using a(2) by (simp add: pextends_def)
    ultimately show ?thesis using ptsresI[of alg ar A W env' "[]" "[]" env "[?dp]" ffs frs] a(1,2,4) by simp
  qed
  have hc: "(\<exists>x X. head_of s = Var x X) \<or> is_rigid (head_of s)"
    if "typed env W (map snd rb) s B" "\<not> is_Abs (head_of s)" for s
  proof -
    have nt: "has_type (tctx env W) (map (tnorm ?\<theta>) (map snd rb)) (tnormt ?\<theta> s) (tnorm ?\<theta> B)"
      using that(1) by (simp add: typed_def)
    have nA': "\<not> is_Abs (head_of (tnormt ?\<theta> s))" using that(2) by (cases "head_of s") auto
    show ?thesis
    proof (rule head_cases[OF nt nA'])
      fix x U assume "head_of (tnormt ?\<theta> s) = Var x U"
      then show ?thesis by (cases "head_of s") auto
    next
      assume "is_rigid (head_of (tnormt ?\<theta> s))"
      then show ?thesis by (cases "head_of s") (auto simp: is_rigid_def)
    qed
  qed
  consider (VV) x X y Y where "head_of t = Var x X" "head_of u = Var y Y"
    | (VR) x X where "head_of t = Var x X" "is_rigid (head_of u)"
    | (RV) y Y where "is_rigid (head_of t)" "head_of u = Var y Y"
    | (RR) "is_rigid (head_of t)" "is_rigid (head_of u)"
    using hc[OF ty(1) nA(1)] hc[OF ty(2) nA(2)] by blast
  then show ?thesis
  proof cases
    case VV
    obtain Us where X: "tnorm ?\<theta> X = foldr fun_type Us B" using typed_head_Var[OF ty(1) VV(1)] ty(3) by metis
    obtain Us' where Y: "tnorm ?\<theta> Y = foldr fun_type Us' B" using typed_head_Var[OF ty(2) VV(2)] ty(3) by metis
    have tX: "tcons ?\<theta> X" "tcons ?\<theta> Y"
      using vps_tys[OF vps_head_of[OF VV(1)]] vps_tys[OF vps_head_of[OF VV(2)]] tct tcu by auto
    from body_type_ptnorm[OF ac tX(1) X ty(4)] obtain B1 where
      b1: "body_type env X = return B1" "tnorm ?\<theta> B1 = B" "tcons ?\<theta> B1" by blast
    from body_type_ptnorm[OF ac tX(2) Y ty(4)] obtain B2 where
      b2: "body_type env Y = return B2" "tnorm ?\<theta> B2 = B" "tcons ?\<theta> B2" by blast
    have cu: "cunify_types alg B1 B2 env = returnW env"
      by (rule cunify_types_same_mod[OF ac b1(3) b2(3)]) (simp add: b1(2) b2(2))
    have "okW (SIMPL0_step alg F ?dp env ffs frs) (env, ?dp # ffs, frs)"
      using VV b1(1) b2(1) cu by (simp add: SIMPL0_step_def return_def)
    moreover have "pff_shape env W ?dp" using ty nAt VV by (auto simp: pff_shape_def)
    moreover have "fch W ?\<theta> ?\<theta> [?dp]"
      using typed_hsat[OF ty(1) _ pi(6)] typed_hsat[OF ty(2) _ pi(6)] ty(3,4) ac(1) by auto
    ultimately show ?thesis
      using ptsresI[of alg ar A W env "[?dp]" "[]" env "[?dp]" ffs frs] pi0 hb ps[of ?dp]
      by (auto simp: cuok_def)
  next
    case VR
    have fr: "pfr_shape env W ?dp" using ty nAt VR by (auto simp: pfr_shape_def)
    from passignment_term[OF pi0 ty] ut
    consider (A) evs where "assignment alg rb t u env = Some (evs, UErr ASSIGN)"
      | (C) evs where "assignment alg rb t u env = Some (evs, UErr CANTUNIFY)"
      | (O) env' v T where "okW (assignment alg rb t u env) env'" "pinv alg ar A W env' []" "pextends env' env"
          "tyenv env' = tyenv env" "maxidx env' = maxidx env" "head_of t = Var v T"
          "\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v"
          "\<forall>\<rho> X. gsol alg ar ?\<theta> \<rho> \<longrightarrow> reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> u))"
      by blast
    then show ?thesis
    proof cases
      case A
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env, ffs, ?dp # frs)"
        using VR A by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep[OF fr pi0 hb(1)] show ?thesis by (auto simp: cuok_def)
    next
      case C
      then show ?thesis using VR
        by (cases "head_of u") (auto simp: SIMPL0_step_def handleW_def is_rigid_def bindW_def cuok_def raiseW_def)
    next
      case O
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env', ffs, frs)"
        using VR O(1) by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF O(2-5) O(8) O(7) O(6)] show ?thesis by (auto simp: cuok_def)
    qed
  next
    case RV
    have fr: "pfr_shape env W (rb, u, t)" using ty nAt RV by (auto simp: pfr_shape_def)
    from passignment_term[OF pinv_swap[OF pi0] ty(2,1,3,4)] uu
    consider (A) evs where "assignment alg rb u t env = Some (evs, UErr ASSIGN)"
      | (C) evs where "assignment alg rb u t env = Some (evs, UErr CANTUNIFY)"
      | (O) env' v T where "okW (assignment alg rb u t env) env'" "pinv alg ar A W env' []" "pextends env' env"
          "tyenv env' = tyenv env" "maxidx env' = maxidx env" "head_of u = Var v T"
          "\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v"
          "\<forall>\<rho> X. gsol alg ar ?\<theta> \<rho> \<longrightarrow> reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> t))"
      by blast
    then show ?thesis
    proof cases
      case A
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env, ffs, (rb, u, t) # frs)"
        using RV A by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep[OF fr pinv_swap[OF pi0] hb(2)] show ?thesis by (auto simp: cuok_def)
    next
      case C
      then show ?thesis using RV
        by (cases "head_of t") (auto simp: SIMPL0_step_def handleW_def is_rigid_def bindW_def cuok_def raiseW_def)
    next
      case O
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env', ffs, frs)"
        using RV O(1) by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF O(2-5) O(8) O(7) O(6)] show ?thesis by (auto simp: cuok_def)
    qed
  next
    case RR
    define h where "h = head_of t"
    define as where "as = snd (strip_comb t)"
    define h' where "h' = head_of u"
    define bs where "bs = snd (strip_comb u)"
    have t: "t = list_comb h as" using head_of_list_comb[of t] by (simp add: h_def as_def)
    have u0: "u = list_comb h' bs" using head_of_list_comb[of u] by (simp add: bs_def h'_def)
    have rig: "is_rigid h" "is_rigid h'" using RR by (simp_all add: h_def h'_def)
    have h0: "\<nexists>f u. h = f $ u" "\<nexists>f u. h' = f $ u" unfolding h_def h'_def using head_of_not_App by blast+
    have twh: "\<forall>U\<in>tys h \<union> tys h'. tyw ar ?\<theta> A U"
      using twd tys_head_of[of t] tys_head_of[of u] by (auto simp: h_def h'_def)
    have "(\<exists>evs. SIMPL0_step alg F ?dp env ffs frs = Some (evs, UErr CANTUNIFY)) \<or>
      (\<exists>env1. SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs) \<and>
        pinv alg ar A W env1 [?dp] \<and> pextends env1 env \<and> maxidx env \<le> maxidx env1 \<and>
        pstep alg ar A W [?dp] [] env env1 \<and> tnormt (tyenv env1) h' = tnormt (tyenv env1) h)"
    proof (cases h)
      case (Const a T)
      show ?thesis
      proof (cases "\<exists>U. h' = Const a U")
        case True
        then obtain U where h': "h' = Const a U" by blast
        have tw: "tyw ar ?\<theta> A T" "tyw ar ?\<theta> A U" using twh Const h' by auto
        from cunify_types_pterm[OF fin pi0 tw, of "[?dp]"] show ?thesis
        proof (elim disjE exE conjE)
          fix evs assume "cunify_types alg T U env = Some (evs, UErr CANTUNIFY)"
          then show ?thesis using Const h' by (auto simp: SIMPL0_step_def h_def h'_def bindW_def)
        next
          fix env1 assume c: "cunify_types alg T U env = returnW env1" "pinv alg ar A W env1 [?dp]"
            "tenv env1 = tenv env" "pextends env1 env" "maxidx env \<le> maxidx env1" "pstep alg ar A W [?dp] [] env env1"
            "tnorm (tyenv env1) T = tnorm (tyenv env1) U"
          have "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs)"
            using Const h' c(1)
            by (simp add: SIMPL0_step_def h_def h'_def bindW_def returnW_def option.map_ident option.map_id)
          with c Const h' show ?thesis by auto
        qed
      next
        case False
        then show ?thesis using Const rig(2)
          by (cases h') (auto simp: SIMPL0_step_def h_def h'_def raiseW_def is_rigid_def)
      qed
    next
      case (Free a T)
      show ?thesis
      proof (cases "\<exists>U. h' = Free a U")
        case True
        then obtain U where h': "h' = Free a U" by blast
        have tw: "tyw ar ?\<theta> A T" "tyw ar ?\<theta> A U" using twh Free h' by auto
        from cunify_types_pterm[OF fin pi0 tw, of "[?dp]"] show ?thesis
        proof (elim disjE exE conjE)
          fix evs assume "cunify_types alg T U env = Some (evs, UErr CANTUNIFY)"
          then show ?thesis using Free h' by (auto simp: SIMPL0_step_def h_def h'_def bindW_def)
        next
          fix env1 assume c: "cunify_types alg T U env = returnW env1" "pinv alg ar A W env1 [?dp]"
            "tenv env1 = tenv env" "pextends env1 env" "maxidx env \<le> maxidx env1" "pstep alg ar A W [?dp] [] env env1"
            "tnorm (tyenv env1) T = tnorm (tyenv env1) U"
          have "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs)"
            using Free h' c(1)
            by (simp add: SIMPL0_step_def h_def h'_def bindW_def returnW_def option.map_ident option.map_id)
          with c Free h' show ?thesis by auto
        qed
      next
        case False
        then show ?thesis using Free rig(2)
          by (cases h') (auto simp: SIMPL0_step_def h_def h'_def raiseW_def is_rigid_def)
      qed
    next
      case (Bound i)
      show ?thesis
      proof (cases "h' = Bound i")
        case True
        then have "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env, ffs, frs)"
          using Bound by (simp add: SIMPL0_step_def h_def h'_def)
        with pi0 Bound True show ?thesis by auto
      next
        case False
        then show ?thesis using Bound rig(2)
          by (cases h') (auto simp: SIMPL0_step_def h_def h'_def raiseW_def is_rigid_def)
      qed
    qed (use rig in \<open>auto simp: is_rigid_def\<close>)
    then show ?thesis
    proof (elim disjE exE conjE)
      fix evs assume "SIMPL0_step alg F ?dp env ffs frs = Some (evs, UErr CANTUNIFY)"
      then show ?thesis by (simp add: cuok_def)
    next
      fix env1 assume s1: "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs)"
        "pinv alg ar A W env1 [?dp]" "pextends env1 env" "maxidx env \<le> maxidx env1"
        "pstep alg ar A W [?dp] [] env env1" "tnormt (tyenv env1) h' = tnormt (tyenv env1) h"
      let ?\<theta>1 = "tyenv env1" and ?V1 = "tctx env1 W" and ?Ts1 = "map (tnorm (tyenv env1)) (map snd rb)"
      let ?args = "map (\<lambda>(a, b). (rb, a, b)) (zip as bs)"
      note pi1 = pinvD[OF s1(2)]
      have ac1: "tacyc ?\<theta>1" by (rule tinv_tacyc[OF pi1(2)])
      have te1: "textends ?\<theta> ?\<theta>1" using s1(3) by (simp add: pextends_def)
      have ty1: "typed env1 W (map snd rb) t B" "typed env1 W (map snd rb) u B"
        using typed_wcons[OF ac1 te1 pi(6) pi1(6) ty(1)] typed_wcons[OF ac1 te1 pi(6) pi1(6) ty(2)] by simp_all
      have nt1: "has_type ?V1 ?Ts1 (list_comb (tnormt ?\<theta>1 h) (map (tnormt ?\<theta>1) as)) (tnorm ?\<theta>1 B)"
        using ty1(1) t by (simp add: typed_def)
      have nu1: "has_type ?V1 ?Ts1 (list_comb (tnormt ?\<theta>1 h) (map (tnormt ?\<theta>1) bs)) (tnorm ?\<theta>1 B)"
        using ty1(2) u0 s1(6) by (simp add: typed_def)
      from nt1 obtain Vs where hV: "has_type ?V1 ?Ts1 (tnormt ?\<theta>1 h) (foldr fun_type Vs (tnorm ?\<theta>1 B))"
        and aV: "list_all2 (has_type ?V1 ?Ts1) (map (tnormt ?\<theta>1) as) Vs"
        by (auto simp: has_type_list_comb)
      from nu1 obtain Vs' where hV': "has_type ?V1 ?Ts1 (tnormt ?\<theta>1 h) (foldr fun_type Vs' (tnorm ?\<theta>1 B))"
        and bV: "list_all2 (has_type ?V1 ?Ts1) (map (tnormt ?\<theta>1) bs) Vs'"
        by (auto simp: has_type_list_comb)
      have VV: "Vs' = Vs" using foldr_fun_type_same_base[OF has_type_unique[OF hV' hV]] .
      have lV: "length Vs = length as" "length Vs' = length bs"
        using list_all2_lengthD[OF aV] list_all2_lengthD[OF bV] by simp_all
      have len: "length as = length bs" using lV VV by simp
      have nV: "tnorm ?\<theta>1 (Vs ! i) = Vs ! i" if "i < length as" for i
      proof (rule has_type_normal[OF list_all2_nthD[OF aV] ac1])
        show "i < length (map (tnormt ?\<theta>1) as)" using that by simp
        show "\<forall>x. tnorm ?\<theta>1 (?V1 x) = ?V1 x" by (simp add: tctx_normal[OF ac1])
        show "\<forall>T\<in>set ?Ts1. tnorm ?\<theta>1 T = T" by (auto simp: tnorm_idem[OF ac1])
        show "\<forall>T\<in>tys (map (tnormt ?\<theta>1) as ! i). tnorm ?\<theta>1 T = T"
          using that by (auto simp: tys_tnormt tnorm_idem[OF ac1])
      qed
      have tyarg: "typed env1 W (map snd rb) (as ! i) (Vs ! i)" "typed env1 W (map snd rb) (bs ! i) (Vs ! i)"
        if i: "i < length as" for i
        using list_all2_nthD[OF aV] list_all2_nthD[OF bV] i len lV VV nV[OF i] by (simp_all add: typed_def)
      have twa: "\<forall>U\<in>dtys (rb, as ! i, bs ! i). tyw ar ?\<theta> A U" if "i < length as" for i
        using twd that len t u0 by (auto simp: tys_list_comb)
      have pca: "pinv alg ar A W env1 [(rb, as ! i, bs ! i)]" if i: "i < length as" for i
      proof -
        have "swf_dp ar (rb, as ! i, bs ! i)" using swd i len t u0 by (simp add: swf_tm_list_comb)
        moreover have "\<forall>U\<in>dtys (rb, as ! i, bs ! i). tyw ar ?\<theta>1 A U"
          using twa[OF i] tyw_textends[OF ac1 te1] by blast
        moreover have "ptyped env1 W (rb, as ! i, bs ! i)" using tyarg[OF i] by auto
        moreover have "dp_below (maxidx env1) (rb, as ! i, bs ! i)"
          using bl i len t u0 below_mono[OF _ s1(4)] by (simp add: below_list_comb)
        ultimately show ?thesis using pinv_Nil[OF s1(2)] by (auto simp: pinv_def)
      qed
      have Fa: "cuok (F (rb, as ! i, bs ! i) st) (ptsres alg ar A W [(rb, as ! i, bs ! i)] st)"
        if i: "i < length as" and st: "pinv alg ar A W (fst st) []" "pextends (fst st) env1"
          "maxidx env1 \<le> maxidx (fst st)" "pstep alg ar A W [?dp] [] env1 (fst st)" for i st
      proof (rule IH[OF RR(1)])
        show "t = list_comb (head_of t) as" using t by (simp add: h_def)
        show "u = list_comb (head_of u) bs" using u0 by (simp add: h'_def)
        show "length as = length bs" by (rule len)
        show "i < length as" by (rule i)
        show "pinv alg ar A W (fst st) [(rb, as ! i, bs ! i)]"
          by (rule pinv_transfer[OF pca[OF i] st(1) _ st(3)]) (use st(2) in \<open>simp add: pextends_def\<close>)
        show "pextends (fst st) env" by (rule pextends_trans[OF st(2) s1(3)])
        show "maxidx env \<le> maxidx (fst st)" using s1(4) st(3) by simp
        show "pstep alg ar A W [?dp] [] env (fst st)"
          by (rule iffD1[OF pstep_set pstep_trans[OF s1(5) st(4)]]) auto
      qed
      have Dsub: "vps_dps ?args \<subseteq> vps t \<union> vps u"
        using t u0 by (fastforce simp: vps_list_comb dest: set_zip_leftD set_zip_rightD)
      have isub: "ivps \<rho> ?args \<subseteq> ivps \<rho> [?dp]" for \<rho>
        unfolding ivps_vps by (rule image_mono) (use Dsub in simp)
      have sr: "cuok (simrands F rb u (list_comb h as) (list_comb h' bs) (env1, ffs, frs))
          (ptsres alg ar A W ?args (env1, ffs, frs))"
        by (rule psimrands_term[where eo = env1 and D = "[?dp]", OF Fa h0 subset_trans[OF isub reach_incl] len])
          (use pinv_Nil[OF s1(2)] in simp_all)
      have p0: "ptsres alg ar A W [?dp] (env, ffs, frs) (env1, ffs, frs)"
        using ptsresI[of alg ar A W env1 "[]" "[]" env "[?dp]" ffs frs] pinv_Nil[OF s1(2)] s1(3-5) te1 by simp
      have sub2: "ivps \<rho> ([?dp] @ ?args) \<subseteq> reach (instE \<rho> env) (ivps \<rho> [?dp])" for \<rho>
      proof -
        have "ivps \<rho> ([?dp] @ ?args) = ivps \<rho> [?dp] \<union> ivps \<rho> ?args"
          by (simp only: map_append set_append image_Un Union_Un_distrib)
        also have "\<dots> \<subseteq> ivps \<rho> [?dp]" using isub[of \<rho>] by blast
        also have "\<dots> \<subseteq> reach (instE \<rho> env) (ivps \<rho> [?dp])" by (rule reach_incl)
        finally show ?thesis .
      qed
      have cu: "cuok (simrands F rb u (list_comb h as) (list_comb h' bs) (env1, ffs, frs))
          (ptsres alg ar A W [?dp] (env, ffs, frs))"
      proof (rule cuok_mono[OF sr])
        fix st' assume r: "ptsres alg ar A W ?args (env1, ffs, frs) st'"
        from ptsres_trans[OF p0 r] show "ptsres alg ar A W [?dp] (env, ffs, frs) st'"
          by (rule ptsres_mono_dps) (rule sub2)
      qed
      have "simrands F rb u t u (env1, ffs, frs) = simrands F rb u (list_comb h as) (list_comb h' bs) (env1, ffs, frs)"
        by (simp only: t[symmetric] u0[symmetric])
      then show ?thesis using s1(1) cu by simp
    qed
  qed
qed

end

context csig
begin

subsection \<open>Termination of \<open>SIMPL0\<close>\<close>

lemma pinv_inst_typed:
  assumes pi0: "pinv alg ar A W env [(rb, t, u)]" and g: "gsol alg ar (tyenv env) \<rho>"
  obtains T where "has_type (ityp \<rho> env W) (map snd (instb \<rho> rb)) (inst \<rho> t) T"
proof -
  note pi = pinvD[OF pi0]
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  from pi(4)[of "(rb, t, u)"] obtain T where ty: "\<forall>U\<in>dtys (rb, t, u). tyw ar (tyenv env) A U"
    and tt: "typed env W (map snd rb) t T"
    by auto
  have tc: "tcons (tyenv env) U" if "U \<in> dtys (rb, t, u)" for U
    using tyw_tcons[OF pi(2)] ty that by blast
  have tcT: "tcons (tyenv env) (tnorm (tyenv env) T)" by (rule tcons_tnorm[OF ac(1)])
  have "has_type (ityp \<rho> env W) (map (tsubst \<rho>) (map snd rb)) (inst \<rho> t) (tsubst \<rho> (tnorm (tyenv env) T))"
    by (rule typed_inst[OF ac sol _ tcT]) (use tc tt in \<open>auto simp: typed_tnorm[OF ac(1)]\<close>)
  then show ?thesis using that by (simp add: map_snd_instb)
qed

end

context wf_csig
begin

text \<open>Head normalization makes only reachable variables of every ground instance visible:\<close>

lemma head_norm_dpair_ivps:
  assumes pi0: "pinv alg ar A W env [(rb, t, u)]"
    and hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env')"
    and g: "gsol alg ar (tyenv env) \<rho>"
  shows "ivps \<rho> [(rb', t', u')] \<subseteq> reach (instE \<rho> env) (ivps \<rho> [(rb, t, u)])"
proof -
  show ?thesis
  proof (rule head_norm_dpair_pgen[OF pi0 g])
    fix rb'' t'' u'' T
    assume h: "okW (head_norm_dpair alg env (rb, t, u)) ((rb'', t'', u''), env)"
      "pinv alg ar A W env [(rb'', t'', u'')]"
      "tnorm (tyenv env) T = T" "typed env W (map snd rb) t T"
      "map (tnorm (tyenv env)) (map snd rb'') = rev (arg_types T) @ map (tnorm (tyenv env)) (map snd rb)"
      "typed env W (map snd rb'') t'' (res_type T)" "typed env W (map snd rb'') u'' (res_type T)"
      "\<not> is_Abs t''" "\<not> is_Abs u''" "\<not> is_Abs (head_of t'')" "\<not> is_Abs (head_of u'')"
      "\<And>F U. head_of t'' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
      "\<And>F U. head_of u'' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
      "vps (inst \<rho> t'') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
      "vps (inst \<rho> u'') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> u))"
      "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb'' t''" "env \<Turnstile> rlist_abs rb u \<approx> rlist_abs rb'' u''"
    from h(1) hd have "t'' = t'" "u'' = u'" by auto
    then show ?thesis
      using h(14,15) reach_subset[of "vps (inst \<rho> t)" "vps (inst \<rho> t) \<union> vps (inst \<rho> u)" "instE \<rho> env"]
        reach_subset[of "vps (inst \<rho> u)" "vps (inst \<rho> t) \<union> vps (inst \<rho> u)" "instE \<rho> env"]
      by auto
  qed
qed

text \<open>
  \<^const>\<open>SIMPL0\<close> terminates, by induction on the number of unbound type variables of the problem,
  the number of unbound variables of the ground instance that are reachable from the pair, and
  the size \<^const>\<open>dsz\<close> of the ground instance of the pair under a solution of the ground instance
  of the environment.
\<close>

lemma SIMPL0_pterm_aux:
  "(card (uvarsA (tyenv env) A), card (unb (instE \<rho> env) (ivps \<rho> [(rb, t, u)])),
      dsz (tau (ityp \<rho> env W)) \<sigma> (instb \<rho> rb) (inst \<rho> t) T) = p \<Longrightarrow>
    finite A \<Longrightarrow> pinv alg ar A W env [(rb, t, u)] \<Longrightarrow> gsol alg ar (tyenv env) \<rho> \<Longrightarrow>
    solution (ityp \<rho> env W) (tau (ityp \<rho> env W)) \<sigma> (instE \<rho> env) \<Longrightarrow>
    has_type (ityp \<rho> env W) (map snd (instb \<rho> rb)) (inst \<rho> t) T \<Longrightarrow>
    cuok (SIMPL0 alg (rb, t, u) (env, ffs, frs)) (ptsres alg ar A W [(rb, t, u)] (env, ffs, frs))"
proof (induction p arbitrary: rb t u T env \<rho> \<sigma> ffs frs
    rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_lex_prod[OF wf_less_than wf_less_than]]])
  case (1 p rb t u T env \<rho> \<sigma> ffs frs)
  note fin = "1.prems"(2) and pi0 = "1.prems"(3) and g = "1.prems"(4)
  let ?\<theta> = "tyenv env" and ?V = "ityp \<rho> env W"
  note pi = pinvD[OF pi0]
  have sol: "tsol ?\<theta> \<rho>" using g by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  note \<sigma> = solutionD[OF "1.prems"(5)]
  have Vw: "?V = (\<lambda>x. tsubst \<rho> (W x))" by (rule pinv_ityp[OF pi0 g])
  obtain rb' t' u' T0 where hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    and inv': "pinv alg ar A W env [(rb', t', u')]"
    and T0: "tnorm ?\<theta> T0 = T0" and tyt0: "typed env W (map snd rb) t T0"
    and rbn: "map (tnorm ?\<theta>) (map snd rb') = rev (arg_types T0) @ map (tnorm ?\<theta>) (map snd rb)"
    and ty': "typed env W (map snd rb') t' (res_type T0)" "typed env W (map snd rb') u' (res_type T0)"
    and nAt: "\<not> is_Abs t'" "\<not> is_Abs u'"
    and nA: "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    and ut: "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and vt: "vps (inst \<rho> t') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
      "vps (inst \<rho> u') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> u))"
    and eqv: "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'"
    by (rule head_norm_dpair_pgen[OF pi0 g]) blast
  have cs: "closed_on UNIV (\<sigma> \<circ> cren \<rho>)" "sat (\<sigma> \<circ> cren \<rho>) env"
    using closed_on_cren[OF \<sigma>(1)] \<sigma>(4) by (simp_all add: sat_instE)
  have eq: "mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb' t'))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb t)))"
    using equiv_sym[OF env_equivD[OF eqv cs]] by (simp add: mk_subst_inst)
  define B where "B = res_type T0"
  have nfB: "\<not> is_funT B" by (simp add: B_def res_type_base)
  have Bn: "tnorm ?\<theta> B = B" using tnorm_res_type[OF T0] by (simp add: B_def)
  from pi(4)[of "(rb, t, u)"] have tw: "\<forall>U\<in>snd ` set rb \<union> tys t. tyw ar ?\<theta> A U" by auto
  from pinvD(4)[OF inv', of "(rb', t', u')"]
  have tw': "\<forall>U\<in>snd ` set rb' \<union> tys t'. tyw ar ?\<theta> A U" by auto
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  have tsn: "tsubst \<rho> (tnorm ?\<theta> U) = tsubst \<rho> U" if "tyw ar ?\<theta> A U" for U
    by (rule tsubst_tnorm[OF ac sol tcU[OF that]])
  have tcT0: "tcons ?\<theta> T0" using tcons_tnorm[OF ac(1), of T0] T0 by simp
  have tcB: "tcons ?\<theta> B" using tcons_tnorm[OF ac(1), of B] Bn by simp
  have tyi: "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> t) (tsubst \<rho> T0)"
    using typed_inst[OF ac sol _ tcT0 tyt0] tw tcU by (auto simp: map_snd_instb)
  have TT0: "T = tsubst \<rho> T0" by (rule has_type_unique[OF "1.prems"(6) tyi])
  have tyi': "has_type ?V (map snd (instb \<rho> rb')) (inst \<rho> t') (tsubst \<rho> B)"
    using typed_inst[OF ac sol _ tcB ty'(1)[folded B_def]] tw' tcU by (auto simp: map_snd_instb)
  have m': "map (tsubst \<rho>) (map snd rb') = map (tsubst \<rho>) (map (tnorm ?\<theta>) (map snd rb'))"
    and m: "map (tsubst \<rho>) (map snd rb) = map (tsubst \<rho>) (map (tnorm ?\<theta>) (map snd rb))"
    using tw tw' tsn by auto
  have TT: "foldr fun_type (rev (map snd (instb \<rho> rb'))) (tsubst \<rho> B) =
      foldr fun_type (rev (map snd (instb \<rho> rb))) T"
  proof -
    have "map snd (instb \<rho> rb') = rev (map (tsubst \<rho>) (arg_types T0)) @ map snd (instb \<rho> rb)"
      using arg_cong[OF rbn, of "map (tsubst \<rho>)"] m m' by (simp add: map_snd_instb rev_map)
    then show ?thesis
      using arg_res_type[of T0] TT0 by (simp add: B_def tsubst_foldr_fun[symmetric])
  qed
  have dszeq: "dsz (tau ?V) \<sigma> (instb \<rho> rb') (inst \<rho> t') (tsubst \<rho> B) = dsz (tau ?V) \<sigma> (instb \<rho> rb) (inst \<rho> t) T"
    by (rule dsz_equiv[OF "1.prems"(6) tyi' TT _ \<sigma>(1,2)]) (use eq in \<open>simp add: inst_rlist_abs\<close>)
  let ?X = "ivps \<rho> [(rb, t, u)]" and ?D = "ivps \<rho> [(rb', t', u')]"
  have Dsub: "?D \<subseteq> reach (instE \<rho> env) ?X" by (rule head_norm_dpair_ivps[OF pi0 hd g])
  have "cuok (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs) (ptsres alg ar A W [(rb', t', u')] (env, ffs, frs))"
  proof (rule SIMPL0_step_pterm[OF fin inv' ty'[folded B_def] Bn nfB nAt nA ut uu])
    fix i and st :: sstate and as bs
    assume rig: "is_rigid (head_of t')" and t': "t' = list_comb (head_of t') as"
      and u': "u' = list_comb (head_of u') bs" and lab: "length as = length bs" and i: "i < length as"
      and ci: "pinv alg ar A W (fst st) [(rb', as ! i, bs ! i)]" and ex: "pextends (fst st) env"
      and mx: "maxidx env \<le> maxidx (fst st)" and ps: "pstep alg ar A W [(rb', t', u')] [] env (fst st)"
    obtain env1 ffs1 frs1 where st: "st = (env1, ffs1, frs1)" by (cases st)
    have ci1: "pinv alg ar A W env1 [(rb', as ! i, bs ! i)]" using ci st by simp
    show "cuok (SIMPL0 alg (rb', as ! i, bs ! i) st) (ptsres alg ar A W [(rb', as ! i, bs ! i)] st)"
    proof (cases "tyenv env1 = ?\<theta>")
      case False
      then have lt: "card (uvarsA (tyenv env1) A) < card (uvarsA ?\<theta> A)" using ps st by (auto simp: pstep_def)
      obtain \<rho>1 where g1: "gsol alg ar (tyenv env1) \<rho>1" by (rule pinv_gsol_exists[OF ci1])
      define \<sigma>1 where "\<sigma>1 = env_sol (instE \<rho>1 env1) (ityp \<rho>1 env1 W)"
      have sol1: "solution (ityp \<rho>1 env1 W) (tau (ityp \<rho>1 env1 W)) \<sigma>1 (instE \<rho>1 env1)"
        unfolding \<sigma>1_def by (rule pinv_env_sol[OF ci1 g1])
      obtain T1 where ty1: "has_type (ityp \<rho>1 env1 W) (map snd (instb \<rho>1 rb')) (inst \<rho>1 (as ! i)) T1"
        by (rule pinv_inst_typed[OF ci1 g1])
      have less: "((card (uvarsA (tyenv env1) A), card (unb (instE \<rho>1 env1) (ivps \<rho>1 [(rb', as ! i, bs ! i)])),
          dsz (tau (ityp \<rho>1 env1 W)) \<sigma>1 (instb \<rho>1 rb') (inst \<rho>1 (as ! i)) T1), p) \<in>
          less_than <*lex*> less_than <*lex*> less_than"
        using lt "1.prems"(1) by auto
      from "1.IH"[OF less refl fin ci1 g1 sol1 ty1, of ffs1 frs1] st show ?thesis by simp
    next
      case True
      have g1: "gsol alg ar (tyenv env1) \<rho>" using g True by simp
      have V1: "ityp \<rho> env1 W = ?V" using pinv_ityp[OF ci1 g1] Vw by simp
      have is1: "istep (\<lambda>x. tsubst \<rho> (W x)) ?D (instE \<rho> env) (instE \<rho> env1)"
        using ps st True g by (auto simp: pstep_def)
      have "inst \<rho> t' = list_comb (inst \<rho> (head_of t')) (map (inst \<rho>) as)"
        by (subst t') (simp add: inst_list_comb)
      with tyi' obtain Us where tyh: "has_type ?V (map snd (instb \<rho> rb')) (inst \<rho> (head_of t')) (foldr fun_type Us (tsubst \<rho> B))"
        and tyas: "list_all2 (has_type ?V (map snd (instb \<rho> rb'))) (map (inst \<rho>) as) Us"
        by (auto simp: has_type_list_comb)
      have "dsz (tau ?V) \<sigma> (instb \<rho> rb') (map (inst \<rho>) as ! i) (Us ! i) <
          dsz (tau ?V) \<sigma> (instb \<rho> rb') (list_comb (inst \<rho> (head_of t')) (map (inst \<rho>) as)) (tsubst \<rho> B)"
        by (rule dsz_args[OF tyh tyas _ \<sigma>(1,2,3)]) (use rig i in simp_all)
      also have "\<dots> = dsz (tau ?V) \<sigma> (instb \<rho> rb) (inst \<rho> t) T"
        using dszeq \<open>inst \<rho> t' = _\<close> by simp
      finally have lt: "dsz (tau ?V) \<sigma> (instb \<rho> rb') (inst \<rho> (as ! i)) (Us ! i) < dsz (tau ?V) \<sigma> (instb \<rho> rb) (inst \<rho> t) T"
        using i by simp
      have tyi0: "has_type ?V (map snd (instb \<rho> rb')) (inst \<rho> (as ! i)) (Us ! i)"
        using list_all2_nthD[OF tyas] i by simp
      have ib: "i < length bs" using i lab by simp
      have Ysub0: "ivps \<rho> [(rb', as ! i, bs ! i)] \<subseteq> ?D"
      proof -
        have "vps (as ! i) \<subseteq> vps t'" using i by (subst t') (auto simp: vps_list_comb)
        moreover have "vps (bs ! i) \<subseteq> vps u'" using ib by (subst u') (auto simp: vps_list_comb)
        ultimately show ?thesis by (auto simp: vps_inst)
      qed
      have Ysub: "ivps \<rho> [(rb', as ! i, bs ! i)] \<subseteq> reach (instE \<rho> env) ?D"
        using Ysub0 reach_incl by blast
      have finX: "finite ?X" "finite ?D" by simp_all
      have u1: "unb (instE \<rho> env1) (ivps \<rho> [(rb', as ! i, bs ! i)]) \<subseteq> unb (instE \<rho> env) ?X"
        using istep_unb[OF is1 Ysub] unb_reach_mono[OF Dsub] by blast
      have finU: "finite (unb (instE \<rho> env) ?X)"
        by (rule finite_subset[OF _ finite_reach[OF finX(1)]]) (auto simp: unb_def)
      show ?thesis
      proof (cases "same_lk (instE \<rho> env) (instE \<rho> env1)")
        case True
        have sol1: "solution (ityp \<rho> env1 W) (tau (ityp \<rho> env1 W)) \<sigma> (instE \<rho> env1)"
          using same_lk_solution[OF True] "1.prems"(5) V1 by simp
        have "card (unb (instE \<rho> env1) (ivps \<rho> [(rb', as ! i, bs ! i)])) \<le> card (unb (instE \<rho> env) ?X)"
          by (rule card_mono[OF finU u1])
        with lt "1.prems"(1) \<open>tyenv env1 = ?\<theta>\<close> V1 have less:
          "((card (uvarsA (tyenv env1) A), card (unb (instE \<rho> env1) (ivps \<rho> [(rb', as ! i, bs ! i)])),
            dsz (tau (ityp \<rho> env1 W)) \<sigma> (instb \<rho> rb') (inst \<rho> (as ! i)) (Us ! i)), p) \<in>
            less_than <*lex*> less_than <*lex*> less_than"
          by auto
        from "1.IH"[OF less refl fin ci1 g1 sol1, of ffs1 frs1] tyi0 V1 st show ?thesis by simp
      next
        case False
        define \<sigma>1 where "\<sigma>1 = env_sol (instE \<rho> env1) (ityp \<rho> env1 W)"
        have sol1: "solution (ityp \<rho> env1 W) (tau (ityp \<rho> env1 W)) \<sigma>1 (instE \<rho> env1)"
          unfolding \<sigma>1_def by (rule pinv_env_sol[OF ci1 g1])
        have ety: "env_typed (\<lambda>x. tsubst \<rho> (W x)) (instE \<rho> env1)"
          using env_invD(3)[OF penv_inv_inst[OF pinvD(1)[OF ci1] g1]] pinv_ityp[OF ci1 g1] by simp
        have "card (unb (instE \<rho> env1) (ivps \<rho> [(rb', as ! i, bs ! i)])) < card (unb (instE \<rho> env) ?D)"
          by (rule istep_unb_less[OF is1 Ysub finX(2) ety False])
        also have "\<dots> \<le> card (unb (instE \<rho> env) ?X)"
          by (rule card_mono[OF finU unb_reach_mono[OF Dsub]])
        finally have "card (unb (instE \<rho> env1) (ivps \<rho> [(rb', as ! i, bs ! i)])) < card (unb (instE \<rho> env) ?X)" .
        with "1.prems"(1) \<open>tyenv env1 = ?\<theta>\<close> have less:
          "((card (uvarsA (tyenv env1) A), card (unb (instE \<rho> env1) (ivps \<rho> [(rb', as ! i, bs ! i)])),
            dsz (tau (ityp \<rho> env1 W)) \<sigma>1 (instb \<rho> rb') (inst \<rho> (as ! i)) (Us ! i)), p) \<in>
            less_than <*lex*> less_than <*lex*> less_than"
          by auto
        from "1.IH"[OF less refl fin ci1 g1 sol1, of ffs1 frs1] tyi0 V1 st show ?thesis by simp
      qed
    qed
  qed
  moreover have "ivps \<rho>' [(rb', t', u')] \<subseteq> reach (instE \<rho>' env) (ivps \<rho>' [(rb, t, u)])"
    if "gsol alg ar ?\<theta> \<rho>'" for \<rho>'
    by (rule head_norm_dpair_ivps[OF pi0 hd that])
  ultimately have step: "cuok (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs)
      (ptsres alg ar A W [(rb, t, u)] (env, ffs, frs))"
    by (elim cuok_mono) (rule ptsres_mono_dps)
  have "SIMPL0 alg (rb, t, u) (env, ffs, frs) =
      bindW (head_norm_dpair alg env (rb, t, u)) (\<lambda>(dp, env). SIMPL0_step alg (SIMPL0 alg) dp env ffs frs)"
    by (simp add: SIMPL0_unfold)
  moreover have "cuok (bindW (head_norm_dpair alg env (rb, t, u))
      (\<lambda>(dp, env). SIMPL0_step alg (SIMPL0 alg) dp env ffs frs)) (ptsres alg ar A W [(rb, t, u)] (env, ffs, frs))"
  proof (rule cuok_bindW[where P = "\<lambda>x. x = ((rb', t', u'), env)"])
    show "cuok (head_norm_dpair alg env (rb, t, u)) (\<lambda>x. x = ((rb', t', u'), env))"
      using hd by (auto simp: cuok_def)
  qed (use step in auto)
  ultimately show ?case by simp
qed

theorem SIMPL0_pterm:
  assumes "finite A" "pinv alg ar A W env [dp]"
  shows "cuok (SIMPL0 alg dp (env, ffs, frs)) (ptsres alg ar A W [dp] (env, ffs, frs))"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF assms(2)])
  obtain T where ty: "has_type (ityp \<rho> env W) (map snd (instb \<rho> rb)) (inst \<rho> t) T"
    by (rule pinv_inst_typed[OF assms(2)[unfolded dp] g])
  from SIMPL0_pterm_aux[OF refl assms(1) assms(2)[unfolded dp] g pinv_env_sol[OF assms(2) g] ty, of ffs frs] dp
  show ?thesis by simp
qed

end


context csig
begin

subsection \<open>Termination of \<open>SIMPL\<close>\<close>

lemma ptsres_set:
  assumes "set dps = set dps'"
  shows "ptsres alg ar A W dps st st' = ptsres alg ar A W dps' st st'"
  unfolding ptsres_def using pstep_set[OF assms refl] by simp

lemma pstep_mono_dps2:
  assumes "pstep alg ar A W dps' n env env'"
    and sub: "\<And>\<rho>. tyenv env' = tyenv env \<Longrightarrow> gsol alg ar (tyenv env) \<rho> \<Longrightarrow>
      ivps \<rho> dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
  shows "pstep alg ar A W dps n env env'"
proof (cases "tyenv env' = tyenv env")
  case True
  show ?thesis by (rule pstep_mono_dps[OF assms(1) sub[OF True]])
next
  case False
  with assms(1) show ?thesis by (auto simp: pstep_def)
qed

lemma pvtyped_pinv:
  assumes "pinv alg ar A W env dps" "(rb, t, u) \<in> set dps"
  shows "pvtyped env W t" "pvtyped env W u"
proof -
  note pi = pinvD[OF assms(1)]
  from pi(4)[OF assms(2)] obtain T where tw: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar (tyenv env) A U"
    and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T" by auto
  have "pvtyped env W s" if "s = t \<or> s = u" "typed env W (map snd rb) s T" for s
    unfolding pvtyped_def
  proof (intro ballI, clarify)
    fix x U assume xU: "(x, U) \<in> vps s"
    have "tyw ar (tyenv env) A U" using tw vps_tys[OF xU] that(1) by auto
    then show "tcons (tyenv env) U \<and> tnorm (tyenv env) U = tnorm (tyenv env) (W x)"
      using tyw_tcons[OF pi(2)] typed_vps[OF that(2) xU] wcons_tctx[OF pi(6)] by simp
  qed
  then show "pvtyped env W t" "pvtyped env W u" using ty by blast+
qed

end

context wf_csig
begin

lemma foldrW_SIMPL0_pterm:
  "finite A \<Longrightarrow> pinv alg ar A W env dps \<Longrightarrow>
    cuok (foldrW (SIMPL0 alg) dps (env, [], [])) (ptsres alg ar A W dps (env, [], []))"
proof (induction dps)
  case Nil
  then show ?case using ptsres_refl[OF pinv_Nil[OF Nil(2)]] by simp
next
  case (Cons dp dps)
  from Cons.prems(2) have c1: "pinv alg ar A W env [dp]" and c2: "pinv alg ar A W env dps"
    by (simp_all add: pinv_def)
  have "cuok (bindW (foldrW (SIMPL0 alg) dps (env, [], [])) (SIMPL0 alg dp)) (ptsres alg ar A W (dp # dps) (env, [], []))"
  proof (rule cuok_bindW[OF Cons.IH[OF Cons.prems(1) c2]])
    fix st1 assume r1: "ptsres alg ar A W dps (env, [], []) st1"
    obtain env1 ffn frn where s1: "st1 = (env1, ffn @ [], frn @ [])" "pinv alg ar A W env1 (ffn @ frn)"
      "pextends env1 env" "maxidx env \<le> maxidx env1"
      by (rule ptsresD[OF r1])
    have "pinv alg ar A W env1 [dp]"
      by (rule pinv_transfer[OF c1 pinv_Nil[OF s1(2)] _ s1(4)]) (use s1(3) in \<open>simp add: pextends_def\<close>)
    from SIMPL0_pterm[OF Cons.prems(1) this, of ffn frn]
    have "cuok (SIMPL0 alg dp st1) (ptsres alg ar A W [dp] st1)" using s1(1) by simp
    then show "cuok (SIMPL0 alg dp st1) (ptsres alg ar A W (dp # dps) (env, [], []))"
    proof (rule cuok_mono)
      fix st2 assume "ptsres alg ar A W [dp] st1 st2"
      from ptsres_trans[OF r1 this] have "ptsres alg ar A W (dps @ [dp]) (env, [], []) st2" .
      then show "ptsres alg ar A W (dp # dps) (env, [], []) st2"
        using ptsres_set[of "dps @ [dp]" "dp # dps"] by simp
    qed
  qed
  then show ?case by simp
qed

end

context csig
begin

text \<open>The result of \<^const>\<open>SIMPL\<close>, as \<^const>\<open>psimpl_res\<close>:\<close>

definition ptsimpl_res :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    dpair list \<Rightarrow> env \<Rightarrow> sstate \<Rightarrow> bool" where
  "ptsimpl_res alg ar A W dps env st' \<longleftrightarrow> (case st' of (env', ffs, frs) \<Rightarrow>
    pinv alg ar A W env' (ffs @ frs) \<and> pextends env' env \<and> maxidx env \<le> maxidx env' \<and>
    pstep alg ar A W dps (ffs @ frs) env env' \<and>
    (\<forall>dp\<in>set ffs. pff_shape env' W dp) \<and> (\<forall>dp\<in>set frs. pfr_shape env' W dp) \<and>
    (\<forall>dp\<in>set (ffs @ frs). heads_unb env' dp) \<and> fch W (tyenv env') (tyenv env) ffs)"

end

context wf_csig
begin

lemma SIMPL_pterm_aux:
  "(card (uvarsA (tyenv env) A), card (unb (instE \<rho> env) (ivps \<rho> dps))) = p \<Longrightarrow> finite A \<Longrightarrow>
    pinv alg ar A W env dps \<Longrightarrow> gsol alg ar (tyenv env) \<rho> \<Longrightarrow>
    cuok (SIMPL alg env dps) (ptsimpl_res alg ar A W dps env)"
proof (induction p arbitrary: env dps \<rho> rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  case (1 p env dps \<rho>)
  note fin = "1.prems"(2) and pi0 = "1.prems"(3) and g = "1.prems"(4)
  have body: "SIMPL alg env dps = do {
      st \<leftarrow> foldrW (SIMPL0 alg) dps (env, [], []);
      case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then SIMPL alg env' dps else returnW st}}"
    by (subst SIMPL.simps) (rule refl)
  have "cuok (bindW (foldrW (SIMPL0 alg) dps (env, [], [])) (\<lambda>st. case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then SIMPL alg env' dps else returnW st}))
      (ptsimpl_res alg ar A W dps env)"
  proof (rule cuok_bindW[OF foldrW_SIMPL0_pterm[OF fin pi0]])
    fix st1 assume r1: "ptsres alg ar A W dps (env, [], []) st1"
    obtain env1 ffs frs where s1: "st1 = (env1, ffs @ [], frs @ [])" "pinv alg ar A W env1 (ffs @ frs)"
      "pextends env1 env" "maxidx env \<le> maxidx env1" "pstep alg ar A W dps (ffs @ frs) env env1"
      "\<And>dp. dp \<in> set ffs \<Longrightarrow> pff_shape env1 W dp" "\<And>dp. dp \<in> set frs \<Longrightarrow> pfr_shape env1 W dp"
      "\<And>dp. dp \<in> set (ffs @ frs) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env1) (tyenv env) ffs"
      by (rule ptsresD[OF r1]) (rule that)
    let ?\<theta>1 = "tyenv env1"
    note pi1 = pinvD[OF s1(2)]
    have ok1: "tyok env1" by (rule tyok_tinv[OF pi1(2)])
    have bt1: "tcons ?\<theta>1 U" if "vt_lookup (tenv env1) x = Some (U, u)" for x U u
      using etysI[OF that] pi1(3) tyw_tcons[OF pi1(2)] by blast
    define dps' where "dps' = frs @ ffs"
    have c1: "pinv alg ar A W env1 dps'" using s1(2) by (auto simp: pinv_def dps'_def)
    define ch where "ch = (\<lambda>s. \<exists>x T. head_of s = Var x T \<and> vt_lookup (tenv env1) x \<noteq> None)"
    have ex: "existsM (\<lambda>(_, t, u). do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) dps' =
      return (\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
    proof (rule existsM_return)
      fix dp assume dp: "dp \<in> set dps'"
      obtain rb t u where dp0: "dp = (rb, t, u)" by (cases dp)
      note pv = pvtyped_pinv[OF c1 dp[unfolded dp0]]
      show "(case dp of (_, t, u) \<Rightarrow> do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) =
        return (case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
        by (auto simp: dp0 changed_ptyped[OF ok1 pi1(6) bt1 pv(1)] changed_ptyped[OF ok1 pi1(6) bt1 pv(2)]
          ch_def return_def)
    qed
    show "cuok (case st1 of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then SIMPL alg env' dps else returnW st1})
      (ptsimpl_res alg ar A W dps env)"
    proof (cases "\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u")
      case False
      have "heads_unb env1 dp" if "dp \<in> set (ffs @ frs)" for dp
      proof -
        obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
        with that have "(rb, t, u) \<in> set dps'" by (auto simp: dps'_def)
        with False have "\<not> ch t" "\<not> ch u" by auto
        then show ?thesis unfolding dp heads_unb_def prod.case ch_def by blast
      qed
      then have "ptsimpl_res alg ar A W dps env (env1, ffs, frs)"
        using s1 by (auto simp: ptsimpl_res_def)
      then show ?thesis using s1(1) ex False by (simp add: dps'_def return_def)
    next
      case True
      then obtain rb t u where dp: "(rb, t, u) \<in> set dps'" and cht: "ch t \<or> ch u" by blast
      obtain s x T where s: "s \<in> {t, u}" "head_of s = Var x T" "vt_lookup (tenv env1) x \<noteq> None"
        using cht unfolding ch_def by blast
      have hb: "heads_unb env (rb, t, u)" using s1(8) dp by (auto simp: dps'_def)
      then have xu: "vt_lookup (tenv env) x = None" using s(1,2) unfolding heads_unb_def prod.case by blast
      have r2: "cuok (SIMPL alg env1 dps') (ptsimpl_res alg ar A W dps' env1)"
      proof (cases "?\<theta>1 = tyenv env")
        case False
        then have lt: "card (uvarsA ?\<theta>1 A) < card (uvarsA (tyenv env) A)" using s1(5) by (auto simp: pstep_def)
        obtain \<rho>1 where g1: "gsol alg ar ?\<theta>1 \<rho>1" by (rule pinv_gsol_exists[OF c1])
        have "((card (uvarsA ?\<theta>1 A), card (unb (instE \<rho>1 env1) (ivps \<rho>1 dps'))), p) \<in> less_than <*lex*> less_than"
          using lt "1.prems"(1) by auto
        from "1.IH"[OF this refl fin c1 g1] show ?thesis .
      next
        case True
        have g1: "gsol alg ar ?\<theta>1 \<rho>" using g True by simp
        from s1(5) True g have is1: "istep (\<lambda>x. tsubst \<rho> (W x)) (ivps \<rho> dps) (instE \<rho> env) (instE \<rho> env1)"
          and v0: "ivps \<rho> (ffs @ frs) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
          by (auto simp: pstep_def)
        have v1: "ivps \<rho> dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)" using v0 by (auto simp: dps'_def)
        let ?y = "(x, tsubst \<rho> T)"
        have "?y \<in> vps (inst \<rho> s)" using vps_head_of[OF s(2)] by (force simp: vps_inst)
        moreover have "vps (inst \<rho> s) \<subseteq> ivps \<rho> dps'" using dp s(1) by force
        ultimately have xr: "?y \<in> reach (instE \<rho> env) (ivps \<rho> dps)" using v1 by blast
        have xin: "?y \<in> unb (instE \<rho> env) (ivps \<rho> dps)" using xr xu by (simp add: unb_def lk_def)
        have xout: "?y \<notin> unb (instE \<rho> env1) (ivps \<rho> dps')"
        proof -
          from s(3) obtain U w where b: "vt_lookup (tenv env1) x = Some (U, w)" by auto
          have pv: "pvtyped env1 W s" using pvtyped_pinv[OF c1 dp] s(1) by auto
          then have T: "tcons ?\<theta>1 T" "tnorm ?\<theta>1 T = tnorm ?\<theta>1 (W x)"
            using vps_head_of[OF s(2)] by (auto simp: pvtyped_def)
          have "tnorm ?\<theta>1 U = tnorm ?\<theta>1 (W x)" using pi1(6) b unfolding wcons_def by blast
          moreover have ac1: "tacyc ?\<theta>1" "tcons_env ?\<theta>1" using tinv_tacyc[OF pi1(2)] tinv_tcons_env[OF pi1(2)] by simp_all
          moreover have "tsol ?\<theta>1 \<rho>" using g1 by (simp add: gsol_def)
          ultimately have "tsubst \<rho> U = tsubst \<rho> T"
            using tsubst_tnorm[OF ac1, of \<rho> U] tsubst_tnorm[OF ac1, of \<rho> T] T bt1[OF b] by simp
          with b show ?thesis by (simp add: unb_def lk_def)
        qed
        have sub: "unb (instE \<rho> env1) (ivps \<rho> dps') \<subseteq> unb (instE \<rho> env) (ivps \<rho> dps)"
          by (rule istep_unb[OF is1 v1])
        have "finite (vps_dp dp)" for dp by (cases dp) simp
        then have finU: "finite (unb (instE \<rho> env) (ivps \<rho> dps))" by (intro finite_unb) simp
        have "card (unb (instE \<rho> env1) (ivps \<rho> dps')) < card (unb (instE \<rho> env) (ivps \<rho> dps))"
          using sub xin xout by (intro psubset_card_mono[OF finU]) blast
        then have "((card (uvarsA ?\<theta>1 A), card (unb (instE \<rho> env1) (ivps \<rho> dps'))), p) \<in> less_than <*lex*> less_than"
          using True "1.prems"(1) by auto
        from "1.IH"[OF this refl fin c1 g1] show ?thesis .
      qed
      have "cuok (SIMPL alg env1 dps') (ptsimpl_res alg ar A W dps env)"
      proof (rule cuok_mono[OF r2])
        fix st' assume r: "ptsimpl_res alg ar A W dps' env1 st'"
        obtain env2 ffs2 frs2 where st': "st' = (env2, ffs2, frs2)" by (cases st')
        from r st' have r': "pinv alg ar A W env2 (ffs2 @ frs2)" "pextends env2 env1" "maxidx env1 \<le> maxidx env2"
          "pstep alg ar A W dps' (ffs2 @ frs2) env1 env2"
          "\<forall>dp\<in>set ffs2. pff_shape env2 W dp" "\<forall>dp\<in>set frs2. pfr_shape env2 W dp"
          "\<forall>dp\<in>set (ffs2 @ frs2). heads_unb env2 dp" "fch W (tyenv env2) (tyenv env1) ffs2"
          by (auto simp: ptsimpl_res_def)
        have "pstep alg ar A W (dps @ dps') ((ffs2 @ frs2) @ ffs @ frs) env env2"
          by (rule pstep_trans[OF s1(5) r'(4)])
        then have "pstep alg ar A W dps ((ffs2 @ frs2) @ ffs @ frs) env env2"
        proof (rule pstep_mono_dps2)
          fix \<rho>' assume te: "tyenv env2 = tyenv env" and g': "gsol alg ar (tyenv env) \<rho>'"
          have "tyenv env1 = tyenv env"
          proof (rule ccontr)
            assume ne: "tyenv env1 \<noteq> tyenv env"
            then have "card (uvarsA (tyenv env1) A) < card (uvarsA (tyenv env) A)" using s1(5) by (auto simp: pstep_def)
            moreover have "tyenv env2 = tyenv env1 \<or> card (uvarsA (tyenv env2) A) < card (uvarsA (tyenv env1) A)"
              using r'(4) by (auto simp: pstep_def)
            ultimately show False using te ne by auto
          qed
          then have "ivps \<rho>' (ffs @ frs) \<subseteq> reach (instE \<rho>' env) (ivps \<rho>' dps)"
            using s1(5) g' by (auto simp: pstep_def)
          then have "ivps \<rho>' dps' \<subseteq> reach (instE \<rho>' env) (ivps \<rho>' dps)" by (auto simp: dps'_def)
          then show "ivps \<rho>' (dps @ dps') \<subseteq> reach (instE \<rho>' env) (ivps \<rho>' dps)"
            using reach_incl[of "ivps \<rho>' dps" "instE \<rho>' env"] by auto
        qed
        then have "pstep alg ar A W dps (ffs2 @ frs2) env env2" by (rule pstep_weaken) auto
        moreover have "pextends env2 env" by (rule pextends_trans[OF r'(2) s1(3)])
        moreover have "maxidx env \<le> maxidx env2" using s1(4) r'(3) by simp
        moreover have "fch W (tyenv env2) (tyenv env) ffs2" using fch_down[OF r'(8) pextendsD(2)[OF s1(3)]] .
        ultimately show "ptsimpl_res alg ar A W dps env st'" using r' st' by (simp add: ptsimpl_res_def)
      qed
      then show ?thesis using s1(1) ex True by (simp add: dps'_def return_def)
    qed
  qed
  then show ?case by (simp add: body)
qed

theorem SIMPL_pterm:
  assumes "finite A" "pinv alg ar A W env dps"
  shows "cuok (SIMPL alg env dps) (ptsimpl_res alg ar A W dps env)"
proof -
  obtain \<rho> where "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF assms(2)])
  from SIMPL_pterm_aux[OF refl assms this] show ?thesis .
qed

end

end
