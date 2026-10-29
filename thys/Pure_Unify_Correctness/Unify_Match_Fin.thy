section \<open>Finiteness of \<open>MATCH\<close>\<close>

theory Unify_Match_Fin
  imports Unify_Dead
begin

text \<open>
  \<open>matchcopy\<close> copies the rigid side \<open>u\<close> of a flex-rigid pair; it copies the arguments of an
  imitation when its sequence is pulled, after head-normalizing them in the environment of the
  copies of the arguments to their right. The projections of these copies may assign variables
  and thus change the arguments still to be copied. We measure an argument by the size of its
  instance under the canonical solution of the environment (\<^const>\<open>env_sol\<close>), \<open>\<eta>\<close>-long and
  \<open>\<beta>\<close>-normal: by the results of \<^theory>\<open>Pure_Unify_Correctness.Unify_Dead\<close>, it changes only
  when one of the finitely many variables of the original problem is assigned.
\<close>


subsection \<open>The size of instances\<close>

definition isz :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> nat" where
  "isz env V Bs t T = lsize (bnd_env Bs) (tau V) (\<beta>_nf (mk_subst (env_sol env V) (tr t))) (trty T)"

context
  fixes ar V env
  assumes ei: "env_inv ar V env"
begin

lemma esol: "solution V (tau V) (env_sol env V) env"
  using env_solution(1) env_invD[OF ei] by blast

lemma inst_typed: "has_type V Bs t T \<Longrightarrow> (bnd_env Bs, tau V) \<turnstile> mk_subst (env_sol env V) (tr t) : trty T"
  by (rule typing_mk_subst[OF has_type_tr typed_on_mono[OF solutionD(2)[OF esol] FV_tr_range]])

lemma inst_nf:
  assumes "has_type V Bs t T"
  shows "(bnd_env Bs, tau V) \<turnstile> \<beta>_nf (mk_subst (env_sol env V) (tr t)) : trty T"
    "no_redex (\<beta>_nf (mk_subst (env_sol env V) (tr t)))"
    "\<beta>_nf (mk_subst (env_sol env V) (tr t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (env_sol env V) (tr t)"
proof -
  let ?s = "mk_subst (env_sol env V) (tr t)"
  note ty = inst_typed[OF assms]
  show "(bnd_env Bs, tau V) \<turnstile> \<beta>_nf ?s : trty T" by (rule subject_reduction'[OF \<beta>_nf_reduces ty])
  show "no_redex (\<beta>_nf ?s)"
    by (rule beta_normal_no_redex[OF \<beta>_nf_normal[OF typable_termip[OF typableI[OF ty]]]])
  show "\<beta>_nf ?s \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?s" by (rule equiv_sym[OF beta_into_equiv[OF \<beta>_nf_reduces]])
qed

text \<open>Terms with \<open>\<beta>\<eta>\<close>-equivalent instances have instances of the same size.\<close>

lemma isz_equiv:
  assumes "has_type V Bs t T" "has_type V Bs t' T"
    "mk_subst (env_sol env V) (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (env_sol env V) (tr t')"
  shows "isz env V Bs t T = isz env V Bs t' T"
  unfolding isz_def
proof (rule lsize_equiv)
  note n = inst_nf[OF assms(1)] and n' = inst_nf[OF assms(2)]
  show "\<beta>_nf (mk_subst (env_sol env V) (tr t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<beta>_nf (mk_subst (env_sol env V) (tr t'))"
    using equiv_trans[OF equiv_trans[OF n(3) assms(3)] equiv_sym[OF n'(3)]] .
qed (use inst_nf[OF assms(1)] inst_nf[OF assms(2)] in auto)

end

lemma funs_inj_len: "Ts \<Rrightarrow> T = Us \<Rrightarrow> T \<Longrightarrow> length Ts = length Us \<Longrightarrow> Ts = Us"
proof (induction Ts arbitrary: Us)
  case (Cons A Ts)
  then show ?case by (cases Us) auto
qed simp

context
  fixes ar V env
  assumes ei: "env_inv ar V env"
begin

lemma isz_Abs:
  assumes "has_type V Bs (Abs a A b) (A \<rightarrow>\<^sub>T U)"
  shows "isz env V Bs (Abs a A b) (A \<rightarrow>\<^sub>T U) = isz env V (A # Bs) b U"
proof -
  have "typable (dB.Abs (mk_subst (env_sol env V) (tr b)))"
    using typableI[OF inst_typed[OF ei assms]] by simp
  then show ?thesis by (simp add: isz_def \<beta>_nf_Abs bnd_env_Cons)
qed

text \<open>The arguments of a rigid term have smaller instances.\<close>

lemma isz_rigid_arg:
  assumes r: "is_rigid h" and tyh: "has_type V Bs h (foldr fun_type As U)"
    and tys: "list_all2 (has_type V Bs) ts As" and i: "i < length ts"
  shows "isz env V Bs (ts ! i) (As ! i) < isz env V Bs (list_comb h ts) U"
proof -
  let ?\<sigma> = "env_sol env V"
  let ?h = "tr h" and ?ws = "map (\<lambda>t. mk_subst ?\<sigma> (tr t)) ts"
  have ty: "has_type V Bs (list_comb h ts) U" using tyh tys by (auto simp: has_type_list_comb)
  have hh: "mk_subst ?\<sigma> ?h = ?h" and at: "(\<exists>n. ?h = dB.Var n) \<or> (\<exists>j. ?h = BVar j)"
    using r rigid_substD[OF solutionD(3)[OF esol[OF ei]]] by (auto simp: is_rigid_def)
  have e: "mk_subst ?\<sigma> (tr (list_comb h ts)) = ?h \<degree>\<degree> ?ws"
    using hh by (simp add: tr_list_comb mk_subst_list_app comp_def)
  note n = inst_nf[OF ei ty]
  have nf: "\<beta>_nf (?h \<degree>\<degree> ?ws) = ?h \<degree>\<degree> map \<beta>_nf ?ws"
    by (rule \<beta>_nf_atom_apps[OF _ at]) (use typableI[OF inst_typed[OF ei ty]] e in simp)
  have tyf: "(bnd_env Bs, tau V) \<turnstile> ?h \<degree>\<degree> map \<beta>_nf ?ws : trty U" using n(1) e nf by simp
  then obtain Ts where th: "(bnd_env Bs, tau V) \<turnstile> ?h : Ts \<Rrightarrow> trty U"
    and tws: "(bnd_env Bs, tau V) \<tturnstile> map \<beta>_nf ?ws : Ts"
    by (elim list_app_typeE)
  have lT: "length Ts = length ts" using typings_length[OF tws] by simp
  have th': "(bnd_env Bs, tau V) \<turnstile> ?h : map trty As \<Rrightarrow> trty U"
    using has_type_tr[OF tyh] by (simp add: trty_foldr)
  have "Ts \<Rrightarrow> trty U = map trty As \<Rrightarrow> trty U" using th th' at by auto
  then have Ts: "Ts = map trty As" using funs_inj_len lT list_all2_lengthD[OF tys] by force
  have nr: "\<forall>w\<in>set (map \<beta>_nf ?ws). no_redex w"
  proof
    fix w assume "w \<in> set (map \<beta>_nf ?ws)"
    then obtain t where t: "t \<in> set ts" "w = \<beta>_nf (mk_subst ?\<sigma> (tr t))" by auto
    from t(1) tys obtain A where "has_type V Bs t A" by (metis in_set_conv_nth list_all2_conv_all_nth)
    from inst_nf(2)[OF ei this] t(2) show "no_redex w" by simp
  qed
  have "lsize (bnd_env Bs) (tau V) (?h \<degree>\<degree> map \<beta>_nf ?ws) (trty U) =
      Suc (\<Sum>j<length ts. lsize (bnd_env Bs) (tau V) (map \<beta>_nf ?ws ! j) (Ts ! j)) + (tsize (trty U) - 1)"
    using lsize_atom_apps[OF _ th tws nr] at by auto
  moreover have "lsize (bnd_env Bs) (tau V) (map \<beta>_nf ?ws ! i) (Ts ! i) \<le>
      (\<Sum>j<length ts. lsize (bnd_env Bs) (tau V) (map \<beta>_nf ?ws ! j) (Ts ! j))"
    using i by (intro member_le_sum) auto
  ultimately show ?thesis
    using i Ts list_all2_lengthD[OF tys] by (simp add: isz_def e nf)
qed

end

subsection \<open>Instances under extensions\<close>

lemma spine_type_cong: "(\<And>n. n \<in> FV s \<Longrightarrow> \<tau> n = \<tau>' n) \<Longrightarrow> spine_type e \<tau> s = spine_type e \<tau>' s"
  by (induction s) auto

lemma hsize_lsize_cong:
  "(\<And>n. n \<in> FV s \<Longrightarrow> \<tau> n = \<tau>' n) \<Longrightarrow> hsize e \<tau> s = hsize e \<tau>' s \<and> lsize e \<tau> s T = lsize e \<tau>' s T"
proof (induction s arbitrary: e T)
  case (App s t)
  then show ?case using spine_type_cong[of s \<tau> \<tau>' e] by auto
qed auto

lemma vars_eq_vps: "vars t = fst ` vps t"
  by (induction t) auto

text \<open>The variables reachable from consistently typed variables are consistently typed.\<close>

lemma reach_vtyped:
  assumes ety: "env_typed V env" and X: "\<forall>y\<in>X. V (fst y) = snd y" and y: "y \<in> reach env X"
  shows "V (fst y) = snd y"
proof -
  from y obtain x where x: "x \<in> X" "(y, x) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  from x(2) show ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    with X x(1) show ?case by blast
  next
    case (step y z)
    from step.hyps(1) obtain u where lk: "lk env (fst z) (snd z) = Some u" and yu: "y \<in> vps u"
      by (auto simp: dep_def)
    from env_typedD[OF ety lkD[OF lk]] have "has_type V [] u (snd z)" by simp
    from has_type_vps[OF this, of "fst y" "snd y"] yu show ?case by simp
  qed
qed

text \<open>
  The canonical solution does not change on the variables reachable from \<open>X\<close> if none of them
  is assigned, and the types of the unbound ones do not change.
\<close>

lemma env_sol_reach:
  assumes ei: "env_inv ar V env" and ei': "env_inv ar V' env'" and ext: "extends env' env"
    and X: "\<forall>y\<in>X. V (fst y) = snd y"
    and R: "\<And>y. y \<in> reach env X \<Longrightarrow> lk env (fst y) (snd y) = None \<Longrightarrow>
      lk env' (fst y) (snd y) = None \<and> V' (fst y) = V (fst y)"
  shows "(x, T) \<in> reach env X \<Longrightarrow> env_sol env' V' (code (AVar x)) = env_sol env V (code (AVar x))"
proof (induction x arbitrary: T rule: wf_induct_rule[OF wf_dvar[OF env_invD(1,3)[OF ei]]])
  case (1 x)
  note e = env_invD[OF ei] and e' = env_invD[OF ei']
  have Tx: "V x = T" using reach_vtyped[OF e(3) X "1.prems"] by simp
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case None
    then have "lk env x T = None" by (simp add: lk_def)
    from R[OF "1.prems"] this have n': "lk env' x T = None" and V': "V' x = V x" by simp_all
    have "vt_lookup (tenv env') x = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env') x \<noteq> None"
      then obtain U u where "vt_lookup (tenv env') x = Some (U, u)" by auto
      moreover from this env_typedD[OF e'(3)] have "U = T" using V' Tx by auto
      ultimately show False using n' by (simp add: lk_def)
    qed
    then show ?thesis
      using env_map_unbound[OF e(1,3) None] env_map_unbound[OF e'(1,3)] V' by (simp add: env_sol_def)
  next
    case (Some b)
    then obtain U u where b: "vt_lookup (tenv env) x = Some (U, u)" by (cases b) auto
    have b': "vt_lookup (tenv env') x = Some (U, u)" using ext b unfolding extends_def by (cases x) auto
    have UT: "U = T" using env_typedD[OF e(3) b] Tx by simp
    have tu: "has_type V [] u U" using env_typedD[OF e(3) b] by simp
    have "mk_subst (env_sol env' V') (tr u) = mk_subst (env_sol env V) (tr u)"
    proof (rule mk_subst_cong)
      fix n assume "n \<in> FV (tr u)"
      from FV_tr[OF this] show "env_sol env' V' n = env_sol env V n"
      proof
        assume "rigid_code n"
        then show ?thesis using env_map_rigid[OF e(1,3)] env_map_rigid[OF e'(1,3)] by (simp add: env_sol_def)
      next
        assume "\<exists>y\<in>vars u. n = code (AVar y)"
        then obtain y where y: "y \<in> vars u" "n = code (AVar y)" by blast
        from y(1) obtain U' where yU: "(y, U') \<in> vps u" by (auto simp: vars_eq_vps)
        have "lk env x T = Some u" using b UT by (simp add: lk_def)
        with yU have "(y, U') \<in> reach env X"
          using reach_lk[of env x T u] reach_incl[of "vps u" env] reach_mono[of "{(x, T)}" env X] "1.prems"
          by blast
        moreover have "(y, x) \<in> dvar env" by (rule dvarI[OF b y(1)])
        ultimately show ?thesis using "1.IH" y(2) by blast
      qed
    qed
    then show ?thesis
      using env_map_bound[OF e(1,3) b] env_map_bound[OF e'(1,3) b'] by (simp add: env_sol_def)
  qed
qed

lemma tau_rigid: "rigid_code m \<Longrightarrow> tau V' m = tau V m"
  by (auto simp: rigid_code_def)

lemma inst_extend:
  assumes ei: "env_inv ar V env" and ei': "env_inv ar V' env'" and ext: "extends env' env"
    and vt: "vtyped V t"
    and R: "\<And>y. y \<in> reach env (vps t) \<Longrightarrow> lk env (fst y) (snd y) = None \<Longrightarrow>
      lk env' (fst y) (snd y) = None \<and> V' (fst y) = V (fst y)"
  shows "mk_subst (env_sol env' V') (tr t) = mk_subst (env_sol env V) (tr t)"
proof (rule mk_subst_cong)
  note e = env_invD[OF ei] and e' = env_invD[OF ei']
  have X: "\<forall>y\<in>vps t. V (fst y) = snd y" using vt by (simp add: vtyped_def)
  fix n assume "n \<in> FV (tr t)"
  from FV_tr[OF this] show "env_sol env' V' n = env_sol env V n"
  proof
    assume "rigid_code n"
    then show ?thesis using env_map_rigid[OF e(1,3)] env_map_rigid[OF e'(1,3)] by (simp add: env_sol_def)
  next
    assume "\<exists>y\<in>vars t. n = code (AVar y)"
    then obtain y U where y: "(y, U) \<in> vps t" "n = code (AVar y)" by (auto simp: vars_eq_vps)
    then have "(y, U) \<in> reach env (vps t)" using reach_incl by blast
    from env_sol_reach[OF ei ei' ext X R this] y(2) show ?thesis by simp
  qed
qed

lemma isz_extend:
  assumes ei: "env_inv ar V env" and ei': "env_inv ar V' env'" and ext: "extends env' env"
    and vt: "vtyped V t"
    and R: "\<And>y. y \<in> reach env (vps t) \<Longrightarrow> lk env (fst y) (snd y) = None \<Longrightarrow>
      lk env' (fst y) (snd y) = None \<and> V' (fst y) = V (fst y)"
  shows "isz env' V' Bs t T = isz env V Bs t T"
proof -
  let ?s = "mk_subst (env_sol env V) (tr t)"
  have "m \<in> FV ?s \<Longrightarrow> rigid_code m" for m
    using env_solution(2)[OF env_invD(1,2,3)[OF ei]] FV_tr_range[of t] unfolding FV_mk_subst by blast
  then have "\<And>n. n \<in> FV (\<beta>_nf ?s) \<Longrightarrow> tau V' n = tau V n"
    using \<beta>_nf_FV[of ?s] tau_rigid by blast
  with hsize_lsize_cong[of "\<beta>_nf ?s" "tau V'" "tau V"] inst_extend[OF ei ei' ext vt R]
  show ?thesis by (simp add: isz_def)
qed

lemma cinv_sol: "env_inv ar V env \<Longrightarrow> cinv ar V (tau V) (env_sol env V) env []"
  by (simp add: cinv_def esol)

text \<open>The normalization of an argument by \<^const>\<open>copycons\<close> keeps the size of its instance.\<close>

lemma copy_norm_isz:
  assumes ei: "env_inv ar V env" and bok: "binders_ok ar rb" and w: "wf_tm ar rb t"
    and ty: "has_type V (map snd rb) t T" and bl: "below (maxidx env) t"
  obtains u1 u2 where "ok (head_norm env t) u1" "ok (eta_norm env rb u1) u2"
    "wf_tm ar rb u2" "hnf u2" "hlong V (map snd rb) u2 T" "below (maxidx env) u2"
    "vps u2 \<subseteq> reach env (vps t)" "isz env V (map snd rb) u2 T = isz env V (map snd rb) t T"
proof -
  from copy_norm_complete[OF cinv_sol[OF ei] bok w ty bl] obtain u1 u2 where
    c: "ok (head_norm env t) u1" "ok (eta_norm env rb u1) u2"
    "wf_tm ar rb u2" "hnf u2" "hlong V (map snd rb) u2 T" "below (maxidx env) u2"
    "vps u2 \<subseteq> reach env (vps t)" "mk_subst (env_sol env V) (tr u2) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (env_sol env V) (tr t)"
    by blast
  from isz_equiv[OF ei hlong_typed[OF c(5)] ty c(8)] c(1-7) that show thesis by blast
qed

subsection \<open>Extensions of states without a solution\<close>

text \<open>The counterpart of \<^const>\<open>sext\<close> without a solution:\<close>

definition tsext :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "tsext ar V env V' env' dps' D NV \<longleftrightarrow>
    tyinv ar V' env' dps' \<and> agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
    finite NV \<and> (\<forall>y\<in>NV. maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env') \<and>
    (\<forall>X. reach env' X \<subseteq> reach env (X \<union> D) \<union> NV) \<and> vps_dps dps' \<subseteq> reach env D \<union> NV"

lemma tsextD:
  assumes "tsext ar V env V' env' dps' D NV"
  shows "tyinv ar V' env' dps'" "agreeV (maxidx env) V V'" "maxidx env \<le> maxidx env'" "extends env' env"
    "finite NV" "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'"
    "\<And>X. reach env' X \<subseteq> reach env (X \<union> D) \<union> NV" "vps_dps dps' \<subseteq> reach env D \<union> NV"
  using assms by (auto simp: tsext_def)

lemma tsext_refl: "tyinv ar V env dps \<Longrightarrow> vps_dps dps \<subseteq> D \<Longrightarrow> tsext ar V env V env dps D {}"
  using reach_incl[of D env] by (auto simp: tsext_def reach_Un)

lemma tsext_mono:
  assumes s: "tsext ar V env V' env' dps' D NV" and D: "D \<subseteq> D'"
  shows "tsext ar V env V' env' dps' D' NV"
proof -
  have r: "reach env (X \<union> D) \<subseteq> reach env (X \<union> D')" for X using D by (intro reach_subset) blast
  have "reach env D \<subseteq> reach env D'" using D by (rule reach_subset)
  then have "vps_dps dps' \<subseteq> reach env D' \<union> NV" using s by (auto simp: tsext_def)
  moreover have "reach env' X \<subseteq> reach env (X \<union> D') \<union> NV" for X using s r[of X] by (auto simp: tsext_def)
  ultimately show ?thesis using s by (simp add: tsext_def)
qed

lemma tsext_trans:
  assumes s1: "tsext ar V env V1 env1 dps1 D1 NV1" and s2: "tsext ar V1 env1 V2 env2 dps2 D2 NV2"
    and fr: "fresh_env env" and D: "D2 \<subseteq> reach env D1 \<union> NV1"
  shows "tsext ar V env V2 env2 dps2 D1 (NV1 \<union> NV2)"
proof -
  note c1 = tsextD[OF s1] and c2 = tsextD[OF s2]
  have nv1: "reach env NV1 = NV1" using reach_new[OF fr] c1(6) by blast
  have rD2: "reach env D2 \<subseteq> reach env D1 \<union> NV1"
    using reach_mono[of D2 env "D1 \<union> NV1"] D reach_incl[of "D1 \<union> NV1" env] nv1
    by (auto simp: reach_Un)
  have r: "reach env2 X \<subseteq> reach env (X \<union> D1) \<union> (NV1 \<union> NV2)" for X
  proof -
    have "reach env2 X \<subseteq> reach env1 (X \<union> D2) \<union> NV2" by (rule c2(7))
    also have "\<dots> \<subseteq> reach env (X \<union> D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(7)[of "X \<union> D2"] by blast
    also have "\<dots> \<subseteq> reach env (X \<union> D1) \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: reach_Un)
    finally show ?thesis .
  qed
  have v: "vps_dps dps2 \<subseteq> reach env D1 \<union> (NV1 \<union> NV2)"
  proof -
    have "vps_dps dps2 \<subseteq> reach env1 D2 \<union> NV2" by (rule c2(8))
    also have "\<dots> \<subseteq> reach env (D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(7)[of D2] by blast
    also have "\<dots> \<subseteq> reach env D1 \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: reach_Un)
    finally show ?thesis .
  qed
  show ?thesis unfolding tsext_def
  proof (intro conjI c2(1) r v allI ballI)
    show "agreeV (maxidx env) V V2" using agreeV_trans[OF c1(2) c2(2) c1(3)] .
    show "maxidx env \<le> maxidx env2" using c1(3) c2(3) by simp
    show "extends env2 env" using c2(4) c1(4) by (rule extends_trans)
    show "finite (NV1 \<union> NV2)" using c1(5) c2(5) by simp
    show "maxidx env < snd (fst y)" if "y \<in> NV1 \<union> NV2" for y
      using that c1(3) c1(6)[of y] c2(6)[of y] by auto
    show "snd (fst y) \<le> maxidx env2" if "y \<in> NV1 \<union> NV2" for y
      using that c2(3) c1(6)[of y] c2(6)[of y] by auto
  qed
qed


subsection \<open>New variables without a solution\<close>

text \<open>A closed term of every type, to extend the canonical solution to new variables:\<close>

definition cterm :: "ptyp \<Rightarrow> dB" where
  "cterm T = Abs_m (length (arg_types T)) (dB.Var (code (AFree STR '''' (res_type T))))"

lemma cterm_props: "no_loose_bound (cterm T) 0 \<and> (\<forall>e. (e, tau V) \<turnstile> cterm T : trty T)"
proof (intro conjI allI)
  show "no_loose_bound (cterm T) 0" by (simp add: cterm_def loose_bound_Abs_m)
  fix e
  let ?As = "arg_types T" and ?R = "res_type T"
  have "(env_ext e (map trty ?As), tau V) \<turnstile> dB.Var (code (AFree STR '''' ?R)) : trty ?R"
    by (rule typing.Var) simp
  from typing_Abs_m[OF this] show "(e, tau V) \<turnstile> cterm T : trty T"
    using trty_foldr[of ?As ?R] arg_res_type[of T] by (simp add: cterm_def)
qed

lemma make_args_term:
  assumes ei: "env_inv ar V env" and ma: "make_args a Ts env Us = (env1, args)"
  obtains V1 xs where "env_inv ar V1 env1" "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env1"
    "extends env1 env" "tenv env1 = tenv env" "length xs = length Us" "distinct xs"
    "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env1"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
proof -
  let ?ws = "map (\<lambda>U. cterm (foldr fun_type Ts U)) Us"
  have ws: "no_loose_bound (?ws ! i) 0 \<and> (\<forall>e. (e, tau V) \<turnstile> ?ws ! i : trty (foldr fun_type Ts (Us ! i)))"
    if "i < length Us" for i
    using cterm_props that by simp
  obtain V1 \<sigma>1 xs where
    me: "cinv ar V1 (tau V) \<sigma>1 env1 []" "agree (maxidx env) (env_sol env V) \<sigma>1"
    "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env1"
    "extends env1 env" "length xs = length Us" "distinct xs"
    "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env1"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. \<sigma>1 (code (AVar (xs ! i))) = ?ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    by (rule make_args_extend[OF cinv_sol[OF ei] ma _ ws]) simp_all
  from that[OF cinvD(1)[OF me(1)] me(3-5) make_args_props(1)[OF ma] me(6-9)] me(10) show thesis by blast
qed

lemma genvar_term:
  assumes ei: "env_inv ar V env" and G: "genvar a env T = (env1, G)"
  defines "V1 \<equiv> V((a, maxidx env + 1) := T)"
  shows "env_inv ar V1 env1" "agreeV (maxidx env) V V1" "maxidx env1 = maxidx env + 1"
    "G = Var (a, maxidx env + 1) T" "extends env1 env" "tenv env1 = tenv env" "V1 (a, maxidx env + 1) = T"
proof -
  note ge = genvar_extend[OF cinv_sol[OF ei] G conjunct1[OF cterm_props] conjunct2[OF cterm_props, rule_format],
      folded V1_def]
  show "env_inv ar V1 env1" using cinvD(1)[OF ge(1)] .
  show "agreeV (maxidx env) V V1" "maxidx env1 = maxidx env + 1" "G = Var (a, maxidx env + 1) T"
    "extends env1 env" "V1 (a, maxidx env + 1) = T"
    by (rule ge)+
  show "tenv env1 = tenv env" by (rule genvar_simps(1)[OF G])
qed

end
