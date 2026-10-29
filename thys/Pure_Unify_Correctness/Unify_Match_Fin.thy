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

subsection \<open>Variables reachable from terms\<close>

lemma reach_free:
  assumes vg: "vgood Fd Ft env" and X: "\<forall>y\<in>X. fst y \<notin> Ft" and y: "y \<in> reach env X"
  shows "fst y \<notin> Ft"
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
    from vgoodD[OF vg lkD[OF lk]] have "vars u \<inter> Ft = {}" by simp
    with yu show ?case by (auto simp: vars_eq_vps)
  qed
qed

lemma reach_below:
  assumes fr: "fresh_env env" and X: "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" and y: "y \<in> reach env X"
  shows "snd (fst y) \<le> maxidx env"
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
    from fresh_envD[OF fr lkD[OF lk]] have "below (maxidx env) u" by simp
    with yu show ?case by (auto simp: below_def vars_eq_vps)
  qed
qed

lemma lk_extends_None: "extends env' env \<Longrightarrow> lk env' x T = None \<Longrightarrow> lk env x T = None"
  by (cases "vt_lookup (tenv env) x") (auto simp: lk_def dest: extendsD split: if_splits)


subsection \<open>The setting of a step of matching\<close>

text \<open>
  The variables up to index \<open>m0\<close> are those of the original problem; the old ones that it can
  reach are among the finite set \<open>S0\<close>. The new variables are dead (\<open>Fd\<close>) if one of the
  arguments of the flexible side is not a bound variable, and occur at heads only (\<open>Ft\<close>)
  otherwise.
\<close>

locale mfin =
  fixes ar :: "name \<Rightarrow> nat" and cfg :: cfg and vname :: name and m0 :: integer
    and S0 :: "(indexname \<times> ptyp) set" and Fd Ft :: "indexname set"
  assumes S0: "finite S0" "\<And>y. y \<in> S0 \<Longrightarrow> snd (fst y) \<le> m0"
    and regime: "Fd = {x. m0 < snd x} \<and> Ft = {} \<or> Fd = {} \<and> Ft = {x. m0 < snd x}"
begin

definition mu1 :: "env \<Rightarrow> nat" where
  "mu1 env = card {y\<in>S0. lk env (fst y) (snd y) = None}"

definition oldin :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "oldin env X \<longleftrightarrow> (\<forall>y\<in>reach env X. snd (fst y) \<le> m0 \<longrightarrow> y \<in> S0)"

lemma mu1_mono: "extends env' env \<Longrightarrow> mu1 env' \<le> mu1 env"
  unfolding mu1_def using S0(1) by (intro card_mono) (auto dest: lk_extends_None)

lemma mu1_eq:
  assumes "extends env' env" "mu1 env' = mu1 env" "y \<in> S0" "lk env (fst y) (snd y) = None"
  shows "lk env' (fst y) (snd y) = None"
proof -
  let ?A = "{y\<in>S0. lk env' (fst y) (snd y) = None}" and ?B = "{y\<in>S0. lk env (fst y) (snd y) = None}"
  have "?A \<subseteq> ?B" using assms(1) by (auto dest: lk_extends_None)
  moreover have "finite ?B" using S0(1) by simp
  moreover have "card ?A = card ?B" using assms(2) by (simp add: mu1_def)
  ultimately have "?A = ?B" by (intro card_subset_eq)
  with assms(3,4) show ?thesis by blast
qed

lemma oldin_mono: "oldin env Y \<Longrightarrow> X \<subseteq> reach env Y \<Longrightarrow> oldin env X"
  using reach_mono[of X env Y] by (auto simp: oldin_def)

lemma oldin_tsext:
  assumes "tsext ar V env V' env' dps' D NV" "oldin env (X \<union> D)" "m0 \<le> maxidx env"
  shows "oldin env' X"
  unfolding oldin_def
proof (intro ballI impI)
  fix y assume y: "y \<in> reach env' X" "snd (fst y) \<le> m0"
  from tsextD(7)[OF assms(1)] y(1) have "y \<in> reach env (X \<union> D) \<or> y \<in> NV" by blast
  then show "y \<in> S0"
  proof
    assume "y \<in> NV"
    with tsextD(6)[OF assms(1), of y] y(2) assms(3) show ?thesis by simp
  qed (use assms(2) y(2) in \<open>auto simp: oldin_def\<close>)
qed

text \<open>The shape of the terms of the original problem:\<close>

definition sh :: "pterm \<Rightarrow> bool" where
  "sh t \<longleftrightarrow> dead Fd t \<and> vars t \<inter> Ft = {}"

text \<open>The instance of such a term does not change as long as no old variable is assigned.\<close>

lemma isz_stable:
  assumes ei: "env_inv ar V env" and vg: "vgood Fd Ft env" and s: "tsext ar V env V' env' dps' D NV"
    and vg': "vgood Fd Ft env'" and o: "oldin env (vps a)" and ty: "has_type V Bs a A"
    and b: "below (maxidx env) a" and sa: "sh a" and mu: "mu1 env' = mu1 env"
  shows "isz env' V' Bs a A = isz env V Bs a A"
proof (rule isz_extend[OF ei tyinvD(1)[OF tsextD(1)[OF s]] tsextD(4)[OF s] has_type_vtyped[OF ty]])
  note e = env_invD[OF ei]
  fix y assume y: "y \<in> reach env (vps a)" and n: "lk env (fst y) (snd y) = None"
  have yb: "snd (fst y) \<le> maxidx env"
    using reach_below[OF e(4) _ y] b by (auto simp: below_def vars_eq_vps)
  show "lk env' (fst y) (snd y) = None \<and> V' (fst y) = V (fst y)"
  proof
    show "V' (fst y) = V (fst y)" by (rule agreeV_D[OF tsextD(2)[OF s] yb])
    show "lk env' (fst y) (snd y) = None"
    proof (cases "snd (fst y) \<le> m0")
      case True
      with o y have "y \<in> S0" by (auto simp: oldin_def)
      from mu1_eq[OF tsextD(4)[OF s] mu this n] show ?thesis .
    next
      case False
      with regime have "fst y \<in> Fd \<or> fst y \<in> Ft" by auto
      moreover have "fst y \<notin> Ft" using reach_free[OF vg _ y] sa by (auto simp: sh_def vars_eq_vps)
      ultimately have "fst y \<in> Fd" by simp
      then have "vt_lookup (tenv env') (fst y) = None"
        using vg' by (cases "vt_lookup (tenv env') (fst y)") (auto dest: vgoodD)
      then show ?thesis by (simp add: lk_def)
    qed
  qed
qed

end

lemma tsext_mono':
  assumes s: "tsext ar V env V' env' dps' D NV" and D: "D \<subseteq> reach env D'"
  shows "tsext ar V env V' env' dps' D' NV"
proof -
  have r: "reach env (X \<union> D) \<subseteq> reach env (X \<union> D')" for X
    using D reach_mono[of "X \<union> D" env "X \<union> D'"] reach_incl[of "X \<union> D'" env] reach_subset[of D' "X \<union> D'" env]
    by blast
  have "reach env D \<subseteq> reach env D'" using D by (rule reach_mono)
  then have "vps_dps dps' \<subseteq> reach env D' \<union> NV" using s by (auto simp: tsext_def)
  moreover have "reach env' X \<subseteq> reach env (X \<union> D') \<union> NV" for X using s r[of X] by (auto simp: tsext_def)
  ultimately show ?thesis using s by (simp add: tsext_def)
qed

context mfin
begin

subsection \<open>Copies\<close>

text \<open>
  The arguments \<open>targs\<close> of the flexible side satisfy the condition of the kind of the new
  variables:
\<close>

definition tok :: "pterm list \<Rightarrow> bool" where
  "tok targs \<longleftrightarrow> (Fd \<noteq> {} \<longrightarrow> (\<exists>t\<in>set targs. \<not> is_Bound t)) \<and> (Ft \<noteq> {} \<longrightarrow> (\<forall>t\<in>set targs. is_Bound t))"

text \<open>The context of a copy, the term to copy, and the results:\<close>

definition cpre :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "cpre V env dps rb targs Ts \<longleftrightarrow> tyinv ar V env dps \<and> binders_ok ar rb \<and>
    (\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t \<and> sh t) \<and>
    list_all2 (has_type V (map snd rb)) targs Ts \<and> vgood Fd Ft env \<and> (\<forall>dp\<in>set dps. pgood Fd Ft dp) \<and>
    tok targs \<and> m0 \<le> maxidx env"

definition upre :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "upre V env rb u U \<longleftrightarrow> wf_tm ar rb u \<and> has_type V (map snd rb) u U \<and> below (maxidx env) u \<and> sh u"

definition cres :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "cres V env D V' env' dps' NV \<longleftrightarrow>
    tsext ar V env V' env' dps' D NV \<and> vgood Fd Ft env' \<and> (\<forall>dp\<in>set dps'. pgood Fd Ft dp)"

definition cpy :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "cpy V' env' NV Ts u' U \<longleftrightarrow>
    has_type V' (rev Ts) u' U \<and> wf_cp ar (length Ts) u' \<and> below (maxidx env') u' \<and> vps u' \<subseteq> NV"

lemma cres_trans:
  assumes "cres V env D V1 env1 dps1 NV1" "cres V1 env1 D1 V2 env2 dps2 NV2" "fresh_env env"
    "D1 \<subseteq> reach env D \<union> NV1"
  shows "cres V env D V2 env2 dps2 (NV1 \<union> NV2)"
  using assms tsext_trans[of ar V env V1 env1 dps1 D NV1 V2 env2 dps2 D1 NV2] by (simp add: cres_def)

lemma cres_mono: "cres V env D V' env' dps' NV \<Longrightarrow> D \<subseteq> reach env D' \<Longrightarrow> cres V env D' V' env' dps' NV"
  by (auto simp: cres_def intro: tsext_mono')

lemma cpy_mono:
  assumes "cpy V1 env1 NV1 Ts u U" "agreeV (maxidx env1) V1 V2" "maxidx env1 \<le> maxidx env2" "NV1 \<subseteq> NV"
  shows "cpy V2 env2 NV Ts u U"
  using assms has_type_agreeV[of V1 "rev Ts" u U "maxidx env1" V2] below_mono[of "maxidx env1" u "maxidx env2"]
  by (auto simp: cpy_def)

lemma cpreD:
  assumes "cpre V env dps rb targs Ts"
  shows "tyinv ar V env dps" "binders_ok ar rb" "\<And>t. t \<in> set targs \<Longrightarrow> wf_tm ar rb t \<and> below (maxidx env) t \<and> sh t"
    "list_all2 (has_type V (map snd rb)) targs Ts" "vgood Fd Ft env" "\<And>dp. dp \<in> set dps \<Longrightarrow> pgood Fd Ft dp"
    "tok targs" "m0 \<le> maxidx env"
  using assms by (auto simp: cpre_def)

text \<open>The new variables are those beyond \<open>m0\<close>:\<close>

lemma fresh_iff: "x \<in> Fd \<union> Ft \<longleftrightarrow> m0 < snd x"
  using regime by auto

lemma sh_incr: "sh t \<Longrightarrow> sh (incr_boundvars 1 t)"
  by (simp add: sh_def incr_boundvars_def vars_incr_bv)

lemma tok_incr: "tok targs \<Longrightarrow> tok (map (incr_boundvars 1) targs @ [Bound 0])"
  by (auto simp: tok_def incr_boundvars_def)

end

lemma make_projs_idx:
  "okW (make_projs u targs0 Ts targs) ps \<Longrightarrow> length Ts = length targs \<and>
    (\<forall>(bv, T, targ)\<in>set ps. \<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length targs \<and>
      targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T = Ts ! (length targs - 1 - nat_of_integer j))"
proof (induction u targs0 Ts targs arbitrary: ps rule: make_projs.induct)
  case (1 u targs0 T Ts targ targs)
  from "1.prems" obtain ps' where ps': "okW (make_projs u targs0 Ts targs) ps'"
    and ps: "ps = (Bound (ilength Ts), T, targ) # ps'" by auto
  note IH = "1.IH"[OF ps']
  have hd: "\<exists>j. Bound (ilength Ts) = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length (targ # targs) \<and>
      targ = (targ # targs) ! (length (targ # targs) - 1 - nat_of_integer j) \<and>
      T = (T # Ts) ! (length (targ # targs) - 1 - nat_of_integer j)"
    using IH by (intro exI[of _ "ilength Ts"]) simp
  have tl: "\<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length (targ # targs) \<and>
      targ' = (targ # targs) ! (length (targ # targs) - 1 - nat_of_integer j) \<and>
      T' = (T # Ts) ! (length (targ # targs) - 1 - nat_of_integer j)"
    if "(bv, T', targ') \<in> set ps'" for bv T' targ'
  proof -
    from IH that obtain j where j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length targs"
      "targ' = targs ! (length targs - 1 - nat_of_integer j)" "T' = Ts ! (length targs - 1 - nat_of_integer j)"
      by fastforce
    moreover have "(targ # targs) ! (length (targ # targs) - 1 - nat_of_integer j) =
        targs ! (length targs - 1 - nat_of_integer j)"
      "(T # Ts) ! (length (targ # targs) - 1 - nat_of_integer j) = Ts ! (length targs - 1 - nat_of_integer j)"
      using j(3) by (simp_all add: nth_Cons' Suc_diff_Suc)
    ultimately show ?thesis by (intro exI[of _ j]) simp
  qed
  from IH hd tl ps show ?case by fastforce
qed auto

lemma rrs_list_comb: "rrs F (list_comb h ts) \<longleftrightarrow> rrs F h \<and> (\<forall>t\<in>set ts. gs F t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma cuok_mono_ok: "cuok m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> cuok m Q"
  by (auto simp: cuok_def)

context mfin
begin

text \<open>A projection: the simplification of the projection pair yields a copy.\<close>

lemma proj_res:
  assumes cp: "cpre V env dps rb targs Ts" and up: "upre V env rb u U"
    and hu: "is_rigid (head_of u)" and nA: "\<not> is_Abs u"
    and j: "0 \<le> j" "nat_of_integer j < length targs"
    and T: "T = Ts ! (length targs - 1 - nat_of_integer j)"
    and targ: "targ = targs ! (length targs - 1 - nat_of_integer j)"
    and rT: "res_type T = U"
    and ma: "make_args vname Ts env (arg_types T) = (env', args)"
  shows "cuok (SIMPL (cfg_alg cfg) env' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
    (\<lambda>(env2, fr, ff). \<exists>V' NV. cres V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) V' env2 (fr @ ff) NV \<and>
      cpy V' env2 NV Ts (list_comb (Bound j) args) U)"
proof -
  note c = cpreD[OF cp]
  have ei: "env_inv ar V env" by (rule tyinvD(1)[OF c(1)])
  note e = env_invD[OF ei]
  have wu: "wf_tm ar rb u" and tyu: "has_type V (map snd rb) u U" and bu: "below (maxidx env) u" and shu: "sh u"
    using up by (simp_all add: upre_def)
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF c(4)] by simp
  define k where "k = length targs - 1 - nat_of_integer j"
  have k: "k < length targs" using j by (simp add: k_def)
  have tyt: "has_type V (map snd rb) targ T" using c(4) k by (simp add: list_all2_conv_all_nth T targ k_def)
  have wtg: "wf_tm ar rb targ" "below (maxidx env) targ" "sh targ"
    using c(3)[of targ] k by (simp_all add: targ k_def)
  define Us where "Us = arg_types T"
  have T_eq: "T = foldr fun_type Us U" using arg_res_type[of T] rT by (simp add: Us_def)
  have e0: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF e(2)])
  have gTs: "ground ar A" if "A \<in> set Ts" for A
  proof -
    from that obtain i where i: "i < length Ts" "A = Ts ! i" by (auto simp: in_set_conv_nth)
    with c(4) have "has_type V (map snd rb) (targs ! i) A" by (simp add: list_all2_conv_all_nth)
    moreover have "wf_tm ar rb (targs ! i)" using c(3) i lTs by simp
    ultimately show ?thesis using ground_has_type[OF e0 c(2)] by blast
  qed
  have gT: "ground ar T" using gTs k lTs by (simp add: T k_def[symmetric])
  have gUs: "\<forall>A\<in>set Us. ground ar A"
    using strip_type_ground(1)[OF e0 gT, of Us "res_type T"] by (simp add: strip_type_arg_res[OF e0] Us_def)
  obtain V1 xs where me: "env_inv ar V1 env'" "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env'"
    "extends env' env" "tenv env' = tenv env" "length xs = length Us" "distinct xs"
    "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env'"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    by (rule make_args_term[OF ei ma[folded Us_def]])
  have la: "length args = length Us" using me(6,9) by simp
  have ai: "args ! i = combound (Var (xs ! i) (foldr fun_type Ts (Us ! i))) 0 (length Ts)"
    if "i < length Us" for i using me(6,9) that by simp
  have hai: "head_of (args ! i) = Var (xs ! i) (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
    using ai[OF that] by (simp add: head_of_combound)
  define Ls where "Ls = map (\<lambda>arg. list_comb (head_of arg) targs) args"
  define dp where "dp = (rb, list_comb targ Ls, u)"
  have lLs: "length Ls = length Us" using la by (simp add: Ls_def)
  have Lsi: "Ls ! i = list_comb (Var (xs ! i) (foldr fun_type Ts (Us ! i))) targs" if "i < length Us" for i
    using hai[OF that] la that by (simp add: Ls_def)
  have tg1: "list_all2 (has_type V1 (map snd rb)) targs Ts"
    using list_all2_has_type_agreeV[OF c(4) _ me(2)] c(3) by blast
  have tyt1: "has_type V1 (map snd rb) targ T" using has_type_agreeV[OF tyt wtg(2) me(2)] .
  have tyGi: "has_type V1 Bs (Var (xs ! i) (foldr fun_type Ts (Us ! i))) (foldr fun_type Ts (Us ! i))"
    if "i < length Us" for i Bs
    using me(10) that by (simp add: has_type.Var)
  have tyli: "list_all2 (has_type V1 (map snd rb)) Ls Us"
    unfolding list_all2_conv_all_nth using lLs Lsi tyGi tg1 by (auto simp: has_type_list_comb)
  have tylhs: "has_type V1 (map snd rb) (list_comb targ Ls) U"
    using tyt1 tyli T_eq by (auto simp: has_type_list_comb)
  have tyu1: "has_type V1 (map snd rb) u U" using has_type_agreeV[OF tyu bu me(2)] .
  have gGi: "ground ar (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
    using ground_foldr_fun_type[of Ts ar "Us ! i"] gTs gUs that by auto
  have bGi: "maxidx env < snd (xs ! i)" "snd (xs ! i) \<le> maxidx env'" if "i < length Us" for i
    using me(8) me(6) that by (auto dest: nth_mem)
  have wLs: "wf_tm ar rb t \<and> below (maxidx env') t" if "t \<in> set Ls" for t
  proof -
    from that obtain i where i: "i < length Us" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
    then show ?thesis using Lsi[OF i(1)] gGi[OF i(1)] bGi(2)[OF i(1)] c(3) below_mono[OF _ me(3)]
      by (auto simp: wf_tm_def proper_list_comb typs_ok_list_comb tr_list_comb no_loose_bound_list_app
          below_list_comb)
  qed
  have ti: "tyinv ar V1 env' (dp # dps)"
  proof -
    have "tyinv ar V1 env' dps"
      by (rule tyinv_transfer[OF me(1) _ me(2,3)]) (use tyinvD(2)[OF c(1)] in blast)
    moreover have "wf_dp ar dp" using c(2) wtg wu wLs by (simp add: dp_def wf_tm_list_comb)
    moreover have "dp_typed V1 dp" using tylhs tyu1 by (auto simp: dp_def dp_typed_def)
    moreover have "dp_below (maxidx env') dp"
      using wtg(2) bu wLs below_mono[OF _ me(3)] by (auto simp: dp_def dp_below_def below_list_comb)
    ultimately show ?thesis by (simp add: tyinv_def)
  qed
  text \<open>The shape of the projection pair:\<close>
  have pg: "pgood Fd Ft dp"
  proof -
    have dL: "dead Fd L" if "L \<in> set Ls" for L
    proof -
      from that obtain i where i: "i < length Us" "L = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      have "xs ! i \<in> Fd \<Longrightarrow> \<exists>t\<in>set targs. \<not> is_Bound t" using c(7) by (auto simp: tok_def)
      with Lsi[OF i(1)] i(2) c(3) show ?thesis by (auto simp: dd_list_comb sh_def)
    qed
    have d: "dead Fd (list_comb targ Ls)" "dead Fd u"
      using dL wtg(3) shu by (auto simp: dd_list_comb sh_def intro: dd_True)
    have "gs Ft (list_comb targ Ls) \<and> gs Ft u \<or> rrs Ft (list_comb targ Ls) \<and> rrs Ft u"
    proof (cases "Ft = {}")
      case True
      then show ?thesis by (simp add: gs_free)
    next
      case False
      then have "\<forall>t\<in>set targs. is_Bound t" using c(7) by (simp add: tok_def)
      then have "is_Bound targ" using k by (simp add: targ k_def)
      then have r1: "rrs Ft targ" by (cases targ) auto
      have gL: "gs Ft L" if "L \<in> set Ls" for L
      proof -
        from that obtain i where i: "i < length Us" "L = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
        have "hok Ft L" using Lsi[OF i(1)] i(2) c(3) by (auto simp: hok_list_comb sh_def)
        then show ?thesis by (rule hok_gs)
      qed
      have "u = list_comb (head_of u) (snd (strip_comb u))" by (rule head_of_list_comb)
      moreover have "rrs Ft (head_of u)" using hu by (auto simp: is_rigid_def)
      moreover have "\<forall>t\<in>set (snd (strip_comb u)). gs Ft t"
      proof
        fix t assume "t \<in> set (snd (strip_comb u))"
        then have "vars t \<subseteq> vars u" using vars_list_comb[of "head_of u" "snd (strip_comb u)"]
          head_of_list_comb[of u] by auto
        with shu show "gs Ft t" by (auto simp: sh_def intro: gs_free)
      qed
      ultimately have "rrs Ft u" by (metis rrs_list_comb)
      with r1 gL show ?thesis by (simp add: rrs_list_comb)
    qed
    with d show ?thesis by (simp add: pgood_def dp_def)
  qed
  have vg1: "vgood Fd Ft env'" using c(5) by (simp add: vgood_tenv[OF me(5)])
  have pgs: "\<forall>dp\<in>set (dp # dps). pgood Fd Ft dp" using pg c(6) by simp
  define NV where "NV = set (map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us)"
  define D where "D = vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
  have "map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us = map (\<lambda>i. (xs ! i, foldr fun_type Ts (Us ! i))) [0..<length Us]"
    using me(6) by (intro nth_equalityI) auto
  then have NVi: "y \<in> NV \<longleftrightarrow> (\<exists>i<length Us. y = (xs ! i, foldr fun_type Ts (Us ! i)))" for y
    by (auto simp: NV_def)
  have NVb: "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'" if "y \<in> NV" for y
    using that NVi bGi by auto
  have vai: "vps (args ! i) = {(xs ! i, foldr fun_type Ts (Us ! i))}" if "i < length Us" for i
    using ai[OF that] by simp
  have vargs: "\<Union> (vps ` set args) = NV"
  proof
    show "\<Union> (vps ` set args) \<subseteq> NV" using vai la NVi by (force simp: in_set_conv_nth)
    show "NV \<subseteq> \<Union> (vps ` set args)"
    proof
      fix y assume "y \<in> NV"
      then obtain i where i: "i < length Us" "y = (xs ! i, foldr fun_type Ts (Us ! i))" using NVi by blast
      then have "y \<in> vps (args ! i)" using vai by simp
      with i(1) la show "y \<in> \<Union> (vps ` set args)" by (auto dest: nth_mem[of i args])
    qed
  qed
  have vLs: "\<Union> (vps ` set Ls) \<subseteq> NV \<union> \<Union> (vps ` set targs)"
  proof
    fix y assume "y \<in> \<Union> (vps ` set Ls)"
    then obtain i where i: "i < length Us" "y \<in> vps (Ls ! i)" using lLs by (auto simp: in_set_conv_nth)
    then show "y \<in> NV \<union> \<Union> (vps ` set targs)" using Lsi[OF i(1)] NVi by (auto simp: vps_list_comb)
  qed
  have tgD: "vps targ \<subseteq> D" using k by (auto simp: D_def targ k_def[symmetric] dest: nth_mem)
  have vdp: "vps_dps (dp # dps) \<subseteq> D \<union> NV"
    using vLs tgD by (auto simp: dp_def vps_dp_def vps_list_comb D_def)
  have rr: "reach env' = reach env" by (rule reach_tenv[OF me(5)])
  have nvr: "reach env NV = NV" using reach_new[OF e(4)] NVb by blast
  have rDNV: "reach env (X \<union> D \<union> NV) = reach env (X \<union> D) \<union> NV" for X using nvr by (simp add: reach_Un)
  have cpy: "cpy V1 env2 NV Ts (list_comb (Bound j) args) U" if "maxidx env2 = maxidx env'" for env2
  proof -
    have tyBj: "has_type V1 (rev Ts) (Bound j) (foldr fun_type Us U)"
      using j lTs T_eq T by (simp add: has_type_Bound_iff rev_nth)
    have "has_type V1 (rev Ts) (args ! i) (Us ! i)" if "i < length Us" for i
      using has_type_combound0[of V1 Ts "[]" "Var (xs ! i) (foldr fun_type Ts (Us ! i))" "Us ! i"]
        tyGi[OF that] ai[OF that] by simp
    then have tyai: "list_all2 (has_type V1 (rev Ts)) args Us" using la by (simp add: list_all2_conv_all_nth)
    have tyu': "has_type V1 (rev Ts) (list_comb (Bound j) args) U"
      using tyBj tyai by (auto simp: has_type_list_comb)
    have vu': "vps (list_comb (Bound j) args) = NV" using vargs by (simp add: vps_list_comb)
    have "typs_ok ar a" if "a \<in> set args" for a
      using that la ai gGi by (auto simp: in_set_conv_nth typs_ok_combound)
    then have "wf_cp ar (length Ts) (list_comb (Bound j) args)"
      unfolding wf_cp_def using has_type_proper[OF tyu'] has_type_closed[OF tyu'] by (auto simp: typs_ok_list_comb)
    moreover have "below (maxidx env2) (list_comb (Bound j) args)"
      using vu' NVb that by (auto simp: below_vps_iff)
    ultimately show ?thesis using tyu' vu' by (simp add: cpy_def)
  qed
  have "cuok (SIMPL (cfg_alg cfg) env' (dp # dps)) (\<lambda>(env2, f1, f2).
      \<exists>V' NV. cres V env D V' env2 (f1 @ f2) NV \<and> cpy V' env2 NV Ts (list_comb (Bound j) args) U)"
  proof (rule cuok_mono_ok[OF SIMPL_term[OF ti, of "cfg_alg cfg"]])
    fix st assume ok: "okW (SIMPL (cfg_alg cfg) env' (dp # dps)) st" and sr: "tsimpl_res ar V1 (dp # dps) env' st"
    obtain env2 a b where st: "st = (env2, a, b)" by (cases st)
    from sr st have sr': "tyinv ar V1 env2 (a @ b)" "tstep V1 (vps_dps (dp # dps)) env' env2"
      "vps_dps (a @ b) \<subseteq> reach env' (vps_dps (dp # dps))"
      by (simp_all add: tsimpl_res_def)
    note ts = tstepD[OF sr'(2)]
    from SIMPL_good'[OF ok[unfolded st] vg1 pgs] have sg: "vgood Fd Ft env2" "\<forall>dp\<in>set (a @ b). pgood Fd Ft dp"
      by (auto simp: sgood_def)
    have tx: "tsext ar V env V1 env2 (a @ b) D NV"
      unfolding tsext_def
    proof (intro conjI allI ballI sr'(1) me(2))
      show "maxidx env \<le> maxidx env2" using me(3) ts(2) by simp
      show "extends env2 env" using ts(1) me(4) by (rule extends_trans)
      show "finite NV" by (simp add: NV_def)
      show "maxidx env < snd (fst y)" if "y \<in> NV" for y using NVb that by blast
      show "snd (fst y) \<le> maxidx env2" if "y \<in> NV" for y using NVb that ts(2) by simp
      show "reach env2 X \<subseteq> reach env (X \<union> D) \<union> NV" for X
      proof -
        have "reach env2 X \<subseteq> reach env (X \<union> vps_dps (dp # dps))" using ts(3)[of X] rr by simp
        also have "\<dots> \<subseteq> reach env (X \<union> D \<union> NV)" using vdp by (intro reach_subset) blast
        finally show ?thesis using rDNV by simp
      qed
      show "vps_dps (a @ b) \<subseteq> reach env D \<union> NV"
      proof -
        have "vps_dps (a @ b) \<subseteq> reach env (vps_dps (dp # dps))" using sr'(3) rr by simp
        also have "\<dots> \<subseteq> reach env ({} \<union> D \<union> NV)" using vdp by (intro reach_subset) blast
        finally show ?thesis using rDNV[of "{}"] by simp
      qed
    qed
    have "cres V env D V1 env2 (a @ b) NV" using tx sg by (simp add: cres_def)
    with cpy[OF ts(2)] st show "case st of (env2, f1, f2) \<Rightarrow>
        \<exists>V' NV. cres V env D V' env2 (f1 @ f2) NV \<and> cpy V' env2 NV Ts (list_comb (Bound j) args) U"
      by auto
  qed
  then show ?thesis by (simp add: D_def dp_def Ls_def)
qed

end

context mfin
begin

text \<open>The elements of the sequences of copies of a term and of argument lists:\<close>

definition EC :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> elem \<Rightarrow> bool" where
  "EC V env D Ts U x \<longleftrightarrow>
    (\<exists>u' env' dps' V' NV. x = El_C u' env' dps' \<and> cres V env D V' env' dps' NV \<and> cpy V' env' NV Ts u' U)"

definition ED :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> ptyp list \<Rightarrow> ptyp list \<Rightarrow> elem \<Rightarrow> bool" where
  "ED V env D Ts As x \<longleftrightarrow>
    (\<exists>us env' dps' V' NV. x = El_D us env' dps' \<and> cres V env D V' env' dps' NV \<and>
      list_all2 (\<lambda>u' A. cpy V' env' NV Ts u' A) us As)"

text \<open>The projections of \<^const>\<open>matchfun\<close>, followed by the imitation:\<close>

lemma matchfun_fin:
  assumes cp: "cpre V env dps rb targs Ts" and up: "upre V env rb u U"
    and hu: "is_rigid (head_of u)" and nA: "\<not> is_Abs u" and gU: "ground ar U"
    and projs: "\<forall>(bv, T, targ)\<in>set projs. ground ar T \<and> (\<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
      nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and>
      T = Ts ! (length targs - 1 - nat_of_integer j))"
    and imit: "fin cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) (EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U)"
  shows "\<exists>sq. okW (matchfun cfg vname rb targs u env dps uhead uargs U Ts projs) sq \<and>
    fin cfg sq (EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U)"
  using projs
proof (induction projs)
  case Nil
  with imit show ?case by simp
next
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  from Cons.prems p obtain j where gT: "ground ar T" and bv: "bv = Bound j" and j: "0 \<le> j"
    "nat_of_integer j < length targs" and targ: "targ = targs ! (length targs - 1 - nat_of_integer j)"
    and T: "T = Ts ! (length targs - 1 - nat_of_integer j)"
    by auto
  from Cons.IH Cons.prems obtain tail where tl: "okW (matchfun cfg vname rb targs u env dps uhead uargs U Ts projs) tail"
    and ftl: "fin cfg tail (EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U)"
    by auto
  have e: "vt_is_empty (tyenv env)"
    using wf_envD(1)[OF env_invD(2)[OF tyinvD(1)[OF cpreD(1)[OF cp]]]] .
  have gb: "ground ar (res_type T)"
    using strip_type_ground(2)[OF e gT, of "arg_types T" "res_type T"] by (simp add: strip_type_arg_res[OF e])
  let ?r = "if U = res_type T then S_Proj vname env Ts (arg_types T) targs rb u dps bv targ tail else tail"
  have pe: "okW (projenv cfg vname rb targs u env dps U Ts bv (arg_types T, res_type T) targ tail) ?r"
    by (rule projenv_result[OF gU gb])
  have mf: "okW (matchfun cfg vname rb targs u env dps uhead uargs U Ts (p # projs)) ?r"
    using tl pe by (auto simp: p strip_type_arg_res[OF e])
  have "fin cfg ?r (EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U)"
  proof (cases "U = res_type T")
    case True
    obtain env' args where ma: "make_args vname Ts env (arg_types T) = (env', args)"
      by (cases "make_args vname Ts env (arg_types T)")
    note pr = proj_res[OF cp up hu nA j T targ True[symmetric] ma]
    have "fin cfg (S_Proj vname env Ts (arg_types T) targs rb u dps bv targ tail)
        (EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U)"
    proof (rule fin_Proj[OF ma _ ftl])
      show "cuok (SIMPL (cfg_alg cfg) env'
          ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
        (\<lambda>(env2, f1, f2). EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U
          (El_C (list_comb bv args) env2 (f1 @ f2)))"
        by (rule cuok_mono[OF pr]) (auto simp: EC_def bv)
    qed
    with True show ?thesis by simp
  qed (simp add: ftl)
  with mf show ?case by blast
qed

end

end
