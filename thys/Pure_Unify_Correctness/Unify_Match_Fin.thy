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
  have pe: "okW (projenv cfg vname rb targs u env dps U Ts bv (arg_types T, res_type T) targ 0 tail) ?r"
    by (rule projenv_result[OF gU gb])
  have mf: "okW (matchfun cfg vname rb targs u env dps uhead uargs U Ts (p # projs)) ?r"
    using tl pe by (auto simp: p strip_type_arg_res[OF e] foldrW_arity_guesses_ground[OF gb])
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

context mfin
begin

text \<open>The measure of a copy: the number of unbound old variables, and the size of the instance.\<close>

abbreviation mlex :: "((nat \<times> nat) \<times> (nat \<times> nat)) set" where
  "mlex \<equiv> less_than <*lex*> less_than"

text \<open>The results of a state extension apply in the extended state:\<close>

lemma cpre_ext:
  assumes cp: "cpre V env dps rb targs Ts" and cr: "cres V env D V' env' dps' NV"
  shows "cpre V' env' dps' rb targs Ts"
proof -
  note c = cpreD[OF cp] and t = tsextD[OF conjunct1[OF cr[unfolded cres_def]]]
  have "list_all2 (has_type V' (map snd rb)) targs Ts"
    using list_all2_has_type_agreeV[OF c(4) _ t(2)] c(3) by blast
  then show ?thesis
    using c t(1,3) cr below_mono[OF _ t(3)] by (auto simp: cpre_def cres_def)
qed

lemma upre_ext:
  "upre V env rb a A \<Longrightarrow> cres V env D V' env' dps' NV \<Longrightarrow> upre V' env' rb a A"
  using has_type_agreeV[of V "map snd rb" a A "maxidx env" V'] below_mono[of "maxidx env" a "maxidx env'"]
  by (auto simp: upre_def cres_def tsext_def)

lemma oldin_ext:
  assumes cr: "cres V env D V' env' dps' NV" and o: "oldin env (X \<union> D)" and fr: "fresh_env env"
    and m: "m0 \<le> maxidx env"
  shows "oldin env' (X \<union> vps_dps dps')"
  unfolding oldin_def
proof (intro ballI impI)
  note t = tsextD[OF conjunct1[OF cr[unfolded cres_def]]]
  fix y assume y: "y \<in> reach env' (X \<union> vps_dps dps')" "snd (fst y) \<le> m0"
  have nv: "y \<notin> NV" using t(6)[of y] y(2) m by auto
  have rn: "reach env NV = NV" using reach_new[OF fr] t(6) by blast
  from t(7) y(1) nv have "y \<in> reach env (X \<union> vps_dps dps' \<union> D)" by blast
  moreover have "reach env (vps_dps dps') \<subseteq> reach env D \<union> NV"
    using reach_mono[of "vps_dps dps'" env "D \<union> NV"] t(8) reach_incl[of D env] rn
    by (auto simp: reach_Un)
  ultimately have "y \<in> reach env (X \<union> D)" using nv reach_mono[of D env "X \<union> D"] reach_incl[of "X \<union> D" env]
    by (auto simp: reach_Un)
  with o y(2) show "y \<in> S0" by (auto simp: oldin_def)
qed

text \<open>The copies of the arguments of an imitation, given the copies of each argument:\<close>

lemma copyargs_fin:
  assumes CC: "\<And>V' env' dps' a A us. ((mu1 env', isz env' V' (map snd rb) a A), (c, N)) \<in> mlex \<Longrightarrow>
      cpre V' env' dps' rb targs Ts \<Longrightarrow> upre V' env' rb a A \<Longrightarrow>
      oldin env' (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps') \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname rb targs a us env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>u' env'' dps'' V'' NV. x = El_D (u' # us) env'' dps'' \<and>
          cres V' env' (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps') V'' env'' dps'' NV \<and>
          cpy V'' env'' NV Ts u' A)"
    and cp: "cpre V env dps rb targs Ts" and mu: "mu1 env = c"
    and args: "list_all2 (\<lambda>a A. upre V env rb a A \<and> isz env V (map snd rb) a A < N) uargs As"
    and o: "oldin env (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps)"
  shows "fin cfg (copyargs vname rb targs env dps uargs)
    (ED V env (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts As)"
  using args o
proof (induction uargs As rule: list_all2_induct)
  case Nil
  note c = cpreD[OF cp]
  have "cres V env (\<Union> (vps ` set targs) \<union> vps_dps dps) V env dps {}"
    using tsext_refl[OF c(1)] c(5,6) by (auto simp: cres_def)
  then show ?case by (auto simp: ED_def intro!: fin_Single)
next
  case (Cons a uargs A As)
  note c = cpreD[OF cp]
  have ei: "env_inv ar V env" by (rule tyinvD(1)[OF c(1)])
  note e = env_invD[OF ei]
  define D where "D = \<Union> (vps ` set (a # uargs)) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
  define D' where "D' = \<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
  have DD': "D' \<subseteq> D" by (auto simp: D_def D'_def)
  have oD: "oldin env D" using Cons.prems by (simp add: D_def)
  have "oldin env D'" by (rule oldin_mono[OF oD]) (use DD' reach_incl[of D env] in blast)
  then have IH: "fin cfg (copyargs vname rb targs env dps uargs) (ED V env D' Ts As)"
    using Cons.IH unfolding D'_def by blast
  have ua: "upre V env rb a A" and ia: "isz env V (map snd rb) a A < N" using Cons.hyps(1) by simp_all
  have step: "\<exists>cs. okW (copycons cfg vname rb targs a us env' dps') cs \<and>
      fin cfg cs (ED V env D Ts (A # As))"
    if x: "ED V env D' Ts As (El_D us env' dps')" for us env' dps'
  proof -
    from x obtain V' NV where cr': "cres V env D' V' env' dps' NV"
      and cps: "list_all2 (\<lambda>u' A. cpy V' env' NV Ts u' A) us As"
      by (auto simp: ED_def)
    have cr: "cres V env D V' env' dps' NV" by (rule cres_mono[OF cr']) (use DD' reach_incl[of D env] in blast)
    note t = tsextD[OF conjunct1[OF cr[unfolded cres_def]]]
    have vg': "vgood Fd Ft env'" using cr by (simp add: cres_def)
    have cp': "cpre V' env' dps' rb targs Ts" by (rule cpre_ext[OF cp cr])
    have ua': "upre V' env' rb a A" by (rule upre_ext[OF ua cr])
    have Da: "vps a \<union> \<Union> (vps ` set targs) \<union> D = D" by (auto simp: D_def)
    have oa': "oldin env' (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps')"
      using oldin_ext[OF cr _ e(4) c(8), of "vps a \<union> \<Union> (vps ` set targs)"] oD Da by simp
    have lex: "((mu1 env', isz env' V' (map snd rb) a A), (c, N)) \<in> mlex"
    proof (cases "mu1 env' < mu1 env")
      case True
      with mu show ?thesis by simp
    next
      case False
      with mu1_mono[OF t(4)] have eq: "mu1 env' = mu1 env" by simp
      have "oldin env (vps a)" by (rule oldin_mono[OF oD]) (auto simp: D_def intro: reach_incl[THEN subsetD])
      moreover have "has_type V (map snd rb) a A" "below (maxidx env) a" "sh a" using ua by (simp_all add: upre_def)
      ultimately have "isz env' V' (map snd rb) a A = isz env V (map snd rb) a A"
        using isz_stable[OF ei c(5) conjunct1[OF cr[unfolded cres_def]] vg'] eq by blast
      with ia eq mu show ?thesis by simp
    qed
    from CC[OF lex cp' ua' oa'] obtain cs where cc: "okW (copycons cfg vname rb targs a us env' dps') cs"
      and fc: "fin cfg cs (\<lambda>x. \<exists>u' env'' dps'' V'' NV. x = El_D (u' # us) env'' dps'' \<and>
          cres V' env' (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps') V'' env'' dps'' NV \<and>
          cpy V'' env'' NV Ts u' A)"
      by blast
    have "fin cfg cs (ED V env D Ts (A # As))"
    proof (rule fin_mono[OF fc])
      fix x assume "\<exists>u' env'' dps'' V'' NV'. x = El_D (u' # us) env'' dps'' \<and>
          cres V' env' (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps') V'' env'' dps'' NV' \<and>
          cpy V'' env'' NV' Ts u' A"
      then obtain u' env'' dps'' V'' NV' where xe: "x = El_D (u' # us) env'' dps''"
        and cr2: "cres V' env' (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps') V'' env'' dps'' NV'"
        and cu: "cpy V'' env'' NV' Ts u' A"
        by blast
      note t2 = tsextD[OF conjunct1[OF cr2[unfolded cres_def]]]
      have "vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps' \<subseteq> reach env D \<union> NV"
        using t(8) reach_incl[of D env] by (auto simp: D_def)
      from cres_trans[OF cr cr2 e(4) this] have cr3: "cres V env D V'' env'' dps'' (NV \<union> NV')" .
      have "cpy V'' env'' (NV \<union> NV') Ts u' A" by (rule cpy_mono[OF cu]) auto
      moreover have "list_all2 (\<lambda>u' A. cpy V'' env'' (NV \<union> NV') Ts u' A) us As"
        by (rule list_all2_mono[OF cps]) (rule cpy_mono[OF _ t2(2,3)], auto)
      ultimately have "list_all2 (\<lambda>u' A. cpy V'' env'' (NV \<union> NV') Ts u' A) (u' # us) (A # As)"
        by simp
      with xe cr3 show "ED V env D Ts (A # As) x" by (auto simp: ED_def)
    qed
    with cc show ?thesis by blast
  qed
  have "fin cfg (S_Maps vname rb targs a (copyargs vname rb targs env dps uargs)) (ED V env D Ts (A # As))"
  proof (rule fin_Maps)
    show "fin cfg (copyargs vname rb targs env dps uargs) (\<lambda>x. \<exists>us env' dps' cs. x = El_D us env' dps' \<and>
        okW (copycons cfg vname rb targs a us env' dps') cs \<and> fin cfg cs (ED V env D Ts (A # As)))"
      by (rule fin_mono[OF IH]) (use step in \<open>fastforce simp: ED_def\<close>)
  qed
  then show ?case by (simp add: D_def)
qed

end

context mfin
begin

text \<open>
  \<open>mc\<close> on a term \<open>u\<close> in head normal form: by induction on the size of \<open>u\<close>, given the
  finiteness of the copies of arguments with a smaller measure.
\<close>

lemma mc_fin_aux:
  assumes CC: "\<And>V' env' dps' rb' targs' Ts' a A us. ((mu1 env', isz env' V' (map snd rb') a A), (c, N)) \<in> mlex \<Longrightarrow>
      cpre V' env' dps' rb' targs' Ts' \<Longrightarrow> upre V' env' rb' a A \<Longrightarrow>
      oldin env' (vps a \<union> \<Union> (vps ` set targs') \<union> vps_dps dps') \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname rb' targs' a us env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>u' env'' dps'' V'' NV. x = El_D (u' # us) env'' dps'' \<and>
          cres V' env' (vps a \<union> \<Union> (vps ` set targs') \<union> vps_dps dps') V'' env'' dps'' NV \<and>
          cpy V'' env'' NV Ts' u' A)"
  shows "cpre V env dps rb targs Ts \<Longrightarrow> upre V env rb u U \<Longrightarrow> hnf u \<Longrightarrow> hlong V (map snd rb) u U \<Longrightarrow>
    oldin env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) \<Longrightarrow> mu1 env = c \<Longrightarrow>
    isz env V (map snd rb) u U \<le> N \<Longrightarrow>
    \<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
      fin cfg sq (EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U)"
proof (induction "size u" arbitrary: rb targs Ts u U rule: less_induct)
  case less
  note cp = less.prems(1) and up = less.prems(2) and hu = less.prems(3) and hl = less.prems(4)
    and o = less.prems(5) and mu = less.prems(6) and szN = less.prems(7)
  note c = cpreD[OF cp]
  have ei: "env_inv ar V env" by (rule tyinvD(1)[OF c(1)])
  note e = env_invD[OF ei]
  have e0: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF e(2)])
  have wu: "wf_tm ar rb u" and tyu: "has_type V (map snd rb) u U" and bu: "below (maxidx env) u"
    and shu: "sh u"
    using up by (simp_all add: upre_def)
  define D where "D = vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
  from has_type_head_of[OF tyu] obtain T0 where tyh: "has_type V (map snd rb) (head_of u) T0" ..
  have mcu: "mc cfg vname rb targs u env dps =
    (case head_of u of
        Abs a T body \<Rightarrow> do {
          s \<leftarrow> mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps;
          returnW (S_MapAbs a T s)}
      | Var w _ \<Rightarrow>
          (let (env', newhd) = genvar (fst w) env (foldr fun_type Ts (res_type T0)) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u) # dps))))
      | _ \<Rightarrow> do {
          projs \<leftarrow> make_projs u targs Ts targs;
          matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) (res_type T0) Ts (rev projs)})"
    by (rule mc_unfold[OF e0 fastype_typed[OF e0 tyh] mapM_fastype[OF e0 c(4)]])
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF c(4)] by simp
  have gTs: "ground ar T" if "T \<in> set Ts" for T
  proof -
    from that obtain i where i: "i < length Ts" "T = Ts ! i" by (auto simp: in_set_conv_nth)
    with c(4) have "has_type V (map snd rb) (targs ! i) T" by (simp add: list_all2_conv_all_nth)
    moreover have "wf_tm ar rb (targs ! i)" using c(3) i lTs by simp
    ultimately show ?thesis using ground_has_type[OF e0 c(2)] by blast
  qed
  have gU: "ground ar U" by (rule ground_has_type[OF e0 c(2) wu tyu])
  have rigid: "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and> fin cfg sq (EC V env D Ts U)"
    if hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
  proof -
    have nA: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
    have nfU: "\<not> is_funT U" using hl nA by (cases rule: hlong.cases) auto
    have rT0: "res_type T0 = U" using res_type_head(1)[OF tyu nfU tyh] .
    define uargs where "uargs = snd (strip_comb u)"
    from res_type_head(2)[OF tyu nfU tyh] obtain As where T0: "T0 = foldr fun_type As U"
      and tyargs: "list_all2 (has_type V (map snd rb)) uargs As" by (auto simp: uargs_def)
    have u_eq: "u = list_comb (head_of u) uargs" unfolding uargs_def by (rule head_of_list_comb)
    have hrig: "is_rigid (head_of u)"
      using hA hV head_of_not_App[of u] tyh
      by (cases "head_of u") (auto simp: is_rigid_def has_type_Bound_iff)
    from make_projs_exact[OF lTs, of u targs] obtain projs where pr: "make_projs u targs Ts targs = returnW projs"
      by blast
    have pidx: "\<forall>(bv, T, targ)\<in>set (rev projs). ground ar T \<and> (\<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
        nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and>
        T = Ts ! (length targs - 1 - nat_of_integer j))"
    proof
      fix p assume pin: "p \<in> set (rev projs)"
      obtain bv T targ where p1: "p = (bv, T, targ)" by (cases p)
      with pin have p: "p = (bv, T, targ)" "(bv, T, targ) \<in> set projs" by simp_all
      from make_projs_idx[of u targs Ts targs projs] pr p(2) obtain j where
        j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length targs"
        "targ = targs ! (length targs - 1 - nat_of_integer j)" "T = Ts ! (length targs - 1 - nat_of_integer j)"
        by fastforce
      have "ground ar T" using gTs j(3,5) lTs by simp
      with j p(1) show "case p of (bv, T, targ) \<Rightarrow> ground ar T \<and> (\<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
          nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and>
          T = Ts ! (length targs - 1 - nat_of_integer j))" by auto
    qed
    have imit: "fin cfg (case head_of u of
        Const _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) (EC V env D Ts U)"
    proof -
      have whd: "wf_tm ar rb (head_of u)" and wua: "\<forall>t\<in>set uargs. wf_tm ar rb t"
        using wu u_eq by (metis wf_tm_list_comb)+
      have bua: "\<forall>t\<in>set uargs. below (maxidx env) t" using bu u_eq by (metis below_list_comb)
      have dua: "\<forall>t\<in>set uargs. dead Fd t" using shu u_eq by (metis dd_list_comb sh_def)
      have vua: "\<forall>t\<in>set uargs. vars t \<subseteq> vars u" using u_eq vars_list_comb[of "head_of u" uargs] by auto
      have tyhA: "has_type V (map snd rb) (head_of u) (foldr fun_type As U)" using tyh T0 by simp
      have args: "list_all2 (\<lambda>a A. upre V env rb a A \<and> isz env V (map snd rb) a A < N) uargs As"
      proof (rule list_all2_all_nthI)
        show "length uargs = length As" using list_all2_lengthD[OF tyargs] .
        fix i assume i: "i < length uargs"
        have "has_type V (map snd rb) (uargs ! i) (As ! i)" using tyargs i by (simp add: list_all2_conv_all_nth)
        moreover have "sh (uargs ! i)" using dua vua shu i by (auto simp: sh_def dest!: nth_mem)
        ultimately have "upre V env rb (uargs ! i) (As ! i)"
          using wua bua i by (simp add: upre_def)
        moreover have "isz env V (map snd rb) (uargs ! i) (As ! i) < isz env V (map snd rb) u U"
          using isz_rigid_arg[OF ei hrig tyhA tyargs i] u_eq by simp
        ultimately show "upre V env rb (uargs ! i) (As ! i) \<and> isz env V (map snd rb) (uargs ! i) (As ! i) < N"
          using szN by simp
      qed
      have Da: "\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps \<subseteq> D"
        using u_eq vps_list_comb[of "head_of u" uargs] by (auto simp: D_def)
      have oa: "oldin env (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps)"
        by (rule oldin_mono[OF o[folded D_def]]) (use Da reach_incl[of D env] in blast)
      note ca = copyargs_fin[OF CC cp mu args oa]
      show ?thesis
      proof (cases "\<exists>cn Tc. head_of u = Const cn Tc \<or> head_of u = Free cn Tc")
        case True
        then obtain cn Tc where hc: "head_of u = Const cn Tc \<or> head_of u = Free cn Tc" by blast
        have Tc: "Tc = T0" using tyh hc by (auto elim: has_type_elims)
        have "fin cfg (copyargs vname rb targs env dps uargs) (\<lambda>x. \<exists>us e d. x = El_D us e d \<and>
            EC V env D Ts U (El_C (list_comb (head_of u) us) e d))"
        proof (rule fin_mono[OF ca])
          fix x assume "ED V env (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts As x"
          then obtain us e d V' NV where x: "x = El_D us e d"
            and cr: "cres V env (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) V' e d NV"
            and cps: "list_all2 (\<lambda>u' A. cpy V' e NV Ts u' A) us As"
            by (auto simp: ED_def)
          have cr': "cres V env D V' e d NV" by (rule cres_mono[OF cr]) (use Da reach_incl[of D env] in blast)
          have tyc: "list_all2 (has_type V' (rev Ts)) us As" using cps by (auto simp: cpy_def elim: list_all2_mono)
          have tyhu: "has_type V' (rev Ts) (head_of u) (foldr fun_type As U)"
            using hc Tc T0 tyh by (auto intro: has_type.Const has_type.Free elim: has_type_elims)
          have "cpy V' e NV Ts (list_comb (head_of u) us) U"
            unfolding cpy_def
          proof (intro conjI)
            show "has_type V' (rev Ts) (list_comb (head_of u) us) U" using tyhu tyc by (auto simp: has_type_list_comb)
            show "wf_cp ar (length Ts) (list_comb (head_of u) us)"
              using whd cps hc by (auto simp: cpy_def wf_cp_def wf_tm_def proper_list_comb typs_ok_list_comb
                  tr_list_comb no_loose_bound_list_app list_all2_conv_all_nth in_set_conv_nth)
            show "below (maxidx e) (list_comb (head_of u) us)"
              using cps hc by (auto simp: cpy_def below_list_comb list_all2_conv_all_nth in_set_conv_nth)
            have "vps t \<subseteq> NV" if "t \<in> set us" for t
            proof -
              from that obtain i where "i < length us" "t = us ! i" by (auto simp: in_set_conv_nth)
              with cps show ?thesis by (auto simp: cpy_def list_all2_conv_all_nth)
            qed
            then show "vps (list_comb (head_of u) us) \<subseteq> NV" using hc by (auto simp: vps_list_comb)
          qed
          with x cr' show "\<exists>us e d. x = El_D us e d \<and> EC V env D Ts U (El_C (list_comb (head_of u) us) e d)"
            by (auto simp: EC_def)
        qed
        then have "fin cfg (S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs)) (EC V env D Ts U)"
          by (rule fin_MapJoin)
        with hc show ?thesis by auto
      next
        case False
        then show ?thesis by (cases "head_of u") auto
      qed
    qed
    from matchfun_fin[OF cp up hrig nA gU pidx imit[unfolded D_def]] obtain sq where
      mf: "okW (matchfun cfg vname rb targs u env dps (head_of u) uargs U Ts (rev projs)) sq"
      and fs: "fin cfg sq (EC V env D Ts U)"
      by (auto simp: D_def)
    have "okW (mc cfg vname rb targs u env dps) sq"
      using mcu pr mf hA hV rT0 by (cases "head_of u") (simp_all add: uargs_def)
    with fs show ?thesis by blast
  qed
  show ?case
  proof (cases "head_of u")
    case (Abs a T body)
    have u: "u = Abs a T body" using hnf_Abs_head[OF hu] Abs by (simp add: fst_strip_comb)
    from hl u obtain U' where U: "U = T \<rightarrow>\<^sub>T U'" and hlb: "hlong V (T # map snd rb) body U'"
      by (auto elim: hlong.cases)
    have wb: "wf_tm ar ((a, T) # rb) body" and gT: "ground ar T" using wu u by (simp_all add: wf_tm_def)
    have bok': "binders_ok ar ((a, T) # rb)" using c(2) gT by (simp add: binders_ok_def)
    have hb: "hnf body" using hu u by simp
    have bb: "below (maxidx env) body" using bu u by simp
    have shb: "sh body" using shu u by (simp add: sh_def)
    define targs' where "targs' = map (incr_boundvars 1) targs @ [Bound 0]"
    have tg': "\<forall>t\<in>set targs'. wf_tm ar ((a, T) # rb) t \<and> below (maxidx env) t \<and> sh t"
    proof
      fix t assume "t \<in> set targs'"
      then consider (i) t0 where "t0 \<in> set targs" "t = incr_boundvars 1 t0" | (b) "t = Bound 0"
        by (auto simp: targs'_def)
      then show "wf_tm ar ((a, T) # rb) t \<and> below (maxidx env) t \<and> sh t"
      proof cases
        case i
        then show ?thesis using c(3)[OF i(1)] by (auto simp: below_vps_iff intro: wf_tm_incr sh_incr)
      qed (simp add: wf_tm_Bound0 sh_def below_def)
    qed
    have tgty': "list_all2 (has_type V (map snd ((a, T) # rb))) targs' (Ts @ [T])"
      unfolding targs'_def
    proof (rule list_all2_appendI)
      show "list_all2 (has_type V (map snd ((a, T) # rb))) (map (incr_boundvars 1) targs) Ts"
        using c(4) by (simp add: list_all2_map1) (erule list_all2_mono, simp add: has_type_incr_boundvars1)
    qed (simp add: has_type_Bound_iff)
    have cp': "cpre V env dps ((a, T) # rb) targs' (Ts @ [T])"
      using c tg' tgty' bok' tok_incr[OF c(7)] by (simp add: cpre_def targs'_def)
    have tyb: "has_type V (T # map snd rb) body U'" by (rule hlong_typed[OF hlb])
    have up': "upre V env ((a, T) # rb) body U'" using wb tyb bb shb by (simp add: upre_def)
    have vt': "\<Union> (vps ` set targs') = \<Union> (vps ` set targs)" by (auto simp: targs'_def)
    have Db: "vps body \<union> \<Union> (vps ` set targs') \<union> vps_dps dps = D" using u vt' by (simp add: D_def)
    have o': "oldin env (vps body \<union> \<Union> (vps ` set targs') \<union> vps_dps dps)" using o Db by (simp add: D_def)
    have "isz env V (map snd ((a, T) # rb)) body U' = isz env V (map snd rb) u U"
      using isz_Abs[OF ei tyu[unfolded u U]] u U by simp
    with szN have sz': "isz env V (map snd ((a, T) # rb)) body U' \<le> N" by simp
    have "size body < size u" using u by simp
    from less.hyps[OF this cp' up' hb _ o' mu sz'] hlb obtain sq where
      mcb: "okW (mc cfg vname ((a, T) # rb) targs' body env dps) sq"
      and fb: "fin cfg sq (EC V env (vps body \<union> \<Union> (vps ` set targs') \<union> vps_dps dps) (Ts @ [T]) U')"
      by auto
    have mc: "okW (mc cfg vname rb targs u env dps) (S_MapAbs a T sq)"
      using mcu Abs mcb by (simp add: targs'_def)
    have "fin cfg sq (\<lambda>x. \<exists>u'' e'' d''. x = El_C u'' e'' d'' \<and> EC V env D Ts U (El_C (Abs a T u'') e'' d''))"
    proof (rule fin_mono[OF fb])
      fix x assume "EC V env (vps body \<union> \<Union> (vps ` set targs') \<union> vps_dps dps) (Ts @ [T]) U' x"
      then obtain u' env' dps' V' NV where x: "x = El_C u' env' dps'" and cr: "cres V env D V' env' dps' NV"
        and cu: "cpy V' env' NV (Ts @ [T]) u' U'"
        by (auto simp: EC_def Db)
      have "cpy V' env' NV Ts (Abs a T u') U"
        using cu gT U by (auto simp: cpy_def wf_cp_def intro: has_type.Abs)
      with x cr show "\<exists>u'' e'' d''. x = El_C u'' e'' d'' \<and> EC V env D Ts U (El_C (Abs a T u'') e'' d'')"
        by (auto simp: EC_def)
    qed
    then have "fin cfg (S_MapAbs a T sq) (EC V env D Ts U)" by (rule fin_MapAbs)
    with mc show ?thesis by (auto simp: D_def)
  next
    case (Var w W)
    have nA: "\<not> is_Abs u" using Var by (cases u) auto
    have nfU: "\<not> is_funT U" using hl nA by (cases rule: hlong.cases) auto
    have rT0: "res_type T0 = U" using res_type_head(1)[OF tyu nfU tyh] .
    define GT where "GT = foldr fun_type Ts U"
    have gGT: "ground ar GT" unfolding GT_def by (rule ground_foldr_fun_type) (use gTs gU in auto)
    obtain env1 newhd where g: "genvar (fst w) env GT = (env1, newhd)" by (cases "genvar (fst w) env GT")
    define G where "G = (fst w, maxidx env + 1)"
    define V1 where "V1 = V(G := GT)"
    note ge = genvar_term[OF ei g, folded G_def V1_def]
    define dp where "dp = (rb, list_comb newhd targs, u)"
    have tg1: "list_all2 (has_type V1 (map snd rb)) targs Ts"
      using list_all2_has_type_agreeV[OF c(4) _ ge(2)] c(3) by blast
    have tyu1: "has_type V1 (map snd rb) u U" using has_type_agreeV[OF tyu bu ge(2)] .
    have tyG: "has_type V1 Bs newhd GT" for Bs using ge(4,7) by (simp add: has_type.Var)
    have tyl: "has_type V1 (map snd rb) (list_comb newhd targs) U"
      using tyG tg1 by (auto simp: has_type_list_comb GT_def)
    have wG: "wf_tm ar rb newhd" using ge(4) gGT by (simp add: wf_tm_def)
    have bG: "below (maxidx env1) newhd" using ge(3,4) by (simp add: G_def)
    have ti: "tyinv ar V1 env1 (dp # dps)"
    proof -
      have "tyinv ar V1 env1 dps"
        by (rule tyinv_transfer[OF ge(1) _ ge(2)]) (use tyinvD(2)[OF c(1)] ge(3) in auto)
      moreover have "wf_dp ar dp" using c(2,3) wG wu by (simp add: dp_def wf_tm_list_comb)
      moreover have "dp_typed V1 dp" using tyl tyu1 by (auto simp: dp_def dp_typed_def)
      moreover have "dp_below (maxidx env1) dp"
        using bG c(3) bu ge(3) below_mono[of "maxidx env" _ "maxidx env + 1"]
        by (auto simp: dp_def dp_below_def below_list_comb)
      ultimately show ?thesis by (simp add: tyinv_def)
    qed
    have pg: "pgood Fd Ft dp"
    proof -
      have "G \<in> Fd \<union> Ft" using fresh_iff c(8) by (simp add: G_def)
      have "G \<in> Fd \<Longrightarrow> \<exists>t\<in>set targs. \<not> is_Bound t" using c(7) by (auto simp: tok_def)
      then have d: "dead Fd (list_comb newhd targs)" using ge(4) c(3) by (auto simp: dd_list_comb sh_def G_def)
      have "hok Ft (list_comb newhd targs)" using ge(4) c(3) by (auto simp: hok_list_comb sh_def)
      then have "gs Ft (list_comb newhd targs)" by (rule hok_gs)
      moreover have "gs Ft u" using shu by (auto simp: sh_def intro: gs_free)
      ultimately show ?thesis using d shu by (simp add: pgood_def dp_def sh_def)
    qed
    have mc: "okW (mc cfg vname rb targs u env dps)
        (S_Single (El_C (combound newhd 0 (length Ts)) env1 (dp # dps)))"
      using mcu Var g rT0 by (simp add: dp_def GT_def)
    define NV where "NV = {(G, GT)}"
    have rr: "reach env1 = reach env" by (rule reach_tenv[OF ge(6)])
    have tx: "tsext ar V env V1 env1 (dp # dps) D NV"
      unfolding tsext_def
    proof (intro conjI allI ballI ti ge(2,5))
      show "maxidx env \<le> maxidx env1" using ge(3) by simp
      show "finite NV" by (simp add: NV_def)
      show "maxidx env < snd (fst y)" if "y \<in> NV" for y using that by (simp add: NV_def G_def)
      show "snd (fst y) \<le> maxidx env1" if "y \<in> NV" for y using that ge(3) by (simp add: NV_def G_def)
      show "reach env1 X \<subseteq> reach env (X \<union> D) \<union> NV" for X using reach_subset[of X "X \<union> D" env] rr by auto
      have "vps_dps (dp # dps) \<subseteq> D \<union> NV" using ge(4) by (auto simp: dp_def vps_dp_def vps_list_comb D_def NV_def)
      then show "vps_dps (dp # dps) \<subseteq> reach env D \<union> NV" using reach_incl[of D env] by blast
    qed
    have cr: "cres V env D V1 env1 (dp # dps) NV"
      using tx pg c(5,6) by (simp add: cres_def vgood_tenv[OF ge(6)])
    have cu: "cpy V1 env1 NV Ts (combound newhd 0 (length Ts)) U"
      unfolding cpy_def
    proof (intro conjI)
      show "has_type V1 (rev Ts) (combound newhd 0 (length Ts)) U"
        using has_type_combound0[of V1 Ts "[]" newhd U] tyG by (simp add: GT_def)
      show "wf_cp ar (length Ts) (combound newhd 0 (length Ts))"
        by (rule wf_cp_combound) (use ge(4) gGT in simp_all)
      show "below (maxidx env1) (combound newhd 0 (length Ts))" using bG by (simp add: below_vps_iff)
      show "vps (combound newhd 0 (length Ts)) \<subseteq> NV" using ge(4) by (simp add: NV_def)
    qed
    have "fin cfg (S_Single (El_C (combound newhd 0 (length Ts)) env1 (dp # dps))) (EC V env D Ts U)"
      by (rule fin_Single) (use cr cu in \<open>auto simp: EC_def\<close>)
    with mc show ?thesis by (auto simp: D_def)
  next
    case (Const cn Tc)
    then show ?thesis using rigid by (simp add: D_def)
  next
    case (Free cn Tc)
    then show ?thesis using rigid by (simp add: D_def)
  next
    case (Bound i)
    then show ?thesis using rigid by (simp add: D_def)
  next
    case (App f x)
    then show ?thesis by (simp add: head_of_not_App)
  qed
qed

end

context mfin
begin

text \<open>
  The copies of an argument by \<^const>\<open>copycons\<close> form a finite enumeration: by well-founded
  induction on the number of unbound old variables and the size of the instance of the argument.
\<close>

lemma copycons_fin_aux:
  "\<forall>V env dps rb targs Ts a A us. (mu1 env, isz env V (map snd rb) a A) = m \<longrightarrow>
    cpre V env dps rb targs Ts \<longrightarrow> upre V env rb a A \<longrightarrow>
    oldin env (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) \<longrightarrow>
    (\<exists>cs. okW (copycons cfg vname rb targs a us env dps) cs \<and>
      fin cfg cs (\<lambda>x. \<exists>u' env' dps' V' NV. x = El_D (u' # us) env' dps' \<and>
        cres V env (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) V' env' dps' NV \<and> cpy V' env' NV Ts u' A))"
proof (induction m rule: wf_induct[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  case (1 m)
  obtain c N where m: "m = (c, N)" by (cases m)
  show ?case
  proof (intro allI impI)
    fix V env dps rb targs Ts a A us
    assume mu: "(mu1 env, isz env V (map snd rb) a A) = m" and cp: "cpre V env dps rb targs Ts"
      and ua: "upre V env rb a A" and o: "oldin env (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps)"
    note c = cpreD[OF cp]
    have ei: "env_inv ar V env" by (rule tyinvD(1)[OF c(1)])
    have wa: "wf_tm ar rb a" and tya: "has_type V (map snd rb) a A" and ba: "below (maxidx env) a"
      and sha: "sh a"
      using ua by (simp_all add: upre_def)
    have CC: "\<exists>cs. okW (copycons cfg vname rb' targs' a' us' env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>u' env'' dps'' V'' NV. x = El_D (u' # us') env'' dps'' \<and>
          cres V' env' (vps a' \<union> \<Union> (vps ` set targs') \<union> vps_dps dps') V'' env'' dps'' NV \<and>
          cpy V'' env'' NV Ts' u' A')"
      if "((mu1 env', isz env' V' (map snd rb') a' A'), (c, N)) \<in> mlex" "cpre V' env' dps' rb' targs' Ts'"
        "upre V' env' rb' a' A'" "oldin env' (vps a' \<union> \<Union> (vps ` set targs') \<union> vps_dps dps')"
      for V' env' dps' rb' targs' Ts' a' A' us'
      using "1.IH"[rule_format, of "(mu1 env', isz env' V' (map snd rb') a' A')"] that m by blast
    from copy_norm_isz[OF ei c(2) wa tya ba] obtain u1 u2 where
      h: "ok (head_norm env a) u1" and et: "ok (eta_norm env rb u1) u2"
      and w2: "wf_tm ar rb u2" and hn2: "hnf u2" and hl2: "hlong V (map snd rb) u2 A"
      and b2: "below (maxidx env) u2" and v2: "vps u2 \<subseteq> reach env (vps a)"
      and is2: "isz env V (map snd rb) u2 A = isz env V (map snd rb) a A"
      by blast
    have sh2: "sh u2"
    proof -
      have "dead Fd u1" using head_norm_good(1)[OF h c(5)] sha by (simp add: sh_def)
      then have "dead Fd u2" using eta_norm_good[OF et] by blast
      moreover have "fst y \<notin> Ft" if "y \<in> vps u2" for y
        using reach_free[OF c(5) _ v2[THEN subsetD, OF that]] sha by (auto simp: sh_def vars_eq_vps)
      ultimately show ?thesis by (auto simp: sh_def vars_eq_vps)
    qed
    have up2: "upre V env rb u2 A" using w2 hlong_typed[OF hl2] b2 sh2 by (simp add: upre_def)
    have da: "ok (defer_arg env rb u2) False"
      using defer_arg_typed[OF wf_envD(1)[OF env_invD(2)[OF ei]] c(2) _ hlong_typed[OF hl2]] w2
      by (simp add: wf_tm_def)
    define D where "D = vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
    have D2: "vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps \<subseteq> reach env D"
      using v2 reach_subset[of "vps a" D env] reach_incl[of D env] by (auto simp: D_def)
    have o2: "oldin env (vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps)"
      by (rule oldin_mono[OF o[folded D_def] D2])
    from mu m have mu': "mu1 env = c" and szN: "isz env V (map snd rb) u2 A \<le> N" using is2 by auto
    from mc_fin_aux[OF CC cp up2 hn2 hl2 o2 mu' szN] obtain sq where
      mc: "okW (mc cfg vname rb targs u2 env dps) sq"
      and fs: "fin cfg sq (EC V env (vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts A)"
      by blast
    have "fin cfg (S_MapCons us sq) (\<lambda>x. \<exists>u' env' dps' V' NV. x = El_D (u' # us) env' dps' \<and>
        cres V env D V' env' dps' NV \<and> cpy V' env' NV Ts u' A)"
    proof (rule fin_MapCons, rule fin_mono[OF fs])
      fix x assume "EC V env (vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts A x"
      then obtain u' env' dps' V' NV where x: "x = El_C u' env' dps'"
        and cr: "cres V env (vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) V' env' dps' NV"
        and cu: "cpy V' env' NV Ts u' A"
        by (auto simp: EC_def)
      have "cres V env D V' env' dps' NV" by (rule cres_mono[OF cr D2])
      with x cu show "\<exists>u e d. x = El_C u e d \<and> (\<exists>u' env' dps' V' NV. El_D (u # us) e d = El_D (u' # us) env' dps' \<and>
          cres V env D V' env' dps' NV \<and> cpy V' env' NV Ts u' A)"
        by blast
    qed
    then show "\<exists>cs. okW (copycons cfg vname rb targs a us env dps) cs \<and>
        fin cfg cs (\<lambda>x. \<exists>u' env' dps' V' NV. x = El_D (u' # us) env' dps' \<and>
          cres V env (vps a \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) V' env' dps' NV \<and> cpy V' env' NV Ts u' A)"
      using copycons_ok[OF h et da mc, of us] unfolding D_def by blast
  qed
qed

theorem mc_fin:
  assumes "cpre V env dps rb targs Ts" "upre V env rb u U" "hnf u" "hlong V (map snd rb) u U"
    "oldin env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps)"
  shows "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
    fin cfg sq (EC V env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U)"
  by (rule mc_fin_aux[OF _ assms refl order_refl])
    (use copycons_fin_aux in blast)

end

subsection \<open>Binding the variable of the pair, without a solution\<close>

lemma new_dset_term:
  assumes inv: "tyinv ar V' env' dps'" and tyu': "has_type V' (rev Ts) u' U" and wc: "wf_cp ar (length Ts) u'"
    and bu': "below (maxidx env') u'" and T: "T = foldr fun_type Ts U" and Vv: "V' v = T"
    and gT: "ground ar T" and gTs: "\<forall>A\<in>set Ts. ground ar A" and vm: "snd v \<le> maxidx env'"
    and ac: "(v, T) \<notin> reach env' (vps u')"
  shows "\<exists>y. okW (new_dset (v, T) Ts u' env' dps') y \<and> (\<exists>env'' dps''. y = El_E env'' dps'' \<and> tyinv ar V' env'' dps'')"
proof -
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  have e: "vt_is_empty (tyenv env')" by (rule wf_envD(1)[OF ei(2)])
  have tya: "has_type V' [] (types_abs Ts u') T" using has_type_types_abs[of V' Ts "[]" u' U] tyu' T by simp
  have wa: "wf_tm ar [] (types_abs Ts u')" by (rule wf_tm_types_abs[OF gTs wc])
  from lookup_typed[OF e ei(3) Vv] obtain r where lr: "lookup env' v T = return r" by blast
  then have lk: "ok (lookup env' v T) r" by (simp add: return_def)
  from ok_lookup[OF e lk] show ?thesis
  proof (elim disjE exE conjE)
    assume r: "r = None" and vn: "vt_lookup (tenv env') v = None"
    from update_unbound_ok[OF vn, of T "types_abs Ts u'"] obtain env'' where
      upd: "update (v, T) (types_abs Ts u') env' = Some (Ok env'')" by blast
    have upd': "ok (update (v, T) (types_abs Ts u') env') env''" using upd by simp
    have ok: "okW (new_dset (v, T) Ts u' env' dps') (El_E env'' dps')"
      using lr r upd by (simp add: new_dset_def return_def)
    have ba: "below (maxidx env') (types_abs Ts u')" using bu' by simp
    note ut = update_typed[OF ei(4) ei(3) upd' Vv tya vm ba]
    have ac'': "acyc env''"
      unfolding acyc_def
      by (rule acyclic_update[OF dep_update[OF ok_update(2,1)[OF upd']]])
        (use ac ei(1) in \<open>simp_all add: acyc_def\<close>)
    have wf'': "wf_env ar env''"
      using ok_update_wf_env[OF upd' ei(2) _ _ gT] wa by (simp add: wf_tm_def)
    have "tyinv ar V' env'' dps'"
      using inv ac'' wf'' ut by (simp add: tyinv_def env_inv_def)
    then show ?thesis using ok by blast
  next
    fix s0 assume r: "r = Some s0" and vs0: "vt_lookup (tenv env') v = Some (T, s0)"
    let ?dp = "([], s0, types_abs Ts u')"
    have ok: "okW (new_dset (v, T) Ts u' env' dps') (El_E env' (?dp # dps'))"
      using lr r by (simp add: new_dset_def return_def)
    have ws0: "wf_tm ar [] s0" using wf_envD[OF ei(2)] vs0 by (auto simp: wf_env_def wf_tm_def)
    have ty0: "has_type V' [] s0 T" using env_typedD[OF ei(3) vs0] by simp
    have b0: "below (maxidx env') s0" using fresh_envD[OF ei(4) vs0] by simp
    have "tyinv ar V' env' (?dp # dps')"
      using inv ws0 wa ty0 tya b0 bu' by (auto simp: tyinv_def binders_ok_def)
    then show ?thesis using ok by blast
  qed
qed

subsection \<open>The single step of matching\<close>

text \<open>The counterpart of @{thm [source] make_args_copy} without a solution:\<close>

lemma make_args_copy_term:
  assumes inv: "tyinv ar V env dps" and ma: "make_args vname Ts env Us = (env', args)"
    and gTs: "\<forall>A\<in>set Ts. ground ar A" and gUs: "\<forall>A\<in>set Us. ground ar A"
    and tyhd: "\<And>V'. has_type V' (rev Ts) hd0 (foldr fun_type Us U)" and vhd: "vps hd0 = {}"
    and thd: "typs_ok ar hd0"
  obtains V1 where "tyinv ar V1 env' dps" "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env'"
    "tenv env' = tenv env" "has_type V1 (rev Ts) (list_comb hd0 args) U"
    "wf_cp ar (length Ts) (list_comb hd0 args)" "below (maxidx env') (list_comb hd0 args)"
    "\<forall>y\<in>vps (list_comb hd0 args). maxidx env < snd (fst y)"
proof -
  have ei: "env_inv ar V env" by (rule tyinvD(1)[OF inv])
  obtain V1 xs where me: "env_inv ar V1 env'" "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env'"
    "extends env' env" "tenv env' = tenv env" "length xs = length Us" "distinct xs"
    "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env'"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    by (rule make_args_term[OF ei ma])
  have la: "length args = length Us" using me(6,9) by simp
  have ai: "args ! i = combound (Var (xs ! i) (foldr fun_type Ts (Us ! i))) 0 (length Ts)"
    if "i < length Us" for i using me(6,9) that by simp
  have gGi: "ground ar (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
    using ground_foldr_fun_type[of Ts ar "Us ! i"] gTs gUs that by auto
  have bGi: "maxidx env < snd (xs ! i)" "snd (xs ! i) \<le> maxidx env'" if "i < length Us" for i
    using me(8) me(6) that by (auto dest: nth_mem)
  have vai: "vps (args ! i) = {(xs ! i, foldr fun_type Ts (Us ! i))}" if "i < length Us" for i
    using ai[OF that] by simp
  have vargs: "y \<in> vps a \<Longrightarrow> a \<in> set args \<Longrightarrow> maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'" for y a
    using vai bGi la by (auto simp: in_set_conv_nth)
  define u' where "u' = list_comb hd0 args"
  have "has_type V1 (rev Ts) (args ! i) (Us ! i)" if "i < length Us" for i
    using has_type_combound0[of V1 Ts "[]" "Var (xs ! i) (foldr fun_type Ts (Us ! i))" "Us ! i"]
      me(10) that ai[OF that] by (simp add: has_type.Var)
  then have tyai: "list_all2 (has_type V1 (rev Ts)) args Us" using la by (simp add: list_all2_conv_all_nth)
  have tyu': "has_type V1 (rev Ts) u' U" using tyhd[of V1] tyai by (auto simp: u'_def has_type_list_comb)
  have vu': "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'" if "y \<in> vps u'" for y
    using that vargs vhd by (fastforce simp: u'_def vps_list_comb)
  have wc: "wf_cp ar (length Ts) u'"
  proof -
    have "typs_ok ar a" if "a \<in> set args" for a
      using that la ai gGi by (auto simp: in_set_conv_nth typs_ok_combound)
    then show ?thesis
      unfolding wf_cp_def using has_type_proper[OF tyu'] has_type_closed[OF tyu'] thd
      by (auto simp: u'_def typs_ok_list_comb)
  qed
  have bu': "below (maxidx env') u'" using vu' by (auto simp: below_vps_iff)
  have ti: "tyinv ar V1 env' dps"
    by (rule tyinv_transfer[OF me(1) _ me(2,3)]) (use tyinvD(2)[OF inv] in blast)
  show ?thesis by (rule that[OF ti me(2,3,5) tyu'[unfolded u'_def] wc[unfolded u'_def] bu'[unfolded u'_def]])
    (use vu' in \<open>simp add: u'_def\<close>)
qed

lemma match1_projs_fin:
  assumes "vt_is_empty (tyenv env)" "ground ar base" "fin cfg tail Q"
    "\<forall>(bv, T, targ)\<in>set projs. ground ar T \<and> (res_type T = base \<longrightarrow>
      (\<forall>env' args. make_args vname Ts env (arg_types T) = (env', args) \<longrightarrow> Q (El_C (list_comb bv args) env' dps)))"
  shows "\<exists>sq. okW (match1_projs cfg vname env dps base Ts projs tail) sq \<and> fin cfg sq Q"
  using assms(4)
proof (induction projs)
  case Nil
  show ?case using assms(3) by simp
next
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  from Cons obtain tl where tl: "okW (match1_projs cfg vname env dps base Ts projs tail) tl"
    and ftl: "fin cfg tl Q" by auto
  have gT: "ground ar T" using Cons.prems p by simp
  have gb: "ground ar (res_type T)"
    using strip_type_ground(2)[OF assms(1) gT, of "arg_types T" "res_type T"]
    by (simp add: strip_type_arg_res[OF assms(1)])
  obtain env1 args1 where ma: "make_args vname Ts env (arg_types T) = (env1, args1)"
    by (cases "make_args vname Ts env (arg_types T)")
  let ?r = "if base = res_type T then S_Append (S_Single (El_C (list_comb bv args1) env1 dps)) tl else tl"
  let ?m = "(if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base (res_type T) env
    else cunify_types (cfg_alg cfg) base (res_type T) env)"
  let ?b = "do {env' \<leftarrow> ?m; (case make_args vname Ts env' (arg_types T) of (env'', args) \<Rightarrow>
    returnW (S_Append (S_Single (El_C (list_comb bv args) env'' dps)) tl))}"
  have h: "okW (handleW ?b (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tl | _ \<Rightarrow> raiseW e)) ?r"
  proof (cases "base = res_type T")
    case True
    then have "okW ?m env"
      by (auto simp: test_unify_types_def cunify_types_same okW_whenW)
    then have "okW ?b (S_Append (S_Single (El_C (list_comb bv args1) env1 dps)) tl)" using ma by auto
    then show ?thesis using True by (simp add: okW_handleW)
  next
    case False
    from cunify_types_ground_neq[OF assms(2) gb False] obtain evs
      where c: "cunify_types (cfg_alg cfg) base (res_type T) env = Some (evs, UErr CANTUNIFY)" by blast
    then have "\<exists>evs. ?m = Some (evs, UErr CANTUNIFY)"
      by (auto simp: test_unify_types_def bindW_def)
    then have "\<exists>evs. ?b = Some (evs, UErr CANTUNIFY)" by (auto simp: bindW_def)
    with False show ?thesis by (auto simp: okW_handleW)
  qed
  have "okW (match1_projs cfg vname env dps base Ts (p # projs) tail) ?r"
    using tl h by (auto simp: p strip_type_arg_res[OF assms(1)] foldrW_arity_guesses_ground[OF gb] match1_proj_0)
  moreover have "fin cfg ?r Q"
  proof (cases "base = res_type T")
    case True
    then have "Q (El_C (list_comb bv args1) env1 dps)" using Cons.prems p ma by auto
    with True ftl show ?thesis by (simp add: fin_Append fin_Single)
  qed (use ftl in simp)
  ultimately show ?case by blast
qed

text \<open>The elements of the sequence of copies that \<^const>\<open>new_dset\<close> maps:\<close>

definition mcopy :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow>
    elem \<Rightarrow> bool" where
  "mcopy ar V env Ts U v T x \<longleftrightarrow> (\<exists>u' env' dps' V'. x = El_C u' env' dps' \<and> tyinv ar V' env' dps' \<and>
    agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> has_type V' (rev Ts) u' U \<and>
    wf_cp ar (length Ts) u' \<and> below (maxidx env') u' \<and> (v, T) \<notin> reach env' (vps u'))"

lemma match1_fin:
  assumes inv: "tyinv ar V env dps" and bok: "binders_ok ar rb"
    and tgw: "\<forall>t\<in>set targs. wf_tm ar rb t" and tgty: "list_all2 (has_type V (map snd rb)) targs Ts"
    and wu: "wf_tm ar rb u" and tyu: "has_type V (map snd rb) u U" and nfU: "\<not> is_funT U"
    and vm: "snd v \<le> maxidx env"
  shows "\<exists>sq. okW (match1 cfg vname rb targs u env dps) sq \<and> fin cfg sq (mcopy ar V env Ts U v T)"
proof -
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from has_type_head_of[OF tyu] obtain T0 where tyh: "has_type V (map snd rb) (head_of u) T0" ..
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF tgty] by simp
  have gTs: "\<forall>A\<in>set Ts. ground ar A"
  proof
    fix A assume "A \<in> set Ts"
    then obtain i where i: "i < length Ts" "A = Ts ! i" by (auto simp: in_set_conv_nth)
    with tgty have "has_type V (map snd rb) (targs ! i) A" by (simp add: list_all2_conv_all_nth)
    moreover have "wf_tm ar rb (targs ! i)" using tgw i lTs by simp
    ultimately show "ground ar A" using ground_has_type[OF e bok] by blast
  qed
  have gU: "ground ar U" by (rule ground_has_type[OF e bok wu tyu])
  have rT0: "res_type T0 = U" using res_type_head(1)[OF tyu nfU tyh] .
  from res_type_head(2)[OF tyu nfU tyh] obtain As where T0: "T0 = foldr fun_type As U" by blast
  have aT0: "arg_types T0 = As" using arg_res_type_fun[OF nfU, of As] T0 by simp
  from make_projs_exact[OF lTs, of u targs] obtain projs where pr: "make_projs u targs Ts targs = returnW projs"
    by blast
  have pri: "\<forall>(bv, T, targ)\<in>set projs. \<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length targs \<and>
      targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T = Ts ! (length targs - 1 - nat_of_integer j)"
    using make_projs_idx[of u targs Ts targs projs] pr by simp
  text \<open>A copy with a closed head:\<close>
  have cp: "mcopy ar V env Ts U v T (El_C (list_comb hd0 args) env' dps)"
    if ma: "make_args vname Ts env Us = (env', args)" and gUs: "\<forall>A\<in>set Us. ground ar A"
      and tyhd: "\<And>V'. has_type V' (rev Ts) hd0 (foldr fun_type Us U)" and vhd: "vps hd0 = {}"
      and thd: "typs_ok ar hd0"
    for hd0 Us env' args
  proof -
    obtain V1 where c: "tyinv ar V1 env' dps" "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env'"
      "tenv env' = tenv env" "has_type V1 (rev Ts) (list_comb hd0 args) U"
      "wf_cp ar (length Ts) (list_comb hd0 args)" "below (maxidx env') (list_comb hd0 args)"
      "\<forall>y\<in>vps (list_comb hd0 args). maxidx env < snd (fst y)"
      by (rule make_args_copy_term[OF inv ma gTs gUs tyhd vhd thd])
    have "reach env' (vps (list_comb hd0 args)) = vps (list_comb hd0 args)"
      using reach_tenv[OF c(4)] reach_new[OF ei(4) c(8)] by simp
    then have "(v, T) \<notin> reach env' (vps (list_comb hd0 args))" using c(8) vm by fastforce
    with c show ?thesis unfolding mcopy_def by blast
  qed
  define imit where "imit = (case head_of u of
      Const _ _ \<Rightarrow> (case make_args vname Ts env As of (env', args) \<Rightarrow>
        S_Single (El_C (list_comb (head_of u) args) env' dps))
    | Free _ _ \<Rightarrow> (case make_args vname Ts env As of (env', args) \<Rightarrow>
        S_Single (El_C (list_comb (head_of u) args) env' dps))
    | _ \<Rightarrow> S_Empty)"
  have m1: "match1 cfg vname rb targs u env dps = match1_projs cfg vname env dps (res_type T0) Ts (rev projs) imit"
    using match1_unfold[OF e fastype_typed[OF e tyh] mapM_fastype[OF e tgty], of cfg vname dps] pr aT0
    by (cases "head_of u") (simp_all add: imit_def split: prod.split)
  have fi: "fin cfg imit (mcopy ar V env Ts U v T)"
  proof (cases "\<exists>a Tc. head_of u = Const a Tc \<or> head_of u = Free a Tc")
    case True
    then obtain a Tc where hu': "head_of u = Const a Tc \<or> head_of u = Free a Tc" by blast
    have Tc: "Tc = T0" using tyh hu' by (auto elim: has_type_elims)
    have whd: "wf_tm ar rb (head_of u)" using wu head_of_list_comb[of u] by (metis wf_tm_list_comb)
    have gT0: "ground ar T0" by (rule ground_has_type[OF e bok whd tyh])
    then have gAs: "\<forall>A\<in>set As. ground ar A" unfolding T0 by (induction As) simp_all
    have tyhd: "has_type V' (rev Ts) (head_of u) (foldr fun_type As U)" for V'
      using hu' Tc T0 tyh by (auto intro: has_type.Const has_type.Free elim: has_type_elims)
    have vt: "vps (head_of u) = {}" "typs_ok ar (head_of u)" using hu' whd by (auto simp: wf_tm_def)
    obtain env' args where ma: "make_args vname Ts env As = (env', args)"
      by (cases "make_args vname Ts env As")
    have "imit = S_Single (El_C (list_comb (head_of u) args) env' dps)"
      using hu' ma by (auto simp: imit_def)
    then show ?thesis using cp[OF ma gAs tyhd vt] by (simp add: fin_Single)
  next
    case False
    then have "imit = S_Empty" by (cases "head_of u") (auto simp: imit_def)
    then show ?thesis by simp
  qed
  have "\<exists>sq. okW (match1_projs cfg vname env dps (res_type T0) Ts (rev projs) imit) sq \<and>
      fin cfg sq (mcopy ar V env Ts U v T)"
  proof (rule match1_projs_fin[OF e _ fi])
    show "ground ar (res_type T0)" using rT0 gU by simp
    show "\<forall>(bv, T', targ)\<in>set (rev projs). ground ar T' \<and> (res_type T' = res_type T0 \<longrightarrow>
        (\<forall>env' args. make_args vname Ts env (arg_types T') = (env', args) \<longrightarrow>
          mcopy ar V env Ts U v T (El_C (list_comb bv args) env' dps)))"
    proof (clarify)
      fix bv T' targ assume "(bv, T', targ) \<in> set (rev projs)"
      then obtain j where j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length targs"
        "T' = Ts ! (length targs - 1 - nat_of_integer j)"
        using pri by fastforce
      have gT': "ground ar T'" using gTs j(3,4) lTs by simp
      moreover have "mcopy ar V env Ts U v T (El_C (list_comb bv args) env' dps)"
        if rT: "res_type T' = res_type T0" and ma: "make_args vname Ts env (arg_types T') = (env', args)"
        for env' args
      proof (rule cp[OF ma])
        show "\<forall>A\<in>set (arg_types T'). ground ar A"
          using strip_type_ground(1)[OF e gT', of "arg_types T'" "res_type T'"]
          by (simp add: strip_type_arg_res[OF e])
        have T'_eq: "T' = foldr fun_type (arg_types T') U" using arg_res_type[of T'] rT rT0 by simp
        have "rev Ts ! nat_of_integer j = T'" using j(3,4) lTs by (simp add: rev_nth)
        then show "has_type V' (rev Ts) bv (foldr fun_type (arg_types T') U)" for V'
          using j(1-3) lTs T'_eq by (simp add: has_type_Bound_iff)
        show "vps bv = {}" "typs_ok ar bv" using j(1) by simp_all
      qed
      ultimately show "ground ar T' \<and> (res_type T' = res_type T0 \<longrightarrow>
        (\<forall>env' args. make_args vname Ts env (arg_types T') = (env', args) \<longrightarrow>
          mcopy ar V env Ts U v T (El_C (list_comb bv args) env' dps)))" by blast
    qed
  qed
  then show ?thesis using m1 by simp
qed

subsection \<open>Finiteness of \<open>MATCH\<close>\<close>

lemma dd_free: "vars t \<inter> F = {} \<Longrightarrow> dd F b t"
  by (induction t arbitrary: b) auto

lemma below_disj: "below m t \<Longrightarrow> vars t \<inter> {x. m < snd x} = {}"
  by (auto simp: below_def)

text \<open>
  The branch of \<^const>\<open>MATCH\<close> that copies the rigid side: the new variables are dead if one of
  the arguments of the flexible side is not a bound variable, and occur at heads only otherwise.
\<close>

lemma mc_mcopy:
  assumes inv: "tyinv ar V env dps" and bok: "binders_ok ar rb"
    and tgw: "\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t"
    and tgty: "list_all2 (has_type V (map snd rb)) targs Ts"
    and wu: "wf_tm ar rb u" and tyu: "has_type V (map snd rb) u U" and bu: "below (maxidx env) u"
    and nfU: "\<not> is_funT U" and hr: "is_rigid (head_of u)" and vm: "snd v \<le> maxidx env"
    and nD: "(v, T) \<notin> reach env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps)"
  shows "\<exists>sq. okW (mc cfg (fst v) rb targs u env dps) sq \<and> fin cfg sq (mcopy ar V env Ts U v T)"
proof -
  define m0 where "m0 = maxidx env"
  define F where "F = {x::indexname. m0 < snd x}"
  define D0 where "D0 = vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
  define S0 where "S0 = {y \<in> reach env D0. snd (fst y) \<le> m0}"
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  obtain Fd Ft where rg: "Fd = F \<and> Ft = {} \<or> Fd = {} \<and> Ft = F"
    and tk: "(Fd \<noteq> {} \<longrightarrow> (\<exists>t\<in>set targs. \<not> is_Bound t)) \<and> (Ft \<noteq> {} \<longrightarrow> (\<forall>t\<in>set targs. is_Bound t))"
  proof (cases "\<forall>t\<in>set targs. is_Bound t")
    case True
    then show ?thesis using that[of "{}" F] by simp
  next
    case False
    then show ?thesis using that[of F "{}"] by simp
  qed
  have fD0: "finite D0"
  proof -
    have "finite (vps_dp dq)" for dq by (cases dq) simp
    then show ?thesis by (simp add: D0_def)
  qed
  interpret mfin ar cfg "fst v" m0 S0 Fd Ft
  proof
    show "finite S0" using finite_reach[OF fD0, of env] by (simp add: S0_def)
    show "snd (fst y) \<le> m0" if "y \<in> S0" for y using that by (simp add: S0_def)
    show "Fd = {x. m0 < snd x} \<and> Ft = {} \<or> Fd = {} \<and> Ft = {x. m0 < snd x}" using rg by (simp add: F_def)
  qed
  have FdF: "Fd \<subseteq> F" and FtF: "Ft \<subseteq> F" using rg by auto
  have shb: "sh t" if "below (maxidx env) t" for t
    using below_disj[OF that] FdF FtF by (auto simp: sh_def m0_def F_def intro!: dd_free)
  have gsb: "gs Ft t" if "below (maxidx env) t" for t
    using below_disj[OF that] FtF by (auto simp: m0_def F_def intro!: gs_free)
  have cp: "cpre V env dps rb targs Ts"
    unfolding cpre_def
  proof (intro conjI ballI inv bok tgty)
    show "wf_tm ar rb t" "below (maxidx env) t" "sh t" if "t \<in> set targs" for t using tgw that shb by auto
    show "vgood Fd Ft env"
      unfolding vgood_def
    proof (intro allI impI)
      fix x U w assume "vt_lookup (tenv env) x = Some (U, w)"
      from fresh_envD[OF ei(4) this] have "snd x \<le> maxidx env" "below (maxidx env) w" by simp_all
      then show "x \<notin> Fd \<and> dead Fd w \<and> vars w \<inter> Ft = {}" using shb FdF by (auto simp: sh_def F_def m0_def)
    qed
    show "pgood Fd Ft dp" if "dp \<in> set dps" for dp
    proof -
      obtain rb' t' u' where dp: "dp = (rb', t', u')" by (cases dp)
      from tyinvD(2)[OF inv that] have "below (maxidx env) t'" "below (maxidx env) u'"
        by (simp_all add: dp dp_below_def)
      then show ?thesis using shb gsb by (simp add: pgood_def dp sh_def)
    qed
    show "tok targs" using tk by (simp add: tok_def)
    show "m0 \<le> maxidx env" by (simp add: m0_def)
  qed
  have up: "upre V env rb u U" using wu tyu bu shb by (simp add: upre_def)
  have hA: "\<not> is_Abs (head_of u)" using hr by (auto simp: is_rigid_def)
  have nAu: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
  have hnu: "hnf u" using hA by (cases u) auto
  have hlu: "hlong V (map snd rb) u U" by (rule hlong.base[OF tyu nAu nfU])
  have od: "oldin env D0" unfolding oldin_def by (simp add: S0_def)
  from mc_fin[OF cp up hnu hlu od[unfolded D0_def]] obtain sq where
    sq: "okW (mc cfg (fst v) rb targs u env dps) sq" "fin cfg sq (EC V env D0 Ts U)"
    unfolding D0_def by blast
  have "fin cfg sq (mcopy ar V env Ts U v T)"
  proof (rule fin_mono[OF sq(2)])
    fix x assume "EC V env D0 Ts U x"
    then obtain u' env' dps' V' NV where x: "x = El_C u' env' dps'"
      and cr: "cres V env D0 V' env' dps' NV" and cu: "cpy V' env' NV Ts u' U"
      by (auto simp: EC_def)
    note s = tsextD[OF conjunct1[OF cr[unfolded cres_def]]]
    have vu': "vps u' \<subseteq> NV" using cu by (simp add: cpy_def)
    have rNV: "reach env NV = NV" using reach_new[OF ei(4)] s(6) by blast
    have "reach env' (vps u') \<subseteq> reach env (vps u' \<union> D0) \<union> NV" by (rule s(7))
    also have "\<dots> \<subseteq> reach env D0 \<union> NV"
      using reach_subset[OF vu', of env] rNV by (auto simp: reach_Un)
    finally have "(v, T) \<notin> reach env' (vps u')" using nD s(6)[of "(v, T)"] vm by (auto simp: D0_def)
    then show "mcopy ar V env Ts U v T x" using x s(1-3) cu by (auto simp: mcopy_def cpy_def)
  qed
  with sq(1) show ?thesis by blast
qed

text \<open>
  \<^const>\<open>MATCH\<close> on a flex-rigid pair yields a finite sequence of states in the typing
  invariant.
\<close>

theorem MATCH_fin:
  assumes inv: "tyinv ar V env (dp # dps)" and frs: "fr_shape V dp" and hun: "heads_unb env dp"
  shows "\<exists>ms. okW (MATCH cfg env dp dps) ms \<and>
    fin cfg ms (\<lambda>x. \<exists>env' dps' V'. x = El_E env' dps' \<and> tyinv ar V' env' dps')"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from frs obtain B where nfB: "\<not> is_funT B" and tyt: "has_type V (map snd rb) t B"
    and tyu: "has_type V (map snd rb) u B" and hvt: "is_Var (head_of t)" and hru: "is_rigid (head_of u)"
    by (auto simp: fr_shape_def dp)
  from hvt obtain v T where ht: "head_of t = Var v T" by (cases "head_of t") auto
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from tyinvD(2)[OF inv, of dp] have wfd: "wf_dp ar (rb, t, u)" and bt: "below (maxidx env) t"
    and bu: "below (maxidx env) u"
    by (auto simp: dp dp_below_def)
  define targs where "targs = snd (strip_comb t)"
  have sc: "strip_comb t = (Var v T, targs)" using fst_strip_comb[of t] ht by (simp add: targs_def prod_eq_iff)
  have t_eq: "t = list_comb (Var v T) targs" using head_of_list_comb[of t] ht by (simp add: targs_def)
  have tyh: "has_type V (map snd rb) (Var v T) T" and Vv: "V v = T"
    using has_type_head_of[OF tyt] ht by (auto elim: has_type_elims intro: has_type.Var)
  from res_type_head(2)[OF tyt nfB tyh[folded ht]] obtain Ts where T: "T = foldr fun_type Ts B"
    and tgty: "list_all2 (has_type V (map snd rb)) targs Ts" by (auto simp: targs_def)
  have aT: "arg_types T = Ts" using arg_res_type_fun[OF nfB, of Ts] T by simp
  have bT: "binder_types env T = return Ts" using binder_types_arg[OF e] aT by simp
  have bok: "binders_ok ar rb" and wu: "wf_tm ar rb u" using wfd by simp_all
  have wt: "wf_tm ar rb (list_comb (Var v T) targs)" using wfd t_eq by simp
  have whd: "wf_tm ar rb (Var v T)" and tgw: "\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t"
    using wt bt t_eq by (auto simp: wf_tm_list_comb below_list_comb)
  have gT: "ground ar T" by (rule ground_has_type[OF e bok whd tyh])
  have gTs: "\<forall>A\<in>set Ts. ground ar A" using gT unfolding T by (induction Ts) simp_all
  have vm: "snd v \<le> maxidx env" using below_vps[OF bt vps_head_of[OF ht]] by simp
  let ?ts = "u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)"
  have vty: "\<forall>t\<in>set ?ts. vtyped V t"
  proof -
    have "vtyped V t'" if "t' \<in> set targs" for t'
      using that tgty by (metis has_type_vtyped in_set_conv_nth list_all2_conv_all_nth)
    moreover have "vtyped V t' \<and> vtyped V u'" if "(rb', t', u') \<in> set dps" for rb' t' u'
      using tyinvD(2)[OF inv, of "(rb', t', u')"] that by (auto intro: has_type_vtyped simp: dp_typed_def)
    ultimately show ?thesis using has_type_vtyped[OF tyu] by auto
  qed
  from occurs_terms_term[OF e ei(3) vty] obtain occ where oc: "occurs_terms env v ?ts = return occ" by blast
  have okc: "ok (occurs_terms env v ?ts) occ" using oc by (simp add: return_def)
  have vl: "vps_list ?ts = vps u \<union> vps_list targs \<union> vps_dps dps"
    unfolding vps_list_dpairs[symmetric] by auto
  have occ: "occ \<longleftrightarrow> occ_in env v (vps u \<union> vps_list targs \<union> vps_dps dps)"
    using occurs_terms_correct[OF e ei(1) okc] unfolding vl .
  have M: "MATCH cfg env dp dps = do {
      s \<leftarrow> (if occ then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps) else mc cfg (fst v) rb targs u env dps);
      returnW (S_MapNewDset (v, T) Ts s)}"
  proof -
    have "MATCH cfg env (rb, t, u) dps = match_pair cfg env (rb, t, u) dps"
    proof (rule MATCH_ground[OF e wfd])
      fix rb' t' u' v' T' targs' Ts'
      assume "(rb, t, u) = (rb', t', u')" "strip_comb t' = (Var v' T', targs')"
        "binder_types env T' = return Ts'"
      with sc bT list_all2_lengthD[OF tgty] show "length Ts' = length targs'" by (auto simp: return_def)
    qed
    then show ?thesis by (simp add: dp match_pair_def sc bT oc liftM_return)
  qed
  obtain sq where sq: "okW (if occ then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps)
      else mc cfg (fst v) rb targs u env dps) sq"
    and fs: "fin cfg sq (mcopy ar V env Ts B v T)"
  proof (cases occ)
    case True
    have inv1: "tyinv ar V env ((rb, t, u) # dps)" using inv by (simp add: dp)
    from match1_fin[OF inv1 bok _ tgty wu tyu nfB vm, of cfg "fst v"] tgw True that show thesis by auto
  next
    case False
    have inv0: "tyinv ar V env dps" using inv by (simp add: tyinv_def)
    have nD: "(v, T) \<notin> reach env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps)"
      using False occ by (auto simp: occ_in_def)
    from mc_mcopy[OF inv0 bok tgw tgty wu tyu bu nfB hru vm nD, of cfg] False that show thesis by auto
  qed
  have "fin cfg (S_MapNewDset (v, T) Ts sq) (\<lambda>x. \<exists>env' dps' V'. x = El_E env' dps' \<and> tyinv ar V' env' dps')"
  proof (rule fin_MapNewDset, rule fin_mono[OF fs])
    fix x assume "mcopy ar V env Ts B v T x"
    then obtain u' env' dps' V' where x: "x = El_C u' env' dps'" and c: "tyinv ar V' env' dps'"
      "agreeV (maxidx env) V V'" "maxidx env \<le> maxidx env'" "has_type V' (rev Ts) u' B"
      "wf_cp ar (length Ts) u'" "below (maxidx env') u'" "(v, T) \<notin> reach env' (vps u')"
      unfolding mcopy_def by blast
    have Vv': "V' v = T" using agreeV_D[OF c(2) vm] Vv by simp
    have vm': "snd v \<le> maxidx env'" using vm c(3) by simp
    from new_dset_term[OF c(1,4,5,6) T Vv' gT gTs vm' c(7)] x
    show "\<exists>u env dps y. x = El_C u env dps \<and> okW (new_dset (v, T) Ts u env dps) y \<and>
        (\<exists>env' dps' V'. y = El_E env' dps' \<and> tyinv ar V' env' dps')"
      by blast
  qed
  moreover have "okW (MATCH cfg env dp dps) (S_MapNewDset (v, T) Ts sq)" using M sq by simp
  ultimately show ?thesis by blast
qed

theorem match_fin_holds: "match_fin cfg ar"
  unfolding match_fin_def cuok_def using MATCH_fin by blast

subsection \<open>Termination of the enumeration\<close>

text \<open>
  Pulling the sequence of unifiers of a well-typed problem terminates: it yields finitely many
  unifiers and then the end of the sequence, without an exception, for every configuration.
\<close>

theorem hounifiers_fin:
  "tyinv ar V env (map (\<lambda>(t, u). (rb, t, u)) tus) \<Longrightarrow>
    fin cfg (hounifiers rb env tus) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> rres ar env' tps)"
  by (rule hounifiers_fin_match[OF match_fin_holds])

theorem unifiers_fin:
  assumes "tyinv ar V env (dps_of tus)"
  obtains s where "unifiers alg env tus = Some (Ok s)"
    "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> rres ar env' tps)"
  by (rule unifiers_fin_match[OF match_fin_holds assms])

end
