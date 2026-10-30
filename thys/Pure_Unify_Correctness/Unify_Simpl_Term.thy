section \<open>Termination of the Simplification Phase\<close>

theory Unify_Simpl_Term
  imports Unify_Unifiers
begin

text \<open>
  \<^const>\<open>SIMPL0\<close> and \<^const>\<open>SIMPL\<close> terminate on every well-typed problem with an acyclic
  environment, solvable or not: they return a state or raise \<open>CANTUNIFY\<close>. This is the
  counterpart of the completeness of the simplification phase (theory \<open>Unify_Simpl_Complete\<close>)
  without a solution. The measure of a pair is lexicographic: the number of unbound
  variables that are reachable from it, and the size \<^const>\<open>dsz\<close> of its instance under a
  solution of the environment, such as the canonical one (@{thm [source] env_solution}). An
  assignment binds a reachable unbound variable; otherwise the environment, and hence its
  solutions, do not change.
\<close>

subsection \<open>Results\<close>

text \<open>A computation succeeds with a result satisfying \<open>P\<close> or fails with \<open>CANTUNIFY\<close>:\<close>

context csig
begin

definition cuok :: "'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "cuok m P \<longleftrightarrow> (\<exists>evs. m = Some (evs, UErr CANTUNIFY)) \<or> (\<exists>x. okW m x \<and> P x)"

lemma cuok_mono: "cuok m P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> cuok m Q"
  by (auto simp: cuok_def)

lemma cuok_raiseW[simp]: "cuok (raiseW CANTUNIFY) P"
  by (simp add: cuok_def raiseW_def)

lemma cuok_returnW[simp]: "cuok (returnW x) P \<longleftrightarrow> P x"
  by (auto simp: cuok_def returnW_def)

lemma cuok_bindW:
  "cuok m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> cuok (f x) Q) \<Longrightarrow> cuok (bindW m f) Q"
  unfolding cuok_def by (auto simp: bindW_def split: option.splits ures.splits)


subsection \<open>Environments with the same bindings\<close>

definition same_lk :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "same_lk env env' \<longleftrightarrow> (\<forall>x. vt_lookup (tenv env') x = vt_lookup (tenv env) x)"

lemma same_lk_lk: "same_lk env env' \<Longrightarrow> lk env' = lk env"
  by (auto simp: same_lk_def lk_def fun_eq_iff)

lemma same_lk_reach: "same_lk env env' \<Longrightarrow> reach env' = reach env"
  by (auto simp: reach_def dep_def same_lk_lk fun_eq_iff)

lemma same_lk_unb: "same_lk env env' \<Longrightarrow> unb env' = unb env"
  by (auto simp: unb_def same_lk_reach same_lk_lk fun_eq_iff)

lemma same_lk_sat: "same_lk env env' \<Longrightarrow> sat \<sigma> env' \<longleftrightarrow> sat \<sigma> env"
  by (simp add: same_lk_def sat_def)

lemma same_lk_solution: "same_lk env env' \<Longrightarrow> solution V \<tau>' \<sigma> env' \<longleftrightarrow> solution V \<tau>' \<sigma> env"
  by (simp add: solution_def same_lk_sat)

lemma same_lk_refl[simp]: "same_lk env env"
  by (simp add: same_lk_def)

text \<open>
  A step from \<open>env\<close> to \<open>env'\<close> that binds only variables reachable from \<open>D\<close> and makes only
  variables reachable that were reachable from \<open>D\<close>:
\<close>

definition tstep :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "tstep V D env env' \<longleftrightarrow> extends env' env \<and> maxidx env' = maxidx env \<and>
    (\<forall>X. reach env' X \<subseteq> reach env (X \<union> D)) \<and>
    (\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> (x, V x) \<in> reach env D)"

lemma tstepD:
  assumes "tstep V D env env'"
  shows "extends env' env" "maxidx env' = maxidx env" "reach env' X \<subseteq> reach env (X \<union> D)"
    "vt_lookup (tenv env') x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> (x, V x) \<in> reach env D"
  using assms unfolding tstep_def by blast+

lemma tstep_refl[simp]: "tstep V D env env"
  unfolding tstep_def by (auto simp: reach_Un)

lemma tstep_trans:
  assumes "tstep V D1 env env1" "tstep V D2 env1 env2"
  shows "tstep V (D1 \<union> D2) env env2"
  unfolding tstep_def
proof (intro conjI allI impI)
  show "extends env2 env" using assms by (auto simp: tstep_def intro: extends_trans)
  show "maxidx env2 = maxidx env" using assms by (simp add: tstep_def)
  fix X
  have "reach env2 X \<subseteq> reach env1 (X \<union> D2)" using assms(2) by (simp add: tstep_def)
  also have "\<dots> \<subseteq> reach env (X \<union> D2 \<union> D1)" using assms(1) by (simp add: tstep_def)
  finally show "reach env2 X \<subseteq> reach env (X \<union> (D1 \<union> D2))" by (simp add: Un_ac)
next
  fix x assume b: "vt_lookup (tenv env2) x \<noteq> None" and u: "vt_lookup (tenv env) x = None"
  show "(x, V x) \<in> reach env (D1 \<union> D2)"
  proof (cases "vt_lookup (tenv env1) x = None")
    case True
    with tstepD(4)[OF assms(2) b] have "(x, V x) \<in> reach env1 D2" by simp
    also have "\<dots> \<subseteq> reach env (D2 \<union> D1)" using assms(1) by (simp add: tstep_def)
    finally show ?thesis by (simp add: Un_ac)
  next
    case False
    with tstepD(4)[OF assms(1) _ u] have "(x, V x) \<in> reach env D1" by simp
    then show ?thesis using reach_subset[of D1 "D1 \<union> D2" env] by blast
  qed
qed

lemma tstep_mono: "tstep V D env env' \<Longrightarrow> D \<subseteq> reach env D' \<Longrightarrow> tstep V D' env env'"
proof -
  assume s: "tstep V D env env'" and D: "D \<subseteq> reach env D'"
  have m: "reach env (X \<union> D) \<subseteq> reach env (X \<union> D')" for X
    using D by (intro reach_mono) (auto intro: set_mp[OF reach_incl] set_mp[OF reach_subset])
  have m': "reach env D \<subseteq> reach env D'" using D by (rule reach_mono)
  from s m m' show ?thesis by (fastforce simp: tstep_def)
qed

text \<open>
  After a step from \<open>env\<close>, the unbound variables reachable from variables reachable from \<open>D\<close>
  were unbound and reachable from \<open>D\<close> before, and if the step bound a variable, there are fewer.
\<close>

lemma tstep_unb:
  assumes s: "tstep V D env env'" and Y: "Y \<subseteq> reach env D"
  shows "unb env' Y \<subseteq> unb env D"
proof
  fix y assume y: "y \<in> unb env' Y"
  then have "y \<in> reach env (Y \<union> D)" using s by (auto simp: unb_def tstep_def)
  also have "\<dots> = reach env D" using reach_absorb[OF Y, of "{}"] by simp
  finally have "y \<in> reach env D" .
  moreover have "lk env (fst y) (snd y) = None"
    using y extends_lk[of env' env] s by (cases "lk env (fst y) (snd y)") (auto simp: unb_def tstep_def)
  ultimately show "y \<in> unb env D" by (simp add: unb_def)
qed

lemma tstep_unb_less:
  assumes s: "tstep V D env env'" and Y: "Y \<subseteq> reach env D" and fin: "finite D"
    and ty: "env_typed V env'" and new: "\<not> same_lk env env'"
  shows "card (unb env' Y) < card (unb env D)"
proof -
  from new obtain x where x: "vt_lookup (tenv env') x \<noteq> vt_lookup (tenv env) x"
    by (auto simp: same_lk_def)
  have u: "vt_lookup (tenv env) x = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env) x \<noteq> None"
    then obtain b where "vt_lookup (tenv env) x = Some b" by blast
    with tstepD(1)[OF s] x show False unfolding extends_def by metis
  qed
  with x obtain U w where b: "vt_lookup (tenv env') x = Some (U, w)" by auto
  have r: "(x, V x) \<in> reach env D" using tstepD(4)[OF s _ u] b by simp
  have "(x, V x) \<in> unb env D" using r u by (simp add: unb_def lk_def)
  moreover have "(x, V x) \<notin> unb env' Y"
    using env_typedD[OF ty b] b by (simp add: unb_def lk_def)
  moreover have "finite (unb env D)"
    by (rule finite_subset[OF _ finite_reach[OF fin]]) (auto simp: unb_def)
  ultimately show ?thesis using tstep_unb[OF s Y] by (intro psubset_card_mono) blast+
qed


subsection \<open>Head normalization and assignments\<close>

lemma update_typed:
  assumes fr: "fresh_env env" and ety: "env_typed V env" and upd: "ok (update (F, T) t env) env'"
    and ty: "V F = T" "has_type V [] t T" and Fm: "snd F \<le> maxidx env" and tm: "below (maxidx env) t"
  shows "env_typed V env'" "fresh_env env'" "maxidx env' = maxidx env"
proof -
  note u = ok_update[OF upd]
  show "env_typed V env'"
    unfolding env_typed_def u(2)
  proof (intro allI impI)
    fix x U u' assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u')"
    then show "V x = U \<and> has_type V [] u' U"
      using env_typedD[OF ety] ty by (auto split: if_splits)
  qed
  show "fresh_env env'"
    unfolding fresh_env_def u(2) u(4)
  proof (intro allI impI)
    fix x U u' assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u')"
    then show "snd x \<le> maxidx env \<and> below (maxidx env) u'"
      using fresh_envD[OF fr] Fm tm by (auto split: if_splits)
  qed
  show "maxidx env' = maxidx env" by (rule u(4))
qed

text \<open>The counterpart of @{thm [source] head_norm_dpair_complete} without a solution:\<close>

lemma head_norm_dpair_term:
  assumes inv: "tyinv ar V env [(rb, t, u)]"
  obtains rb' t' u' T where
    "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    "tyinv ar V env [(rb', t', u')]"
    "has_type V (map snd rb) t T" "map snd rb' = rev (arg_types T) @ map snd rb"
    "has_type V (map snd rb') t' (res_type T)" "has_type V (map snd rb') u' (res_type T)"
    "\<not> is_Abs t'" "\<not> is_Abs u'" "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    "vps t' \<subseteq> reach env (vps t)" "vps u' \<subseteq> reach env (vps u)"
    "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'"
proof -
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  from tyinvD(2)[OF inv, of "(rb, t, u)"] obtain T where wfd: "wf_dp ar (rb, t, u)"
    and tyt: "has_type V (map snd rb) t T" and tyu: "has_type V (map snd rb) u T"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from head_norm_term[OF ei(1,2,3) tyt] obtain t1 where ht: "head_norm env t = Some (Ok t1)" by blast
  from head_norm_term[OF ei(1,2,3) tyu] obtain u1 where hu: "head_norm env u = Some (Ok u1)" by blast
  have tyt1: "has_type V (map snd rb) t1 T" by (rule head_norm_typed[OF ht refl ei(2,3) tyt])
  have tyu1: "has_type V (map snd rb) u1 T" by (rule head_norm_typed[OF hu refl ei(2,3) tyu])
  from eta_norm_term[OF e tyt1] obtain t2 where et: "eta_norm env rb t1 = Some (Ok t2)" by blast
  from eta_norm_term[OF e tyu1] obtain u2 where eu: "eta_norm env rb u1 = Some (Ok u2)" by blast
  have hlt: "hlong V (map snd rb) t2 T" by (rule eta_norm_hlong[OF e tyt1]) (simp add: et)
  have hlu: "hlong V (map snd rb) u2 T" by (rule eta_norm_hlong[OF e tyu1]) (simp add: eu)
  from new_dpair_hlong[OF hlt hlu, of alg env] obtain rb' where
    nd: "new_dpair alg rb t2 u2 env = returnW ((rb', strip_abs_body t2, strip_abs_body u2), env)"
    and rb': "map snd rb' = rev (arg_types T) @ map snd rb"
    and ty': "has_type V (map snd rb') (strip_abs_body t2) (res_type T)"
      "has_type V (map snd rb') (strip_abs_body u2) (res_type T)"
    and nA: "\<not> is_Abs (strip_abs_body t2)" "\<not> is_Abs (strip_abs_body u2)"
    by blast
  define t' where "t' = strip_abs_body t2"
  define u' where "u' = strip_abs_body u2"
  have hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    by (simp add: head_norm_dpair_def ht hu et eu nd t'_def u'_def)
  note snd = head_norm_dpair_sound[OF hd ei(2) wfd]
  note shp = head_norm_dpair_shape[OF hd ei(2) wfd]
  note est = eta_norm_shape[OF _ e, of rb t1 t2] eta_norm_shape[OF _ e, of rb u1 u2]
  have vt: "vps t' = vps t1" "vps u' = vps u1" using est et eu by (simp_all add: t'_def u'_def)
  have rt: "vps t1 \<subseteq> reach env (vps t)" "vps u1 \<subseteq> reach env (vps u)"
    using hn_vps[OF head_norm_hn[OF ht e refl]] hn_vps[OF head_norm_hn[OF hu e refl]] by simp_all
  have bt: "below (maxidx env) t'" "below (maxidx env) u'"
    using below_head_norm[OF ht refl ei(2,4) bl(1)] below_head_norm[OF hu refl ei(2,4) bl(2)] vt
    by (simp_all add: below_vps_iff)
  have "tyinv ar V env [(rb', t', u')]"
    using tyinvD(1)[OF inv] snd(2) ty' bt by (auto simp: tyinv_def t'_def u'_def)
  moreover have "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    using shp(3,4) nA by (simp_all add: hnf_nonAbs t'_def u'_def)
  moreover have "vt_lookup (tenv env) F = None" if "head_of t' = Var F U" for F U
  proof -
    have "head_rel (head_of (strip_abs_body t1)) (head_of t')"
      using est(1) et by (simp add: t'_def)
    with that have "head_of (strip_abs_body t1) = Var F U" unfolding head_rel_def by blast
    from head_norm_body_head_unbound[OF ht refl e this] show ?thesis .
  qed
  moreover have "vt_lookup (tenv env) F = None" if "head_of u' = Var F U" for F U
  proof -
    have "head_rel (head_of (strip_abs_body u1)) (head_of u')"
      using est(2) eu by (simp add: u'_def)
    with that have "head_of (strip_abs_body u1) = Var F U" unfolding head_rel_def by blast
    from head_norm_body_head_unbound[OF hu refl e this] show ?thesis .
  qed
  ultimately show ?thesis
    using that[OF hd _ tyt rb' ty'[folded t'_def u'_def] nA[folded t'_def u'_def]] vt rt snd(3)
    by blast
qed

text \<open>The counterpart of @{thm [source] assignment_complete} without a solution:\<close>

lemma assignment_term:
  assumes inv: "tyinv ar V env [(rb, t, u)]"
    and ty: "has_type V (map snd rb) t B" "has_type V (map snd rb) u B" "\<not> is_funT B"
    and xu: "\<And>x T. head_of t = Var x T \<Longrightarrow> vt_lookup (tenv env) x = None"
  shows "(\<exists>evs. assignment alg rb t u env = Some (evs, UErr ASSIGN)) \<or>
    (\<exists>evs. assignment alg rb t u env = Some (evs, UErr CANTUNIFY)) \<or>
    (\<exists>env'. okW (assignment alg rb t u env) env' \<and> env_inv ar V env' \<and>
      tstep V (vps t \<union> vps u) env env')"
proof -
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  from tyinvD(2)[OF inv, of "(rb, t, u)"] have wfd: "wf_dp ar (rb, t, u)"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  consider "get_eta_var rb 0 t = raiseW ASSIGN" | v T where "get_eta_var rb 0 t = returnW (v, T)"
    using get_eta_var_cases by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: assignment_def bindW_def raiseW_def)
  next
    case 2
    then have gev: "okW (get_eta_var rb 0 t) (v, T)" by (simp add: returnW_def)
    from get_eta_var_type[OF gev _ ty(1)] have T: "T = foldr fun_type (rev (map snd rb)) B"
      and Vv: "V v = T" and ht: "head_of t = Var v T"
      by (simp_all add: rev_nth)
    have vu: "vt_lookup (tenv env) v = None" using xu[OF ht] .
    from rigid_occurs_term_terminates[OF ei(1,2,3) has_type_vtyped[OF ty(2)], of v] obtain oc
      where oc: "rigid_occurs_term env v u = return oc" by blast
    show ?thesis
    proof (cases oc)
      case Rigid
      then show ?thesis using 2 oc by (simp add: assignment_def returnW_def return_def raiseW_def bindW_def)
    next
      case Nonrigid
      then show ?thesis using 2 oc by (simp add: assignment_def returnW_def return_def raiseW_def bindW_def)
    next
      case NoOcc
      have bt: "body_type env T = return B" using T body_type_base[OF e ty(3)] by simp
      have ft: "fastype env rb u = return B" by (rule fastype_typed[OF e ty(2)])
      from update_unbound_ok[OF vu, of T "rlist_abs rb u"] obtain env' where
        upd: "update (v, T) (rlist_abs rb u) env = Some (Ok env')" by blast
      have ok: "okW (assignment alg rb t u env) env'"
        using 2 oc NoOcc bt ft upd by (simp add: assignment_def cunify_types_same return_def)
      have tyr: "has_type V [] (rlist_abs rb u) T"
        using has_type_rlist_abs[of V rb "[]" u B] ty(2) T by simp
      have Fm: "snd v \<le> maxidx env" using below_vps[OF bl(1) vps_head_of[OF ht]] by simp
      have tm: "below (maxidx env) (rlist_abs rb u)" using bl(2) by (simp add: below_vps_iff vps_rlist_abs)
      have upd': "ok (update (v, T) (rlist_abs rb u) env) env'" using upd by simp
      note ut = update_typed[OF ei(4) ei(3) upd' Vv tyr Fm tm]
      have "acyc env'" by (rule assignment_acyc[OF ok ei(2) wfd ei(1)])
      moreover have "wf_env ar env'" by (rule assignment_wf[OF ok ei(2) wfd])
      ultimately have inv': "env_inv ar V env'" using ut by (simp add: env_inv_def)
      have "tstep V (vps t \<union> vps u) env env'"
        unfolding tstep_def
      proof (intro conjI allI impI)
        show "extends env' env" by (rule ok_update_extends[OF upd'])
        show "maxidx env' = maxidx env" by (rule ut(3))
        fix X
        have "reach env' X \<subseteq> reach env (X \<union> vps u)"
          using reach_update[OF upd'] by (simp add: vps_rlist_abs)
        also have "\<dots> \<subseteq> reach env (X \<union> (vps t \<union> vps u))" by (rule reach_subset) auto
        finally show "reach env' X \<subseteq> reach env (X \<union> (vps t \<union> vps u))" .
      next
        fix x assume "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None"
        then have "x = v" using ok_update(2)[OF upd'] by (auto split: if_splits)
        then have "(x, V x) \<in> vps t" using vps_head_of[OF ht] Vv by simp
        then show "(x, V x) \<in> reach env (vps t \<union> vps u)" using reach_incl by blast
      qed
      with ok inv' show ?thesis by blast
    qed
  qed
qed

subsection \<open>Composing simplification steps\<close>

text \<open>The counterpart of \<^const>\<open>sres\<close> without a solution:\<close>

definition tsres :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> dpair list \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "tsres ar V dps st st' \<longleftrightarrow> (case (st, st') of ((env, ffs, frs), (env', ffs', frs')) \<Rightarrow>
    \<exists>ffn frn. ffs' = ffn @ ffs \<and> frs' = frn @ frs \<and> tyinv ar V env' (ffn @ frn) \<and>
      tstep V (vps_dps dps) env env' \<and> vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps) \<and>
      (\<forall>dp\<in>set ffn. ff_shape V dp) \<and> (\<forall>dp\<in>set frn. fr_shape V dp) \<and>
      (\<forall>dp\<in>set (ffn @ frn). heads_unb env dp))"

lemma tsresD:
  assumes "tsres ar V dps (env, ffs, frs) st'"
  obtains env' ffn frn where "st' = (env', ffn @ ffs, frn @ frs)" "tyinv ar V env' (ffn @ frn)"
    "tstep V (vps_dps dps) env env'" "vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
  using assms by (cases st') (auto simp: tsres_def)

lemma tsresI:
  assumes "tyinv ar V env' (ffn @ frn)" "tstep V (vps_dps dps) env env'"
    "vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
  shows "tsres ar V dps (env, ffs, frs) (env', ffn @ ffs, frn @ frs)"
  using assms by (auto simp: tsres_def)

lemma tyinv_Nil: "tyinv ar V env dps \<Longrightarrow> tyinv ar V env []"
  by (simp add: tyinv_def)

lemma tyinv_same: "tyinv ar V env dps \<Longrightarrow> env_inv ar V env' \<Longrightarrow> maxidx env' = maxidx env \<Longrightarrow> tyinv ar V env' dps"
  by (simp add: tyinv_def)

lemma tsres_refl: "tyinv ar V env [] \<Longrightarrow> tsres ar V dps (env, ffs, frs) (env, ffs, frs)"
  using tsresI[of ar V env "[]" "[]" dps env ffs frs] by simp

lemma tsres_trans:
  assumes "tsres ar V dps1 (env, ffs, frs) st1" "tsres ar V dps2 st1 st2"
  shows "tsres ar V (dps1 @ dps2) (env, ffs, frs) st2"
proof -
  from tsresD[OF assms(1)] obtain env1 ffn1 frn1 where s1: "st1 = (env1, ffn1 @ ffs, frn1 @ frs)"
    "tyinv ar V env1 (ffn1 @ frn1)" "tstep V (vps_dps dps1) env env1"
    "vps_dps (ffn1 @ frn1) \<subseteq> reach env (vps_dps dps1)"
    "\<And>dp. dp \<in> set ffn1 \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn1 \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn1 @ frn1) \<Longrightarrow> heads_unb env dp"
    by blast
  from tsresD[OF assms(2)[unfolded s1(1)]] obtain env2 ffn2 frn2 where
    s2: "st2 = (env2, ffn2 @ ffn1 @ ffs, frn2 @ frn1 @ frs)"
    "tyinv ar V env2 (ffn2 @ frn2)" "tstep V (vps_dps dps2) env1 env2"
    "vps_dps (ffn2 @ frn2) \<subseteq> reach env1 (vps_dps dps2)"
    "\<And>dp. dp \<in> set ffn2 \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn2 \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn2 @ frn2) \<Longrightarrow> heads_unb env1 dp"
    by blast
  have st: "tstep V (vps_dps (dps1 @ dps2)) env env2"
    using tstep_trans[OF s1(3) s2(3)] by (simp add: Un_ac)
  have c1: "tyinv ar V env2 (ffn1 @ frn1)"
    using tyinv_same[OF s1(2) tyinvD(1)[OF s2(2)]] tstepD(2)[OF s2(3)] by simp
  have c: "tyinv ar V env2 ((ffn2 @ ffn1) @ frn2 @ frn1)"
    using c1 s2(2) by (auto simp: tyinv_def)
  have vv: "vps_dps ((ffn2 @ ffn1) @ frn2 @ frn1) \<subseteq> reach env (vps_dps (dps1 @ dps2))"
  proof -
    have "vps_dps (ffn2 @ frn2) \<subseteq> reach env (vps_dps dps2 \<union> vps_dps dps1)"
      using s2(4) tstepD(3)[OF s1(3), of "vps_dps dps2"] by blast
    moreover have "vps_dps (ffn1 @ frn1) \<subseteq> reach env (vps_dps dps2 \<union> vps_dps dps1)"
      using s1(4) reach_subset[of "vps_dps dps1" "vps_dps dps2 \<union> vps_dps dps1" env] by blast
    ultimately show ?thesis by (auto simp: Un_ac)
  qed
  have ffh: "ff_shape V dp" if "dp \<in> set (ffn2 @ ffn1)" for dp using that s1(5) s2(5) by (metis Un_iff set_append)
  have frh: "fr_shape V dp" if "dp \<in> set (frn2 @ frn1)" for dp using that s1(6) s2(6) by (metis Un_iff set_append)
  have hh: "heads_unb env dp" if "dp \<in> set ((ffn2 @ ffn1) @ frn2 @ frn1)" for dp
    using that s1(7) s2(7) heads_unb_extends[OF _ tstepD(1)[OF s1(3)]] by (metis Un_iff set_append)
  have "tsres ar V (dps1 @ dps2) (env, ffs, frs) (env2, (ffn2 @ ffn1) @ ffs, (frn2 @ frn1) @ frs)"
    by (rule tsresI[OF c st vv ffh frh hh])
  then show ?thesis using s2(1) by simp
qed

lemma tsres_mono_dps:
  assumes "tsres ar V dps' (env, ffs, frs) st'" "vps_dps dps' \<subseteq> reach env (vps_dps dps)"
  shows "tsres ar V dps (env, ffs, frs) st'"
proof -
  have m': "reach env (vps_dps dps') \<subseteq> reach env (vps_dps dps)"
    using assms(2) by (rule reach_mono)
  from tsresD[OF assms(1)] obtain env' ffn frn where s: "st' = (env', ffn @ ffs, frn @ frs)"
    "tyinv ar V env' (ffn @ frn)" "tstep V (vps_dps dps') env env'"
    "vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps')"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
    by blast
  have "tsres ar V dps (env, ffs, frs) (env', ffn @ ffs, frn @ frs)"
    by (rule tsresI[OF s(2) tstep_mono[OF s(3) assms(2)] _ s(5,6,7)]) (use s(4) m' in blast)
  with s(1) show ?thesis by simp
qed

text \<open>The arguments of rigid-rigid pairs with equal heads.\<close>

lemma simrands_term:
  assumes F: "\<And>i st. i < length as \<Longrightarrow> tyinv ar V (fst st) [] \<Longrightarrow> tstep V D env0 (fst st) \<Longrightarrow>
      cuok (F (rb, as ! i, bs ! i) st) (tsres ar V [(rb, as ! i, bs ! i)] st)"
    and h: "\<nexists>f u. h = f $ u"
  shows "length as = length bs \<Longrightarrow> tyinv ar V (fst st) [] \<Longrightarrow> tstep V D env0 (fst st) \<Longrightarrow>
    vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) \<subseteq> D \<Longrightarrow>
    cuok (simrands F rb u0 (list_comb h as) (list_comb h bs) st)
      (tsres ar V (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) st)"
  using F
proof (induction as arbitrary: bs st rule: rev_induct)
  case Nil
  then have "bs = []" by simp
  moreover have "simrands F rb u0 h h st = returnW st" using h by (cases h) simp_all
  ultimately show ?case using tsres_refl[OF Nil.prems(2)] by (cases st) simp
next
  case (snoc a as)
  obtain env0' ffs0 frs0 where st: "st = (env0', ffs0, frs0)" by (cases st)
  from snoc.prems(1) obtain b bs' where bs: "bs = bs' @ [b]" "length as = length bs'"
    by (metis length_Suc_conv_rev)
  have F': "cuok (F (rb, as ! i, bs' ! i) st) (tsres ar V [(rb, as ! i, bs' ! i)] st)"
    if "i < length as" "tyinv ar V (fst st) []" "tstep V D env0 (fst st)" for i st
    using snoc.prems(5)[of i st] that bs by (simp add: nth_append)
  have D': "vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) \<subseteq> D"
    using snoc.prems(4) bs by auto
  have Dab: "vps_dps [(rb, a, b)] \<subseteq> D" using snoc.prems(4) bs by auto
  have "simrands F rb u0 (list_comb h (as @ [a])) (list_comb h bs) st =
      bindW (simrands F rb u0 (list_comb h as) (list_comb h bs') st) (F (rb, a, b))"
    using bs by (simp add: list_comb_snoc)
  moreover have "cuok (bindW (simrands F rb u0 (list_comb h as) (list_comb h bs') st) (F (rb, a, b)))
      (tsres ar V (map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs)) st)"
  proof (rule cuok_bindW[OF snoc.IH[OF bs(2) snoc.prems(2,3) D' F']])
    fix st1 assume r1: "tsres ar V (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) st st1"
    obtain env1 ffn frn where
      s1: "st1 = (env1, ffn @ ffs0, frn @ frs0)" "tyinv ar V env1 (ffn @ frn)"
        "tstep V (vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs'))) env0' env1"
      by (rule tsresD[OF r1[unfolded st]])
    have c1: "tyinv ar V (fst st1) []" using s1(1,2) by (simp add: tyinv_Nil)
    have "tstep V (D \<union> vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs'))) env0 env1"
      using tstep_trans[OF snoc.prems(3)[unfolded st, simplified] s1(3)] .
    then have t1: "tstep V D env0 (fst st1)"
      using s1(1) D' by (auto intro: tstep_mono intro!: set_mp[OF reach_incl])
    from snoc.prems(5)[of "length as" st1] c1 t1 bs
    have "cuok (F (rb, a, b) st1) (tsres ar V [(rb, a, b)] st1)" by (simp add: nth_append)
    then show "cuok (F (rb, a, b) st1) (tsres ar V (map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs)) st)"
      by (rule cuok_mono) (use tsres_trans[OF r1[unfolded st]] bs st in simp)
  qed
  ultimately show ?case by simp
qed

subsection \<open>Termination of \<open>SIMPL0\<close>\<close>

lemma SIMPL0_step_clash:
  assumes "is_rigid (head_of t)" "is_rigid (head_of u)" "head_of t \<noteq> head_of u"
    "typs_ok ar (head_of t)" "typs_ok ar (head_of u)"
  shows "\<exists>evs. SIMPL0_step alg F (rb, t, u) env ffs frs = Some (evs, UErr CANTUNIFY)"
proof -
  have cl: "\<exists>evs. bindW (cunify_types alg T U env) f = Some (evs, UErr CANTUNIFY)"
    if "ground ar T" "ground ar U" "T \<noteq> U" for T U and f :: "env \<Rightarrow> sstate W"
    using cunify_types_ground_neq[OF that, of alg env] by (auto simp: bindW_def)
  from assms(1,2) show ?thesis
    unfolding is_rigid_def
  proof (elim disjE exE conjE)
    fix a T b U assume h: "head_of t = Const a T" "head_of u = Const b U"
    then show ?thesis using assms(3-5) cl[of T U] by (auto simp: SIMPL0_step_def raiseW_def)
  next
    fix a T b U assume h: "head_of t = Free a T" "head_of u = Free b U"
    then show ?thesis using assms(3-5) cl[of T U] by (auto simp: SIMPL0_step_def raiseW_def)
  next
    fix i j assume h: "head_of t = Bound i" "head_of u = Bound j"
    then show ?thesis using assms(3) by (auto simp: SIMPL0_step_def raiseW_def)
  qed (auto simp: SIMPL0_step_def raiseW_def)
qed

lemma foldr_fun_type_base_inj:
  "\<not> is_funT B \<Longrightarrow> \<not> is_funT B' \<Longrightarrow> foldr fun_type Us B = foldr fun_type Us' B' \<Longrightarrow> Us = Us' \<and> B = B'"
proof (induction Us arbitrary: Us')
  case Nil
  then show ?case by (cases Us') auto
next
  case (Cons U Us)
  then show ?case by (cases Us') auto
qed

text \<open>One step of \<^const>\<open>SIMPL0\<close> on a head-normalized pair, as @{thm [source] SIMPL0_step_complete}.\<close>

lemma SIMPL0_step_term:
  assumes inv: "tyinv ar V env [(rb, t, u)]"
    and ty: "has_type V (map snd rb) t B" "has_type V (map snd rb) u B" "\<not> is_funT B"
    and nA: "\<not> is_Abs (head_of t)" "\<not> is_Abs (head_of u)"
    and ut: "\<And>F U. head_of t = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and IH: "\<And>i st as bs Us. is_rigid (head_of t) \<Longrightarrow> t = list_comb (head_of t) as \<Longrightarrow>
      u = list_comb (head_of t) bs \<Longrightarrow>
      has_type V (map snd rb) (head_of t) (foldr fun_type Us B) \<Longrightarrow>
      list_all2 (has_type V (map snd rb)) as Us \<Longrightarrow> list_all2 (has_type V (map snd rb)) bs Us \<Longrightarrow>
      i < length as \<Longrightarrow> tyinv ar V (fst st) [(rb, as ! i, bs ! i)] \<Longrightarrow>
      tstep V (vps t \<union> vps u) env (fst st) \<Longrightarrow>
      cuok (F (rb, as ! i, bs ! i) st) (tsres ar V [(rb, as ! i, bs ! i)] st)"
  shows "cuok (SIMPL0_step alg F (rb, t, u) env ffs frs) (tsres ar V [(rb, t, u)] (env, ffs, frs))"
proof -
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from tyinvD(2)[OF inv, of "(rb, t, u)"] have wfd: "wf_dp ar (rb, t, u)"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  have c0: "tyinv ar V env []" by (rule tyinv_Nil[OF inv])
  have vsub: "vps_dps [(rb, t, u)] \<subseteq> reach env (vps_dps [(rb, t, u)])" by (rule reach_incl)
  have hb: "heads_unb env (rb, t, u)" "heads_unb env (rb, u, t)"
    using ut uu by (auto simp: heads_unb_def)
  have keep_fr: "tsres ar V [(rb, t, u)] (env, ffs, frs) (env, ffs, (rb, t, u) # frs)"
    if "fr_shape V (rb, t, u)"
    using tsresI[of ar V env "[]" "[(rb, t, u)]" "[(rb, t, u)]" env ffs frs] inv vsub hb that by simp
  have keep_fr': "tsres ar V [(rb, t, u)] (env, ffs, frs) (env, ffs, (rb, u, t) # frs)"
    if "fr_shape V (rb, u, t)"
  proof -
    have "tyinv ar V env [(rb, u, t)]" using inv by (auto simp: tyinv_def)
    then show ?thesis
      using tsresI[of ar V env "[]" "[(rb, u, t)]" "[(rb, t, u)]" env ffs frs] vsub hb that
      by (simp add: Un_commute)
  qed
  have asg: "tsres ar V [(rb, t, u)] (env, ffs, frs) (env', ffs, frs)"
    if "env_inv ar V env'" "tstep V (vps t \<union> vps u) env env'" for env'
    using tsresI[of ar V env' "[]" "[]" "[(rb, t, u)]" env ffs frs] that tstepD(2)[OF that(2)]
    by (simp add: tyinv_def)
  consider (VV) x X y Y where "head_of t = Var x X" "head_of u = Var y Y"
    | (VR) x X where "head_of t = Var x X" "is_rigid (head_of u)"
    | (RV) y Y where "is_rigid (head_of t)" "head_of u = Var y Y"
    | (RR) "is_rigid (head_of t)" "is_rigid (head_of u)"
    using head_cases[OF ty(1) nA(1)] head_cases[OF ty(2) nA(2)] by metis
  then show ?thesis
  proof cases
    case VV
    have bt: "body_type env X = return B" "body_type env Y = return B"
      using body_type_head[OF ty(1,3) VV(1) e] body_type_head[OF ty(2,3) VV(2) e] by simp_all
    have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env, (rb, t, u) # ffs, frs)"
      using VV bt by (simp add: SIMPL0_step_def cunify_types_same return_def)
    moreover have "ff_shape V (rb, t, u)" using ty VV by (auto simp: ff_shape_def)
    ultimately show ?thesis
      using tsresI[of ar V env "[(rb, t, u)]" "[]" "[(rb, t, u)]" env ffs frs] inv vsub hb
      by (auto simp: cuok_def)
  next
    case VR
    have fr: "fr_shape V (rb, t, u)" using ty VR by (auto simp: fr_shape_def)
    have "(\<exists>evs. assignment alg rb t u env = Some (evs, UErr ASSIGN)) \<or>
      (\<exists>evs. assignment alg rb t u env = Some (evs, UErr CANTUNIFY)) \<or>
      (\<exists>env'. okW (assignment alg rb t u env) env' \<and> env_inv ar V env' \<and>
        tstep V (vps t \<union> vps u) env env')"
      by (rule assignment_term[OF inv ty]) (rule ut)
    then consider (A) evs where "assignment alg rb t u env = Some (evs, UErr ASSIGN)"
      | (C) evs where "assignment alg rb t u env = Some (evs, UErr CANTUNIFY)"
      | (O) env' where "okW (assignment alg rb t u env) env'" "env_inv ar V env'"
          "tstep V (vps t \<union> vps u) env env'"
      by blast
    then show ?thesis
    proof cases
      case A
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env, ffs, (rb, t, u) # frs)"
        using VR A by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep_fr[OF fr] show ?thesis by (auto simp: cuok_def)
    next
      case C
      then show ?thesis using VR
        by (cases "head_of u") (auto simp: SIMPL0_step_def handleW_def is_rigid_def bindW_def cuok_def raiseW_def)
    next
      case O
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env', ffs, frs)"
        using VR O(1) by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF O(2,3)] show ?thesis by (auto simp: cuok_def)
    qed
  next
    case RV
    have fr: "fr_shape V (rb, u, t)" using ty RV by (auto simp: fr_shape_def)
    have inv': "tyinv ar V env [(rb, u, t)]" using inv by (auto simp: tyinv_def)
    have "(\<exists>evs. assignment alg rb u t env = Some (evs, UErr ASSIGN)) \<or>
      (\<exists>evs. assignment alg rb u t env = Some (evs, UErr CANTUNIFY)) \<or>
      (\<exists>env'. okW (assignment alg rb u t env) env' \<and> env_inv ar V env' \<and>
        tstep V (vps u \<union> vps t) env env')"
      by (rule assignment_term[OF inv' ty(2,1,3)]) (rule uu)
    then consider (A) evs where "assignment alg rb u t env = Some (evs, UErr ASSIGN)"
      | (C) evs where "assignment alg rb u t env = Some (evs, UErr CANTUNIFY)"
      | (O) env' where "okW (assignment alg rb u t env) env'" "env_inv ar V env'"
          "tstep V (vps u \<union> vps t) env env'"
      by blast
    then show ?thesis
    proof cases
      case A
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env, ffs, (rb, u, t) # frs)"
        using RV A by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep_fr'[OF fr] show ?thesis by (auto simp: cuok_def)
    next
      case C
      then show ?thesis using RV
        by (cases "head_of t") (auto simp: SIMPL0_step_def handleW_def is_rigid_def bindW_def cuok_def raiseW_def)
    next
      case O
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env', ffs, frs)"
        using RV O(1) by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF O(2) O(3)[unfolded Un_commute[of "vps u"]]] show ?thesis by (auto simp: cuok_def)
    qed
  next
    case RR
    define h where "h = head_of t"
    define as where "as = snd (strip_comb t)"
    define h' where "h' = head_of u"
    define bs where "bs = snd (strip_comb u)"
    have t: "t = list_comb h as" using head_of_list_comb[of t] by (simp add: h_def as_def)
    have u0: "u = list_comb h' bs" using head_of_list_comb[of u] by (simp add: bs_def h'_def)
    have tyo: "typs_ok ar h" "typs_ok ar h'"
      using wfd typs_ok_head_of by (auto simp: wf_tm_def h_def h'_def)
    show ?thesis
    proof (cases "h' = h")
      case False
      then have "head_of t \<noteq> head_of u" by (simp add: h_def h'_def)
      from SIMPL0_step_clash[OF RR this tyo[unfolded h_def h'_def]]
      show ?thesis by (auto simp: cuok_def)
    next
      case True
      from ty(1) t obtain Us where tyh: "has_type V (map snd rb) h (foldr fun_type Us B)"
        and tyas: "list_all2 (has_type V (map snd rb)) as Us"
        by (auto simp: has_type_list_comb)
      from ty(2) u0 obtain Us' where tyh': "has_type V (map snd rb) h' (foldr fun_type Us' B)"
        and tybs: "list_all2 (has_type V (map snd rb)) bs Us'"
        by (auto simp: has_type_list_comb)
      have "foldr fun_type Us B = foldr fun_type Us' B" using has_type_unique[OF tyh tyh'[unfolded True]] .
      then have UU: "Us' = Us" using foldr_fun_type_base_inj[OF ty(3) ty(3)] by simp
      have u: "u = list_comb h bs" using u0 True by simp
      have lUs: "length Us = length as" "length Us' = length bs"
        using list_all2_lengthD[OF tyas] list_all2_lengthD[OF tybs] by simp_all
      have len: "length as = length bs" using lUs UU by simp
      have rig: "is_rigid h" using RR by (simp add: h_def)
      have h0: "\<nexists>f u. h = f $ u" using head_of_not_App h_def by metis
      have step_eq: "SIMPL0_step alg F (rb, t, u) env ffs frs = simrands F rb u t u (env, ffs, frs)"
        using rig True by (auto simp: SIMPL0_step_def is_rigid_def h_def h'_def cunify_types_same bindW_def
          returnW_def case_prod_beta option.map_ident option.map_id)
      have wfa: "wf_tm ar rb (as ! i)" "wf_tm ar rb (bs ! i)" if "i < length as" for i
        using wfd that len t u by (auto simp: wf_tm_list_comb)
      have bla: "below (maxidx env) (as ! i)" "below (maxidx env) (bs ! i)" if "i < length as" for i
        using bl that len t u by (auto simp: below_list_comb)
      let ?D = "vps t \<union> vps u"
      have F: "cuok (F (rb, as ! i, bs ! i) st) (tsres ar V [(rb, as ! i, bs ! i)] st)"
        if i: "i < length as" and st: "tyinv ar V (fst st) []" "tstep V ?D env (fst st)" for i st
      proof (rule IH[OF RR(1)])
        show "t = list_comb (head_of t) as" using t by (simp add: h_def)
        show "u = list_comb (head_of t) bs" using u by (simp add: h_def)
        show "has_type V (map snd rb) (head_of t) (foldr fun_type Us B)" using tyh by (simp add: h_def)
        show "list_all2 (has_type V (map snd rb)) as Us" by (rule tyas)
        show "list_all2 (has_type V (map snd rb)) bs Us" using tybs UU by simp
        show "i < length as" by (rule i)
        have "has_type V (map snd rb) (bs ! i) (Us ! i)" using list_all2_nthD[OF tybs] i len UU by simp
        moreover have "has_type V (map snd rb) (as ! i) (Us ! i)" using list_all2_nthD[OF tyas i] .
        moreover have "maxidx (fst st) = maxidx env" using tstepD(2)[OF st(2)] .
        ultimately show "tyinv ar V (fst st) [(rb, as ! i, bs ! i)]"
          using st(1) wfa[OF i] bla[OF i] wfd by (auto simp: tyinv_def)
        show "tstep V (vps t \<union> vps u) env (fst st)" by (rule st(2))
      qed
      have Dsub: "vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) \<subseteq> ?D"
        using t u by (fastforce simp: vps_list_comb dest: set_zip_leftD set_zip_rightD)
      have "cuok (simrands F rb u (list_comb h as) (list_comb h bs) (env, ffs, frs))
        (tsres ar V (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) (env, ffs, frs))"
        by (rule simrands_term[where F = F and st = "(env, ffs, frs)", OF F h0 len _ tstep_refl Dsub])
          (use c0 in simp_all)
      moreover have "vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) \<subseteq> reach env (vps_dps [(rb, t, u)])"
        using Dsub reach_incl[of "vps t \<union> vps u" env] by auto
      ultimately have "cuok (simrands F rb u (list_comb h as) (list_comb h bs) (env, ffs, frs))
        (tsres ar V [(rb, t, u)] (env, ffs, frs))"
        by (elim cuok_mono) (rule tsres_mono_dps)
      then show ?thesis using step_eq t u by simp
    qed
  qed
qed

text \<open>
  \<^const>\<open>SIMPL0\<close> terminates, by induction on the number of unbound variables reachable from
  the pair and the size \<^const>\<open>dsz\<close> of its instance under a solution of the environment.
\<close>

lemma SIMPL0_term_aux:
  "(card (unb env (vps t \<union> vps u)), dsz (tau V) \<sigma> rb t T) = p \<Longrightarrow> tyinv ar V env [(rb, t, u)] \<Longrightarrow>
    solution V (tau V) \<sigma> env \<Longrightarrow> has_type V (map snd rb) t T \<Longrightarrow>
    cuok (SIMPL0 alg (rb, t, u) (env, ffs, frs)) (tsres ar V [(rb, t, u)] (env, ffs, frs))"
proof (induction p arbitrary: rb t u T env \<sigma> ffs frs rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  case (1 p rb t u T env \<sigma> ffs frs)
  note inv = "1.prems"(2)
  note \<sigma> = solutionD[OF "1.prems"(3)]
  note ei = env_invD[OF tyinvD(1)[OF inv]]
  obtain rb' t' u' T0 where hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    and inv': "tyinv ar V env [(rb', t', u')]"
    and tyt0: "has_type V (map snd rb) t T0" and rb': "map snd rb' = rev (arg_types T0) @ map snd rb"
    and ty': "has_type V (map snd rb') t' (res_type T0)" "has_type V (map snd rb') u' (res_type T0)"
    and nA: "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    and vt: "vps t' \<subseteq> reach env (vps t)" "vps u' \<subseteq> reach env (vps u)"
    and ut: "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and eqv: "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'"
    by (rule head_norm_dpair_term[OF inv, where alg = alg]) blast
  have T0: "T0 = T" by (rule has_type_unique[OF tyt0 "1.prems"(4)])
  define B where "B = res_type T"
  have nfB: "\<not> is_funT B" by (simp add: B_def res_type_base)
  have TT: "foldr fun_type (rev (map snd rb')) B = foldr fun_type (rev (map snd rb)) T"
    using rb' T0 arg_res_type[of T] by (simp add: B_def)
  have eq: "mk_subst \<sigma> (tr (rlist_abs rb' t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t))"
    using equiv_sym[OF env_equivD[OF eqv \<sigma>(1,4)]] .
  have dszeq: "dsz (tau V) \<sigma> rb' t' B = dsz (tau V) \<sigma> rb t T"
    by (rule dsz_equiv[OF "1.prems"(4) ty'(1)[unfolded T0, folded B_def] TT eq \<sigma>(1,2)])
  let ?X = "vps t \<union> vps u" and ?D = "vps t' \<union> vps u'"
  have Dsub: "?D \<subseteq> reach env ?X"
    using vt reach_subset[of "vps t" ?X env] reach_subset[of "vps u" ?X env] by blast
  have "cuok (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs) (tsres ar V [(rb', t', u')] (env, ffs, frs))"
  proof (rule SIMPL0_step_term[OF inv' ty'[unfolded T0, folded B_def] nfB nA ut uu])
    fix i and st :: sstate and as bs Us
    assume rig: "is_rigid (head_of t')" and t': "t' = list_comb (head_of t') as"
      and u': "u' = list_comb (head_of t') bs"
      and tyh: "has_type V (map snd rb') (head_of t') (foldr fun_type Us B)"
      and tyas: "list_all2 (has_type V (map snd rb')) as Us"
      and tybs: "list_all2 (has_type V (map snd rb')) bs Us" and i: "i < length as"
      and ci: "tyinv ar V (fst st) [(rb', as ! i, bs ! i)]" and ts: "tstep V ?D env (fst st)"
    obtain env1 ffs1 frs1 where st: "st = (env1, ffs1, frs1)" by (cases st)
    have tyi: "has_type V (map snd rb') (as ! i) (Us ! i)" using list_all2_nthD[OF tyas i] .
    have ib: "i < length bs" using i list_all2_lengthD[OF tyas] list_all2_lengthD[OF tybs] by simp
    note ei1 = env_invD[OF tyinvD(1)[OF ci[unfolded st, simplified]]]
    have ts': "tstep V ?X env env1" using tstep_mono[OF ts Dsub] st by simp
    have Ysub: "vps (as ! i) \<union> vps (bs ! i) \<subseteq> reach env ?X"
    proof -
      have "vps (as ! i) \<subseteq> vps (list_comb (head_of t') as)" using nth_mem[OF i] by (auto simp: vps_list_comb)
      then have "vps (as ! i) \<subseteq> vps t'" using t'[symmetric] by simp
      moreover have "vps (bs ! i) \<subseteq> vps (list_comb (head_of t') bs)" using nth_mem[OF ib] by (auto simp: vps_list_comb)
      then have "vps (bs ! i) \<subseteq> vps u'" using u'[symmetric] by simp
      ultimately show ?thesis using Dsub by blast
    qed
    have finX: "finite ?X" by simp
    have cle: "card (unb env (vps (as ! i) \<union> vps (bs ! i))) \<le> card (unb env ?X)"
      by (rule card_mono[OF finite_subset[OF _ finite_reach[OF finX]] unb_reach_mono[OF Ysub]])
        (auto simp: unb_def)
    show "cuok (SIMPL0 alg (rb', as ! i, bs ! i) st) (tsres ar V [(rb', as ! i, bs ! i)] st)"
    proof (cases "same_lk env env1")
      case True
      have sol1: "solution V (tau V) \<sigma> env1" using same_lk_solution[OF True] "1.prems"(3) by simp
      have "dsz (tau V) \<sigma> rb' (as ! i) (Us ! i) < dsz (tau V) \<sigma> rb' (list_comb (head_of t') as) B"
        by (rule dsz_args[OF tyh tyas rig \<sigma>(1,2,3) i])
      with dszeq t' have lt: "dsz (tau V) \<sigma> rb' (as ! i) (Us ! i) < dsz (tau V) \<sigma> rb t T" by simp
      have "card (unb env1 (vps (as ! i) \<union> vps (bs ! i))) \<le> card (unb env ?X)"
        using cle same_lk_unb[OF True] by simp
      with lt "1.prems"(1) have less: "((card (unb env1 (vps (as ! i) \<union> vps (bs ! i))),
          dsz (tau V) \<sigma> rb' (as ! i) (Us ! i)), p) \<in> less_than <*lex*> less_than"
        by auto
      from "1.IH"[OF less refl ci[unfolded st, simplified] sol1 tyi, of ffs1 frs1] st show ?thesis by simp
    next
      case False
      define \<sigma>1 where "\<sigma>1 = env_sol env1 V"
      have sol1: "solution V (tau V) \<sigma>1 env1" unfolding \<sigma>1_def by (rule env_solution(1)[OF ei1(1,2,3)])
      have "card (unb env1 (vps (as ! i) \<union> vps (bs ! i))) < card (unb env ?X)"
        by (rule tstep_unb_less[OF ts' Ysub finX ei1(3) False])
      with "1.prems"(1) have less: "((card (unb env1 (vps (as ! i) \<union> vps (bs ! i))),
          dsz (tau V) \<sigma>1 rb' (as ! i) (Us ! i)), p) \<in> less_than <*lex*> less_than"
        by auto
      from "1.IH"[OF less refl ci[unfolded st, simplified] sol1 tyi, of ffs1 frs1] st show ?thesis by simp
    qed
  qed
  moreover have "vps_dps [(rb', t', u')] \<subseteq> reach env (vps_dps [(rb, t, u)])" using Dsub by simp
  ultimately have step: "cuok (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs)
      (tsres ar V [(rb, t, u)] (env, ffs, frs))"
    by (elim cuok_mono) (rule tsres_mono_dps)
  have "SIMPL0 alg (rb, t, u) (env, ffs, frs) =
      bindW (head_norm_dpair alg env (rb, t, u)) (\<lambda>(dp, env). SIMPL0_step alg (SIMPL0 alg) dp env ffs frs)"
    by (simp add: SIMPL0_unfold)
  moreover have "cuok (bindW (head_norm_dpair alg env (rb, t, u))
      (\<lambda>(dp, env). SIMPL0_step alg (SIMPL0 alg) dp env ffs frs)) (tsres ar V [(rb, t, u)] (env, ffs, frs))"
  proof (rule cuok_bindW[where P = "\<lambda>x. x = ((rb', t', u'), env)"])
    show "cuok (head_norm_dpair alg env (rb, t, u)) (\<lambda>x. x = ((rb', t', u'), env))"
      using hd by (auto simp: cuok_def)
  qed (use step in auto)
  ultimately show ?case by simp
qed

theorem SIMPL0_term:
  assumes "tyinv ar V env [dp]"
  shows "cuok (SIMPL0 alg dp (env, ffs, frs)) (tsres ar V [dp] (env, ffs, frs))"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from tyinvD(2)[OF assms, of dp] dp obtain T where ty: "has_type V (map snd rb) t T" by auto
  note ei = env_invD[OF tyinvD(1)[OF assms]]
  have "solution V (tau V) (env_sol env V) env" by (rule env_solution(1)[OF ei(1,2,3)])
  from SIMPL0_term_aux[OF refl assms[unfolded dp] this ty, of alg ffs frs] dp show ?thesis by simp
qed


subsection \<open>Termination of \<open>SIMPL\<close>\<close>

lemma tsres_set: "set dps = set dps' \<Longrightarrow> tsres ar V dps st st' = tsres ar V dps' st st'"
  by (simp add: tsres_def)

lemma foldrW_SIMPL0_term:
  "tyinv ar V env dps \<Longrightarrow>
    cuok (foldrW (SIMPL0 alg) dps (env, [], [])) (tsres ar V dps (env, [], []))"
proof (induction dps)
  case Nil
  then show ?case using tsres_refl[OF tyinv_Nil[OF Nil]] by simp
next
  case (Cons dp dps)
  from Cons.prems have c1: "tyinv ar V env [dp]" and c2: "tyinv ar V env dps"
    by (simp_all add: tyinv_def)
  have "cuok (bindW (foldrW (SIMPL0 alg) dps (env, [], [])) (SIMPL0 alg dp)) (tsres ar V (dp # dps) (env, [], []))"
  proof (rule cuok_bindW[OF Cons.IH[OF c2]])
    fix st1 assume r1: "tsres ar V dps (env, [], []) st1"
    obtain env1 ffn frn where s1: "st1 = (env1, ffn @ [], frn @ [])" "tyinv ar V env1 (ffn @ frn)"
      "tstep V (vps_dps dps) env env1"
      by (rule tsresD[OF r1])
    have "tyinv ar V env1 [dp]"
      using tyinv_same[OF c1 tyinvD(1)[OF s1(2)]] tstepD(2)[OF s1(3)] by simp
    from SIMPL0_term[OF this, of alg ffn frn]
    have "cuok (SIMPL0 alg dp st1) (tsres ar V [dp] st1)" using s1(1) by simp
    then show "cuok (SIMPL0 alg dp st1) (tsres ar V (dp # dps) (env, [], []))"
    proof (rule cuok_mono)
      fix st2 assume "tsres ar V [dp] st1 st2"
      from tsres_trans[OF r1 this] have "tsres ar V (dps @ [dp]) (env, [], []) st2" .
      then show "tsres ar V (dp # dps) (env, [], []) st2" using tsres_set[of "dps @ [dp]" "dp # dps"] by simp
    qed
  qed
  then show ?case by simp
qed

text \<open>The result of \<^const>\<open>SIMPL\<close>, as \<^const>\<open>simpl_res\<close>:\<close>

definition tsimpl_res :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> sstate \<Rightarrow> bool" where
  "tsimpl_res ar V dps env st' \<longleftrightarrow> (case st' of (env', ffs, frs) \<Rightarrow>
    tyinv ar V env' (ffs @ frs) \<and> tstep V (vps_dps dps) env env' \<and> vps_dps (ffs @ frs) \<subseteq> reach env (vps_dps dps) \<and>
    (\<forall>dp\<in>set ffs. ff_shape V dp) \<and> (\<forall>dp\<in>set frs. fr_shape V dp) \<and>
    (\<forall>dp\<in>set (ffs @ frs). heads_unb env' dp))"

lemma SIMPL_term_aux:
  "card (unb env (vps_dps dps)) < n \<Longrightarrow> tyinv ar V env dps \<Longrightarrow>
    cuok (SIMPL alg env dps) (tsimpl_res ar V dps env)"
proof (induction n arbitrary: env dps)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note ei = env_invD[OF tyinvD(1)[OF Suc.prems(2)]]
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
      (tsimpl_res ar V dps env)"
  proof (rule cuok_bindW[OF foldrW_SIMPL0_term[OF Suc.prems(2)]])
    fix st1 assume r1: "tsres ar V dps (env, [], []) st1"
    obtain env1 ffs frs where s1: "st1 = (env1, ffs @ [], frs @ [])" "tyinv ar V env1 (ffs @ frs)"
      "tstep V (vps_dps dps) env env1" "vps_dps (ffs @ frs) \<subseteq> reach env (vps_dps dps)"
      "\<And>dp. dp \<in> set ffs \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frs \<Longrightarrow> fr_shape V dp"
      "\<And>dp. dp \<in> set (ffs @ frs) \<Longrightarrow> heads_unb env dp"
      by (rule tsresD[OF r1]) (rule that)
    note ei1 = env_invD[OF tyinvD(1)[OF s1(2)]]
    have e1: "vt_is_empty (tyenv env1)" by (rule wf_envD(1)[OF ei1(2)])
    define dps' where "dps' = frs @ ffs"
    define ch where "ch = (\<lambda>s. \<exists>x T. head_of s = Var x T \<and> vt_lookup (tenv env1) x \<noteq> None)"
    have vty: "vtyped V t \<and> vtyped V u" if "(rb, t, u) \<in> set dps'" for rb t u
      using tyinvD(2)[OF s1(2), of "(rb, t, u)"] that by (auto simp: dps'_def intro: has_type_vtyped)
    have ex: "existsM (\<lambda>(_, t, u). do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) dps' =
      return (\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
    proof (rule existsM_return)
      fix dp assume "dp \<in> set dps'"
      obtain rb t u where dp0: "dp = (rb, t, u)" by (cases dp)
      with \<open>dp \<in> set dps'\<close> vty have dp: "dp = (rb, t, u)" "vtyped V t" "vtyped V u" by auto
      then show "(case dp of (_, t, u) \<Rightarrow> do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) =
        return (case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
        by (auto simp: changed_typed[OF e1 ei1(3)] ch_def return_def)
    qed
    show "cuok (case st1 of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then SIMPL alg env' dps else returnW st1})
      (tsimpl_res ar V dps env)"
    proof (cases "\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u")
      case False
      have "heads_unb env1 dp" if "dp \<in> set (ffs @ frs)" for dp
      proof -
        obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
        with that have "(rb, t, u) \<in> set dps'" by (auto simp: dps'_def)
        with False have "\<not> ch t" "\<not> ch u" by auto
        then show ?thesis unfolding dp heads_unb_def prod.case ch_def by blast
      qed
      then have "tsimpl_res ar V dps env (env1, ffs, frs)"
        using s1 by (auto simp: tsimpl_res_def)
      then show ?thesis using s1(1) ex False by (simp add: dps'_def return_def)
    next
      case True
      then obtain rb t u where dp: "(rb, t, u) \<in> set dps'" and cht: "ch t \<or> ch u" by blast
      have c1: "tyinv ar V env1 dps'" using s1(2) by (auto simp: tyinv_def dps'_def)
      obtain s x T where s: "s \<in> {t, u}" "head_of s = Var x T" "vt_lookup (tenv env1) x \<noteq> None"
        using cht unfolding ch_def by blast
      have hb: "heads_unb env (rb, t, u)" using s1(7) dp by (auto simp: dps'_def)
      then have xu: "vt_lookup (tenv env) x = None" using s(1,2) unfolding heads_unb_def prod.case by blast
      have "vps s \<subseteq> vps_dps dps'" using dp s(1) by auto
      moreover have "vps_dps dps' \<subseteq> reach env (vps_dps dps)" using s1(4) by (auto simp: dps'_def)
      ultimately have xr: "(x, T) \<in> reach env (vps_dps dps)" using vps_head_of[OF s(2)] by blast
      have xin: "(x, T) \<in> unb env (vps_dps dps)" using xr xu by (simp add: unb_def lk_def)
      have Vx: "V x = T" using vty[OF dp] s vps_head_of[OF s(2)] by (auto simp: vtyped_def)
      have xout: "(x, T) \<notin> unb env1 (vps_dps dps')"
      proof -
        from s(3) obtain U w where "vt_lookup (tenv env1) x = Some (U, w)" by auto
        moreover from this env_typedD[OF ei1(3)] Vx have "U = T" by blast
        ultimately show ?thesis by (simp add: unb_def lk_def)
      qed
      have sub: "unb env1 (vps_dps dps') \<subseteq> unb env (vps_dps dps)"
        by (rule tstep_unb[OF s1(3)]) (use s1(4) in \<open>auto simp: dps'_def\<close>)
      have fin: "finite (unb env (vps_dps dps))"
        by (rule finite_subset[OF _ finite_reach[of "vps_dps dps" env]]) (auto simp: unb_def)
      have "card (unb env1 (vps_dps dps')) < card (unb env (vps_dps dps))"
        using sub xin xout by (intro psubset_card_mono[OF fin]) blast
      with Suc.prems(1) have lt: "card (unb env1 (vps_dps dps')) < n" by simp
      have r2: "cuok (SIMPL alg env1 dps') (tsimpl_res ar V dps' env1)" by (rule Suc.IH[OF lt c1])
      have v1: "vps_dps dps' \<subseteq> reach env (vps_dps dps)" using s1(4) by (auto simp: dps'_def)
      have "cuok (SIMPL alg env1 dps') (tsimpl_res ar V dps env)"
      proof (rule cuok_mono[OF r2])
        fix st' assume r: "tsimpl_res ar V dps' env1 st'"
        obtain env2 ffs2 frs2 where st': "st' = (env2, ffs2, frs2)" by (cases st')
        from r st' have r': "tyinv ar V env2 (ffs2 @ frs2)" "tstep V (vps_dps dps') env1 env2"
          "vps_dps (ffs2 @ frs2) \<subseteq> reach env1 (vps_dps dps')"
          "\<forall>dp\<in>set ffs2. ff_shape V dp" "\<forall>dp\<in>set frs2. fr_shape V dp" "\<forall>dp\<in>set (ffs2 @ frs2). heads_unb env2 dp"
          by (auto simp: tsimpl_res_def)
        have "tstep V (vps_dps dps) env env2"
          using tstep_mono[OF tstep_trans[OF s1(3) r'(2)], of "vps_dps dps"] v1
          by (auto intro: set_mp[OF reach_incl])
        moreover have "vps_dps (ffs2 @ frs2) \<subseteq> reach env (vps_dps dps)"
          using r'(3) tstepD(3)[OF s1(3), of "vps_dps dps'"] reach_absorb[OF v1, of "{}"] by auto
        ultimately show "tsimpl_res ar V dps env st'" using r' st' by (simp add: tsimpl_res_def)
      qed
      then show ?thesis using s1(1) ex True by (simp add: dps'_def return_def)
    qed
  qed
  then show ?case by (simp add: body)
qed

theorem SIMPL_term: "tyinv ar V env dps \<Longrightarrow> cuok (SIMPL alg env dps) (tsimpl_res ar V dps env)"
  using SIMPL_term_aux[OF lessI] by blast

end

end
