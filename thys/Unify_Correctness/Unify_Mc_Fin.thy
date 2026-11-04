section \<open>Finiteness of the Copies of \<open>mc\<close>\<close>

theory Unify_Mc_Fin
  imports Unify_Match_Fin
begin

text \<open>
  The copies of the rigid side of a flex-rigid pair (\<^const>\<open>mc\<close>) form a finite enumeration.
  This is not a structural recursion: \<^const>\<open>S_Maps\<close> copies an argument after the copies of the
  arguments to its right, in the environment that their projections (\<^const>\<open>S_Proj\<close>, which runs
  \<^const>\<open>SIMPL\<close>) have extended, so that the argument may grow. As in the termination proof of
  theory \<open>Pure_Unify_Correctness.Unify_Poly_Match_Fin\<close>, the measure of an argument is the number
  of unbound variables of the original problem, followed by the number of rigid atoms of the
  \<open>\<beta>\<close>-normal form of its unfolding. The new variables of the copies do not change this measure:
  if one of the arguments of the flexible side is not a bound variable, they only occur applied
  to such arguments (they are \<^emph>\<open>dead\<close>) and are never assigned; otherwise they occur only at the
  heads of the sides of pairs and never in the values of the environment.
\<close>

context pure_sig
begin

subsection \<open>Reachability\<close>

abbreviation vns :: "pterm \<Rightarrow> indexname set" where
  "vns t \<equiv> fst ` vars t"

definition vreach :: "env \<Rightarrow> indexname set \<Rightarrow> indexname set" where
  "vreach env X = {y. \<exists>x\<in>X. (y, x) \<in> (dep env)\<^sup>*}"

lemma vreach_incl: "X \<subseteq> vreach env X"
  by (auto simp: vreach_def)

lemma vreach_subset: "X \<subseteq> Y \<Longrightarrow> vreach env X \<subseteq> vreach env Y"
  by (auto simp: vreach_def)

lemma vreach_Un: "vreach env (X \<union> Y) = vreach env X \<union> vreach env Y"
  by (auto simp: vreach_def)

lemma vreach_mono: "X \<subseteq> vreach env Y \<Longrightarrow> vreach env X \<subseteq> vreach env Y"
  by (auto simp: vreach_def intro: rtrancl_trans)

lemma vreach_absorb: "Y \<subseteq> vreach env Z \<Longrightarrow> vreach env (X \<union> Y) \<subseteq> vreach env (X \<union> Z)"
  using vreach_mono[of Y env Z] vreach_subset[of Z "X \<union> Z" env] by (auto simp: vreach_Un)

lemma vreach_tenv: "tenv env' = tenv env \<Longrightarrow> vreach env' = vreach env"
  by (simp add: vreach_def dep_def fun_eq_iff)

lemma vreach_step:
  assumes b: "vt_lookup (tenv env) x = Some (U, w)" and x: "x \<in> vreach env X"
  shows "vns w \<subseteq> vreach env X"
proof
  fix y assume y: "y \<in> vns w"
  from x obtain x' where "x' \<in> X" "(x, x') \<in> (dep env)\<^sup>*" by (auto simp: vreach_def)
  moreover have "(y, x) \<in> dep env" using y b by (auto simp: dep_def)
  ultimately show "y \<in> vreach env X" by (auto simp: vreach_def intro: converse_rtrancl_into_rtrancl)
qed

lemma vreach_update:
  assumes "tenv env' = vt_update (v, (T, w)) (tenv env)"
  shows "vreach env' X \<subseteq> vreach env (X \<union> vns w)"
proof
  fix y assume "y \<in> vreach env' X"
  then obtain x where x: "x \<in> X" "(y, x) \<in> (dep env')\<^sup>*" by (auto simp: vreach_def)
  from x(2) show "y \<in> vreach env (X \<union> vns w)"
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case using x(1) vreach_incl by blast
  next
    case (step y z)
    from step.hyps(1) obtain U u where b: "vt_lookup (tenv env') z = Some (U, u)" and yu: "y \<in> vns u"
      by (auto simp: dep_def)
    show ?case
    proof (cases "z = v")
      case True
      with b assms have "u = w" by simp
      with yu show ?thesis using vreach_incl[of "X \<union> vns w" env] by blast
    next
      case False
      with b assms have "vt_lookup (tenv env) z = Some (U, u)" by simp
      from vreach_step[OF this step.IH] yu show ?thesis by blast
    qed
  qed
qed


subsection \<open>Normalization\<close>

lemma head_norm_vreach_aux:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vns t' \<subseteq> vreach env (vns t)"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vns s' \<subseteq> vreach env (vns s)" if "ok (hn env s) s'" for s s'
    using "1.IH"[OF that(1) refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest have "t' = t" by simp
      then show ?thesis using vreach_incl by blast
    next
      case (Some w)
      from ok_lookup_Some[OF lr[unfolded Some]] obtain U where b: "vt_lookup (tenv env) x = Some (U, w)" .
      from Some rest have "ok (hn env w) t'" by simp
      from IH[OF this] have a: "vns t' \<subseteq> vreach env (vns w)" .
      have "x \<in> vreach env (vns t)" using Var vreach_incl[of "vns t" env] by auto
      from vreach_step[OF b this] have "vns w \<subseteq> vreach env (vns t)" .
      with a show ?thesis using vreach_mono by blast
    qed
  next
    case (Abs a T body)
    with h obtain b' where hb: "ok (hn env body) b'" and e: "t' = Abs a T b'" by auto
    from IH[OF hb] e Abs show ?thesis by simp
  next
    case (App f u)
    have sb: "vns (subst_bound u body) \<subseteq> vreach env (vns t)" if "vns body \<subseteq> vreach env (vns f)" for body
    proof -
      have "vars (subst_bound u body) \<subseteq> vars body \<union> vars u" by (simp add: subst_bound_subst vars_subst)
      then have "vns (subst_bound u body) \<subseteq> vns body \<union> vns u" by blast
      moreover have "vns f \<subseteq> vns t" "vns u \<subseteq> vns t" using App by auto
      moreover have "vreach env (vns f) \<subseteq> vreach env (vns t)" by (rule vreach_subset) fact
      moreover note vreach_incl[of "vns t" env]
      ultimately show ?thesis using that by (meson Un_least order_trans)
    qed
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = Abs a T body" by (cases f) auto
      with h App have hs: "ok (hn env (subst_bound u body)) t'" by simp
      have "vns (subst_bound u body) \<subseteq> vreach env (vns t)" by (rule sb) (use f vreach_incl in auto)
      with IH[OF hs] vreach_mono show ?thesis by blast
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      note IHf = IH[OF nf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = Abs a T body" by (cases nf) auto
        with rest have hs: "ok (hn env (subst_bound u body)) t'" by simp
        have "vns (subst_bound u body) \<subseteq> vreach env (vns t)" by (rule sb) (use IHf nfa in simp)
        with IH[OF hs] vreach_mono show ?thesis by blast
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with IHf App vreach_incl[of "vns t" env] vreach_subset[of "vns f" "vns t" env] show ?thesis by auto
      qed
    qed
  qed (use h in auto)
qed

lemma head_norm_vreach: "ok (head_norm env t) t' \<Longrightarrow> vns t' \<subseteq> vreach env (vns t)"
  using head_norm_vreach_aux[of env t _ t'] by auto

lemma etif_vars_aux:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> vars t' = vars t"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et tye T t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by blast
    with h obtain u where u: "ok (et tye U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u" by auto
    from "1.IH"[OF u refl] t' show ?thesis by (simp add: incr_boundvars_def vars_incr_bv)
  next
    case False
    show ?thesis
    proof (cases T)
      case (Type a Ts)
      with False h have "t' = t" by (auto split: list.splits if_splits)
      then show ?thesis by simp
    next
      case (TVar w S)
      with h obtain r' where r': "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t) t'"
        by auto
      show ?thesis
      proof (cases r')
        case None
        with r' show ?thesis by simp
      next
        case (Some T')
        with r' have "ok (et tye T' t) t'" by simp
        from "1.IH"[OF this refl] show ?thesis .
      qed
    qed (use h in auto)
  qed
qed

lemma eta_norm_etif: "\<not> is_Abs t \<Longrightarrow> ok (eta_norm env rb t) t' \<Longrightarrow> \<exists>U. ok (etif (tyenv env) U t) t'"
  by (cases t) (auto simp: fastype_def)

lemma eta_norm_vars: "ok (eta_norm env rb t) t' \<Longrightarrow> vars t' = vars t"
proof (induction t arbitrary: rb t')
  case (Abs a A body)
  then show ?case by auto
qed (use eta_norm_etif etif_vars_aux in fastforce)+


subsection \<open>Simplification\<close>

definition vdp :: "dpair \<Rightarrow> indexname set" where
  "vdp dp = (case dp of (rb, t, u) \<Rightarrow> vns t \<union> vns u)"

lemma vdp_simp [simp]: "vdp (rb, t, u) = vns t \<union> vns u"
  by (simp add: vdp_def)

abbreviation vdps :: "dpair list \<Rightarrow> indexname set" where
  "vdps dps \<equiv> \<Union> (vdp ` set dps)"

definition vsp :: "sstate \<Rightarrow> indexname set" where
  "vsp st = (case st of (env, ffs, frs) \<Rightarrow> vdps (ffs @ frs))"

lemma vsp_simp [simp]: "vsp (env, ffs, frs) = vdps ffs \<union> vdps frs"
  by (simp add: vsp_def)

text \<open>
  A step from \<open>st\<close> to \<open>st'\<close> on pairs with variables \<open>D\<close>: only variables reachable from \<open>D\<close>
  become reachable or bound, and the variables of the new pairs are reachable from those of the
  old pairs and \<open>D\<close>.
\<close>

definition vsr :: "indexname set \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "vsr D st st' \<longleftrightarrow> (\<forall>X. vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D)) \<and>
    vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D) \<and>
    (\<forall>x. vt_lookup (tenv (fst st')) x \<noteq> None \<longrightarrow> vt_lookup (tenv (fst st)) x = None \<longrightarrow> x \<in> vreach (fst st) D)"

lemma vsrD:
  assumes "vsr D st st'"
  shows "vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D)" "vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D)"
    "vt_lookup (tenv (fst st')) x \<noteq> None \<Longrightarrow> vt_lookup (tenv (fst st)) x = None \<Longrightarrow> x \<in> vreach (fst st) D"
  using assms unfolding vsr_def by blast+

lemma vsr_refl: "vsr D st st"
  unfolding vsr_def using vreach_subset[of _ _ "fst st"] vreach_incl[of _ "fst st"] by blast

lemma vsr_tenv:
  "tenv e1 = tenv e \<Longrightarrow> vsr D (e1, ffs, frs) st' \<longleftrightarrow> vsr D (e, ffs, frs) st'"
  using vreach_tenv[of e1 e] by (simp add: vsr_def)

lemma vsr_trans:
  assumes "vsr D1 st st1" "vsr D2 st1 st2"
  shows "vsr (D1 \<union> D2) st st2"
  unfolding vsr_def
proof (intro conjI allI impI)
  let ?e = "fst st" and ?e1 = "fst st1" and ?e2 = "fst st2"
  fix X
  have "vreach ?e2 X \<subseteq> vreach ?e1 (X \<union> D2)" using assms(2) by (simp add: vsr_def)
  also have "\<dots> \<subseteq> vreach ?e (X \<union> D2 \<union> D1)" using assms(1) by (simp add: vsr_def)
  finally show "vreach ?e2 X \<subseteq> vreach ?e (X \<union> (D1 \<union> D2))" by (simp add: Un_ac)
next
  let ?e = "fst st" and ?e1 = "fst st1" and ?e2 = "fst st2"
  have "vsp st2 \<subseteq> vreach ?e1 (vsp st1 \<union> D2)" using assms(2) by (simp add: vsr_def)
  also have "\<dots> \<subseteq> vreach ?e (vsp st1 \<union> D2 \<union> D1)" using assms(1) by (simp add: vsr_def)
  also have "\<dots> \<subseteq> vreach ?e ((D2 \<union> D1) \<union> (vsp st \<union> D1))"
    using vreach_absorb[of "vsp st1" ?e "vsp st \<union> D1" "D2 \<union> D1"] assms(1) by (simp add: vsr_def Un_ac)
  finally show "vsp st2 \<subseteq> vreach ?e (vsp st \<union> (D1 \<union> D2))" by (simp add: Un_ac)
next
  let ?e = "fst st" and ?e1 = "fst st1" and ?e2 = "fst st2"
  fix x assume b: "vt_lookup (tenv ?e2) x \<noteq> None" and n: "vt_lookup (tenv ?e) x = None"
  show "x \<in> vreach ?e (D1 \<union> D2)"
  proof (cases "vt_lookup (tenv ?e1) x = None")
    case True
    with b assms(2) have "x \<in> vreach ?e1 D2" unfolding vsr_def by blast
    also have "\<dots> \<subseteq> vreach ?e (D2 \<union> D1)" using assms(1) by (simp add: vsr_def)
    finally show ?thesis by (simp add: Un_ac)
  next
    case False
    with n assms(1) have "x \<in> vreach ?e D1" unfolding vsr_def by blast
    then show ?thesis using vreach_subset[of D1 "D1 \<union> D2" ?e] by blast
  qed
qed

lemma vsr_mono:
  assumes "vsr D st st'" "D \<subseteq> vreach (fst st) D'"
  shows "vsr D' st st'"
  unfolding vsr_def
proof (intro conjI allI impI)
  fix X
  show "vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D')"
    using assms(1) vreach_absorb[OF assms(2), of X] by (auto simp: vsr_def)
  show "vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D')"
    using assms(1) vreach_absorb[OF assms(2), of "vsp st"] by (auto simp: vsr_def)
next
  fix x assume "vt_lookup (tenv (fst st')) x \<noteq> None" "vt_lookup (tenv (fst st)) x = None"
  with assms(1) have "x \<in> vreach (fst st) D" unfolding vsr_def by blast
  then show "x \<in> vreach (fst st) D'" using vreach_mono[OF assms(2)] by blast
qed

lemma new_dpair_strip:
  "okW (new_dpair al rb t u env) ((rb', t', u'), env') \<Longrightarrow>
    t' = strip_abs_body t \<and> u' = strip_abs_body u \<and> tenv env' = tenv env"
proof (induction al rb t u env rule: new_dpair.induct)
  case (1 al rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types al T U env) env1"
    and rec: "okW (new_dpair al ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  from "1.IH"[OF cu c_def rec] cunify_types_sound(1)[OF cu] show ?case by simp
qed auto

lemma vars_strip_abs_body [simp]: "vars (strip_abs_body t) = vars t"
  by (induction t) auto

lemma head_norm_dpair_vreach:
  assumes "okW (head_norm_dpair al env dp) (dp', env')"
  shows "vdp dp' \<subseteq> vreach env (vdp dp) \<and> tenv env' = tenv env"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain rb' t' u' where dp': "dp' = (rb', t', u')" by (cases dp')
  from assms obtain t1 t2 u1 u2 where h1: "ok (head_norm env t) t1" and e1: "ok (eta_norm env rb t1) t2"
    and h2: "ok (head_norm env u) u1" and e2: "ok (eta_norm env rb u1) u2"
    and nd: "okW (new_dpair al rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def dp dp')
  note s = new_dpair_strip[OF nd]
  have "vns t' \<subseteq> vreach env (vns t)" using head_norm_vreach[OF h1] eta_norm_vars[OF e1] s by simp
  moreover have "vns u' \<subseteq> vreach env (vns u)" using head_norm_vreach[OF h2] eta_norm_vars[OF e2] s by simp
  ultimately show ?thesis
    using vreach_subset[of "vns t" "vns t \<union> vns u" env] vreach_subset[of "vns u" "vns t \<union> vns u" env] s
    by (auto simp: dp dp')
qed

lemma mc_vars_rlist_abs [simp]: "vars (rlist_abs rb t) = vars t"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma vars_head_of: "vars (head_of t) \<subseteq> vars t"
  by (induction t) auto

lemma get_eta_var_head: "okW (get_eta_var bs n t) (v, T) \<Longrightarrow> head_of t = Var v T"
  using get_eta_var_app[of bs n t v T] by (simp add: app_apps head_of_apps')

lemma assignment_vreach:
  assumes "okW (assignment al rb t u env) env'"
  shows "vreach env' X \<subseteq> vreach env (X \<union> vns u)"
    "vt_lookup (tenv env') x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> vns t"
proof -
  from assms obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types al T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where cu: "okW (cunify_types al T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have te: "tenv env' = vt_update (v, (T, rlist_abs rb u)) (tenv env)"
    using ok_update(2)[OF upd] cunify_types_sound(1)[OF cu] by simp
  from vreach_update[OF te] show "vreach env' X \<subseteq> vreach env (X \<union> vns u)" by simp
  assume "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None"
  with te have "x = v" by (auto split: if_splits)
  moreover have "(v, T) \<in> vars t"
    using get_eta_var_head[OF gev] vars_head_of[of t] by auto
  ultimately show "x \<in> vns t" by force
qed


lemma okW_ASSIGN_ret: "okW (case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

lemma okW_assign_handle:
  assumes "okW (handleW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)})
    (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e)) st'"
  shows "(\<exists>env'. okW (assignment al rb t u env) env' \<and> st' = (env', ffs, frs)) \<or> st' = x"
proof -
  from assms[unfolded okW_handleW] consider
    (a) "okW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)}) st'"
  | (b) e where "okW (case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) st'"
    by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis by auto
  next
    case b
    from okW_ASSIGN_ret[OF b] show ?thesis by simp
  qed
qed

lemma simrands_vreach:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> vsr (vdp dp) st st') \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> vsr (vns t \<union> vns u) st st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  have v1: "vsr (vns f1 \<union> vns g1) st st1" by (rule "1.IH"[OF "1.prems"(1) r])
  have v2: "vsr (vns t \<union> vns u) st1 st'" using "1.prems"(1)[OF s] by simp
  from vsr_trans[OF v1 v2] show ?case by (simp add: Un_ac image_Un)
qed (auto intro: vsr_refl)

lemma SIMPL0_rest_vreach:
  assumes F: "\<And>dp st st'. okW (S al dp st) st' \<Longrightarrow> vsr (vdp dp) st st'"
    and ok: "okW (SIMPL0_rest S al rb t u env ffs frs) st'"
  shows "vsr (vns t \<union> vns u) (env, ffs, frs) st'"
proof -
  let ?D = "vns t \<union> vns u"
  have keep: "vsr ?D (env, ffs, frs) (env', ffs', frs')"
    if "tenv env' = tenv env" "vsp (env', ffs', frs') \<subseteq> vsp (env, ffs, frs) \<union> ?D" for env' ffs' frs'
    unfolding vsr_def fst_conv
  proof (intro conjI allI impI)
    fix X
    show "vreach env' X \<subseteq> vreach env (X \<union> ?D)"
      unfolding vreach_tenv[OF that(1)] by (rule vreach_subset) blast
    show "vsp (env', ffs', frs') \<subseteq> vreach env (vsp (env, ffs, frs) \<union> ?D)"
      using that(2) vreach_incl[of "vsp (env, ffs, frs) \<union> ?D" env] by blast
  next
    fix x assume "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None"
    with that(1) show "x \<in> vreach env ?D" by simp
  qed
  have asg: "vsr ?D (env, ffs, frs) (env', ffs, frs)" if "okW (assignment al rb s s' env) env'"
    "s = t \<and> s' = u \<or> s = u \<and> s' = t" for env' s s'
    unfolding vsr_def
  proof (intro conjI allI impI)
    note a = assignment_vreach[OF that(1)]
    fix X
    show "vreach (fst (env', ffs, frs)) X \<subseteq> vreach (fst (env, ffs, frs)) (X \<union> ?D)"
      using a(1)[of X] that(2) vreach_subset[of "X \<union> vns s'" "X \<union> ?D" env] by auto
    show "vsp (env', ffs, frs) \<subseteq> vreach (fst (env, ffs, frs)) (vsp (env, ffs, frs) \<union> ?D)"
      using vreach_incl[of "vsp (env, ffs, frs) \<union> ?D" env] by auto
  next
    fix x assume "vt_lookup (tenv (fst (env', ffs, frs))) x \<noteq> None" "vt_lookup (tenv (fst (env, ffs, frs))) x = None"
    with assignment_vreach(2)[OF that(1)] have "x \<in> vns s" by simp
    with that(2) show "x \<in> vreach (fst (env, ffs, frs)) ?D" using vreach_incl[of ?D env] by auto
  qed
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok obtain T' U' env' where cu: "okW (cunify_types al T' U' env) env'"
      and st': "st' = (env', (rb, t, u) # ffs, frs)"
      by (auto simp: SIMPL0_rest_def)
    show ?thesis unfolding st' by (rule keep[OF cunify_types_sound(1)[OF cu]]) auto
  next
    case VR
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    from okW_assign_handle[OF h] show ?thesis
    proof
      assume "\<exists>env'. okW (assignment al rb t u env) env' \<and> st' = (env', ffs, frs)"
      then obtain env' where "okW (assignment al rb t u env) env'" "st' = (env', ffs, frs)" by blast
      with asg show ?thesis by blast
    next
      assume "st' = (env, ffs, (rb, t, u) # frs)"
      then show ?thesis by (simp only:) (rule keep, auto)
    qed
  next
    case RV
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    from okW_assign_handle[OF h] show ?thesis
    proof
      assume "\<exists>env'. okW (assignment al rb u t env) env' \<and> st' = (env', ffs, frs)"
      then obtain env' where "okW (assignment al rb u t env) env'" "st' = (env', ffs, frs)" by blast
      with asg show ?thesis by blast
    next
      assume "st' = (env, ffs, (rb, u, t) # frs)"
      then show ?thesis by (simp only:) (rule keep, auto)
    qed
  next
    case RR
    have ct: "tenv env' = tenv env" if "cunify_types al T U env = Some (evs, UOk env')" for T U evs env'
      using that by (intro cunify_types_sound(1)) blast
    from ok RR obtain env1 where e1: "tenv env1 = tenv env"
      and sr: "okW (simrands (S al) rb u t u (env1, ffs, frs)) st'"
      by (cases "head_of t"; cases "head_of u") (auto simp: SIMPL0_rest_def split: if_splits dest: ct)
    from simrands_vreach[OF F sr] show ?thesis by (simp add: vsr_tenv[OF e1])
  qed
qed

theorem SIMPL0_vreach:
  assumes "SIMPL0 al dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vsr (vdp dp0) st st'"
  using assms
proof (induction al dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S al dp0 st r)
  have IH: "vsr (vdp dp) st1 st2" if "okW (S al dp st1) st2" for dp st1 st2
  proof -
    from that obtain evs where "S al dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  have "\<exists>rb t u env1. okW (head_norm_dpair al env dp0) ((rb, t, u), env1) \<and>
      okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] st by (auto simp: SIMPL0_rest_def split: prod.splits)
  then obtain rb t u env1 where hnd: "okW (head_norm_dpair al env dp0) ((rb, t, u), env1)"
    and step: "okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    by blast
  note hd = head_norm_dpair_vreach[OF hnd]
  have e1: "tenv env1 = tenv env" using hd by simp
  from SIMPL0_rest_vreach[OF IH step] have "vsr (vns t \<union> vns u) (env1, ffs, frs) st'" .
  then have "vsr (vdp (rb, t, u)) (env, ffs, frs) st'" unfolding vsr_tenv[OF e1] by simp
  from vsr_mono[OF this] hd st show ?case by simp
qed

corollary SIMPL0_vreach': "okW (SIMPL0 al dp st) st' \<Longrightarrow> vsr (vdp dp) st st'"
  using SIMPL0_vreach by fastforce

lemma foldrW_SIMPL0_vreach: "okW (foldrW (SIMPL0 al) dps st) st' \<Longrightarrow> vsr (vdps dps) st st'"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 al) dps st) st1"
    and s: "okW (SIMPL0 al dp st1) st'" by auto
  from vsr_trans[OF Cons.IH[OF f] SIMPL0_vreach'[OF s]] show ?case by (simp add: Un_ac)
qed (simp add: vsr_refl)

theorem SIMPL_vreach:
  assumes "SIMPL al env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vsr (vdps dpairs) (env, [], []) st'"
  using assms
proof (induction al env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S al env dpairs r)
  have "\<exists>env1 ffs frs. okW (foldrW (SIMPL0 al) dpairs (env, [], [])) (env1, ffs, frs) \<and>
      (okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs))"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs frs where f: "okW (foldrW (SIMPL0 al) dpairs (env, [], [])) (env1, ffs, frs)"
    and r: "okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by blast
  have v1: "vsr (vdps dpairs) (env, [], []) (env1, ffs, frs)" by (rule foldrW_SIMPL0_vreach[OF f])
  show ?case
  proof (cases "okW (S al env1 (frs @ ffs)) st'")
    case True
    then obtain evs where "S al env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    from "1.IH"[OF this] have v2: "vsr (vdps (frs @ ffs)) (env1, [], []) st'" by simp
    have sub: "vdps (frs @ ffs) \<subseteq> vreach env (vdps dpairs)" using v1 by (auto simp: vsr_def)
    show ?thesis
      unfolding vsr_def
    proof (intro conjI allI impI)
      fix X
      have "vreach (fst st') X \<subseteq> vreach env1 (X \<union> vdps (frs @ ffs))" using v2 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env (X \<union> vdps (frs @ ffs) \<union> vdps dpairs)" using v1 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env ((X \<union> vdps dpairs) \<union> vdps dpairs)"
        using vreach_absorb[OF sub, of "X \<union> vdps dpairs"] by (simp add: Un_ac)
      finally show "vreach (fst st') X \<subseteq> vreach (fst (env, [], [])) (X \<union> vdps dpairs)" by simp
      have "vsp st' \<subseteq> vreach env1 (vdps (frs @ ffs))" using v2 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env (vdps (frs @ ffs) \<union> vdps dpairs)" using v1 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env (vdps dpairs \<union> vdps dpairs)"
        using vreach_absorb[OF sub, of "vdps dpairs"] by (simp add: Un_ac)
      finally show "vsp st' \<subseteq> vreach (fst (env, [], [])) (vsp (env, [], []) \<union> vdps dpairs)" by simp
    next
      fix x assume b: "vt_lookup (tenv (fst st')) x \<noteq> None" and n: "vt_lookup (tenv (fst (env, [], []))) x = None"
      show "x \<in> vreach (fst (env, [], [])) (vdps dpairs)"
      proof (cases "vt_lookup (tenv env1) x = None")
        case True
        with b v2 have "x \<in> vreach env1 (vdps (frs @ ffs))" unfolding vsr_def fst_conv by blast
        also have "\<dots> \<subseteq> vreach env (vdps (frs @ ffs) \<union> vdps dpairs)" using v1 by (simp add: vsr_def)
        also have "\<dots> \<subseteq> vreach env (vdps dpairs \<union> vdps dpairs)"
          using vreach_absorb[OF sub, of "vdps dpairs"] by (simp add: Un_ac)
        finally show ?thesis by simp
      next
        case False
        with n v1 show ?thesis unfolding vsr_def fst_conv by blast
      qed
    qed
  next
    case False
    with r v1 show ?thesis by simp
  qed
qed

corollary SIMPL_vreach': "okW (SIMPL al env dps) st' \<Longrightarrow> vsr (vdps dps) (env, [], []) st'"
  using SIMPL_vreach by fastforce



subsection \<open>Dead occurrences\<close>

text \<open>
  \<open>dd F b t\<close>: every occurrence of a variable of \<open>F\<close> in \<open>t\<close> is applied to an argument that is not
  a bound variable, where \<open>b\<close> tells whether the arguments that \<open>t\<close> itself is applied to
  contain one.
\<close>

fun dd :: "indexname set \<Rightarrow> bool \<Rightarrow> pterm \<Rightarrow> bool" where
  "dd F b (f $ a) \<longleftrightarrow> dd F (b \<or> \<not> is_Bound a) f \<and> dd F False a"
| "dd F b (Var y T) \<longleftrightarrow> (y \<in> F \<longrightarrow> b)"
| "dd F b (Abs n T t) \<longleftrightarrow> dd F False t"
| "dd F b _ \<longleftrightarrow> True"

abbreviation dead :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "dead F t \<equiv> dd F False t"

lemma dd_mono: "dd F b t \<Longrightarrow> b \<le> b' \<Longrightarrow> dd F b' t"
  by (induction F b t arbitrary: b' rule: dd.induct) (auto simp: le_bool_def)

lemma dd_True: "dead F t \<Longrightarrow> dd F b t"
  using dd_mono[of F False t b] by simp

lemma dd_list_comb:
  "dd F b (list_comb h ts) \<longleftrightarrow> dd F (b \<or> (\<exists>t\<in>set ts. \<not> is_Bound t)) h \<and> (\<forall>t\<in>set ts. dead F t)"
  by (induction ts arbitrary: h b) (auto simp: list_comb_def intro: dd_mono)

lemma is_Bound_incr_bv [simp]: "is_Bound (incr_bv i k t) \<longleftrightarrow> is_Bound t"
  by (cases "(i, k, t)" rule: incr_bv.cases) auto

lemma dd_incr_bv [simp]: "dd F b (incr_bv i k t) \<longleftrightarrow> dd F b t"
  by (induction i k t arbitrary: b rule: incr_bv.induct) auto

lemma dd_incr_boundvars [simp]: "dd F b (incr_boundvars i t) \<longleftrightarrow> dd F b t"
  by (simp add: incr_boundvars_def)

lemma is_Bound_subst_bound_aux: "\<not> is_Bound t \<Longrightarrow> \<not> is_Bound (subst_bound_aux u k t)"
  by (cases "(u, k, t)" rule: subst_bound_aux.cases) auto

lemma dd_subst_bound_aux: "dead F u \<Longrightarrow> dd F b t \<Longrightarrow> dd F b (subst_bound_aux u k t)"
proof (induction u k t arbitrary: b rule: subst_bound_aux.induct)
  case (3 u k t1 t2)
  have "dd F (b \<or> \<not> is_Bound t2) (subst_bound_aux u k t1)" using 3 by simp
  then have "dd F (b \<or> \<not> is_Bound (subst_bound_aux u k t2)) (subst_bound_aux u k t1)"
    by (rule dd_mono) (auto simp: le_bool_def dest: is_Bound_subst_bound_aux)
  with 3 show ?case by simp
qed (auto intro: dd_True)

lemma dd_subst_bound: "dead F u \<Longrightarrow> dd F b t \<Longrightarrow> dd F b (subst_bound u t)"
  by (simp add: subst_bound_def dd_subst_bound_aux)


subsection \<open>Variables at the head only\<close>

text \<open>\<open>hok F t\<close>: the variables of \<open>F\<close> occur in \<open>t\<close> at most as its head, applied to terms without them.\<close>

fun hok :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "hok F (f $ a) \<longleftrightarrow> hok F f \<and> vns a \<inter> F = {}"
| "hok F (Var y T) \<longleftrightarrow> True"
| "hok F t \<longleftrightarrow> vns t \<inter> F = {}"

fun gs :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "gs F (Abs n T t) \<longleftrightarrow> gs F t"
| "gs F t \<longleftrightarrow> hok F t"

lemma hok_free: "vns t \<inter> F = {} \<Longrightarrow> hok F t"
  by (induction F t rule: hok.induct) auto

lemma gs_free: "vns t \<inter> F = {} \<Longrightarrow> gs F t"
  by (induction F t rule: gs.induct) (auto intro: hok_free)

lemma hok_list_comb: "hok F (list_comb h ts) \<longleftrightarrow> hok F h \<and> (\<forall>t\<in>set ts. vns t \<inter> F = {})"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma hok_nonVar: "hok F t \<Longrightarrow> \<not> is_Var (head_of t) \<Longrightarrow> vns t \<inter> F = {}"
  by (induction F t rule: hok.induct) auto

lemma hok_incr_bv: "hok F (incr_bv i k t) \<longleftrightarrow> hok F t"
  by (induction i k t rule: incr_bv.induct) (auto simp: vars_incr_bv)

lemma gs_incr_bv: "gs F (incr_bv i k t) \<longleftrightarrow> gs F t"
  by (induction i k t rule: incr_bv.induct) (auto simp: vars_incr_bv hok_incr_bv)


subsection \<open>Environments\<close>

text \<open>
  The values of the environment have only dead occurrences of \<open>Fd\<close> and none of \<open>Ft\<close>, and the
  variables of \<open>Fd\<close> are unbound.
\<close>

definition vgood :: "indexname set \<Rightarrow> indexname set \<Rightarrow> env \<Rightarrow> bool" where
  "vgood Fd Ft env \<longleftrightarrow>
    (\<forall>x U w. vt_lookup (tenv env) x = Some (U, w) \<longrightarrow> x \<notin> Fd \<and> dead Fd w \<and> vns w \<inter> Ft = {})"

lemma vgoodD:
  "vgood Fd Ft env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, w) \<Longrightarrow> x \<notin> Fd \<and> dead Fd w \<and> vns w \<inter> Ft = {}"
  unfolding vgood_def by blast

lemma vgood_tenv: "tenv env' = tenv env \<Longrightarrow> vgood Fd Ft env' \<longleftrightarrow> vgood Fd Ft env"
  by (simp add: vgood_def)


subsection \<open>Head normalization\<close>

lemma disj_sub3: "A \<subseteq> B \<union> C \<Longrightarrow> B \<inter> F = {} \<and> C \<inter> F = {} \<Longrightarrow> A \<inter> F = {}"
  by blast

lemma head_norm_good_aux:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow>
    (dd Fd b t \<longrightarrow> dd Fd b t') \<and> (vns t \<inter> Ft = {} \<longrightarrow> vns t' \<inter> Ft = {}) \<and> (hok Ft t \<longrightarrow> hok Ft t')"
  using assms
proof (induction env t r arbitrary: t' b rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note vg = "1.prems"(2)
  have IH: "(dd Fd b' s \<longrightarrow> dd Fd b' s') \<and> (vns s \<inter> Ft = {} \<longrightarrow> vns s' \<inter> Ft = {}) \<and>
      (hok Ft s \<longrightarrow> hok Ft s')" if "ok (hn env s) s'" for s s' b'
    using "1.IH"[OF that refl vg] .
  show ?case
  proof (cases t)
    case (Var xi T)
    with h obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest show ?thesis by simp
    next
      case (Some w)
      from ok_lookup_Some[OF lk[unfolded Some]] obtain U where "vt_lookup (tenv env) xi = Some (U, w)" .
      from vgoodD[OF vg this] have w: "dead Fd w" "vns w \<inter> Ft = {}" by simp_all
      from Some rest have "ok (hn env w) t'" by simp
      from IH[OF this, of b] w show ?thesis by (auto intro: dd_True hok_free)
    qed
  next
    case (Abs a T body)
    with h obtain b' where hb: "ok (hn env body) b'" and e: "t' = Abs a T b'" by auto
    from IH[OF hb, of False] e Abs show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = Abs a T body" by (cases f) auto
      with h App have hs: "ok (hn env (subst_bound u body)) t'" by simp
      have "vars (subst_bound u body) \<subseteq> vars body \<union> vars u" by (simp add: subst_bound_subst vars_subst)
      then have v: "vns (subst_bound u body) \<subseteq> vns body \<union> vns u" by blast
      note ih = IH[OF hs, of b]
      have d: "dd Fd b t'" if "dd Fd b t" using that ih App f by (auto intro: dd_subst_bound dd_True)
      have bu: "vns body \<inter> Ft = {} \<and> vns u \<inter> Ft = {}" if "hok Ft t \<or> vns t \<inter> Ft = {}"
        using that App f by auto
      have fr: "vns t' \<inter> Ft = {}" if "hok Ft t \<or> vns t \<inter> Ft = {}"
      proof -
        from bu[OF that]
        have "vns (subst_bound u body) \<inter> Ft = {}" using disj_sub3[OF v] by blast
        with ih show ?thesis by (simp only: simp_thms)
      qed
      show ?thesis
      proof (intro conjI impI)
        show "dd Fd b t'" if "dd Fd b t" using d that .
        show "vns t' \<inter> Ft = {}" if "vns t \<inter> Ft = {}" by (rule fr[OF disjI2[OF that]])
        show "hok Ft t'" if "hok Ft t" by (rule hok_free[OF fr[OF disjI1[OF that]]])
      qed
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      note IHf = IH[OF nf, of "b \<or> \<not> is_Bound u"]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = Abs a T body" by (cases nf) auto
        with rest have hs: "ok (hn env (subst_bound u body)) t'" by simp
        have "vars (subst_bound u body) \<subseteq> vars body \<union> vars u" by (simp add: subst_bound_subst vars_subst)
        then have v: "vns (subst_bound u body) \<subseteq> vns body \<union> vns u" by blast
        note ih = IH[OF hs, of b]
        have d: "dd Fd b t'" if "dd Fd b t" using that ih IHf App nfa by (auto intro: dd_subst_bound dd_True)
        have "hok Ft f \<and> vns u \<inter> Ft = {}" if "hok Ft t \<or> vns t \<inter> Ft = {}"
          using that App by (auto intro: hok_free)
        then have bu: "vns body \<inter> Ft = {} \<and> vns u \<inter> Ft = {}" if "hok Ft t \<or> vns t \<inter> Ft = {}"
          using that IHf nfa by simp
        have fr: "vns t' \<inter> Ft = {}" if "hok Ft t \<or> vns t \<inter> Ft = {}"
        proof -
          from bu[OF that]
          have "vns (subst_bound u body) \<inter> Ft = {}" using disj_sub3[OF v] by blast
          with ih show ?thesis by (simp only: simp_thms)
        qed
        show ?thesis
      proof (intro conjI impI)
        show "dd Fd b t'" if "dd Fd b t" using d that .
        show "vns t' \<inter> Ft = {}" if "vns t \<inter> Ft = {}" by (rule fr[OF disjI2[OF that]])
        show "hok Ft t'" if "hok Ft t" by (rule hok_free[OF fr[OF disjI1[OF that]]])
      qed
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with IHf App show ?thesis by auto
      qed
    qed
  qed (use h in auto)
qed

lemma head_norm_good:
  assumes "ok (head_norm env t) t'" "vgood Fd Ft env"
  shows "dd Fd b t \<Longrightarrow> dd Fd b t'" "vns t \<inter> Ft = {} \<Longrightarrow> vns t' \<inter> Ft = {}" "hok Ft t \<Longrightarrow> hok Ft t'"
  using head_norm_good_aux[of env t _ t' Fd Ft b] assms by auto


subsection \<open>Rigid sides\<close>

text \<open>\<open>rrs F t\<close>: \<open>t\<close> is a rigid atom applied to arguments that have \<open>F\<close> at their heads only.\<close>

fun rrs :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "rrs F (f $ a) \<longleftrightarrow> rrs F f \<and> gs F a"
| "rrs F (Const c T) \<longleftrightarrow> True"
| "rrs F (Free c T) \<longleftrightarrow> True"
| "rrs F (Bound i) \<longleftrightarrow> True"
| "rrs F _ \<longleftrightarrow> False"

lemma rrs_incr_bv: "rrs F (incr_bv i k t) \<longleftrightarrow> rrs F t"
  by (induction F t arbitrary: k rule: rrs.induct) (auto simp: gs_incr_bv)

lemma rrs_nonAbs: "rrs F t \<Longrightarrow> \<not> is_Abs t"
  by (cases t) auto

lemma rrs_head_norm: "rrs F t \<Longrightarrow> head_norm env t = return t"
proof (induction F t rule: rrs.induct)
  case (1 F f a)
  then have hf: "head_norm env f = return f" by simp
  have "\<not> is_Abs f" using "1.prems" by (cases f) auto
  with hf show ?case by (subst head_norm.simps) (cases f; simp add: return_def)
qed (simp_all add: head_norm.simps return_def)

lemma gs_nonAbs: "\<not> is_Abs t \<Longrightarrow> gs F t \<longleftrightarrow> hok F t"
  by (cases t) auto

lemma hok_gs: "hok F t \<Longrightarrow> gs F t"
  by (cases t) (auto intro: gs_free)

lemma dead_strip_abs_body: "dead F t \<Longrightarrow> dead F (strip_abs_body t)"
  by (induction t) auto

lemma gs_strip_abs_body: "gs F (strip_abs_body t) \<longleftrightarrow> gs F t"
  by (induction t) auto

lemma is_Abs_strip_abs_body: "\<not> is_Abs (strip_abs_body t)"
  by (induction t) auto


subsection \<open>\<open>\<eta>\<close>-expansion\<close>

lemma etif_good_aux:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> \<not> is_Abs t \<Longrightarrow>
    (dead Fd t \<longrightarrow> dead Fd t') \<and> (gs Ft t \<longrightarrow> gs Ft t') \<and> (rrs Ft t \<longrightarrow> rrs Ft (strip_abs_body t'))"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et tye T t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note nA = "1.prems"(2)
  have same: "(dead Fd t \<longrightarrow> dead Fd t) \<and> (gs Ft t \<longrightarrow> gs Ft t) \<and> (rrs Ft t \<longrightarrow> rrs Ft (strip_abs_body t))"
    using nA by (cases t) auto
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by blast
    with h obtain u where u: "ok (et tye U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u" by auto
    from "1.IH"[OF u refl] have
      "dead Fd (incr_boundvars 1 t $ Bound 0) \<longrightarrow> dead Fd u"
      "gs Ft (incr_boundvars 1 t $ Bound 0) \<longrightarrow> gs Ft u"
      "rrs Ft (incr_boundvars 1 t $ Bound 0) \<longrightarrow> rrs Ft (strip_abs_body u)"
      by simp_all
    moreover have "gs Ft (incr_boundvars 1 t $ Bound 0) \<longleftrightarrow> gs Ft t"
      using nA by (simp add: gs_nonAbs incr_boundvars_def hok_incr_bv)
    ultimately show ?thesis using t' by (simp add: incr_boundvars_def rrs_incr_bv)
  next
    case False
    show ?thesis
    proof (cases T)
      case (Type a Ts)
      with False h have "t' = t" by (auto split: list.splits if_splits)
      with same show ?thesis by simp
    next
      case (TVar w S)
      with h obtain r' where r': "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t) t'"
        by auto
      show ?thesis
      proof (cases r')
        case None
        with r' same show ?thesis by simp
      next
        case (Some T')
        with r' have "ok (et tye T' t) t'" by simp
        from "1.IH"[OF this refl nA] show ?thesis .
      qed
    qed (use h same in auto)
  qed
qed

lemma eta_norm_good:
  "ok (eta_norm env rb t) t' \<Longrightarrow>
    (dead Fd t \<longrightarrow> dead Fd t') \<and> (gs Ft t \<longrightarrow> gs Ft t') \<and> (rrs Ft t \<longrightarrow> rrs Ft (strip_abs_body t'))"
proof (induction env rb t arbitrary: t' rule: eta_norm.induct)
  case (1 env rb a A body)
  then show ?case by (auto dest: rrs_nonAbs)
qed (auto dest!: etif_good_aux[OF _ refl] simp: fastype_def)


subsection \<open>Pairs\<close>

text \<open>
  A pair is good if its sides have only dead occurrences of \<open>Fd\<close>, and both have \<open>Ft\<close> at
  their heads only, or both are rigid with such arguments.
\<close>

definition pgood :: "indexname set \<Rightarrow> indexname set \<Rightarrow> dpair \<Rightarrow> bool" where
  "pgood Fd Ft dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    dead Fd t \<and> dead Fd u \<and> (gs Ft t \<and> gs Ft u \<or> rrs Ft t \<and> rrs Ft u))"

lemma head_norm_Abs_ok:
  "ok (head_norm env (Abs a T b)) t' \<Longrightarrow> \<exists>b'. t' = Abs a T b' \<and> ok (head_norm env b) b'"
  by (subst (asm) head_norm.simps) auto

lemma head_norm_gs: "ok (head_norm env t) t' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow> gs Ft t \<Longrightarrow> gs Ft t'"
proof (induction t arbitrary: t')
  case (Abs a T b)
  from head_norm_Abs_ok[OF Abs.prems(1)] obtain b' where "t' = Abs a T b'" "ok (head_norm env b) b'" by blast
  with Abs show ?case by simp
qed (auto simp: gs_nonAbs intro: hok_gs dest: head_norm_good(3))

lemma head_norm_dpair_good:
  assumes "okW (head_norm_dpair al env dp) (dp', env')" "vgood Fd Ft env" "pgood Fd Ft dp"
  shows "pgood Fd Ft dp' \<and> tenv env' = tenv env"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain rb' t' u' where dp': "dp' = (rb', t', u')" by (cases dp')
  from assms(1) obtain t1 t2 u1 u2 where h1: "ok (head_norm env t) t1" and e1: "ok (eta_norm env rb t1) t2"
    and h2: "ok (head_norm env u) u1" and e2: "ok (eta_norm env rb u1) u2"
    and nd: "okW (new_dpair al rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def dp dp')
  note s = new_dpair_strip[OF nd]
  note et = eta_norm_good[OF e1, of Fd Ft] eta_norm_good[OF e2, of Fd Ft]
  have g: "dead Fd t" "dead Fd u" "gs Ft t \<and> gs Ft u \<or> rrs Ft t \<and> rrs Ft u"
    using assms(3) by (auto simp: pgood_def dp)
  have d: "dead Fd t'" "dead Fd u'"
    using head_norm_good(1)[OF h1 assms(2) g(1)] head_norm_good(1)[OF h2 assms(2) g(2)] et s
    by (auto intro: dead_strip_abs_body)
  from g(3) have "gs Ft t' \<and> gs Ft u' \<or> rrs Ft t' \<and> rrs Ft u'"
  proof
    assume "gs Ft t \<and> gs Ft u"
    with head_norm_gs[OF h1 assms(2)] head_norm_gs[OF h2 assms(2)] et s
    show ?thesis by (simp add: gs_strip_abs_body)
  next
    assume r: "rrs Ft t \<and> rrs Ft u"
    then have "t1 = t" "u1 = u" using h1 h2 by (auto simp: rrs_head_norm return_def)
    with r et s show ?thesis by simp
  qed
  with d s dp' show ?thesis by (simp add: pgood_def)
qed


subsection \<open>Simplification keeps the new variables good\<close>

definition sgood :: "indexname set \<Rightarrow> indexname set \<Rightarrow> sstate \<Rightarrow> bool" where
  "sgood Fd Ft st \<longleftrightarrow> (case st of (env, ffs, frs) \<Rightarrow>
    vgood Fd Ft env \<and> (\<forall>dp\<in>set (ffs @ frs). pgood Fd Ft dp))"

lemma get_eta_var_dead: "okW (get_eta_var rb n t) (v, T) \<Longrightarrow> dead F t \<Longrightarrow> v \<notin> F"
proof (induction rb arbitrary: n t)
  case Nil
  then show ?case by (cases t) auto
next
  case (Cons aT rb)
  from Cons.prems(1) obtain f where t: "t = f $ Bound n"
    and rec: "okW (get_eta_var rb (n + 1) f) (v, T)"
    by (cases "(aT # rb, n, t)" rule: get_eta_var.cases) (auto split: if_splits)
  with Cons.IH[OF rec] Cons.prems(2) show ?case by simp
qed

lemma dd_rlist_abs: "dead F t \<Longrightarrow> dead F (rlist_abs rb t)"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma assignment_good:
  assumes "okW (assignment al rb t u env) env'" "vgood Fd Ft env" "dead Fd t" "dead Fd u"
    "vns u \<inter> Ft = {}"
  shows "vgood Fd Ft env'"
proof -
  from assms(1) obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types al T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where cu: "okW (cunify_types al T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have "tenv env' = vt_update (v, (T, rlist_abs rb u)) (tenv env)"
    using ok_update(2)[OF upd] cunify_types_sound(1)[OF cu] by simp
  moreover have "v \<notin> Fd" by (rule get_eta_var_dead[OF gev assms(3)])
  ultimately show ?thesis
    using assms(2,4,5) dd_rlist_abs[OF assms(4), of rb]
    by (auto simp: vgood_def)
qed

text \<open>The arguments of rigid sides, for \<^const>\<open>simrands\<close>:\<close>

fun hargs :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "hargs F (f $ a) \<longleftrightarrow> hargs F f \<and> gs F a"
| "hargs F _ \<longleftrightarrow> True"

lemma hargs_free: "vns t \<inter> F = {} \<Longrightarrow> hargs F t"
  by (induction t) (auto intro: gs_free)

lemma rrs_hargs: "rrs F t \<Longrightarrow> hargs F t"
  by (induction F t rule: rrs.induct) auto

lemma simrands_good:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st') \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow>
    dd Fd True t \<Longrightarrow> dd Fd True u \<Longrightarrow> hargs Ft t \<Longrightarrow> hargs Ft u \<Longrightarrow> sgood Fd Ft st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  note F = "1.prems"(1)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  from "1.IH"[OF F r "1.prems"(3)] "1.prems"(4-7) have "sgood Fd Ft st1" by simp
  moreover have "pgood Fd Ft (rb, t, u)" using "1.prems"(4-7) by (simp add: pgood_def)
  ultimately show ?case by (rule F[OF s])
qed auto

lemma SIMPL0_rest_good:
  assumes F: "\<And>dp st st'. okW (S al dp st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
    and ok: "okW (SIMPL0_rest S al rb t u env ffs frs) st'"
    and sg: "sgood Fd Ft (env, ffs, frs)" and pg: "pgood Fd Ft (rb, t, u)"
    and nA: "\<not> is_Abs t" "\<not> is_Abs u"
  shows "sgood Fd Ft st'"
proof -
  have vg: "vgood Fd Ft env" using sg by (simp add: sgood_def)
  have d: "dead Fd t" "dead Fd u" and g: "gs Ft t \<and> gs Ft u \<or> rrs Ft t \<and> rrs Ft u"
    using pg by (auto simp: pgood_def)
  have rr_V: "\<not> rrs Ft s" if "is_Var (head_of s)" for s
    using that by (induction Ft s rule: rrs.induct) auto
  have free: "vns s \<inter> Ft = {}" if "gs Ft s" "\<not> is_Abs s" "\<not> is_Var (head_of s)" for s
    using hok_nonVar[of Ft s] that by (simp add: gs_nonAbs)
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok obtain T' U' env' where cu: "okW (cunify_types al T' U' env) env'"
      and st': "st' = (env', (rb, t, u) # ffs, frs)"
      by (auto simp: SIMPL0_rest_def)
    with sg pg show ?thesis by (simp add: sgood_def vgood_tenv[OF cunify_types_sound(1)[OF cu]])
  next
    case VR
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    have fu: "vns u \<inter> Ft = {}" using g rr_V[of t] VR free[of u] nA by auto
    from okW_assign_handle[OF h] show ?thesis
    proof
      assume "\<exists>env'. okW (assignment al rb t u env) env' \<and> st' = (env', ffs, frs)"
      then obtain env' where a: "okW (assignment al rb t u env) env'" "st' = (env', ffs, frs)" by blast
      from assignment_good[OF a(1) vg d fu] a(2) sg show ?thesis by (simp add: sgood_def)
    qed (use sg pg in \<open>simp add: sgood_def\<close>)
  next
    case RV
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    have ft: "vns t \<inter> Ft = {}" using g rr_V[of u] RV free[of t] nA by auto
    have pg': "pgood Fd Ft (rb, u, t)" using pg by (auto simp: pgood_def)
    from okW_assign_handle[OF h] show ?thesis
    proof
      assume "\<exists>env'. okW (assignment al rb u t env) env' \<and> st' = (env', ffs, frs)"
      then obtain env' where a: "okW (assignment al rb u t env) env'" "st' = (env', ffs, frs)" by blast
      from assignment_good[OF a(1) vg d(2,1) ft] a(2) sg show ?thesis by (simp add: sgood_def)
    qed (use sg pg' in \<open>simp add: sgood_def\<close>)
  next
    case RR
    have hs: "hargs Ft t" "hargs Ft u"
      using g free[of t] free[of u] RR nA by (auto intro: hargs_free rrs_hargs)
    have ct: "tenv env' = tenv env" if "cunify_types al T U env = Some (evs, UOk env')" for T U evs env'
      using that by (intro cunify_types_sound(1)) blast
    from ok RR obtain env1 where e1: "tenv env1 = tenv env"
      and sr: "okW (simrands (S al) rb u t u (env1, ffs, frs)) st'"
      by (cases "head_of t"; cases "head_of u") (auto simp: SIMPL0_rest_def split: if_splits dest: ct)
    have "sgood Fd Ft (env1, ffs, frs)" using sg by (simp add: sgood_def vgood_tenv[OF e1])
    from simrands_good[OF F sr this dd_True[OF d(1)] dd_True[OF d(2)] hs] show ?thesis .
  qed
qed

theorem SIMPL0_good:
  assumes "SIMPL0 al dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp0 \<Longrightarrow> sgood Fd Ft st'"
  using assms
proof (induction al dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S al dp0 st r)
  have IH: "sgood Fd Ft st2" if "okW (S al dp st1) st2" "sgood Fd Ft st1" "pgood Fd Ft dp" for dp st1 st2
  proof -
    from that(1) obtain evs where "S al dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this _ that(2,3)] show ?thesis by simp
  qed
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  have "\<exists>rb t u env1. okW (head_norm_dpair al env dp0) ((rb, t, u), env1) \<and>
      okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] st by (auto simp: SIMPL0_rest_def split: prod.splits)
  then obtain rb t u env1 where hnd: "okW (head_norm_dpair al env dp0) ((rb, t, u), env1)"
    and step: "okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    by blast
  have vg: "vgood Fd Ft env" using "1.prems"(2) st by (simp add: sgood_def)
  note hg = head_norm_dpair_good[OF hnd vg "1.prems"(3)]
  have nA: "\<not> is_Abs t" "\<not> is_Abs u"
  proof -
    obtain rb0 t0 u0 where dp0: "dp0 = (rb0, t0, u0)" by (cases dp0)
    from hnd obtain t2 u2 where "okW (new_dpair al rb0 t2 u2 env) ((rb, t, u), env1)"
      by (auto simp: head_norm_dpair_def dp0)
    from new_dpair_strip[OF this] show "\<not> is_Abs t" "\<not> is_Abs u"
      by (simp_all add: is_Abs_strip_abs_body)
  qed
  have "sgood Fd Ft (env1, ffs, frs)"
    using "1.prems"(2) st hg by (simp add: sgood_def vgood_tenv[OF hg[THEN conjunct2]])
  from SIMPL0_rest_good[OF IH step this hg[THEN conjunct1] nA]
  show ?case .
qed

corollary SIMPL0_good':
  "okW (SIMPL0 al dp st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
  using SIMPL0_good by fastforce

lemma foldrW_SIMPL0_good:
  "okW (foldrW (SIMPL0 al) dps st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> \<forall>dp\<in>set dps. pgood Fd Ft dp \<Longrightarrow>
    sgood Fd Ft st'"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 al) dps st) st1"
    and s: "okW (SIMPL0 al dp st1) st'" by auto
  from Cons.IH[OF f Cons.prems(2)] Cons.prems(3) have "sgood Fd Ft st1" by simp
  from SIMPL0_good'[OF s this] Cons.prems(3) show ?case by simp
qed simp

theorem SIMPL_good:
  assumes "SIMPL al env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow> \<forall>dp\<in>set dpairs. pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
  using assms
proof (induction al env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S al env dpairs r)
  have "\<exists>env1 ffs frs. okW (foldrW (SIMPL0 al) dpairs (env, [], [])) (env1, ffs, frs) \<and>
      (okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs))"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs frs where f: "okW (foldrW (SIMPL0 al) dpairs (env, [], [])) (env1, ffs, frs)"
    and r: "okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by blast
  have "sgood Fd Ft (env, [], [])" using "1.prems"(2) by (simp add: sgood_def)
  from foldrW_SIMPL0_good[OF f this "1.prems"(3)] have g1: "sgood Fd Ft (env1, ffs, frs)" .
  show ?case
  proof (cases "okW (S al env1 (frs @ ffs)) st'")
    case True
    then obtain evs where "S al env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    from "1.IH"[OF this] g1 show ?thesis by (auto simp: sgood_def)
  next
    case False
    with r g1 show ?thesis by simp
  qed
qed

corollary SIMPL_good':
  "okW (SIMPL al env dps) st' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow> \<forall>dp\<in>set dps. pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
  using SIMPL_good by fastforce



subsection \<open>Counting rigid atoms\<close>

text \<open>
  The measure of a term is the number of constants and free variables of the \<open>\<beta>\<close>-normal form of
  its unfolding. It does not depend on types, and \<open>\<eta>\<close>-expansion does not change it.
\<close>

fun rcnt :: "pterm \<Rightarrow> nat" where
  "rcnt (Const c T) = 1"
| "rcnt (Free x T) = 1"
| "rcnt (s $ t) = rcnt s + rcnt t"
| "rcnt (Abs a T t) = rcnt t"
| "rcnt (Var x T) = 0"
| "rcnt (Bound i) = 0"

lemma rcnt_incr_bv [simp]: "rcnt (incr_bv n k t) = rcnt t"
  by (induction n k t rule: incr_bv.induct) auto

lemma rcnt_subst: "rcnt s = 0 \<Longrightarrow> rcnt (t[s/k]) = rcnt t"
  by (induction t arbitrary: s k) (auto simp: subst_Bound)

lemma rcnt_inst [simp]: "rcnt (inst \<rho> t) = rcnt t"
  by (induction t) auto

lemma rcnt_apps: "rcnt (h \<degree>\<degree> ts) = rcnt h + sum_list (map rcnt ts)"
  by (induction ts arbitrary: h) simp_all

definition rsz :: "env \<Rightarrow> pterm \<Rightarrow> nat" where
  "rsz env t = rcnt (bnorm (unf env t))"

lemma no_redex_inst [simp]: "no_redex (inst \<rho> t) \<longleftrightarrow> no_redex t"
proof (induction t)
  case (App s t)
  then show ?case by (cases s) auto
qed auto

lemma bnorm_inst: "termip beta t \<Longrightarrow> bnorm (inst \<rho> t) = inst \<rho> (bnorm t)"
  using bnorm[of t] by (intro bnorm_eqI) (auto simp: inst_reds)

lemma rsz_inst: "termip beta (inst \<rho> (unf env t)) \<Longrightarrow> rsz env t = rcnt (bnorm (inst \<rho> (unf env t)))"
  using bnorm_inst[OF termip_inst[OF _ refl]] by (simp add: rsz_def)

lemma rsz_typed: "e \<turnstile> inst \<rho> (unf env t) : T \<Longrightarrow> rsz env t = rcnt (bnorm (inst \<rho> (unf env t)))"
  by (rule rsz_inst[OF type_implies_termi])

lemma termip_typed_unf: "e \<turnstile> inst \<rho> (unf env t) : T \<Longrightarrow> termip beta (unf env t)"
  by (rule termip_inst[OF type_implies_termi refl])

lemma rsz_head_norm:
  assumes "ok (head_norm env t) t'" "acyc env" "closed_env env" "termip beta (unf env t)"
  shows "rsz env t' = rsz env t"
proof -
  have "unf env t \<rightarrow>\<^sub>\<beta>\<^sup>* unf env t'" using head_norm_unf[of env t "Ok t'" t'] assms(1-3) by auto
  from bnorm_reds[OF assms(4) this] show ?thesis by (simp add: rsz_def)
qed

lemma rsz_Abs: "termip beta (unf env (Abs a T b)) \<Longrightarrow> rsz env (Abs a T b) = rsz env b"
  by (simp add: rsz_def bnorm_Abs)

lemma lift_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> lift s 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift t 0"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma rcnt_bnorm_eta:
  assumes sn: "termip beta s"
  shows "rcnt (bnorm (lift s 0 $ Bound 0)) = rcnt (bnorm s)"
proof -
  from bnorm[OF sn] have r: "s \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm s" and n: "no_redex (bnorm s)" by blast+
  have l: "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift (bnorm s) 0 $ Bound 0"
    by (rule rtrancl_beta_AppL[OF lift_reds[OF r]])
  show ?thesis
  proof (cases "is_Abs (bnorm s)")
    case True
    then obtain a A b where nb: "bnorm s = Abs a A b" by (cases "bnorm s") auto
    have "lift (bnorm s) 0 $ Bound 0 = Abs a A (incr_bv 1 1 b) $ Bound 0" by (simp add: nb)
    then have "lift (bnorm s) 0 $ Bound 0 \<rightarrow>\<^sub>\<beta> (incr_bv 1 1 b)[Bound 0/0]" by (simp only:) (rule beta.beta)
    moreover have "(incr_bv 1 1 b)[Bound 0/0] = b" by simp
    ultimately have "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* b" using l by (metis rtranclp.rtrancl_into_rtrancl)
    moreover have "no_redex b" using n nb by simp
    ultimately have "bnorm (lift s 0 $ Bound 0) = b" by (rule bnorm_eqI)
    then show ?thesis using nb by simp
  next
    case False
    then have "\<not> is_Abs (lift (bnorm s) 0)" by (cases "bnorm s") auto
    then have "no_redex (lift (bnorm s) 0 $ Bound 0)" using n by (simp add: no_redex_lift)
    from bnorm_eqI[OF l this] show ?thesis by simp
  qed
qed

text \<open>The arguments of an imitation have smaller measures:\<close>

lemma rsz_rigid_arg:
  assumes h: "h = Const c C \<or> h = Free c C" and ty: "e \<turnstile> inst \<rho> (unf env (h \<degree>\<degree> ts)) : T"
    and t: "t \<in> set ts"
  shows "rsz env t < rsz env (h \<degree>\<degree> ts)"
proof -
  let ?xs = "map (inst \<rho> \<circ> unf env) ts"
  have i: "inst \<rho> (unf env (h \<degree>\<degree> ts)) = inst \<rho> h \<degree>\<degree> ?xs"
    using h by (auto simp: unf_apps inst_apps)
  have at: "atom (inst \<rho> h)" using h by auto
  have b: "bnorm (inst \<rho> h \<degree>\<degree> ?xs) = inst \<rho> h \<degree>\<degree> map bnorm ?xs"
    by (rule bnorm_atom_apps[OF at ty[unfolded i]])
  have rh: "rcnt h = 1" using h by auto
  from typing_args[OF ty[unfolded i], of "inst \<rho> (unf env t)"] t obtain U where
    tyt: "e \<turnstile> inst \<rho> (unf env t) : U" by auto
  have "rcnt (bnorm (inst \<rho> (unf env t))) \<le> sum_list (map rcnt (map bnorm ?xs))"
    using t by (intro member_le_sum_list) auto
  then show ?thesis
    using rsz_typed[OF ty] rsz_typed[OF tyt] by (simp add: i b rcnt_apps rh)
qed

text \<open>Unfolding in an extension that keeps the reachable unbound variables unbound:\<close>

lemma unf_cong_vars:
  "(\<And>y T. (y, T) \<in> vars t \<Longrightarrow> unf env' (Var y T) = unf env (Var y T)) \<Longrightarrow> unf env' t = unf env t"
  by (induction t) auto

lemma unf_ext:
  assumes ac: "acyc env" and ac': "acyc env'" and ext: "extends env env'"
    and H: "\<And>y. y \<in> vreach env (vns t) \<Longrightarrow> vt_lookup (tenv env) y = None \<Longrightarrow> vt_lookup (tenv env') y = None"
  shows "unf env' t = unf env t"
proof -
  have V: "(\<forall>y\<in>vreach env {x}. vt_lookup (tenv env) y = None \<longrightarrow> vt_lookup (tenv env') y = None) \<longrightarrow>
    unf env' (Var x T) = unf env (Var x T)" for x T
  proof (induction x arbitrary: T rule: dep_induct[OF ac])
    case (1 x)
    show ?case
    proof (intro impI)
      assume Hx: "\<forall>y\<in>vreach env {x}. vt_lookup (tenv env) y = None \<longrightarrow> vt_lookup (tenv env') y = None"
      show "unf env' (Var x T) = unf env (Var x T)"
      proof (cases "vt_lookup (tenv env) x")
        case None
        with Hx vreach_incl[of "{x}" env] have "vt_lookup (tenv env') x = None" by blast
        with None show ?thesis by (simp add: unf_Var[OF ac] unf_Var[OF ac'])
      next
        case (Some b)
        obtain U u where b: "b = (U, u)" by force
        have b': "vt_lookup (tenv env') x = Some (U, u)" using extends_lookup[OF ext Some] b by simp
        have "unf env' u = unf env u"
        proof (rule unf_cong_vars)
          fix y T' assume yu: "(y, T') \<in> vars u"
          have d: "(y, x) \<in> dep env" by (rule depI[OF Some[unfolded b] yu])
          have "vreach env {y} \<subseteq> vreach env {x}"
            using d by (auto simp: vreach_def intro: rtrancl_into_rtrancl)
          with Hx have "\<forall>z\<in>vreach env {y}. vt_lookup (tenv env) z = None \<longrightarrow> vt_lookup (tenv env') z = None"
            by blast
          with "1.IH"[OF d] show "unf env' (Var y T') = unf env (Var y T')" by blast
        qed
        then show ?thesis using Some b b' by (simp add: unf_Var[OF ac] unf_Var[OF ac'])
      qed
    qed
  qed
  show ?thesis
  proof (rule unf_cong_vars)
    fix y T assume yt: "(y, T) \<in> vars t"
    have "vreach env {y} \<subseteq> vreach env (vns t)" using yt by (intro vreach_subset) force
    with H V[of y T] show "unf env' (Var y T) = unf env (Var y T)" by blast
  qed
qed

lemma rsz_ext:
  assumes "acyc env" "acyc env'" "extends env env'"
    "\<And>y. y \<in> vreach env (vns t) \<Longrightarrow> vt_lookup (tenv env) y = None \<Longrightarrow> vt_lookup (tenv env') y = None"
  shows "rsz env' t = rsz env t"
  using unf_ext[OF assms] by (simp add: rsz_def)

text \<open>\<open>\<eta>\<close>-expansion does not change the measure:\<close>

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

lemma rsz_etif:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> ok (etif \<theta> T t) t' \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : tnorm \<theta> T \<and> rsz env t' = rsz env t"
proof -
  let ?\<rho> = "tnorm_inst \<theta>"
  assume tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<forall>t t' e. ok (etif \<theta> T t) t' \<longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> T \<and> rsz env t' = rsz env t"
  proof (induction rule: tnorm_induct[OF ti_ac[OF ti] ti_tc[OF ti], consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst etif.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (intro allI impI)
      fix t t' e
      assume ok: "ok (etif \<theta> (Type a Ts) t) t'" and c: "cert_typ alg ar (tnorm \<theta> (Type a Ts))"
        and ty: "e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> (Type a Ts)"
      show "e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> (Type a Ts) \<and> rsz env t' = rsz env t"
      proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
        case True
        then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
        let ?t = "incr_boundvars 1 t $ Bound 0"
        from ok Ts a obtain u where u: "ok (etif \<theta> U ?t) u" and t': "t' = Abs STR '''' T1 u"
          by (subst (asm) etif.simps) auto
        from c Ts a have c1: "cert_typ alg ar (tnorm \<theta> T1)" and c2: "cert_typ alg ar (tnorm \<theta> U)"
          by (simp_all add: cert_typ_fun)
        have ty1: "e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U" using ty Ts a by simp
        have "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> lift (inst ?\<rho> (unf env t)) 0 : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U"
          by (rule lift_type[OF ty1]) simp
        then have tyt: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unf env ?t) : tnorm \<theta> U"
          by (simp only: inst_unf_incr[OF ac cl]) (rule typing.App, auto)
        from Type(1)[of U] Ts u c2 tyt
        have IH: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unf env u) : tnorm \<theta> U" "rsz env u = rsz env ?t"
          by auto
        have tyt': "e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> (Type a Ts)" using IH(1) c1 t' Ts a by auto
        have "rsz env t' = rsz env u"
          by (rule rsz_Abs[OF termip_typed_unf[OF tyt'[unfolded t']], folded t'])
        also have "\<dots> = rsz env t"
        proof -
          have "unf env ?t = lift (unf env t) 0 $ Bound 0"
            by (simp add: incr_boundvars_1 unf_lift[OF ac cl])
          then have "rsz env ?t = rcnt (bnorm (unf env t))"
            using rcnt_bnorm_eta[OF termip_typed_unf[OF ty]] by (simp add: rsz_def)
          with IH(2) show ?thesis by (simp add: rsz_def)
        qed
        finally show ?thesis using tyt' by blast
      next
        case False
        with ok have "t' = t" by (subst (asm) etif.simps) (auto split: list.splits)
        with ty show ?thesis by simp
      qed
    qed
  next
    case (Unbound v S)
    then show ?case by (subst etif.simps) (simp add: type_lookup_ok)
  next
    case (Bound v S U)
    then show ?case by (subst etif.simps) (simp add: type_lookup_ok tnorm_TVar[OF ti_ac[OF ti]])
  qed
  then show "ok (etif \<theta> T t) t' \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> T \<and> rsz env t' = rsz env t"
    using tinv_tcons[OF ti tv] by blast
qed

lemma rsz_eta_norm_nonAbs:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env" and nA: "\<not> is_Abs t"
    and ok: "ok (eta_norm env bs t) t'" and ty: "e \<turnstile> inst (tnorm_inst \<theta>) t : T" and bs: "bs_env (tnorm_inst \<theta>) e bs"
    and lb: "\<not> loose_bvar t (ilength bs)" and tv: "ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A"
    and tyu: "e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : T"
  shows "e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : T \<and> rsz env t' = rsz env t"
proof -
  from ok nA obtain T0 where T0: "ok (fastype env bs t) T0" and et: "ok (etif \<theta> T0 t) t'"
    by (auto simp: eta_norm_nonAbs th)
  have "tsubst (tnorm_inst \<theta>) T0 = T"
    by (rule fastype_sound[OF T0 _ bs ty]) (simp add: th tsol_tnorm[OF ti_ac[OF ti]])
  then have tT: "tnorm \<theta> T0 = T" by simp
  from env_fastype_term[OF ti th ty bs lb tv] T0 have tv0: "tvars T0 \<subseteq> tvars_env \<theta> \<union> A"
    by (auto simp: fastype_def return_def)
  have c: "cert_typ alg ar T" by (rule bs_env_cert[OF bs ty lb])
  from rsz_etif[OF th ac cl tv0 et _ tyu[folded tT]] c tT show ?thesis by simp
qed

lemma rsz_eta_norm:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "ok (eta_norm env bs t) t' \<Longrightarrow> e \<turnstile> inst (tnorm_inst \<theta>) t : T \<Longrightarrow> bs_env (tnorm_inst \<theta>) e bs \<Longrightarrow>
    \<not> loose_bvar t (ilength bs) \<Longrightarrow> ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : T \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : T \<and> rsz env t' = rsz env t"
proof (induction t arbitrary: e T bs t')
  case (Abs a B0 b)
  let ?\<rho> = "tnorm_inst \<theta>"
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, B0) # bs) b) b'" and t': "t' = Abs a B0 b'" by auto
  from Abs.prems(2) obtain W where c: "cert_typ alg ar (tsubst ?\<rho> B0)"
    and tb: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> b : W" and T: "T = tsubst ?\<rho> B0 \<rightarrow>\<^sub>T W"
    by auto
  from Abs.prems(6) T have tbu: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unf env b) : W" by auto
  have lb: "\<not> loose_bvar b (ilength ((a, B0) # bs))" using Abs.prems(4) by (simp add: algebra_simps)
  have tv: "ttvars b \<union> btvars ((a, B0) # bs) \<subseteq> tvars_env \<theta> \<union> A" using Abs.prems(5) by (auto simp: btvars_def)
  from Abs.IH[OF b' tb bs_env_Cons[OF Abs.prems(3) c] lb tv tbu]
  have IH: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unf env b') : W" "rsz env b' = rsz env b"
    by blast+
  have ty': "e \<turnstile> inst ?\<rho> (unf env t') : T" using IH(1) c T t' by auto
  show ?case
    using ty' rsz_Abs[OF termip_typed_unf[OF ty'[unfolded t']]] rsz_Abs[OF termip_typed_unf[OF Abs.prems(6)]]
      IH(2) t' by simp
qed (rule rsz_eta_norm_nonAbs[OF th ac cl], simp, assumption+)+

end



subsection \<open>The invariants of the copies\<close>

abbreviation vnsl :: "pterm list \<Rightarrow> indexname set" where
  "vnsl ts \<equiv> \<Union> (vns ` set ts)"

text \<open>
  The variables up to index \<open>m0\<close> are those of the original problem, and the ones it can reach
  are among the finite set \<open>S0\<close>; the measure counts its unbound ones (\<open>pmu\<close>). The new variables
  are dead (\<open>Fd\<close>) or occur at heads only (\<open>Ft\<close>), according to the arguments of the flexible side
  (\<open>ptok\<close>).
\<close>

definition pmu :: "indexname set \<Rightarrow> env \<Rightarrow> nat" where
  "pmu S0 env = card {x\<in>S0. vt_lookup (tenv env) x = None}"

definition poldin :: "integer \<Rightarrow> indexname set \<Rightarrow> env \<Rightarrow> indexname set \<Rightarrow> bool" where
  "poldin m0 S0 env Y \<longleftrightarrow> (\<forall>y\<in>vreach env Y. snd y \<le> m0 \<longrightarrow> y \<in> S0)"

definition psh :: "indexname set \<Rightarrow> indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "psh Fd Ft t \<longleftrightarrow> dead Fd t \<and> vns t \<inter> Ft = {}"

definition ptok :: "indexname set \<Rightarrow> indexname set \<Rightarrow> pterm list \<Rightarrow> bool" where
  "ptok Fd Ft targs \<longleftrightarrow> (Fd \<noteq> {} \<longrightarrow> (\<exists>t\<in>set targs. \<not> is_Bound t)) \<and> (Ft \<noteq> {} \<longrightarrow> (\<forall>t\<in>set targs. is_Bound t))"

text \<open>The context of a copy: the problem, the binders, and the arguments \<open>targs\<close> of types \<open>Tts\<close>.\<close>

definition cpre :: "indexname set \<Rightarrow> indexname set \<Rightarrow> integer \<Rightarrow> (indexname \<times> psort) set \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow>
    ptyp list \<Rightarrow> bool" where
  "cpre Fd Ft m0 A K X env dps rb targs Tts \<longleftrightarrow> finite X \<and> finite K \<and> sinv A K X env dps \<and>
    vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    (\<forall>t\<in>set targs. pok A env rb X t t \<and> psh Fd Ft t) \<and> length Tts = length targs \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow>
      (\<forall>e. bs_env \<rho> e rb \<longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Tts)) \<and>
    vgood Fd Ft env \<and> (\<forall>dp\<in>set dps. pgood Fd Ft dp) \<and> ptok Fd Ft targs \<and> m0 \<le> maxidx env"

text \<open>The term to copy:\<close>

definition upre :: "indexname set \<Rightarrow> indexname set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "upre Fd Ft A X env rb u \<longleftrightarrow> pok A env rb X u u \<and> psh Fd Ft u"

text \<open>Its type is the result type of its head, after its abstractions (it is \<open>\<eta>\<close>-long at the top):\<close>

definition sat :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "sat env rb u \<longleftrightarrow> (\<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) u : U \<and> nabs u = arity U)"

text \<open>
  The result of a copy: a new problem in the invariant, which extends the old one; only the old
  variables reachable from \<open>D\<close> and the new variables \<open>NV\<close> become reachable or bound.
\<close>

definition cres :: "indexname set \<Rightarrow> indexname set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> indexname set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> indexname set \<Rightarrow> bool" where
  "cres Fd Ft A X env D A' K' X' env' dps' NV \<longleftrightarrow> finite X' \<and> finite K' \<and> A \<subseteq> A' \<and> X \<subseteq> X' \<and>
    sinv A' K' X' env' dps' \<and> vtvars X' \<subseteq> tvars_env (tyenv env') \<union> A' \<and>
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    (\<forall>y\<in>NV. maxidx env < snd y) \<and> (\<forall>Y. vreach env' Y \<subseteq> vreach env (Y \<union> D) \<union> NV) \<and>
    vdps dps' \<subseteq> vreach env D \<union> NV \<and>
    {x. vt_lookup (tenv env') x \<noteq> None \<and> vt_lookup (tenv env) x = None} \<subseteq> vreach env D \<union> NV \<and>
    vgood Fd Ft env' \<and> (\<forall>dp\<in>set dps'. pgood Fd Ft dp)"

text \<open>A copy \<open>c\<close> of \<open>u\<close>: its variables are new, and it has the type of \<open>u\<close> under the arguments.\<close>

definition cpy :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> indexname set \<Rightarrow>
    binders \<Rightarrow> pterm \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> bool" where
  "cpy A' X' env' NV rb u Tts c \<longleftrightarrow> vns c \<subseteq> NV \<and> vars c \<subseteq> X' \<union> evars env' \<and>
    ttvars c \<subseteq> tvars_env (tyenv env') \<union> A' \<and> \<not> loose_bvar c (ilength Tts) \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<forall>e U. bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> c : U)))"

text \<open>The elements of the sequences of copies of a term and of argument lists:\<close>

definition PEC :: "indexname set \<Rightarrow> indexname set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> indexname set \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> ptyp list \<Rightarrow> elem \<Rightarrow> bool" where
  "PEC Fd Ft A X env D rb u Tts x \<longleftrightarrow> (\<exists>c env' dps' A' K' X' NV. x = El_C c env' dps' \<and>
    cres Fd Ft A X env D A' K' X' env' dps' NV \<and> cpy A' X' env' NV rb u Tts c)"

definition PED :: "indexname set \<Rightarrow> indexname set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> indexname set \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> elem \<Rightarrow> bool" where
  "PED Fd Ft A X env D rb us Tts x \<longleftrightarrow> (\<exists>cs env' dps' A' K' X' NV. x = El_D cs env' dps' \<and>
    cres Fd Ft A X env D A' K' X' env' dps' NV \<and> list_all2 (\<lambda>a c. cpy A' X' env' NV rb a Tts c) us cs)"

lemma cpreD:
  assumes "cpre Fd Ft m0 A K X env dps rb targs Tts"
  shows "finite X" "finite K" "sinv A K X env dps" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    "btvars rb \<subseteq> tvars_env (tyenv env) \<union> A" "\<And>t. t \<in> set targs \<Longrightarrow> pok A env rb X t t \<and> psh Fd Ft t"
    "length Tts = length targs"
    "\<And>\<rho> e. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Tts"
    "vgood Fd Ft env" "\<And>dp. dp \<in> set dps \<Longrightarrow> pgood Fd Ft dp" "ptok Fd Ft targs" "m0 \<le> maxidx env"
  using assms unfolding cpre_def by blast+

lemma cresD:
  assumes "cres Fd Ft A X env D A' K' X' env' dps' NV"
  shows "finite X'" "finite K'" "A \<subseteq> A'" "X \<subseteq> X'" "sinv A' K' X' env' dps'"
    "vtvars X' \<subseteq> tvars_env (tyenv env') \<union> A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd y"
    "\<And>Y. vreach env' Y \<subseteq> vreach env (Y \<union> D) \<union> NV" "vdps dps' \<subseteq> vreach env D \<union> NV"
    "\<And>x. vt_lookup (tenv env') x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> vreach env D \<union> NV"
    "vgood Fd Ft env'" "\<And>dp. dp \<in> set dps' \<Longrightarrow> pgood Fd Ft dp"
proof -
  note c = assms[unfolded cres_def]
  show "finite X'" "finite K'" "A \<subseteq> A'" "X \<subseteq> X'" "sinv A' K' X' env' dps'"
    "vtvars X' \<subseteq> tvars_env (tyenv env') \<union> A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "vdps dps' \<subseteq> vreach env D \<union> NV" "vgood Fd Ft env'"
    using c by simp_all
  show "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd y" "\<And>Y. vreach env' Y \<subseteq> vreach env (Y \<union> D) \<union> NV"
    "\<And>dp. dp \<in> set dps' \<Longrightarrow> pgood Fd Ft dp" using c by simp_all
  fix x assume "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None"
  then have "x \<in> {x. vt_lookup (tenv env') x \<noteq> None \<and> vt_lookup (tenv env) x = None}" by simp
  with c show "x \<in> vreach env D \<union> NV" by (elim conjE) (erule subsetD)
qed

lemma cresI:
  assumes "finite X'" "finite K'" "A \<subseteq> A'" "X \<subseteq> X'" "sinv A' K' X' env' dps'"
    "vtvars X' \<subseteq> tvars_env (tyenv env') \<union> A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd y"
    "\<And>Y. vreach env' Y \<subseteq> vreach env (Y \<union> D) \<union> NV" "vdps dps' \<subseteq> vreach env D \<union> NV"
    "\<And>x. vt_lookup (tenv env') x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> vreach env D \<union> NV"
    "vgood Fd Ft env'" "\<And>dp. dp \<in> set dps' \<Longrightarrow> pgood Fd Ft dp"
  shows "cres Fd Ft A X env D A' K' X' env' dps' NV"
proof -
  have "{x. vt_lookup (tenv env') x \<noteq> None \<and> vt_lookup (tenv env) x = None} \<subseteq> vreach env D \<union> NV"
    using assms(12) by blast
  with assms show ?thesis unfolding cres_def by (simp only: Ball_def) blast
qed

lemma cpyD:
  assumes "cpy A' X' env' NV rb u Tts c"
  shows "vns c \<subseteq> NV" "vars c \<subseteq> X' \<union> evars env'" "ttvars c \<subseteq> tvars_env (tyenv env') \<union> A'"
    "\<not> loose_bvar c (ilength Tts)"
    "\<And>\<rho> e U e'. tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> c : U"
  using assms unfolding cpy_def by blast+

lemma vreach_fresh:
  assumes bb: "bbelow env" and NV: "\<forall>y\<in>NV. maxidx env < snd y"
  shows "vreach env NV = NV"
proof
  show "vreach env NV \<subseteq> NV"
  proof
    fix y assume "y \<in> vreach env NV"
    then obtain x where x: "x \<in> NV" "(y, x) \<in> (dep env)\<^sup>*" by (auto simp: vreach_def)
    have "vt_lookup (tenv env) x = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env) x \<noteq> None"
      then obtain b where "vt_lookup (tenv env) x = Some b" by blast
      from bbelowD[OF bb this] NV x(1) show False by fastforce
    qed
    from rtrancl_dep_unbound[OF this x(2)] x(1) show "y \<in> NV" by simp
  qed
  show "NV \<subseteq> vreach env NV" by (rule vreach_incl)
qed

lemma sinv_bbelow: "sinv A K X env dps \<Longrightarrow> bbelow env"
  unfolding sinv_def using einvD(5) by blast

lemma set_lem1: "a \<subseteq> b \<union> n \<union> c \<Longrightarrow> b \<subseteq> c \<Longrightarrow> a \<union> u \<union> d \<subseteq> (u \<union> c \<union> d) \<union> n"
  by blast

lemma set_lem2: "x \<subseteq> d \<union> n \<Longrightarrow> y \<union> x \<subseteq> (y \<union> d) \<union> n"
  by blast

lemma vtvars_Un: "vtvars (X \<union> Y) = vtvars X \<union> vtvars Y"
  by (auto simp: vtvars_def)

lemma cres_refl:
  assumes "finite X" "finite K" "sinv A K X env dps" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    "vgood Fd Ft env" "\<forall>dp\<in>set dps. pgood Fd Ft dp" "vdps dps \<subseteq> D"
  shows "cres Fd Ft A X env D A K X env dps {}"
  unfolding cres_def using assms vreach_incl[of D env] vreach_subset[of _ _ env]
  by (auto simp: vreach_Un)

lemma cres_mono:
  assumes c: "cres Fd Ft A X env D A' K' X' env' dps' NV" and D: "D \<subseteq> vreach env D'"
  shows "cres Fd Ft A X env D' A' K' X' env' dps' NV"
proof -
  note r = vreach_absorb[OF D] and m = vreach_mono[OF D]
  have "vreach env' Y \<subseteq> vreach env (Y \<union> D') \<union> NV" for Y
    using cresD(10)[OF c, of Y] r[of Y] by (meson Un_mono order_refl order_trans)
  moreover have "vdps dps' \<subseteq> vreach env D' \<union> NV"
    using cresD(11)[OF c] m by (meson Un_mono order_refl order_trans)
  moreover have "x \<in> vreach env D' \<union> NV" if "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None" for x
    using cresD(12)[OF c that] m by (meson UnCI UnE subsetD)
  ultimately show ?thesis using cresD[OF c] by (intro cresI) auto
qed

lemma cres_trans:
  assumes c1: "cres Fd Ft A X env D A1 K1 X1 env1 dps1 NV1" and c2: "cres Fd Ft A1 X1 env1 D1 A2 K2 X2 env2 dps2 NV2"
    and bb: "bbelow env" and D: "D1 \<subseteq> vreach env D \<union> NV1"
  shows "cres Fd Ft A X env D A2 K2 X2 env2 dps2 (NV1 \<union> NV2)"
proof -
  note a = cresD[OF c1] and b = cresD[OF c2]
  have nv1: "vreach env NV1 = NV1" using vreach_fresh[OF bb] a(9) by blast
  have rD1: "vreach env D1 \<subseteq> vreach env D \<union> NV1"
    using vreach_mono[of D1 env "D \<union> NV1"] D vreach_incl[of "D \<union> NV1" env] nv1
    by (auto simp: vreach_Un)
  have r: "vreach env2 Y \<subseteq> vreach env (Y \<union> D) \<union> (NV1 \<union> NV2)" for Y
  proof -
    have "vreach env2 Y \<subseteq> vreach env1 (Y \<union> D1) \<union> NV2" by (rule b(10))
    also have "\<dots> \<subseteq> vreach env (Y \<union> D1 \<union> D) \<union> NV1 \<union> NV2" using a(10)[of "Y \<union> D1"] by blast
    also have "\<dots> \<subseteq> vreach env (Y \<union> D) \<union> (NV1 \<union> NV2)" using rD1 by (auto simp: vreach_Un)
    finally show ?thesis .
  qed
  have v: "vdps dps2 \<subseteq> vreach env D \<union> (NV1 \<union> NV2)"
  proof -
    have "vdps dps2 \<subseteq> vreach env1 D1 \<union> NV2" by (rule b(11))
    also have "\<dots> \<subseteq> vreach env (D1 \<union> D) \<union> NV1 \<union> NV2" using a(10)[of D1] by blast
    also have "\<dots> \<subseteq> vreach env D \<union> (NV1 \<union> NV2)" using rD1 by (auto simp: vreach_Un)
    finally show ?thesis .
  qed
  have bn: "x \<in> vreach env D \<union> (NV1 \<union> NV2)"
    if x: "vt_lookup (tenv env2) x \<noteq> None" "vt_lookup (tenv env) x = None" for x
  proof (cases "vt_lookup (tenv env1) x = None")
    case True
    from b(12)[OF x(1) True] have "x \<in> vreach env1 D1 \<union> NV2" .
    moreover have "vreach env1 D1 \<subseteq> vreach env (D1 \<union> D) \<union> NV1" by (rule a(10))
    ultimately show ?thesis using rD1 by (auto simp: vreach_Un)
  next
    case False
    from a(12)[OF False x(2)] show ?thesis by blast
  qed
  have ny: "maxidx env < snd y" if "y \<in> NV1 \<union> NV2" for y
    using that a(9)[of y] b(9)[of y] a(7) by (auto simp: extends_def)
  show ?thesis
  proof (rule cresI)
    show "extends env env2" by (rule extends_trans[OF a(7) b(7)])
    show "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" using a(8) b(8) by (rule order_trans)
    show "A \<subseteq> A2" using a(3) b(3) by (rule order_trans)
    show "X \<subseteq> X2" using a(4) b(4) by (rule order_trans)
  qed (use b(1,2,5,6,13,14) r v bn ny in auto)
qed

lemma pok_ext:
  assumes "pok A env rb X s t" "cres Fd Ft A X env D A' K' X' env' dps' NV"
  shows "pok A' env' rb X' s t"
proof -
  note c = cresD[OF assms(2)]
  have "pok A' env rb X s t" by (rule pok_Amono[OF assms(1) c(3)])
  then have "pok A' env' rb X s t" by (rule pok_mono[OF _ c(7,8)])
  then show ?thesis by (rule pok_Xmono[OF _ c(4,6)])
qed

lemma cpre_ext:
  assumes cp: "cpre Fd Ft m0 A K X env dps rb targs Tts" and c: "cres Fd Ft A X env D A' K' X' env' dps' NV"
  shows "cpre Fd Ft m0 A' K' X' env' dps' rb targs Tts"
proof -
  note a = cpreD[OF cp] and b = cresD[OF c]
  have "\<forall>t\<in>set targs. pok A' env' rb X' t t \<and> psh Fd Ft t" using a(6) pok_ext[OF _ c] by blast
  moreover have "btvars rb \<subseteq> tvars_env (tyenv env') \<union> A'" using a(5) b(3,8) by blast
  moreover have "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Tts"
    if "tsol (tyenv env') \<rho>" "cert_inst \<rho>" "bs_env \<rho> e rb" for \<rho> e
    using a(8)[OF extends_tsol[OF that(1) b(7)] that(2,3)] .
  moreover have "m0 \<le> maxidx env'" using a(12) b(7) by (auto simp: extends_def)
  ultimately show ?thesis using a(7,11) b(1,2,5,6,13,14) unfolding cpre_def by blast
qed

lemma upre_ext:
  "upre Fd Ft A X env rb u \<Longrightarrow> cres Fd Ft A X env D A' K' X' env' dps' NV \<Longrightarrow> upre Fd Ft A' X' env' rb u"
  unfolding upre_def using pok_ext by blast

lemma cpy_ext:
  assumes cp: "cpy A1 X1 env1 NV1 rb u Tts c" and cr: "cres Fd Ft A1 X1 env1 D A2 K2 X2 env2 dps2 NV2"
    and NV: "NV1 \<subseteq> NV"
  shows "cpy A2 X2 env2 NV rb u Tts c"
proof -
  note a = cpyD[OF cp] and b = cresD[OF cr]
  have "vars c \<subseteq> X2 \<union> evars env2" using a(2) b(4) evars_extends[OF b(7)] by blast
  moreover have "ttvars c \<subseteq> tvars_env (tyenv env2) \<union> A2" using a(3) b(3,8) by blast
  moreover have "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> c : U"
    if "tsol (tyenv env2) \<rho>" "cert_inst \<rho>" "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> u : U" for \<rho> e U e'
    by (rule a(5)[OF extends_tsol[OF that(1) b(7)] that(2-4)])
  ultimately show ?thesis using a(1,4) NV unfolding cpy_def by blast
qed

lemma pmu_mono:
  assumes "finite S0" "extends env env'"
  shows "pmu S0 env' \<le> pmu S0 env"
  unfolding pmu_def
proof (rule card_mono)
  show "{x\<in>S0. vt_lookup (tenv env') x = None} \<subseteq> {x\<in>S0. vt_lookup (tenv env) x = None}"
  proof
    fix x assume "x \<in> {x\<in>S0. vt_lookup (tenv env') x = None}"
    then show "x \<in> {x\<in>S0. vt_lookup (tenv env) x = None}"
      using extends_lookup[OF assms(2), of x] by (cases "vt_lookup (tenv env) x") auto
  qed
qed (use assms(1) in simp)

lemma pmu_eq:
  assumes "finite S0" "extends env env'" "pmu S0 env' = pmu S0 env" "y \<in> S0" "vt_lookup (tenv env) y = None"
  shows "vt_lookup (tenv env') y = None"
proof -
  let ?A = "{y\<in>S0. vt_lookup (tenv env') y = None}" and ?B = "{y\<in>S0. vt_lookup (tenv env) y = None}"
  have "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then show "x \<in> ?B" using extends_lookup[OF assms(2), of x] by (cases "vt_lookup (tenv env) x") auto
  qed
  moreover have "finite ?B" using assms(1) by simp
  moreover have "card ?A = card ?B" using assms(3) by (simp add: pmu_def)
  ultimately have "?A = ?B" by (intro card_subset_eq)
  with assms(4,5) show ?thesis by blast
qed

lemma poldin_mono: "poldin m0 S0 env Y \<Longrightarrow> X \<subseteq> vreach env Y \<Longrightarrow> poldin m0 S0 env X"
  using vreach_mono[of X env Y] by (auto simp: poldin_def)

lemma poldin_ext:
  assumes cr: "cres Fd Ft A X env D A' K' X' env' dps' NV" and o: "poldin m0 S0 env (Y \<union> D)"
    and m: "m0 \<le> maxidx env" and bb: "bbelow env"
  shows "poldin m0 S0 env' (Y \<union> vdps dps')"
  unfolding poldin_def
proof (intro ballI impI)
  note t = cresD[OF cr]
  fix y assume y: "y \<in> vreach env' (Y \<union> vdps dps')" "snd y \<le> m0"
  have nv: "y \<notin> NV" using t(9)[of y] y(2) m by auto
  have rn: "vreach env NV = NV" using vreach_fresh[OF bb] t(9) by blast
  from t(10) y(1) nv have "y \<in> vreach env (Y \<union> vdps dps' \<union> D)" by blast
  moreover have "vreach env (vdps dps') \<subseteq> vreach env D \<union> NV"
    using vreach_mono[of "vdps dps'" env "D \<union> NV"] t(11) vreach_incl[of D env] rn
    by (auto simp: vreach_Un)
  ultimately have "y \<in> vreach env (Y \<union> D)" using nv vreach_mono[of D env "Y \<union> D"] vreach_incl[of "Y \<union> D" env]
    by (auto simp: vreach_Un)
  with o y(2) show "y \<in> S0" by (auto simp: poldin_def)
qed


lemma vreach_free:
  assumes vg: "vgood Fd Ft env" and X: "X \<inter> Ft = {}" and y: "y \<in> vreach env X"
  shows "y \<notin> Ft"
proof -
  from y obtain x where x: "x \<in> X" "(y, x) \<in> (dep env)\<^sup>*" by (auto simp: vreach_def)
  from x(2) show ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    with X x(1) show ?case by blast
  next
    case (step a b)
    from step.hyps(1) obtain U u where "vt_lookup (tenv env) b = Some (U, u)" "a \<in> vns u"
      by (auto simp: dep_def)
    with vgoodD[OF vg this(1)] show ?case by blast
  qed
qed

text \<open>The measure of a term of the original problem does not change as long as no old variable is assigned:\<close>

lemma rsz_stable:
  assumes finS0: "finite S0" and regime: "Fd = {x. m0 < snd x} \<and> Ft = {} \<or> Fd = {} \<and> Ft = {x. m0 < snd x}"
    and ac: "acyc env" and vg: "vgood Fd Ft env" and cr: "cres Fd Ft A X env D A' K' X' env' dps' NV"
    and o: "poldin m0 S0 env (vns a)" and sa: "psh Fd Ft a" and mu: "pmu S0 env' = pmu S0 env"
  shows "rsz env' a = rsz env a"
proof (rule rsz_ext[OF ac])
  note c = cresD[OF cr]
  show "acyc env'" using c(5) unfolding sinv_def using einvD(3) by blast
  show "extends env env'" by (rule c(7))
  fix y assume y: "y \<in> vreach env (vns a)" and n: "vt_lookup (tenv env) y = None"
  show "vt_lookup (tenv env') y = None"
  proof (cases "snd y \<le> m0")
    case True
    with o y have "y \<in> S0" by (auto simp: poldin_def)
    from pmu_eq[OF finS0 c(7) mu this n] show ?thesis .
  next
    case False
    have "y \<notin> Ft" using vreach_free[OF vg _ y] sa by (auto simp: psh_def)
    with regime False have "y \<in> Fd" by auto
    show ?thesis
    proof (rule ccontr)
      assume "vt_lookup (tenv env') y \<noteq> None"
      then obtain U w where "vt_lookup (tenv env') y = Some (U, w)" by auto
      from vgoodD[OF c(13) this] \<open>y \<in> Fd\<close> show False by blast
    qed
  qed
qed


subsection \<open>Types\<close>

lemma typing_bs:
  assumes "bs_env \<rho> e rb" "bs_env \<rho> e' rb" "e \<turnstile> s : T" "\<not> loose_bvar s (ilength rb)"
  shows "e' \<turnstile> s : T"
proof (rule typing_env_cong[OF assms(3)])
  fix i assume i: "0 \<le> i" "loose_bvar1 s i"
  with loose_bvar1_less[OF assms(4)] have "i < ilength rb" by blast
  with assms(1,2) i(1) show "e' i = e i" by (simp add: bs_env_def)
qed

lemma typings_bs:
  assumes "bs_env \<rho> e rb" "bs_env \<rho> e' rb" "e \<tturnstile> ss : Ts" "\<forall>s\<in>set ss. \<not> loose_bvar s (ilength rb)"
  shows "e' \<tturnstile> ss : Ts"
  using assms(3,4) by (induction ss arbitrary: Ts) (auto split: list.splits intro: typing_bs[OF assms(1,2)])

lemma pok_typing:
  assumes "pok A env rb X u u" "tsol (tyenv env) \<rho>" "cert_inst \<rho>" "bs_env \<rho> e rb"
  shows "\<exists>U. e \<turnstile> inst \<rho> u : U"
proof -
  from pokD(9)[OF assms(1-3)] obtain e0 U where b0: "bs_env \<rho> e0 rb" and t0: "e0 \<turnstile> inst \<rho> u : U" by blast
  have "e \<turnstile> inst \<rho> u : U" by (rule typing_bs[OF b0 assms(4) t0]) (use pokD(7)[OF assms(1)] in simp)
  then show ?thesis by blast
qed

lemma mc_types:
  assumes cp: "cpre Fd Ft m0 A K X env dps rb targs Tts" and up: "upre Fd Ft A X env rb u"
  shows "\<exists>T0 base Ts'. fastype env rb (head_of u) = return T0 \<and> body_type env T0 = return base \<and>
    tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A \<and> tvars base \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    mapM (fastype env rb) targs = return Ts' \<and> (\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts)"
proof -
  let ?\<theta> = "tyenv env" and ?h = "head_of u" and ?\<rho> = "rho0 env"
  note c = cpreD[OF cp]
  have ei: "einv A K env" using c(3) by (simp add: sinv_def)
  have p: "pok A env rb X u u" using up by (simp add: upre_def)
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  from pd(9)[OF r0] obtain e0 U where bs: "bs_env ?\<rho> e0 rb" and tyu: "e0 \<turnstile> inst ?\<rho> u : U" by blast
  have u: "u = ?h \<degree>\<degree> snd (strip_comb u)" by (rule t_apps)
  from tyu[unfolded u[THEN arg_cong[of _ _ "inst ?\<rho>"]] inst_apps] obtain Vs where
    tyh: "e0 \<turnstile> inst ?\<rho> ?h : Vs \<Rrightarrow> U" by (rule list_app_typeE)
  have lbh: "\<not> loose_bvar ?h (ilength rb)" using pd(7) u by (metis loose_bvar_apps)
  have tvh: "ttvars ?h \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
    using ttvars_head[of u] pd(3,5) by auto
  from env_fastype_term[OF x(2) refl tyh bs lbh tvh] obtain T0 where
    T0: "env_fastype env (map snd rb) ?h = return T0" "tvars T0 \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  from body_type_term[OF x(2) refl T0(2)] obtain base where
    base: "body_type env T0 = return base" "tvars base \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  have "\<forall>s\<in>set targs. \<exists>e U. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
  proof
    fix s assume s: "s \<in> set targs"
    then have ps: "pok A env rb X s s" using c(6) by blast
    from pokD(9)[OF ps r0] obtain e U where "bs_env ?\<rho> e rb" "e \<turnstile> inst ?\<rho> s : U" by blast
    then show "\<exists>e U. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
        ttvars s \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
      using pokD(3,5,7)[OF ps] by blast
  qed
  from mapM_fastype_term[OF ei this] obtain Ts' where
    Ts': "mapM (fastype env rb) targs = return Ts'" "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  have "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts" if \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    from pd(9)[OF \<rho>] obtain e U where bs\<rho>: "bs_env \<rho> e rb" by blast
    show ?thesis
      by (rule mapM_fastype_types[OF _ \<rho>(1) bs\<rho> c(8)[OF \<rho> bs\<rho>]]) (use Ts'(1) in \<open>simp add: return_def\<close>)
  qed
  with T0 base Ts' show ?thesis by (auto simp: fastype_def)
qed

text \<open>A saturated term without abstractions has the body type of its head:\<close>

lemma sat_base:
  assumes ei: "einv A K env" and s: "sat env rb u" and nA: "\<not> is_Abs u"
    and T0: "ok (fastype env rb (head_of u)) T0" and base: "ok (body_type env T0) base"
    and \<rho>: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> u : U"
  shows "U = tsubst \<rho> base"
proof -
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env" and ?h = "head_of u" and ?as = "snd (strip_comb u)"
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei]
  from mf_body_type_sound[of env T0 "Ok base" base] base x(6) obtain Zs where
    nb: "\<forall>A B. tnorm ?\<theta> base \<noteq> A \<rightarrow>\<^sub>T B" and Zs: "\<And>\<rho>. tsol ?\<theta> \<rho> \<Longrightarrow> tsubst \<rho> T0 = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> base"
    by auto
  have u: "u = ?h \<degree>\<degree> ?as" by (rule t_apps)
  from s obtain e0 U0 where bs0: "bs_env ?\<rho> e0 rb" and ty0: "e0 \<turnstile> inst ?\<rho> u : U0" and ar: "nabs u = arity U0"
    by (auto simp: sat_def)
  have na: "\<forall>A B. U0 \<noteq> A \<rightarrow>\<^sub>T B" using ar nA by auto
  from ty0[unfolded u[THEN arg_cong[of _ _ "inst ?\<rho>"]] inst_apps] obtain Vs0 where
    h0: "e0 \<turnstile> inst ?\<rho> ?h : Vs0 \<Rrightarrow> U0" and a0: "e0 \<tturnstile> map (inst ?\<rho>) ?as : Vs0" by (rule list_app_typeE)
  have "tsubst ?\<rho> T0 = Vs0 \<Rrightarrow> U0" by (rule fastype_sound[OF T0 r0(1) bs0 h0])
  with Zs[OF r0(1)] have "Vs0 \<Rrightarrow> U0 = map (tsubst ?\<rho>) Zs \<Rrightarrow> tnorm ?\<theta> base" by simp
  from funs_nonarrow_eq[OF this na nb] have l0: "length Vs0 = length Zs" by simp
  have la: "length ?as = length Zs" using typings_nth[OF a0] l0 by simp
  from ty[unfolded u[THEN arg_cong[of _ _ "inst \<rho>"]] inst_apps] obtain Vs where
    h: "e \<turnstile> inst \<rho> ?h : Vs \<Rrightarrow> U" and a: "e \<tturnstile> map (inst \<rho>) ?as : Vs" by (rule list_app_typeE)
  have "tsubst \<rho> T0 = Vs \<Rrightarrow> U" by (rule fastype_sound[OF T0 \<rho> bs h])
  with Zs[OF \<rho>] have "Vs \<Rrightarrow> U = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> base" by simp
  moreover have "length Vs = length (map (tsubst \<rho>) Zs)" using typings_nth[OF a] la by simp
  ultimately show ?thesis using funs_eq by blast
qed

lemma mc_unfold:
  assumes "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts"
  shows "mc cfg vname rb targs u env dps =
    (case fst (strip_comb u) of
      Abs a T body \<Rightarrow> do {
        s \<leftarrow> mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps;
        returnW (S_MapAbs a T s)}
    | Var w _ \<Rightarrow>
        (let (env', newhd) = genvar (fst w) env (foldr fun_type Ts base) in
          returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
            ((rb, list_comb newhd targs, u) # dps))))
    | _ \<Rightarrow> do {
        projs \<leftarrow> make_projs u targs Ts targs;
        matchfun cfg vname rb targs u env dps (fst (strip_comb u)) (snd (strip_comb u)) base Ts (rev projs)})"
  by (subst mc.simps) (simp add: Let_def assms(2,3) assms(1)[unfolded head_of_strip_comb]
      liftM_def return_def bindW_def returnW_def option.map_id)



subsection \<open>Copies by a new variable\<close>

lemma pgood_newpair:
  assumes "\<forall>t\<in>set targs. psh Fd Ft t" "ptok Fd Ft targs" "psh Fd Ft u" "x \<notin> Fd \<or> Fd \<noteq> {}"
  shows "pgood Fd Ft (rb, list_comb (Var x T) targs, u)"
proof -
  have "dd Fd (\<exists>t\<in>set targs. \<not> is_Bound t) (Var x T)"
    using assms(2,4) by (auto simp: ptok_def)
  then have "dead Fd (list_comb (Var x T) targs)" using assms(1) by (simp add: dd_list_comb psh_def)
  moreover have "gs Ft (list_comb (Var x T) targs)"
    by (rule hok_gs) (use assms(1) in \<open>simp add: hok_list_comb psh_def\<close>)
  moreover have "dead Fd u" "gs Ft u" using assms(3) by (auto simp: psh_def intro: gs_free)
  ultimately show ?thesis by (simp add: pgood_def)
qed

text \<open>The copy by a new variable \<open>newhd\<close> of type \<open>Ts' \<Rightarrow> B\<close> applied to the bound variables, with the new pair \<open>newhd targs =?= u\<close>:\<close>

lemma flex_copy:
  assumes cp: "cpre Fd Ft m0 A K X env dps rb targs Tts" and up: "upre Fd Ft A X env rb u"
    and Ts': "mapM (fastype env rb) targs = return Ts'" and tvTs': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and TsEq: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts"
    and tvB: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A"
    and tyB: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> B"
    and g: "genvar a env (foldr fun_type Ts' B) = (env', newhd)"
  shows "PEC Fd Ft A X env (vns u \<union> vnsl targs \<union> vdps dps) rb u Tts
    (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u) # dps))"
proof -
  let ?\<theta> = "tyenv env" and ?D = "vns u \<union> vnsl targs \<union> vdps dps" and ?GT = "foldr fun_type Ts' B"
  let ?G = "(a, maxidx env + 1)" and ?c = "combound newhd 0 (length Ts')"
  note c = cpreD[OF cp] and gs = genvar_simps[OF g]
  have p: "pok A env rb X u u" and su: "psh Fd Ft u" using up by (simp_all add: upre_def)
  have ei: "einv A K env" and wi: "winv env X" using c(3) by (simp_all add: sinv_def)
  have lTs': "length Ts' = length targs" using Ts' by (simp add: ok_mapM list_all2_lengthD return_def)
  have lTs: "length Ts' = length Tts" using lTs' c(7) by simp
  have nh: "newhd = Var ?G ?GT" by (rule gs(4))
  have tvGT: "tvars ?GT \<subseteq> tvars_env ?\<theta> \<union> A" using tvTs' tvB by (auto simp: tvars_funs)
  have ext: "extends env env'" by (rule extends_genvar[OF g])
  have Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) [newhd] [B]" using nh by simp
  let ?X' = "vars newhd \<union> X"
  have vX': "vtvars ?X' \<subseteq> tvars_env (tyenv env') \<union> A" using c(4) tvGT nh gs(2) by (auto simp: vtvars_def)
  have ei': "einv A K env'" by (rule einv_genvar[OF g ei])
  have wi': "winv env' ?X'"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
    then have "wt_env \<rho> env \<and> vinv \<rho> env X" using winvD[OF wi] gs(2) by simp
    then show "wt_env \<rho> env' \<and> vinv \<rho> env' ?X'" using wt_env_genvar[OF g] vinv_genvar[OF g] by blast
  qed
  have pold: "pok A env' rb' ?X' t' u'" if "(rb', t', u') \<in> set dps" for rb' t' u'
  proof -
    from c(3) that have p0: "pok A env rb' X t' u'" by (auto simp: sinv_def)
    have "pok A env rb' ?X' t' u'" by (rule pok_Xmono[OF p0]) (use pokD(6)[OF p0] vX' gs(2) in auto)
    then show ?thesis by (rule pok_mono[OF _ ext]) (simp add: gs(2))
  qed
  have tyc: "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> ?c : U \<and> e \<turnstile> inst \<rho> (list_comb newhd targs) : U"
    if \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : U" for \<rho> e U e'
  proof -
    have UB: "U = tsubst \<rho> B" by (rule tyB[OF \<rho> bs tyu])
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu pokD(7)[OF p]])
    have tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Tts" by (rule c(8)[OF \<rho> bs])
    have lba: "\<forall>s\<in>set targs. \<not> loose_bvar s (ilength rb)" using c(6) pokD(7) by blast
    have cTs: "\<forall>T\<in>set Tts. cert_typ alg ar (tsubst \<rho> T)" by (rule mf_cert_targs[OF bs tya lba])
    have ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts" by (rule TsEq[OF \<rho>])
    have cTs': "\<forall>T\<in>set Ts'. cert_typ alg ar (tsubst \<rho> T)"
    proof
      fix T assume "T \<in> set Ts'"
      then have "tsubst \<rho> T \<in> set (map (tsubst \<rho>) Tts)" using ts by (metis image_eqI list.set_map)
      then show "cert_typ alg ar (tsubst \<rho> T)" using cTs by auto
    qed
    have "pushes e' (map (tsubst \<rho>) Tts) \<tturnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) [newhd]) :
        map (tsubst \<rho>) [B]"
      by (rule mf_typings_new_args[OF Gs ts cTs _ lTs]) (use cU UB in simp)
    then have t1: "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> ?c : U" using UB by (simp add: mf_combound_bvs)
    have "e \<turnstile> inst \<rho> newhd : map (tsubst \<rho>) Tts \<Rrightarrow> U"
      using cTs cTs' cU UB ts by (auto simp: nh tsubst_funs cert_typ_funs)
    from list_app_typeI[OF this tya] have "e \<turnstile> inst \<rho> (list_comb newhd targs) : U"
      by (simp add: list_comb_apps inst_apps)
    with t1 show ?thesis by blast
  qed
  have pnew: "pok A env' rb ?X' (list_comb newhd targs) u"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars (list_comb newhd targs) \<union> vars u \<subseteq> ?X' \<union> evars env'"
      using c(6) pokD(1)[OF p] evars_genvar[OF g] by (fastforce simp: list_comb_apps vars_apps dest: pokD(1))
    show "ttvars (list_comb newhd targs) \<union> ttvars u \<union> btvars rb \<union> vtvars ?X' \<subseteq> tvars_env (tyenv env') \<union> A"
      using c(5,6) pokD(3)[OF p] tvGT vX' gs(2) nh
      by (auto simp: list_comb_apps ttvars_apps dest: pokD(3))
    show "\<not> loose_bvar (list_comb newhd targs) (ilength rb)"
      using c(6) nh by (auto simp: list_comb_apps loose_bvar_apps dest: pokD(7))
    show "\<not> loose_bvar u (ilength rb)" by (rule pokD(7)[OF p])
    fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
    then have \<rho>': "tsol ?\<theta> \<rho>" using gs(2) by simp
    from pokD(9)[OF p \<rho>' \<rho>(2)] obtain e U where bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : U" by blast
    from tyc[OF \<rho>' \<rho>(2) bs tyu] tyu bs
    show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> (list_comb newhd targs) : T \<and> e \<turnstile> inst \<rho> u : T" by blast
  qed
  have si': "sinv A K ?X' env' ((rb, list_comb newhd targs, u) # dps)"
    using ei' wi' pold pnew by (auto simp: sinv_def)
  have rb: "vreach env' Y = vreach env Y" for Y using vreach_tenv[OF gs(1)] by simp
  have cr: "cres Fd Ft A X env ?D A K ?X' env' ((rb, list_comb newhd targs, u) # dps) {?G}"
  proof (rule cresI)
    show "finite ?X'" using c(1) by simp
    show "finite K" by (rule c(2))
    show "extends env env'" by (rule ext)
    show "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env')" using gs(2) by simp
    show "maxidx env < snd y" if "y \<in> {?G}" for y using that by simp
    show "vreach env' Y \<subseteq> vreach env (Y \<union> ?D) \<union> {?G}" for Y
      unfolding rb using vreach_subset[of Y "Y \<union> ?D" env] by blast
    have "vdps ((rb, list_comb newhd targs, u) # dps) \<subseteq> ?D \<union> {?G}"
      using nh by (auto simp: list_comb_apps vars_apps)
    then show "vdps ((rb, list_comb newhd targs, u) # dps) \<subseteq> vreach env ?D \<union> {?G}"
      using vreach_incl[of ?D env] by blast
    show "x \<in> vreach env ?D \<union> {?G}" if "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None" for x
      using that gs(1) by simp
    show "vgood Fd Ft env'" using c(9) vgood_tenv[OF gs(1)] by simp
    have "pgood Fd Ft (rb, list_comb newhd targs, u)"
      unfolding nh by (rule pgood_newpair) (use c(6,11) su in auto)
    then show "pgood Fd Ft dp" if "dp \<in> set ((rb, list_comb newhd targs, u) # dps)" for dp
      using that c(10)[of dp] by auto
  qed (use si' vX' in auto)
  have cpc: "cpy A ?X' env' {?G} rb u Tts ?c"
    unfolding cpy_def
  proof (intro conjI allI impI)
    have "[?c] = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) [newhd]" by (simp add: mf_combound_bvs)
    note na = new_args_props[OF Gs lTs this]
    have pr: "\<not> loose_bvar ?c (ilength Tts)" "vars ?c = vars newhd" "ttvars ?c = ttvars newhd"
      using na lTs nh by (auto simp: mf_combound_bvs)
    show "vns ?c \<subseteq> {?G}" using pr(2) nh by simp
    show "vars ?c \<subseteq> ?X' \<union> evars env'" using pr(2) by blast
    show "ttvars ?c \<subseteq> tvars_env (tyenv env') \<union> A" using pr(3) tvGT nh gs(2) by simp
    show "\<not> loose_bvar ?c (ilength Tts)" by (rule pr(1))
    fix \<rho> e U e' assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb"
      and tyu: "e \<turnstile> inst \<rho> u : U"
    from tyc[OF _ \<rho>(2) bs tyu, of e'] \<rho>(1) gs(2)
    show "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> ?c : U" by simp
  qed
  from cr cpc show ?thesis unfolding PEC_def by blast
qed



subsection \<open>Copies by projection\<close>

lemma rrs_apps: "rrs F (h \<degree>\<degree> ts) \<longleftrightarrow> rrs F h \<and> (\<forall>t\<in>set ts. gs F t)"
  by (induction ts arbitrary: h) auto

lemma dd_empty: "dd {} b t"
  by (induction "{} :: indexname set" b t rule: dd.induct) auto

lemma typings_Gs_targs:
  assumes Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us" and ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts"
    and cTs: "\<forall>T\<in>set Tts. cert_typ alg ar (tsubst \<rho> T)" and cUs: "\<forall>U\<in>set Us. cert_typ alg ar (tsubst \<rho> U)"
    and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Tts"
  shows "e \<tturnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs) : map (tsubst \<rho>) Us"
  unfolding mf_typings_iff
proof (rule list_all2_all_nthI)
  have lGs: "length Gs = length Us" by (rule list_all2_lengthD[OF Gs])
  then show "length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs)) = length (map (tsubst \<rho>) Us)" by simp
  fix k assume "k < length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs))"
  then have k: "k < length Gs" by simp
  from list_all2_nthD[OF Gs k] obtain x where G: "Gs ! k = Var x (Ts' \<Rrightarrow> (Us ! k))" by blast
  have cTs': "\<forall>T\<in>set Ts'. cert_typ alg ar (tsubst \<rho> T)"
  proof
    fix T assume "T \<in> set Ts'"
    then have "tsubst \<rho> T \<in> set (map (tsubst \<rho>) Tts)" using ts by (metis image_eqI list.set_map)
    then show "cert_typ alg ar (tsubst \<rho> T)" using cTs by auto
  qed
  have "Us ! k \<in> set Us" using k lGs by simp
  then have "e \<turnstile> inst \<rho> (Gs ! k) : map (tsubst \<rho>) Tts \<Rrightarrow> tsubst \<rho> (Us ! k)"
    using cTs cTs' cUs ts by (auto simp: G tsubst_funs cert_typ_funs)
  from list_app_typeI[OF this tya]
  show "typing e (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs) ! k) (map (tsubst \<rho>) Us ! k)"
    using k lGs by (simp add: inst_apps)
qed

text \<open>A projection with the guess of \<open>Cs\<close> arguments: the simplification of the projection pair yields a copy.\<close>

lemma proj_res:
  assumes cp: "cpre Fd Ft m0 A K X env dps rb targs Tts" and up: "upre Fd Ft A X env rb u"
    and hr: "rigid (head_of u)" and nA: "\<not> is_Abs u" and st: "sat env rb u"
    and T0: "ok (fastype env rb (head_of u)) T0" and base: "ok (body_type env T0) base"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'" and tvTs': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and TsEq: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts"
    and k: "k < length targs" and stT: "ok (strip_type env (Ts' ! k)) (Us, bary)"
    and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    and g: "gentvars p env = (env0, Cs)"
    and post: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' dps" "tenv env' = tenv env0" "extends env0 env'"
      "tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env')"
      "\<And>\<rho>. tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
    and ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)"
  shows "cuok (SIMPL alg env'' ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
    (\<lambda>(env2, fr, ff). PEC Fd Ft A X env (vns u \<union> vnsl targs \<union> vdps dps) rb u Tts
      (El_C (list_comb (Bound (integer_of_nat (length targs - 1 - k))) args) env2 (fr @ ff)))"
proof -
  let ?\<theta> = "tyenv env" and ?A = "A \<union> ntv Cs" and ?K = "K \<union> ntv Cs" and ?targ = "targs ! k"
  let ?D = "vns u \<union> vnsl targs \<union> vdps dps" and ?bv = "Bound (integer_of_nat (length targs - 1 - k))"
  note c = cpreD[OF cp] and gs = gentvars_simps[OF g]
  have p: "pok A env rb X u u" and su: "psh Fd Ft u" using up by (simp_all add: upre_def)
  have ei: "einv A K env" using c(3) by (simp add: sinv_def)
  have lTs': "length Ts' = length targs" using Ts' by (simp add: ok_mapM list_all2_lengthD)
  have lTs: "length Ts' = length Tts" using lTs' c(7) by simp
  have targk: "?targ \<in> set targs" using k by simp
  have ext0: "extends env env0" using gs by (simp add: extends_def)
  have ext': "extends env env'" by (rule extends_trans[OF ext0 post(3)])
  have te': "tenv env' = tenv env" using post(2) gs(1) by simp
  have tve': "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env')" using post(4) gs(2) by simp
  have tvTs'': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env') \<union> ?A" using tvTs' tve' by blast
  have tvC: "\<forall>C\<in>set Cs. tvars C \<subseteq> ntv Cs" by (auto simp: ntv_def)
  have tvUC: "\<forall>U\<in>set (Us @ Cs). tvars U \<subseteq> tvars_env (tyenv env') \<union> ?A" using tvUs tvC tve' by auto
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs (Us @ Cs)"
    and ma': "tenv env'' = tenv env'" "tyenv env'' = tyenv env'" "maxidx env' \<le> maxidx env''"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
    and si'': "sinv ?A ?K (mlvars Gs \<union> X) env'' dps"
    and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env') \<union> ?A"
    by (rule sinv_make_args[OF post(1) ma tvTs'' tvUC])
  let ?X'' = "mlvars Gs \<union> X" and ?NV = "fst ` mlvars Gs"
  have Gv: "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U" using Gi by blast
  have te'': "tenv env'' = tenv env" using ma'(1) te' by simp
  have ext'': "extends env env''" using ext' ma' by (auto simp: extends_def)
  have tve'': "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env'')" using tve' ma'(2) by simp
  have mx: "maxidx env \<le> maxidx env'" using ext' by (simp add: extends_def)
  have NVf: "\<forall>y\<in>?NV. maxidx env < snd y" using Gi mx by fastforce
  have hargs: "map (\<lambda>arg. list_comb (head_of arg) targs) args = map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    using Gv by (auto simp: args list_comb_apps head_of_apps')
  let ?lhs = "?targ \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs"
  have lhs: "list_comb ?targ (map (\<lambda>arg. list_comb (head_of arg) targs) args) = ?lhs"
    unfolding hargs by (simp add: list_comb_apps)
  note pk = c(6)[OF targk]
  have vlhs: "vars ?lhs = vars ?targ \<union> mlvars Gs \<union> (if Gs = [] then {} else \<Union> (vars ` set targs))"
    using Gv by (auto simp: vars_apps)
  have vlhs': "vars ?lhs \<subseteq> vars ?targ \<union> mlvars Gs \<union> \<Union> (vars ` set targs)" using vlhs by (auto split: if_splits)
  have tvlhs: "ttvars ?lhs \<subseteq> ttvars ?targ \<union> vtvars (mlvars Gs) \<union> \<Union> (ttvars ` set targs)"
    using ttvars_mlvars_Gs[OF Gv] by (auto simp: ttvars_apps)
  \<comment> \<open>Typing of the projection pair and of the copy\<close>
  have tyall: "U = tsubst \<rho> base \<and> e \<turnstile> inst \<rho> ?lhs : U \<and>
      pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> (list_comb ?bv args) : U"
    if \<rho>: "tsol (tyenv env'') \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : U"
    for \<rho> e U e'
  proof -
    have \<rho>': "tsol (tyenv env') \<rho>" using \<rho>(1) ma'(2) by simp
    have \<rho>0: "tsol ?\<theta> \<rho>" by (rule extends_tsol[OF \<rho>' ext'])
    have UB: "U = tsubst \<rho> base" by (rule sat_base[OF ei st nA T0 base \<rho>0 bs tyu])
    have tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Tts" by (rule c(8)[OF \<rho>0 \<rho>(2) bs])
    have lba: "\<forall>s\<in>set targs. \<not> loose_bvar s (ilength rb)" using c(6) pokD(7) by blast
    have cTs: "\<forall>T\<in>set Tts. cert_typ alg ar (tsubst \<rho> T)" by (rule mf_cert_targs[OF bs tya lba])
    have ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts" by (rule TsEq[OF \<rho>0 \<rho>(2)])
    have kT: "tsubst \<rho> (Tts ! k) = tsubst \<rho> (Ts' ! k)"
      using arg_cong[OF ts, of "\<lambda>xs. xs ! k"] k lTs lTs' by simp
    have Tk': "tsubst \<rho> (Ts' ! k) = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> bary" by (rule strip_type_sound[OF stT \<rho>0])
    have jT: "tsubst \<rho> (Tts ! k) = map (tsubst \<rho>) (Us @ Cs) \<Rrightarrow> tsubst \<rho> base"
      using kT Tk' post(5)[OF \<rho>'] by (simp add: tsubst_funs)
    have cTk: "cert_typ alg ar (tsubst \<rho> (Tts ! k))" using cTs k c(7) by simp
    have cUs: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho> U)" using cTk by (auto simp: jT cert_typ_funs)
    have tyk: "e \<turnstile> inst \<rho> ?targ : tsubst \<rho> (Tts ! k)"
      using typings_nth[OF tya] k c(7) by auto
    have "e \<tturnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs) : map (tsubst \<rho>) (Us @ Cs)"
      by (rule typings_Gs_targs[OF Gs ts cTs cUs tya])
    from list_app_typeI[OF tyk[unfolded jT] this] have t1: "e \<turnstile> inst \<rho> ?lhs : U"
      using UB by (simp add: inst_apps)
    have tyargs: "pushes e' (map (tsubst \<rho>) Tts) \<tturnstile> map (inst \<rho>) args : map (tsubst \<rho>) (Us @ Cs)"
      using mf_typings_new_args[OF Gs ts cTs cUs lTs] by (simp add: args)
    have j: "0 \<le> integer_of_nat (length targs - 1 - k)" "integer_of_nat (length targs - 1 - k) < ilength Tts"
      using k c(7) by (simp_all add: ilength_eq integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq)
    have "pushes e' (map (tsubst \<rho>) Tts) (integer_of_nat (length targs - 1 - k)) = map (tsubst \<rho>) (Us @ Cs) \<Rrightarrow> tsubst \<rho> base"
    proof -
      have "pushes e' (map (tsubst \<rho>) Tts) (integer_of_nat (length targs - 1 - k)) =
          rev (map (tsubst \<rho>) Tts) ! (length targs - 1 - k)"
        using j by (simp add: pushes_nth)
      also have "\<dots> = tsubst \<rho> (Tts ! k)" using k c(7) by (simp add: rev_nth)
      finally show ?thesis using jT by simp
    qed
    from list_app_typeI[OF typing.Bound[where e="pushes e' (map (tsubst \<rho>) Tts)", OF j(1) this] tyargs]
    have "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> (list_comb ?bv args) : U"
      using UB by (simp add: list_comb_apps inst_apps)
    with UB t1 show ?thesis by blast
  qed
  have pnew: "pok ?A env'' rb ?X'' ?lhs u"
    unfolding pok_def
  proof (intro conjI allI impI)
    have va: "\<Union> (vars ` set targs) \<subseteq> X \<union> evars env"
    proof
      fix y assume "y \<in> \<Union> (vars ` set targs)"
      then obtain t where "t \<in> set targs" "y \<in> vars t" by blast
      with c(6)[OF this(1)] show "y \<in> X \<union> evars env" using pokD(1) by blast
    qed
    have vt: "vars ?targ \<subseteq> X \<union> evars env" using va targk by blast
    have ev: "evars env'' = evars env" by (rule evars_tenv[OF te''])
    have "vars ?lhs \<subseteq> ?X'' \<union> evars env''" using vlhs' va vt unfolding ev by blast
    then show "vars ?lhs \<union> vars u \<subseteq> ?X'' \<union> evars env''" using pokD(1)[OF p] unfolding ev by blast
    have ta: "\<Union> (ttvars ` set targs) \<subseteq> tvars_env ?\<theta> \<union> A"
    proof
      fix y assume "y \<in> \<Union> (ttvars ` set targs)"
      then obtain t where "t \<in> set targs" "y \<in> ttvars t" by blast
      with c(6)[OF this(1)] show "y \<in> tvars_env ?\<theta> \<union> A" using pokD(3) by blast
    qed
    have tt: "ttvars ?targ \<subseteq> tvars_env ?\<theta> \<union> A" using ta targk by blast
    have sub: "tvars_env ?\<theta> \<union> A \<subseteq> tvars_env (tyenv env'') \<union> ?A" using tve'' by blast
    have sub': "tvars_env (tyenv env') \<union> ?A \<subseteq> tvars_env (tyenv env'') \<union> ?A" using ma'(2) by simp
    have "vtvars ?X'' = vtvars (mlvars Gs) \<union> vtvars X" by (rule vtvars_Un)
    then have "vtvars ?X'' \<subseteq> tvars_env (tyenv env'') \<union> ?A" using vG c(4) sub sub' by blast
    moreover have "ttvars ?lhs \<subseteq> tvars_env (tyenv env'') \<union> ?A" using tvlhs tt ta vG sub sub' by blast
    moreover have "ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env'') \<union> ?A" using pokD(3)[OF p] c(5) sub by blast
    ultimately show "ttvars ?lhs \<union> ttvars u \<union> btvars rb \<union> vtvars ?X'' \<subseteq> tvars_env (tyenv env'') \<union> ?A"
      by blast
    show "\<not> loose_bvar ?lhs (ilength rb)"
      using c(6) pokD(7) targk Gv by (fastforce simp: loose_bvar_apps)
    show "\<not> loose_bvar u (ilength rb)" by (rule pokD(7)[OF p])
    fix \<rho> assume \<rho>: "tsol (tyenv env'') \<rho>" "cert_inst \<rho>"
    have \<rho>0: "tsol ?\<theta> \<rho>" using extends_tsol[OF \<rho>(1) ext''] .
    from pokD(9)[OF p \<rho>0 \<rho>(2)] obtain e U where bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : U" by blast
    from tyall[OF \<rho> bs tyu] tyu bs show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> ?lhs : T \<and> e \<turnstile> inst \<rho> u : T"
      by blast
  qed
  let ?dp = "(rb, ?lhs, u)"
  have si3: "sinv ?A ?K ?X'' env'' (?dp # dps)" using si'' pnew by (simp add: sinv_def)
  have finX'': "finite ?X''" using c(1) by simp
  have finK': "finite ?K" using c(2) by simp
  \<comment> \<open>The new variables stay good\<close>
  have vg'': "vgood Fd Ft env''" using c(9) vgood_tenv[OF te''] by simp
  have pg: "pgood Fd Ft ?dp"
  proof -
    have dl: "dead Fd ?lhs"
    proof (cases "Fd = {}")
      case True
      then show ?thesis by (simp add: dd_empty)
    next
      case False
      with c(11) obtain t0 where t0: "t0 \<in> set targs" "\<not> is_Bound t0" by (auto simp: ptok_def)
      have "dead Fd (G \<degree>\<degree> targs)" if "G \<in> set Gs" for G
      proof -
        from Gv that obtain x U where "G = Var x U" by blast
        then show ?thesis using c(6) t0 by (auto simp: dd_list_comb[unfolded list_comb_apps] psh_def)
      qed
      moreover have "dead Fd ?targ" using c(6) targk by (simp add: psh_def)
      ultimately show ?thesis by (auto simp: dd_list_comb[unfolded list_comb_apps] intro: dd_True)
    qed
    have du: "dead Fd u" using su by (simp add: psh_def)
    have gr: "gs Ft ?lhs \<and> gs Ft u \<or> rrs Ft ?lhs \<and> rrs Ft u"
    proof (cases "Ft = {}")
      case True
      then show ?thesis by (auto intro: gs_free)
    next
      case False
      with c(11) have bt: "is_Bound ?targ" using targk by (auto simp: ptok_def)
      have "gs Ft (G \<degree>\<degree> targs)" if "G \<in> set Gs" for G
      proof -
        from Gv that obtain x U where "G = Var x U" by blast
        then show ?thesis using c(6) by (auto intro!: hok_gs simp: hok_list_comb[unfolded list_comb_apps] psh_def)
      qed
      then have "rrs Ft ?lhs" using bt by (cases ?targ) (auto simp: rrs_apps)
      moreover have "rrs Ft u"
      proof -
        have "u = head_of u \<degree>\<degree> snd (strip_comb u)" by (rule t_apps)
        moreover have "rrs Ft (head_of u)" using hr by (cases "head_of u") auto
        moreover have "\<forall>t\<in>set (snd (strip_comb u)). gs Ft t"
        proof
          fix t assume "t \<in> set (snd (strip_comb u))"
          then have "vns t \<subseteq> vns u" by (subst (2) t_apps) (auto simp: vars_apps)
          with su show "gs Ft t" by (auto intro!: gs_free simp: psh_def)
        qed
        ultimately show ?thesis by (metis rrs_apps)
      qed
      ultimately show ?thesis by blast
    qed
    from dl du gr show ?thesis by (simp add: pgood_def)
  qed
  show ?thesis unfolding lhs
  proof (rule cuok_mono_ok[OF SIMPL_term[OF finX'' finK' si3]])
    fix st assume ok: "okW (SIMPL alg env'' (?dp # dps)) st" and sp: "simpl_post ?A ?K ?X'' env'' st"
    obtain env2 fr ff where ste: "st = (env2, fr, ff)" by (cases st)
    from sp ste have si2: "sinv ?A ?K ?X'' env2 (ff @ fr)" and ss: "sstep ?K ?X'' env'' env2"
      by (auto simp: simpl_post_def)
    note sd = sstepD[OF ss]
    have vs: "vsr (vdps (?dp # dps)) (env'', [], []) (env2, fr, ff)" using SIMPL_vreach'[OF ok] ste by simp
    have sg: "sgood Fd Ft (env2, fr, ff)"
      by (rule SIMPL_good'[OF ok[unfolded ste] vg'']) (use pg c(10) in auto)
    have rD: "vdps (?dp # dps) \<subseteq> ?D \<union> ?NV"
    proof -
      have "vns ?lhs \<subseteq> vns ?targ \<union> ?NV \<union> vnsl targs"
        using image_mono[OF vlhs', of fst] by (simp add: image_Un image_Union)
      moreover have "vns ?targ \<subseteq> vnsl targs" using targk by blast
      moreover have "vdps (?dp # dps) = vns ?lhs \<union> vns u \<union> vdps dps" by simp
      ultimately show ?thesis by (simp only:) (rule set_lem1)
    qed
    have rr: "vreach env (Y \<union> vdps (?dp # dps)) \<subseteq> vreach env (Y \<union> ?D) \<union> ?NV" for Y
    proof -
      have s: "Y \<union> vdps (?dp # dps) \<subseteq> (Y \<union> ?D) \<union> ?NV" by (rule set_lem2[OF rD])
      have "vreach env (Y \<union> vdps (?dp # dps)) \<subseteq> vreach env ((Y \<union> ?D) \<union> ?NV)" by (rule vreach_subset[OF s])
      also have "\<dots> = vreach env (Y \<union> ?D) \<union> ?NV"
        by (simp only: vreach_Un vreach_fresh[OF sinv_bbelow[OF c(3)] NVf])
      finally show ?thesis .
    qed
    have rv: "vreach env'' = vreach env" using vreach_tenv[OF te''] .
    have cr: "cres Fd Ft A X env ?D ?A ?K ?X'' env2 (fr @ ff) ?NV"
    proof (rule cresI)
      show "finite ?X''" "finite ?K" by (fact finX'', fact finK')
      show "sinv ?A ?K ?X'' env2 (fr @ ff)" by (rule sinv_mono[OF si2]) auto
      have "vtvars ?X'' = vtvars (mlvars Gs) \<union> vtvars X" by (rule vtvars_Un)
      moreover have "tvars_env (tyenv env') \<subseteq> tvars_env (tyenv env2)" using sd(2) ma'(2) by simp
      ultimately show "vtvars ?X'' \<subseteq> tvars_env (tyenv env2) \<union> ?A"
        using c(4) vG tve' by blast
      show "extends env env2" by (rule extends_trans[OF ext'' sd(1)])
      show "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env2)" using tve'' sd(2) by blast
      show "maxidx env < snd y" if "y \<in> ?NV" for y using NVf that by blast
      show "vreach env2 Y \<subseteq> vreach env (Y \<union> ?D) \<union> ?NV" for Y
      proof -
        have "vreach env2 Y \<subseteq> vreach env (Y \<union> vdps (?dp # dps))" using vsrD(1)[OF vs, of Y] rv by simp
        from order_trans[OF this rr[of Y]] show ?thesis .
      qed
      show "vdps (fr @ ff) \<subseteq> vreach env ?D \<union> ?NV"
      proof -
        have "vdps (fr @ ff) \<subseteq> vreach env ({} \<union> vdps (?dp # dps))"
          using vsrD(2)[OF vs] rv by (simp add: Un_ac)
        from order_trans[OF this rr[of "{}"]] show ?thesis by simp
      qed
      show "x \<in> vreach env ?D \<union> ?NV" if "vt_lookup (tenv env2) x \<noteq> None" "vt_lookup (tenv env) x = None" for x
      proof -
        have "x \<in> vreach env'' (vdps (?dp # dps))" using vsrD(3)[OF vs] that te'' by simp
        then have "x \<in> vreach env ({} \<union> vdps (?dp # dps))" using rv by simp
        with rr[of "{}"] show ?thesis by auto
      qed
      show "vgood Fd Ft env2" using sg by (simp add: sgood_def)
      show "pgood Fd Ft dp" if "dp \<in> set (fr @ ff)" for dp using sg that by (auto simp: sgood_def)
    qed auto
    have cpc: "cpy ?A ?X'' env2 ?NV rb u Tts (list_comb ?bv args)"
      unfolding cpy_def
    proof (intro conjI allI impI)
      note na = new_args_props[OF Gs lTs args]
      have vu: "vars (list_comb ?bv args) = mlvars Gs" using na(2) by (simp add: list_comb_apps vars_apps)
      show "vns (list_comb ?bv args) \<subseteq> ?NV" using vu by simp
      show "vars (list_comb ?bv args) \<subseteq> ?X'' \<union> evars env2" using vu by blast
      have "ttvars (list_comb ?bv args) = vtvars (mlvars Gs)"
        using na(3) ttvars_mlvars_Gs[OF Gv] by (simp add: list_comb_apps ttvars_apps)
      then show "ttvars (list_comb ?bv args) \<subseteq> tvars_env (tyenv env2) \<union> ?A"
        using vG ma'(2) sd(2) by auto
      have j: "integer_of_nat (length targs - 1 - k) < ilength Tts"
        using k c(7) by (simp add: ilength_eq integer_less_iff integer_of_nat.rep_eq)
      show "\<not> loose_bvar (list_comb ?bv args) (ilength Tts)"
        using na(1) j by (auto simp: list_comb_apps loose_bvar_apps)
      fix \<rho> e U e' assume \<rho>: "tsol (tyenv env2) \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb"
        and tyu: "e \<turnstile> inst \<rho> u : U"
      have \<rho>'': "tsol (tyenv env'') \<rho>" by (rule extends_tsol[OF \<rho>(1) sd(1)])
      from tyall[OF \<rho>'' \<rho>(2) bs tyu] show "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> (list_comb ?bv args) : U"
        by blast
    qed
    from cr cpc ste show "case st of (env2, fr, ff) \<Rightarrow> PEC Fd Ft A X env ?D rb u Tts
        (El_C (list_comb ?bv args) env2 (fr @ ff))"
      unfolding PEC_def by blast
  qed
qed



subsection \<open>The enumerations of \<^const>\<open>matchfun\<close>\<close>

lemma projenv_fin:
  assumes g: "gentvars p env = (env0, Cs)" and P: "cuok (proj_unify cfg base bary Cs env0) P"
    and R: "\<And>env' env'' args. okW (proj_unify cfg base bary Cs env0) env' \<Longrightarrow> P env' \<Longrightarrow>
      make_args vname Ts env' (Us @ Cs) = (env'', args) \<Longrightarrow>
      cuok (SIMPL (cfg_alg cfg) env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
        (\<lambda>(env2, fr, ff). Q (El_C (list_comb head args) env2 (fr @ ff)))"
    and t: "fin cfg tail Q"
  shows "cuok (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail) (\<lambda>s. fin cfg s Q)"
  unfolding projenv_def g prod.case
proof (rule cuok_handle_CANTUNIFY_ret[OF cuok_bindW[OF P]])
  fix env' assume ok: "okW (proj_unify cfg base bary Cs env0) env'" and Pe: "P env'"
  obtain env'' args where ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)"
    by (cases "make_args vname Ts env' (Us @ Cs)")
  show "cuok (returnW (S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ tail)) (\<lambda>s. fin cfg s Q)"
    using fin_Proj[OF ma R[OF ok Pe ma] t] by simp
qed (use t in simp_all)

lemma foldrW_cuok_fin:
  assumes "\<And>x b. x \<in> set xs \<Longrightarrow> fin cfg b Q \<Longrightarrow> cuok (f x b) (\<lambda>s. fin cfg s Q)" "fin cfg b0 Q"
  shows "cuok (foldrW f xs b0) (\<lambda>s. fin cfg s Q)"
  using assms(1) by (induction xs) (auto intro: assms(2) cuok_bindW)

lemma matchfun_fin:
  assumes PF: "\<forall>(bv, T, targ)\<in>set projs. \<exists>Us bary. strip_type env T = return (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail Q \<longrightarrow>
        cuok (projenv cfg vname rb targs u env dps base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s Q))"
    and imit: "fin cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) Q"
  shows "cuok (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) (\<lambda>s. fin cfg s Q)"
  using PF
proof (induction projs)
  case Nil
  with imit show ?case by simp
next
  case (Cons q projs)
  obtain bv T targ where q: "q = (bv, T, targ)" by (cases q)
  from Cons.prems q obtain Us bary where st: "strip_type env T = return (Us, bary)"
    and gs: "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail Q \<longrightarrow>
        cuok (projenv cfg vname rb targs u env dps base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s Q)"
    by auto
  have IH: "cuok (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) (\<lambda>s. fin cfg s Q)"
    using Cons.IH Cons.prems by simp
  show ?case unfolding q matchfun.simps
    by (rule cuok_liftM_return[OF st], rule cuok_bindW[OF IH], simp,
        rule foldrW_cuok_fin[where Q = Q]) (use gs in auto)
qed

lemma matchfun_okW: "cuok (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) P \<Longrightarrow>
    \<exists>s. okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) s \<and> P s"
  using noCU_matchfun[of cfg vname rb targs u env dps uhead uargs base Ts projs]
  unfolding cuok_def noCU_def by auto



subsection \<open>Copies under abstractions and of arguments\<close>

lemma mc_pushes_append: "pushes e (Ts @ Us) = pushes (pushes e Ts) Us"
  by (induction Ts arbitrary: e) simp_all

lemma typings_append: "e \<tturnstile> xs : Xs \<Longrightarrow> e \<tturnstile> ys : Ys \<Longrightarrow> e \<tturnstile> xs @ ys : Xs @ Ys"
  unfolding mf_typings_iff by (rule list_all2_appendI)

lemma ilength_Cons: "ilength (x # xs) = ilength xs + 1"
  by (simp add: ilength_eq integer_of_nat_eq_of_nat)

lemma pok_incr:
  assumes p: "pok A env rb X t t" and cT: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
    and tvT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "pok A env ((a, T) # rb) X (incr_boundvars 1 t) (incr_boundvars 1 t)"
  unfolding pok_def
proof (intro conjI allI impI)
  note pd = pokD[OF p]
  show "vars (incr_boundvars 1 t) \<union> vars (incr_boundvars 1 t) \<subseteq> X \<union> evars env"
    using pd(1) by (simp add: incr_boundvars_def vars_incr_bv)
  show "ttvars (incr_boundvars 1 t) \<union> ttvars (incr_boundvars 1 t) \<union> btvars ((a, T) # rb) \<union> vtvars X \<subseteq>
      tvars_env (tyenv env) \<union> A"
    using pd(3,5,6) tvT by (auto simp: incr_boundvars_def btvars_def)
  have "\<not> loose_bvar (incr_bv 1 0 t) (ilength rb + 1)"
    using mf_loose_bvar_incr_bv[of 1 0 "ilength rb" t] pd(7) ilength_nonneg[of rb] by simp
  then show "\<not> loose_bvar (incr_boundvars 1 t) (ilength ((a, T) # rb))"
    by (simp add: incr_boundvars_def ilength_Cons)
  then show "\<not> loose_bvar (incr_boundvars 1 t) (ilength ((a, T) # rb))" .
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  from pd(9)[OF \<rho>] obtain e U where bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> t : U" by blast
  have "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> (incr_boundvars 1 t) : U"
    using lift_type[OF ty, of 0] by (simp add: incr_boundvars_1)
  with bs_env_Cons[OF bs cT[OF \<rho>]] show "\<exists>e T'. bs_env \<rho> e ((a, T) # rb) \<and>
      e \<turnstile> inst \<rho> (incr_boundvars 1 t) : T' \<and> e \<turnstile> inst \<rho> (incr_boundvars 1 t) : T'" by blast
qed

lemma pok_Bound0:
  assumes cT: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
    and tvT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" and tvb: "btvars rb \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and bsex: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e. bs_env \<rho> e rb"
  shows "pok A env ((a, T) # rb) X (Bound 0) (Bound 0)"
  unfolding pok_def
proof (intro conjI allI impI)
  show "vars (Bound 0) \<union> vars (Bound 0) \<subseteq> X \<union> evars env" by simp
  show "ttvars (Bound 0) \<union> ttvars (Bound 0) \<union> btvars ((a, T) # rb) \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    using tvT tvb by (auto simp: btvars_def ttvars_def)
  show "\<not> loose_bvar (Bound 0) (ilength ((a, T) # rb))" "\<not> loose_bvar (Bound 0) (ilength ((a, T) # rb))"
    using ilength_nonneg[of rb] by (simp_all add: ilength_Cons integer_arith)
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  from bsex[OF \<rho>] obtain e where bs: "bs_env \<rho> e rb" by blast
  have "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> Bound 0 : tsubst \<rho> T" by auto
  with bs_env_Cons[OF bs cT[OF \<rho>]] show "\<exists>e T'. bs_env \<rho> e ((a, T) # rb) \<and>
      e \<turnstile> inst \<rho> (Bound 0) : T' \<and> e \<turnstile> inst \<rho> (Bound 0) : T'" by auto
qed

lemma psh_incr: "psh Fd Ft t \<Longrightarrow> psh Fd Ft (incr_boundvars 1 t)"
  by (simp add: psh_def incr_boundvars_def vars_incr_bv)

lemma ptok_incr: "ptok Fd Ft targs \<Longrightarrow> ptok Fd Ft (map (incr_boundvars 1) targs @ [Bound 0])"
  by (auto simp: ptok_def incr_boundvars_def)

lemma cpre_Abs:
  assumes cp: "cpre Fd Ft m0 A K X env dps rb targs Tts" and tvT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and cT: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
    and bsex: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e. bs_env \<rho> e rb"
  shows "cpre Fd Ft m0 A K X env dps ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) (Tts @ [T])"
proof -
  note c = cpreD[OF cp]
  let ?targs = "map (incr_boundvars 1) targs @ [Bound 0]"
  have bt: "btvars ((a, T) # rb) \<subseteq> tvars_env (tyenv env) \<union> A" using c(5) tvT by (auto simp: btvars_def)
  have pk: "\<forall>t\<in>set ?targs. pok A env ((a, T) # rb) X t t \<and> psh Fd Ft t"
  proof
    fix t assume "t \<in> set ?targs"
    then consider s where "s \<in> set targs" "t = incr_boundvars 1 s" | "t = Bound 0" by auto
    then show "pok A env ((a, T) # rb) X t t \<and> psh Fd Ft t"
    proof cases
      case 1
      with c(6)[OF 1(1)] show ?thesis using pok_incr[OF _ cT tvT] psh_incr by blast
    next
      case 2
      have "pok A env ((a, T) # rb) X (Bound 0) (Bound 0)" by (rule pok_Bound0[OF cT tvT _ bsex]) (use c(4,5) in auto)
      then show ?thesis using 2 by (simp add: psh_def)
    qed
  qed
  have ty: "e \<tturnstile> map (inst \<rho>) ?targs : map (tsubst \<rho>) (Tts @ [T])"
    if \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e ((a, T) # rb)" for \<rho> e
  proof -
    from bsex[OF \<rho>] obtain e0 where bs0: "bs_env \<rho> e0 rb" by blast
    note bs1 = bs_env_Cons[OF bs0 cT[OF \<rho>], of a]
    have "e0 \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Tts" by (rule c(8)[OF \<rho> bs0])
    from lift_types[OF this, of 0 "tsubst \<rho> T"]
    have "e0\<langle>0:tsubst \<rho> T\<rangle> \<tturnstile> map (inst \<rho>) (map (incr_boundvars 1) targs) : map (tsubst \<rho>) Tts"
      by (simp add: incr_boundvars_1 comp_def)
    moreover have "e0\<langle>0:tsubst \<rho> T\<rangle> \<tturnstile> map (inst \<rho>) [Bound 0] : map (tsubst \<rho>) [T]" by auto
    ultimately have "e0\<langle>0:tsubst \<rho> T\<rangle> \<tturnstile> map (inst \<rho>) ?targs : map (tsubst \<rho>) (Tts @ [T])"
      using typings_append by fastforce
    moreover have "\<forall>t\<in>set ?targs. \<not> loose_bvar t (ilength ((a, T) # rb))" using pk pokD(7) by blast
    then have "\<forall>t\<in>set (map (inst \<rho>) ?targs). \<not> loose_bvar t (ilength ((a, T) # rb))" by simp
    ultimately show ?thesis by (rule typings_bs[OF bs1 bs])
  qed
  show ?thesis
    unfolding cpre_def using c(1-5,7,9-12) bt pk ty ptok_incr[OF c(11)] by auto
qed

lemma upre_Abs:
  assumes up: "upre Fd Ft A X env rb (Abs a T body)" and ei: "einv A K env"
  shows "upre Fd Ft A X env ((a, T) # rb) body" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
    "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e. bs_env \<rho> e rb"
proof -
  have p: "pok A env rb X (Abs a T body) (Abs a T body)" and s: "psh Fd Ft (Abs a T body)"
    using up by (simp_all add: upre_def)
  note pd = pokD[OF p]
  show tvT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using pd(3) by (simp add: ttvars_def)
  show cT: "cert_typ alg ar (tsubst \<rho> T)" if \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
    using pd(9)[OF \<rho>] by auto
  show "\<exists>e. bs_env \<rho> e rb" if \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
    using pd(9)[OF \<rho>] by auto
  have "pok A env ((a, T) # rb) X body body"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars body \<union> vars body \<subseteq> X \<union> evars env" using pd(1) by simp
    show "ttvars body \<union> ttvars body \<union> btvars ((a, T) # rb) \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
      using pd(3,5,6) tvT by (auto simp: btvars_def ttvars_def)
    show "\<not> loose_bvar body (ilength ((a, T) # rb))" "\<not> loose_bvar body (ilength ((a, T) # rb))"
      using pd(7) by (simp_all add: ilength_Cons algebra_simps)
    fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
    from pd(9)[OF \<rho>] obtain e U where bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> (Abs a T body) : U" by blast
    from ty obtain W where c: "cert_typ alg ar (tsubst \<rho> T)" and tb: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> body : W"
      by auto
    from bs_env_Cons[OF bs c] tb show "\<exists>e T'. bs_env \<rho> e ((a, T) # rb) \<and> e \<turnstile> inst \<rho> body : T' \<and>
        e \<turnstile> inst \<rho> body : T'" by blast
  qed
  moreover have "psh Fd Ft body" using s by (simp add: psh_def)
  ultimately show "upre Fd Ft A X env ((a, T) # rb) body" by (simp add: upre_def)
qed

lemma sat_Abs: "sat env rb (Abs a T body) \<Longrightarrow> sat env ((a, T) # rb) body"
proof -
  assume "sat env rb (Abs a T body)"
  then obtain e U where bs: "bs_env (rho0 env) e rb" and ty: "e \<turnstile> inst (rho0 env) (Abs a T body) : U"
    and n: "nabs (Abs a T body) = arity U" by (auto simp: sat_def)
  from ty obtain W where c: "cert_typ alg ar (tsubst (rho0 env) T)"
    and tb: "e\<langle>0:tsubst (rho0 env) T\<rangle> \<turnstile> inst (rho0 env) body : W" and U: "U = tsubst (rho0 env) T \<rightarrow>\<^sub>T W"
    by auto
  from bs_env_Cons[OF bs c] tb n U show "sat env ((a, T) # rb) body" unfolding sat_def by auto
qed

lemma cpy_Abs:
  assumes cp: "cpy A' X' env' NV ((a, T) # rb) body (Tts @ [T]) c"
    and tvT: "tvars T \<subseteq> tvars_env (tyenv env') \<union> A'"
  shows "cpy A' X' env' NV rb (Abs a T body) Tts (Abs a T c)"
  unfolding cpy_def
proof (intro conjI allI impI)
  note d = cpyD[OF cp]
  show "vns (Abs a T c) \<subseteq> NV" "vars (Abs a T c) \<subseteq> X' \<union> evars env'" using d(1,2) by simp_all
  show "ttvars (Abs a T c) \<subseteq> tvars_env (tyenv env') \<union> A'" using d(3) tvT by (simp add: ttvars_def)
  show "\<not> loose_bvar (Abs a T c) (ilength Tts)"
    using d(4) by (simp add: ilength_eq integer_of_nat_eq_of_nat algebra_simps)
  fix \<rho> e U e' assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb"
    and ty: "e \<turnstile> inst \<rho> (Abs a T body) : U"
  from ty obtain W where c: "cert_typ alg ar (tsubst \<rho> T)" and tb: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> body : W"
    and U: "U = tsubst \<rho> T \<rightarrow>\<^sub>T W" by auto
  have "pushes e' (map (tsubst \<rho>) (Tts @ [T])) \<turnstile> inst \<rho> c : W" by (rule d(5)[OF \<rho> bs_env_Cons[OF bs c] tb])
  then have "(pushes e' (map (tsubst \<rho>) Tts))\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> c : W" by (simp add: mc_pushes_append)
  with c U show "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> (Abs a T c) : U" by auto
qed

lemma upre_arg:
  assumes up: "upre Fd Ft A X env rb u" and a: "a \<in> set (snd (strip_comb u))"
  shows "upre Fd Ft A X env rb a"
proof -
  have p: "pok A env rb X u u" and s: "psh Fd Ft u" using up by (simp_all add: upre_def)
  note pd = pokD[OF p]
  have u: "u = head_of u \<degree>\<degree> snd (strip_comb u)" by (rule t_apps)
  have va: "vars a \<subseteq> vars u" using a by (subst u) (auto simp: vars_apps)
  have ta: "ttvars a \<subseteq> ttvars u" using a by (subst u) (auto simp: ttvars_apps)
  have la: "\<not> loose_bvar a (ilength rb)" using a pd(7) u by (metis loose_bvar_apps)
  have "pok A env rb X a a"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars a \<union> vars a \<subseteq> X \<union> evars env" using va pd(1) by blast
    show "ttvars a \<union> ttvars a \<union> btvars rb \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" using ta pd(3,5,6) by blast
    show "\<not> loose_bvar a (ilength rb)" "\<not> loose_bvar a (ilength rb)" by (fact la)+
    fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
    from pd(9)[OF \<rho>] obtain e U where bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> u : U" by blast
    from ty[unfolded u[THEN arg_cong[of _ _ "inst \<rho>"]] inst_apps] a obtain V where "e \<turnstile> inst \<rho> a : V"
      using typing_args by fastforce
    with bs show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> a : T \<and> e \<turnstile> inst \<rho> a : T" by blast
  qed
  moreover have "psh Fd Ft a"
  proof -
    have "dead Fd u" using s by (simp add: psh_def)
    then have "dead Fd a" using a by (subst (asm) u) (auto simp: dd_list_comb[unfolded list_comb_apps])
    moreover have "vns a \<inter> Ft = {}" using s va by (auto simp: psh_def)
    ultimately show ?thesis by (simp add: psh_def)
  qed
  ultimately show ?thesis by (simp add: upre_def)
qed


lemma set_lem4: "a \<subseteq> b \<Longrightarrow> b \<union> t \<union> d \<subseteq> r \<Longrightarrow> a \<union> t \<union> d \<subseteq> r"
  by blast

lemma PECI: "cres Fd Ft A X env D A' K' X' env' dps' NV \<Longrightarrow> cpy A' X' env' NV rb u Tts c \<Longrightarrow>
    PEC Fd Ft A X env D rb u Tts (El_C c env' dps')"
  unfolding PEC_def by blast

lemma set_lem3: "a \<subseteq> d \<Longrightarrow> d \<subseteq> r \<Longrightarrow> v \<subseteq> r \<union> n \<Longrightarrow> a \<union> v \<subseteq> r \<union> n"
  by blast

lemma sinv_acyc: "sinv A K X env dps \<Longrightarrow> acyc env"
  unfolding sinv_def using einvD(3) by blast

lemma cpy_NV: "cpy A' X' env' NV rb u Tts c \<Longrightarrow> NV \<subseteq> NV' \<Longrightarrow> cpy A' X' env' NV' rb u Tts c"
  unfolding cpy_def by blast

text \<open>The imitation by a constant or free variable:\<close>

lemma cpy_imit:
  assumes h: "h = Const c0 C \<or> h = Free c0 C" and tvh: "ttvars h \<subseteq> tvars_env (tyenv env') \<union> A'"
    and cs: "list_all2 (\<lambda>a c. cpy A' X' env' NV rb a Tts c) uargs cs"
  shows "cpy A' X' env' NV rb (h \<degree>\<degree> uargs) Tts (list_comb h cs)"
  unfolding cpy_def
proof (intro conjI allI impI)
  have hv: "vars h = {}" "\<not> loose_bvar h k" "closed h" for k using h by (auto simp: closed_def)
  have l: "length cs = length uargs" using list_all2_lengthD[OF cs] by simp
  have cc: "cpy A' X' env' NV rb (uargs ! i) Tts (cs ! i)" if "i < length cs" for i
    using list_all2_nthD2[OF cs that] .
  have ex: "\<exists>a. cpy A' X' env' NV rb a Tts c" if "c \<in> set cs" for c
  proof -
    from that obtain i where "i < length cs" "cs ! i = c" by (auto simp: in_set_conv_nth)
    with cc show ?thesis by blast
  qed
  have d1: "vns c \<subseteq> NV" "vars c \<subseteq> X' \<union> evars env'" "ttvars c \<subseteq> tvars_env (tyenv env') \<union> A'"
    "\<not> loose_bvar c (ilength Tts)" if "c \<in> set cs" for c
    using cpyD(1-4)[of A' X' env' NV rb _ Tts c] ex[OF that] by blast+
  have d: "\<forall>c\<in>set cs. vns c \<subseteq> NV" "\<forall>c\<in>set cs. vars c \<subseteq> X' \<union> evars env'"
    "\<forall>c\<in>set cs. ttvars c \<subseteq> tvars_env (tyenv env') \<union> A'" "\<forall>c\<in>set cs. \<not> loose_bvar c (ilength Tts)"
    using d1 by blast+
  show "vns (list_comb h cs) \<subseteq> NV" using d(1) hv(1) by (auto simp: list_comb_apps vars_apps)
  show "vars (list_comb h cs) \<subseteq> X' \<union> evars env'" using d(2) hv(1) by (auto simp: list_comb_apps vars_apps)
  show "ttvars (list_comb h cs) \<subseteq> tvars_env (tyenv env') \<union> A'"
    using d(3) tvh by (auto simp: list_comb_apps ttvars_apps)
  show "\<not> loose_bvar (list_comb h cs) (ilength Tts)" using d(4) hv(2) by (auto simp: list_comb_apps loose_bvar_apps)
  fix \<rho> e U e' assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb"
    and ty: "e \<turnstile> inst \<rho> (h \<degree>\<degree> uargs) : U"
  from ty[unfolded inst_apps] obtain Vs where th: "e \<turnstile> inst \<rho> h : Vs \<Rrightarrow> U"
    and ta: "e \<tturnstile> map (inst \<rho>) uargs : Vs" by (rule list_app_typeE)
  have th': "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> h : Vs \<Rrightarrow> U"
    using typing_closed[OF th] hv(3) by (simp add: closed_def)
  have lV: "length Vs = length uargs" using typings_nth[OF ta] by simp
  have "pushes e' (map (tsubst \<rho>) Tts) \<tturnstile> map (inst \<rho>) cs : Vs"
    unfolding mf_typings_iff
  proof (rule list_all2_all_nthI)
    show "length (map (inst \<rho>) cs) = length Vs" using l lV by simp
    fix i assume i: "i < length (map (inst \<rho>) cs)"
    then have i': "i < length cs" by simp
    have "e \<turnstile> inst \<rho> (uargs ! i) : Vs ! i" using typings_nth[OF ta] i' l by auto
    from cpyD(5)[OF cc[OF i'] \<rho> bs this]
    show "typing (pushes e' (map (tsubst \<rho>) Tts)) (map (inst \<rho>) cs ! i) (Vs ! i)" using i' by simp
  qed
  from list_app_typeI[OF th' this] show "pushes e' (map (tsubst \<rho>) Tts) \<turnstile> inst \<rho> (list_comb h cs) : U"
    by (simp add: list_comb_apps inst_apps)
qed

context
  fixes cfg :: cfg and vname :: name and m0 :: integer and S0 :: "indexname set" and Fd Ft :: "indexname set"
  assumes cfg: "cfg_alg cfg = alg" and finS0: "finite S0"
    and regime: "Fd = {x. m0 < snd x} \<and> Ft = {} \<or> Fd = {} \<and> Ft = {x. m0 < snd x}"
begin

text \<open>The copies of the arguments of an imitation, given the copies of each argument:\<close>

lemma copyargs_fin:
  assumes CC: "\<And>A' K' X' env' dps' a us. ((pmu S0 env', rsz env' a), (c, N)) \<in> less_than <*lex*> less_than \<Longrightarrow>
      cpre Fd Ft m0 A' K' X' env' dps' rb targs Tts \<Longrightarrow> upre Fd Ft A' X' env' rb a \<Longrightarrow>
      poldin m0 S0 env' (vns a \<union> vnsl targs \<union> vdps dps') \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname rb targs a us env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV. x = El_D (c' # us) env'' dps'' \<and>
          cres Fd Ft A' X' env' (vns a \<union> vnsl targs \<union> vdps dps') A'' K'' X'' env'' dps'' NV \<and>
          cpy A'' X'' env'' NV rb a Tts c')"
    and cp: "cpre Fd Ft m0 A K X env dps rb targs Tts" and mu: "pmu S0 env = c"
  shows "\<forall>a\<in>set uargs. upre Fd Ft A X env rb a \<and> rsz env a < N \<Longrightarrow>
    poldin m0 S0 env (vnsl uargs \<union> vnsl targs \<union> vdps dps) \<Longrightarrow>
    fin cfg (copyargs vname rb targs env dps uargs)
      (PED Fd Ft A X env (vnsl uargs \<union> vnsl targs \<union> vdps dps) rb uargs Tts)"
proof (induction uargs)
  case Nil
  note c = cpreD[OF cp]
  have "cres Fd Ft A X env (vnsl [] \<union> vnsl targs \<union> vdps dps) A K X env dps {}"
    by (rule cres_refl) (use c in auto)
  then have "PED Fd Ft A X env (vnsl [] \<union> vnsl targs \<union> vdps dps) rb [] Tts (El_D [] env dps)"
    unfolding PED_def by blast
  then show ?case by (simp add: fin_Single)
next
  case (Cons a uargs)
  note c = cpreD[OF cp]
  have bb: "bbelow env" by (rule sinv_bbelow[OF c(3)])
  have ac: "acyc env" by (rule sinv_acyc[OF c(3)])
  define D where "D = vnsl (a # uargs) \<union> vnsl targs \<union> vdps dps"
  define D' where "D' = vnsl uargs \<union> vnsl targs \<union> vdps dps"
  have DD': "D' \<subseteq> D" by (auto simp: D_def D'_def)
  have DD'': "D' \<subseteq> vreach env D" using DD' vreach_incl[of D env] by (rule order_trans)
  have oD: "poldin m0 S0 env D" using Cons.prems(2) by (simp add: D_def)
  have "poldin m0 S0 env D'" by (rule poldin_mono[OF oD DD''])
  then have IH: "fin cfg (copyargs vname rb targs env dps uargs) (PED Fd Ft A X env D' rb uargs Tts)"
    using Cons.IH Cons.prems(1) unfolding D'_def by simp
  have ua: "upre Fd Ft A X env rb a" and ia: "rsz env a < N" using Cons.prems(1) by simp_all
  have aD: "vns a \<union> vnsl targs \<subseteq> D" by (auto simp: D_def)
  have step: "\<exists>cs. okW (copycons cfg vname rb targs a us env' dps') cs \<and>
      fin cfg cs (PED Fd Ft A X env D rb (a # uargs) Tts)"
    if cr': "cres Fd Ft A X env D' A' K' X' env' dps' NV"
      and cps: "list_all2 (\<lambda>a' c. cpy A' X' env' NV rb a' Tts c) uargs us" for us env' dps' A' K' X' NV
  proof -
    have cr: "cres Fd Ft A X env D A' K' X' env' dps' NV" by (rule cres_mono[OF cr' DD''])
    note t = cresD[OF cr]
    have cp': "cpre Fd Ft m0 A' K' X' env' dps' rb targs Tts" by (rule cpre_ext[OF cp cr])
    have ua': "upre Fd Ft A' X' env' rb a" by (rule upre_ext[OF ua cr])
    have Da: "(vns a \<union> vnsl targs) \<union> D = D" using aD by blast
    have oa': "poldin m0 S0 env' (vns a \<union> vnsl targs \<union> vdps dps')"
      using poldin_ext[where Y = "vns a \<union> vnsl targs", OF cr _ c(12) bb] oD Da by simp
    have lex: "((pmu S0 env', rsz env' a), (c, N)) \<in> less_than <*lex*> less_than"
    proof (cases "pmu S0 env' < pmu S0 env")
      case True
      with mu show ?thesis by simp
    next
      case False
      with pmu_mono[OF finS0 t(7)] have eq: "pmu S0 env' = pmu S0 env" by simp
      have "vns a \<subseteq> vreach env D" using aD vreach_incl[of D env] by blast
      then have "poldin m0 S0 env (vns a)" by (rule poldin_mono[OF oD])
      moreover have "psh Fd Ft a" using ua by (simp add: upre_def)
      ultimately have "rsz env' a = rsz env a" by (rule rsz_stable[OF finS0 regime ac c(9) cr _ _ eq])
      with ia eq mu show ?thesis by simp
    qed
    from CC[OF lex cp' ua' oa'] obtain cs where cc: "okW (copycons cfg vname rb targs a us env' dps') cs"
      and fc: "fin cfg cs (\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV'. x = El_D (c' # us) env'' dps'' \<and>
          cres Fd Ft A' X' env' (vns a \<union> vnsl targs \<union> vdps dps') A'' K'' X'' env'' dps'' NV' \<and>
          cpy A'' X'' env'' NV' rb a Tts c')"
      by blast
    have "fin cfg cs (PED Fd Ft A X env D rb (a # uargs) Tts)"
    proof (rule fin_mono[OF fc])
      fix x assume "\<exists>c' env'' dps'' A'' K'' X'' NV'. x = El_D (c' # us) env'' dps'' \<and>
          cres Fd Ft A' X' env' (vns a \<union> vnsl targs \<union> vdps dps') A'' K'' X'' env'' dps'' NV' \<and>
          cpy A'' X'' env'' NV' rb a Tts c'"
      then obtain c' env'' dps'' A'' K'' X'' NV' where xe: "x = El_D (c' # us) env'' dps''"
        and cr2: "cres Fd Ft A' X' env' (vns a \<union> vnsl targs \<union> vdps dps') A'' K'' X'' env'' dps'' NV'"
        and cu: "cpy A'' X'' env'' NV' rb a Tts c'"
        by blast
      have "vns a \<union> vnsl targs \<union> vdps dps' \<subseteq> vreach env D \<union> NV"
        using set_lem3[OF aD vreach_incl[of D env] t(11)] by (simp add: Un_assoc)
      from cres_trans[OF cr cr2 bb this] have cr3: "cres Fd Ft A X env D A'' K'' X'' env'' dps'' (NV \<union> NV')" .
      have "cpy A'' X'' env'' (NV \<union> NV') rb a Tts c'" by (rule cpy_NV[OF cu]) blast
      moreover have "list_all2 (\<lambda>a' c. cpy A'' X'' env'' (NV \<union> NV') rb a' Tts c) uargs us"
        by (rule list_all2_mono[OF cps]) (rule cpy_ext[OF _ cr2], auto)
      ultimately have "list_all2 (\<lambda>a' c. cpy A'' X'' env'' (NV \<union> NV') rb a' Tts c) (a # uargs) (c' # us)"
        by simp
      with xe cr3 show "PED Fd Ft A X env D rb (a # uargs) Tts x" unfolding PED_def by blast
    qed
    with cc show ?thesis by blast
  qed
  have "fin cfg (S_Maps vname rb targs a (copyargs vname rb targs env dps uargs)) (PED Fd Ft A X env D rb (a # uargs) Tts)"
  proof (rule fin_Maps, rule fin_mono[OF IH])
    fix x assume "PED Fd Ft A X env D' rb uargs Tts x"
    then obtain us env' dps' A' K' X' NV where x: "x = El_D us env' dps'"
      and cr': "cres Fd Ft A X env D' A' K' X' env' dps' NV"
      and cps: "list_all2 (\<lambda>a' c. cpy A' X' env' NV rb a' Tts c) uargs us"
      unfolding PED_def by blast
    from step[OF cr' cps] x show "\<exists>us env' dps' cs. x = El_D us env' dps' \<and>
        okW (copycons cfg vname rb targs a us env' dps') cs \<and> fin cfg cs (PED Fd Ft A X env D rb (a # uargs) Tts)"
      by blast
  qed
  then show ?case by (simp add: D_def)
qed


text \<open>
  \<^const>\<open>mc\<close> on a term in head normal form: by induction on the size of the term, given the
  finiteness of the copies of arguments with a smaller measure.
\<close>

lemma mc_fin_aux:
  assumes CC: "\<And>A' K' X' env' dps' rb' targs' Tts' a us. ((pmu S0 env', rsz env' a), (c, N)) \<in> less_than <*lex*> less_than \<Longrightarrow>
      cpre Fd Ft m0 A' K' X' env' dps' rb' targs' Tts' \<Longrightarrow> upre Fd Ft A' X' env' rb' a \<Longrightarrow>
      poldin m0 S0 env' (vns a \<union> vnsl targs' \<union> vdps dps') \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname rb' targs' a us env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV. x = El_D (c' # us) env'' dps'' \<and>
          cres Fd Ft A' X' env' (vns a \<union> vnsl targs' \<union> vdps dps') A'' K'' X'' env'' dps'' NV \<and>
          cpy A'' X'' env'' NV rb' a Tts' c')"
  shows "cpre Fd Ft m0 A K X env dps rb targs Tts \<Longrightarrow> upre Fd Ft A X env rb u \<Longrightarrow> hnf env u \<Longrightarrow> sat env rb u \<Longrightarrow>
    poldin m0 S0 env (vns u \<union> vnsl targs \<union> vdps dps) \<Longrightarrow> pmu S0 env = c \<Longrightarrow> rsz env u \<le> N \<Longrightarrow>
    \<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
      fin cfg sq (PEC Fd Ft A X env (vns u \<union> vnsl targs \<union> vdps dps) rb u Tts)"
proof (induction "size u" arbitrary: rb targs Tts u rule: less_induct)
  case less
  note cp = less.prems(1) and up = less.prems(2) and hu = less.prems(3) and st = less.prems(4)
    and o = less.prems(5) and mu = less.prems(6) and szN = less.prems(7)
  note c = cpreD[OF cp]
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env"
  let ?D = "vns u \<union> vnsl targs \<union> vdps dps"
  let ?Q = "PEC Fd Ft A X env ?D rb u Tts"
  have ei: "einv A K env" and wi: "winv env X" using c(3) by (simp_all add: sinv_def)
  note r0 = einv_rho0[OF ei]
  have p: "pok A env rb X u u" and su: "psh Fd Ft u" using up by (simp_all add: upre_def)
  from pokD(9)[OF p r0] obtain e0 U0 where bs0: "bs_env ?\<rho> e0 rb" and ty0: "e0 \<turnstile> inst ?\<rho> u : U0" by blast
  have tyu0: "e0 \<turnstile> inst ?\<rho> (unf env u) : U0" by (rule typing_unf0[OF ei wi pokD(1)[OF p] ty0])
  from mc_types[OF cp up] obtain T0 base Ts' where
    ty: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
      "tvars T0 \<subseteq> tvars_env ?\<theta> \<union> A" "tvars base \<subseteq> tvars_env ?\<theta> \<union> A"
      "mapM (fastype env rb) targs = return Ts'" "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env ?\<theta> \<union> A"
      "\<forall>\<rho>. tsol ?\<theta> \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts"
    by blast
  have TsEq: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts" if "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
    using ty(7) that by blast
  have T0': "ok (fastype env rb (head_of u)) T0" and base': "ok (body_type env T0) base"
    and Ts'': "ok (mapM (fastype env rb) targs) Ts'" using ty by (simp_all add: return_def)
  note mcu = mc_unfold[OF ty(1,2,5), of cfg vname dps]
  have lTs': "length Ts' = length targs" using Ts'' by (simp add: ok_mapM list_all2_lengthD)
  have tyB: "U = tsubst \<rho> base"
    if nA: "\<not> is_Abs u" and \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : U" for \<rho> e U
    by (rule sat_base[OF ei st nA T0' base' \<rho>(1) bs tyu])
  have rigid_case: ?case if hr: "rigid (head_of u)"
  proof -
    have nA: "\<not> is_Abs u" using hr by (cases u) auto
    from make_projs_term[OF lTs', of u targs] obtain projs where mp: "okW (make_projs u targs Ts' targs) projs"
      by blast
    note mpp = mf_make_projs_props[OF mp]
    have mcR: "mc cfg vname rb targs u env dps = bindW (make_projs u targs Ts' targs)
        (\<lambda>projs. matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) base Ts' (rev projs))"
      unfolding mcu head_of_strip_comb[symmetric] using hr by (cases "head_of u") simp_all
    have cbase: "cert_typ alg ar (tnorm ?\<theta> base)"
      using tyB[OF nA r0 bs0 ty0] bs_env_cert[OF bs0 ty0 pokD(7)[OF p]] by simp
    have tya0: "e0 \<tturnstile> map (inst ?\<rho>) targs : map (tsubst ?\<rho>) Tts" by (rule c(8)[OF r0 bs0])
    have cTs0: "\<forall>T\<in>set Tts. cert_typ alg ar (tsubst ?\<rho> T)"
      by (rule mf_cert_targs[OF bs0 tya0]) (use c(6) pokD(7) in blast)
    have PF: "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>Us bary. strip_type env T = return (Us, bary) \<and>
        (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail ?Q \<longrightarrow>
          cuok (projenv cfg vname rb targs u env dps base Ts' bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q))"
    proof (clarify)
      fix bv T targ assume "(bv, T, targ) \<in> set (rev projs)"
      then obtain k where k: "k < length targs" "bv = Bound (integer_of_nat (length targs - 1 - k))"
        "T = Ts' ! k" "targ = targs ! k"
        using mpp by fastforce
      have tvT: "tvars T \<subseteq> tvars_env ?\<theta> \<union> A" using ty(6) k(1,3) lTs' by simp
      from binder_types_term[OF einvD(2)[OF ei] refl tvT] obtain Us where bU: "binder_types env T = return Us"
        by blast
      from body_type_term[OF einvD(2)[OF ei] refl tvT] obtain bary where
        bB: "body_type env T = return bary" "tvars bary \<subseteq> tvars_env ?\<theta> \<union> A" by blast
      have tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env ?\<theta> \<union> A"
        using mf_binder_types_sound[OF bU[unfolded return_def] refl einvD(6)[OF ei]] tvT by blast
      have sT: "strip_type env T = return (Us, bary)" using bU bB by (simp add: strip_type_def)
      have cbary: "cert_typ alg ar (tnorm ?\<theta> bary)"
      proof -
        have "tsubst ?\<rho> (Ts' ! k) = tsubst ?\<rho> (Tts ! k)"
          using arg_cong[OF TsEq[OF r0], of "\<lambda>xs. xs ! k"] k(1) lTs' c(7) by simp
        moreover have "cert_typ alg ar (tsubst ?\<rho> (Tts ! k))" using cTs0 k(1) c(7) by simp
        moreover have "tsubst ?\<rho> (Ts' ! k) = map (tsubst ?\<rho>) Us \<Rrightarrow> tsubst ?\<rho> bary"
          by (rule strip_type_sound[OF _ r0(1)]) (use sT k(3) in \<open>simp add: return_def\<close>)
        ultimately show ?thesis by (simp add: cert_typ_funs)
      qed
      have "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail ?Q \<longrightarrow>
          cuok (projenv cfg vname rb targs u env dps base Ts' bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q)"
      proof (intro ballI allI impI)
        fix p tail assume t: "fin cfg tail ?Q"
        obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
        note gs = gentvars_simps[OF g]
        have si0: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env0 dps" by (rule sinv_gentvars[OF c(3) g])
        have ei0: "einv (A \<union> ntv Cs) (K \<union> ntv Cs) env0" using si0 by (simp add: sinv_def)
        have cC: "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)"
        proof
          fix C assume "C \<in> set Cs"
          then obtain a' where "C = TVar a' []" using gs(6) by blast
          then have "cert_typ alg ar C" by (simp add: cert_typ_def sort_ok_def)
          then show "cert_typ alg ar (tnorm (tyenv env0) C)" by (rule cert_tnorm[OF ei0])
        qed
        have Pc: "cuok (proj_unify cfg base bary Cs env0) (\<lambda>env'. sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' dps \<and>
            tenv env' = tenv env0 \<and> extends env0 env' \<and> tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and>
            (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
          by (rule proj_unify_sinv[OF cfg finite_UnI[OF c(2) finite_ntv] si0])
            (use ty(4) bB(2) gs(2) cbase cbary cC in \<open>auto simp: ntv_def\<close>)
        show "cuok (projenv cfg vname rb targs u env dps base Ts' bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q)"
        proof (rule projenv_fin[OF g Pc _ t])
          fix env' env'' args
          assume P: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' dps \<and>
            tenv env' = tenv env0 \<and> extends env0 env' \<and> tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and>
            (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base))"
            and ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)"
          from P have post: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' dps" "tenv env' = tenv env0" "extends env0 env'"
            "tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env')"
            "\<And>\<rho>. tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)" by blast+
          have stT: "ok (strip_type env (Ts' ! k)) (Us, bary)" using sT k(3) by (simp add: return_def)
          show "cuok (SIMPL (cfg_alg cfg) env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
              (\<lambda>(env2, fr, ff). ?Q (El_C (list_comb bv args) env2 (fr @ ff)))"
            unfolding cfg k(2,4)
            by (rule proj_res[OF cp up hr nA st T0' base' Ts'' ty(6) TsEq k(1) stT tvUs g post ma])
        qed
      qed
      with sT show "\<exists>Us bary. strip_type env T = return (Us, bary) \<and>
          (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail ?Q \<longrightarrow>
            cuok (projenv cfg vname rb targs u env dps base Ts' bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q))"
        by blast
    qed
    have imit: "fin cfg (case head_of u of
        Const _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | Free _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | _ \<Rightarrow> S_Empty) ?Q"
    proof (cases "\<exists>c0 C. head_of u = Const c0 C \<or> head_of u = Free c0 C")
      case True
      then obtain c0 C where h: "head_of u = Const c0 C \<or> head_of u = Free c0 C" by blast
      let ?h = "head_of u" and ?as = "snd (strip_comb u)"
      have u: "u = ?h \<degree>\<degree> ?as" by (rule t_apps)
      have tyu0': "e0 \<turnstile> inst ?\<rho> (unf env (?h \<degree>\<degree> ?as)) : U0" using tyu0 by (subst (asm) u)
      have args: "\<forall>a\<in>set ?as. upre Fd Ft A X env rb a \<and> rsz env a < N"
      proof
        fix a assume a: "a \<in> set ?as"
        have "rsz env a < rsz env (?h \<degree>\<degree> ?as)" by (rule rsz_rigid_arg[OF h tyu0' a])
        then have "rsz env a < rsz env u" by (subst u)
        with upre_arg[OF up a] szN show "upre Fd Ft A X env rb a \<and> rsz env a < N" by simp
      qed
      have vas: "vnsl ?as \<subseteq> vns u"
      proof
        fix y assume "y \<in> vnsl ?as"
        then obtain a where "a \<in> set ?as" "y \<in> vns a" by blast
        then show "y \<in> vns u" by (subst u) (auto simp: vars_apps)
      qed
      have DaD: "vnsl ?as \<union> vnsl targs \<union> vdps dps \<subseteq> vreach env ?D"
        by (rule set_lem4[OF vas vreach_incl])
      have o': "poldin m0 S0 env (vnsl ?as \<union> vnsl targs \<union> vdps dps)" by (rule poldin_mono[OF o DaD])
      from copyargs_fin[OF CC cp mu args o']
      have fa: "fin cfg (copyargs vname rb targs env dps ?as)
          (PED Fd Ft A X env (vnsl ?as \<union> vnsl targs \<union> vdps dps) rb ?as Tts)" .
      have "fin cfg (S_MapJoin ?h (copyargs vname rb targs env dps ?as)) ?Q"
      proof (rule fin_MapJoin, rule fin_mono[OF fa])
        fix x assume "PED Fd Ft A X env (vnsl ?as \<union> vnsl targs \<union> vdps dps) rb ?as Tts x"
        then obtain cs env' dps' A' K' X' NV where x: "x = El_D cs env' dps'"
          and cr: "cres Fd Ft A X env (vnsl ?as \<union> vnsl targs \<union> vdps dps) A' K' X' env' dps' NV"
          and cps: "list_all2 (\<lambda>a c. cpy A' X' env' NV rb a Tts c) ?as cs"
          unfolding PED_def by blast
        have cr': "cres Fd Ft A X env ?D A' K' X' env' dps' NV" by (rule cres_mono[OF cr DaD])
        have tvh: "ttvars ?h \<subseteq> tvars_env (tyenv env') \<union> A'"
          using ttvars_head[of u] pokD(3)[OF p] cresD(3,8)[OF cr] by blast
        have "cpy A' X' env' NV rb (?h \<degree>\<degree> ?as) Tts (list_comb ?h cs)" by (rule cpy_imit[OF h tvh cps])
        then have "cpy A' X' env' NV rb u Tts (list_comb ?h cs)" by (subst u)
        from PECI[OF cr' this] x show "\<exists>uargs env dps. x = El_D uargs env dps \<and> ?Q (El_C (list_comb ?h uargs) env dps)"
          by blast
      qed
      then show ?thesis using h by auto
    next
      case False
      then show ?thesis by (cases "head_of u") auto
    qed
    have "cuok (matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) base Ts' (rev projs))
        (\<lambda>s. fin cfg s ?Q)"
      by (rule matchfun_fin[OF PF imit])
    from matchfun_okW[OF this] obtain sq where
      "okW (matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) base Ts' (rev projs)) sq"
      "fin cfg sq ?Q" by blast
    then show ?thesis unfolding mcR using mp by auto
  qed
  show ?case
  proof (cases "head_of u")
    case (Abs a T body)
    have u: "u = Abs a T body" using Abs hu by (cases u) (auto simp: ahd_def)
    note ub = upre_Abs[OF up[unfolded u] ei]
    have cpA: "cpre Fd Ft m0 A K X env dps ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) (Tts @ [T])"
      by (rule cpre_Abs[OF cp ub(2,3,4)])
    have hb: "hnf env body" using hu u by simp
    have sb: "sat env ((a, T) # rb) body" using sat_Abs st u by simp
    have vt: "vnsl (map (incr_boundvars 1) targs @ [Bound 0]) = vnsl targs"
      by (auto simp: incr_boundvars_def vars_incr_bv)
    have Deq: "vns body \<union> vnsl (map (incr_boundvars 1) targs @ [Bound 0]) \<union> vdps dps = ?D"
      using vt u by simp
    have ob: "poldin m0 S0 env (vns body \<union> vnsl (map (incr_boundvars 1) targs @ [Bound 0]) \<union> vdps dps)"
      using o Deq by simp
    have rb: "rsz env body = rsz env u" using rsz_Abs[OF termip_typed_unf[OF tyu0[unfolded u]]] u by simp
    have sz: "size body < size u" using u by simp
    from less.hyps[OF sz cpA ub(1) hb sb ob mu] rb szN obtain sqb where
      okb: "okW (mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps) sqb"
      and fb: "fin cfg sqb (PEC Fd Ft A X env (vns body \<union> vnsl (map (incr_boundvars 1) targs @ [Bound 0]) \<union> vdps dps)
        ((a, T) # rb) body (Tts @ [T]))"
      by auto
    have okA: "okW (mc cfg vname rb targs u env dps) (S_MapAbs a T sqb)"
      using okb unfolding mcu by (simp add: u strip_comb_def)
    have "fin cfg (S_MapAbs a T sqb) ?Q"
    proof (rule fin_MapAbs, rule fin_mono[OF fb])
      fix x assume "PEC Fd Ft A X env (vns body \<union> vnsl (map (incr_boundvars 1) targs @ [Bound 0]) \<union> vdps dps)
        ((a, T) # rb) body (Tts @ [T]) x"
      then obtain c' env' dps' A' K' X' NV where x: "x = El_C c' env' dps'"
        and cr: "cres Fd Ft A X env ?D A' K' X' env' dps' NV"
        and cc: "cpy A' X' env' NV ((a, T) # rb) body (Tts @ [T]) c'"
        unfolding PEC_def Deq by blast
      have tvT: "tvars T \<subseteq> tvars_env (tyenv env') \<union> A'" using ub(2) cresD(3,8)[OF cr] by blast
      have "cpy A' X' env' NV rb (Abs a T body) Tts (Abs a T c')" by (rule cpy_Abs[OF cc tvT])
      with x cr u show "\<exists>u' env dps. x = El_C u' env dps \<and> ?Q (El_C (Abs a T u') env dps)"
        unfolding PEC_def by blast
    qed
    with okA show ?thesis by blast
  next
    case (Var w W)
    have nA: "\<not> is_Abs u" using Var by (cases u) auto
    obtain env' newhd where g: "genvar (fst w) env (foldr fun_type Ts' base) = (env', newhd)"
      by (cases "genvar (fst w) env (foldr fun_type Ts' base)")
    have mcV: "mc cfg vname rb targs u env dps =
        returnW (S_Single (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u) # dps)))"
      unfolding mcu head_of_strip_comb[symmetric] Var using g by simp
    have "?Q (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u) # dps))"
      by (rule flex_copy[OF cp up ty(5,6) TsEq ty(4) tyB[OF nA] g])
    then show ?thesis unfolding mcV by (auto intro: fin_Single)
  qed (use rigid_case head_of_not_App in auto)
qed


lemma cpy_conv:
  assumes "cpy A' X' env' NV rb u2 Tts c"
    and "\<And>\<rho> e U. tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> a : U \<Longrightarrow>
      e \<turnstile> inst \<rho> u2 : U"
  shows "cpy A' X' env' NV rb a Tts c"
  using assms unfolding cpy_def by blast

text \<open>\<^const>\<open>copycons\<close>: the copies of an argument, by well-founded induction on the measure.\<close>

lemma copycons_fin_aux:
  "\<forall>A K X env dps rb targs Tts a us. (pmu S0 env, rsz env a) = m \<longrightarrow>
    cpre Fd Ft m0 A K X env dps rb targs Tts \<longrightarrow> upre Fd Ft A X env rb a \<longrightarrow>
    poldin m0 S0 env (vns a \<union> vnsl targs \<union> vdps dps) \<longrightarrow>
    (\<exists>cs. okW (copycons cfg vname rb targs a us env dps) cs \<and>
      fin cfg cs (\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV. x = El_D (c' # us) env'' dps'' \<and>
        cres Fd Ft A X env (vns a \<union> vnsl targs \<union> vdps dps) A'' K'' X'' env'' dps'' NV \<and>
        cpy A'' X'' env'' NV rb a Tts c'))"
proof (induction m rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  case (1 m)
  show ?case
  proof (intro allI impI)
    fix A K X env dps rb targs Tts a us
    assume m: "(pmu S0 env, rsz env a) = m" and cp: "cpre Fd Ft m0 A K X env dps rb targs Tts"
      and up: "upre Fd Ft A X env rb a" and o: "poldin m0 S0 env (vns a \<union> vnsl targs \<union> vdps dps)"
    let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env" and ?Da = "vns a \<union> vnsl targs \<union> vdps dps"
    let ?R = "\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV. x = El_D (c' # us) env'' dps'' \<and>
        cres Fd Ft A X env ?Da A'' K'' X'' env'' dps'' NV \<and> cpy A'' X'' env'' NV rb a Tts c'"
    note c = cpreD[OF cp]
    have ei: "einv A K env" and wi: "winv env X" using c(3) by (simp_all add: sinv_def)
    note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
    have p: "pok A env rb X a a" and sa: "psh Fd Ft a" using up by (simp_all add: upre_def)
    have CC: "\<exists>cs. okW (copycons cfg vname rb' targs' a' us' env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV. x = El_D (c' # us') env'' dps'' \<and>
          cres Fd Ft A' X' env' (vns a' \<union> vnsl targs' \<union> vdps dps') A'' K'' X'' env'' dps'' NV \<and>
          cpy A'' X'' env'' NV rb' a' Tts' c')"
      if "((pmu S0 env', rsz env' a'), (pmu S0 env, rsz env a)) \<in> less_than <*lex*> less_than"
        "cpre Fd Ft m0 A' K' X' env' dps' rb' targs' Tts'" "upre Fd Ft A' X' env' rb' a'"
        "poldin m0 S0 env' (vns a' \<union> vnsl targs' \<union> vdps dps')"
      for A' K' X' env' dps' rb' targs' Tts' a' us'
      using "1.IH"[of "(pmu S0 env', rsz env' a')"] that m by blast
    \<comment> \<open>Normalization of the argument\<close>
    from hn_term[OF ei wi p] obtain u1 u1' where h1: "head_norm env a = return u1"
      and h1': "head_norm env a = return u1'" and pu: "pok A env rb X u1 u1'" by blast
    from h1 h1' have "u1' = u1" by (simp add: return_def)
    with pu have pu1: "pok A env rb X u1 u1" by simp
    have h1o: "ok (head_norm env a) u1" using h1 by (simp add: return_def)
    have hf1: "hnf env u1" by (rule head_norm_hnf[OF h1[unfolded return_def] refl])
    from pokD(9)[OF pu1 r0] obtain e1 U1 where bs1: "bs_env ?\<rho> e1 rb" and ty1: "e1 \<turnstile> inst ?\<rho> u1 : U1" by blast
    have tv1: "ttvars u1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" using pokD(3,5)[OF pu1] by blast
    from eta_norm_term[OF e(2) refl ty1 bs1 pokD(7)[OF pu1] tv1] hf1 obtain u2 where
      et: "eta_norm env rb u1 = return u2" and tv2: "ttvars u2 \<subseteq> tvars_env ?\<theta> \<union> A"
      and na2: "nabs u2 = arity U1" and hf2: "hnf env u2"
      by blast
    have eto: "ok (eta_norm env rb u1) u2" using et by (simp add: return_def)
    note E = eta_norm_sound[OF eto]
    have pu2: "pok A env rb X u2 u2"
      using pok_sym[OF pok_eta_norm[OF pok_sym[OF pok_eta_norm[OF pu1 eto tv2]] eto tv2]] .
    have ty2: "e1 \<turnstile> inst ?\<rho> u2 : U1" using E r0(1) bs1 ty1 pokD(7)[OF pu1] by blast
    have sat2: "sat env rb u2" unfolding sat_def using bs1 ty2 na2 by blast
    have vg: "vgood Fd Ft env" by (rule c(9))
    have sh2: "psh Fd Ft u2"
    proof -
      have "dead Fd u1" using head_norm_good(1)[OF h1o vg] sa by (simp add: psh_def)
      then have "dead Fd u2" using eta_norm_good[OF eto] by blast
      moreover have "vns u1 \<inter> Ft = {}" using head_norm_good(2)[OF h1o vg] sa by (simp add: psh_def)
      ultimately show ?thesis using eta_norm_vars[OF eto] by (simp add: psh_def)
    qed
    have up2: "upre Fd Ft A X env rb u2" using pu2 sh2 by (simp add: upre_def)
    have vu2: "vns u2 \<subseteq> vreach env (vns a)" using head_norm_vreach[OF h1o] eta_norm_vars[OF eto] by simp
    have D2: "vns u2 \<union> vnsl targs \<union> vdps dps \<subseteq> vreach env ?Da"
    proof -
      have "vreach env (vns a) \<subseteq> vreach env ?Da" by (rule vreach_subset) blast
      with vu2 have "vns u2 \<subseteq> vreach env ?Da" by (rule order_trans)
      moreover have "vnsl targs \<union> vdps dps \<subseteq> vreach env ?Da" using vreach_incl[of ?Da env] by blast
      ultimately show ?thesis by blast
    qed
    have o2: "poldin m0 S0 env (vns u2 \<union> vnsl targs \<union> vdps dps)" by (rule poldin_mono[OF o D2])
    have tyua: "e1 \<turnstile> inst ?\<rho> (unf env a) : U1"
    proof -
      from pokD(9)[OF p r0] obtain ea Ua where bsa: "bs_env ?\<rho> ea rb" and tya: "ea \<turnstile> inst ?\<rho> a : Ua" by blast
      have "ea \<turnstile> inst ?\<rho> u1 : Ua"
        using head_norm_sound[OF h1[unfolded return_def] refl r0(1) _ tya] winvD[OF wi r0] by blast
      then have "e1 \<turnstile> inst ?\<rho> u1 : Ua" by (rule typing_bs[OF bsa bs1]) (simp add: pokD(7)[OF pu1])
      then have "Ua = U1" using ty1 typing_unique by blast
      have "e1 \<turnstile> inst ?\<rho> a : Ua" by (rule typing_bs[OF bsa bs1 tya]) (simp add: pokD(7)[OF p])
      then show ?thesis using typing_unf0[OF ei wi pokD(1)[OF p]] \<open>Ua = U1\<close> by blast
    qed
    have tyu1: "e1 \<turnstile> inst ?\<rho> (unf env u1) : U1" by (rule typing_unf0[OF ei wi pokD(1)[OF pu1] ty1])
    have rsz2: "rsz env u2 = rsz env a"
    proof -
      have "rsz env u2 = rsz env u1"
        using rsz_eta_norm[OF e(2) refl e(3) e(4) eto ty1 bs1 pokD(7)[OF pu1] tv1 tyu1] by blast
      also have "\<dots> = rsz env a" by (rule rsz_head_norm[OF h1o e(3,4) termip_typed_unf[OF tyua]])
      finally show ?thesis .
    qed
    have tyconv: "e \<turnstile> inst \<rho> u2 : U"
      if \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb" and tya: "e \<turnstile> inst \<rho> a : U" for \<rho> e U
    proof -
      have "e \<turnstile> inst \<rho> u1 : U"
        using head_norm_sound[OF h1[unfolded return_def] refl \<rho>(1) _ tya] winvD[OF wi \<rho>] by blast
      then show ?thesis using E \<rho>(1) bs pokD(7)[OF pu1] by blast
    qed
    \<comment> \<open>The results for the normalized argument\<close>
    have conv: "?R (El_D (c' # us) env' dps')"
      if "PEC Fd Ft A X env (vns u2 \<union> vnsl targs \<union> vdps dps) rb u2 Tts (El_C c' env' dps')" for c' env' dps'
    proof -
      from that obtain A' K' X' NV where cr: "cres Fd Ft A X env (vns u2 \<union> vnsl targs \<union> vdps dps) A' K' X' env' dps' NV"
        and cc: "cpy A' X' env' NV rb u2 Tts c'" unfolding PEC_def by blast
      have cr': "cres Fd Ft A X env ?Da A' K' X' env' dps' NV" by (rule cres_mono[OF cr D2])
      have "cpy A' X' env' NV rb a Tts c'"
      proof (rule cpy_conv[OF cc])
        fix \<rho> e U assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb" and tya: "e \<turnstile> inst \<rho> a : U"
        show "e \<turnstile> inst \<rho> u2 : U" by (rule tyconv[OF extends_tsol[OF \<rho>(1) cresD(7)[OF cr']] \<rho>(2) bs tya])
      qed
      with cr' show ?thesis by blast
    qed
    \<comment> \<open>Deferring the argument\<close>
    from env_fastype_term[OF e(2) refl ty2 bs1 pokD(7)[OF pu2]] tv2 pokD(5)[OF pu2] obtain A2 where
      fA: "env_fastype env (map snd rb) u2 = return A2" "tvars A2 \<subseteq> tvars_env ?\<theta> \<union> A" by blast
    have fA': "fastype env rb u2 = return A2" using fA(1) by (simp add: fastype_def)
    from body_type_term[OF e(2) refl fA(2)] obtain B2 where bB2: "body_type env A2 = return B2" by blast
    have da: "defer_arg env rb u2 = return (is_TVar B2)" by (simp add: defer_arg_def fA' bB2)
    let ?d = "0 < cfg_arity_bound cfg \<and> is_TVar B2"
    have dW: "okW (if 0 < cfg_arity_bound cfg then liftM (defer_arg env rb u2) else returnW False) ?d"
      using da by (auto simp: return_def)
    obtain s where sok: "okW (if ?d then do {
          A \<leftarrow> liftM (fastype env rb u2);
          Ts \<leftarrow> liftM (mapM (fastype env rb) targs);
          (let (env', newhd) = genvar vname env (foldr fun_type Ts A) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u2) # dps))))}
         else mc cfg vname rb targs u2 env dps) s"
      and fs: "fin cfg s (PEC Fd Ft A X env (vns u2 \<union> vnsl targs \<union> vdps dps) rb u2 Tts)"
    proof (cases ?d)
      case True
      from mc_types[OF cp up2] obtain T0 base Ts' where
        mt: "mapM (fastype env rb) targs = return Ts'" "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env ?\<theta> \<union> A"
          "\<forall>\<rho>. tsol ?\<theta> \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Tts"
        by blast
      obtain env' newhd where g: "genvar vname env (foldr fun_type Ts' A2) = (env', newhd)"
        by (cases "genvar vname env (foldr fun_type Ts' A2)")
      have tyA: "U = tsubst \<rho> A2"
        if "tsol ?\<theta> \<rho>" "cert_inst \<rho>" "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> u2 : U" for \<rho> e U
        using fastype_sound[of env rb u2 A2 \<rho> e U] fA' that by (simp add: return_def)
      have pe: "PEC Fd Ft A X env (vns u2 \<union> vnsl targs \<union> vdps dps) rb u2 Tts
          (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u2) # dps))"
        by (rule flex_copy[OF cp up2 mt(1,2) _ fA(2) tyA g]) (use mt(3) in blast)
      show ?thesis
        by (rule that[of "S_Single (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u2) # dps))"])
          (use True fA' mt(1) g pe in \<open>simp_all add: return_def fin_Single\<close>)
    next
      case False
      have "\<exists>sq. okW (mc cfg vname rb targs u2 env dps) sq \<and>
          fin cfg sq (PEC Fd Ft A X env (vns u2 \<union> vnsl targs \<union> vdps dps) rb u2 Tts)"
      proof (rule mc_fin_aux[where c = "pmu S0 env" and N = "rsz env a"])
        fix A' K' X' env' dps' rb' targs' Tts' a' us'
        assume "((pmu S0 env', rsz env' a'), (pmu S0 env, rsz env a)) \<in> less_than <*lex*> less_than"
          "cpre Fd Ft m0 A' K' X' env' dps' rb' targs' Tts'" "upre Fd Ft A' X' env' rb' a'"
          "poldin m0 S0 env' (vns a' \<union> vnsl targs' \<union> vdps dps')"
        then show "\<exists>cs. okW (copycons cfg vname rb' targs' a' us' env' dps') cs \<and>
          fin cfg cs (\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV. x = El_D (c' # us') env'' dps'' \<and>
            cres Fd Ft A' X' env' (vns a' \<union> vnsl targs' \<union> vdps dps') A'' K'' X'' env'' dps'' NV \<and>
            cpy A'' X'' env'' NV rb' a' Tts' c')"
          by (rule CC)
      qed (use cp up2 hf2 sat2 o2 rsz2 in auto)
      then obtain sq where "okW (mc cfg vname rb targs u2 env dps) sq"
        "fin cfg sq (PEC Fd Ft A X env (vns u2 \<union> vnsl targs \<union> vdps dps) rb u2 Tts)" by blast
      then show ?thesis using that False by simp
    qed
    have ok: "okW (copycons cfg vname rb targs a us env dps) (S_MapCons us s)"
      unfolding copycons_def okW_bindW okW_liftM
      by (rule exI[of _ u1], rule conjI[OF h1o], rule exI[of _ u2], rule conjI[OF eto],
          rule exI[of _ ?d], rule conjI[OF dW], rule exI[of _ s], rule conjI[OF sok], simp)
    have fM: "fin cfg (S_MapCons us s) ?R"
    proof (rule fin_MapCons, rule fin_mono[OF fs])
      fix x assume x: "PEC Fd Ft A X env (vns u2 \<union> vnsl targs \<union> vdps dps) rb u2 Tts x"
      then obtain c' env' dps' where xe: "x = El_C c' env' dps'" unfolding PEC_def by blast
      from conv[OF x[unfolded xe]] xe show "\<exists>u env dps. x = El_C u env dps \<and> ?R (El_D (u # us) env dps)" by blast
    qed
    show "\<exists>cs. okW (copycons cfg vname rb targs a us env dps) cs \<and> fin cfg cs ?R"
      by (intro exI[of _ "S_MapCons us s"] conjI ok fM)
  qed
qed

theorem mc_fin_ctx:
  assumes cp: "cpre Fd Ft m0 A K X env dps rb targs Tts" and up: "upre Fd Ft A X env rb u"
    and hu: "hnf env u" and st: "sat env rb u" and o: "poldin m0 S0 env (vns u \<union> vnsl targs \<union> vdps dps)"
  shows "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
    fin cfg sq (PEC Fd Ft A X env (vns u \<union> vnsl targs \<union> vdps dps) rb u Tts)"
proof (rule mc_fin_aux[where c = "pmu S0 env" and N = "rsz env u"])
  fix A' K' X' env' dps' rb' targs' Tts' a' us'
  assume a: "((pmu S0 env', rsz env' a'), (pmu S0 env, rsz env u)) \<in> less_than <*lex*> less_than"
    "cpre Fd Ft m0 A' K' X' env' dps' rb' targs' Tts'" "upre Fd Ft A' X' env' rb' a'"
    "poldin m0 S0 env' (vns a' \<union> vnsl targs' \<union> vdps dps')"
  from copycons_fin_aux[of "(pmu S0 env', rsz env' a')"] a(2-4)
  show "\<exists>cs. okW (copycons cfg vname rb' targs' a' us' env' dps') cs \<and>
    fin cfg cs (\<lambda>x. \<exists>c' env'' dps'' A'' K'' X'' NV. x = El_D (c' # us') env'' dps'' \<and>
      cres Fd Ft A' X' env' (vns a' \<union> vnsl targs' \<union> vdps dps') A'' K'' X'' env'' dps'' NV \<and>
      cpy A'' X'' env'' NV rb' a' Tts' c')"
    by blast
qed (use cp up hu st o in auto)

end



subsection \<open>The occurs check, as reachability\<close>

lemma occurs_list_good:
  assumes ac: "acyc env" and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
  shows "\<forall>t\<in>set ts. vok env (vars t \<union> evars env) \<Longrightarrow> occurs_list env v seen ts = return (False, s) \<Longrightarrow>
    \<forall>t\<in>set ts. \<forall>y\<in>vns t. good env v seen y"
proof (induction ts arbitrary: seen)
  case (Cons t ts)
  from occur_term[OF ac tac tc order_refl, of t v seen] Cons.prems(1) obtain b s1 where
    o: "occur t env v seen = return (b, s1)" "set seen \<subseteq> set s1" "\<not> b \<longrightarrow> osafe env v seen t s1" by auto
  from Cons.prems(2) o(1) have nb: "\<not> b" and r: "occurs_list env v s1 ts = return (False, s)"
    by (auto simp: return_def split: if_splits)
  from o(3) nb have os: "\<forall>y\<in>vns t. good env v seen y" "\<forall>w\<in>set s1. good env v seen w"
    by (simp_all add: osafe_def)
  from Cons.IH[OF _ r] Cons.prems(1) have "\<forall>t\<in>set ts. \<forall>y\<in>vns t. good env v s1 y" by simp
  then have "\<forall>t\<in>set ts. \<forall>y\<in>vns t. good env v seen y" using good_trans[OF os(2)] by blast
  with os(1) show ?case by simp
qed simp

lemma occurs_terms_vreach:
  assumes ei: "einv A K env" and wi: "winv env X" and vX: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and vt: "\<forall>t\<in>set ts. vars t \<subseteq> X \<union> evars env" and oc: "occurs_terms env v ts = return False"
  shows "v \<notin> vreach env (vnsl ts)"
proof
  assume v: "v \<in> vreach env (vnsl ts)"
  note e = einvD[OF ei]
  have vk: "vok env (X \<union> evars env)" by (rule vok_winv[OF ei wi vX])
  have vks: "\<forall>t\<in>set ts. vok env (vars t \<union> evars env)" using vt by (auto intro: vok_mono[OF vk])
  from occurs_list_term[OF e(3,6,7) vks, of v "[]"] obtain r where r: "occurs_list env v [] ts = return r" by blast
  with oc have "fst r = False" by (simp add: occurs_terms_def return_def)
  with r have r': "occurs_list env v [] ts = return (False, snd r)" by (cases r) simp
  from occurs_list_good[OF e(3,6,7) vks r'] have g: "\<forall>t\<in>set ts. \<forall>y\<in>vns t. good env v [] y" .
  from v obtain x where x: "x \<in> vnsl ts" "(v, x) \<in> (dep env)\<^sup>*" unfolding vreach_def by blast
  from x(1) obtain t where t: "t \<in> set ts" "x \<in> vns t" by (rule UN_E)
  from bspec[OF bspec[OF g t(1)] t(2)] x(2) show False by (simp add: good_def)
qed

lemma finite_vreach: "finite D \<Longrightarrow> finite (vreach env D)"
proof -
  assume fD: "finite D"
  have "vreach env D \<subseteq> D \<union> Domain (dep env)"
  proof
    fix y assume "y \<in> vreach env D"
    then obtain x where x: "x \<in> D" "(y, x) \<in> (dep env)\<^sup>*" unfolding vreach_def by blast
    show "y \<in> D \<union> Domain (dep env)"
    proof (cases "y = x")
      case True
      with x(1) show ?thesis by simp
    next
      case False
      with x(2) obtain z where "(y, z) \<in> dep env" by (meson converse_rtranclE)
      then show ?thesis by blast
    qed
  qed
  moreover have "finite (Domain (dep env))" using finite_dep[of env] by (rule finite_Domain)
  ultimately show ?thesis using fD by (meson finite_UnI finite_subset)
qed

lemma dd_free: "vns t \<inter> F = {} \<Longrightarrow> dd F b t"
  by (induction F b t rule: dd.induct) auto

lemma below_vars:
  assumes "einv A K env" "winv env X" "vars s \<subseteq> X \<union> evars env" "y \<in> vns s"
  shows "snd y \<le> maxidx env"
proof -
  from winvD[OF assms(2) einv_rho0[OF assms(1)]] have "below (maxidx env) (X \<union> evars env)"
    by (simp add: vinv_def)
  with assms(3,4) show ?thesis by (auto simp: below_def)
qed

lemma arity_nonfun: "(\<forall>A B. U \<noteq> A \<rightarrow>\<^sub>T B) \<Longrightarrow> arity U = 0"
  by (cases U rule: arity.cases) auto


subsection \<open>The copies of \<^const>\<open>mc\<close>\<close>

theorem mc_fin:
  assumes cfg: "cfg_alg cfg = alg" and finX: "finite X" and finK: "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
    and oc: "occurs_terms env v (u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)) = return False"
  shows "cuok (mc cfg (fst v) rb targs u env dps) (\<lambda>s. fin cfg s (copy_ok (v, T) Ts))"
proof -
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env" and ?m0 = "maxidx env"
  let ?D = "vns u \<union> vnsl targs \<union> vdps dps"
  let ?N = "{x :: indexname. ?m0 < snd x}"
  define Fd where "Fd = (if \<exists>s\<in>set targs. \<not> is_Bound s then ?N else {})"
  define Ft where "Ft = (if \<exists>s\<in>set targs. \<not> is_Bound s then {} else ?N)"
  define S0 where "S0 = vreach env ?D"
  have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and ps: "\<forall>(rb', t', u')\<in>set dps. pok A env rb' X t' u'" using si by (auto simp: sinv_def)
  note pd = pokD[OF p] and hv = head_var_props[OF p st fr] and r0 = einv_rho0[OF ei]
  have regime: "Fd = ?N \<and> Ft = {} \<or> Fd = {} \<and> Ft = ?N" by (simp add: Fd_def Ft_def)
  have finD: "finite ?D" by auto
  have finS0: "finite S0" unfolding S0_def by (rule finite_vreach[OF finD])
  have old: "snd y \<le> ?m0" if "vars s \<subseteq> X \<union> evars env" "y \<in> vns s" for s y
    by (rule below_vars[OF ei wi that])
  have oldF: "vns s \<inter> Fd = {} \<and> vns s \<inter> Ft = {}" if vs: "vars s \<subseteq> X \<union> evars env" for s
  proof -
    have "vns s \<inter> ?N = {}"
    proof (rule equals0I)
      fix y assume "y \<in> vns s \<inter> ?N"
      then have y: "y \<in> vns s" "?m0 < snd y" by simp_all
      from old[OF vs y(1)] y(2) show False by simp
    qed
    then show ?thesis by (cases "\<exists>s\<in>set targs. \<not> is_Bound s") (simp_all add: Fd_def Ft_def)
  qed
  have pshF: "psh Fd Ft s" if "vars s \<subseteq> X \<union> evars env" for s
    using oldF[OF that] dd_free by (simp add: psh_def)
  \<comment> \<open>The types of the pair\<close>
  from match1_types[OF si fr st bt len] obtain T0 base Ts' where
    ty: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "tvars base \<subseteq> tvars_env ?\<theta> \<union> A"
    by blast
  have T0: "ok (fastype env rb (fst (strip_comb u))) T0" and base: "ok (body_type env T0) base"
    using ty by (simp_all add: return_def)
  note pb = pair_base[OF ei p st bt len T0 base ty(3)]
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  \<comment> \<open>The context of the copy\<close>
  have targsok: "pok A env rb X s s \<and> psh Fd Ft s" if s: "s \<in> set targs" for s
  proof
    have vs: "vars s \<subseteq> X \<union> evars env" using hv(4) s by blast
    show "psh Fd Ft s" by (rule pshF[OF vs])
    show "pok A env rb X s s"
      unfolding pok_def
    proof (intro conjI allI impI)
      show "vars s \<union> vars s \<subseteq> X \<union> evars env" using vs by simp
      show "ttvars s \<union> ttvars s \<union> btvars rb \<union> vtvars X \<subseteq> tvars_env ?\<theta> \<union> A" using hv(4) s pd(5,6) by blast
      show "\<not> loose_bvar s (ilength rb)" "\<not> loose_bvar s (ilength rb)" using hv(4) s by blast+
      fix \<rho> assume \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>"
      from pd(9)[OF \<rho>] obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : U" by blast
      from tyt[unfolded t inst_apps] obtain Us where "e \<tturnstile> map (inst \<rho>) targs : Us" by (rule list_app_typeE)
      with s obtain V where "e \<turnstile> inst \<rho> s : V" by (auto simp: in_set_conv_nth dest!: typings_nth)
      with bs show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> s : T" by blast
    qed
  qed
  have tyT: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    if \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" and bs: "bs_env \<rho> e rb" for \<rho> e
  proof -
    from pd(9)[OF \<rho>] obtain e0 U where bs0: "bs_env \<rho> e0 rb" and tyt: "e0 \<turnstile> inst \<rho> t : U" by blast
    have "e0 \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" by (rule pb(3)[OF \<rho>(1) tyt])
    then show ?thesis by (rule typings_bs[OF bs0 bs]) (use hv(4) in simp)
  qed
  have vgF: "vgood Fd Ft env"
    unfolding vgood_def
  proof (intro allI impI)
    fix x U w assume b: "vt_lookup (tenv env) x = Some (U, w)"
    have "snd x \<le> ?m0" by (rule bbelowD[OF einvD(5)[OF ei] b])
    then have "x \<notin> Fd" by (simp add: Fd_def)
    moreover have "vars w \<subseteq> X \<union> evars env" using b by (auto simp: evars_def bnds_def)
    ultimately show "x \<notin> Fd \<and> dead Fd w \<and> vns w \<inter> Ft = {}" using pshF by (simp add: psh_def)
  qed
  have pgF: "pgood Fd Ft dp" if dpin: "dp \<in> set dps" for dp
  proof -
    obtain rb' t' u' where dp: "dp = (rb', t', u')" by (cases dp)
    with ps dpin have p': "pok A env rb' X t' u'" by auto
    from pshF[OF pokD(1)[OF p']] pshF[OF pokD(2)[OF p']] oldF[OF pokD(1)[OF p']] oldF[OF pokD(2)[OF p']]
    show ?thesis by (auto simp: pgood_def dp psh_def intro: gs_free)
  qed
  have ptF: "ptok Fd Ft targs" by (auto simp: ptok_def Fd_def Ft_def)
  have siD: "sinv A K X env dps" by (rule sinv_mono[OF si]) auto
  have cp: "cpre Fd Ft ?m0 A K X env dps rb targs Ts"
    unfolding cpre_def using finX finK siD pd(5,6) len targsok tyT vgF pgF ptF by blast
  have up: "upre Fd Ft A X env rb u"
    unfolding upre_def
  proof
    show "psh Fd Ft u" by (rule pshF[OF pd(2)])
    show "pok A env rb X u u"
      unfolding pok_def
    proof (intro conjI allI impI)
      show "vars u \<union> vars u \<subseteq> X \<union> evars env" using pd(2) by simp
      show "ttvars u \<union> ttvars u \<union> btvars rb \<union> vtvars X \<subseteq> tvars_env ?\<theta> \<union> A" using pd(4-6) by blast
      show "\<not> loose_bvar u (ilength rb)" "\<not> loose_bvar u (ilength rb)" by (fact pd(8))+
      fix \<rho> assume \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>"
      from pd(9)[OF \<rho>] show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> u : T \<and> e \<turnstile> inst \<rho> u : T" by blast
    qed
  qed
  have frs: "frs0 (rb, t, u)" using fr by (simp add: fr_shape_def)
  have nAu: "\<not> is_Abs u" and hr: "rigid (head_of u)" using frs by (simp_all add: frs0_def)
  have hu: "hnf env u" using nAu hr by (simp add: hnf_nonAbs ahd_def)
  have sat: "sat env rb u"
  proof -
    from pd(9)[OF r0] obtain e U where bs: "bs_env ?\<rho> e rb" and tyt: "e \<turnstile> inst ?\<rho> t : U"
      and tyu: "e \<turnstile> inst ?\<rho> u : U" by blast
    have "U = tnorm ?\<theta> base" using pb(1)[OF r0(1) tyt] by simp
    moreover from mf_body_type_sound[of env T0 "Ok base" base] base einvD(6)[OF ei]
    have "\<forall>A B. tnorm ?\<theta> base \<noteq> A \<rightarrow>\<^sub>T B" by auto
    ultimately have "arity U = 0" by (simp add: arity_nonfun)
    with bs tyu nAu show ?thesis unfolding sat_def by auto
  qed
  have o: "poldin ?m0 S0 env ?D" by (simp add: poldin_def S0_def)
  from mc_fin_ctx[OF cfg finS0 regime cp up hu sat o]
  obtain sq where ok: "okW (mc cfg (fst v) rb targs u env dps) sq" and fs: "fin cfg sq (PEC Fd Ft A X env ?D rb u Ts)"
    by blast
  \<comment> \<open>The occurs check\<close>
  have vD: "v \<notin> vreach env ?D"
  proof -
    let ?ts = "u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)"
    have vts: "\<forall>s\<in>set ?ts. vars s \<subseteq> X \<union> evars env"
    proof
      fix s assume "s \<in> set ?ts"
      then consider "s = u" | "s \<in> set targs" | rb' t' u' where "(rb', t', u') \<in> set dps" "s = t' \<or> s = u'"
        by auto
      then show "vars s \<subseteq> X \<union> evars env"
      proof cases
        case 3
        with ps have "pok A env rb' X t' u'" by auto
        with 3(2) show ?thesis using pokD(1,2) by blast
      qed (use pd(2) hv(4) in auto)
    qed
    have "vdps dps \<subseteq> vnsl (concat (map (\<lambda>(_, t, u). [t, u]) dps))"
    proof
      fix y assume "y \<in> vdps dps"
      then obtain dp where dp: "dp \<in> set dps" "y \<in> vdp dp" by blast
      obtain rb' t' u' where dpe: "dp = (rb', t', u')" by (cases dp)
      with dp have m: "(rb', t', u') \<in> set dps" and y: "y \<in> vns t' \<union> vns u'" by simp_all
      have "t' \<in> set (concat (map (\<lambda>(_, t, u). [t, u]) dps))" "u' \<in> set (concat (map (\<lambda>(_, t, u). [t, u]) dps))"
        using m by force+
      with y show "y \<in> vnsl (concat (map (\<lambda>(_, t, u). [t, u]) dps))" by blast
    qed
    then have "?D \<subseteq> vnsl ?ts" by auto
    then have "vreach env ?D \<subseteq> vreach env (vnsl ?ts)" by (rule vreach_subset)
    with occurs_terms_vreach[OF ei wi pd(6) vts oc] show ?thesis by blast
  qed
  have vm: "snd v \<le> ?m0" by (rule below_head[OF si hv(1)])
  have "fin cfg sq (copy_ok (v, T) Ts)"
  proof (rule fin_mono[OF fs])
    fix x assume "PEC Fd Ft A X env ?D rb u Ts x"
    then obtain c env' dps' A' K' X' NV where x: "x = El_C c env' dps'"
      and cr: "cres Fd Ft A X env ?D A' K' X' env' dps' NV" and cc: "cpy A' X' env' NV rb u Ts c"
      unfolding PEC_def by blast
    note r = cresD[OF cr] and d = cpyD[OF cc]
    have vNV: "v \<notin> NV" using r(9)[of v] vm by auto
    show "copy_ok (v, T) Ts x"
      unfolding x
    proof (rule copy_okI[OF r(1,2,5)])
      show "vt_lookup (tenv env') v = None"
      proof (rule ccontr)
        assume "vt_lookup (tenv env') v \<noteq> None"
        from r(12)[OF this hv(2)] vD vNV show False by blast
      qed
      show "(v, T) \<in> X' \<union> evars env'" using hv(1) r(4) evars_extends[OF r(7)] by blast
      show "(v, y) \<notin> (dep env')\<^sup>*" if "(y, U) \<in> vars c" for y U
      proof
        assume "(v, y) \<in> (dep env')\<^sup>*"
        then have "v \<in> vreach env' {y}" by (auto simp: vreach_def)
        with r(10)[of "{y}"] have "v \<in> vreach env ({y} \<union> ?D) \<union> NV" by blast
        moreover have "y \<in> NV" using d(1) that by force
        then have "vreach env {y} \<subseteq> NV"
        proof -
          have "\<forall>y\<in>NV. maxidx env < snd y" using r(9) by blast
          from vreach_fresh[OF einvD(5)[OF ei] this] vreach_subset[of "{y}" NV env] \<open>y \<in> NV\<close>
          show ?thesis by blast
        qed
        ultimately show False using vD vNV vreach_Un[of env "{y}" ?D] by blast
      qed
      show "\<not> loose_bvar c (ilength Ts)" by (rule d(4))
      show "vars c \<subseteq> X' \<union> evars env'" by (rule d(2))
      have tvTs: "(\<Union>T\<in>set Ts. tvars T) \<subseteq> tvars_env ?\<theta> \<union> A"
        using mf_binder_types_sound[OF bt[unfolded return_def] refl einvD(6)[OF ei]] hv(3) by blast
      show "tvars T \<union> ttvars (types_abs Ts c) \<subseteq> tvars_env (tyenv env') \<union> A'"
        using hv(3) tvTs d(3) r(3,8) by (auto simp: mf_ttvars_types_abs)
      fix \<rho> e assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
      have \<rho>0: "tsol ?\<theta> \<rho>" by (rule extends_tsol[OF \<rho>(1) r(7)])
      from pd(9)[OF \<rho>0 \<rho>(2)] obtain e0 U where bs: "bs_env \<rho> e0 rb" and tyt: "e0 \<turnstile> inst \<rho> t : U"
        and tyu: "e0 \<turnstile> inst \<rho> u : U" by blast
      note pb' = pb[OF \<rho>0 tyt]
      have cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
        by (rule mf_cert_targs[OF bs pb'(3)]) (use hv(4) in blast)
      have "pushes e (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> c : U" by (rule d(5)[OF \<rho> bs tyu])
      from mf_typing_types_abs[OF this] cTs
      show "e \<turnstile> inst \<rho> (types_abs Ts c) : tsubst \<rho> T"
        using pb'(1,2) by (simp add: mf_inst_types_abs)
    qed
  qed
  with ok show ?thesis by (auto simp: cuok_def)
qed



subsection \<open>The step of matching\<close>

text \<open>
  The assignments of \<^const>\<open>match_pair\<close> to the variable of a saturated flex-rigid pair are copies
  of the rigid side if the variable does not occur (\<^const>\<open>mc\<close>, theorem @{thm [source] mc_fin}),
  and single steps (\<^const>\<open>match1\<close>, theorem @{thm [source] match1_fin}) otherwise. Hence
  \<^const>\<open>MATCH\<close> on a flex-rigid pair of \<^const>\<open>SIMPL\<close> raises at most \<open>CANTUNIFY\<close> and
  otherwise yields a finite enumeration of new problems in the invariant.
\<close>

theorem match_pair_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts"
    and len: "length Ts = length targs"
  shows "cuok (match_pair cfg env (rb, t, u) dps) (\<lambda>s. fin cfg s mres)"
proof -
  let ?L = "u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)"
  have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and ps: "\<forall>(rb', t', u')\<in>set dps. pok A env rb' X t' u'"
    using si by (auto simp: sinv_def)
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have "\<forall>s\<in>set ?L. vars s \<subseteq> X \<union> evars env"
  proof
    fix s assume "s \<in> set ?L"
    then consider "s = u" | "s \<in> set targs" | rb' t' u' where "(rb', t', u') \<in> set dps" "s = t' \<or> s = u'"
      by auto
    then show "vars s \<subseteq> X \<union> evars env"
    proof cases
      case 2
      then show ?thesis using pokD(1)[OF p] t by (auto simp: vars_apps)
    next
      case (3 rb' t' u')
      with ps have "pok A env rb' X t' u'" by auto
      with 3(2) show ?thesis using pokD(1,2) by blast
    qed (use pokD(2)[OF p] in simp)
  qed
  from occurs_terms_term[OF ei wi pokD(6)[OF p] this, of v] obtain b where oc: "occurs_terms env v ?L = return b"
    by blast
  have "cuok (if b then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps) else mc cfg (fst v) rb targs u env dps)
      (\<lambda>s. fin cfg s (copy_ok (v, T) Ts))"
    using match1_fin[OF cfg fin si fr st bt len] mc_fin[OF cfg fin si fr st bt len] oc by (cases b) simp_all
  then have "cuok (bindW (if b then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps) else mc cfg (fst v) rb targs u env dps)
      (\<lambda>s. returnW (S_MapNewDset (v, T) Ts s))) (\<lambda>s. fin cfg s mres)"
    by (rule cuok_bindW) (simp add: fin_MapNewDset_copy)
  then show ?thesis unfolding match_pair_def prod.case st
    by (simp only: pterm.case) (intro cuok_liftM_return[OF bt] cuok_liftM_return[OF oc])
qed

lemma match_sat_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp"
  shows "cuok (match_sat cfg env dp dps) (\<lambda>s. fin cfg s mres)"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain v T targs where st: "strip_comb t = (Var v T, targs)" by (auto elim: fr_shape_strip_comb)
  have ei: "einv A K env" and p: "pok A env rb X t u" using si dp by (auto simp: sinv_def)
  have tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    using head_tvars_strip_comb[OF st] pokD(3)[OF p] by blast
  from binder_types_term[OF einvD(2)[OF ei] refl tv] obtain Ts where bt: "binder_types env T = return Ts" by blast
  note ex = sinv_eta_expand[OF si[unfolded dp] st bt]
  define Es where "Es = drop (length targs) Ts"
  have st': "strip_comb (incr_bv (ilength Es) 0 t \<degree>\<degree> mbvs (length Es)) =
      (Var v T, map (incr_bv (ilength Es) 0) targs @ mbvs (length Es))"
    by (rule mf_strip_comb_expand[OF st])
  have len: "length Ts = length (map (incr_bv (ilength Es) 0) targs @ mbvs (length Es))"
    using ex(1) by (simp add: Es_def)
  have "cuok (match_pair cfg env (eta_expand_dpair Es (rb, t, u)) dps) (\<lambda>s. fin cfg s mres)"
    unfolding eta_expand_dpair_eq
    by (rule match_pair_fin[OF cfg fin _ _ st' bt len])
      (use ex(2) fr_shape_eta_expand[OF fr[unfolded dp], of Es] in \<open>simp_all add: Es_def eta_expand_dpair_eq\<close>)
  then show ?thesis unfolding match_sat_def dp prod.case st Es_def
    by (simp only: pterm.case) (intro cuok_liftM_return[OF bt])
qed

lemma match_eta_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp"
    and B: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" "is_TVar B" and tl: "fin cfg tail mres"
  shows "cuok (match_eta cfg env dp dps B j tail) (\<lambda>s. fin cfg s mres)"
proof (cases "j = 0")
  case True
  show ?thesis unfolding match_eta_def if_P[OF True]
    by (rule cuok_bindW[OF match_sat_fin[OF cfg fin si fr]]) (simp add: fin_Append tl)
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by (cases "gentvars (Suc j) env")
  note gs = gentvars_simps[OF g]
  let ?A = "A \<union> ntv Rs" and ?K = "K \<union> ntv Rs"
  have si1: "sinv ?A ?K X env1 (dp # dps)" by (rule sinv_gentvars[OF si g])
  have finK: "finite ?K" using fin(2) by simp
  have th: "tyenv env1 = tyenv env" by (rule gs(2))
  have ei1: "einv ?A ?K env1" using si1 by (simp add: sinv_def)
  have Rs: "Rs \<noteq> []" using gs(4) by auto
  have tvR: "tvars (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) \<subseteq> ntv Rs"
    using Rs hd_in_set[OF Rs] list.set_sel(2)[OF Rs] by (fastforce simp: tvars_funs ntv_def)
  have cB: "cert_typ alg ar (tnorm (tyenv env1) B)"
  proof -
    obtain v S where Bv: "B = TVar v S" using B(2) by (cases B) auto
    then have "(v, S) \<in> tvars_env (tyenv env1) \<union> ?A" using B(1) th by auto
    then have "sort_ok alg S" using einvD(10)[OF ei1] tcertD by blast
    then have "cert_typ alg ar B" by (simp add: Bv cert_typ_def)
    then show ?thesis by (rule cert_tnorm[OF ei1])
  qed
  have cR: "cert_typ alg ar (tnorm (tyenv env1) (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)))"
  proof (rule cert_tnorm[OF ei1])
    have "cert_typ alg ar C" if "C \<in> set Rs" for C
      using gs(6)[OF that] by (auto simp: cert_typ_def sort_ok_def)
    then show "cert_typ alg ar (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs))"
      using Rs by (simp add: cert_typ_funs) (meson list.set_sel(1,2))
  qed
  have inner: "cuok (do {
      env2 \<leftarrow> cunify_types (cfg_alg cfg) B (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) env1;
      s \<leftarrow> match_sat cfg env2 dp dps;
      returnW (S_Append s tail)}) (\<lambda>s. fin cfg s mres)"
    unfolding cfg
  proof (rule cuok_bindW[OF cunify_types_sinv[OF finK si1 _ cB _ cR]])
    show "tvars B \<subseteq> tvars_env (tyenv env1) \<union> ?A" using B(1) th by auto
    show "tvars (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) \<subseteq> tvars_env (tyenv env1) \<union> ?A" using tvR by auto
    fix env2 assume "sinv ?A ?K X env2 (dp # dps) \<and> tenv env2 = tenv env1 \<and> extends env1 env2 \<and>
      tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env2) \<and>
      (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> B = tsubst \<rho> (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)))"
    then have si2: "sinv ?A ?K X env2 (dp # dps)" and te: "tenv env2 = tenv env" using gs(1) by auto
    have fr2: "fr_shape env2 dp" using fr fr_shape_tenv[OF te] by simp
    show "cuok (match_sat cfg env2 dp dps \<bind> (\<lambda>s. returnW (S_Append s tail))) (\<lambda>s. fin cfg s mres)"
      by (rule cuok_bindW[OF match_sat_fin[OF cfg fin(1) finK si2 fr2]]) (simp add: fin_Append tl)
  qed
  show ?thesis unfolding match_eta_def if_not_P[OF False] g prod.case
    by (rule cuok_handle_CANTUNIFY_ret[OF inner]) (simp_all add: tl)
qed

lemma foldrW_match_eta_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp"
    and B: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" "is_TVar B"
  shows "cuok (foldrW (match_eta cfg env dp dps B) js S_Empty) (\<lambda>s. fin cfg s mres)"
proof (induction js)
  case (Cons j js)
  show ?case by (simp, rule cuok_bindW[OF Cons.IH match_eta_fin[OF cfg fin si fr B]])
qed simp

theorem MATCH_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp"
  shows "cuok (MATCH cfg env dp dps) (\<lambda>ms. fin cfg ms mres)"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain v T targs where st: "strip_comb t = (Var v T, targs)" by (auto elim: fr_shape_strip_comb)
  have ei: "einv A K env" and p: "pok A env rb X t u" using si dp by (auto simp: sinv_def)
  from fastype_pair_term[OF ei p] obtain T1 U1 where
    ty: "fastype env rb t = return T1" "fastype env rb u = return U1"
      "tvars T1 \<subseteq> tvars_env (tyenv env) \<union> A" "tvars U1 \<subseteq> tvars_env (tyenv env) \<union> A"
      "tnorm (tyenv env) T1 = tnorm (tyenv env) U1" "cert_typ alg ar (tnorm (tyenv env) T1)"
    by blast
  have "cuok (do {
      env' \<leftarrow> cunify_types (cfg_alg cfg) T1 U1 env;
      B \<leftarrow> liftM (body_type env' T);
      if is_TVar B then foldrW (match_eta cfg env' dp dps B) (arity_guesses cfg B) S_Empty
      else match_sat cfg env' dp dps}) (\<lambda>ms. fin cfg ms mres)"
    unfolding cfg
  proof (rule cuok_bindW[OF cunify_types_sinv[OF fin(2) si ty(3,6,4)]])
    show "cert_typ alg ar (tnorm (tyenv env) U1)" using ty(5,6) by simp
    fix env' assume "sinv A K X env' (dp # dps) \<and> tenv env' = tenv env \<and> extends env env' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T1 = tsubst \<rho> U1)"
    then have si': "sinv A K X env' (dp # dps)" and te: "tenv env' = tenv env" by auto
    have fr': "fr_shape env' dp" using fr fr_shape_tenv[OF te] by simp
    have ei': "einv A K env'" using si' by (simp add: sinv_def)
    have p': "pok A env' rb X t u" using si' dp by (simp add: sinv_def)
    have tv: "tvars T \<subseteq> tvars_env (tyenv env') \<union> A"
      using head_tvars_strip_comb[OF st] pokD(3)[OF p'] by blast
    from body_type_term[OF einvD(2)[OF ei'] refl tv] obtain B where
      bt: "body_type env' T = return B" "tvars B \<subseteq> tvars_env (tyenv env') \<union> A" by blast
    show "cuok (liftM (body_type env' T) \<bind> (\<lambda>B. if is_TVar B then foldrW (match_eta cfg env' dp dps B)
        (arity_guesses cfg B) S_Empty else match_sat cfg env' dp dps)) (\<lambda>ms. fin cfg ms mres)"
    proof (rule cuok_liftM_return[OF bt(1)])
      show "cuok (if is_TVar B then foldrW (match_eta cfg env' dp dps B) (arity_guesses cfg B) S_Empty
          else match_sat cfg env' dp dps) (\<lambda>ms. fin cfg ms mres)"
        using foldrW_match_eta_fin[OF cfg fin si' fr' bt(2)] match_sat_fin[OF cfg fin si' fr'] by simp
    qed
  qed
  then show ?thesis unfolding MATCH_def dp prod.case st
    by (simp only: pterm.case) (intro cuok_liftM_return[OF ty(1)] cuok_liftM_return[OF ty(2)])
qed

end

end
