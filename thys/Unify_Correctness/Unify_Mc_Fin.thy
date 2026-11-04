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

end

end
