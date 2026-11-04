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

end

end
