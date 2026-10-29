section \<open>Problems with Type Variables: Finiteness of \<open>MATCH\<close>\<close>

theory Unify_Poly_Match_Fin
  imports Unify_Poly_Fin Unify_Match_Fin
begin

hide_const (open) Unify_Flexflex_Complete.inst

text \<open>
  \<^const>\<open>MATCH\<close> on a problem with type variables yields, unless it fails, a finite enumeration of
  new problems in the invariant, for every arity bound: the analogue of
  \<^theory>\<open>Pure_Unify_Correctness.Unify_Match_Fin\<close>. Copying an argument may bind type variables,
  also to function types, which changes \<open>\<eta>\<close>-long forms; we therefore measure an argument by the
  number of rigid atoms of the \<open>\<beta>\<close>-normal form of its ground instance, which does not depend on the
  ground instance. Reachability is measured without types.
\<close>


subsection \<open>Reachability without types\<close>

definition vreach :: "env \<Rightarrow> indexname set \<Rightarrow> indexname set" where
  "vreach env X = {y. \<exists>x\<in>X. (y, x) \<in> (ndep env)\<^sup>*}"

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
  by (simp add: vreach_def ndep_def fun_eq_iff)

lemma vreach_step: "vt_lookup (tenv env) x = Some (U, w) \<Longrightarrow> x \<in> vreach env X \<Longrightarrow> vars w \<subseteq> vreach env X"
  by (auto simp: vreach_def ndep_def intro: converse_rtrancl_into_rtrancl)

lemma vreach_update:
  assumes "tenv env' = vt_update (v, (T, w)) (tenv env)"
  shows "vreach env' X \<subseteq> vreach env (X \<union> vars w)"
proof
  fix y assume "y \<in> vreach env' X"
  then obtain x where x: "x \<in> X" "(y, x) \<in> (ndep env')\<^sup>*" by (auto simp: vreach_def)
  from x(2) show "y \<in> vreach env (X \<union> vars w)"
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case using x(1) vreach_incl by blast
  next
    case (step y z)
    from step.hyps(1) obtain U u where b: "vt_lookup (tenv env') z = Some (U, u)" and yu: "y \<in> vars u"
      by (auto simp: ndep_def)
    show ?case
    proof (cases "z = v")
      case True
      with b assms have "u = w" by simp
      with yu vreach_incl show ?thesis by blast
    next
      case False
      with b assms have "vt_lookup (tenv env) z = Some (U, u)" by simp
      from vreach_step[OF this step.IH] yu show ?thesis by blast
    qed
  qed
qed

subsection \<open>Normalization\<close>

lemma head_norm_vreach_aux:
  assumes "head_norm e t = Some r"
  shows "e = env \<Longrightarrow> r = Ok t' \<Longrightarrow> vars t' \<subseteq> vreach env (vars t)"
  using assms
proof (induction e t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn e t r)
  have t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using "1.hyps" "1.prems"(2) unfolding "1.prems"(1) by simp
  have IH: "vars s' \<subseteq> vreach env (vars s)" if "hn env s = Some (Ok s')" for s s'
    using "1.IH"[OF that refl refl] .
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest show ?thesis using vreach_incl by fastforce
    next
      case (Some w)
      from ok_lookup_Some[OF lk[unfolded Some]] obtain U where b: "vt_lookup (tenv env) xi = Some (U, w)" ..
      from Some rest have "hn env w = Some (Ok t')" by simp
      from IH[OF this] have "vars t' \<subseteq> vreach env (vars w)" .
      moreover have "vars w \<subseteq> vreach env (vars t)" using vreach_step[OF b] vreach_incl Var by fastforce
      ultimately show ?thesis using vreach_mono by blast
    qed
  next
    case (Abs a T body)
    with t' obtain b' where h: "hn env body = Some (Ok b')" and e: "t' = pterm.Abs a T b'" by auto
    from IH[OF h] e Abs show ?thesis by simp
  next
    case (App f u)
    have sb: "vars (subst_bound u body) \<subseteq> vreach env (vars t)" if "vars body \<subseteq> vreach env (vars f)" for body
      using vars_subst_bound[of u body] that vreach_incl[of "vars t" env] vreach_subset[of "vars f" "vars t" env] App
      by fastforce
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have h: "hn env (subst_bound u body) = Some (Ok t')" by simp
      have "vars (subst_bound u body) \<subseteq> vreach env (vars t)" by (rule sb) (use f vreach_incl in auto)
      with IH[OF h] vreach_mono show ?thesis by blast
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      note IHf = IH[OF nf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have h: "hn env (subst_bound u body) = Some (Ok t')" by simp
        have "vars (subst_bound u body) \<subseteq> vreach env (vars t)" by (rule sb) (use IHf nfa in simp)
        with IH[OF h] vreach_mono show ?thesis by blast
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with IHf App vreach_incl[of "vars t" env] vreach_subset[of "vars f" "vars t" env] show ?thesis by auto
      qed
    qed
  qed (use t' in auto)
qed

lemma head_norm_vreach: "ok (head_norm env t) t' \<Longrightarrow> vars t' \<subseteq> vreach env (vars t)"
  using head_norm_vreach_aux[of env t _ env t'] by auto

lemma etif_vars_aux:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> vars t' = vars t"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et tye T t r)
  have body: "ok (case T of
      Type a Ts \<Rightarrow>
        (case Ts of
          [T1, U] \<Rightarrow>
            if a = STR ''fun'' then do {
              u \<leftarrow> et tye U (incr_boundvars 1 t $ Bound 0);
              return (Abs STR '''' T1 u)}
            else return t
        | _ \<Rightarrow> return t)
    | TVar v S \<Rightarrow> do {
        r \<leftarrow> type_lookup tye v S;
        case r of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t}
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by blast
    with body obtain u where u: "et tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u" by auto
    from "1.IH"[OF u refl] t' show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases T)
      case (Type a Ts)
      with False body have "t' = t" by (auto split: list.splits if_splits)
      then show ?thesis by simp
    next
      case (TVar v S)
      with body obtain r' where r': "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t) t'"
        by auto
      show ?thesis
      proof (cases r')
        case None
        with r' show ?thesis by simp
      next
        case (Some T')
        with r' have "et tye T' t = Some (Ok t')" by simp
        from "1.IH"[OF this refl] show ?thesis .
      qed
    qed (use body in auto)
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
  "vdp dp = (case dp of (rb, t, u) \<Rightarrow> vars t \<union> vars u)"

lemma vdp_simp[simp]: "vdp (rb, t, u) = vars t \<union> vars u"
  by (simp add: vdp_def)

abbreviation vdps :: "dpair list \<Rightarrow> indexname set" where
  "vdps dps \<equiv> \<Union> (vdp ` set dps)"

definition vsp :: "sstate \<Rightarrow> indexname set" where
  "vsp st = (case st of (env, ffs, frs) \<Rightarrow> vdps (ffs @ frs))"

lemma vsp_simp[simp]: "vsp (env, ffs, frs) = vdps ffs \<union> vdps frs"
  by (simp add: vsp_def)

text \<open>
  A step from \<open>st\<close> to \<open>st'\<close> on pairs with variables \<open>D\<close>: only variables reachable from \<open>D\<close>
  become reachable, and the variables of the new pairs are reachable from those of the old pairs
  and \<open>D\<close>.
\<close>

definition vsr :: "indexname set \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "vsr D st st' \<longleftrightarrow> (\<forall>X. vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D)) \<and>
    vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D)"

lemma vsr_refl: "vsr D st st"
  unfolding vsr_def using vreach_subset[of _ _ "fst st"] vreach_incl[of _ "fst st"] by blast

lemma vsr_tenv:
  "tenv e1 = tenv e \<Longrightarrow> vsr D (e1, ffs, frs) st' \<longleftrightarrow> vsr D (e, ffs, frs) st'"
  using vreach_tenv[of e1 e] by (simp add: vsr_def)

lemma vsr_trans:
  assumes "vsr D1 st st1" "vsr D2 st1 st2"
  shows "vsr (D1 \<union> D2) st st2"
  unfolding vsr_def
proof (intro conjI allI)
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
qed

lemma vsr_mono:
  assumes "vsr D st st'" "D \<subseteq> vreach (fst st) D'"
  shows "vsr D' st st'"
  unfolding vsr_def
proof (intro conjI allI)
  fix X
  show "vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D')"
    using assms(1) vreach_absorb[OF assms(2), of X] by (auto simp: vsr_def)
  show "vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D')"
    using assms(1) vreach_absorb[OF assms(2), of "vsp st"] by (auto simp: vsr_def)
qed

lemma head_norm_dpair_vreach:
  assumes "okW (head_norm_dpair alg env dp) (dp', env')"
  shows "vdp dp' \<subseteq> vreach env (vdp dp) \<and> tenv env' = tenv env"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain rb' t' u' where dp': "dp' = (rb', t', u')" by (cases dp')
  from assms obtain t1 t2 u1 u2 where h1: "ok (head_norm env t) t1" and e1: "ok (eta_norm env rb t1) t2"
    and h2: "ok (head_norm env u) u1" and e2: "ok (eta_norm env rb u1) u2"
    and nd: "okW (new_dpair alg rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def dp dp')
  note s = new_dpair_strip[OF nd]
  have "vars t' \<subseteq> vreach env (vars t)" using head_norm_vreach[OF h1] eta_norm_vars[OF e1] s by simp
  moreover have "vars u' \<subseteq> vreach env (vars u)" using head_norm_vreach[OF h2] eta_norm_vars[OF e2] s by simp
  ultimately show ?thesis
    using vreach_subset[of "vars t" "vars t \<union> vars u" env] vreach_subset[of "vars u" "vars t \<union> vars u" env] s
    by (auto simp: dp dp')
qed

lemma assignment_vreach:
  assumes "okW (assignment alg rb t u env) env'"
  shows "vreach env' X \<subseteq> vreach env (X \<union> vars u)"
proof -
  from assms obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types alg T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where cu: "okW (cunify_types alg T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have "tenv env' = vt_update (v, (T, rlist_abs rb u)) (tenv env)"
    using ok_update(2)[OF upd] cunify_types_tenv[OF cu] by simp
  from vreach_update[OF this] show ?thesis by (simp add: vars_rlist_abs)
qed

lemma simrands_vreach:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> vsr (vdp dp) st st') \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> vsr (vars t \<union> vars u) st st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  have v1: "vsr (vars f1 \<union> vars g1) st st1" by (rule "1.IH"[OF "1.prems"(1) r])
  have v2: "vsr (vars t \<union> vars u) st1 st'" using "1.prems"(1)[OF s] by simp
  from vsr_trans[OF v1 v2] show ?case by (simp add: Un_ac)
qed (auto intro: vsr_refl)

lemma SIMPL0_step_vreach:
  assumes F: "\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> vsr (vdp dp) st st'"
    and ok: "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st'"
  shows "vsr (vars t \<union> vars u) (env, ffs, frs) st'"
proof -
  let ?D = "vars t \<union> vars u"
  have keep: "vsr ?D (env, ffs, frs) (env', ffs', frs')"
    if "tenv env' = tenv env" "vsp (env', ffs', frs') \<subseteq> vsp (env, ffs, frs) \<union> ?D" for env' ffs' frs'
    unfolding vsr_def using that vreach_tenv[OF that(1)] vreach_subset[of _ _ env] vreach_incl[of _ env]
    by (simp del: vsp_simp) blast
  have asg: "vsr ?D (env, ffs, frs) (env', ffs, frs)" if "\<And>X. vreach env' X \<subseteq> vreach env (X \<union> vars s)"
    "s = t \<or> s = u" for env' s
    unfolding vsr_def
  proof (intro conjI allI)
    fix X
    show "vreach (fst (env', ffs, frs)) X \<subseteq> vreach (fst (env, ffs, frs)) (X \<union> ?D)"
      using that vreach_subset[of "X \<union> vars s" "X \<union> ?D" env] by auto
    show "vsp (env', ffs, frs) \<subseteq> vreach (fst (env, ffs, frs)) (vsp (env, ffs, frs) \<union> ?D)"
      using vreach_incl[of "vsp (env, ffs, frs) \<union> ?D" env] by auto
  qed
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok obtain T' U' env' where cu: "okW (cunify_types alg T' U' env) env'"
      and st': "st' = (env', (rb, t, u) # ffs, frs)"
      by (auto simp: SIMPL0_step_def)
    show ?thesis unfolding st' by (rule keep[OF cunify_types_tenv[OF cu]]) auto
  next
    case VR
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_step_def)
    from h consider env' where "okW (assignment alg rb t u env) env'" "st' = (env', ffs, frs)"
      | "st' = (env, ffs, (rb, t, u) # frs)"
      unfolding okW_handleW by (auto dest!: okW_ASSIGN_handler)
    then show ?thesis
    proof cases
      case 1
      show ?thesis unfolding 1(2) by (rule asg[OF assignment_vreach[OF 1(1)]]) simp
    next
      case 2
      show ?thesis unfolding 2 by (rule keep) auto
    qed
  next
    case RV
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_step_def)
    from h consider env' where "okW (assignment alg rb u t env) env'" "st' = (env', ffs, frs)"
      | "st' = (env, ffs, (rb, u, t) # frs)"
      unfolding okW_handleW by (auto dest!: okW_ASSIGN_handler)
    then show ?thesis
    proof cases
      case 1
      show ?thesis unfolding 1(2) by (rule asg[OF assignment_vreach[OF 1(1)]]) simp
    next
      case 2
      show ?thesis unfolding 2 by (rule keep) auto
    qed
  next
    case RR
    have ct: "tenv env' = tenv env" if "cunify_types alg T U env = Some (evs, UOk env')" for T U evs env'
      using that by (intro cunify_types_tenv) blast
    from ok RR obtain env1 where e1: "tenv env1 = tenv env"
      and sr: "okW (simrands F rb u t u (env1, ffs, frs)) st'"
      by (cases "head_of t"; cases "head_of u") (auto simp: SIMPL0_step_def split: if_splits dest: ct)
    from simrands_vreach[OF F sr] show ?thesis by (simp add: vsr_tenv[OF e1])
  qed
qed

theorem SIMPL0_vreach:
  assumes "SIMPL0 alg dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vsr (vdp dp0) st st'"
  using assms
proof (induction alg dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S alg dp0 st r)
  have IH: "vsr (vdp dp) st1 st2" if "okW (S alg dp st1) st2" for dp st1 st2
  proof -
    from that obtain evs where "S alg dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  have "(case st of (env, ffs, frs) \<Rightarrow> do {
      (dp, env) \<leftarrow> head_norm_dpair alg env dp0; SIMPL0_step alg (S alg) dp env ffs frs}) = Some r"
    using "1.hyps" by (simp only: SIMPL0_step_def)
  with "1.prems"(1) st
  have "okW (head_norm_dpair alg env dp0 \<bind>
      (\<lambda>(dp, env). SIMPL0_step alg (S alg) dp env ffs frs)) st'"
    by (cases r) auto
  then obtain dp env1 where hnd: "okW (head_norm_dpair alg env dp0) (dp, env1)"
    and step: "okW (SIMPL0_step alg (S alg) dp env1 ffs frs) st'"
    by (auto split: prod.splits)
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  note hd = head_norm_dpair_vreach[OF hnd]
  have e1: "tenv env1 = tenv env" using hd by simp
  from SIMPL0_step_vreach[OF IH step[unfolded dp]] have "vsr (vars t \<union> vars u) (env1, ffs, frs) st'" .
  then have "vsr (vdp dp) (env, ffs, frs) st'" unfolding vsr_tenv[OF e1] by (simp add: dp)
  from vsr_mono[OF this] hd st show ?case by simp
qed

corollary SIMPL0_vreach': "okW (SIMPL0 alg dp st) st' \<Longrightarrow> vsr (vdp dp) st st'"
  using SIMPL0_vreach by fastforce

lemma foldrW_SIMPL0_vreach: "okW (foldrW (SIMPL0 alg) dps st) st' \<Longrightarrow> vsr (vdps dps) st st'"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 alg) dps st) st1"
    and s: "okW (SIMPL0 alg dp st1) st'" by auto
  from vsr_trans[OF Cons.IH[OF f] SIMPL0_vreach'[OF s]] show ?case by (simp add: Un_ac)
qed (simp add: vsr_refl)

theorem SIMPL_vreach:
  assumes "SIMPL alg env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vsr (vdps dpairs) (env, [], []) st'"
  using assms
proof (induction alg env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S alg env dpairs r)
  note body = okW_of[OF "1.hyps" "1.prems"(1)]
  from body obtain env1 ffs frs
    where f: "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) (env1, ffs, frs)"
      and r: "okW (S alg env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by (rule SIMPL_bodyE)
  have v1: "vsr (vdps dpairs) (env, [], []) (env1, ffs, frs)" by (rule foldrW_SIMPL0_vreach[OF f])
  show ?case
  proof (cases "okW (S alg env1 (frs @ ffs)) st'")
    case True
    then obtain evs where "S alg env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    from "1.IH"[OF this snd_conv] have v2: "vsr (vdps (frs @ ffs)) (env1, [], []) st'" .
    have sub: "vdps (frs @ ffs) \<subseteq> vreach env (vdps dpairs)" using v1 by (auto simp: vsr_def)
    show ?thesis
      unfolding vsr_def
    proof (intro conjI allI)
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
    qed
  next
    case False
    with r v1 show ?thesis by simp
  qed
qed

corollary SIMPL_vreach': "okW (SIMPL alg env dps) st' \<Longrightarrow> vsr (vdps dps) (env, [], []) st'"
  using SIMPL_vreach by fastforce


subsection \<open>Counting rigid atoms\<close>

fun rcnt :: "dB \<Rightarrow> nat" where
  "rcnt (dB.Var n) = (if rigid_code n then 1 else 0)"
| "rcnt (BVar i) = 0"
| "rcnt (s \<degree> t) = rcnt s + rcnt t"
| "rcnt (dB.Abs t) = rcnt t"

lemma rcnt_map_BVars[simp]: "rcnt (map_BVars f s) = rcnt s"
  by (induction s arbitrary: f) auto

lemma rcnt_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> rcnt t = rcnt s"
proof (induction rule: eta.induct)
  case (eta s dummy)
  then show ?case by (simp add: subst_dummy_map_BVars)
qed auto

lemma rcnt_\<beta>\<eta>cl:
  assumes "\<beta>\<eta>cl s t" "(e, \<tau>) \<turnstile> s : T" "no_redex s"
  shows "rcnt t = rcnt s \<and> no_redex t"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case (step t u)
  have ty: "(e, \<tau>) \<turnstile> t : T" using subject_reduction_\<beta>\<eta>[OF step.hyps(1) assms(2)] .
  moreover from step.IH have nr: "no_redex t" by simp
  moreover from this step.hyps(2) have "t \<rightarrow>\<^sub>\<eta> u" by (auto dest: no_redex_no_beta)
  ultimately show ?case using rcnt_eta lsize_eta step.IH by metis
qed (simp add: assms(3))

lemma rcnt_equiv:
  assumes "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t" "(e, \<tau>) \<turnstile> s : T" "(e, \<tau>) \<turnstile> t : T" "no_redex s" "no_redex t"
  shows "rcnt s = rcnt t"
proof -
  from normal_form_ex[OF assms(2)] obtain n where n: "\<beta>\<eta>cl s n" "normal n" by blast
  have "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> n" using assms(1) n(1) by (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
  then have "\<beta>\<eta>cl t n" using n(2) by (rule equiv_\<beta>\<eta>cl_normal)
  with n(1) show ?thesis using rcnt_\<beta>\<eta>cl assms(2-5) by metis
qed


subsection \<open>Erasing the types of atoms\<close>

definition dT :: ptyp where
  "dT = TFree STR '''' []"

definition ec :: "nat \<Rightarrow> nat" where
  "ec n = (if n \<in> range code then
    (case atom_of n of AConst a T \<Rightarrow> code (AConst a dT) | AFree a T \<Rightarrow> code (AFree a dT) | AVar x \<Rightarrow> n)
   else n)"

lemma ec_simps[simp]:
  "ec (code (AConst a T)) = code (AConst a dT)" "ec (code (AFree a T)) = code (AFree a dT)"
  "ec (code (AVar x)) = code (AVar x)"
  by (simp_all add: ec_def)

lemma rigid_code_ec[simp]: "rigid_code (ec n) \<longleftrightarrow> rigid_code n"
proof (cases "n \<in> range code")
  case True
  then obtain a where "n = code a" by blast
  then show ?thesis by (cases a) (simp_all add: rigid_code_def)
qed (simp add: ec_def)

abbreviation ren :: "(nat \<Rightarrow> nat) \<Rightarrow> dB \<Rightarrow> dB" where
  "ren f s \<equiv> mk_subst (\<lambda>n. dB.Var (f n)) s"

lemma rcnt_ren: "(\<And>n. rigid_code (f n) \<longleftrightarrow> rigid_code n) \<Longrightarrow> rcnt (ren f s) = rcnt s"
  by (induction s) auto

lemma ren_beta_back: "ren f s \<rightarrow>\<^sub>\<beta> u \<Longrightarrow> \<exists>s'. s \<rightarrow>\<^sub>\<beta> s'"
proof (induction s arbitrary: u)
  case (App a b)
  have "ren f a \<degree> ren f b \<rightarrow>\<^sub>\<beta> u" using App.prems by simp
  then have "(\<exists>s'. ren f a = dB.Abs s') \<or> (\<exists>t. ren f a \<rightarrow>\<^sub>\<beta> t) \<or> (\<exists>t. ren f b \<rightarrow>\<^sub>\<beta> t)" by blast
  then show ?case
  proof (elim disjE exE)
    fix s' assume "ren f a = dB.Abs s'"
    then obtain a' where "a = dB.Abs a'" by (cases a) auto
    then show ?thesis by blast
  next
    fix t assume "ren f a \<rightarrow>\<^sub>\<beta> t"
    with App.IH(1) show ?thesis by blast
  next
    fix t assume "ren f b \<rightarrow>\<^sub>\<beta> t"
    with App.IH(2) show ?thesis by blast
  qed
next
  case (Abs t)
  have "dB.Abs (ren f t) \<rightarrow>\<^sub>\<beta> u" using Abs.prems by simp
  then obtain u' where "ren f t \<rightarrow>\<^sub>\<beta> u'" by blast
  with Abs.IH show ?case by blast
qed auto

lemma ren_\<beta>_nf:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sup>* n" "\<beta>_normal n"
  shows "\<beta>_nf (ren f s) = ren f n"
proof (rule \<beta>_nf_eq)
  show "ren f s \<rightarrow>\<^sub>\<beta>\<^sup>* ren f n" by (rule fact8_1[OF assms(1)]) simp
  show "\<beta>_normal (ren f n)" using ren_beta_back assms(2) by blast
qed

text \<open>Terms with the same atoms up to their types have the same erasure:\<close>

lemma tr_inst_ren:
  assumes "\<And>a T. h (code (AConst a T)) = dB.Var (code (AConst a dT))"
    "\<And>a T. h (code (AFree a T)) = dB.Var (code (AFree a dT))"
    "\<And>a T. h' (code (AConst a T)) = dB.Var (code (AConst a dT))"
    "\<And>a T. h' (code (AFree a T)) = dB.Var (code (AFree a dT))"
    "\<And>x. x \<in> vars s \<Longrightarrow> h (code (AVar x)) = h' (code (AVar x))"
  shows "mk_subst h (tr (inst \<rho> s)) = mk_subst h' (tr (inst \<rho>' s))"
  using assms(5) by (induction s) (simp_all add: assms(1-4))

text \<open>The erasures of the canonical solutions of the ground instances agree:\<close>

lemma ER_env_sol:
  assumes pi: "pinv alg ar A W env dps" and pi': "pinv alg ar A W' env dps'"
    and g: "gsol alg ar (tyenv env) \<rho>" and g': "gsol alg ar (tyenv env) \<rho>'"
  shows "ren ec (env_sol (instE \<rho> env) (ityp \<rho> env W) (code (AVar x))) =
    ren ec (env_sol (instE \<rho>' env) (ityp \<rho>' env W') (code (AVar x)))"
proof -
  note ei = env_invD[OF penv_inv_inst[OF pinvD(1)[OF pi] g]]
  note ei' = env_invD[OF penv_inv_inst[OF pinvD(1)[OF pi'] g']]
  let ?\<sigma> = "env_sol (instE \<rho> env) (ityp \<rho> env W)" and ?\<sigma>' = "env_sol (instE \<rho>' env) (ityp \<rho>' env W')"
  have rg: "?\<sigma> (code (AConst a T)) = dB.Var (code (AConst a T))" "?\<sigma> (code (AFree a T)) = dB.Var (code (AFree a T))"
    "?\<sigma>' (code (AConst a T)) = dB.Var (code (AConst a T))" "?\<sigma>' (code (AFree a T)) = dB.Var (code (AFree a T))"
    for a T
    by (simp_all add: env_sol_def env_map_rigid[OF ei(1,3)] env_map_rigid[OF ei'(1,3)])
  show ?thesis
  proof (induction x rule: wf_induct_rule[OF wf_dvar[OF ei(1,3)]])
    case (1 x)
    show ?case
    proof (cases "vt_lookup (tenv env) x")
      case None
      then have "vt_lookup (tenv (instE \<rho> env)) x = None" "vt_lookup (tenv (instE \<rho>' env)) x = None" by simp_all
      then show ?thesis
        by (simp add: env_sol_def env_map_unbound[OF ei(1,3)] env_map_unbound[OF ei'(1,3)])
    next
      case (Some b)
      then obtain U u where b: "vt_lookup (tenv env) x = Some (U, u)" by (cases b) auto
      have bi: "vt_lookup (tenv (instE \<rho> env)) x = Some (tsubst \<rho> U, inst \<rho> u)"
        "vt_lookup (tenv (instE \<rho>' env)) x = Some (tsubst \<rho>' U, inst \<rho>' u)"
        using b by simp_all
      have "ren ec (?\<sigma> (code (AVar x))) = mk_subst (\<lambda>n. ren ec (?\<sigma> n)) (tr (inst \<rho> u))"
        using env_map_bound[OF ei(1,3) bi(1)] by (simp add: env_sol_def subst_comp_def)
      also have "\<dots> = mk_subst (\<lambda>n. ren ec (?\<sigma>' n)) (tr (inst \<rho>' u))"
      proof (rule tr_inst_ren)
        fix y assume "y \<in> vars u"
        then have "(y, x) \<in> dvar (instE \<rho> env)" using dvarI[OF bi(1)] by simp
        with "1.IH" show "ren ec (?\<sigma> (code (AVar y))) = ren ec (?\<sigma>' (code (AVar y)))" by blast
      qed (simp_all add: rg)
      also have "\<dots> = ren ec (?\<sigma>' (code (AVar x)))"
        using env_map_bound[OF ei'(1,3) bi(2)] by (simp add: env_sol_def subst_comp_def)
      finally show ?thesis .
    qed
  qed
qed

lemma ER_inst:
  assumes pi: "pinv alg ar A W env dps" and pi': "pinv alg ar A W' env dps'"
    and g: "gsol alg ar (tyenv env) \<rho>" and g': "gsol alg ar (tyenv env) \<rho>'"
  shows "ren ec (mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))) =
    ren ec (mk_subst (env_sol (instE \<rho>' env) (ityp \<rho>' env W')) (tr (inst \<rho>' t)))"
proof -
  note ei = env_invD[OF penv_inv_inst[OF pinvD(1)[OF pi] g]]
  note ei' = env_invD[OF penv_inv_inst[OF pinvD(1)[OF pi'] g']]
  show ?thesis unfolding mk_subst_comp subst_comp_def
    by (rule tr_inst_ren) (simp_all add: env_sol_def env_map_rigid[OF ei(1,3)] env_map_rigid[OF ei'(1,3)]
      ER_env_sol[OF assms, unfolded env_sol_def])
qed

subsection \<open>The measure\<close>

definition rsz_at :: "tinst \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" where
  "rsz_at \<rho> env W t = rcnt (\<beta>_nf (mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))))"

lemma inst_typed_normal:
  assumes pi: "pinv alg ar A W env dps" and g: "gsol alg ar (tyenv env) \<rho>"
    and ty: "typed env W Ts t T" and tw: "\<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U"
  shows "(bnd_env (map (tsubst \<rho>) Ts), tau (ityp \<rho> env W)) \<turnstile>
      mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t)) : trty (tsubst \<rho> (tnorm (tyenv env) T))"
    "\<beta>_normal (\<beta>_nf (mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))))"
proof -
  note p = pinvD[OF pi]
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF p(2)] tinv_tcons_env[OF p(2)] by simp_all
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  have tc: "\<forall>U\<in>set Ts \<union> tys t. tcons (tyenv env) U" using tw tyw_tcons[OF p(2)] by blast
  have tyi: "has_type (ityp \<rho> env W) (map (tsubst \<rho>) Ts) (inst \<rho> t) (tsubst \<rho> (tnorm (tyenv env) T))"
    by (rule typed_inst[OF ac sol tc tcons_tnorm[OF ac(1)]]) (use ty in \<open>simp add: typed_tnorm[OF ac(1)]\<close>)
  show ty': "(bnd_env (map (tsubst \<rho>) Ts), tau (ityp \<rho> env W)) \<turnstile>
      mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t)) : trty (tsubst \<rho> (tnorm (tyenv env) T))"
    by (rule Unify_Match_Fin.inst_typed[OF penv_inv_inst[OF p(1) g] tyi])
  show "\<beta>_normal (\<beta>_nf (mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))))"
    by (rule \<beta>_nf_normal[OF typable_termip[OF typableI[OF ty']]])
qed

lemma rsz_at_indep:
  assumes pi: "pinv alg ar A W env dps" and pi': "pinv alg ar A W' env dps'"
    and g: "gsol alg ar (tyenv env) \<rho>" and g': "gsol alg ar (tyenv env) \<rho>'"
    and n: "\<beta>_normal (\<beta>_nf (mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))))"
      "\<beta>_normal (\<beta>_nf (mk_subst (env_sol (instE \<rho>' env) (ityp \<rho>' env W')) (tr (inst \<rho>' t))))"
  shows "rsz_at \<rho> env W t = rsz_at \<rho>' env W' t"
proof -
  let ?s = "mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))"
  let ?s' = "mk_subst (env_sol (instE \<rho>' env) (ityp \<rho>' env W')) (tr (inst \<rho>' t))"
  have "rsz_at \<rho> env W t = rcnt (ren ec (\<beta>_nf ?s))" by (simp add: rsz_at_def rcnt_ren)
  also have "\<dots> = rcnt (\<beta>_nf (ren ec ?s))" using ren_\<beta>_nf[OF \<beta>_nf_reduces n(1)] by simp
  also have "\<dots> = rcnt (\<beta>_nf (ren ec ?s'))" using ER_inst[OF assms(1-4)] by simp
  also have "\<dots> = rcnt (ren ec (\<beta>_nf ?s'))" using ren_\<beta>_nf[OF \<beta>_nf_reduces n(2)] by simp
  also have "\<dots> = rsz_at \<rho>' env W' t" by (simp add: rsz_at_def rcnt_ren)
  finally show ?thesis .
qed

definition rsz :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" where
  "rsz alg ar env W t = rsz_at (SOME \<rho>. gsol alg ar (tyenv env) \<rho>) env W t"

context wf_algebra
begin

text \<open>The measure is that of every ground instance:\<close>

lemma rsz_eq:
  assumes pi: "pinv alg ar A W env dps" and g: "gsol alg ar (tyenv env) \<rho>"
    and ty: "typed env W Ts t T" and tw: "\<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U"
  shows "rsz alg ar env W t = rsz_at \<rho> env W t"
proof -
  obtain \<rho>0 where "gsol alg ar (tyenv env) \<rho>0" by (rule pinv_gsol_exists[OF pi])
  then have g0: "gsol alg ar (tyenv env) (SOME \<rho>. gsol alg ar (tyenv env) \<rho>)"
    by (rule someI[where P = "\<lambda>\<rho>. gsol alg ar (tyenv env) \<rho>"])
  show ?thesis unfolding rsz_def
    by (rule rsz_at_indep[OF pi pi g0 g inst_typed_normal(2)[OF pi g0 ty tw] inst_typed_normal(2)[OF pi g ty tw]])
qed

end

subsection \<open>Properties of the measure\<close>

lemma rcnt_list_app: "rcnt (h \<degree>\<degree> ws) = rcnt h + sum_list (map rcnt ws)"
  by (induction ws arbitrary: h) simp_all

context wf_algebra
begin

lemma pinv_pcinv_sol:
  assumes "pinv alg ar A W env dps" "gsol alg ar (tyenv env) \<rho>"
  shows "pcinv alg ar A W \<rho> (tau (ityp \<rho> env W)) (env_sol (instE \<rho> env) (ityp \<rho> env W)) env []"
  using pinv_Nil[OF assms(1)] assms(2) pinv_env_sol[OF assms] by (simp add: pcinv_def)

lemma rsz_equiv:
  assumes pi: "pinv alg ar A W env dps" and g: "gsol alg ar (tyenv env) \<rho>"
    and ty: "typed env W Ts t T" "typed env W Ts t' T"
    and tw: "\<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U" "\<forall>U\<in>set Ts \<union> tys t'. tyw ar (tyenv env) A U"
    and eq: "mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))"
  shows "rsz alg ar env W t' = rsz alg ar env W t"
proof -
  let ?\<sigma> = "env_sol (instE \<rho> env) (ityp \<rho> env W)"
  let ?s = "mk_subst ?\<sigma> (tr (inst \<rho> t))" and ?s' = "mk_subst ?\<sigma> (tr (inst \<rho> t'))"
  note n = inst_typed_normal[OF pi g ty(1) tw(1)] and n' = inst_typed_normal[OF pi g ty(2) tw(2)]
  have "rcnt (\<beta>_nf ?s') = rcnt (\<beta>_nf ?s)"
  proof (rule rcnt_equiv)
    show "\<beta>_nf ?s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<beta>_nf ?s"
      using equiv_trans[OF equiv_trans[OF \<beta>_nf_equiv eq] equiv_sym[OF \<beta>_nf_equiv]] .
    show "no_redex (\<beta>_nf ?s')" "no_redex (\<beta>_nf ?s)"
      using beta_normal_no_redex n(2) n'(2) by blast+
  qed (use \<beta>_nf_typing n(1) n'(1) in blast)+
  then show ?thesis
    using rsz_eq[OF pi g ty(1) tw(1)] rsz_eq[OF pi g ty(2) tw(2)] by (simp add: rsz_at_def)
qed

text \<open>\<^const>\<open>copycons\<close> normalizes an argument without changing its measure:\<close>

lemma pcopy_norm_rsz:
  assumes pi: "pinv alg ar A W env dps" and sb: "sbinders ar rb"
    and twb: "\<forall>U\<in>snd ` set rb. tyw ar (tyenv env) A U"
    and w: "swf_tm ar rb t" and twt: "\<forall>U\<in>tys t. tyw ar (tyenv env) A U"
    and ty: "typed env W (map snd rb) t T" and bl: "below (maxidx env) t"
  obtains u1 u2 where "ok (head_norm env t) u1" "ok (eta_norm env rb u1) u2"
    "swf_tm ar rb u2" "\<forall>U\<in>tys u2. tyw ar (tyenv env) A U" "hnf u2"
    "hlong (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u2) (tnorm (tyenv env) T)"
    "below (maxidx env) u2" "typed env W (map snd rb) u2 T" "rsz alg ar env W u2 = rsz alg ar env W t"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  have ac: "tacyc (tyenv env)" using tinv_tacyc[OF pinvD(2)[OF pi]] .
  obtain u1 u2 where
    c: "ok (head_norm env t) u1" "ok (eta_norm env rb u1) u2"
    "swf_tm ar rb u2" "\<forall>U\<in>tys u2. tyw ar (tyenv env) A U" "hnf u2"
    "hlong (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u2) (tnorm (tyenv env) T)"
    "below (maxidx env) u2" "vps (inst \<rho> u2) \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
    "mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> u2)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> t))"
    by (rule pcopy_norm[OF pinv_pcinv_sol[OF pi g] sb twb w twt ty bl])
  have ty2: "typed env W (map snd rb) u2 T"
    using hlong_typed[OF c(6)] by (simp add: typed_def)
  have "rsz alg ar env W u2 = rsz alg ar env W t"
    by (rule rsz_equiv[OF pi g ty ty2 _ _ c(9)]) (use twb twt c(4) in auto)
  from that[OF c(1-7) ty2 this] show thesis .
qed

text \<open>The arguments of an imitation have smaller measures:\<close>

lemma rsz_rigid_arg:
  assumes pi: "pinv alg ar A W env dps" and ty: "typed env W Ts (list_comb h ts) B"
    and tw: "\<forall>U\<in>set Ts \<union> tys (list_comb h ts). tyw ar (tyenv env) A U"
    and h: "h = Const a T \<or> h = Free a T" and i: "i < length ts"
  shows "rsz alg ar env W (ts ! i) < rsz alg ar env W (list_comb h ts)"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  have ac: "tacyc (tyenv env)" using tinv_tacyc[OF pinvD(2)[OF pi]] .
  note ei = env_invD[OF penv_inv_inst[OF pinvD(1)[OF pi] g]]
  from typed_list_comb_args[OF ac ty] obtain As where tya: "list_all2 (typed env W Ts) ts As" by blast
  have tyi: "typed env W Ts (ts ! i) (As ! i)" using list_all2_nthD[OF tya i] .
  have twi: "\<forall>U\<in>set Ts \<union> tys (ts ! i). tyw ar (tyenv env) A U"
    using tw i by (auto simp: tys_list_comb)
  let ?\<sigma> = "env_sol (instE \<rho> env) (ityp \<rho> env W)"
  let ?ws = "map (\<lambda>t. mk_subst ?\<sigma> (tr (inst \<rho> t))) ts"
  obtain n where hn: "tr (inst \<rho> h) = dB.Var n" "rigid_code n" using h by auto
  have sn: "?\<sigma> n = dB.Var n" using env_map_rigid[OF ei(1,3) hn(2)] by (simp add: env_sol_def)
  have s: "mk_subst ?\<sigma> (tr (inst \<rho> (list_comb h ts))) = dB.Var n \<degree>\<degree> ?ws"
    using hn sn by (simp add: Poly_Inst.inst_list_comb tr_list_comb comp_def)
  note n = inst_typed_normal[OF pi g ty tw]
  have nf: "\<beta>_nf (dB.Var n \<degree>\<degree> ?ws) = dB.Var n \<degree>\<degree> map \<beta>_nf ?ws"
    by (rule \<beta>_nf_atom_apps) (use typableI[OF n(1)] s in simp_all)
  have "rcnt (\<beta>_nf (?ws ! i)) \<le> sum_list (map rcnt (map \<beta>_nf ?ws))"
    using i by (intro member_le_sum_list) auto
  then have "rsz_at \<rho> env W (ts ! i) < rsz_at \<rho> env W (list_comb h ts)"
    using i hn(2) by (simp add: rsz_at_def s nf rcnt_list_app)
  then show ?thesis using rsz_eq[OF pi g ty tw] rsz_eq[OF pi g tyi twi] by simp
qed

lemma rsz_Abs:
  assumes pi: "pinv alg ar A W env dps"
    and ty: "typed env W Ts (Abs a T b) U" "typed env W (T # Ts) b U'"
    and tw: "\<forall>U\<in>set Ts \<union> tys (Abs a T b). tyw ar (tyenv env) A U"
  shows "rsz alg ar env W (Abs a T b) = rsz alg ar env W b"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  have tw': "\<forall>U\<in>set (T # Ts) \<union> tys b. tyw ar (tyenv env) A U" using tw by auto
  note n = inst_typed_normal[OF pi g ty(1) tw]
  let ?s = "mk_subst (env_sol (instE \<rho> env) (ityp \<rho> env W)) (tr (inst \<rho> b))"
  have "\<beta>_nf (dB.Abs ?s) = dB.Abs (\<beta>_nf ?s)" by (rule \<beta>_nf_Abs) (use typableI[OF n(1)] in simp)
  then have "rsz_at \<rho> env W (Abs a T b) = rsz_at \<rho> env W b" by (simp add: rsz_at_def)
  then show ?thesis using rsz_eq[OF pi g ty(1) tw] rsz_eq[OF pi g ty(2) tw'] by simp
qed

end


subsection \<open>Extensions of states without a solution\<close>

lemma vreach_new:
  assumes fr: "fresh_env env" and NV: "\<forall>y\<in>NV. maxidx env < snd y"
  shows "vreach env NV = NV"
proof
  show "vreach env NV \<subseteq> NV"
  proof
    fix y assume "y \<in> vreach env NV"
    then obtain x where x: "x \<in> NV" "(y, x) \<in> (ndep env)\<^sup>*" by (auto simp: vreach_def)
    from x(2) have "y = x"
    proof (cases rule: rtranclE)
      case (step w)
      from step(2) obtain U u where "vt_lookup (tenv env) x = Some (U, u)" by (auto simp: ndep_def)
      from fresh_envD[OF fr this] NV x(1) show ?thesis by auto
    qed simp
    with x(1) show "y \<in> NV" by simp
  qed
  show "NV \<subseteq> vreach env NV" by (rule vreach_incl)
qed

text \<open>The counterpart of \<^const>\<open>tsext\<close> for problems with type variables, with reachability without types:\<close>

definition ptsext :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> indexname set \<Rightarrow> indexname set \<Rightarrow> bool" where
  "ptsext alg ar A W env W' env' dps' D NV \<longleftrightarrow>
    pinv alg ar A W' env' dps' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
    finite NV \<and> (\<forall>y\<in>NV. maxidx env < snd y \<and> snd y \<le> maxidx env') \<and>
    (\<forall>X. vreach env' X \<subseteq> vreach env (X \<union> D) \<union> NV) \<and> vdps dps' \<subseteq> vreach env D \<union> NV"

lemma ptsextD:
  assumes "ptsext alg ar A W env W' env' dps' D NV"
  shows "pinv alg ar A W' env' dps'" "agreeV (maxidx env) W W'" "maxidx env \<le> maxidx env'" "pextends env' env"
    "finite NV" "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd y \<and> snd y \<le> maxidx env'"
    "\<And>X. vreach env' X \<subseteq> vreach env (X \<union> D) \<union> NV" "vdps dps' \<subseteq> vreach env D \<union> NV"
  using assms by (auto simp: ptsext_def)

lemma ptsext_refl: "pinv alg ar A W env dps \<Longrightarrow> vdps dps \<subseteq> D \<Longrightarrow> ptsext alg ar A W env W env dps D {}"
  using vreach_incl[of D env] vreach_subset[of _ _ env]
  by (auto simp: ptsext_def pextends_def extends_def vreach_Un)

lemma ptsext_mono:
  assumes s: "ptsext alg ar A W env W' env' dps' D NV" and D: "D \<subseteq> vreach env D'"
  shows "ptsext alg ar A W env W' env' dps' D' NV"
proof -
  have r: "vreach env (X \<union> D) \<subseteq> vreach env (X \<union> D')" for X by (rule vreach_absorb[OF D])
  have "vreach env D \<subseteq> vreach env D'" using D by (rule vreach_mono)
  then have "vdps dps' \<subseteq> vreach env D' \<union> NV" using s by (auto simp: ptsext_def)
  moreover have "vreach env' X \<subseteq> vreach env (X \<union> D') \<union> NV" for X using s r[of X] by (auto simp: ptsext_def)
  ultimately show ?thesis using s by (simp add: ptsext_def)
qed

lemma ptsext_trans:
  assumes s1: "ptsext alg ar A W env W1 env1 dps1 D1 NV1" and s2: "ptsext alg ar A W1 env1 W2 env2 dps2 D2 NV2"
    and fr: "fresh_env env" and D: "D2 \<subseteq> vreach env D1 \<union> NV1"
  shows "ptsext alg ar A W env W2 env2 dps2 D1 (NV1 \<union> NV2)"
proof -
  note c1 = ptsextD[OF s1] and c2 = ptsextD[OF s2]
  have nv1: "vreach env NV1 = NV1" using vreach_new[OF fr] c1(6) by blast
  have rD2: "vreach env D2 \<subseteq> vreach env D1 \<union> NV1"
    using vreach_mono[of D2 env "D1 \<union> NV1"] D vreach_incl[of "D1 \<union> NV1" env] nv1
    by (auto simp: vreach_Un)
  have r: "vreach env2 X \<subseteq> vreach env (X \<union> D1) \<union> (NV1 \<union> NV2)" for X
  proof -
    have "vreach env2 X \<subseteq> vreach env1 (X \<union> D2) \<union> NV2" by (rule c2(7))
    also have "\<dots> \<subseteq> vreach env (X \<union> D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(7)[of "X \<union> D2"] by blast
    also have "\<dots> \<subseteq> vreach env (X \<union> D1) \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: vreach_Un)
    finally show ?thesis .
  qed
  have v: "vdps dps2 \<subseteq> vreach env D1 \<union> (NV1 \<union> NV2)"
  proof -
    have "vdps dps2 \<subseteq> vreach env1 D2 \<union> NV2" by (rule c2(8))
    also have "\<dots> \<subseteq> vreach env (D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(7)[of D2] by blast
    also have "\<dots> \<subseteq> vreach env D1 \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: vreach_Un)
    finally show ?thesis .
  qed
  show ?thesis unfolding ptsext_def
  proof (intro conjI allI ballI c2(1) r v)
    show "agreeV (maxidx env) W W2" using agreeV_trans[OF c1(2) c2(2) c1(3)] .
    show "maxidx env \<le> maxidx env2" using c1(3) c2(3) by simp
    show "pextends env2 env" using c2(4) c1(4) by (rule pextends_trans)
    show "finite (NV1 \<union> NV2)" using c1(5) c2(5) by simp
    show "maxidx env < snd y" if "y \<in> NV1 \<union> NV2" for y
      using that c1(3) c1(6)[of y] c2(6)[of y] by auto
    show "snd y \<le> maxidx env2" if "y \<in> NV1 \<union> NV2" for y
      using that c2(3) c1(6)[of y] c2(6)[of y] by auto
  qed
qed

text \<open>Reachability in a ground instance is reachability without types:\<close>

lemma reach_inst_vreach: "y \<in> reach (instE \<rho> env) X \<Longrightarrow> fst y \<in> vreach env (fst ` X)"
proof -
  assume "y \<in> reach (instE \<rho> env) X"
  then obtain x where x: "x \<in> X" "(y, x) \<in> (dep (instE \<rho> env))\<^sup>*" by (auto simp: reach_def)
  have "(fst y, fst x) \<in> (ndep env)\<^sup>*" using x(2)
  proof (induction rule: converse_rtrancl_induct)
    case (step a b)
    from step.hyps(1) obtain u where lu: "lk (instE \<rho> env) (fst b) (snd b) = Some u" and au: "a \<in> vps u"
      by (auto simp: dep_def)
    from lkD[OF lu] obtain U u0 where b: "vt_lookup (tenv env) (fst b) = Some (U, u0)" and u: "u = inst \<rho> u0"
      by auto
    have "fst a \<in> vars u" using au by (force simp: vars_eq_vps)
    then have "(fst a, fst b) \<in> ndep env" using b u by (auto simp: ndep_def)
    from converse_rtrancl_into_rtrancl[OF this step.IH] show ?case .
  qed simp
  with x(1) show "fst y \<in> vreach env (fst ` X)" by (auto simp: vreach_def)
qed

lemma vreach_below:
  assumes fr: "fresh_env env" and X: "\<forall>y\<in>X. snd y \<le> maxidx env" and y: "y \<in> vreach env X"
  shows "snd y \<le> maxidx env"
proof -
  from y obtain x where x: "x \<in> X" "(y, x) \<in> (ndep env)\<^sup>*" by (auto simp: vreach_def)
  from x(2) show ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    with X x(1) show ?case by blast
  next
    case (step a b)
    from step.hyps(1) obtain U u where "vt_lookup (tenv env) b = Some (U, u)" "a \<in> vars u"
      by (auto simp: ndep_def)
    with fresh_envD[OF fr] show ?case by (auto simp: below_def)
  qed
qed

lemma vreach_free:
  assumes vg: "vgood Fd Ft env" and X: "X \<inter> Ft = {}" and y: "y \<in> vreach env X"
  shows "y \<notin> Ft"
proof -
  from y obtain x where x: "x \<in> X" "(y, x) \<in> (ndep env)\<^sup>*" by (auto simp: vreach_def)
  from x(2) show ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    with X x(1) show ?case by blast
  next
    case (step a b)
    from step.hyps(1) obtain U u where "vt_lookup (tenv env) b = Some (U, u)" "a \<in> vars u"
      by (auto simp: ndep_def)
    with vgoodD[OF vg] show ?case by blast
  qed
qed

lemma extends_instE: "extends env' env \<Longrightarrow> extends (instE \<rho> env') (instE \<rho> env)"
  by (auto simp: extends_def)

lemma gsol_textends: "textends \<theta> \<theta>' \<Longrightarrow> gsol alg ar \<theta>' \<rho> \<Longrightarrow> gsol alg ar \<theta> \<rho>"
  by (auto simp: gsol_def intro: tsol_textends)


subsection \<open>The setting of a step of matching\<close>

text \<open>
  As in locale \<^locale>\<open>mfin\<close>: the variables up to index \<open>m0\<close> are those of the original
  problem, and the old ones it can reach are among the finite set \<open>S0\<close>; the new variables are
  dead (\<open>Fd\<close>) or occur at heads only (\<open>Ft\<close>).
\<close>

locale pmfin = wf_algebra +
  fixes A :: "(indexname \<times> psort) set" and cfg :: cfg and vname :: name and m0 :: integer
    and S0 :: "indexname set" and Fd Ft :: "indexname set"
  assumes finA: "finite A" and cfg: "cfg_alg cfg = alg"
    and S0: "finite S0" "\<And>x. x \<in> S0 \<Longrightarrow> snd x \<le> m0"
    and regime: "Fd = {x. m0 < snd x} \<and> Ft = {} \<or> Fd = {} \<and> Ft = {x. m0 < snd x}"
begin

definition pmu1 :: "env \<Rightarrow> nat" where
  "pmu1 env = card {x\<in>S0. vt_lookup (tenv env) x = None}"

definition poldin :: "env \<Rightarrow> indexname set \<Rightarrow> bool" where
  "poldin env X \<longleftrightarrow> (\<forall>y\<in>vreach env X. snd y \<le> m0 \<longrightarrow> y \<in> S0)"

definition psh :: "pterm \<Rightarrow> bool" where
  "psh t \<longleftrightarrow> dead Fd t \<and> vars t \<inter> Ft = {}"

definition ptok :: "pterm list \<Rightarrow> bool" where
  "ptok targs \<longleftrightarrow> (Fd \<noteq> {} \<longrightarrow> (\<exists>t\<in>set targs. \<not> is_Bound t)) \<and> (Ft \<noteq> {} \<longrightarrow> (\<forall>t\<in>set targs. is_Bound t))"

lemma extends_None: "extends env' env \<Longrightarrow> vt_lookup (tenv env') x = None \<Longrightarrow> vt_lookup (tenv env) x = None"
  unfolding extends_def by (metis option.distinct(1) option.exhaust)

lemma pmu1_mono: "extends env' env \<Longrightarrow> pmu1 env' \<le> pmu1 env"
  unfolding pmu1_def using S0(1) by (intro card_mono) (auto dest: extends_None)

lemma pmu1_eq:
  assumes "extends env' env" "pmu1 env' = pmu1 env" "y \<in> S0" "vt_lookup (tenv env) y = None"
  shows "vt_lookup (tenv env') y = None"
proof -
  let ?A = "{y\<in>S0. vt_lookup (tenv env') y = None}" and ?B = "{y\<in>S0. vt_lookup (tenv env) y = None}"
  have "?A \<subseteq> ?B" using assms(1) by (auto dest: extends_None)
  moreover have "finite ?B" using S0(1) by simp
  moreover have "card ?A = card ?B" using assms(2) by (simp add: pmu1_def)
  ultimately have "?A = ?B" by (intro card_subset_eq)
  with assms(3,4) show ?thesis by blast
qed

lemma poldin_mono: "poldin env Y \<Longrightarrow> X \<subseteq> vreach env Y \<Longrightarrow> poldin env X"
  using vreach_mono[of X env Y] by (auto simp: poldin_def)

lemma poldin_ptsext:
  assumes "ptsext alg ar A W env W' env' dps' D NV" "poldin env (X \<union> D)" "m0 \<le> maxidx env"
  shows "poldin env' X"
  unfolding poldin_def
proof (intro ballI impI)
  fix y assume y: "y \<in> vreach env' X" "snd y \<le> m0"
  from ptsextD(7)[OF assms(1)] y(1) have "y \<in> vreach env (X \<union> D) \<or> y \<in> NV" by blast
  then show "y \<in> S0"
  proof
    assume "y \<in> NV"
    with ptsextD(6)[OF assms(1), of y] y(2) assms(3) show ?thesis by simp
  qed (use assms(2) y(2) in \<open>auto simp: poldin_def\<close>)
qed

text \<open>The measure of a term of the original problem does not change as long as no old variable is assigned.\<close>

lemma rsz_stable:
  assumes pi: "pinv alg ar A W env dps" and vg: "vgood Fd Ft env"
    and s: "ptsext alg ar A W env W' env' dps' D NV" and vg': "vgood Fd Ft env'"
    and o: "poldin env (vars a)" and ty: "typed env W Bs a T"
    and tw: "\<forall>U\<in>set Bs \<union> tys a. tyw ar (tyenv env) A U" and b: "below (maxidx env) a" and sa: "psh a"
    and mu: "pmu1 env' = pmu1 env"
  shows "rsz alg ar env' W' a = rsz alg ar env W a"
proof -
  note c = ptsextD[OF s]
  note p = pinvD[OF pi] and p' = pinvD[OF c(1)]
  obtain \<rho> where g': "gsol alg ar (tyenv env') \<rho>" by (rule pinv_gsol_exists[OF c(1)])
  have te: "textends (tyenv env) (tyenv env')" using c(4) by (simp add: pextends_def)
  have g: "gsol alg ar (tyenv env) \<rho>" by (rule gsol_textends[OF te g'])
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF p(2)] tinv_tcons_env[OF p(2)] by simp_all
  have ac': "tacyc (tyenv env')" using tinv_tacyc[OF p'(2)] .
  have ty': "typed env' W' Bs a T" by (rule typed_psext[OF ac' c(4) p(6) p'(6) c(2) b ty])
  have tw': "\<forall>U\<in>set Bs \<union> tys a. tyw ar (tyenv env') A U" using tw tyw_textends[OF ac' te] by blast
  let ?V = "ityp \<rho> env W" and ?V' = "ityp \<rho> env' W'"
  have ei: "env_inv ar ?V (instE \<rho> env)" by (rule penv_inv_inst[OF p(1) g])
  have ei': "env_inv ar ?V' (instE \<rho> env')" by (rule penv_inv_inst[OF p'(1) g'])
  note e = env_invD[OF ei]
  have ext: "extends (instE \<rho> env') (instE \<rho> env)" by (rule extends_instE[OF pextendsD(1)[OF c(4)]])
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  have tc: "\<forall>U\<in>set Bs \<union> tys a. tcons (tyenv env) U" using tw tyw_tcons[OF p(2)] by blast
  have tyi: "has_type ?V (map (tsubst \<rho>) Bs) (inst \<rho> a) (tsubst \<rho> (tnorm (tyenv env) T))"
    by (rule typed_inst[OF ac sol tc tcons_tnorm[OF ac(1)]]) (use ty in \<open>simp add: typed_tnorm[OF ac(1)]\<close>)
  have vt: "vtyped ?V (inst \<rho> a)" by (rule has_type_vtyped[OF tyi])
  have "mk_subst (env_sol (instE \<rho> env') ?V') (tr (inst \<rho> a)) = mk_subst (env_sol (instE \<rho> env) ?V) (tr (inst \<rho> a))"
  proof (rule Unify_Match_Fin.inst_extend[OF ei ei' ext vt])
    fix y assume y: "y \<in> reach (instE \<rho> env) (vps (inst \<rho> a))" and n: "lk (instE \<rho> env) (fst y) (snd y) = None"
    have yv: "fst y \<in> vreach env (vars a)"
      using reach_inst_vreach[OF y] by (simp add: vars_eq_vps[symmetric])
    have Vy: "?V (fst y) = snd y"
      by (rule reach_vtyped[OF e(3) _ y]) (use vt in \<open>auto simp: vtyped_def\<close>)
    have unb: "vt_lookup (tenv env) (fst y) = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env) (fst y) \<noteq> None"
      then obtain U u where bd: "vt_lookup (tenv env) (fst y) = Some (U, u)" by auto
      then have bi: "vt_lookup (tenv (instE \<rho> env)) (fst y) = Some (tsubst \<rho> U, inst \<rho> u)" by simp
      from env_typedD[OF e(3) bi] Vy have "tsubst \<rho> U = snd y" by simp
      then have "lk (instE \<rho> env) (fst y) (snd y) = Some (inst \<rho> u)" unfolding lk_def bi by simp
      with n show False by simp
    qed
    have yb: "snd (fst y) \<le> maxidx env"
      by (rule vreach_below[OF penv_invD(6)[OF p(1)] _ yv]) (use b in \<open>auto simp: below_def\<close>)
    have unb': "vt_lookup (tenv env') (fst y) = None"
    proof (cases "snd (fst y) \<le> m0")
      case True
      with o yv have "fst y \<in> S0" by (auto simp: poldin_def)
      from pmu1_eq[OF pextendsD(1)[OF c(4)] mu this unb] show ?thesis .
    next
      case False
      with regime have "fst y \<in> Fd \<or> fst y \<in> Ft" by auto
      moreover have "fst y \<notin> Ft" using vreach_free[OF vg _ yv] sa by (auto simp: psh_def)
      ultimately have "fst y \<in> Fd" by simp
      then show ?thesis using vg' by (cases "vt_lookup (tenv env') (fst y)") (auto dest: vgoodD)
    qed
    have "?V' (fst y) = ?V (fst y)"
      using fun_cong[OF pinv_ityp[OF c(1) g'], of "fst y"] fun_cong[OF pinv_ityp[OF pi g], of "fst y"]
        agreeV_D[OF c(2) yb] by simp
    then show "lk (instE \<rho> env') (fst y) (snd y) = None \<and> ?V' (fst y) = ?V (fst y)"
      using unb' by (simp add: lk_def)
  qed
  then have "rsz_at \<rho> env' W' a = rsz_at \<rho> env W a" by (simp add: rsz_at_def)
  then show ?thesis using rsz_eq[OF c(1) g' ty' tw'] rsz_eq[OF pi g ty tw] by simp
qed

end


subsection \<open>Type unification of projections\<close>

lemma okW_cunify_types: "okW (cunify_types alg T U env) env' \<Longrightarrow> unify_types alg T U env = Some (Ok env')"
  by (auto simp: cunify_types_def bindW_def raiseW_def emit_def split: option.splits res.splits exn.splits)

lemma proj_unify_cunify:
  "okW (proj_unify cfg base bary Cs env) env' \<Longrightarrow>
    okW (cunify_types (cfg_alg cfg) (if Cs = [] then base else bary) (if Cs = [] then bary else foldr fun_type Cs base) env) env'"
  by (cases "Cs = []") (auto simp: proj_unify_def test_unify_types_def bindW_def whenW_def emit_def returnW_def
      split: if_splits option.splits ures.splits prod.splits)

context wf_algebra
begin

text \<open>The type unification of a projection with the guess \<open>p\<close> keeps the invariant:\<close>

lemma proj_unify_pinv:
  assumes pi0: "pinv alg ar A W env dps" and twb: "tyw ar (tyenv env) A base" and twy: "tyw ar (tyenv env) A bary"
    and cfg: "cfg_alg cfg = alg" and g: "gentvars p env = (e0, Cs)"
    and pu: "okW (proj_unify cfg base bary Cs e0) env'"
  shows "pinv alg ar A W env' dps" "tenv env' = tenv env" "pextends env' env" "maxidx env \<le> maxidx env'"
    "\<forall>C\<in>set Cs. tyw ar (tyenv env') A C" "tnorm (tyenv env') bary = tnorm (tyenv env') (foldr fun_type Cs base)"
proof -
  let ?\<theta> = "tyenv env" and ?A' = "A \<union> ctvars Cs"
  note pi = pinvD[OF pi0]
  note ei = penv_invD[OF pi(1)]
  note gs = gentvars_simps[OF g] and gm = gentvars_cases(1)[OF g]
  define X where "X = (if Cs = [] then base else bary)"
  define Y where "Y = (if Cs = [] then bary else foldr fun_type Cs base)"
  have cu: "okW (cunify_types alg X Y e0) env'" using proj_unify_cunify[OF pu] cfg by (simp add: X_def Y_def)
  have ti0: "tinv ar (maxidx e0) ?\<theta> A" by (rule tinv_mono[OF pi(2) gm])
  have pi1: "pinv alg ar A W e0 dps"
    by (rule pinv_text[OF pi0 gs(1)]) (simp_all add: gs(2) textends_refl gm ti0 ei(2))
  have ti0': "tinv ar (maxidx e0) (tyenv e0) ?A'" using tinv_gentvars[OF pi(2) g] gs(2) by simp
  have twC: "\<forall>C\<in>set Cs. tyw ar (tyenv e0) ?A' C" using tyw_gentvars[OF pi(2) g] gs(2) by simp
  have tw0: "tyw ar (tyenv e0) ?A' base" "tyw ar (tyenv e0) ?A' bary"
    using twb twy gs(2) by (auto intro: tyw_mono)
  have twXY: "tyw ar (tyenv e0) ?A' X" "tyw ar (tyenv e0) ?A' Y"
    using tw0 twC by (auto simp: X_def Y_def tyw_foldr_fun)
  have srt0: "tsorted alg (tyenv e0)" using ei(2) gs(2) by simp
  from unify_types_poly[OF ti0' srt0 twXY] okW_cunify_types[OF cu]
  have te: "tenv env' = tenv e0"
    and ts0: "Type_Mgu.tstep alg ar ?A' (\<lambda>\<rho>. tsubst \<rho> X = tsubst \<rho> Y) (tyenv e0) (maxidx e0) (tyenv env') (maxidx env')"
    and eq: "\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> X = tsubst \<rho> Y" and srt: "tsorted alg (tyenv env')"
    by auto
  note ts = Type_Mgu.tstepD[OF ts0]
  have ti': "tinv ar (maxidx env') (tyenv env') A" by (rule tinv_subset[OF ts(3)]) blast
  show pi': "pinv alg ar A W env' dps" by (rule pinv_text[OF pi1 te ts(1,2) ti' srt])
  show "tenv env' = tenv env" using te gs(1) by simp
  show pe: "pextends env' env"
    using te ts(1) gs by (simp add: pextends_def extends_def)
  show "maxidx env \<le> maxidx env'" using gm ts(2) by simp
  let ?\<theta>' = "tyenv env'"
  have ac': "tacyc ?\<theta>'" by (rule tinv_tacyc[OF ts(3)])
  have ext0: "textends ?\<theta> ?\<theta>'" using pe by (simp add: pextends_def)
  have tXY: "tnorm ?\<theta>' X = tnorm ?\<theta>' Y" by (rule tnorm_eq_tsol[OF ac']) (use eq in blast)
  show tb': "tnorm ?\<theta>' bary = tnorm ?\<theta>' (foldr fun_type Cs base)"
    using tXY by (cases "Cs = []") (simp_all add: X_def Y_def)
  show "\<forall>C\<in>set Cs. tyw ar ?\<theta>' A C"
  proof
    fix C assume C: "C \<in> set Cs"
    have t1: "tyw ar ?\<theta>' ?A' C" using twC C tyw_textends[OF ac' ext0] gs(2) by simp
    have "uvars ?\<theta>' C \<subseteq> uvars ?\<theta>' (foldr fun_type Cs base)" using C by (auto simp: uvars_foldr_fun)
    also have "\<dots> = uvars ?\<theta>' bary" using uvars_tnorm_eq[OF tb'] by simp
    also have "\<dots> \<subseteq> uvarsA ?\<theta>' A" using tyw_textends[OF ac' ext0 twy] by (simp add: tyw_def)
    finally show "tyw ar ?\<theta>' A C" by (rule tyw_shrink[OF ts(3) t1])
  qed
qed

end

end
