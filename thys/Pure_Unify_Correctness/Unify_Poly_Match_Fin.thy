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


text \<open>The new variables of \<^const>\<open>make_args\<close> and \<^const>\<open>genvar\<close> keep the invariant:\<close>

lemma pinv_psext:
  assumes pi0: "pinv alg ar A W env dps" and pi1: "pinv alg ar A W1 env1 []"
    and pe: "pextends env1 env" and ag: "agreeV (maxidx env) W W1" and mx: "maxidx env \<le> maxidx env1"
  shows "pinv alg ar A W1 env1 dps"
proof -
  note pi = pinvD[OF pi0] and pi' = pinvD[OF pi1]
  have ac': "tacyc (tyenv env1)" by (rule tinv_tacyc[OF pi'(2)])
  have ext: "textends (tyenv env) (tyenv env1)" using pe by (simp add: pextends_def)
  have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar (tyenv env1) A T) \<and> ptyped env1 W1 dp \<and>
      dp_below (maxidx env1) dp" if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from pi(4)[OF dp] dpe obtain T where w: "swf_dp ar dp" and tw: "\<forall>T\<in>dtys dp. tyw ar (tyenv env) A T"
      and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T"
      and bl: "below (maxidx env) t" "below (maxidx env) u"
      by auto
    have "ptyped env1 W1 dp"
      using typed_psext[OF ac' pe pi(6) pi'(6) ag bl(1) ty(1)] typed_psext[OF ac' pe pi(6) pi'(6) ag bl(2) ty(2)] dpe
      by auto
    moreover have "\<forall>T\<in>dtys dp. tyw ar (tyenv env1) A T" using tw tyw_textends[OF ac' ext] by blast
    moreover have "dp_below (maxidx env1) dp" using bl below_mono[OF _ mx] dpe by simp
    ultimately show ?thesis using w by blast
  qed
  with pi1 show ?thesis by (auto simp: pinv_def)
qed

lemma make_args_pinv:
  assumes pi: "pinv alg ar A W env dps" and ma: "make_args a Ts env Us = (env1, args)"
    and tw: "\<forall>T\<in>set Ts \<union> set Us. tyw ar (tyenv env) A T"
  obtains W1 xs where "pinv alg ar A W1 env1 dps" "agreeV (maxidx env) W W1" "maxidx env \<le> maxidx env1"
    "pextends env1 env" "tenv env1 = tenv env" "tyenv env1 = tyenv env"
    "length xs = length Us" "distinct xs" "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env1"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. W1 (xs ! i) = foldr fun_type Ts (Us ! i)"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  show ?thesis
  proof (rule make_args_pextend[OF pinv_pcinv_sol[OF pi g] ma tw,
        of "map (\<lambda>U. cterm (tsubst \<rho> (foldr fun_type Ts U))) Us"])
    fix i assume "i < length Us"
    then show "no_loose_bound (map (\<lambda>U. cterm (tsubst \<rho> (foldr fun_type Ts U))) Us ! i) 0 \<and>
        (\<forall>e. (e, tau (ityp \<rho> env W)) \<turnstile> map (\<lambda>U. cterm (tsubst \<rho> (foldr fun_type Ts U))) Us ! i :
          trty (tsubst \<rho> (foldr fun_type Ts (Us ! i))))"
      by (simp add: cterm_props)
  next
    fix W1 \<sigma>1 xs
    assume "pcinv alg ar A W1 \<rho> (tau (ityp \<rho> env W)) \<sigma>1 env1 []" "agree (maxidx env) (env_sol (instE \<rho> env) (ityp \<rho> env W)) \<sigma>1"
      "agreeV (maxidx env) W W1" "maxidx env \<le> maxidx env1" "pextends env1 env"
      "tenv env1 = tenv env" "tyenv env1 = tyenv env"
      "length xs = length Us" "distinct xs" "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env1"
      "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
      "\<forall>i<length Us. \<sigma>1 (code (AVar (xs ! i))) = map (\<lambda>U. cterm (tsubst \<rho> (foldr fun_type Ts U))) Us ! i \<and>
        W1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    note a = this
    show ?thesis
      by (rule that[OF pinv_psext[OF pi pcinvD(1)[OF a(1)] a(5,3,4)] a(3-11)]) (use a(12) in blast)
  qed simp
qed

lemma genvar_pinv:
  assumes pi: "pinv alg ar A W env dps" and G: "genvar a env T = (env1, G)"
    and tw: "tyw ar (tyenv env) A T"
  shows "pinv alg ar A (W((a, maxidx env + 1) := T)) env1 dps" "agreeV (maxidx env) W (W((a, maxidx env + 1) := T))"
    "maxidx env1 = maxidx env + 1" "G = Var (a, maxidx env + 1) T" "pextends env1 env"
    "tenv env1 = tenv env" "tyenv env1 = tyenv env"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  note gp = genvar_pextend[OF pinv_pcinv_sol[OF pi g] G tw, of "cterm (tsubst \<rho> T)",
      OF cterm_props[THEN conjunct1] cterm_props[THEN conjunct2, THEN spec]]
  show "pinv alg ar A (W((a, maxidx env + 1) := T)) env1 dps"
    by (rule pinv_psext[OF pi pcinvD(1)[OF gp(1)] gp(6,3)]) (simp add: gp(4))
  show "agreeV (maxidx env) W (W((a, maxidx env + 1) := T))" "maxidx env1 = maxidx env + 1"
    "G = Var (a, maxidx env + 1) T" "pextends env1 env" "tenv env1 = tenv env" "tyenv env1 = tyenv env"
    by (rule gp)+
qed
end


subsection \<open>Copies: projections\<close>

lemma fin_foldrW:
  assumes "\<And>x t. x \<in> set xs \<Longrightarrow> fin cfg t Q \<Longrightarrow> \<exists>r. okW (f x t) r \<and> fin cfg r Q" and "fin cfg b Q"
  shows "\<exists>r. okW (foldrW f xs b) r \<and> fin cfg r Q"
  using assms by (induction xs) fastforce+

text \<open>The projections of \<^const>\<open>matchfun\<close>, with all guesses, given the results of each:\<close>

definition proj_fin :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow>
    ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> nat \<Rightarrow> (elem \<Rightarrow> bool) \<Rightarrow> bool" where
  "proj_fin cfg vname rb targs u env dps base Ts head Us bary targ p Q \<longleftrightarrow> proj_total cfg env base bary p \<and>
    (\<forall>env0 Cs env' env'' args. gentvars p env = (env0, Cs) \<longrightarrow>
      okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> make_args vname Ts env' (Us @ Cs) = (env'', args) \<longrightarrow>
      cuok (SIMPL (cfg_alg cfg) env''
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
        (\<lambda>(env2, fr, ff). Q (El_C (list_comb head args) env2 (fr @ ff))))"

lemma projenv_fin:
  assumes pf: "proj_fin cfg vname rb targs u env dps base Ts head Us bary targ p Q" and t: "fin cfg tail Q"
  shows "\<exists>r. okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail) r \<and> fin cfg r Q"
proof -
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  let ?m = "proj_unify cfg base bary Cs env0"
  let ?r = "do {env' \<leftarrow> ?m; returnW (S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ tail)}"
  have pe: "projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail =
      handleW ?r (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)"
    by (simp add: projenv_def g)
  from pf g have "(\<exists>env'. okW ?m env') \<or> (\<exists>evs. ?m = Some (evs, UErr CANTUNIFY))"
    by (simp add: proj_fin_def proj_total_def)
  then show ?thesis
  proof
    assume "\<exists>env'. okW ?m env'"
    then obtain env' where e': "okW ?m env'" by blast
    let ?R = "S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ tail"
    have "okW ?r ?R" using e' by auto
    then have ok: "okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail) ?R"
      unfolding pe by (rule okW_handleW[THEN iffD2, OF disjI1])
    obtain env'' args where ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)"
      by (cases "make_args vname Ts env' (Us @ Cs)")
    have "fin cfg ?R Q" by (rule fin_Proj[OF ma _ t]) (use pf g e' ma in \<open>simp add: proj_fin_def\<close>)
    with ok show ?thesis by blast
  next
    assume "\<exists>evs. ?m = Some (evs, UErr CANTUNIFY)"
    then obtain evs where c: "?m = Some (evs, UErr CANTUNIFY)" by blast
    then have "?r = Some (evs, UErr CANTUNIFY)" by (simp add: bindW_def)
    then have "okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail) tail"
      unfolding pe by (auto simp: okW_handleW)
    with t show ?thesis by blast
  qed
qed

lemma pmatchfun_fin:
  assumes "\<forall>(bv, T, targ)\<in>set projs. \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_fin cfg vname rb targs u env dps base Ts bv Us bary targ p Q)"
    and imit: "fin cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) Q"
  shows "\<exists>sq. okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) sq \<and> fin cfg sq Q"
  using assms(1)
proof (induction projs)
  case Nil
  with imit show ?case by simp
next
  case (Cons pr projs)
  obtain bv T targ where pr: "pr = (bv, T, targ)" by (cases pr)
  from Cons.prems pr obtain Us bary where st: "ok (strip_type env T) (Us, bary)"
    and gs: "\<forall>p\<in>set (arity_guesses cfg bary). proj_fin cfg vname rb targs u env dps base Ts bv Us bary targ p Q"
    by auto
  from Cons.IH Cons.prems obtain tail where
    tl: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) tail" and ft: "fin cfg tail Q"
    by auto
  have "\<exists>r. okW (foldrW (projenv cfg vname rb targs u env dps base Ts bv (Us, bary) targ)
      (arity_guesses cfg bary) tail) r \<and> fin cfg r Q"
    by (rule fin_foldrW[OF _ ft]) (use gs projenv_fin in blast)
  then show ?case using tl st by (auto simp: pr)
qed

lemma strip_type_tnorm:
  assumes ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and T: "tcons (tyenv env) T"
    and st: "ok (strip_type env T) (Us, bary)"
  shows "tnorm (tyenv env) T = tnorm (tyenv env) (foldr fun_type Us bary)"
proof -
  let ?\<theta> = "tyenv env"
  have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
    by (simp add: arg_res_type)
  from strip_type_ptnorm[OF ac T this res_type_base] obtain Us' B' where
    s: "strip_type env T = return (Us', B')" "map (tnorm ?\<theta>) Us' = arg_types (tnorm ?\<theta> T)"
      "tnorm ?\<theta> B' = res_type (tnorm ?\<theta> T)"
    by blast
  from s(1) st have "Us' = Us" "B' = bary" by (simp_all add: return_def)
  with s(2,3) show ?thesis using arg_res_type[of "tnorm ?\<theta> T"] by (simp add: tnorm_foldr_fun)
qed

lemma pcpy_typed_mono:
  assumes "typed env1 W1 Bs u U" "swf_cp ar k u" "\<forall>T\<in>tys u. tyw ar (tyenv env1) A T" "below (maxidx env1) u"
    and pi: "pinv alg ar A W1 env1 []" "pinv alg ar A W2 env2 []" and pe: "pextends env2 env1"
    and ag: "agreeV (maxidx env1) W1 W2" and mx: "maxidx env1 \<le> maxidx env2"
  shows "typed env2 W2 Bs u U" "\<forall>T\<in>tys u. tyw ar (tyenv env2) A T" "below (maxidx env2) u"
proof -
  note p1 = pinvD[OF pi(1)] and p2 = pinvD[OF pi(2)]
  have ac: "tacyc (tyenv env2)" by (rule tinv_tacyc[OF p2(2)])
  have ext: "textends (tyenv env1) (tyenv env2)" using pe by (simp add: pextends_def)
  show "typed env2 W2 Bs u U" by (rule typed_psext[OF ac pe p1(6) p2(6) ag assms(4,1)])
  show "\<forall>T\<in>tys u. tyw ar (tyenv env2) A T" using assms(3) tyw_textends[OF ac ext] by blast
  show "below (maxidx env2) u" by (rule below_mono[OF assms(4) mx])
qed

context pmfin
begin

subsection \<open>Copies\<close>

text \<open>The context of a copy, the term to copy, and the results:\<close>

definition pcpre :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "pcpre W env dps rb targs Ts \<longleftrightarrow> pinv alg ar A W env dps \<and> sbinders ar rb \<and>
    (\<forall>T\<in>snd ` set rb. tyw ar (tyenv env) A T) \<and>
    (\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> psh t \<and> (\<forall>T\<in>tys t. tyw ar (tyenv env) A T)) \<and>
    list_all2 (typed env W (map snd rb)) targs Ts \<and> (\<forall>T\<in>set Ts. tyw ar (tyenv env) A T) \<and>
    vgood Fd Ft env \<and> (\<forall>dp\<in>set dps. pgood Fd Ft dp) \<and> ptok targs \<and> m0 \<le> maxidx env"

definition pupre :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "pupre W env rb u U \<longleftrightarrow> swf_tm ar rb u \<and> (\<forall>T\<in>tys u. tyw ar (tyenv env) A T) \<and>
    typed env W (map snd rb) u U \<and> tyw ar (tyenv env) A U \<and> below (maxidx env) u \<and> psh u"

definition pcres :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> indexname set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> indexname set \<Rightarrow> bool" where
  "pcres W env D W' env' dps' NV \<longleftrightarrow>
    ptsext alg ar A W env W' env' dps' D NV \<and> vgood Fd Ft env' \<and> (\<forall>dp\<in>set dps'. pgood Fd Ft dp)"

definition pcpy :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> indexname set \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "pcpy W' env' NV Ts u' U \<longleftrightarrow> typed env' W' (rev Ts) u' U \<and> swf_cp ar (length Ts) u' \<and>
    (\<forall>T\<in>tys u'. tyw ar (tyenv env') A T) \<and> below (maxidx env') u' \<and> vars u' \<subseteq> NV"

lemma pcpreD:
  assumes "pcpre W env dps rb targs Ts"
  shows "pinv alg ar A W env dps" "sbinders ar rb" "\<forall>T\<in>snd ` set rb. tyw ar (tyenv env) A T"
    "\<And>t. t \<in> set targs \<Longrightarrow> swf_tm ar rb t \<and> below (maxidx env) t \<and> psh t \<and> (\<forall>T\<in>tys t. tyw ar (tyenv env) A T)"
    "list_all2 (typed env W (map snd rb)) targs Ts" "\<forall>T\<in>set Ts. tyw ar (tyenv env) A T"
    "vgood Fd Ft env" "\<And>dp. dp \<in> set dps \<Longrightarrow> pgood Fd Ft dp" "ptok targs" "m0 \<le> maxidx env"
  using assms by (auto simp: pcpre_def)

lemma pupreD:
  assumes "pupre W env rb u U"
  shows "swf_tm ar rb u" "\<forall>T\<in>tys u. tyw ar (tyenv env) A T" "typed env W (map snd rb) u U"
    "tyw ar (tyenv env) A U" "below (maxidx env) u" "psh u"
  using assms by (auto simp: pupre_def)

lemma pcres_trans:
  assumes "pcres W env D W1 env1 dps1 NV1" "pcres W1 env1 D1 W2 env2 dps2 NV2" "fresh_env env"
    "D1 \<subseteq> vreach env D \<union> NV1"
  shows "pcres W env D W2 env2 dps2 (NV1 \<union> NV2)"
  using assms ptsext_trans[of alg ar A W env W1 env1 dps1 D NV1 W2 env2 dps2 D1 NV2] by (simp add: pcres_def)

lemma pcres_mono: "pcres W env D W' env' dps' NV \<Longrightarrow> D \<subseteq> vreach env D' \<Longrightarrow> pcres W env D' W' env' dps' NV"
  by (auto simp: pcres_def intro: ptsext_mono)

lemma pcpy_mono:
  assumes "pcpy W1 env1 NV1 Ts u U" "pinv alg ar A W1 env1 []" "pinv alg ar A W2 env2 []" "pextends env2 env1"
    "agreeV (maxidx env1) W1 W2" "maxidx env1 \<le> maxidx env2" "NV1 \<subseteq> NV"
  shows "pcpy W2 env2 NV Ts u U"
proof -
  from assms(1) have c: "typed env1 W1 (rev Ts) u U" "swf_cp ar (length Ts) u"
    "\<forall>T\<in>tys u. tyw ar (tyenv env1) A T" "below (maxidx env1) u" "vars u \<subseteq> NV1"
    by (simp_all add: pcpy_def)
  note m = pcpy_typed_mono[OF c(1-4) assms(2-6)]
  show ?thesis using m c(2,5) assms(7) by (auto simp: pcpy_def)
qed

lemma pfresh_iff: "x \<in> Fd \<union> Ft \<longleftrightarrow> m0 < snd x"
  using regime by auto

lemma psh_incr: "psh t \<Longrightarrow> psh (incr_boundvars 1 t)"
  by (simp add: psh_def incr_boundvars_def vars_incr_bv)

lemma ptok_incr: "ptok targs \<Longrightarrow> ptok (map (incr_boundvars 1) targs @ [Bound 0])"
  by (auto simp: ptok_def incr_boundvars_def)

end

context pmfin
begin

text \<open>A projection with a guess: the simplification of the projection pair yields a copy.\<close>

lemma pproj_res:
  assumes cp: "pcpre W env dps rb targs Ts" and up: "pupre W env rb u U"
    and hu: "is_rigid (head_of u)" and nA: "\<not> is_Abs u"
    and Ts': "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts" "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T"
    and j: "0 \<le> j" "nat_of_integer j < length targs"
    and T: "T = Ts' ! (length targs - 1 - nat_of_integer j)"
    and targ: "targ = targs ! (length targs - 1 - nat_of_integer j)"
    and st: "ok (strip_type env T) (Us, bary)"
    and bU: "tnorm (tyenv env) base = tnorm (tyenv env) U" and twb: "tyw ar (tyenv env) A base"
    and g: "gentvars p env = (e0, Cs)" and pu: "okW (proj_unify cfg base bary Cs e0) env'"
    and ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)"
  shows "cuok (SIMPL alg env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
    (\<lambda>(env2, fr, ff). \<exists>W' NV. pcres W env (vars u \<union> \<Union> (vars ` set targs) \<union> vdps dps) W' env2 (fr @ ff) NV \<and>
      pcpy W' env2 NV Ts (list_comb (Bound j) args) U)"
proof -
  let ?\<theta> = "tyenv env"
  note c = pcpreD[OF cp] and uu = pupreD[OF up]
  note pi = pinvD[OF c(1)]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF c(5)] by simp
  have lTs': "length Ts' = length Ts" using arg_cong[OF Ts'(1), of length] by simp
  define k where "k = length targs - 1 - nat_of_integer j"
  have k: "k < length targs" using j by (simp add: k_def)
  have Tk: "T = Ts' ! k" and tk: "targ = targs ! k" using T targ by (simp_all add: k_def)
  have twT: "tyw ar ?\<theta> A T" using Ts'(2) k lTs lTs' by (simp add: Tk)
  have twUs: "\<forall>X\<in>set Us. tyw ar ?\<theta> A X" and twy: "tyw ar ?\<theta> A bary"
    using strip_type_tyw[OF st pi(2) twT] by simp_all
  have tT0: "tnorm ?\<theta> T = tnorm ?\<theta> (foldr fun_type Us bary)" by (rule strip_type_tnorm[OF ac tcU[OF twT] st])
  note pu1 = proj_unify_pinv[OF c(1) twb twy cfg g pu]
  let ?\<theta>' = "tyenv env'"
  have ac': "tacyc ?\<theta>'" by (rule tinv_tacyc[OF pinvD(2)[OF pu1(1)]])
  have ext0: "textends ?\<theta> ?\<theta>'" using pu1(3) by (simp add: pextends_def)
  define UC where "UC = Us @ Cs"
  have twUC: "\<forall>X\<in>set Ts' \<union> set UC. tyw ar ?\<theta>' A X"
    using Ts'(2) twUs pu1(5) tyw_textends[OF ac' ext0] by (auto simp: UC_def)
  have tT: "tnorm ?\<theta>' T = tnorm ?\<theta>' (foldr fun_type UC base)"
  proof -
    have "tnorm ?\<theta>' T = tnorm ?\<theta>' (tnorm ?\<theta> T)" by (simp add: tnorm_textends[OF ac' ext0])
    also have "\<dots> = tnorm ?\<theta>' (foldr fun_type Us bary)" by (simp add: tT0 tnorm_textends[OF ac' ext0])
    also have "\<dots> = foldr fun_type (map (tnorm ?\<theta>') Us) (tnorm ?\<theta>' bary)" by (simp add: tnorm_foldr_fun)
    also have "tnorm ?\<theta>' bary = tnorm ?\<theta>' (foldr fun_type Cs base)" by (rule pu1(6))
    finally show ?thesis by (simp add: tnorm_foldr_fun UC_def)
  qed
  obtain W1 xs where me: "pinv alg ar A W1 env'' dps" "agreeV (maxidx env') W W1" "maxidx env' \<le> maxidx env''"
    "pextends env'' env'" "tenv env'' = tenv env'" "tyenv env'' = tyenv env'"
    "length xs = length UC" "distinct xs" "\<forall>x\<in>set xs. maxidx env' < snd x \<and> snd x \<le> maxidx env''"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts' U)) 0 (length Ts')) xs UC"
    "\<forall>i<length UC. W1 (xs ! i) = foldr fun_type Ts' (UC ! i)"
    by (rule make_args_pinv[OF pu1(1) ma[folded UC_def] twUC])
  have la: "length args = length UC" using me(7,10) by simp
  have ai: "args ! i = combound (Var (xs ! i) (foldr fun_type Ts' (UC ! i))) 0 (length Ts')"
    if "i < length UC" for i using me(7,10) that by simp
  have hai: "head_of (args ! i) = Var (xs ! i) (foldr fun_type Ts' (UC ! i))" if "i < length UC" for i
    using ai[OF that] by (simp add: head_of_combound)
  define Ls where "Ls = map (\<lambda>arg. list_comb (head_of arg) targs) args"
  define dp where "dp = (rb, list_comb targ Ls, u)"
  have lLs: "length Ls = length UC" using la by (simp add: Ls_def)
  have Lsi: "Ls ! i = list_comb (Var (xs ! i) (foldr fun_type Ts' (UC ! i))) targs" if "i < length UC" for i
    using hai[OF that] la that by (simp add: Ls_def)
  note pi'' = pinvD[OF me(1)]
  let ?\<theta>'' = "tyenv env''"
  have ac'': "tacyc ?\<theta>''" by (rule tinv_tacyc[OF pi''(2)])
  have pe'': "pextends env'' env" using me(4) pu1(3) by (rule pextends_trans)
  have ext'': "textends ?\<theta> ?\<theta>''" using pe'' by (simp add: pextends_def)
  have mx: "maxidx env \<le> maxidx env''" using pu1(4) me(3) by simp
  have agV: "agreeV (maxidx env) W W1" using agreeV_mono[OF me(2) pu1(4)] .
  have tn'': "tnorm ?\<theta>'' (tnorm ?\<theta> X) = tnorm ?\<theta>'' X" for X by (rule tnorm_textends[OF ac'' ext''])
  have bt: "\<forall>t\<in>set targs. below (maxidx env) t" using c(4) by blast
  have tg1: "list_all2 (typed env'' W1 (map snd rb)) targs Ts"
    by (rule list_all2_typed_psext[OF ac'' pe'' pi(6) pi''(6) agV bt c(5)])
  have mTs: "map (tnorm ?\<theta>'') Ts' = map (tnorm ?\<theta>'') Ts"
    using arg_cong[OF Ts'(1), of "map (tnorm ?\<theta>'')"] by (simp add: comp_def tn'')
  have tg'': "list_all2 (typed env'' W1 (map snd rb)) targs Ts'" by (rule list_all2_typed_tnorm[OF tg1 mTs])
  have tctxi: "tctx env'' W1 (xs ! i) = tnorm ?\<theta>'' (foldr fun_type Ts' (UC ! i))" if "i < length UC" for i
    using wcons_tctx[OF pi''(6)] me(11) that by simp
  have tyLs: "list_all2 (typed env'' W1 (map snd rb)) Ls UC"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length Ls = length UC" by (rule lLs)
    fix i assume "i < length Ls"
    then have i: "i < length UC" using lLs by simp
    show "typed env'' W1 (map snd rb) (Ls ! i) (UC ! i)"
      using typed_Var_list_comb[OF tctxi[OF i] tg''] Lsi[OF i] by simp
  qed
  have tTk: "tnorm ?\<theta>'' T = tnorm ?\<theta>'' (Ts ! k)"
    using arg_cong[OF mTs, of "\<lambda>xs. xs ! k"] k lTs lTs' by (simp add: Tk)
  have tUC: "tnorm ?\<theta>'' (foldr fun_type UC base) = tnorm ?\<theta>'' (Ts ! k)"
    using tT tTk me(6) by simp
  have btarg: "below (maxidx env) targ" using bt k by (simp add: tk)
  have tytarg: "typed env'' W1 (map snd rb) targ (foldr fun_type UC base)"
  proof -
    have "typed env W (map snd rb) targ (Ts ! k)" using c(5) k by (simp add: list_all2_conv_all_nth tk)
    then have "typed env'' W1 (map snd rb) targ (Ts ! k)" by (rule typed_psext[OF ac'' pe'' pi(6) pi''(6) agV btarg])
    then show ?thesis by (rule typed_tnorm_cong[OF _ refl tUC])
  qed
  have tyl: "typed env'' W1 (map snd rb) (list_comb targ Ls) base" by (rule typed_list_comb[OF tytarg tyLs])
  have tbU: "tnorm ?\<theta>'' base = tnorm ?\<theta>'' U" using arg_cong[OF bU, of "tnorm ?\<theta>''"] by (simp add: tn'')
  have tyu'': "typed env'' W1 (map snd rb) u base"
    using typed_psext[OF ac'' pe'' pi(6) pi''(6) agV uu(5,3)] by (rule typed_tnorm_cong[OF _ refl tbU])
  have twG: "tyw ar ?\<theta>'' A (foldr fun_type Ts' (UC ! i))" if "i < length UC" for i
    using twUC that me(6) by (simp add: tyw_foldr_fun)
  have bxs: "maxidx env < snd (xs ! i) \<and> snd (xs ! i) \<le> maxidx env''" if "i < length UC" for i
  proof -
    have "xs ! i \<in> set xs" using me(7) that by simp
    with me(9) pu1(4) show ?thesis by force
  qed
  text \<open>The projection pair keeps the invariant\<close>
  have pid: "pinv alg ar A W1 env'' (dp # dps)"
  proof -
    have wLs: "swf_tm ar rb t" if "t \<in> set Ls" for t
    proof -
      from that obtain i where i: "i < length UC" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      have "swf_tm ar rb (Var (xs ! i) (foldr fun_type Ts' (UC ! i)))" using twG[OF i(1)] by (simp add: swf_tm_def tyw_def)
      then show ?thesis using Lsi[OF i(1)] i(2) c(4) by (simp add: swf_tm_list_comb)
    qed
    have tLs: "tyw ar ?\<theta>'' A X" if "t \<in> set Ls" "X \<in> tys t" for t X
    proof -
      from that obtain i where i: "i < length UC" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      then show ?thesis using that(2) Lsi[OF i(1)] twG[OF i(1)] c(4) tyw_textends[OF ac'' ext'']
        by (auto simp: tys_list_comb)
    qed
    have bLs: "below (maxidx env'') t" if "t \<in> set Ls" for t
    proof -
      from that obtain i where i: "i < length UC" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      have "\<forall>t\<in>set targs. below (maxidx env'') t" using bt mx by (auto intro: below_mono)
      moreover have "below (maxidx env'') (Var (xs ! i) (foldr fun_type Ts' (UC ! i)))"
        using bxs[OF i(1)] by (simp add: below_def)
      ultimately show ?thesis using Lsi[OF i(1)] i(2) by (simp add: below_list_comb)
    qed
    have tgm: "targ \<in> set targs" using k by (simp add: tk)
    have "swf_dp ar dp" using c(2) uu(1) c(4) tgm wLs by (simp add: dp_def swf_dp_def swf_tm_list_comb)
    moreover have "\<forall>X\<in>dtys dp. tyw ar ?\<theta>'' A X"
      using c(3) uu(2) c(4) tgm tLs tyw_textends[OF ac'' ext''] by (auto simp: dp_def tys_list_comb)
    moreover have "ptyped env'' W1 dp" using tyl tyu'' by (auto simp: dp_def)
    moreover have "dp_below (maxidx env'') dp"
      using btarg uu(5) bLs mx by (auto simp: dp_def dp_below_def below_list_comb intro: below_mono)
    ultimately show ?thesis using me(1) by (simp add: pinv_def)
  qed
  text \<open>The shape of the projection pair\<close>
  have pg: "pgood Fd Ft dp"
  proof -
    have dL: "dead Fd L" if "L \<in> set Ls" for L
    proof -
      from that obtain i where i: "i < length UC" "L = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      have "xs ! i \<in> Fd \<Longrightarrow> \<exists>t\<in>set targs. \<not> is_Bound t" using c(9) by (auto simp: ptok_def)
      with Lsi[OF i(1)] i(2) c(4) show ?thesis by (auto simp: dd_list_comb psh_def)
    qed
    have shtarg: "psh targ" using c(4) k by (simp add: tk)
    have d: "dead Fd (list_comb targ Ls)" "dead Fd u"
      using dL shtarg uu(6) by (auto simp: dd_list_comb psh_def intro: dd_True)
    have "gs Ft (list_comb targ Ls) \<and> gs Ft u \<or> rrs Ft (list_comb targ Ls) \<and> rrs Ft u"
    proof (cases "Ft = {}")
      case True
      then show ?thesis by (simp add: gs_free)
    next
      case False
      then have "\<forall>t\<in>set targs. is_Bound t" using c(9) by (simp add: ptok_def)
      then have "is_Bound targ" using k by (simp add: tk)
      then have r1: "rrs Ft targ" by (cases targ) auto
      have gL: "gs Ft L" if "L \<in> set Ls" for L
      proof -
        from that obtain i where i: "i < length UC" "L = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
        have "hok Ft L" using Lsi[OF i(1)] i(2) c(4) by (auto simp: hok_list_comb psh_def)
        then show ?thesis by (rule hok_gs)
      qed
      have "u = list_comb (head_of u) (snd (strip_comb u))" by (rule head_of_list_comb)
      moreover have "rrs Ft (head_of u)" using hu by (auto simp: is_rigid_def)
      moreover have "\<forall>t\<in>set (snd (strip_comb u)). gs Ft t"
      proof
        fix t assume "t \<in> set (snd (strip_comb u))"
        then have "vars t \<subseteq> vars u" using vars_list_comb[of "head_of u" "snd (strip_comb u)"]
          head_of_list_comb[of u] by auto
        with uu(6) show "gs Ft t" by (auto simp: psh_def intro: gs_free)
      qed
      ultimately have "rrs Ft u" by (metis rrs_list_comb)
      with r1 gL show ?thesis by (simp add: rrs_list_comb)
    qed
    with d show ?thesis by (simp add: pgood_def dp_def)
  qed
  have vg1: "vgood Fd Ft env''" using c(7) vgood_tenv[of env'' env Fd Ft] me(5) pu1(2) by simp
  have pgs: "\<forall>dp\<in>set (dp # dps). pgood Fd Ft dp" using pg c(8) by simp
  text \<open>The new variables\<close>
  define NV where "NV = set xs"
  define D where "D = vars u \<union> \<Union> (vars ` set targs) \<union> vdps dps"
  have NVb: "maxidx env < snd y \<and> snd y \<le> maxidx env''" if "y \<in> NV" for y
    using that bxs me(7) by (auto simp: NV_def in_set_conv_nth)
  have vai: "vars (args ! i) = {xs ! i}" if "i < length UC" for i using ai[OF that] by simp
  have vargs: "\<Union> (vars ` set args) = NV"
  proof
    show "\<Union> (vars ` set args) \<subseteq> NV" using vai la me(7) by (force simp: NV_def in_set_conv_nth)
    show "NV \<subseteq> \<Union> (vars ` set args)"
    proof
      fix y assume "y \<in> NV"
      then obtain i where i: "i < length UC" "y = xs ! i" using me(7) by (auto simp: NV_def in_set_conv_nth)
      then have "y \<in> vars (args ! i)" using vai by simp
      with i(1) la show "y \<in> \<Union> (vars ` set args)" by (auto dest: nth_mem[of i args])
    qed
  qed
  have vLs: "\<Union> (vars ` set Ls) \<subseteq> NV \<union> \<Union> (vars ` set targs)"
  proof
    fix y assume "y \<in> \<Union> (vars ` set Ls)"
    then obtain i where i: "i < length UC" "y \<in> vars (Ls ! i)" using lLs by (auto simp: in_set_conv_nth)
    then show "y \<in> NV \<union> \<Union> (vars ` set targs)" using Lsi[OF i(1)] me(7) by (auto simp: vars_list_comb NV_def)
  qed
  have tgD: "vars targ \<subseteq> D" using k by (auto simp: D_def tk)
  have vdp: "vdps (dp # dps) \<subseteq> D \<union> NV"
    using vLs tgD by (auto simp: dp_def vars_list_comb D_def)
  have rr: "vreach env'' = vreach env" using vreach_tenv[of env'' env] me(5) pu1(2) by simp
  have nvr: "vreach env NV = NV" using vreach_new[OF ei(6)] NVb by blast
  have rDNV: "vreach env (X \<union> D \<union> NV) = vreach env (X \<union> D) \<union> NV" for X using nvr by (simp add: vreach_Un)
  have cpy: "pcpy W1 env'' NV Ts (list_comb (Bound j) args) U"
  proof -
    have mrTs: "map (tnorm ?\<theta>'') (rev Ts) = map (tnorm ?\<theta>'') (rev Ts')" using mTs by (simp add: rev_map[symmetric])
    have tyBj: "typed env'' W1 (rev Ts) (Bound j) (foldr fun_type UC U)"
    proof -
      have "rev Ts ! nat_of_integer j = Ts ! k" using j lTs by (simp add: rev_nth k_def)
      moreover have "tnorm ?\<theta>'' (foldr fun_type UC U) = tnorm ?\<theta>'' (Ts ! k)"
        using tUC tbU by (simp add: tnorm_foldr_fun)
      ultimately show ?thesis using j lTs by (simp add: typed_def has_type_Bound_iff)
    qed
    have tyai: "list_all2 (typed env'' W1 (rev Ts)) args UC"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length args = length UC" by (rule la)
      fix i assume "i < length args"
      then have i: "i < length UC" using la by simp
      have "typed env'' W1 (rev Ts') (args ! i) (UC ! i)"
        using typed_combound_Var[OF tctxi[OF i]] ai[OF i] by simp
      then show "typed env'' W1 (rev Ts) (args ! i) (UC ! i)" by (rule typed_tnorm_cong[OF _ mrTs refl])
    qed
    have ty: "typed env'' W1 (rev Ts) (list_comb (Bound j) args) U" by (rule typed_list_comb[OF tyBj tyai])
    have "\<forall>a\<in>set args. swf_cp ar (length Ts') a"
      by (rule make_args_swf_cp[OF ma[folded UC_def]]) (use twUC in \<open>auto simp: tyw_def\<close>)
    moreover have "swf_cp ar (length Ts) (Bound j)" using j lTs by (simp add: swf_cp_def)
    ultimately have w: "swf_cp ar (length Ts) (list_comb (Bound j) args)" using lTs' by (simp add: swf_cp_list_comb)
    have tw: "\<forall>X\<in>tys (list_comb (Bound j) args). tyw ar ?\<theta>'' A X"
      using twG ai la by (auto simp: tys_list_comb in_set_conv_nth)
    have "\<forall>a\<in>set args. below (maxidx env'') a"
    proof
      fix a assume "a \<in> set args"
      then obtain i where i: "i < length UC" "a = args ! i" using la by (auto simp: in_set_conv_nth)
      then show "below (maxidx env'') a" using ai[OF i(1)] bxs[OF i(1)] by (simp add: below_def)
    qed
    moreover have "below (maxidx env'') (Bound j)" by (simp add: below_def)
    ultimately have "below (maxidx env'') (list_comb (Bound j) args)" using below_list_comb by blast
    with ty w tw vargs show ?thesis by (simp add: pcpy_def vars_list_comb)
  qed
  have "cuok (SIMPL alg env'' (dp # dps)) (\<lambda>(env2, f1, f2).
      \<exists>W' NV. pcres W env D W' env2 (f1 @ f2) NV \<and> pcpy W' env2 NV Ts (list_comb (Bound j) args) U)"
  proof (rule cuok_mono_ok[OF SIMPL_pterm[OF finA pid]])
    fix st assume ok: "okW (SIMPL alg env'' (dp # dps)) st" and sr: "ptsimpl_res alg ar A W1 (dp # dps) env'' st"
    obtain env2 a b where st: "st = (env2, a, b)" by (cases st)
    from sr st have sr': "pinv alg ar A W1 env2 (a @ b)" "pextends env2 env''" "maxidx env'' \<le> maxidx env2"
      by (simp_all add: ptsimpl_res_def)
    from SIMPL_good'[OF ok[unfolded st] vg1 pgs] have sg: "vgood Fd Ft env2" "\<forall>dp\<in>set (a @ b). pgood Fd Ft dp"
      by (auto simp: sgood_def)
    from SIMPL_vreach'[OF ok[unfolded st]] have vr: "vreach env2 X \<subseteq> vreach env'' (X \<union> vdps (dp # dps))"
      "vdps (a @ b) \<subseteq> vreach env'' (vdps (dp # dps))" for X
      by (auto simp: vsr_def)
    have tx: "ptsext alg ar A W env W1 env2 (a @ b) D NV"
      unfolding ptsext_def
    proof (intro conjI allI ballI sr'(1) agV)
      show "maxidx env \<le> maxidx env2" using mx sr'(3) by simp
      show "pextends env2 env" using sr'(2) pe'' by (rule pextends_trans)
      show "finite NV" by (simp add: NV_def)
      show "maxidx env < snd y" if "y \<in> NV" for y using NVb that by blast
      show "snd y \<le> maxidx env2" if "y \<in> NV" for y using NVb[OF that] sr'(3) by simp
      show "vreach env2 X \<subseteq> vreach env (X \<union> D) \<union> NV" for X
      proof -
        have "vreach env2 X \<subseteq> vreach env (X \<union> vdps (dp # dps))" using vr(1)[of X] rr by simp
        also have "\<dots> \<subseteq> vreach env (X \<union> D \<union> NV)" using vdp by (intro vreach_subset) blast
        finally show ?thesis using rDNV by simp
      qed
      show "vdps (a @ b) \<subseteq> vreach env D \<union> NV"
      proof -
        have "vdps (a @ b) \<subseteq> vreach env (vdps (dp # dps))" using vr(2) rr by simp
        also have "\<dots> \<subseteq> vreach env ({} \<union> D \<union> NV)" using vdp by (intro vreach_subset) blast
        finally show ?thesis using rDNV[of "{}"] by simp
      qed
    qed
    have "pcres W env D W1 env2 (a @ b) NV" using tx sg by (simp add: pcres_def)
    moreover have "pcpy W1 env2 NV Ts (list_comb (Bound j) args) U"
      by (rule pcpy_mono[OF cpy pinv_Nil[OF me(1)] pinv_Nil[OF sr'(1)] sr'(2) _ sr'(3) subset_refl])
        (simp add: agreeV_def)
    ultimately show "case st of (env2, f1, f2) \<Rightarrow>
        \<exists>W' NV. pcres W env D W' env2 (f1 @ f2) NV \<and> pcpy W' env2 NV Ts (list_comb (Bound j) args) U"
      using st by auto
  qed
  then show ?thesis by (simp add: D_def dp_def Ls_def)
qed

end


context pmfin
begin

text \<open>The elements of the sequences of copies of a term and of argument lists:\<close>

definition PEC :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> indexname set \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> elem \<Rightarrow> bool" where
  "PEC W env D Ts U x \<longleftrightarrow>
    (\<exists>u' env' dps' W' NV. x = El_C u' env' dps' \<and> pcres W env D W' env' dps' NV \<and> pcpy W' env' NV Ts u' U)"

definition PED :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> indexname set \<Rightarrow> ptyp list \<Rightarrow> ptyp list \<Rightarrow> elem \<Rightarrow> bool" where
  "PED W env D Ts As x \<longleftrightarrow>
    (\<exists>us env' dps' W' NV. x = El_D us env' dps' \<and> pcres W env D W' env' dps' NV \<and>
      list_all2 (\<lambda>u' A. pcpy W' env' NV Ts u' A) us As)"

text \<open>The results of a state extension apply in the extended state:\<close>

lemma pcpre_ext:
  assumes cp: "pcpre W env dps rb targs Ts" and cr: "pcres W env D W' env' dps' NV"
  shows "pcpre W' env' dps' rb targs Ts"
proof -
  note c = pcpreD[OF cp] and t = ptsextD[OF conjunct1[OF cr[unfolded pcres_def]]]
  note pi = pinvD[OF c(1)] and pi' = pinvD[OF t(1)]
  have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
  have ext: "textends (tyenv env) (tyenv env')" using t(4) by (simp add: pextends_def)
  have bt: "\<forall>t\<in>set targs. below (maxidx env) t" using c(4) by blast
  have "list_all2 (typed env' W' (map snd rb)) targs Ts"
    by (rule list_all2_typed_psext[OF ac' t(4) pi(6) pi'(6) t(2) bt c(5)])
  moreover have "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env') t \<and> psh t \<and> (\<forall>T\<in>tys t. tyw ar (tyenv env') A T)"
    using c(4) below_mono[OF _ t(3)] tyw_textends[OF ac' ext] by blast
  moreover have "\<forall>T\<in>snd ` set rb. tyw ar (tyenv env') A T" "\<forall>T\<in>set Ts. tyw ar (tyenv env') A T"
    using c(3,6) tyw_textends[OF ac' ext] by blast+
  ultimately show ?thesis using c(2,9,10) t(1,3) cr by (auto simp: pcpre_def pcres_def)
qed

lemma pupre_ext:
  assumes "pupre W env rb a T" "pinv alg ar A W env dps0" "pcres W env D W' env' dps' NV"
  shows "pupre W' env' rb a T"
proof -
  note u = pupreD[OF assms(1)] and t = ptsextD[OF conjunct1[OF assms(3)[unfolded pcres_def]]]
  note pi = pinvD[OF assms(2)] and pi' = pinvD[OF t(1)]
  have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
  have ext: "textends (tyenv env) (tyenv env')" using t(4) by (simp add: pextends_def)
  have "typed env' W' (map snd rb) a T" by (rule typed_psext[OF ac' t(4) pi(6) pi'(6) t(2) u(5,3)])
  then show ?thesis
    using u below_mono[OF u(5) t(3)] tyw_textends[OF ac' ext] by (simp add: pupre_def)
qed

lemma poldin_ext:
  assumes cr: "pcres W env D W' env' dps' NV" and o: "poldin env (X \<union> D)" and fr: "fresh_env env"
    and m: "m0 \<le> maxidx env"
  shows "poldin env' (X \<union> vdps dps')"
  unfolding poldin_def
proof (intro ballI impI)
  note t = ptsextD[OF conjunct1[OF cr[unfolded pcres_def]]]
  fix y assume y: "y \<in> vreach env' (X \<union> vdps dps')" "snd y \<le> m0"
  have nv: "y \<notin> NV" using t(6)[of y] y(2) m by auto
  have rn: "vreach env NV = NV" using vreach_new[OF fr] t(6) by blast
  from t(7) y(1) nv have "y \<in> vreach env (X \<union> vdps dps' \<union> D)" by blast
  moreover have "vreach env (vdps dps') \<subseteq> vreach env D \<union> NV"
    using vreach_mono[of "vdps dps'" env "D \<union> NV"] t(8) vreach_incl[of D env] rn
    by (auto simp: vreach_Un)
  ultimately have "y \<in> vreach env (X \<union> D)" using nv vreach_mono[of D env "X \<union> D"] vreach_incl[of "X \<union> D" env]
    by (auto simp: vreach_Un)
  with o y(2) show "y \<in> S0" by (auto simp: poldin_def)
qed

end

context pmfin
begin

text \<open>The measure of a copy: the number of unbound old variables, and the measure of the term.\<close>

abbreviation pmlex :: "((nat \<times> nat) \<times> (nat \<times> nat)) set" where
  "pmlex \<equiv> less_than <*lex*> less_than"

text \<open>The copies of the arguments of an imitation, given the copies of each argument:\<close>

lemma pcopyargs_fin:
  assumes CC: "\<And>W' env' dps' a T us. ((pmu1 env', rsz alg ar env' W' a), (c, N)) \<in> pmlex \<Longrightarrow>
      pcpre W' env' dps' rb targs Ts \<Longrightarrow> pupre W' env' rb a T \<Longrightarrow>
      poldin env' (vars a \<union> \<Union> (vars ` set targs) \<union> vdps dps') \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname rb targs a us env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>u' env'' dps'' W'' NV. x = El_D (u' # us) env'' dps'' \<and>
          pcres W' env' (vars a \<union> \<Union> (vars ` set targs) \<union> vdps dps') W'' env'' dps'' NV \<and>
          pcpy W'' env'' NV Ts u' T)"
    and cp: "pcpre W env dps rb targs Ts" and mu: "pmu1 env = c"
    and args: "list_all2 (\<lambda>a T. pupre W env rb a T \<and> rsz alg ar env W a < N) uargs As"
    and o: "poldin env (\<Union> (vars ` set uargs) \<union> \<Union> (vars ` set targs) \<union> vdps dps)"
  shows "fin cfg (copyargs vname rb targs env dps uargs)
    (PED W env (\<Union> (vars ` set uargs) \<union> \<Union> (vars ` set targs) \<union> vdps dps) Ts As)"
  using args o
proof (induction uargs As rule: list_all2_induct)
  case Nil
  note c = pcpreD[OF cp]
  have "pcres W env (\<Union> (vars ` set targs) \<union> vdps dps) W env dps {}"
    using ptsext_refl[OF c(1)] c(7,8) by (auto simp: pcres_def)
  then show ?case by (auto simp: PED_def intro!: fin_Single)
next
  case (Cons a uargs T As)
  note c = pcpreD[OF cp]
  note pi = pinvD[OF c(1)]
  have fr: "fresh_env env" by (rule penv_invD(6)[OF pi(1)])
  define D where "D = \<Union> (vars ` set (a # uargs)) \<union> \<Union> (vars ` set targs) \<union> vdps dps"
  define D' where "D' = \<Union> (vars ` set uargs) \<union> \<Union> (vars ` set targs) \<union> vdps dps"
  have DD': "D' \<subseteq> D" by (auto simp: D_def D'_def)
  have oD: "poldin env D" using Cons.prems by (simp add: D_def)
  have "poldin env D'" by (rule poldin_mono[OF oD]) (use DD' vreach_incl[of D env] in blast)
  then have IH: "fin cfg (copyargs vname rb targs env dps uargs) (PED W env D' Ts As)"
    using Cons.IH unfolding D'_def by blast
  have ua: "pupre W env rb a T" and ia: "rsz alg ar env W a < N" using Cons.hyps(1) by simp_all
  note u = pupreD[OF ua]
  have step: "\<exists>cs. okW (copycons cfg vname rb targs a us env' dps') cs \<and>
      fin cfg cs (PED W env D Ts (T # As))"
    if x: "PED W env D' Ts As (El_D us env' dps')" for us env' dps'
  proof -
    from x obtain W' NV where cr': "pcres W env D' W' env' dps' NV"
      and cps: "list_all2 (\<lambda>u' A. pcpy W' env' NV Ts u' A) us As"
      by (auto simp: PED_def)
    have cr: "pcres W env D W' env' dps' NV" by (rule pcres_mono[OF cr']) (use DD' vreach_incl[of D env] in blast)
    note t = ptsextD[OF conjunct1[OF cr[unfolded pcres_def]]]
    have vg': "vgood Fd Ft env'" using cr by (simp add: pcres_def)
    have cp': "pcpre W' env' dps' rb targs Ts" by (rule pcpre_ext[OF cp cr])
    have ua': "pupre W' env' rb a T" by (rule pupre_ext[OF ua c(1) cr])
    have Da: "vars a \<union> \<Union> (vars ` set targs) \<union> D = D" by (auto simp: D_def)
    have oa': "poldin env' (vars a \<union> \<Union> (vars ` set targs) \<union> vdps dps')"
      using poldin_ext[OF cr _ fr c(10), of "vars a \<union> \<Union> (vars ` set targs)"] oD Da by simp
    have lex: "((pmu1 env', rsz alg ar env' W' a), (c, N)) \<in> pmlex"
    proof (cases "pmu1 env' < pmu1 env")
      case True
      with mu show ?thesis by simp
    next
      case False
      with pmu1_mono[OF pextendsD(1)[OF t(4)]] have eq: "pmu1 env' = pmu1 env" by simp
      have "poldin env (vars a)" by (rule poldin_mono[OF oD]) (auto simp: D_def intro: vreach_incl[THEN subsetD])
      moreover have "\<forall>U\<in>set (map snd rb) \<union> tys a. tyw ar (tyenv env) A U" using c(3) u(2) by auto
      ultimately have "rsz alg ar env' W' a = rsz alg ar env W a"
        using rsz_stable[OF c(1,7) conjunct1[OF cr[unfolded pcres_def]] vg' _ u(3) _ u(5,6) eq] by blast
      with ia eq mu show ?thesis by simp
    qed
    from CC[OF lex cp' ua' oa'] obtain cs where cc: "okW (copycons cfg vname rb targs a us env' dps') cs"
      and fc: "fin cfg cs (\<lambda>x. \<exists>u' env'' dps'' W'' NV. x = El_D (u' # us) env'' dps'' \<and>
          pcres W' env' (vars a \<union> \<Union> (vars ` set targs) \<union> vdps dps') W'' env'' dps'' NV \<and>
          pcpy W'' env'' NV Ts u' T)"
      by blast
    have "fin cfg cs (PED W env D Ts (T # As))"
    proof (rule fin_mono[OF fc])
      fix x assume "\<exists>u' env'' dps'' W'' NV'. x = El_D (u' # us) env'' dps'' \<and>
          pcres W' env' (vars a \<union> \<Union> (vars ` set targs) \<union> vdps dps') W'' env'' dps'' NV' \<and>
          pcpy W'' env'' NV' Ts u' T"
      then obtain u' env'' dps'' W'' NV' where xe: "x = El_D (u' # us) env'' dps''"
        and cr2: "pcres W' env' (vars a \<union> \<Union> (vars ` set targs) \<union> vdps dps') W'' env'' dps'' NV'"
        and cu: "pcpy W'' env'' NV' Ts u' T"
        by blast
      note t2 = ptsextD[OF conjunct1[OF cr2[unfolded pcres_def]]]
      have "vars a \<union> \<Union> (vars ` set targs) \<union> vdps dps' \<subseteq> vreach env D \<union> NV"
        using t(8) vreach_incl[of D env] by (auto simp: D_def)
      from pcres_trans[OF cr cr2 fr this] have cr3: "pcres W env D W'' env'' dps'' (NV \<union> NV')" .
      have "pcpy W'' env'' (NV \<union> NV') Ts u' T" using cu by (auto simp: pcpy_def)
      moreover have "list_all2 (\<lambda>u' A. pcpy W'' env'' (NV \<union> NV') Ts u' A) us As"
        by (rule list_all2_mono[OF cps])
          (rule pcpy_mono[OF _ pinv_Nil[OF t(1)] pinv_Nil[OF t2(1)] t2(4,2,3)], auto)
      ultimately have "list_all2 (\<lambda>u' A. pcpy W'' env'' (NV \<union> NV') Ts u' A) (u' # us) (T # As)"
        by simp
      with xe cr3 show "PED W env D Ts (T # As) x" by (auto simp: PED_def)
    qed
    with cc show ?thesis by blast
  qed
  have "fin cfg (S_Maps vname rb targs a (copyargs vname rb targs env dps uargs)) (PED W env D Ts (T # As))"
  proof (rule fin_Maps)
    show "fin cfg (copyargs vname rb targs env dps uargs) (\<lambda>x. \<exists>us env' dps' cs. x = El_D us env' dps' \<and>
        okW (copycons cfg vname rb targs a us env' dps') cs \<and> fin cfg cs (PED W env D Ts (T # As)))"
      by (rule fin_mono[OF IH]) (use step in \<open>fastforce simp: PED_def\<close>)
  qed
  then show ?case by (simp add: D_def)
qed

end

lemma typed_tyw:
  assumes ti: "tinv ar n (tyenv env) A" and twB: "\<forall>X\<in>set Bs. tyw ar (tyenv env) A X"
    and twt: "\<forall>X\<in>tys t. tyw ar (tyenv env) A X" and ty: "typed env W Bs t T"
  obtains T' where "tyw ar (tyenv env) A T'" "tnorm (tyenv env) T' = tnorm (tyenv env) T"
proof -
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF ti] tinv_tcons_env[OF ti] by simp_all
  have "\<forall>U\<in>set Bs \<union> tys t. tcons (tyenv env) U" using twB twt tyw_tcons[OF ti] by blast
  from env_fastype_pterm[OF ac this ty[unfolded typed_def]] obtain T' where
    f: "ok (env_fastype env Bs t) T'" "tnorm (tyenv env) T' = tnorm (tyenv env) T" by blast
  from env_fastype_tyw[OF f(1) ti twB twt] f(2) show ?thesis by (rule that)
qed

text \<open>The types computed by \<^const>\<open>mc\<close>, as @{thm [source] pmc_types}:\<close>

lemma pmf_types:
  assumes pi0: "pinv alg ar A W env dps" and twb: "\<forall>T\<in>snd ` set rb. tyw ar (tyenv env) A T"
    and tg: "\<forall>t\<in>set targs. \<forall>T\<in>tys t. tyw ar (tyenv env) A T"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twu: "\<forall>T\<in>tys u. tyw ar (tyenv env) A T"
    and hl: "hlong (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u) (tnorm (tyenv env) U)"
  obtains T0 base Ts' where "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts"
    "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T" "tyw ar (tyenv env) A T0" "tyw ar (tyenv env) A base"
    "has_type (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) (head_of u))
      (tnorm (tyenv env) T0)"
    "tnorm (tyenv env) base = res_type (tnorm (tyenv env) U)"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  note pi = pinvD[OF pi0]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  have tyu: "has_type ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)" by (rule hlong_typed[OF hl])
  from has_type_head_of[OF tyu] obtain Th where tyh: "has_type ?V ?Bs (tnormt ?\<theta> (head_of u)) Th" by auto
  have tch: "\<forall>X\<in>set (map snd rb) \<union> tys (head_of u). tcons ?\<theta> X"
    using twb twu tys_head_of[of u] tcU by auto
  from env_fastype_pterm[OF ac tch tyh] obtain T0 where
    f: "ok (fastype env rb (head_of u)) T0" "tnorm ?\<theta> T0 = Th" by (auto simp: fastype_def)
  have twT0: "tyw ar ?\<theta> A T0" using fastype_tyw[OF f(1) pi(2) twb] twu tys_head_of[of u] by blast
  have rTh: "res_type Th = res_type (tnorm ?\<theta> U)"
  proof (cases "is_Abs u")
    case True
    then have "head_of u = u" by (cases u) auto
    with tyh tyu has_type_unique show ?thesis by metis
  next
    case False
    then have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
    from hlong_nonAbs[OF hl this] have nf: "\<not> is_funT (tnorm ?\<theta> U)" by simp
    have "res_type Th = tnorm ?\<theta> U" using res_type_head(1)[OF tyu nf] tyh by simp
    with nf show ?thesis by (simp add: arg_types_nonfun arg_res_type_base)
  qed
  have "tnorm ?\<theta> T0 = foldr fun_type (arg_types Th) (res_type Th)" using f(2) by (simp add: arg_res_type)
  from body_type_ptnorm[OF ac tcU[OF twT0] this res_type_base] obtain base where
    b: "body_type env T0 = return base" "tnorm ?\<theta> base = res_type Th" by blast
  have twb0: "tyw ar ?\<theta> A base" using body_type_tyw[OF b(1)[unfolded return_def] refl pi(2) twT0] .
  have tct: "\<forall>t\<in>set targs. \<forall>X\<in>tys t. tcons ?\<theta> X" using tg tcU by blast
  from mapM_fastype_ptnorm[OF ac _ tgty tct] twb tcU obtain Ts' where
    m: "mapM (fastype env rb) targs = return Ts'" "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts" by blast
  have twTs: "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T" by (rule mapM_fastype_tyw[OF m(1) pi(2) twb]) (use tg in blast)
  show ?thesis using that[OF _ b(1) m twTs twT0 twb0] f tyh b(2) rTh by (simp add: return_def)
qed

context pmfin
begin

text \<open>A new variable for the copy, with a new pair, as @{thm [source] pflex_copy}:\<close>

lemma pflex_fin:
  assumes cp: "pcpre W env dps rb targs Ts" and up: "pupre W env rb u U"
    and Ts': "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts" "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T"
    and Y: "tyw ar (tyenv env) A Y" "tnorm (tyenv env) Y = tnorm (tyenv env) U"
    and g: "genvar a env (foldr fun_type Ts' Y) = (env1, newhd)"
  shows "PEC W env (vars u \<union> \<Union> (vars ` set targs) \<union> vdps dps) Ts U
    (El_C (combound newhd 0 (length Ts')) env1 ((rb, list_comb newhd targs, u) # dps))"
proof -
  let ?\<theta> = "tyenv env"
  note c = pcpreD[OF cp] and uu = pupreD[OF up]
  note pi = pinvD[OF c(1)]
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF c(5)] by simp
  have lTs': "length Ts' = length Ts" using arg_cong[OF Ts'(1), of length] by simp
  define GT where "GT = foldr fun_type Ts' Y"
  have twGT: "tyw ar ?\<theta> A GT" using Ts'(2) Y(1) by (simp add: GT_def tyw_foldr_fun)
  define G where "G = (a, maxidx env + 1)"
  define W1 where "W1 = W(G := GT)"
  note ge = genvar_pinv[OF c(1) g[folded GT_def] twGT, folded G_def W1_def]
  note pi1 = pinvD[OF ge(1)]
  define dp where "dp = (rb, list_comb newhd targs, u)"
  have tctxG: "tctx env1 W1 G = tnorm (tyenv env1) GT" using wcons_tctx[OF pi1(6)] by (simp add: W1_def)
  have bt: "\<forall>t\<in>set targs. below (maxidx env) t" using c(4) by blast
  have tg1: "list_all2 (typed env1 W1 (map snd rb)) targs Ts'"
    using list_all2_typed_tnorm[OF list_all2_typed_pext[OF c(5) bt ge(7) pi(6) pi1(6) ge(2)] Ts'(1)[folded ge(7)]] .
  have tyl: "typed env1 W1 (map snd rb) (list_comb newhd targs) Y"
    using typed_Var_list_comb[OF tctxG[unfolded GT_def] tg1] ge(4) by (simp add: GT_def)
  have tyu0: "typed env W (map snd rb) u Y" using uu(3) Y(2) by (simp add: typed_def)
  have tyu1: "typed env1 W1 (map snd rb) u Y" by (rule typed_pext[OF tyu0 ge(7) pi(6) pi1(6) ge(2) uu(5)])
  have bG: "below (maxidx env1) newhd" using ge(3,4) by (simp add: below_def G_def)
  have bGT: "below (maxidx env1) (list_comb newhd targs)"
  proof -
    have "\<forall>t\<in>set targs. below (maxidx env1) t" using bt ge(3) by (auto intro: below_mono)
    with bG show ?thesis by (simp add: below_list_comb)
  qed
  have pid: "pinv alg ar A W1 env1 (dp # dps)"
  proof -
    have "swf_tm ar rb newhd" using ge(4) twGT by (simp add: swf_tm_def tyw_def)
    then have "swf_dp ar dp" using c(2) uu(1) c(4) by (simp add: dp_def swf_dp_def swf_tm_list_comb)
    moreover have "\<forall>T\<in>dtys dp. tyw ar (tyenv env1) A T"
      using c(3) uu(2) c(4) twGT ge(4,7) by (auto simp: dp_def tys_list_comb)
    moreover have "ptyped env1 W1 dp" using tyl tyu1 by (auto simp: dp_def)
    moreover have "dp_below (maxidx env1) dp" using bGT uu(5) ge(3) by (auto simp: dp_def dp_below_def intro: below_mono)
    ultimately show ?thesis using ge(1) by (simp add: pinv_def)
  qed
  have pg: "pgood Fd Ft dp"
  proof -
    have "G \<in> Fd \<Longrightarrow> \<exists>t\<in>set targs. \<not> is_Bound t" using c(9) by (auto simp: ptok_def)
    then have d: "dead Fd (list_comb newhd targs)" using ge(4) c(4) by (auto simp: dd_list_comb psh_def G_def)
    have "hok Ft (list_comb newhd targs)" using ge(4) c(4) by (auto simp: hok_list_comb psh_def)
    then have "gs Ft (list_comb newhd targs)" by (rule hok_gs)
    moreover have "gs Ft u" using uu(6) by (auto simp: psh_def intro: gs_free)
    ultimately show ?thesis using d uu(6) by (simp add: pgood_def dp_def psh_def)
  qed
  define NV where "NV = {G}"
  define D where "D = vars u \<union> \<Union> (vars ` set targs) \<union> vdps dps"
  have rr: "vreach env1 = vreach env" using vreach_tenv[of env1 env] ge(6) by simp
  have tx: "ptsext alg ar A W env W1 env1 (dp # dps) D NV"
    unfolding ptsext_def
  proof (intro conjI allI ballI pid ge(2,5))
    show "maxidx env \<le> maxidx env1" using ge(3) by simp
    show "finite NV" by (simp add: NV_def)
    show "maxidx env < snd y" if "y \<in> NV" for y using that by (simp add: NV_def G_def)
    show "snd y \<le> maxidx env1" if "y \<in> NV" for y using that ge(3) by (simp add: NV_def G_def)
    show "vreach env1 X \<subseteq> vreach env (X \<union> D) \<union> NV" for X using vreach_subset[of X "X \<union> D" env] rr by auto
    have "vdps (dp # dps) \<subseteq> D \<union> NV" using ge(4) by (auto simp: dp_def vars_list_comb D_def NV_def)
    then show "vdps (dp # dps) \<subseteq> vreach env D \<union> NV" using vreach_incl[of D env] by blast
  qed
  have vg1: "vgood Fd Ft env1" using c(7) vgood_tenv[of env1 env Fd Ft] ge(6) by simp
  have cr: "pcres W env D W1 env1 (dp # dps) NV" using tx pg c(8) vg1 by (simp add: pcres_def)
  define u' where "u' = combound newhd 0 (length Ts')"
  have cu: "pcpy W1 env1 NV Ts u' U"
    unfolding pcpy_def
  proof (intro conjI)
    have "typed env1 W1 (rev Ts') u' Y"
      using typed_combound_Var[OF tctxG[unfolded GT_def]] ge(4) by (simp add: u'_def GT_def)
    then show "typed env1 W1 (rev Ts) u' U"
      by (rule typed_tnorm_cong) (use Ts'(1) Y(2) ge(7) in \<open>simp_all add: rev_map[symmetric]\<close>)
    show "swf_cp ar (length Ts) u'"
      using ge(4) twGT lTs' by (auto simp: u'_def tyw_def intro!: swf_cp_combound)
    show "\<forall>T\<in>tys u'. tyw ar (tyenv env1) A T" using ge(4,7) twGT by (simp add: u'_def)
    show "below (maxidx env1) u'" using ge(3,4) by (simp add: u'_def below_def G_def)
    show "vars u' \<subseteq> NV" using ge(4) by (simp add: u'_def NV_def)
  qed
  show ?thesis using cr cu by (auto simp: PEC_def D_def dp_def u'_def)
qed

end

context pmfin
begin

text \<open>
  \<open>mc\<close> on a term \<open>u\<close> in head normal form: by induction on the size of \<open>u\<close>, given the
  finiteness of the copies of arguments with a smaller measure.
\<close>

lemma pmc_fin_aux:
  assumes CC: "\<And>W' env' dps' rb' targs' Ts' a T us. ((pmu1 env', rsz alg ar env' W' a), (c, N)) \<in> pmlex \<Longrightarrow>
      pcpre W' env' dps' rb' targs' Ts' \<Longrightarrow> pupre W' env' rb' a T \<Longrightarrow>
      poldin env' (vars a \<union> \<Union> (vars ` set targs') \<union> vdps dps') \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname rb' targs' a us env' dps') cs \<and>
        fin cfg cs (\<lambda>x. \<exists>u' env'' dps'' W'' NV. x = El_D (u' # us) env'' dps'' \<and>
          pcres W' env' (vars a \<union> \<Union> (vars ` set targs') \<union> vdps dps') W'' env'' dps'' NV \<and>
          pcpy W'' env'' NV Ts' u' T)"
  shows "pcpre W env dps rb targs Ts \<Longrightarrow> pupre W env rb u U \<Longrightarrow> hnf u \<Longrightarrow>
    hlong (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u) (tnorm (tyenv env) U) \<Longrightarrow>
    poldin env (vars u \<union> \<Union> (vars ` set targs) \<union> vdps dps) \<Longrightarrow> pmu1 env = c \<Longrightarrow>
    rsz alg ar env W u \<le> N \<Longrightarrow>
    \<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
      fin cfg sq (PEC W env (vars u \<union> \<Union> (vars ` set targs) \<union> vdps dps) Ts U)"
proof (induction "size u" arbitrary: rb targs Ts u U rule: less_induct)
  case less
  let ?\<theta> = "tyenv env"
  note cp = less.prems(1) and up = less.prems(2) and hu = less.prems(3) and hl = less.prems(4)
    and o = less.prems(5) and mu = less.prems(6) and szN = less.prems(7)
  note c = pcpreD[OF cp] and uu = pupreD[OF up]
  note pi = pinvD[OF c(1)]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  define D where "D = vars u \<union> \<Union> (vars ` set targs) \<union> vdps dps"
  obtain T0 base Ts' where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts"
    "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T" "tyw ar ?\<theta> A T0" "tyw ar ?\<theta> A base"
    "has_type (tctx env W) (map (tnorm ?\<theta>) (map snd rb)) (tnormt ?\<theta> (head_of u)) (tnorm ?\<theta> T0)"
    "tnorm ?\<theta> base = res_type (tnorm ?\<theta> U)"
    by (rule pmf_types[OF c(1,3) _ c(5) uu(2) hl]) (use c(4) in blast)
  note mcu = mc_punfold[OF ty0(1-3), of cfg vname dps]
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF c(5)] by simp
  have lTs': "length Ts' = length Ts" using arg_cong[OF ty0(4), of length] by simp
  have nonAbs: "tnorm ?\<theta> base = tnorm ?\<theta> U" if nA: "\<not> is_Abs u"
  proof -
    from nA have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
    from hlong_nonAbs[OF hl this] have "\<not> is_funT (tnorm ?\<theta> U)" by simp
    then show ?thesis using ty0(9) arg_res_type_base by simp
  qed
  have rigid: "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and> fin cfg sq (PEC W env D Ts U)"
    if hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
  proof -
    have nA: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
    note bU = nonAbs[OF nA]
    have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
    have hrig: "is_rigid (head_of u)"
      using hA hV head_of_not_App[of u] ty0(8)
      by (cases "head_of u") (auto simp: is_rigid_def has_type_Bound_iff)
    have lTs'': "length Ts' = length targs" using lTs lTs' by simp
    from make_projs_exact[OF lTs'', of u targs] obtain projs where pr: "make_projs u targs Ts' targs = returnW projs"
      by blast
    have pf: "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
        (\<forall>p\<in>set (arity_guesses cfg bary).
          proj_fin cfg vname rb targs u env dps base Ts' bv Us bary targ p (PEC W env D Ts U))"
    proof (clarify)
      fix bv T targ assume "(bv, T, targ) \<in> set (rev projs)"
      then have "(bv, T, targ) \<in> set projs" by simp
      from make_projs_idx[of u targs Ts' targs projs] pr this obtain j where
        j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length targs"
        "targ = targs ! (length targs - 1 - nat_of_integer j)" "T = Ts' ! (length targs - 1 - nat_of_integer j)"
        by fastforce
      have twT: "tyw ar ?\<theta> A T" using ty0(5) j(3,5) lTs'' by simp
      have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
        by (simp add: arg_res_type)
      from strip_type_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Us bary where
        st: "strip_type env T = return (Us, bary)" by blast
      then have st': "ok (strip_type env T) (Us, bary)" by (simp add: return_def)
      have twy: "tyw ar ?\<theta> A bary" using strip_type_tyw[OF st' pi(2) twT] by simp
      have "proj_fin cfg vname rb targs u env dps base Ts' bv Us bary targ p (PEC W env D Ts U)" for p
        unfolding proj_fin_def
      proof (intro conjI allI impI)
        show "proj_total cfg env base bary p" by (rule proj_total_tyw[OF cfg pi(2) ei(2) ty0(7) twy])
        fix e0 Cs env' env'' args
        assume g: "gentvars p env = (e0, Cs)" and pu: "okW (proj_unify cfg base bary Cs e0) env'"
          and ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)"
        show "cuok (SIMPL (cfg_alg cfg) env''
            ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
          (\<lambda>(env2, fr, ff). PEC W env D Ts U (El_C (list_comb bv args) env2 (fr @ ff)))"
          unfolding cfg by (rule cuok_mono[OF pproj_res[OF cp up hrig nA ty0(4,5) j(2,3,5,4) st' bU ty0(7) g pu ma]])
            (auto simp: PEC_def D_def j(1) cfg)
      qed
      with st' show "\<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
          (\<forall>p\<in>set (arity_guesses cfg bary).
            proj_fin cfg vname rb targs u env dps base Ts' bv Us bary targ p (PEC W env D Ts U))"
        by blast
    qed
    have imit: "fin cfg (case head_of u of
        Const _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | Free _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | _ \<Rightarrow> S_Empty) (PEC W env D Ts U)"
    proof (cases "\<exists>cn Tc. head_of u = Const cn Tc \<or> head_of u = Free cn Tc")
      case True
      then obtain cn Tc where hc: "head_of u = Const cn Tc \<or> head_of u = Free cn Tc" by blast
      define uargs where "uargs = snd (strip_comb u)"
      have u_eq: "u = list_comb (head_of u) uargs" unfolding uargs_def by (rule head_of_list_comb)
      have tyu: "typed env W (map snd rb) (list_comb (head_of u) uargs) U" using uu(3) u_eq by simp
      from typed_list_comb_args[OF ac(1) tyu] obtain As where
        tyh: "typed env W (map snd rb) (head_of u) (foldr fun_type As U)"
        and tya: "list_all2 (typed env W (map snd rb)) uargs As" by blast
      have twu0: "\<forall>X\<in>tys (list_comb (head_of u) uargs). tyw ar ?\<theta> A X" using uu(2) by (simp only: u_eq[symmetric])
      then have twua: "\<forall>t\<in>set uargs. \<forall>X\<in>tys t. tyw ar ?\<theta> A X" by (auto simp: tys_list_comb)
      have tcb: "\<forall>X\<in>snd ` set rb. tcons ?\<theta> X" using c(3) tcU by blast
      from mapM_fastype_ptnorm[OF ac tcb tya] twua tcU obtain As' where
        ma: "mapM (fastype env rb) uargs = return As'" "map (tnorm ?\<theta>) As' = map (tnorm ?\<theta>) As" by blast
      have twAs: "\<forall>X\<in>set As'. tyw ar ?\<theta> A X" by (rule mapM_fastype_tyw[OF ma(1) pi(2) c(3) twua])
      have tya': "list_all2 (typed env W (map snd rb)) uargs As'" by (rule list_all2_typed_tnorm[OF tya ma(2)])
      have tyh': "typed env W (map snd rb) (head_of u) (foldr fun_type As' U)"
        by (rule typed_tnorm_cong[OF tyh refl]) (simp add: tnorm_foldr_fun ma(2))
      have lA: "length As' = length uargs" using list_all2_lengthD[OF tya'] by simp
      have whd: "swf_tm ar rb (head_of u)" and wua: "\<forall>t\<in>set uargs. swf_tm ar rb t"
        using uu(1) u_eq by (metis swf_tm_list_comb)+
      have bua: "\<forall>t\<in>set uargs. below (maxidx env) t" using uu(5) u_eq by (metis below_list_comb)
      have dua: "\<forall>t\<in>set uargs. dead Fd t" using uu(6) u_eq by (metis dd_list_comb psh_def)
      have vua: "\<forall>t\<in>set uargs. vars t \<subseteq> vars u" using u_eq vars_list_comb[of "head_of u" uargs] by auto
      have twu': "\<forall>X\<in>set (map snd rb) \<union> tys (list_comb (head_of u) uargs). tyw ar ?\<theta> A X"
        using c(3) uu(2) u_eq by auto
      have args: "list_all2 (\<lambda>a T. pupre W env rb a T \<and> rsz alg ar env W a < N) uargs As'"
      proof (rule list_all2_all_nthI)
        show "length uargs = length As'" using lA by simp
        fix i assume i: "i < length uargs"
        have "typed env W (map snd rb) (uargs ! i) (As' ! i)" using tya' i by (simp add: list_all2_conv_all_nth)
        moreover have "psh (uargs ! i)" using dua vua uu(6) i by (auto simp: psh_def dest!: nth_mem)
        moreover have "tyw ar ?\<theta> A (As' ! i)" using twAs i lA by simp
        moreover have "\<forall>X\<in>tys (uargs ! i). tyw ar ?\<theta> A X" using twua nth_mem[OF i] by blast
        ultimately have "pupre W env rb (uargs ! i) (As' ! i)"
          using wua bua i by (simp add: pupre_def)
        moreover have "rsz alg ar env W (uargs ! i) < rsz alg ar env W u"
          using rsz_rigid_arg[OF c(1) tyu twu' hc i] u_eq by simp
        ultimately show "pupre W env rb (uargs ! i) (As' ! i) \<and> rsz alg ar env W (uargs ! i) < N"
          using szN by simp
      qed
      have Da: "\<Union> (vars ` set uargs) \<union> \<Union> (vars ` set targs) \<union> vdps dps \<subseteq> D"
        using u_eq vars_list_comb[of "head_of u" uargs] by (auto simp: D_def)
      have oa: "poldin env (\<Union> (vars ` set uargs) \<union> \<Union> (vars ` set targs) \<union> vdps dps)"
        by (rule poldin_mono[OF o[folded D_def]]) (use Da vreach_incl[of D env] in blast)
      note ca = pcopyargs_fin[OF CC cp mu args oa]
      have "fin cfg (copyargs vname rb targs env dps uargs) (\<lambda>x. \<exists>us e d. x = El_D us e d \<and>
          PEC W env D Ts U (El_C (list_comb (head_of u) us) e d))"
      proof (rule fin_mono[OF ca])
        fix x assume "PED W env (\<Union> (vars ` set uargs) \<union> \<Union> (vars ` set targs) \<union> vdps dps) Ts As' x"
        then obtain us e d W' NV where x: "x = El_D us e d"
          and cr: "pcres W env (\<Union> (vars ` set uargs) \<union> \<Union> (vars ` set targs) \<union> vdps dps) W' e d NV"
          and cps: "list_all2 (\<lambda>u' A. pcpy W' e NV Ts u' A) us As'"
          by (auto simp: PED_def)
        have cr': "pcres W env D W' e d NV" by (rule pcres_mono[OF cr]) (use Da vreach_incl[of D env] in blast)
        note t = ptsextD[OF conjunct1[OF cr'[unfolded pcres_def]]]
        have ac': "tacyc (tyenv e)" by (rule tinv_tacyc[OF pinvD(2)[OF t(1)]])
        have ext: "textends ?\<theta> (tyenv e)" using t(4) by (simp add: pextends_def)
        have bh: "below (maxidx env) (head_of u)" using hc by (auto simp: below_def)
        have "typed e W' (map snd rb) (head_of u) (foldr fun_type As' U)"
          by (rule typed_psext[OF ac' t(4) pi(6) pinvD(6)[OF t(1)] t(2) bh tyh'])
        then have tyhe: "typed e W' (rev Ts) (head_of u) (foldr fun_type As' U)"
          using hc by (auto simp: typed_def has_type.Const has_type.Free elim!: has_type_elims)
        have tyc: "list_all2 (typed e W' (rev Ts)) us As'" using cps by (auto simp: pcpy_def elim: list_all2_mono)
        have cpi: "\<exists>A. pcpy W' e NV Ts t A" if "t \<in> set us" for t
        proof -
          from that obtain i where "i < length us" "t = us ! i" by (auto simp: in_set_conv_nth)
          with cps show ?thesis by (auto simp: list_all2_conv_all_nth intro!: exI[of _ "As' ! i"])
        qed
        have "pcpy W' e NV Ts (list_comb (head_of u) us) U"
          unfolding pcpy_def
        proof (intro conjI)
          show "typed e W' (rev Ts) (list_comb (head_of u) us) U" by (rule typed_list_comb[OF tyhe tyc])
          have "swf_cp ar (length Ts) (head_of u)" using whd hc by (auto simp: swf_cp_def swf_tm_def)
          moreover have "\<forall>t\<in>set us. swf_cp ar (length Ts) t" using cpi by (auto simp: pcpy_def)
          ultimately show "swf_cp ar (length Ts) (list_comb (head_of u) us)" by (simp add: swf_cp_list_comb)
          have "\<forall>X\<in>tys (head_of u). tyw ar (tyenv e) A X"
            using uu(2) tys_head_of[of u] tyw_textends[OF ac' ext] by blast
          moreover have "\<forall>t\<in>set us. \<forall>X\<in>tys t. tyw ar (tyenv e) A X" using cpi by (fastforce simp: pcpy_def)
          ultimately show "\<forall>X\<in>tys (list_comb (head_of u) us). tyw ar (tyenv e) A X" by (auto simp: tys_list_comb)
          have "\<forall>t\<in>set us. below (maxidx e) t" using cpi by (auto simp: pcpy_def)
          moreover have "below (maxidx e) (head_of u)" using hc by (auto simp: below_def)
          ultimately show "below (maxidx e) (list_comb (head_of u) us)" using below_list_comb by blast
          have "\<forall>t\<in>set us. vars t \<subseteq> NV" using cpi by (auto simp: pcpy_def)
          then show "vars (list_comb (head_of u) us) \<subseteq> NV" using hc by (auto simp: vars_list_comb)
        qed
        with x cr' show "\<exists>us e d. x = El_D us e d \<and> PEC W env D Ts U (El_C (list_comb (head_of u) us) e d)"
          by (auto simp: PEC_def)
      qed
      then have "fin cfg (S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs)) (PEC W env D Ts U)"
        by (rule fin_MapJoin)
      with hc show ?thesis by (auto simp: uargs_def)
    next
      case False
      then show ?thesis by (cases "head_of u") auto
    qed
    from pmatchfun_fin[OF pf imit] obtain sq where
      mf: "okW (matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) base Ts' (rev projs)) sq"
      and fs: "fin cfg sq (PEC W env D Ts U)"
      by blast
    have "okW (mc cfg vname rb targs u env dps) sq"
      using mcu pr mf hA hV by (cases "head_of u") simp_all
    with fs show ?thesis by blast
  qed
  show ?case
  proof (cases "head_of u")
    case (Abs a T body)
    let ?V = "tctx env W" and ?Bs = "map (tnorm ?\<theta>) (map snd rb)"
    have u: "u = Abs a T body" using hnf_Abs_head[OF hu] Abs by (simp add: fst_strip_comb)
    from hl u obtain U' where U: "tnorm ?\<theta> U = tnorm ?\<theta> T \<rightarrow>\<^sub>T U'"
      and hlb: "hlong ?V (tnorm ?\<theta> T # ?Bs) (tnormt ?\<theta> body) U'"
      by (auto elim: hlong.cases)
    have twT: "tyw ar ?\<theta> A T" using uu(2) u by simp
    have twUn: "tyw ar ?\<theta> A (tnorm ?\<theta> U)" by (rule tyw_tnorm[OF pi(2) uu(4)])
    then have twU': "tyw ar ?\<theta> A U'" using U by (simp add: tyw_fun)
    have nU': "tnorm ?\<theta> U' = U'"
    proof -
      have "tnorm ?\<theta> (tnorm ?\<theta> U) = tnorm ?\<theta> U" by (rule tnorm_idem[OF ac(1)])
      with U show ?thesis by simp
    qed
    have wb: "swf_tm ar ((a, T) # rb) body" and wT: "wft ar T" using uu(1) u by (simp_all add: swf_tm_def)
    have sb': "sbinders ar ((a, T) # rb)" using c(2) wT by (simp add: sbinders_def)
    have hb: "hnf body" using hu u by simp
    have bb: "below (maxidx env) body" using uu(5) u by (simp add: below_def)
    have shb: "psh body" using uu(6) u by (simp add: psh_def)
    define targs' where "targs' = map (incr_boundvars 1) targs @ [Bound 0]"
    have tg': "\<forall>t\<in>set targs'. swf_tm ar ((a, T) # rb) t \<and> below (maxidx env) t \<and> psh t \<and> (\<forall>X\<in>tys t. tyw ar ?\<theta> A X)"
      using c(4) by (auto simp: targs'_def below_def psh_def intro: swf_tm_incr swf_tm_Bound0 psh_incr)
    have tgty': "list_all2 (typed env W (map snd ((a, T) # rb))) targs' (Ts @ [T])"
      unfolding targs'_def
    proof (rule list_all2_appendI)
      show "list_all2 (typed env W (map snd ((a, T) # rb))) (map (incr_boundvars 1) targs) Ts"
        unfolding list_all2_map1 using c(5)
        by (rule list_all2_mono) (simp add: typed_def has_type_incr_boundvars1)
    qed (simp add: typed_def has_type_Bound_iff)
    have cp': "pcpre W env dps ((a, T) # rb) targs' (Ts @ [T])"
      unfolding pcpre_def using c tg' tgty' sb' twT ptok_incr[OF c(9)] by (simp add: targs'_def)
    have tyb: "typed env W (map snd ((a, T) # rb)) body U'"
      using hlong_typed[OF hlb] nU' by (simp add: typed_def)
    have up': "pupre W env ((a, T) # rb) body U'"
      using wb uu(2) u tyb twU' bb shb by (simp add: pupre_def)
    have hlb': "hlong ?V (map (tnorm ?\<theta>) (map snd ((a, T) # rb))) (tnormt ?\<theta> body) (tnorm ?\<theta> U')"
      using hlb nU' by simp
    have vt': "\<Union> (vars ` set targs') = \<Union> (vars ` set targs)" by (auto simp: targs'_def)
    have Db: "vars body \<union> \<Union> (vars ` set targs') \<union> vdps dps = D" using u vt' by (simp add: D_def)
    have o': "poldin env (vars body \<union> \<Union> (vars ` set targs') \<union> vdps dps)" using o Db by (simp add: D_def)
    have tyu: "typed env W (map snd rb) (Abs a T body) U" using uu(3) u by simp
    have "\<forall>X\<in>set (map snd rb) \<union> tys (Abs a T body). tyw ar ?\<theta> A X" using c(3) uu(2) u by auto
    from rsz_Abs[OF c(1) tyu tyb[simplified] this] have "rsz alg ar env W body = rsz alg ar env W u" using u by simp
    with szN have sz': "rsz alg ar env W body \<le> N" by simp
    have "size body < size u" using u by simp
    from less.hyps[OF this cp' up' hb hlb' o' mu sz'] obtain sq where
      mcb: "okW (mc cfg vname ((a, T) # rb) targs' body env dps) sq"
      and fb: "fin cfg sq (PEC W env (vars body \<union> \<Union> (vars ` set targs') \<union> vdps dps) (Ts @ [T]) U')"
      by blast
    have mc: "okW (mc cfg vname rb targs u env dps) (S_MapAbs a T sq)"
      using mcu Abs mcb by (simp add: targs'_def)
    have "fin cfg sq (\<lambda>x. \<exists>u'' e'' d''. x = El_C u'' e'' d'' \<and> PEC W env D Ts U (El_C (Abs a T u'') e'' d''))"
    proof (rule fin_mono[OF fb])
      fix x assume "PEC W env (vars body \<union> \<Union> (vars ` set targs') \<union> vdps dps) (Ts @ [T]) U' x"
      then obtain u' env' dps' W' NV where x: "x = El_C u' env' dps'" and cr: "pcres W env D W' env' dps' NV"
        and cu: "pcpy W' env' NV (Ts @ [T]) u' U'"
        by (auto simp: PEC_def Db)
      note t = ptsextD[OF conjunct1[OF cr[unfolded pcres_def]]]
      have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pinvD(2)[OF t(1)]])
      have ext: "textends ?\<theta> (tyenv env')" using t(4) by (simp add: pextends_def)
      have "tnorm (tyenv env') U = tnorm (tyenv env') T \<rightarrow>\<^sub>T tnorm (tyenv env') U'"
        using arg_cong[OF U, of "tnorm (tyenv env')"] tnorm_textends[OF ac' ext] by simp
      then have "pcpy W' env' NV Ts (Abs a T u') U"
        using cu wT tyw_textends[OF ac' ext twT] by (auto simp: pcpy_def typed_def swf_cp_def below_def intro: has_type.Abs)
      with x cr show "\<exists>u'' e'' d''. x = El_C u'' e'' d'' \<and> PEC W env D Ts U (El_C (Abs a T u'') e'' d'')"
        by (auto simp: PEC_def)
    qed
    then have "fin cfg (S_MapAbs a T sq) (PEC W env D Ts U)" by (rule fin_MapAbs)
    with mc show ?thesis by (auto simp: D_def)
  next
    case (Var w Wt)
    have nA: "\<not> is_Abs u" using Var by (cases u) auto
    obtain env1 newhd where g: "genvar (fst w) env (foldr fun_type Ts' base) = (env1, newhd)"
      by (cases "genvar (fst w) env (foldr fun_type Ts' base)")
    have "PEC W env D Ts U (El_C (combound newhd 0 (length Ts')) env1 ((rb, list_comb newhd targs, u) # dps))"
      unfolding D_def by (rule pflex_fin[OF cp up ty0(4,5,7) nonAbs[OF nA] g])
    moreover have "okW (mc cfg vname rb targs u env dps)
        (S_Single (El_C (combound newhd 0 (length Ts')) env1 ((rb, list_comb newhd targs, u) # dps)))"
      using mcu Var g by simp
    ultimately show ?thesis by (auto simp: D_def intro: fin_Single)
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
end
