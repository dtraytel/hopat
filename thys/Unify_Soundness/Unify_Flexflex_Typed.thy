section \<open>The Typed Invariant of the Flex-Flex Treatment\<close>

theory Unify_Flexflex_Typed
  imports Unify_Acyclic
begin

text \<open>
  The treatment of the flex-flex pairs (\<open>add_ffpair\<close>) keeps the type-level invariant of the
  search (theory \<open>Unify_Typed_Inv\<close>): the type environment stays well-formed, the type
  variables of the bindings and of the remaining pairs stay known, and the type environment
  grows as \<^const>\<open>pure_sig_gen.tgrow\<close> says. The proofs are by induction on the computations and
  need no termination; the typing of the intermediate pairs follows from the soundness of the
  steps (\<^const>\<open>pure_sig_gen.gtyped\<close>).
\<close>

context pure_sig_gen
begin

subsection \<open>Normalization\<close>

lemma ttvars_subst_bound: "ttvars (subst_bound u body) \<subseteq> ttvars body \<union> ttvars u"
  by (simp add: subst_bound_subst ttvars_subst)

lemma norm_term1_known:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> etvars env \<subseteq> S \<Longrightarrow> ttvars t \<subseteq> S \<Longrightarrow> ttvars t' \<subseteq> S"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and kE = "1.prems"(3) and kt = "1.prems"(4)
  have IH: "ttvars u' \<subseteq> S" if "ok (nt te u) u'" "ttvars u \<subseteq> S" for u u'
    using "1.IH"[OF that(1) refl te kE that(2)] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest have "t' = t" by simp
      with kt show ?thesis by simp
    next
      case (Some u)
      with ok_lookup1[OF lr] te have b: "vt_lookup (tenv env) x = Some (T, u)" by simp
      from rest Some have "ok (nt te u) t'" by simp
      then show ?thesis by (rule IH) (use etvarsI[OF b] kE in blast)
    qed
  next
    case (Abs a T body)
    with h obtain body' where b: "ok (nt te body) body'" "t' = Abs a T body'" by auto
    have "ttvars body \<subseteq> S" "tvars T \<subseteq> S" using kt Abs by (auto simp: ttvars_def)
    with IH[OF b(1)] b(2) show ?thesis by (auto simp: ttvars_def)
  next
    case (App f u)
    have kf: "ttvars f \<subseteq> S" and ku: "ttvars u \<subseteq> S" using kt App by (auto simp: ttvars_def)
    have sb: "ttvars t' \<subseteq> S" if "ok (nt te (subst_bound u body)) t'" "ttvars body \<subseteq> S" for body
      by (rule IH[OF that(1)]) (use ttvars_subst_bound[of u body] that(2) ku in blast)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt te (subst_bound u body)) t'" by simp
      then show ?thesis by (rule sb) (use kf f in \<open>auto simp: ttvars_def\<close>)
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      note If = IH[OF hf kf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have r: "ok (nt te (subst_bound u body)) t'" by simp
        show ?thesis by (rule sb[OF r]) (use If nf in \<open>auto simp: ttvars_def\<close>)
      next
        case nA: False
        with rest obtain nu where "ok (nt te u) nu" "t' = nf $ nu" by (cases nf) auto
        with If IH[OF this(1) ku] show ?thesis by (auto simp: ttvars_def)
      qed
    qed
  qed (use h kt in auto)
qed

lemma norm_type_aux_known:
  assumes n: "ok (norm_type_aux (tyenv env) T) T'" and ti: "tinv ar (maxidx env) (tyenv env) A"
    and k: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvars T' \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  have "T' = tnorm (tyenv env) T" by (rule norm_type_aux_tnorm[OF n refl tinv_tacyc[OF ti]])
  with ff_tvars_tnorm[OF tinv_tacyc[OF ti] tinv_tcons_env[OF ti] tinv_tcons[OF ti k]] k show ?thesis by blast
qed

lemma norm_term2_known:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> tinv ar (maxidx env) (tyenv env) A \<Longrightarrow> etvars env \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ti = "1.prems"(2) and kE = "1.prems"(3) and kt = "1.prems"(4)
  let ?S = "tvars_env (tyenv env) \<union> A"
  have IH: "ttvars u' \<subseteq> ?S" if "ok (nt env u) u'" "ttvars u \<subseteq> ?S" for u u'
    using "1.IH"[OF that(1) refl ti kE that(2)] .
  note nk = norm_type_aux_known[OF _ ti]
  show ?case
  proof (cases t)
    case (Const a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Const a T'" by auto
    with nk[OF this(1)] kt Const show ?thesis by (auto simp: ttvars_def)
  next
    case (Free a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Free a T'" by auto
    with nk[OF this(1)] kt Free show ?thesis by (auto simp: ttvars_def)
  next
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Var x T'" by auto
      with nk[OF this(1)] kt Var show ?thesis by (auto simp: ttvars_def)
    next
      case (Some u)
      from ok_lookup_Some[OF lr[unfolded Some]] obtain V where b: "vt_lookup (tenv env) x = Some (V, u)" .
      from rest Some have "ok (nt env u) t'" by simp
      then show ?thesis by (rule IH) (use etvarsI[OF b] kE in blast)
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where T': "ok (norm_type_aux (tyenv env) T) T'" and b: "ok (nt env body) body'"
      and t': "t' = Abs a T' body'" by auto
    have "ttvars body \<subseteq> ?S" "tvars T \<subseteq> ?S" using kt Abs by (auto simp: ttvars_def)
    with IH[OF b] nk[OF T'] t' show ?thesis by (auto simp: ttvars_def)
  next
    case (App f u)
    have kf: "ttvars f \<subseteq> ?S" and ku: "ttvars u \<subseteq> ?S" using kt App by (auto simp: ttvars_def)
    have sb: "ttvars t' \<subseteq> ?S" if "ok (nt env (subst_bound u body)) t'" "ttvars body \<subseteq> ?S" for body
      by (rule IH[OF that(1)]) (use ttvars_subst_bound[of u body] that(2) ku in blast)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      then show ?thesis by (rule sb) (use kf f in \<open>auto simp: ttvars_def\<close>)
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      note If = IH[OF hf kf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have r: "ok (nt env (subst_bound u body)) t'" by simp
        show ?thesis by (rule sb[OF r]) (use If nf in \<open>auto simp: ttvars_def\<close>)
      next
        case nA: False
        with rest obtain nu where "ok (nt env u) nu" "t' = nf $ nu" by (cases nf) auto
        with If IH[OF this(1) ku] show ?thesis by (auto simp: ttvars_def)
      qed
    qed
  qed (use h kt in auto)
qed

lemma norm_term_known:
  assumes n: "ok (norm_term env t) t'" and ti: "tinv ar (maxidx env) (tyenv env) A"
    and kE: "etvars env \<subseteq> tvars_env (tyenv env) \<union> A" and kt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have "t' = t" using n by (simp add: norm_term_def)
    with kt show ?thesis by simp
  next
    case n1
    with n have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_known[OF this refl refl kE kt] show ?thesis .
  next
    case n2
    with n have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_known[OF this refl ti kE kt] show ?thesis .
  qed
qed


subsection \<open>Bindings\<close>

lemma vupdate_known:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
    etvars env' \<subseteq> etvars env \<union> tvars (snd aU) \<union> ttvars t"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  obtain a U where aU: "aU = (a, U)" by (cases aU)
  have upd: "tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
      etvars env' \<subseteq> etvars env \<union> tvars (snd aU) \<union> ttvars t"
    if u: "ok (update aU t env) env'"
    using ok_update(3,4)[OF u[unfolded aU]] etvars_update[OF u[unfolded aU]] aU by auto
  show ?case
  proof (cases t)
    case (Var n T)
    show ?thesis
    proof (cases "fst aU = n")
      case True
      with h Var have "env' = env" by simp
      then show ?thesis by auto
    next
      case ne: False
      show ?thesis
      proof (cases "indexname_less (fst aU) n")
        case lt: True
        with h Var ne obtain lr where lk: "ok (lookup env n T) lr"
          and rest: "ok (case lr of None \<Rightarrow> update (n, T) (Var (fst aU) T) env | Some u \<Rightarrow> vu aU u env) env'"
          by auto
        show ?thesis
        proof (cases lr)
          case None
          with rest have u: "ok (update (n, T) (Var (fst aU) T) env) env'" by simp
          from ok_update(3,4)[OF u] etvars_update[OF u] Var show ?thesis by (auto simp: ttvars_def)
        next
          case (Some u)
          from ok_lookup_Some[OF lk[unfolded Some]] obtain V where b: "vt_lookup (tenv env) n = Some (V, u)" .
          from rest Some have r: "ok (vu aU u env) env'" by simp
          from "1.IH"[OF r refl] etvarsI[OF b] show ?thesis by blast
        qed
      next
        case False
        with h Var ne have "ok (update aU t env) env'" by simp
        from upd[OF this] show ?thesis .
      qed
    qed
  qed (use h upd in simp_all)
qed

lemma einv_tyonly_same:
  "einv A K (tyonly env) \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> maxidx env' = maxidx env \<Longrightarrow> einv A K (tyonly env')"
  by (simp add: tyonly_def)


subsection \<open>Assignments\<close>

lemma ff_assign_known:
  assumes a: "okW (ff_assign alg env rb t u) env'" and fK: "finite K"
    and ei: "einv A K (tyonly env)" and tk: "tknown A env [(rb, t, u)]" and gt: "gtyped env [(rb, t, u)]"
  shows "einv A K (tyonly env') \<and> etvars env' \<subseteq> tvars_env (tyenv env') \<union> A \<and> tgrow A env env'"
proof -
  from a obtain v T where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and rest: "okW (do {b \<leftarrow> liftM (occurs_terms env v [u]);
      if b then raiseW ASSIGN
      else do {
        T1 \<leftarrow> liftM (body_type env T);
        T2 \<leftarrow> liftM (fastype env rb u);
        env' \<leftarrow> cunify_types alg T1 T2 env;
        liftM (vupdate (v, T) (rlist_abs rb u) env')}}) env'"
    by (auto simp: ff_assign_def)
  from rest[unfolded okW_bindW okW_liftM] obtain b where
    r2: "okW (if b then raiseW ASSIGN
      else do {
        T1 \<leftarrow> liftM (body_type env T);
        T2 \<leftarrow> liftM (fastype env rb u);
        env' \<leftarrow> cunify_types alg T1 T2 env;
        liftM (vupdate (v, T) (rlist_abs rb u) env')}) env'"
    by blast
  have nb: "\<not> b" using r2 by (cases b) auto
  from r2[unfolded if_not_P[OF nb] okW_bindW okW_liftM] obtain T1 T2 env1 where
    bt: "ok (body_type env T) T1" and ft: "ok (fastype env rb u) T2"
    and cu: "okW (cunify_types alg T1 T2 env) env1" and vu: "ok (vupdate (v, T) (rlist_abs rb u) env1) env'"
    by blast
  let ?\<theta> = "tyenv env" and ?\<rho> = "tnorm_inst (tyenv env)" and ?KN = "tvars_env (tyenv env) \<union> A"
  have ti: "tinv ar (maxidx env) ?\<theta> A" using einvD(2)[OF ei] by simp
  define "is" where "is = rev (map (\<lambda>j. 0 + integer_of_nat j) [0..<length rb])"
  have t: "t = app (Var v T) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have kt: "ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    using tk by (simp_all add: tknown_pair)
  have kT: "tvars T \<subseteq> ?KN" using kt by (auto simp: t ttvars_def app_apps typs_apps)
  from gtyped_rho0(2)[OF gt ei] obtain e0 W where bs: "bs_env ?\<rho> e0 rb"
    and tyt: "e0 \<turnstile> inst ?\<rho> t : W" and tyu: "e0 \<turnstile> inst ?\<rho> u : W"
    and lbu: "\<not> loose_bvar u (ilength rb)"
    by auto
  from body_type_term[OF ti refl kT] bt have kT1: "tvars T1 \<subseteq> ?KN" by (auto simp: return_def)
  have tvu: "ttvars u \<union> btvars rb \<subseteq> ?KN" using kt by blast
  from env_fastype_term[OF ti refl tyu bs lbu tvu] ft obtain T2' where
    f2: "env_fastype env (map snd rb) u = return T2'" "tvars T2' \<subseteq> ?KN" "tnorm ?\<theta> T2' = W"
    by blast
  have T2: "T2 = T2'" using ft f2(1) by (simp add: fastype_def return_def)
  have kT2: "tvars T2 \<subseteq> ?KN" using f2(2) T2 by simp
  have c2: "cert_typ alg ar (tsubst ?\<rho> T2)" using bs_env_cert[OF bs tyu lbu] f2(3) T2 by simp
  from binder_types_term[OF ti refl kT] obtain Ts where bts: "binder_types env T = return Ts" by blast
  have r0: "tsol ?\<theta> ?\<rho>" using einv_rho0(1)[OF ei] by simp
  have "tsubst ?\<rho> T = map (tsubst ?\<rho>) Ts \<Rrightarrow> tsubst ?\<rho> T1"
    by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt r0])
  moreover have "cert_typ alg ar (tsubst ?\<rho> T)"
  proof -
    from tyt obtain Us where "e0 \<turnstile> Var v (tsubst ?\<rho> T) : Us"
      by (auto simp: t app_apps inst_apps dest!: list_app_typeD)
    then show ?thesis by auto
  qed
  ultimately have c1: "cert_typ alg ar (tsubst ?\<rho> T1)" by (simp add: cert_typ_funs)
  note c = tyinv_cunify[OF cu fK ei kT1 c1 kT2 c2]
  note v = vupdate_known[OF vu refl]
  have ei': "einv A K (tyonly env')" by (rule einv_tyonly_same[OF c(1)]) (use v in simp_all)
  have "btvars (rev rb) = btvars rb" by (simp add: btvars_def)
  then have kr: "ttvars (rlist_abs rb u) \<subseteq> ?KN" using kt by (auto simp: rlist_abs_abs_list ttvars_abs_list)
  have v3: "etvars env' \<subseteq> etvars env1 \<union> tvars T \<union> ttvars (rlist_abs rb u)" and te': "tyenv env' = tyenv env1"
    using v by simp_all
  have "etvars env' \<subseteq> tvars_env (tyenv env') \<union> A"
    unfolding te' using v3 etvars_tenv[OF c(2)] kE kT kr c(3) by blast
  moreover have "tgrow A env env'" using c(7) v by (simp add: tgrow_def tnew_def)
  ultimately show ?thesis using ei' by simp
qed


subsection \<open>Cleaning terms\<close>

lemma flexargs_T: "okW (flexargs js ts Ts) fas \<Longrightarrow> a \<in> set fas \<Longrightarrow> fl_T a \<in> set Ts"
  by (induction js ts Ts arbitrary: fas rule: flexargs.induct) auto

lemma foldrW_change_arg_known:
  "okW (foldrW (change_arg d banned) fas acc) cas \<Longrightarrow> a \<in> set cas \<Longrightarrow>
    a \<in> set acc \<or> (\<exists>a0\<in>set fas. fl_T a = fl_T a0 \<and> ttvars (fl_t a) = ttvars (fl_t a0))"
proof (induction arbitrary: a rule: okW_foldrW_induct)
  case (Cons x xs b b1 b')
  obtain j t T where x: "x = Flarg j t T" by (cases x)
  from Cons.hyps(2) x consider "b' = b1" | t' where "okW (change_bnos banned 0 t) t'" "b' = Flarg j t' T # b1"
    by (auto simp: change_arg_def split: if_splits)
  then show ?case
  proof cases
    case 1
    with Cons.IH[of a] Cons.prems show ?thesis by auto
  next
    case (2 t')
    show ?thesis
    proof (cases "a = Flarg j t' T")
      case True
      with ff_ttvars_change_bnos[OF 2(1)] x show ?thesis by auto
    next
      case False
      with 2(2) Cons.prems have "a \<in> set b1" by simp
      with Cons.IH[of a] show ?thesis by auto
    qed
  qed
qed simp

lemma clean_term_known:
  assumes ct: "okW (clean_term banned env t) (env', t')" and ei: "einv A K (tyonly env)"
    and kE: "etvars env \<subseteq> tvars_env (tyenv env) \<union> A" and kt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tyenv env' = tyenv env \<and> maxidx env \<le> maxidx env' \<and> etvars env' \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A"
  obtain h ts where sc: "strip_comb t = (h, ts)" by (cases "strip_comb t")
  have "\<exists>v T0. h = Var v T0" using ct sc by (cases h) (auto simp: clean_term_def)
  then obtain v T where h: "h = Var v T" by blast
  have t: "t = Var v T \<degree>\<degree> ts" using strip_comb_apps[OF sc] h by simp
  let ?n = "length ts"
  from ct sc h obtain Ts U fas cas where st: "ok (strip_type env T) (Ts, U)"
    and fa: "okW (flexargs (downto0_list ?n) ts Ts) fas"
    and ca: "okW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) cas"
    and rest: "okW (let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')})) (env', t')"
    by (auto simp: clean_term_def Let_def split: prod.splits)
  define args where "args = sort_args cas"
  define ts' where "ts' = map fl_t args"
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  have kT: "tvars T \<subseteq> ?KN" and kts: "\<forall>s\<in>set ts. ttvars s \<subseteq> ?KN" using kt by (auto simp: t ttvars_apps)
  from st have bt: "ok (binder_types env T) Ts" and bdy: "ok (body_type env T) U"
    by (auto simp: strip_type_def)
  from mf_binder_types_sound[OF bt refl tinv_tacyc[OF ti]] kT have kTs: "\<forall>V\<in>set Ts. tvars V \<subseteq> ?KN" by blast
  from body_type_term[OF ti refl kT] bdy have kU: "tvars U \<subseteq> ?KN" by (auto simp: return_def)
  have ka: "ttvars (fl_t a) \<subseteq> ?KN \<and> tvars (fl_T a) \<subseteq> ?KN" if "a \<in> set args" for a
  proof -
    from that have "a \<in> set cas" by (simp add: args_def set_sort_args)
    from foldrW_change_arg_known[OF ca this] obtain a0 where a0: "a0 \<in> set fas" "fl_T a = fl_T a0"
      "ttvars (fl_t a) = ttvars (fl_t a0)" by auto
    with flexargs_mem[OF fa a0(1)] flexargs_T[OF fa a0(1)] kts kTs show ?thesis by simp
  qed
  have kts': "\<forall>s\<in>set ts'. ttvars s \<subseteq> ?KN" using ka by (auto simp: ts'_def)
  have kfT: "\<forall>V\<in>set (map fl_T args). tvars V \<subseteq> ?KN" using ka by auto
  show ?thesis
  proof (cases "decreasing (ilength Ts) args")
    case True
    with rest have env': "env' = env" and t': "t' = Var v T \<degree>\<degree> ts'"
      by (simp_all add: Let_def args_def ts'_def list_comb_apps)
    show ?thesis using kE kT kts' by (auto simp: env' t' ttvars_apps)
  next
    case False
    obtain env1 v' where g: "genvar (fst v) env (foldr fun_type (map fl_T args) U) = (env1, v')" by fastforce
    note gs = genvar_simps[OF g]
    define body where "body = list_comb v' (map (Bound \<circ> fl_j) args)"
    from rest False g obtain env2 where vu: "ok (vupdate (v, T) (types_abs Ts body) env1) env2"
      and nt: "ok (norm_term env2 (list_comb v' ts')) t'" and env': "env' = env2"
      by (auto simp: Let_def args_def ts'_def body_def)
    note v = vupdate_known[OF vu refl]
    have te2: "tyenv env2 = tyenv env" using v gs(2) by simp
    have mx2: "maxidx env \<le> maxidx env2" using v gs(3) by simp
    have kv': "ttvars v' \<subseteq> ?KN" using kfT kU by (auto simp: gs(4) tvars_funs)
    have "ttvars body \<subseteq> ?KN" using kv' by (auto simp: body_def list_comb_apps ttvars_apps)
    then have kb: "ttvars (types_abs Ts body) \<subseteq> ?KN" using kTs by (auto simp: ttvars_types_abs)
    have v3: "etvars env2 \<subseteq> etvars env1 \<union> tvars T \<union> ttvars (types_abs Ts body)" using v by simp
    have kE2: "etvars env2 \<subseteq> ?KN" using v3 kb kT kE etvars_tenv[OF gs(1)] by blast
    have ti2: "tinv ar (maxidx env2) (tyenv env2) A"
      using einvD(2)[OF einv_tyonly_maxidx[OF ei te2 mx2]] by simp
    have "ttvars (list_comb v' ts') \<subseteq> ?KN" using kv' kts' by (auto simp: list_comb_apps ttvars_apps)
    from norm_term_known[OF nt ti2] this kE2 te2 have "ttvars t' \<subseteq> ?KN" by simp
    with te2 mx2 kE2 show ?thesis by (simp add: env')
  qed
qed


subsection \<open>Flex-flex pairs\<close>

lemma tknown_tdps:
  "tknown A env (map (Pair []) tps) \<longleftrightarrow> etvars env \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    (\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A)"
  unfolding tknown_def by (auto simp: btvars_def)

lemma clean_ffpair_known:
  assumes cf: "okW (clean_ffpair alg rb t u env tps) (env', tps')" and fK: "finite K"
    and ei: "einv A K (tyonly env)" and tk: "tknown A env ((rb, t, u) # tdps tps)"
    and gt: "gtyped env ((rb, t, u) # tdps tps)"
  shows "einv A K (tyonly env') \<and> tknown A env' (tdps tps') \<and> tgrow A env env'"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have kp: "ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    and ktp: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> ?KN"
    using tk tknown_Cons[of A env "(rb, t, u)" "tdps tps"] by (auto simp: tknown_pair tknown_tdps)
  have gp: "gtyped env [(rb, t, u)]" by (rule gtyped_mono[OF gt]) simp
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  from clean_binder[OF fb] obtain F where F: "bren_ok banned rb rb' F" by blast
  have krb': "btvars rb' \<subseteq> ?KN" using bren_ok_btvars[OF F] kp by blast
  have "(\<exists>env1 t' env2 u'. okW (clean_term banned env t) (env1, t') \<and>
      okW (clean_term banned env1 u) (env2, u') \<and>
      okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')) \<or>
      (env', tps') = (env, add_tpair rb t u tps)"
    using cf fb by (auto simp: clean_ffpair_def Let_def okW_handleW dest!: okW_CHANGE_FAIL_handler)
  then consider (fail) "(env', tps') = (env, add_tpair rb t u tps)"
    | (main) env1 t' env2 u' where "okW (clean_term banned env t) (env1, t')"
      "okW (clean_term banned env1 u) (env2, u')" "okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')"
    by blast
  then show ?thesis
  proof cases
    case fail
    have "\<forall>(t', u')\<in>set (add_tpair rb t u tps). ttvars t' \<union> ttvars u' \<subseteq> ?KN"
      by (rule add_tpair_known[OF ktp]) (use kp in blast)
    with fail ei kE show ?thesis by (simp add: tknown_tdps)
  next
    case (main env1 t' env2 u')
    have kt: "ttvars t \<subseteq> ?KN" and ku: "ttvars u \<subseteq> ?KN" using kp by blast+
    from clean_term_known[OF main(1) ei kE kt]
    have c1: "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1" "etvars env1 \<subseteq> ?KN" "ttvars t' \<subseteq> ?KN" by blast+
    have ei1: "einv A K (tyonly env1)" by (rule einv_tyonly_maxidx[OF ei c1(1,2)])
    from clean_term_known[OF main(2) ei1] c1 ku
    have c2: "tyenv env2 = tyenv env" "maxidx env1 \<le> maxidx env2" "etvars env2 \<subseteq> ?KN" "ttvars u' \<subseteq> ?KN" by auto
    have mx2: "maxidx env \<le> maxidx env2" using c1(2) c2(2) by simp
    have ei2: "einv A K (tyonly env2)" by (rule einv_tyonly_maxidx[OF ei c2(1) mx2])
    have g2: "tgrow A env env2" by (rule tgrow_tyenv[OF c2(1) mx2])
    have cl: "dstep env [(rb, t, u)] env2 [(rb', t', u')]"
      by (rule clean_dstep[OF clean_term_sound[OF main(1) F] clean_term_sound[OF main(2) F] F])
    have gt2: "gtyped env2 [(rb', t', u')]" by (rule gtyped_dstep[OF cl gp])
    have tk2: "tknown A env2 [(rb', t', u')]" using c1(4) c2 krb' by (simp add: tknown_pair)
    have asg: ?thesis if fa: "okW (ff_assign alg env2 rb' s s') env3" and e: "(env', tps') = (env3, tps)"
      and tks: "tknown A env2 [(rb', s, s')]" and gts: "gtyped env2 [(rb', s, s')]" for s s' env3
    proof -
      from ff_assign_known[OF fa fK ei2 tks gts]
      have r: "einv A K (tyonly env3)" "etvars env3 \<subseteq> tvars_env (tyenv env3) \<union> A" "tgrow A env2 env3" by blast+
      have g: "tgrow A env env3" by (rule tgrow_trans[OF g2 r(3)])
      have "tknown A env3 (tdps tps)" using ktp r(2) tgrowD(1)[OF g] by (fastforce simp: tknown_tdps)
      with r(1) g e show ?thesis by simp
    qed
    from ff_handler[OF main(3)] consider (fa1) env3 where "okW (ff_assign alg env2 rb' t' u') env3"
        "(env', tps') = (env3, tps)"
      | (fa2) env3 where "okW (ff_assign alg env2 rb' u' t') env3" "(env', tps') = (env3, tps)"
      | (keep) "(env', tps') = (env2, add_tpair rb' t' u' tps)"
      by blast
    then show ?thesis
    proof cases
      case (fa1 env3)
      show ?thesis by (rule asg[OF fa1 tk2 gt2])
    next
      case (fa2 env3)
      show ?thesis by (rule asg[OF fa2 tknown_swap[OF tk2] gtyped_swap[OF gt2]])
    next
      case keep
      have "\<forall>(t'', u'')\<in>set (add_tpair rb' t' u' tps). ttvars t'' \<union> ttvars u'' \<subseteq> ?KN"
        by (rule add_tpair_known[OF ktp]) (use c1(4) c2(4) krb' in blast)
      with keep ei2 c2(1,3) g2 show ?thesis by (simp add: tknown_tdps)
    qed
  qed
qed

lemma add_ffpair_known:
  assumes a: "okW (add_ffpair alg dp (env, tps)) (env', tps')" and fK: "finite K"
    and ei: "einv A K (tyonly env)" and tk: "tknown A env (dp # tdps tps)" and gt: "gtyped env (dp # tdps tps)"
  shows "einv A K (tyonly env') \<and> tknown A env' (tdps tps') \<and> tgrow A env env'"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A"
  obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
  from a dp obtain t u where nt: "ok (norm_term env t0) t" and nu: "ok (norm_term env u0) u"
    and rest: "okW (case (head_of t, head_of u) of
        (Var v T, Var w U) \<Rightarrow>
          if v = w then
            (if T = U then returnW (env, add_tpair rb t u tps)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair alg rb u t env tps
          else clean_ffpair alg rb t u env tps
      | _ \<Rightarrow> raiseW (PExn (Term_Error (STR ''add_ffpair: Vars expected'') [t, u]))) (env', tps')"
    by (auto simp: add_ffpair_def)
  have kp: "ttvars t0 \<union> ttvars u0 \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    and ktp: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> ?KN"
    using tk tknown_Cons[of A env "(rb, t0, u0)" "tdps tps"] by (auto simp: dp tknown_pair tknown_tdps)
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  have kt: "ttvars t \<subseteq> ?KN" by (rule norm_term_known[OF nt ti kE]) (use kp in blast)
  have ku: "ttvars u \<subseteq> ?KN" by (rule norm_term_known[OF nu ti kE]) (use kp in blast)
  have n: "dstep env ((rb, t0, u0) # tdps tps) env ((rb, t, u) # tdps tps)"
    using dstep_frame[where fs = "tdps tps", OF norm_term_dstep[where bs = rb, OF nt nu]] by simp
  have gtn: "gtyped env ((rb, t, u) # tdps tps)" by (rule gtyped_dstep[OF n gt[unfolded dp]])
  have tkn: "tknown A env ((rb, t, u) # tdps tps)"
    using tknown_Cons[of A env "(rb, t, u)" "tdps tps"] kt ku kp kE ktp by (auto simp: tknown_pair tknown_tdps)
  from rest consider (same) "env' = env" "tps' = add_tpair rb t u tps"
    | (tu) "okW (clean_ffpair alg rb t u env tps) (env', tps')"
    | (ut) "okW (clean_ffpair alg rb u t env tps) (env', tps')"
    by (auto split: pterm.splits if_splits)
  then show ?thesis
  proof cases
    case same
    have "\<forall>(t', u')\<in>set (add_tpair rb t u tps). ttvars t' \<union> ttvars u' \<subseteq> ?KN"
      by (rule add_tpair_known[OF ktp]) (use kt ku kp in blast)
    with same ei kE show ?thesis by (simp add: tknown_tdps)
  next
    case tu
    from clean_ffpair_known[OF tu fK ei tkn gtn] show ?thesis .
  next
    case ut
    have "tknown A env ((rb, u, t) # tdps tps)"
      using tkn tknown_Cons[of A env _ "tdps tps"] by (auto simp: tknown_pair)
    moreover have "gtyped env ((rb, u, t) # tdps tps)"
      by (rule gtyped_dstep[OF _ gtn]) (rule dstep_swap_in[OF dstep_refl])
    ultimately show ?thesis by (rule clean_ffpair_known[OF ut fK ei])
  qed
qed

theorem foldrW_add_ffpair_known:
  assumes fK: "finite K"
  shows "okW (foldrW (add_ffpair alg) ffs (env, tps)) (env', tps') \<Longrightarrow> einv A K (tyonly env) \<Longrightarrow>
    tknown A env (ffs @ tdps tps) \<Longrightarrow> gtyped env (ffs @ tdps tps) \<Longrightarrow>
    einv A K (tyonly env') \<and> tknown A env' (tdps tps') \<and> tgrow A env env'"
proof (induction ffs arbitrary: env' tps')
  case Nil
  then show ?case by simp
next
  case (Cons dp ffs)
  from Cons.prems(1) obtain env1 tps1 where f: "okW (foldrW (add_ffpair alg) ffs (env, tps)) (env1, tps1)"
    and a: "okW (add_ffpair alg dp (env1, tps1)) (env', tps')" by auto
  have tk0: "tknown A env (ffs @ tdps tps)" by (rule tknown_mono[OF Cons.prems(3)]) auto
  have gt0: "gtyped env (ffs @ tdps tps)" by (rule gtyped_mono[OF Cons.prems(4)]) auto
  from Cons.IH[OF f Cons.prems(2) tk0 gt0]
  have I: "einv A K (tyonly env1)" "tknown A env1 (tdps tps1)" "tgrow A env env1" by blast+
  have d1: "dstep env (ffs @ tdps tps) env1 (tdps tps1)" by (rule foldrW_add_ffpair_sound[OF f])
  have "dstep env ((ffs @ tdps tps) @ [dp]) env1 (tdps tps1 @ [dp])" by (rule dstep_frame[OF d1])
  then have "gtyped env1 (tdps tps1 @ [dp])"
    by (rule gtyped_dstep) (rule gtyped_mono[OF Cons.prems(4)], auto)
  then have gt1: "gtyped env1 (dp # tdps tps1)" by (rule gtyped_mono) auto
  have "etvars env1 \<subseteq> tvars_env (tyenv env1) \<union> A" using I(2) by (simp add: tknown_def)
  then have "tknown A env1 [dp]"
    using tknown_ext[OF tknown_mono[OF Cons.prems(3), of "[dp]"] tgrowD(1)[OF I(3)]] by auto
  with I(2) have tk1: "tknown A env1 (dp # tdps tps1)" using tknown_Cons[of A env1 dp "tdps tps1"] by blast
  from add_ffpair_known[OF a fK I(1) tk1 gt1] tgrow_trans[OF I(3)] show ?case by blast
qed

end

end
