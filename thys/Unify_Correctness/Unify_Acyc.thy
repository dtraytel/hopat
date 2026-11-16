section \<open>Acyclicity of the Results of the Higher-Order Unifier\<close>

theory Unify_Acyc
  imports Unify_Match_Inv
begin

text \<open>
  The environments of the unifiers that \<open>hounifiers\<close> enumerates are acyclic (on names, ignoring
  types), for any names of the variables, if the input environment is: \<open>SIMPL\<close> keeps
  acyclicity by its occurs check (theory \<open>Unify_Acyc_Simpl\<close>), \<open>MATCH\<close> binds variables to terms
  whose variables are new (theory \<open>Unify_Match_Inv\<close> with the flag set), and the treatment of the
  flex-flex pairs (\<open>add_ffpair\<close>) binds the head of a flex term to a term with a new variable
  (\<open>clean_term\<close>) or after an occurs check (\<open>ff_assign\<close>). Partial correctness, no termination.
\<close>

context pure_sig_gen
begin

subsection \<open>Normalization\<close>

text \<open>The variables of a normal form are unbound and have the names of the term or of the bindings:\<close>

abbreviation vnames :: "(indexname \<times> ptyp) set \<Rightarrow> indexname set" where
  "vnames X \<equiv> fst ` X"

definition nvars_ok :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "nvars_ok env t t' \<longleftrightarrow> (\<forall>(x, T)\<in>vars t'. vt_lookup (tenv env) x = None) \<and>
    vnames (vars t') \<subseteq> vnames (vars t) \<union> vnames (evars env)"

lemma vars_subst_bound_mi: "vars (subst_bound u body) \<subseteq> vars body \<union> vars u"
  by (simp add: subst_bound_subst vars_subst)

lemma evars_binding: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> vars u \<subseteq> evars env"
  unfolding evars_def bnds_def by blast

lemma norm_term1_vars:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> nvars_ok env t t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2)
  have IH: "nvars_ok env u u'" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with ok_lookup1[OF lr] te have "vt_lookup (tenv env) x = None" by simp
      moreover from rest None Var have "t' = Var x T" by simp
      ultimately show ?thesis using Var by (simp add: nvars_ok_def)
    next
      case (Some u)
      with ok_lookup1[OF lr] te have b: "vt_lookup (tenv env) x = Some (T, u)" by simp
      from rest Some have "ok (nt te u) t'" by simp
      note I = IH[OF this]
      have "vnames (vars u) \<subseteq> vnames (evars env)" by (rule image_mono[OF evars_binding[OF b]])
      with I show ?thesis unfolding nvars_ok_def by blast
    qed
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH[OF this(1)] Abs show ?thesis by (simp add: nvars_ok_def)
  next
    case (App f u)
    have sb: "nvars_ok env (f $ u) t'"
      if "ok (nt te (subst_bound u body)) t'" "vnames (vars body) \<subseteq> vnames (vars f) \<union> vnames (evars env)"
      for body
    proof -
      note I = IH[OF that(1)]
      have b: "vnames (vars (subst_bound u body)) \<subseteq> vnames (vars body) \<union> vnames (vars u)"
        by (metis image_Un image_mono vars_subst_bound_mi)
      have a: "vnames (vars t') \<subseteq> vnames (vars (subst_bound u body)) \<union> vnames (evars env)"
        using I by (simp add: nvars_ok_def)
      have "vnames (vars t') \<subseteq> vnames (vars f) \<union> vnames (vars u) \<union> vnames (evars env)"
        using a b that(2) by blast
      then show ?thesis using I by (simp add: nvars_ok_def image_Un)
    qed
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt te (subst_bound u body)) t'" by simp
      from sb[OF this] f App show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      note If = IH[OF hf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have r: "ok (nt te (subst_bound u body)) t'" by simp
        have "vnames (vars body) \<subseteq> vnames (vars f) \<union> vnames (evars env)" using If nf by (auto simp: nvars_ok_def)
        from sb[OF r this] App show ?thesis by simp
      next
        case nA: False
        with rest obtain nu where "ok (nt te u) nu" "t' = nf $ nu" by (cases nf) auto
        with If IH[OF this(1)] App show ?thesis by (auto simp: nvars_ok_def)
      qed
    qed
  qed (use h in \<open>auto simp: nvars_ok_def\<close>)
qed


lemma norm_term2_vars:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> nvars_ok env t t'"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "nvars_ok env u u'" if "ok (nt env u) u'" for u u'
    using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      have "vt_lookup (tenv env) x = None" using ok_lookup_None lr None by simp
      moreover from rest None obtain T' where "t' = Var x T'" by auto
      ultimately show ?thesis using Var by (simp add: nvars_ok_def)
    next
      case (Some u)
      from ok_lookup_Some[OF lr[unfolded Some]] obtain U where b: "vt_lookup (tenv env) x = Some (U, u)" .
      from rest Some have "ok (nt env u) t'" by simp
      note I = IH[OF this]
      have "vnames (vars u) \<subseteq> vnames (evars env)" by (rule image_mono[OF evars_binding[OF b]])
      with I show ?thesis unfolding nvars_ok_def by blast
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (nt env body) body'" "t' = Abs a T' body'" by auto
    with IH[OF this(1)] Abs show ?thesis by (simp add: nvars_ok_def)
  next
    case (App f u)
    have sb: "nvars_ok env (f $ u) t'"
      if "ok (nt env (subst_bound u body)) t'" "vnames (vars body) \<subseteq> vnames (vars f) \<union> vnames (evars env)"
      for body
    proof -
      note I = IH[OF that(1)]
      have b: "vnames (vars (subst_bound u body)) \<subseteq> vnames (vars body) \<union> vnames (vars u)"
        by (metis image_Un image_mono vars_subst_bound_mi)
      have a: "vnames (vars t') \<subseteq> vnames (vars (subst_bound u body)) \<union> vnames (evars env)"
        using I by (simp add: nvars_ok_def)
      have "vnames (vars t') \<subseteq> vnames (vars f) \<union> vnames (vars u) \<union> vnames (evars env)"
        using a b that(2) by blast
      then show ?thesis using I by (simp add: nvars_ok_def image_Un)
    qed
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      from sb[OF this] f App show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      note If = IH[OF hf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have r: "ok (nt env (subst_bound u body)) t'" by simp
        have "vnames (vars body) \<subseteq> vnames (vars f) \<union> vnames (evars env)" using If nf by (auto simp: nvars_ok_def)
        from sb[OF r this] App show ?thesis by simp
      next
        case nA: False
        with rest obtain nu where "ok (nt env u) nu" "t' = nf $ nu" by (cases nf) auto
        with If IH[OF this(1)] App show ?thesis by (auto simp: nvars_ok_def)
      qed
    qed
  qed (use h in \<open>auto simp: nvars_ok_def\<close>)
qed

lemma norm_term_vars: "ok (norm_term env t) t' \<Longrightarrow> nvars_ok env t t'"
proof -
  assume n: "ok (norm_term env t) t'"
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have "t' = t" "env_is_empty env" using n by (simp_all add: norm_term_def)
    then show ?thesis by (auto simp: nvars_ok_def env_is_empty_def vt_is_empty_lookup)
  next
    case n1
    with n have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_vars[OF this refl refl] show ?thesis .
  next
    case n2
    with n have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_vars[OF this refl] show ?thesis .
  qed
qed


subsection \<open>Bindings of the flex-flex treatment\<close>

lemma evars_names_update:
  "ok (update (F, T) t env) env' \<Longrightarrow> vnames (evars env') = insert F (vnames (vars t) \<union> vnames (evars env))"
  using evars_update[of F T t env env'] by auto

lemma vupdate_acyc:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> acyc env \<Longrightarrow> vt_lookup (tenv env) (fst aU) = None \<Longrightarrow>
    (\<forall>y\<in>vnames (vars t). (fst aU, y) \<notin> (dep env)\<^sup>*) \<Longrightarrow>
    acyc env' \<and> tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
    vnames (evars env') \<subseteq> insert (fst aU) (vnames (vars t) \<union> vnames (evars env))"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2) and ub = "1.prems"(3) and nr = "1.prems"(4)
  obtain a U where aU: "aU = (a, U)" by (cases aU)
  have upd: "acyc env' \<and> tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
      vnames (evars env') \<subseteq> insert (fst aU) (vnames (vars t) \<union> vnames (evars env))"
    if u: "ok (update aU t env) env'"
  proof -
    have u': "ok (update (a, U) t env) env'" using u aU by simp
    have "acyc env'"
    proof (rule acyc_update[OF u' ac])
      show "(a, y) \<notin> (dep env)\<^sup>*" if "(y, V) \<in> vars t" for y V
        using nr that aU by force
    qed
    with ok_update(3,4)[OF u'] evars_names_update[OF u'] aU show ?thesis by auto
  qed
  show ?case
  proof (cases t)
    case (Var n T)
    show ?thesis
    proof (cases "fst aU = n")
      case True
      with h Var have "env' = env" by simp
      then show ?thesis using ac by auto
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
          have "acyc env'"
          proof (rule acyc_update[OF u ac])
            show "(n, y) \<notin> (dep env)\<^sup>*" if "(y, V) \<in> vars (Var (fst aU) T)" for y V
              using that not_dep_unbound[OF ub, of n] ne by auto
          qed
          with ok_update(3,4)[OF u] evars_names_update[OF u] Var show ?thesis by auto
        next
          case (Some u)
          from ok_lookup_Some[OF lk[unfolded Some]] obtain V where b: "vt_lookup (tenv env) n = Some (V, u)" .
          from rest Some have r: "ok (vu aU u env) env'" by simp
          have nr': "\<forall>y\<in>vnames (vars u). (fst aU, y) \<notin> (dep env)\<^sup>*"
          proof
            fix y assume "y \<in> vnames (vars u)"
            then obtain Y where "(y, Y) \<in> vars u" by auto
            then have "(y, n) \<in> dep env" by (rule depI[OF b])
            moreover have "(fst aU, n) \<notin> (dep env)\<^sup>*" using nr Var by auto
            ultimately show "(fst aU, y) \<notin> (dep env)\<^sup>*" by (meson rtrancl.rtrancl_into_rtrancl)
          qed
          from "1.IH"[OF r refl ac ub nr'] have I: "acyc env' \<and> tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
            vnames (evars env') \<subseteq> insert (fst aU) (vnames (vars u) \<union> vnames (evars env))" .
          have "vnames (vars u) \<subseteq> vnames (evars env)" by (rule image_mono[OF evars_binding[OF b]])
          with I show ?thesis by blast
        qed
      next
        case False
        with h Var ne have "ok (update aU t env) env'" by simp
        from upd[OF this] show ?thesis .
      qed
    qed
  qed (use h upd in simp_all)
qed


theorem ff_assign_acyc:
  assumes a: "okW (ff_assign al env rb t u) env'" and ac: "acyc env"
    and hv: "\<And>v T. head_of t = Var v T \<Longrightarrow> vt_lookup (tenv env) v = None"
  shows "acyc env' \<and> maxidx env \<le> maxidx env' \<and>
    vnames (evars env') \<subseteq> vnames (evars env) \<union> vnames (vars t) \<union> vnames (vars u)"
proof -
  from a obtain v T where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and rest: "okW (do {b \<leftarrow> liftM (occurs_terms env v [u]);
      if b then raiseW ASSIGN
      else do {
        T1 \<leftarrow> liftM (body_type env T);
        T2 \<leftarrow> liftM (fastype env rb u);
        env' \<leftarrow> cunify_types al T1 T2 env;
        liftM (vupdate (v, T) (rlist_abs rb u) env')}}) env'"
    by (auto simp: ff_assign_def)
  from rest[unfolded okW_bindW okW_liftM] obtain b where ocb: "ok (occurs_terms env v [u]) b"
    and r2: "okW (if b then raiseW ASSIGN
      else do {
        T1 \<leftarrow> liftM (body_type env T);
        T2 \<leftarrow> liftM (fastype env rb u);
        env' \<leftarrow> cunify_types al T1 T2 env;
        liftM (vupdate (v, T) (rlist_abs rb u) env')}) env'"
    by blast
  have nb: "\<not> b" using r2 by (cases b) auto
  with ocb have oc: "ok (occurs_terms env v [u]) False" by simp
  from r2[unfolded if_not_P[OF nb] okW_bindW okW_liftM] obtain T1 T2 env1 where
    cu: "okW (cunify_types al T1 T2 env) env1" and vu: "ok (vupdate (v, T) (rlist_abs rb u) env1) env'"
    by blast
  have hd: "head_of t = Var v T" by (rule get_eta_var_head[OF gev])
  have te: "tenv env1 = tenv env" by (rule cunify_types_sound(1)[OF cu])
  have mx: "maxidx env \<le> maxidx env1" using cunify_types_sound(2)[OF cu] by (simp add: extends_def)
  have ac1: "acyc env1" using ac acyc_tenv[OF te] by simp
  have ub: "vt_lookup (tenv env1) v = None" using hv[OF hd] te by simp
  have nr: "\<forall>y\<in>vnames (vars (rlist_abs rb u)). (v, y) \<notin> (dep env1)\<^sup>*"
    using occurs_terms_sound[OF oc ac, of u] dep_tenv[OF te] by auto
  have ub': "vt_lookup (tenv env1) (fst (v, T)) = None" using ub by simp
  have nr': "\<forall>y\<in>vnames (vars (rlist_abs rb u)). (fst (v, T), y) \<notin> (dep env1)\<^sup>*" using nr by simp
  from vupdate_acyc[OF vu refl ac1 ub' nr']
  have r: "acyc env'" "maxidx env' = maxidx env1"
    "vnames (evars env') \<subseteq> insert v (vnames (vars u) \<union> vnames (evars env1))"
    by simp_all
  have "v \<in> vnames (vars t)"
  proof -
    have "(v, T) \<in> vars (head_of t)" using hd by simp
    moreover have "vars (head_of t) \<subseteq> vars t" by (induction t) auto
    ultimately show ?thesis by force
  qed
  with r mx evars_tenv[OF te] show ?thesis by auto
qed

lemma vars_change_bnos: "okW (change_bnos banned lev t) t' \<Longrightarrow> vars t' = vars t"
  by (induction banned lev t arbitrary: t' rule: change_bnos.induct) (auto split: if_splits)

lemma flexargs_mem: "okW (flexargs js ts Ts) fas \<Longrightarrow> a \<in> set fas \<Longrightarrow> fl_t a \<in> set ts"
  by (induction js ts Ts arbitrary: fas rule: flexargs.induct) auto

lemma flexargs_Nil: "okW (flexargs js ts []) fas \<Longrightarrow> fas = [] \<and> ts = []"
  by (cases js; cases ts) auto

lemma foldrW_change_arg_vars:
  "okW (foldrW (change_arg d banned) fas acc) cas \<Longrightarrow> (\<forall>a\<in>set fas. vars (fl_t a) \<subseteq> V) \<Longrightarrow>
    (\<forall>a\<in>set acc. vars (fl_t a) \<subseteq> V) \<Longrightarrow> \<forall>a\<in>set cas. vars (fl_t a) \<subseteq> V"
proof (induction rule: okW_foldrW_induct)
  case (Cons x xs b b1 b')
  have b1: "\<forall>a\<in>set b1. vars (fl_t a) \<subseteq> V" using Cons.IH Cons.prems by simp
  obtain j t T where x: "x = Flarg j t T" by (cases x)
  from Cons.hyps(2) x consider "b' = b1" | t' where "okW (change_bnos banned 0 t) t'" "b' = Flarg j t' T # b1"
    by (auto simp: change_arg_def split: if_splits)
  then show ?case
  proof cases
    case (2 t')
    with vars_change_bnos[OF 2(1)] Cons.prems(1) x b1 show ?thesis by auto
  qed (use b1 in simp)
qed simp

lemma set_ins_arg: "set (ins_arg x xs) = insert x (set xs)"
  by (induction xs) auto

lemma set_sort_args: "set (sort_args xs) = set xs"
  by (induction xs) (auto simp: set_ins_arg)


lemma below_names: "below n X \<longleftrightarrow> (\<forall>x\<in>vnames X. snd x \<le> n)"
  by (auto simp: below_def)

lemma vupdate_nonVar: "\<not> is_Var t \<Longrightarrow> vupdate aU t env = update aU t env"
  by (subst vupdate.simps) (cases t; simp)

theorem clean_term_acyc:
  assumes ct: "okW (clean_term banned env t) (env', t')" and ac: "acyc env"
    and hd: "head_of t = Var v0 T0" and ub: "vt_lookup (tenv env) v0 = None"
    and bl: "below (maxidx env) (vars t \<union> evars env)"
  shows "acyc env' \<and> maxidx env \<le> maxidx env' \<and> below (maxidx env') (vars t' \<union> evars env') \<and>
    (\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v0) \<and>
    (\<exists>h T'. head_of t' = Var h T' \<and> vt_lookup (tenv env') h = None \<and> (h = v0 \<or> maxidx env < snd h))"
proof -
  obtain h ts where sc: "strip_comb t = (h, ts)" by (cases "strip_comb t")
  have "\<exists>v T0. h = Var v T0" using ct sc by (cases h) (auto simp: clean_term_def)
  then obtain v T where h: "h = Var v T" by blast
  have t: "t = Var v T \<degree>\<degree> ts" using strip_comb_apps[OF sc] h by simp
  have vT: "v = v0" "T = T0" using hd t by (simp_all add: head_of_apps)
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
  have lTs: "length Ts = ?n" using flexargs_ok[OF fa] by simp
  have va: "\<forall>a\<in>set cas. vars (fl_t a) \<subseteq> (\<Union>s\<in>set ts. vars s)"
    by (rule foldrW_change_arg_vars[OF ca]) (use flexargs_mem[OF fa] in auto)
  have vts': "vnames (vars (list_comb x ts')) \<subseteq> vnames (vars x) \<union> vnames (vars t)" for x
  proof -
    have "vars (list_comb x ts') \<subseteq> vars x \<union> (\<Union>s\<in>set ts. vars s)"
      using va by (auto simp: ts'_def args_def set_sort_args list_comb_apps vars_apps)
    moreover have "(\<Union>s\<in>set ts. vars s) \<subseteq> vars t" by (auto simp: t vars_apps)
    ultimately show ?thesis by blast
  qed
  have bt: "below (maxidx env) (vars t)" "below (maxidx env) (evars env)" using bl below_mono by blast+
  have "(v, T) \<in> vars t" by (simp add: t vars_apps)
  from belowD[OF bt(1) this] have v_le: "snd v \<le> maxidx env" .
  have bound_le: "snd x \<le> maxidx env" if "vt_lookup (tenv env) x = Some b" for x b
  proof -
    obtain B bb where "b = (B, bb)" by (cases b)
    with that have "(x, B) \<in> evars env" unfolding evars_def bnds_def by (cases x) blast
    from belowD[OF bt(2) this] show ?thesis .
  qed
  show ?thesis
  proof (cases "decreasing (ilength Ts) args")
    case True
    with rest have env': "env' = env" and t': "t' = Var v T \<degree>\<degree> ts'"
      by (simp_all add: Let_def args_def ts'_def list_comb_apps)
    have "vnames (vars t') \<subseteq> insert v (vnames (vars t))" using vts'[of "Var v T"] by (simp add: t' list_comb_apps)
    then have "below (maxidx env) (vars t')" using v_le bt(1) unfolding below_names by blast
    then show ?thesis using ac bt(2) ub vT by (auto simp: env' t' head_of_apps below_def)
  next
    case False
    have Ts: "Ts \<noteq> []"
    proof
      assume Ts: "Ts = []"
      then have "ts = []" using lTs by simp
      with fa Ts have "fas = []" by (simp add: downto0_list_def)
      with ca have "cas = []" by simp
      with False Ts show False by (simp add: args_def)
    qed
    obtain env1 v' where g: "genvar (fst v) env (foldr fun_type (map fl_T args) U) = (env1, v')" by fastforce
    note gs = genvar_simps[OF g]
    define body where "body = list_comb v' (map (Bound \<circ> fl_j) args)"
    from rest False g obtain env2 where vu: "ok (vupdate (v, T) (types_abs Ts body) env1) env2"
      and nt: "ok (norm_term env2 (list_comb v' ts')) t'" and env': "env' = env2"
      by (auto simp: Let_def args_def ts'_def body_def)
    have nV: "\<not> is_Var (types_abs Ts body)" using Ts by (cases Ts) auto
    have up: "ok (update (v, T) (types_abs Ts body) env1) env2" using vu vupdate_nonVar[OF nV] by simp
    let ?y = "(fst v, maxidx env + 1)"
    have vb: "vars (types_abs Ts body) = vars v'" by (simp add: vars_types_abs_mi body_def list_comb_apps vars_apps)
    have yub: "vt_lookup (tenv env1) ?y = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env1) ?y \<noteq> None"
      then obtain b where "vt_lookup (tenv env) ?y = Some b" using gs(1) by auto
      from bound_le[OF this] show False by simp
    qed
    have lt: "maxidx env < maxidx env + 1" by simp
    have vy: "v \<noteq> ?y"
    proof
      assume "v = ?y"
      then have "snd v = maxidx env + 1" by (metis snd_conv)
      with v_le have "maxidx env + 1 \<le> maxidx env" by simp
      with lt show False by simp
    qed
    have ac2: "acyc env2"
    proof (rule acyc_update[OF up])
      show "acyc env1" using ac acyc_tenv[OF gs(1)] by simp
      show "(v, z) \<notin> (dep env1)\<^sup>*" if "(z, Z) \<in> vars (types_abs Ts body)" for z Z
        using that vb gs(4) not_dep_unbound[OF yub vy] by auto
    qed
    have mx2: "maxidx env2 = maxidx env + 1" using ok_update(4)[OF up] gs(3) by simp
    have new: "x = v" if "vt_lookup (tenv env2) x \<noteq> None" "vt_lookup (tenv env) x = None" for x
      using that ok_update(2)[OF up] gs(1) by (auto split: if_splits)
    have y2: "vt_lookup (tenv env2) ?y = None" using yub ok_update(2)[OF up] vy by auto
    have ev2: "vnames (evars env2) = insert v (vnames (vars v') \<union> vnames (evars env))"
      using evars_names_update[OF up] vb evars_tenv[OF gs(1)] by simp
    have bev2: "below (maxidx env2) (evars env2)"
      unfolding below_names ev2 mx2 using v_le bt(2) gs(4) by (auto simp: below_names)
    from norm_term_vars[OF nt] have nv: "vnames (vars t') \<subseteq> vnames (vars (list_comb v' ts')) \<union> vnames (evars env2)"
      by (simp add: nvars_ok_def)
    have "below (maxidx env2) (vars t')"
      unfolding below_names using nv vts'[of v'] bt(1) bev2 mx2 gs(4) by (fastforce simp: below_names)
    moreover have hd': "\<exists>T'. head_of t' = Var ?y T'"
      by (rule norm_term_head[OF nt _ y2]) (simp add: gs(4) list_comb_apps head_of_apps)
    ultimately show ?thesis using ac2 bev2 mx2 new y2 vT unfolding env' by (auto simp: below_def)
  qed
qed


lemma below_Un_iff: "below n (X \<union> Y) \<longleftrightarrow> below n X \<and> below n Y"
  by (auto simp: below_def)

lemma below_le: "below n X \<Longrightarrow> n \<le> m \<Longrightarrow> below m X"
  by (rule below_mono[OF _ order_refl])

theorem clean_ffpair_acyc:
  assumes cf: "okW (clean_ffpair al rb t u env tps) (env', tps')" and ac: "acyc env"
    and ht: "head_of t = Var v0 T0" and hu: "head_of u = Var w0 U0" and vw: "v0 \<noteq> w0"
    and ubt: "vt_lookup (tenv env) v0 = None" and ubu: "vt_lookup (tenv env) w0 = None"
    and bl: "below (maxidx env) (vars t \<union> vars u \<union> evars env)"
  shows "acyc env' \<and> maxidx env \<le> maxidx env' \<and> below (maxidx env') (evars env')"
proof -
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  have "(\<exists>env1 t' env2 u'. okW (clean_term banned env t) (env1, t') \<and>
      okW (clean_term banned env1 u) (env2, u') \<and>
      okW (handleW (do {env3 \<leftarrow> ff_assign al env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign al env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')) \<or>
      (env', tps') = (env, add_tpair rb t u tps)"
    using cf fb by (auto simp: clean_ffpair_def Let_def okW_handleW dest!: okW_CHANGE_FAIL_handler)
  then consider (fail) "(env', tps') = (env, add_tpair rb t u tps)"
    | (main) env1 t' env2 u' where "okW (clean_term banned env t) (env1, t')"
      "okW (clean_term banned env1 u) (env2, u')" "okW (handleW (do {env3 \<leftarrow> ff_assign al env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign al env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')"
    by blast
  then show ?thesis
  proof cases
    case fail
    then show ?thesis using ac bl by (auto simp: below_Un_iff)
  next
    case (main env1 t' env2 u')
    have bl1: "below (maxidx env) (vars t \<union> evars env)" using bl by (auto simp: below_Un_iff)
    from clean_term_acyc[OF main(1) ac ht ubt bl1] obtain h1 T1 where
      ac1: "acyc env1" and mx1: "maxidx env \<le> maxidx env1" and b1: "below (maxidx env1) (vars t' \<union> evars env1)"
      and new1: "\<And>x. vt_lookup (tenv env1) x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x = v0"
      and h1: "head_of t' = Var h1 T1" "vt_lookup (tenv env1) h1 = None" "h1 = v0 \<or> maxidx env < snd h1"
      by blast
    have ubu1: "vt_lookup (tenv env1) w0 = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env1) w0 \<noteq> None"
      from new1[OF this ubu] vw show False by simp
    qed
    have "(w0, U0) \<in> vars u"
    proof -
      have "vars (head_of u) \<subseteq> vars u" by (induction u) auto
      with hu show ?thesis by auto
    qed
    moreover have "below (maxidx env) (vars u)" using bl by (auto simp: below_Un_iff)
    ultimately have w0le: "snd w0 \<le> maxidx env" by (simp add: belowD)
    have blu: "below (maxidx env1) (vars u \<union> evars env1)"
      using bl b1 below_le[OF _ mx1] by (auto simp: below_Un_iff)
    from clean_term_acyc[OF main(2) ac1 hu ubu1 blu] obtain h2 T2 where
      ac2: "acyc env2" and mx2: "maxidx env1 \<le> maxidx env2" and b2: "below (maxidx env2) (vars u' \<union> evars env2)"
      and new2: "\<And>x. vt_lookup (tenv env2) x \<noteq> None \<Longrightarrow> vt_lookup (tenv env1) x = None \<Longrightarrow> x = w0"
      and h2: "head_of u' = Var h2 T2" "vt_lookup (tenv env2) h2 = None"
      by blast
    have h1u: "vt_lookup (tenv env2) h1 = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env2) h1 \<noteq> None"
      from new2[OF this h1(2)] have "h1 = w0" .
      with h1(3) vw w0le show False by auto
    qed
    have bt': "below (maxidx env2) (vars t')" using b1 below_le[OF _ mx2] by (auto simp: below_Un_iff)
    have ball: "below (maxidx env2) (vars t' \<union> vars u' \<union> evars env2)" using bt' b2 by (auto simp: below_Un_iff)
    have fa: "acyc env3 \<and> maxidx env \<le> maxidx env3 \<and> below (maxidx env3) (evars env3)"
      if "okW (ff_assign al env2 rb' s s') env3" "\<And>v T. head_of s = Var v T \<Longrightarrow> vt_lookup (tenv env2) v = None"
        "below (maxidx env2) (vars s \<union> vars s' \<union> evars env2)" for s s' env3
    proof -
      have "acyc env3 \<and> maxidx env2 \<le> maxidx env3 \<and>
          vnames (evars env3) \<subseteq> vnames (evars env2) \<union> vnames (vars s) \<union> vnames (vars s')"
      proof (rule ff_assign_acyc[OF that(1) ac2])
        fix v T assume "head_of s = Var v T"
        then show "vt_lookup (tenv env2) v = None" by (rule that(2))
      qed
      then have r: "acyc env3" "maxidx env2 \<le> maxidx env3"
        "vnames (evars env3) \<subseteq> vnames (evars env2) \<union> vnames (vars s) \<union> vnames (vars s')" by blast+
      have "below (maxidx env3) (evars env3)"
        using r(3) that(3) below_le[OF _ r(2)] unfolding below_names by blast
      with r mx1 mx2 show ?thesis by simp
    qed
    from ff_handler[OF main(3)] consider (fa1) env3 where "okW (ff_assign al env2 rb' t' u') env3"
        "(env', tps') = (env3, tps)"
      | (fa2) env3 where "okW (ff_assign al env2 rb' u' t') env3" "(env', tps') = (env3, tps)"
      | (keep) "(env', tps') = (env2, add_tpair rb' t' u' tps)"
      by blast
    then show ?thesis
    proof cases
      case (fa1 env3)
      have "acyc env3 \<and> maxidx env \<le> maxidx env3 \<and> below (maxidx env3) (evars env3)"
        by (rule fa[OF fa1(1) _ ball]) (use h1(1) h1u in simp)
      with fa1(2) show ?thesis by simp
    next
      case (fa2 env3)
      have "acyc env3 \<and> maxidx env \<le> maxidx env3 \<and> below (maxidx env3) (evars env3)"
        by (rule fa[OF fa2(1)]) (use h2 ball in \<open>auto simp: below_Un_iff\<close>)
      with fa2(2) show ?thesis by simp
    next
      case keep
      with ac2 mx1 mx2 b2 show ?thesis by (auto simp: below_Un_iff)
    qed
  qed
qed

theorem add_ffpair_acyc:
  assumes a: "okW (add_ffpair al dp (env, tps)) (env', tps')" and ac: "acyc env"
    and bl: "below (maxidx env) (dvars [dp] \<union> evars env)"
  shows "acyc env' \<and> maxidx env \<le> maxidx env' \<and> below (maxidx env') (evars env')"
proof -
  obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
  from a dp obtain t u where nt: "ok (norm_term env t0) t" and nu: "ok (norm_term env u0) u"
    and rest: "okW (case (head_of t, head_of u) of
        (Var v T, Var w U) \<Rightarrow>
          if v = w then
            (if T = U then returnW (env, add_tpair rb t u tps)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair al rb u t env tps
          else clean_ffpair al rb t u env tps
      | _ \<Rightarrow> raiseW (PExn (Term_Error (STR ''add_ffpair: Vars expected'') [t, u]))) (env', tps')"
    by (auto simp: add_ffpair_def)
  note n1 = norm_term_vars[OF nt, unfolded nvars_ok_def] and n2 = norm_term_vars[OF nu, unfolded nvars_ok_def]
  have b0: "below (maxidx env) (vars t0 \<union> vars u0 \<union> evars env)" using bl by (simp add: dvars_def dp)
  have btu: "below (maxidx env) (vars t \<union> vars u \<union> evars env)"
    using b0 n1 n2 unfolding below_names by blast
  have ub: "vt_lookup (tenv env) x = None" if "(x, X) \<in> vars s" "s = t \<or> s = u" for x X s
    using that n1 n2 by auto
  have hv: "(x, X) \<in> vars s" if "head_of s = Var x X" for s x X
  proof -
    have "vars (head_of s) \<subseteq> vars s" by (induction s) auto
    with that show ?thesis by auto
  qed
  have "\<exists>v T w U. head_of t = Var v T \<and> head_of u = Var w U \<and>
      ((v = w \<and> env' = env) \<or> (v \<noteq> w \<and> (okW (clean_ffpair al rb u t env tps) (env', tps') \<or>
        okW (clean_ffpair al rb t u env tps) (env', tps'))))"
    using rest by (auto split: pterm.splits if_splits)
  then obtain v T w U where ht: "head_of t = Var v T" and hu: "head_of u = Var w U"
    and c: "(v = w \<and> env' = env) \<or> (v \<noteq> w \<and> (okW (clean_ffpair al rb u t env tps) (env', tps') \<or>
        okW (clean_ffpair al rb t u env tps) (env', tps')))"
    by blast
  have ubv: "vt_lookup (tenv env) v = None" by (rule ub[OF hv[OF ht]]) simp
  have ubw: "vt_lookup (tenv env) w = None" by (rule ub[OF hv[OF hu]]) simp
  from c show ?thesis
  proof (elim disjE conjE)
    assume "env' = env"
    then show ?thesis using ac btu by (auto simp: below_Un_iff)
  next
    assume vw: "v \<noteq> w" and cf: "okW (clean_ffpair al rb u t env tps) (env', tps')"
    have "below (maxidx env) (vars u \<union> vars t \<union> evars env)" using btu by (auto simp: below_Un_iff)
    from clean_ffpair_acyc[OF cf ac hu ht vw[symmetric] ubw ubv this] show ?thesis .
  next
    assume vw: "v \<noteq> w" and cf: "okW (clean_ffpair al rb t u env tps) (env', tps')"
    from clean_ffpair_acyc[OF cf ac ht hu vw ubv ubw btu] show ?thesis .
  qed
qed

theorem foldrW_add_ffpair_acyc:
  "okW (foldrW (add_ffpair al) ffs (env, tps)) (env', tps') \<Longrightarrow> acyc env \<Longrightarrow>
    below (maxidx env) (X \<union> dvars ffs \<union> evars env) \<Longrightarrow>
    acyc env' \<and> maxidx env \<le> maxidx env' \<and> below (maxidx env') (X \<union> evars env')"
proof (induction ffs arbitrary: env' tps' X)
  case Nil
  then show ?case by (simp add: dvars_def)
next
  case (Cons dp ffs)
  from Cons.prems(1) obtain env1 tps1 where f: "okW (foldrW (add_ffpair al) ffs (env, tps)) (env1, tps1)"
    and a: "okW (add_ffpair al dp (env1, tps1)) (env', tps')" by auto
  have "below (maxidx env) ((X \<union> dvars [dp]) \<union> dvars ffs \<union> evars env)"
    using Cons.prems(3) by (simp add: dvars_def Un_ac)
  from Cons.IH[OF f Cons.prems(2) this] have I: "acyc env1" "maxidx env \<le> maxidx env1"
    "below (maxidx env1) (X \<union> dvars [dp] \<union> evars env1)" by blast+
  from add_ffpair_acyc[OF a I(1)] I(3) have A: "acyc env'" "maxidx env1 \<le> maxidx env'" "below (maxidx env') (evars env')"
    by (auto simp: below_Un_iff)
  have "below (maxidx env') X" using I(3) below_le[OF _ A(2)] by (auto simp: below_Un_iff)
  with A I(2) show ?case by (auto simp: below_Un_iff)
qed


subsection \<open>The search\<close>

theorem MATCH_tyinv_acyc:
  assumes cfg: "cfg_alg cfg = alg" and ni: "ninv env (dp # dps)" and ac: "acyc env" and sh: "frs_shape dp"
    and m: "okW (MATCH cfg env dp dps) ms" and ev: "ev cfg ms (El_E env2 dps2)"
  shows "(\<exists>A K. tyinv A K env2 dps2) \<and> acyc env2"
proof -
  from ni obtain A K where gt: "gtyped env (dp # dps)" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env (dp # dps)"
    unfolding ninv_def tyinv_def by blast
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have mo: "MATCH_ok env dp" using ninv_MATCH_ok[OF ni[unfolded dp] sh[unfolded dp]] by (simp add: dp)
  have sq: "seqinv (GE env (dp # dps)) ms" by (rule MATCH_sound[OF m mo])
  have ts: "tseq True (tvars_env (tyenv env) \<union> A) ms" by (rule MATCH_tseq[OF m mo cfg fK ei tk gt]) (simp add: ac)
  from tseq_ev[OF cfg ev ts sq gt] obtain env' dps' where e: "El_E env2 dps2 = El_E env' dps'"
    and t: "tst True (tvars_env (tyenv env) \<union> A) env' dps'" by blast
  from e have "env2 = env'" "dps2 = dps'" by simp_all
  with t tst_tyinv[OF t] show ?thesis by (simp add: tst_def)
qed

text \<open>Every result of the search comes from a node of the search by \<open>SIMPL\<close> and the flex-flex
  treatment:\<close>

lemma ev_sgood_R:
  assumes NI_match: "\<And>env dps env' ffs dp frs. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> MATCH_ok env' dp"
    and NI_step: "\<And>env dps env' ffs dp frs ms env2 dps2. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> okW (MATCH cfg env' dp (frs @ ffs)) ms \<Longrightarrow>
      ev cfg ms (El_E env2 dps2) \<Longrightarrow> NI env2 dps2"
  shows "ev cfg s x \<Longrightarrow> sgood NI cfg env0 dps0 s \<Longrightarrow> x = El_R envR tps \<Longrightarrow>
    \<exists>env dps env1 ffs. NI env dps \<and> okW (SIMPL (cfg_alg cfg) env dps) (env1, ffs, []) \<and>
      okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env1, [])) (envR, tps)"
proof (induction arbitrary: envR tps rule: ev.induct)
  case (au_tail reseq x td env dps)
  from au_tail.prems(1) show ?case by (rule sgood_AddUnifyE) (rule au_tail.IH[OF _ au_tail.prems(2)])
next
  case (au_res env dps env' ffs r td reseq)
  from au_res.prems(1) have ni: "NI env dps" by (rule sgood_AddUnifyE)
  from au_res.prems(2) have r: "r = (envR, tps)" by (cases r) simp
  with ni au_res.hyps show ?case by blast
next
  case (au_match env dps env' ffs dp frs td ms reseq x)
  from au_match.prems(1) obtain d0: "dstep env0 dps0 env dps" and ni: "NI env dps"
    and sR: "sgood NI cfg env0 dps0 reseq"
    by (rule sgood_AddUnifyE) blast
  have d1: "dstep env dps env' (dp # frs @ ffs)" using SIMPL_sound[OF au_match.hyps(1)] by simp
  have mo: "MATCH_ok env' dp" by (rule NI_match[OF ni au_match.hyps(1)])
  have sq: "seqinv (GE env' (dp # frs @ ffs)) ms" by (rule MATCH_sound[OF au_match.hyps(3) mo])
  have "sgood NI cfg env0 dps0 (S_ItRight (td + 1) ms reseq)"
  proof (rule sgood.ItRight[OF _ sR])
    fix y assume y: "ev cfg ms y"
    from ev_sound[OF y sq] obtain env2 dps2 where y2: "y = El_E env2 dps2" and d2: "dstep env' (dp # frs @ ffs) env2 dps2"
      by (cases y) auto
    have "NI env2 dps2" by (rule NI_step[OF ni au_match.hyps(1,3) y[unfolded y2]])
    with y2 dstep_trans[OF dstep_trans[OF d0 d1] d2]
    show "\<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps" by blast
  qed
  then show ?case by (rule au_match.IH[OF _ au_match.prems(2)])
next
  case (ir_tail yq x td xq)
  from ir_tail.prems(1) show ?case by (rule sgood_ItRightE) (rule ir_tail.IH[OF _ ir_tail.prems(2)])
next
  case (ir_head xq env dps td x yq)
  from ir_head.prems(1) obtain h: "\<And>y. ev cfg xq y \<Longrightarrow> \<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps"
    by (rule sgood_ItRightE) blast
  from h[OF ir_head.hyps(1)] have "dstep env0 dps0 env dps" "NI env dps" by auto
  then have "sgood NI cfg env0 dps0 (S_AddUnify td env dps S_Empty)" by (intro sgood.AddUnify sgood.Empty)
  from ir_head.IH(2)[OF this ir_head.prems(2)] show ?case .
qed (auto elim: sgood.cases)

text \<open>
  The acyclicity of the results: if the input environment is acyclic and the input satisfies
  the node invariant, the environment of every unifier that the search enumerates is acyclic,
  and its variables are below its maximal index. There is no hypothesis on the names of the
  variables.
\<close>

theorem hounifiers_acyc:
  assumes cfg: "cfg_alg cfg = alg"
    and NI0: "ninv env (map (\<lambda>(t, u). (rb, t, u)) tus)" and ac0: "acyc env"
    and ev: "ev cfg (hounifiers rb env tus) (El_R env' tps)"
  shows "acyc env' \<and> below (maxidx env') (evars env')"
proof -
  let ?NI = "\<lambda>env dps. ninv env dps \<and> acyc env"
  let ?dps = "map (\<lambda>(t, u). (rb, t, u)) tus"
  have NI_match: "MATCH_ok env1 dp"
    if "?NI e dps" "okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, dp # frs)" for e dps env1 ffs dp frs
    using ninv_SIMPL_MATCH_ok[OF cfg _ that(2)] that(1) by blast
  have NI_step: "?NI env2 dps2"
    if "?NI e dps" "okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, dp # frs)"
      "okW (MATCH cfg env1 dp (frs @ ffs)) ms" "ev cfg ms (El_E env2 dps2)" for e dps env1 ffs dp frs ms env2 dps2
  proof -
    have ni: "ninv env1 (dp # frs @ ffs)" by (rule ninv_SIMPL[OF cfg _ that(2)]) (use that(1) in blast)
    have ac1: "acyc env1" using SIMPL_acyc[OF that(2)] that(1) by blast
    have sh: "frs_shape dp" by (rule SIMPL_frs_shape[OF that(2)])
    have mo: "MATCH_ok env1 dp" by (rule NI_match[OF that(1,2)])
    from MATCH_tyinv_acyc[OF cfg ni ac1 sh that(3,4)] have ty: "\<exists>A K. tyinv A K env2 dps2" "acyc env2" by blast+
    have sq: "seqinv (GE env1 (dp # frs @ ffs)) ms" by (rule MATCH_sound[OF that(3) mo])
    from ev_sound[OF that(4) sq] have d: "dstep env1 (dp # frs @ ffs) env2 dps2" by simp
    have "gtyped env2 dps2" by (rule gtyped_dstep[OF d]) (use ni in \<open>simp add: ninv_def\<close>)
    with ty show ?thesis unfolding ninv_def by blast
  qed
  have sg: "sgood ?NI cfg env ?dps (S_AddUnify 1 env ?dps S_Empty)"
    by (intro sgood.AddUnify sgood.Empty dstep_refl) (use NI0 ac0 in blast)
  have NM: "\<And>e dps env1 ffs dp frs. ?NI e dps \<Longrightarrow> okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, dp # frs) \<Longrightarrow>
      MATCH_ok env1 dp"
    by (rule NI_match)
  have NS: "\<And>e dps env1 ffs dp frs ms env2 dps2. ?NI e dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, dp # frs) \<Longrightarrow> okW (MATCH cfg env1 dp (frs @ ffs)) ms \<Longrightarrow>
      ev cfg ms (El_E env2 dps2) \<Longrightarrow> ?NI env2 dps2"
    by (rule NI_step)
  have "\<exists>e dps env1 ffs. ?NI e dps \<and> okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, []) \<and>
      okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env1, [])) (env', tps)"
    by (rule ev_sgood_R[where NI = ?NI, OF NM NS ev[unfolded hounifiers_def] sg refl])
  then obtain e dps env1 ffs where ni: "?NI e dps" and s: "okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, [])"
    and f: "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env1, [])) (env', tps)"
    by blast
  have ac1: "acyc env1" using SIMPL_acyc[OF s] ni by blast
  from ni obtain A K where gt: "gtyped e dps" and fK: "finite K" and ei: "einv A K (tyonly e)"
    and tk: "tknown A e dps"
    unfolding ninv_def tyinv_def by blast
  from SIMPL_inv[OF fK s[unfolded cfg] ei tk gt] have ei1: "einv A K (tyonly env1)" by blast
  have gt1: "gtyped env1 ([] @ ffs)" by (rule gtyped_dstep[OF SIMPL_sound[OF s] gt])
  have "below (maxidx env1) (dvars ffs \<union> evars env1)" using state_below[OF gt1 ei1] by simp
  then have "below (maxidx env1) ({} \<union> dvars ffs \<union> evars env1)" by simp
  from foldrW_add_ffpair_acyc[OF f ac1 this] show ?thesis by simp
qed


text \<open>
  Hence the steps of the search have typed solutions: for a type instantiation that solves the
  type environment of a result, the ghost solution of the result (\<^const>\<open>gsol\<close>) solves its
  bindings, and if it also solves the remaining flex-flex pairs, it solves the input pairs.
\<close>

theorem hounifiers_typed_solution:
  assumes cfg: "cfg_alg cfg = alg"
    and NI0: "ninv env (map (\<lambda>(t, u). (rb, t, u)) tus)" and ac0: "acyc env"
    and ev: "ev cfg (hounifiers rb env tus) (El_R env' tps)"
    and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env') \<rho>" and wte: "wt_env \<rho> env"
    and dt: "dtyped \<rho> (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and vi: "vinv \<rho> env (dvars (map (\<lambda>(t, u). (rb, t, u)) tus))"
  shows "acyc env'" "solution \<rho> (gsol \<rho> env') env'"
    "dsolved \<rho> (gsol \<rho> env') (tdps tps) \<Longrightarrow> dsolved \<rho> (gsol \<rho> env') (map (\<lambda>(t, u). (rb, t, u)) tus)"
proof -
  let ?dps = "map (\<lambda>(t, u). (rb, t, u)) tus" and ?\<sigma> = "gsol \<rho> env'"
  have ds: "dstep env ?dps env' (tdps tps)" using hounifiers_ev_sound_loose[OF cfg NI0 ev] by simp
  show ac: "acyc env'" using hounifiers_acyc[OF cfg NI0 ac0 ev] by blast
  from dstepD_ghosts[OF ds \<rho>(2) extends_refl wte dt, of "{}"] vi
  have wte': "wt_env \<rho> env'" and dt': "dtyped \<rho> (tdps tps)"
    and de: "deqv (ebinds \<rho> env' \<union> dp_eqs \<rho> (tdps tps)) \<rho> ?dps"
    by simp_all
  show sol: "solution \<rho> ?\<sigma> env'" by (rule gsol_solution[OF ac wte' \<rho>])
  assume sd: "dsolved \<rho> ?\<sigma> (tdps tps)"
  have E: "vsubst ?\<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst ?\<sigma> r"
    if "(l, r) \<in> {(l, r) \<in> ebinds \<rho> env' \<union> dp_eqs \<rho> (tdps tps). \<exists>e T. e \<turnstile> l : T \<and> e \<turnstile> r : T}" for l r
  proof -
    from that obtain e T where lr: "(l, r) \<in> ebinds \<rho> env' \<union> dp_eqs \<rho> (tdps tps)" "e \<turnstile> l : T" "e \<turnstile> r : T"
      by blast
    from lr(1) show ?thesis
    proof
      assume "(l, r) \<in> ebinds \<rho> env'"
      from gsol_ebinds[OF ac wte' \<rho> this lr(2,3)] show ?thesis .
    next
      assume "(l, r) \<in> dp_eqs \<rho> (tdps tps)"
      then obtain rb' t u where p: "(rb', t, u) \<in> set (tdps tps)" and l: "l = inst \<rho> (abs_list (rev rb') t)"
        and r: "r = inst \<rho> (abs_list (rev rb') u)"
        by (auto simp: dp_eqs_def)
      from sd p have "ap \<rho> ?\<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> ?\<sigma> u" by (auto simp: dsolved_def)
      from dsolved_closed[OF dtyped_mem[OF dt' p] solutionD(3)[OF sol] this] show ?thesis unfolding l r .
    qed
  qed
  have "ap \<rho> ?\<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> ?\<sigma> u" if p: "(rb', t, u) \<in> set ?dps" for rb' t u
  proof -
    from dt p obtain e T where "bs_env \<rho> e rb'" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
      by (fastforce simp: dtyped_def)
    with de p have "eqv (ebinds \<rho> env' \<union> dp_eqs \<rho> (tdps tps)) e (inst \<rho> t) (inst \<rho> u)" by (auto simp: deqv_def)
    from eqv_vsubst[OF eqv_typed_pairs[OF this] solutionD(3)[OF sol] E] show ?thesis by (simp add: ap_def)
  qed
  then show "dsolved \<rho> ?\<sigma> ?dps" by (auto simp: dsolved_def)
qed

end

end
