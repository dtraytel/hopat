section \<open>Invariants of the Termination of Pattern Unification\<close>

theory Pattern_Termination_Inv
  imports Pattern_Termination_Base
begin

text \<open>
  The invariants that the termination proof of pattern unification (theory
  \<open>Pattern_Termination_Base\<close>) keeps, and the facts on new variables, bindings and projection that
  it uses.
\<close>

subsection \<open>New variables and bindings keep the invariant\<close>

context pure_sig_gen
begin

lemma einv_genvar: "genvar a env T = (env', G) \<Longrightarrow> einv A K env \<Longrightarrow> einv A K env'"
proof -
  assume g: "genvar a env T = (env', G)" and ei: "einv A K env"
  note gs = genvar_simps[OF g] and e = einvD[OF ei]
  have "bbelow env'" by (rule bbelow_mono[OF e(5)]) (simp_all add: gs)
  moreover have "closed_env env'" using e(4) by (simp add: closed_env_def gs)
  ultimately show ?thesis
    using ei tvinv_genvar[OF g e(1)] acyc_genvar[OF g] by (simp add: einv_def gs)
qed

lemma bbelow_update:
  assumes "bbelow env" "ok (update (F, T) u env) env'" "snd F \<le> maxidx env"
  shows "bbelow env'"
  unfolding bbelow_def
proof (intro allI impI)
  note o = ok_update[OF assms(2)]
  fix x b assume "vt_lookup (tenv env') x = Some b"
  then have "x = F \<or> vt_lookup (tenv env) x = Some b" using o(2) by (simp split: if_splits)
  then show "snd x \<le> maxidx env'"
  proof
    assume "x = F"
    with assms(3) o(4) show ?thesis by simp
  next
    assume "vt_lookup (tenv env) x = Some b"
    from bbelowD[OF assms(1) this] o(4) show ?thesis by simp
  qed
qed

lemma closed_env_update: "closed_env env \<Longrightarrow> ok (update (F, T) u env) env' \<Longrightarrow> closed u \<Longrightarrow> closed_env env'"
  using ok_update(2)[of F T u env env'] by (simp add: closed_env_def)

lemma einv_update:
  assumes ei: "einv A K env" and upd: "ok (update (F, T) u env) env'"
    and acy: "\<And>y U. (y, U) \<in> vars u \<Longrightarrow> (F, y) \<notin> (dep env)\<^sup>*" and cl: "closed u"
    and F: "snd F \<le> maxidx env" and tv: "tvars T \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "einv A K env'"
proof -
  note e = einvD[OF ei] and o = ok_update[OF upd]
  have "tvinv A env'" by (rule tvinv_update[OF upd e(1) tv])
  moreover have "acyc env'" by (rule acyc_update[OF upd e(3) acy])
  moreover have "closed_env env'" by (rule closed_env_update[OF e(4) upd cl])
  moreover have "bbelow env'" by (rule bbelow_update[OF e(5) upd F])
  ultimately show ?thesis using ei by (simp add: einv_def o(3))
qed

lemma loose_bvar_app_Var: "\<not> loose_bvar (app (Var x T) ks) n \<longleftrightarrow> (\<forall>k\<in>set ks. k < n)"
  by (auto simp: app_apps loose_bvar_apps)

lemma not_dep_unbound:
  "vt_lookup (tenv env) G = None \<Longrightarrow> F \<noteq> G \<Longrightarrow> (F, G) \<notin> (dep env)\<^sup>*"
  by (auto elim: rtranclE elim!: depE)

end

subsection \<open>Auxiliary facts on projection\<close>

context pure_sig_gen
begin

lemma beta_vars: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> vars t \<subseteq> vars s"
  by (induction rule: beta.induct) (use vars_subst in auto)

lemma beta_reds_vars: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> vars t \<subseteq> vars s"
  by (induction rule: rtranclp_induct) (use beta_vars in auto)

lemma idx_result: "idx xs j = return (bidx xs j) \<or> idx xs j = raise (Unif No_Trace)"
  by (induction xs) auto

lemma try_trans_return: "\<exists>y. try_trans xs d i = return y"
  using idx_result[of xs "i - d"] by (auto simp: try_trans_def)

lemma trans_result: "(\<exists>j. trans xs d i = return j) \<or> trans xs d i = raise (Unif No_Trace)"
  using idx_result[of xs "i - d"] by (auto simp: trans_def)

text \<open>The head of a head normal form, if a variable, is unbound:\<close>

lemma head_norm_Var_head:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> fst (strip_comb t') = Var F Fty \<Longrightarrow> vt_lookup (tenv env) F = None"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vt_lookup (tenv env) F = None" if "ok (hn env u) u'" "fst (strip_comb u') = Var F Fty" for u u'
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest Var have "t' = Var x T" by simp
      with "1.prems"(2) have "F = x" by (simp add: strip_comb_def)
      with ok_lookup_None[of env x T] lr None show ?thesis by simp
    next
      case (Some u)
      with rest IH "1.prems"(2) show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with h "1.prems"(2) show ?thesis by (auto simp: strip_comb_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where "f = Abs a T body" by (cases f) auto
      with h App IH "1.prems"(2) show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where "nf = Abs a T body" by (cases nf) auto
        with rest IH "1.prems"(2) show ?thesis by simp
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) simp_all
        with IH[OF nf] "1.prems"(2) show ?thesis by (simp add: strip_comb_App)
      qed
    qed
  qed (use h "1.prems"(2) in \<open>auto simp: strip_comb_def\<close>)
qed


text \<open>The well-typedness invariant after projection follows from soundness:\<close>

lemma pr_winv:
  assumes pr: "pr xs s env d bs = Some (Ok (u, env'))" and wi: "winv env X" and vs: "vars s \<subseteq> X \<union> evars env"
    and ty: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T"
    and th: "tyenv env' = tyenv env" and d: "0 \<le> d" and xs: "\<forall>x\<in>set xs. 0 \<le> x"
  shows "winv env' X"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume ts: "tsol (tyenv env') \<rho>" and c: "cert_inst \<rho>"
  have ts0: "tsol (tyenv env) \<rho>" using ts th by simp
  from winvD[OF wi ts0 c] have w: "wt_env \<rho> env" "vinv \<rho> env X" by blast+
  from ty[OF ts0 c] obtain e T where bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> s : T" by blast
  have "X \<union> vars s \<union> evars env = X \<union> evars env" using vs by blast
  then have vi: "vinv \<rho> env (X \<union> vars s)" using w(2) by (simp add: vinv_def)
  note p = pr_sound[OF pr refl d xs]
  from p[unfolded pr_ok_def, THEN conjunct2, THEN conjunct2, rule_format, OF ts extends_refl w(1) bs tys vi]
  have r: "wt_env \<rho> env'" "vinv \<rho> env' (X \<union> vars u)" by blast+
  from r(2) have "vcons \<rho> (X \<union> vars u \<union> evars env')" "below (maxidx env') (X \<union> vars u \<union> evars env')"
    by (simp_all add: vinv_def)
  then have "vinv \<rho> env' X" unfolding vinv_def
    using vcons_mono[of \<rho> "X \<union> vars u \<union> evars env'" "X \<union> evars env'"]
      below_mono[of "maxidx env'" "X \<union> vars u \<union> evars env'" "X \<union> evars env'" "maxidx env'"] by blast
  with r(1) show "wt_env \<rho> env' \<and> vinv \<rho> env' X" by blast
qed

lemma extends_maxidx: "extends env env' \<Longrightarrow> maxidx env \<le> maxidx env'"
  by (simp add: extends_def)

text \<open>Projecting the arguments of a rigid head, threading the environment:\<close>

lemma mapAccM_pr_extends:
  assumes "ok (mapAccM (\<lambda>s env. pr xs s env d bs) ts env) (us, env')" "0 \<le> d" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "extends env env'"
proof -
  have "prs_ok xs ts env d bs us env'"
    by (rule mapAccM_pr_ok[where f = pr, OF assms(1)]) (rule pr_sound[OF _ refl assms(2,3)])
  then show ?thesis by (simp add: prs_ok_def)
qed

lemma pr_unfold: "pr xs s env d bs = head_norm env s \<bind> (\<lambda>s'. pr_step pr xs s' env d bs)"
  unfolding pr_step_def by (rule pr.simps)

end

subsection \<open>Well-formed problems of pattern unification\<close>

context pure_sig_gen
begin


subsubsection \<open>Problems\<close>

text \<open>
  A problem \<open>s =?= t\<close> under the binders \<open>bs\<close> is well-formed for the variables \<open>X\<close> if its
  variables are in \<open>X\<close> or the environment, its type variables are known, its loose bound variables
  are bound by \<open>bs\<close>, and it is well-typed for every certified solution of the type environment.
\<close>

definition upok :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "upok A env bs X s t \<longleftrightarrow> vars s \<union> vars t \<subseteq> X \<union> evars env \<and>
    ttvars s \<union> ttvars t \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    \<not> loose_bvar s (ilength bs) \<and> \<not> loose_bvar t (ilength bs) \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T))"

lemma upokD:
  assumes "upok A env bs X s t"
  shows "vars s \<subseteq> X \<union> evars env" "vars t \<subseteq> X \<union> evars env"
    "ttvars s \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<not> loose_bvar s (ilength bs)" "\<not> loose_bvar t (ilength bs)"
    "tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
  using assms unfolding upok_def by blast+

lemma upok_sym: "upok A env bs X s t \<Longrightarrow> upok A env bs X t s"
  unfolding upok_def by blast

lemma vinv_evars: "vars s \<union> vars t \<subseteq> X \<union> evars env \<Longrightarrow> vinv \<rho> env (X \<union> vars s \<union> vars t) \<longleftrightarrow> vinv \<rho> env X"
proof -
  assume "vars s \<union> vars t \<subseteq> X \<union> evars env"
  then have "X \<union> vars s \<union> vars t \<union> evars env = X \<union> evars env" by blast
  then show ?thesis by (simp add: vinv_def)
qed

subsubsection \<open>The lexicographic order of the measures\<close>

abbreviation ulex :: "((nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat)) set" where
  "ulex \<equiv> less_than <*lex*> less_than <*lex*> less_than"

lemma vt_eqI: "(\<And>k. vt_lookup t k = vt_lookup t' k) \<Longrightarrow> t = t'"
  by transfer auto

lemma textends_antisym: "textends \<theta> \<theta>' \<Longrightarrow> textends \<theta>' \<theta> \<Longrightarrow> \<theta>' = \<theta>"
  unfolding textends_def by (rule vt_eqI) (metis not_None_eq)

subsubsection \<open>Auxiliary facts for the cases of unification\<close>

lemma winv_tyext:
  assumes "winv env X" "tenv env1 = tenv env" "textends (tyenv env) (tyenv env1)" "maxidx env \<le> maxidx env1"
  shows "winv env1 X"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume \<rho>: "tsol (tyenv env1) \<rho>" "cert_inst \<rho>"
  have "tsol (tyenv env) \<rho>" by (rule tsol_textends[OF assms(3) \<rho>(1)])
  from winvD[OF assms(1) this \<rho>(2)] have "wt_env \<rho> env" "vinv \<rho> env X" by blast+
  moreover have "evars env1 = evars env" using assms(2) by (simp add: evars_def bnds_def)
  ultimately show "wt_env \<rho> env1 \<and> vinv \<rho> env1 X"
    using assms(2,4) unfolding wt_env_def vinv_def by (auto intro: below_mono)
qed

lemma upok_mono:
  assumes "upok A env bs X s t" "extends env env1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
  shows "upok A env1 bs X s t"
  unfolding upok_def
proof (intro conjI allI impI)
  note pd = upokD[OF assms(1)]
  show "vars s \<union> vars t \<subseteq> X \<union> evars env1" using pd(1,2) evars_extends[OF assms(2)] by blast
  show "ttvars s \<union> ttvars t \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env1) \<union> A"
    using pd(3-6) assms(3) by blast
  show "\<not> loose_bvar s (ilength bs)" "\<not> loose_bvar t (ilength bs)" by (rule pd(7), rule pd(8))
  fix \<rho> assume "tsol (tyenv env1) \<rho>" "cert_inst \<rho>"
  then show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
    using pd(9) extends_tsol[OF _ assms(2)] by blast
qed

lemma cert_typ_tsubst_rev:
  assumes "cert_typ alg ar (tsubst \<rho> T)" "tcert alg (tvars T)"
  shows "wft ar T" "sorts_ok alg T"
proof -
  have "wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar T" by (induction T) auto
  then show "wft ar T" using assms(1) by (simp add: cert_typ_def)
  have "sorts_ok alg (tsubst \<rho> T) \<Longrightarrow> tcert alg (tvars T) \<Longrightarrow> sorts_ok alg T"
  proof (induction T)
    case (Type a Ts)
    then show ?case by (auto simp: tcert_def)
  qed (auto simp: tcert_def)
  then show "sorts_ok alg T" using assms by (simp add: cert_typ_def)
qed


lemma ubv_tenv: "tenv env1 = tenv env \<Longrightarrow> ubv env1 X = ubv env X"
  by (simp add: ubv_def evars_def bnds_def)

lemma lift_rigid: "rigid h \<Longrightarrow> rigid (lift h k)"
  by (cases h) simp_all

lemma strip_comb_head_cases:
  assumes "\<not> is_Abs h" "\<not> (\<exists>f u. h = f $ u)"
  shows "rigid h \<or> (\<exists>F T. h = Var F T)"
  using assms by (cases h) simp_all


lemma upok_app_flex:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "upok A env bs X s' t'"
    and st: "strip_comb s' = (Var F Fty, ss)" and io: "ints_of' env ss = return is"
  shows "upok A env bs X (app (Var F Fty) is) t'"
  unfolding upok_def
proof (intro conjI allI impI)
  note pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  have s': "s' = Var F Fty \<degree>\<degree> ss" by (rule strip_comb_apps[OF st])
  have io': "ok (ints_of' env ss) is" using io by (simp add: return_def)
  show "vars (app (Var F Fty) is) \<union> vars t' \<subseteq> X \<union> evars env" using pd(1,2) s' by (auto simp: vars_apps)
  show "ttvars (app (Var F Fty) is) \<union> ttvars t' \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(3-6) s' by (auto simp: ttvars_apps)
  have w0: "wt_env (tnorm_inst (tyenv env)) env" using winvD[OF wi r0] by blast
  have "\<forall>i\<in>set is. i < ilength bs"
    by (rule ints_of'_loose[OF io' w0 ilength_nonneg]) (use pd(7) s' in \<open>simp add: loose_bvar_apps\<close>)
  then show "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)" by (simp add: loose_bvar_app_Var)
  show "\<not> loose_bvar t' (ilength bs)" by (rule pd(8))
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s' : T" "e \<turnstile> inst \<rho> t' : T" using pd(9)[OF \<rho>] by blast
  have "wt_env \<rho> env" using winvD[OF wi \<rho>] by blast
  from flex_sound(1)[OF io' \<rho>(1) this ty(2)[unfolded s']] ty(1,3)
  show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<and> e \<turnstile> inst \<rho> t' : T" by blast
qed

definition pairs :: "(pterm \<times> pterm) list \<Rightarrow> pterm list" where
  "pairs ps = concat (map (\<lambda>(a, b). [a, b]) ps)"

lemma pairs_simps [simp]: "pairs [] = []" "pairs ((a, b) # ps) = a # b # pairs ps"
  by (simp_all add: pairs_def)

lemma sum_pairs_zip:
  "length ss = length ts \<Longrightarrow> sum_list (map (f :: pterm \<Rightarrow> nat) (pairs (zip ss ts))) = sum_list (map f ss) + sum_list (map f ts)"
  by (induction ss ts rule: list_induct2) (simp_all add: algebra_simps)

lemma zip_eq_ok: "length ss = length ts \<Longrightarrow> zip_eq ss ts = return (zip ss ts)"
  by (induction ss ts rule: list_induct2) simp_all

lemma ulex_le:
  assumes "((x, y, z), B) \<in> ulex" "x1 \<le> x" "x1 = x \<longrightarrow> y1 \<le> y" "x1 = x \<and> y1 = y \<longrightarrow> z1 \<le> z"
  shows "((x1, y1, z1), B) \<in> ulex"
proof -
  obtain bx "by" bz where B: "B = (bx, by, bz)" by (cases B) auto
  from assms(1) B have "x < bx \<or> x = bx \<and> (y < by \<or> y = by \<and> z < bz)" by simp
  with assms(2-4) B show ?thesis by auto
qed

text \<open>The arguments of rigid problems with the same head:\<close>

lemma rigid_args_pok:
  assumes p: "upok A env bs X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)" and rh: "rigid h" "rigid h'"
    and hh: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
    and r0: "tsol (tyenv env) \<rho>0" "cert_inst \<rho>0"
  shows "length ss = length ts" "\<forall>(a, b)\<in>set (zip ss ts). upok A env bs X a b"
proof -
  note pd = upokD[OF p]
  have tys: "\<exists>e Us. bs_env \<rho> e bs \<and> e \<tturnstile> map (inst \<rho>) ss : Us \<and> e \<tturnstile> map (inst \<rho>) ts : Us \<and>
      length ss = length ts" if \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T" "e \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T"
      using pd(9)[OF \<rho>] by blast
    from list_app_typeD[OF ty(2)[unfolded inst_apps]] obtain Us where
      u1: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> T" "e \<tturnstile> map (inst \<rho>) ss : Us" by blast
    from list_app_typeD[OF ty(3)[unfolded inst_apps hh[OF \<rho>, symmetric]]] obtain Us' where
      u2: "e \<turnstile> inst \<rho> h : Us' \<Rrightarrow> T" "e \<tturnstile> map (inst \<rho>) ts : Us'" by blast
    have at: "atom (inst \<rho> h)" by (rule rigid_inst[OF rh(1)])
    have "Us \<Rrightarrow> T = Us' \<Rrightarrow> T" using u1(1) u2(1) at by (cases "inst \<rho> h") (auto simp: rigid_iff)
    moreover from this have "length Us = length Us'" by (rule funs_eq_length)
    ultimately have "Us' = Us" using funs_eq by blast
    moreover have "length ss = length ts"
      using typings_nth[OF u1(2)] typings_nth[OF u2(2)] \<open>length Us = length Us'\<close> by simp
    ultimately show ?thesis using ty(1) u1(2) u2(2) by auto
  qed
  show len: "length ss = length ts" using tys[OF r0] by blast
  show "\<forall>(a, b)\<in>set (zip ss ts). upok A env bs X a b"
  proof (clarify)
    fix a b assume ab: "(a, b) \<in> set (zip ss ts)"
    then obtain i where i: "i < length ss" "a = ss ! i" "b = ts ! i" using len by (auto simp: set_zip)
    have a: "a \<in> set ss" and b: "b \<in> set ts" using i len by auto
    show "upok A env bs X a b"
      unfolding upok_def
    proof (intro conjI allI impI)
      show "vars a \<union> vars b \<subseteq> X \<union> evars env" using pd(1,2) a b by (auto simp: vars_apps)
      show "ttvars a \<union> ttvars b \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
        using pd(3-6) a b by (auto simp: ttvars_apps)
      show "\<not> loose_bvar a (ilength bs)" "\<not> loose_bvar b (ilength bs)"
        using pd(7,8) a b by (auto simp: loose_bvar_apps)
      fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
      from tys[OF \<rho>] obtain e Us where e: "bs_env \<rho> e bs" "e \<tturnstile> map (inst \<rho>) ss : Us"
        "e \<tturnstile> map (inst \<rho>) ts : Us" by blast
      from typings_nth[OF e(2)] typings_nth[OF e(3)] i len
      have "e \<turnstile> inst \<rho> a : Us ! i" "e \<turnstile> inst \<rho> b : Us ! i" by auto
      with e(1) show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> a : T \<and> e \<turnstile> inst \<rho> b : T" by blast
    qed
  qed
qed

lemma rigid_clash_Unif: "\<exists>u. rigid_clash bs h1 h2 = raise (Unif u)"
  by (auto simp: rigid_clash_def split: pterm.splits)


text \<open>The environments of the results of a list of problems extend the environment:\<close>

lemma foldM_unif_extends:
  "ok (foldM (\<lambda>(s, t) env. unif alg' bs s t env) ps env) env' \<Longrightarrow> extends env env'"
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain a b where p: "p = (a, b)" by force
  from Cons.prems obtain env1 where u: "ok (unif alg' bs a b env) env1"
    and f: "ok (foldM (\<lambda>(s, t) env. unif alg' bs s t env) ps env1) env'"
    by (auto simp: p)
  from step_okD(1)[OF unif_sound[OF u refl]] Cons.IH[OF f] show ?case by (rule extends_trans)
qed

lemma wf_ulex: "wf ulex"
  by (intro wf_lex_prod wf_less_than)

lemma finite_tvars_env: "finite (tvars_env \<theta>)"
proof -
  have "tvars_env \<theta> \<subseteq> (\<Union>v\<in>{v. vt_lookup \<theta> v \<noteq> None}.
      insert (v, fst (the (vt_lookup \<theta> v))) (tvars (snd (the (vt_lookup \<theta> v)))))"
    by (force simp: tvars_env_def)
  moreover have "finite (\<Union>v\<in>{v. vt_lookup \<theta> v \<noteq> None}.
      insert (v, fst (the (vt_lookup \<theta> v))) (tvars (snd (the (vt_lookup \<theta> v)))))"
    using finite_vt_lookup[of \<theta>] by simp
  ultimately show ?thesis by (rule finite_subset)
qed

end

end
