section \<open>Well-Formed Problems of Pattern Unification\<close>

theory Pattern_Term_Unif
  imports Pattern_Term_Proj
begin

context pure_sig_gen
begin


subsection \<open>Problems\<close>

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

subsection \<open>The lexicographic order of the measures\<close>

abbreviation ulex :: "((nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat)) set" where
  "ulex \<equiv> less_than <*lex*> less_than <*lex*> less_than"

lemma vt_eqI: "(\<And>k. vt_lookup t k = vt_lookup t' k) \<Longrightarrow> t = t'"
  by transfer auto

lemma textends_antisym: "textends \<theta> \<theta>' \<Longrightarrow> textends \<theta>' \<theta> \<Longrightarrow> \<theta>' = \<theta>"
  unfolding textends_def by (rule vt_eqI) (metis not_None_eq)

subsection \<open>Auxiliary facts for the cases of unification\<close>

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
