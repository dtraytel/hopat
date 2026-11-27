section \<open>Invariants of \<open>MATCH\<close>\<close>

theory Unify_Match_Inv
  imports Unify_Simpl_Termination "Unify_Soundness.Unify_Match_Base"
begin

text \<open>
  The invariants and auxiliary facts of the termination proof of \<^const>\<open>MATCH\<close> (theory
  \<open>Unify_Match_Termination\<close>): its new problems are in the invariant of
  \<^const>\<open>SIMPL\<close> (theory \<^theory>\<open>Unify_Correctness.Unify_Simpl_Inv\<close>); the arity guesses and the
  \<open>\<eta>\<close>-expansion keep the invariant, with new type variables for the guesses.
\<close>

context pure_sig_gen
begin

subsection \<open>The elements of the enumeration\<close>

text \<open>New problems in the invariant, for finite sets of variables and of type variables, which
  include the type variables \<open>A0\<close> of the original problem \<open>env0\<close>, with only type variables that
  are known in the original problem or new (\<^const>\<open>tnew\<close>):\<close>

definition mres :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> elem \<Rightarrow> bool" where
  "mres A0 env0 x \<longleftrightarrow> (\<exists>env dps A K X. x = El_E env dps \<and> finite X \<and> finite K \<and> A0 \<subseteq> A \<and>
    tnew A0 env0 A env \<and> sinv A K X env dps)"

lemma mres_mono:
  assumes "mres A1 env1 x" "A0 \<subseteq> A1" "tnew A0 env0 A1 env1" "maxidx env0 \<le> maxidx env1"
  shows "mres A0 env0 x"
proof -
  from assms(1) obtain env dps A K X where x: "x = El_E env dps" "finite X" "finite K" "A1 \<subseteq> A"
    "tnew A1 env1 A env" "sinv A K X env dps"
    unfolding mres_def by blast
  have "tnew A0 env0 A env" by (rule tnew_trans[OF assms(3) x(5) assms(4)])
  with x assms(2) show ?thesis unfolding mres_def by blast
qed

subsection \<open>Type unification keeps the invariant\<close>

lemma upok_Amono: "upok A env rb X t u \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> upok A' env rb X t u"
  unfolding upok_def by blast

lemma sinv_tyext:
  assumes "sinv A K X env dps" "einv A K env'" "tenv env' = tenv env" "textends (tyenv env) (tyenv env')"
    "maxidx env \<le> maxidx env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "sinv A K X env' dps"
proof -
  have ext: "extends env env'" using assms(3-5) by (simp add: extends_def)
  have "winv env' X" by (rule winv_tyext) (use assms in \<open>simp_all add: sinv_def\<close>)
  then show ?thesis using assms(1,2) upok_mono[OF _ ext assms(6)] unfolding sinv_def by blast
qed

lemma cunify_types_sinv:
  assumes fin: "finite K" and si: "sinv A K X env dps"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tnorm (tyenv env) T)"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tnorm (tyenv env) U)"
  shows "cuok (cunify_types alg T U env) (\<lambda>env'. sinv A K X env' dps \<and> tenv env' = tenv env \<and>
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U))"
proof -
  have ei: "einv A K env" using si by (simp add: sinv_def)
  have cT: "cert_typ alg ar (tsubst (rho0 env) T)" and cU: "cert_typ alg ar (tsubst (rho0 env) U)"
    using T(2) U(2) by simp_all
  show ?thesis
    using cunify_types_term[OF ei fin T(1) cert_typ_rev[OF ei cT T(1)] U(1) cert_typ_rev[OF ei cU U(1)]]
  proof (rule xokW_mono)
    fix env' assume "einv A K env' \<and> tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and>
      maxidx env \<le> maxidx env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))"
    then show "sinv A K X env' dps \<and> tenv env' = tenv env \<and> extends env env' \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
        (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
      using sinv_tyext[OF si] by (auto simp: extends_def)
  qed
qed


subsection \<open>New type variables\<close>

lemma sinv_gentvars:
  assumes si: "sinv A K X env dps" and g: "gentvars p env = (env1, Cs)"
  shows "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env1 dps"
proof -
  note gs = gentvars_simps[OF g]
  have ei: "einv (A \<union> ntv Cs) (K \<union> ntv Cs) env1" by (rule einv_gentvars[OF _ g]) (use si in \<open>simp add: sinv_def\<close>)
  have ext: "extends env env1" using gs by (simp add: extends_def)
  have "winv env1 X" by (rule winv_tyext) (use si gs in \<open>simp_all add: sinv_def\<close>)
  moreover have "upok (A \<union> ntv Cs) env1 rb X t u" if "(rb, t, u) \<in> set dps" for rb t u
  proof -
    from si that have "upok A env rb X t u" by (auto simp: sinv_def)
    then show ?thesis by (rule upok_mono[OF upok_Amono[OF _ Un_upper1] ext]) (simp add: gs(2))
  qed
  ultimately show ?thesis using ei unfolding sinv_def by blast
qed

text \<open>The new type variables have indices above the maximal index:\<close>

lemma tnew_gentvars:
  assumes g: "gentvars p env = (env1, Cs)"
  shows "tnew A env (A \<union> ntv Cs) env1"
proof -
  have "maxidx env < snd (fst q)" if "q \<in> ntv Cs" for q using ntv_gentvars(1)[OF g that] by simp
  then show ?thesis using gentvars_simps(2)[OF g] by (auto simp: tnew_def)
qed


subsection \<open>The \<open>\<eta>\<close>-expansion of a pair\<close>

lemma mf_ilength_rb: "ilength (rev (map f Es) @ rb) = ilength rb + ilength Es"
  by (simp add: ilength_eq integer_of_nat_eq_of_nat add.commute)

text \<open>The \<open>\<eta>\<close>-expansion of a pair by the missing argument types of its flexible side keeps the
  invariant; the flexible side then has all its arguments.\<close>

lemma sinv_eta_expand:
  assumes si: "sinv A K X env ((rb, t, u) # dps)" and st: "strip_comb t = (Var v T, targs)"
    and bt: "binder_types env T = return Ts"
  shows "length targs \<le> length Ts" "sinv A K X env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps)"
proof -
  have ei: "einv A K env" and p: "upok A env rb X t u" using si by (auto simp: sinv_def)
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p]
  let ?\<theta> = "tyenv env"
  from mf_binder_types_sound[OF bt[unfolded return_def] refl e(6)] obtain W where
    W: "\<And>\<rho>. tsol ?\<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W"
      "\<And>A B. tnorm ?\<theta> W \<noteq> A \<rightarrow>\<^sub>T B" "\<And>U. U \<in> set Ts \<Longrightarrow> tvars U \<subseteq> tvars T \<union> tvars_env ?\<theta>"
    by blast
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have tyt_gen: "\<exists>Us. e \<tturnstile> map (inst \<rho>) targs : Us \<and> Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W"
    if "e \<turnstile> inst \<rho> t : U" "tsol ?\<theta> \<rho>" for e \<rho> U
  proof -
    from that(1)[unfolded t inst_apps] obtain Us where tyv: "e \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U"
      and tyas: "e \<tturnstile> map (inst \<rho>) targs : Us"
      by (rule list_app_typeE)
    from tyv W(1)[OF that(2)] have "Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W" by auto
    with tyas show ?thesis by blast
  qed
  show len: "length targs \<le> length Ts"
  proof (rule ccontr)
    assume n: "\<not> length targs \<le> length Ts"
    from pd(9)[OF r0] obtain e U where "e \<turnstile> inst (rho0 env) t : U" by blast
    from tyt_gen[OF this r0(1)] obtain Us where Us: "e \<tturnstile> map (inst (rho0 env)) targs : Us"
      "Us \<Rrightarrow> U = map (tsubst (rho0 env)) Ts \<Rrightarrow> tsubst (rho0 env) W" by blast
    have lUs: "length Us = length targs" using typings_nth[OF Us(1)] by simp
    have "tsubst (rho0 env) W = drop (length (map (tsubst (rho0 env)) Ts)) Us \<Rrightarrow> U"
      by (rule funs_prefix[OF Us(2)[symmetric]]) (use n lUs in simp)
    then have "tnorm ?\<theta> W = drop (length Ts) Us \<Rrightarrow> U" by simp
    moreover obtain D Ds where "drop (length Ts) Us = D # Ds" using n lUs by (cases "drop (length Ts) Us") auto
    ultimately show False using W(2) by simp
  qed
  define Es where "Es = drop (length targs) Ts"
  define j where "j = length Es"
  let ?rb = "rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
  let ?x = "\<lambda>x. incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j"
  have lbx: "\<not> loose_bvar (?x x) (ilength ?rb)" if "\<not> loose_bvar x (ilength rb)" for x
    unfolding mf_ilength_rb
  proof -
    have "\<not> loose_bvar (incr_bv (ilength Es) 0 x) (ilength rb + ilength Es)"
      using loose_bvar_incr_bv[of "ilength Es" 0 "ilength rb" x] that by simp
    moreover have "\<not> loose_bvar b (ilength rb + ilength Es)" if "b \<in> set (bvs j)" for b
    proof -
      from that obtain x where x: "x < length Es" "b = Bound (integer_of_nat x)" by (auto simp: j_def)
      have "integer_of_nat x < ilength Es" using x by (simp add: ilength_eq integer_less_iff integer_of_nat.rep_eq)
      then have "integer_of_nat x < ilength rb + ilength Es"
        using ilength_nonneg[of rb] by (simp add: integer_less_iff integer_less_eq_iff plus_integer.rep_eq)
      then show ?thesis using x by simp
    qed
    ultimately show "\<not> loose_bvar (?x x) (ilength rb + ilength Es)" by (auto simp: loose_bvar_apps)
  qed
  have tyx: "\<exists>e' W'. bs_env \<rho> e' ?rb \<and> e' \<turnstile> inst \<rho> (?x t) : W' \<and> e' \<turnstile> inst \<rho> (?x u) : W'"
    if \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    from pd(9)[OF \<rho>] obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : U" and tyu: "e \<turnstile> inst \<rho> u : U"
      by blast
    from tyt_gen[OF tyt \<rho>(1)] obtain Us where Us: "e \<tturnstile> map (inst \<rho>) targs : Us"
      "Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W" by auto
    have lUs: "length Us = length targs" using typings_nth[OF Us(1)] by simp
    from funs_prefix[OF Us(2)] len lUs have U: "U = map (tsubst \<rho>) Es \<Rrightarrow> tsubst \<rho> W"
      by (simp add: Es_def drop_map)
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu pd(8)])
    then have cEs: "\<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T)" by (simp add: U cert_typ_funs)
    define e' where "e' = pushes e (map (tsubst \<rho>) Es)"
    have bs': "bs_env \<rho> e' ?rb" unfolding e'_def by (rule bs_env_pushes[OF bs cEs])
    have ty: "e' \<turnstile> inst \<rho> (?x x) : tsubst \<rho> W" if "e \<turnstile> inst \<rho> x : U" for x
      using list_app_typeI[OF typing_incr_pushes[OF that[unfolded U], of "map (tsubst \<rho>) Es", unfolded ilength_map]
          typings_bvs[of e "map (tsubst \<rho>) Es", unfolded length_map]]
      by (simp add: e'_def j_def inst_apps comp_def)
    show ?thesis using bs' ty[OF tyt] ty[OF tyu] by blast
  qed
  have tvT: "tvars T \<subseteq> ttvars t" using t by (simp add: ttvars_apps)
  have tvEs: "btvars ?rb \<subseteq> tvars_env ?\<theta> \<union> A"
  proof -
    have "tvars U \<subseteq> tvars_env ?\<theta> \<union> A" if "U \<in> set Es" for U
      using W(3)[of U] that tvT pd(3) by (auto simp: Es_def dest: in_set_dropD)
    then show ?thesis using pd(5) by (auto simp: btvars_def)
  qed
  have "upok A env ?rb X (?x t) (?x u)"
    unfolding upok_def
    using pd(1-4,6) lbx[OF pd(7)] lbx[OF pd(8)] tyx tvEs
    by (simp add: vars_apps ttvars_apps)
  then show "sinv A K X env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps)"
    using si unfolding eta_expand_dpair_eq Es_def[symmetric] j_def[symmetric] by (simp add: sinv_def)
qed


lemma cert_tnorm: "einv A K env \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> cert_typ alg ar (tnorm (tyenv env) T)"
  using cert_typ_tsubst[OF _ einv_rho0(2)] by simp

lemma is_Abs_incr_bv [simp]: "is_Abs (incr_bv n k t) \<longleftrightarrow> is_Abs t"
  by (cases t) auto

lemma rigid_incr_bv: "rigid h \<Longrightarrow> rigid (incr_bv n k h)"
  by (cases h) simp_all

lemma fr_shape_eta_expand:
  assumes "fr_shape env (rb, t, u)"
  shows "fr_shape env (eta_expand_dpair Es (rb, t, u))"
proof -
  from assms have f: "\<not> is_Abs t" "\<not> is_Abs u" "is_Var (head_of t)" "rigid (head_of u)" "hunb env (rb, t, u)"
    by (auto simp: fr_shape_def frs0_def)
  have ht: "incr_bv n 0 (head_of t) = head_of t" for n using f(3) by (cases "head_of t") auto
  have hu: "rigid (incr_bv n 0 (head_of u))" for n by (rule rigid_incr_bv[OF f(4)])
  show ?thesis using f hu unfolding eta_expand_dpair_eq fr_shape_def frs0_def hunb_def
    by (auto simp: is_Abs_apps head_of_apps head_of_incr_bv ht rigid_def split: pterm.splits)
qed

lemma fr_shape_strip_comb:
  assumes "fr_shape env (rb, t, u)"
  obtains v T targs where "strip_comb t = (Var v T, targs)"
proof -
  from assms have "is_Var (head_of t)" by (simp add: fr_shape_def frs0_def)
  then obtain v T where "head_of t = Var v T" by (cases "head_of t") auto
  then have "fst (strip_comb t) = Var v T" by (simp add: head_of_strip_comb)
  then show ?thesis using that by (cases "strip_comb t") auto
qed

lemma head_tvars_strip_comb:
  "strip_comb t = (Var v T, targs) \<Longrightarrow> tvars T \<subseteq> ttvars t"
  using ttvars_head[of t] by (simp add: head_of_strip_comb)

lemma fr_shape_tenv:
  assumes "tenv env' = tenv env" shows "fr_shape env' dp \<longleftrightarrow> fr_shape env dp"
  unfolding fr_shape_def using hunb_tenv[OF assms, of dp] by simp


subsection \<open>New variables\<close>

text \<open>The new arguments of a projection or an imitation:\<close>

lemma lookup_unbound: "vt_lookup (tenv env) x = None \<Longrightarrow> lookup env x T = return None"
  by (simp add: lookup_def)

lemma upok_Xmono:
  "upok A env rb X t u \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> vtvars X' \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> upok A env rb X' t u"
  unfolding upok_def by blast

lemma vtvars_mlvars_Var:
  "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U \<and> tvars U \<subseteq> S \<Longrightarrow> vtvars (lvars Gs) \<subseteq> S"
  by (fastforce simp: vtvars_def)

lemma sinv_make_args:
  assumes si: "sinv A K X env dps" and ma: "make_args name Ts env Us = (env', args)"
    and tv: "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
  obtains Gs where "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    "sinv A K (lvars Gs \<union> X) env' dps"
    "vtvars (lvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  obtain Gs where Gs: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (lvars Gs \<union> X)"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    by (rule make_args_props_idx[OF ma]) blast
  have ei: "einv A K env" and wi: "winv env X" and ps: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    using si by (auto simp: sinv_def)
  have vG: "vtvars (lvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
  proof (rule vtvars_mlvars_Var, intro ballI)
    fix G assume "G \<in> set Gs"
    then obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs(2) i(1)] i obtain x where "G = Var x (Ts \<Rrightarrow> (Us ! i))" by blast
    moreover have "Us ! i \<in> set Us" using i(1) list_all2_lengthD[OF Gs(2)] by simp
    ultimately show "\<exists>x U. G = Var x U \<and> tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
      using tv by (fastforce simp: tvars_funs)
  qed
  have ei': "einv A K env'" by (rule einv_maxidx[OF ei Gs(3-5)])
  have wi': "winv env' (lvars Gs \<union> X)"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
    then have "wt_env \<rho> env \<and> vinv \<rho> env X" using winvD[OF wi] Gs(4) by simp
    then show "wt_env \<rho> env' \<and> vinv \<rho> env' (lvars Gs \<union> X)" using Gs(6) wt_env_tenv[OF Gs(3)] by blast
  qed
  have ext: "extends env env'" using Gs(3-5) by (simp add: extends_def)
  have "upok A env' rb (lvars Gs \<union> X) t u" if "(rb, t, u) \<in> set dps" for rb t u
  proof -
    from ps that have p: "upok A env rb X t u" by auto
    have "upok A env rb (lvars Gs \<union> X) t u"
      by (rule upok_Xmono[OF p]) (use vG upokD(6)[OF p] in auto)
    then show ?thesis by (rule upok_mono[OF _ ext]) (simp add: Gs(4))
  qed
  then have "sinv A K (lvars Gs \<union> X) env' dps" using ei' wi' by (auto simp: sinv_def)
  with Gs(1-5,7) vG show ?thesis using that by blast
qed

lemma tnorm_funs_mf: "tnorm \<theta> (Ts \<Rrightarrow> T) = map (tnorm \<theta>) Ts \<Rrightarrow> tnorm \<theta> T"
  by (induction Ts) simp_all

text \<open>The type unification of a projection keeps the invariant:\<close>

lemma proj_unify_sinv:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite K" and si: "sinv A K X env dps"
    and tv: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
      "\<forall>C\<in>set Cs. tvars C \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tnorm (tyenv env) base)" "cert_typ alg ar (tnorm (tyenv env) bary)"
      "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env) C)"
  shows "cuok (proj_unify cfg base bary Cs env) (\<lambda>env'. sinv A K X env' dps \<and> tenv env' = tenv env \<and>
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
proof (cases "Cs = []")
  case True
  note cu = cunify_types_sinv[OF fin si tv(1) c(1) tv(2) c(2)]
  have cu': "cuok (cunify_types alg base bary env) (\<lambda>env'. sinv A K X env' dps \<and> tenv env' = tenv env \<and>
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
    by (rule xokW_mono[OF cu]) (simp add: True)
  show ?thesis
  proof (cases "cfg_trace_types cfg")
    case tt: True
    show ?thesis unfolding proj_unify_def using True tt cfg
      by (simp add: test_unify_types_def) (rule xokW_bindW[OF cu'], simp add: xokW_def okW_whenW)
  qed (use True cu' cfg in \<open>simp add: proj_unify_def\<close>)
next
  case False
  have tvC: "tvars (Cs \<Rrightarrow> base) \<subseteq> tvars_env (tyenv env) \<union> A" using tv(1,3) by (auto simp: tvars_funs)
  have cC: "cert_typ alg ar (tnorm (tyenv env) (Cs \<Rrightarrow> base))"
    using c(1,3) by (simp add: tnorm_funs_mf cert_typ_funs)
  note cu = cunify_types_sinv[OF fin si tv(2) c(2) tvC cC]
  show ?thesis unfolding proj_unify_def using False cfg cu by (simp add: List.null_iff)
qed

text \<open>The rigid side of a saturated flex-rigid pair has the body type of its head:\<close>

lemma mf_body_type_sound:
  assumes bt: "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> (\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D) \<and>
    (\<exists>Zs. \<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B)"
  using bt
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" using Type by auto
      with h have "ok (bt env U) B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] obtain Zs where
        "\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D" "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> U = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B"
        by blast
      then show ?thesis using T by (intro conjI exI[of _ "T1 # Zs"]) auto
    next
      case False
      with h Type have "B = T" by (auto split: list.splits if_splits)
      with Type False show ?thesis by (intro conjI exI[of _ "[]"]) auto
    qed
  next
    case (TVar v' S')
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v' S') lr"
      and rest: "ok (case lr of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B" by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr have vn: "vt_lookup (tyenv env) v' = None" by (auto simp: ok_type_lookup split: option.splits)
      from None rest TVar have B: "B = TVar v' S'" by simp
      show ?thesis unfolding B using vn TVar by (intro conjI exI[of _ "[]"]) (simp_all add: tnorm_TVar[OF "1.prems"(2)])
    next
      case (Some T')
      with rest have r: "ok (bt env T') B" by simp
      from lr Some have vb: "vt_lookup (tyenv env) v' = Some (S', T')" by (auto simp: ok_type_lookup split: option.splits)
      from "1.IH"[OF r refl "1.prems"(2)] obtain Zs where
        "\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D" "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> T' = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B"
        by blast
      then show ?thesis using TVar tsolD[OF _ vb] by (intro conjI exI[of _ Zs]) auto
    qed
  next
    case (TFree a S)
    with h show ?thesis by (intro conjI exI[of _ "[]"]) auto
  qed
qed

subsection \<open>The copies of a single step\<close>

lemma make_projs_term: "length Ts = length targs \<Longrightarrow> \<exists>ps. okW (make_projs u targs0 Ts targs) ps"
proof (induction Ts arbitrary: targs)
  case (Cons T Ts)
  then obtain targ targs' where "targs = targ # targs'" by (cases targs) auto
  with Cons show ?case by fastforce
qed auto

lemma mapM_fastype_term:
  assumes ei: "einv A K env"
    and ty: "\<forall>s\<in>set ss. \<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>Ss. mapM (fastype env rb) ss = return Ss \<and> (\<forall>S\<in>set Ss. tvars S \<subseteq> tvars_env (tyenv env) \<union> A)"
  using ty
proof (induction ss)
  case (Cons s ss)
  from Cons.prems obtain e U where "bs_env (rho0 env) e rb" "e \<turnstile> inst (rho0 env) s : U"
    "\<not> loose_bvar s (ilength rb)" "ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A" by auto
  from env_fastype_term[OF einvD(2)[OF ei] refl this(2,1,3,4)] obtain S where
    "env_fastype env (map snd rb) s = return S" "tvars S \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  moreover from Cons obtain Ss where "mapM (fastype env rb) ss = return Ss"
    "\<forall>S\<in>set Ss. tvars S \<subseteq> tvars_env (tyenv env) \<union> A" by auto
  ultimately show ?case by (auto simp: fastype_def[abs_def])
qed simp

text \<open>The new variables applied to the bound variables of the arguments:\<close>

lemma new_args_props:
  assumes Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us" and len: "length Ts' = length Ts"
    and args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs"
  shows "\<forall>a\<in>set args. \<not> loose_bvar a (ilength Ts)" "(\<Union>a\<in>set args. vars a) = lvars Gs"
    "(\<Union>a\<in>set args. ttvars a) = (\<Union>G\<in>set Gs. ttvars G)"
  unfolding args
proof -
  have var: "\<exists>x U. G = Var x U" if "G \<in> set Gs" for G
  proof -
    from that obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs i(1)] i(2) show ?thesis by blast
  qed
  have lb: "\<not> loose_bvar b (ilength Ts)" if "b \<in> set (bvs (length Ts'))" for b
    using that len by (auto simp: ilength_eq integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq)
  show "\<forall>a\<in>set (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs). \<not> loose_bvar a (ilength Ts)"
    using var lb by (fastforce simp: loose_bvar_apps)
  show "(\<Union>a\<in>set (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs). vars a) = lvars Gs"
    by (auto simp: vars_apps)
  show "(\<Union>a\<in>set (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs). ttvars a) = (\<Union>G\<in>set Gs. ttvars G)"
    by (auto simp: ttvars_apps)
qed

lemma ttvars_mlvars_Gs:
  assumes "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U"
  shows "(\<Union>G\<in>set Gs. ttvars G) = vtvars (lvars Gs)"
proof -
  have e: "ttvars G = vtvars (vars G)" if "G \<in> set Gs" for G using assms that by (fastforce simp: vtvars_def)
  have "vtvars (lvars Gs) = (\<Union>G\<in>set Gs. vtvars (vars G))" by (auto simp: vtvars_def)
  then show ?thesis using e by auto
qed

text \<open>The new variables are unbound and do not reach \<open>v\<close>:\<close>

lemma below_head:
  assumes "sinv A K X env dps" "(v, T) \<in> X \<union> evars env"
  shows "snd v \<le> maxidx env"
proof -
  have "einv A K env" "winv env X" using assms(1) by (simp_all add: sinv_def)
  from winvD[OF this(2) einv_rho0[OF this(1)]] assms(2) show ?thesis by (auto simp: vinv_def dest: belowD)
qed

end

end
