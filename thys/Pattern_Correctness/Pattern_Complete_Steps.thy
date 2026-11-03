section \<open>Completeness of the Steps\<close>

theory Pattern_Complete_Steps
  imports Pattern_Complete_Base
begin

context pure_sig
begin

subsection \<open>The invariant\<close>

text \<open>
  The completeness invariant for a solution \<open>(\<rho>, \<sigma>)\<close> of \<open>env\<close>, binders \<open>bs\<close> with types \<open>e\<close>,
  the variables \<open>X\<close> of the pending problems, and the type variables \<open>A\<close> of the problem: the
  soundness invariants, the type invariant, and the type variables of the binders and of \<open>X\<close>
  are known to the type environment or in \<open>A\<close>.
\<close>

definition vtvars :: "(indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set" where
  "vtvars X = (\<Union>(x, T)\<in>X. tvars T)"

definition btvars :: "binders \<Rightarrow> (indexname \<times> psort) set" where
  "btvars bs = (\<Union>(x, T)\<in>set bs. tvars T)"

definition cinv :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "cinv \<rho> \<sigma> env e bs X A \<longleftrightarrow> solution \<rho> \<sigma> env \<and> wt_env \<rho> env \<and> bs_env \<rho> e bs \<and> vinv \<rho> env X \<and>
    tvinv A env \<and> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"

text \<open>A term of the problem, of type \<open>T\<close> after instantiation by \<open>\<rho>\<close>:\<close>

definition cterm :: "tinst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow> (indexname \<times> psort) set \<Rightarrow>
    pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "cterm \<rho> env e bs A t T \<longleftrightarrow> e \<turnstile> inst \<rho> t : T \<and> \<not> loose_bvar t (ilength bs) \<and>
    ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"

text \<open>
  The conclusion: no \<open>Unif\<close> failure, and a successful result has a solution that agrees with
  \<open>(\<rho>, \<sigma>)\<close> on the old variables and keeps the type invariant.
\<close>

definition ccon :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env M \<Rightarrow> bool" where
  "ccon \<rho> \<sigma> env A r \<longleftrightarrow> no_unif r \<and> (\<forall>env'. ok r env' \<longrightarrow> (\<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and> tvinv A env' \<and>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')))"

text \<open>A step is complete if it is complete for every solution of the problem \<open>s =?= t\<close>:\<close>

definition step_cp :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env M \<Rightarrow> bool" where
  "step_cp env bs s t r \<longleftrightarrow> (\<forall>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<longrightarrow> vars s \<union> vars t \<subseteq> X \<longrightarrow>
    cterm \<rho> env e bs A s T \<longrightarrow> cterm \<rho> env e bs A t T \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<longrightarrow>
    ccon \<rho> \<sigma> env A r)"

lemma step_cpI:
  assumes "\<And>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> vars s \<union> vars t \<subseteq> X \<Longrightarrow>
    cterm \<rho> env e bs A s T \<Longrightarrow> cterm \<rho> env e bs A t T \<Longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<Longrightarrow>
    ccon \<rho> \<sigma> env A r"
  shows "step_cp env bs s t r"
  using assms unfolding step_cp_def by blast

lemma step_cpD:
  "step_cp env bs s t r \<Longrightarrow> cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> vars s \<union> vars t \<subseteq> X \<Longrightarrow>
    cterm \<rho> env e bs A s T \<Longrightarrow> cterm \<rho> env e bs A t T \<Longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<Longrightarrow>
    ccon \<rho> \<sigma> env A r"
  unfolding step_cp_def by blast

lemma step_cp_sym: "step_cp env bs s t r \<Longrightarrow> step_cp env bs t s r"
  unfolding step_cp_def by (blast intro: conv_sym)

lemma cinv_mono: "cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> cinv \<rho> \<sigma> env e bs Y A"
  unfolding cinv_def vtvars_def by (blast intro: vinv_mono)

lemma ccon_Ok:
  assumes "solution \<rho> \<sigma> env" "tvinv A env"
  shows "ccon \<rho> \<sigma> env A (return env)"
proof -
  have "solution \<rho> \<sigma> env \<and> tagree (maxidx env) \<rho> \<rho> \<and> sagree (maxidx env) \<sigma> \<sigma> \<and> tvinv A env"
    using assms by simp
  then show ?thesis unfolding ccon_def by (auto intro!: exI[of _ \<rho>] exI[of _ \<sigma>])
qed


subsection \<open>Agreement\<close>

lemma evarsE:
  assumes "(x, T) \<in> evars env"
  obtains y U u where "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
  using assms unfolding evars_def bnds_def by blast

lemma tvinv_evars:
  assumes "tvinv A env" "(x, T) \<in> evars env"
  shows "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  from assms(2) obtain y U u where b: "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
    by (rule evarsE)
  have "tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" by (rule tvinvD(2)[OF assms(1) b(1)])
  with b(2) show ?thesis by (auto simp: ttvars_def dest: vars_typs)
qed

lemma tsubst_agree: "tagree n \<rho> \<rho>' \<Longrightarrow> tbelow n (tvars T) \<Longrightarrow> tsubst \<rho>' T = tsubst \<rho> T"
  by (rule tagree_tsubst) (auto simp: tbelow_def)

lemma vinv_agree:
  assumes "vinv \<rho> env X" "tagree (maxidx env) \<rho> \<rho>'" "tvinv A env"
    "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "vinv \<rho>' env X"
proof -
  have eq: "tsubst \<rho>' T = tsubst \<rho> T" if "(x, T) \<in> X \<union> evars env" for x T
  proof (rule tsubst_agree[OF assms(2)], rule tvinv_tbelow[OF assms(3)])
    show "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
      using that assms(4) tvinv_evars[OF assms(3)] unfolding vtvars_def by blast
  qed
  show ?thesis using assms(1) eq unfolding vinv_def vcons_def by metis
qed

lemma wt_env_agree:
  assumes "wt_env \<rho> env" "tagree (maxidx env) \<rho> \<rho>'" "tvinv A env"
  shows "wt_env \<rho>' env"
  unfolding wt_env_def
proof (intro allI impI conjI)
  fix x U u e assume b: "vt_lookup (tenv env) x = Some (U, u)"
  have tv: "tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" by (rule tvinvD(2)[OF assms(3) b])
  then have "tbelow (maxidx env) (tvars U)" "tbelow (maxidx env) (ttvars u)"
    using tvinv_tbelow[OF assms(3)] by auto
  then have "tsubst \<rho>' U = tsubst \<rho> U" "inst \<rho>' u = inst \<rho> u"
    using tsubst_agree[OF assms(2)] inst_agree[OF assms(2)] by blast+
  moreover have "closed u" "e \<turnstile> inst \<rho> u : tsubst \<rho> U" using assms(1) b unfolding wt_env_def by blast+
  ultimately show "closed u" "e \<turnstile> inst \<rho>' u : tsubst \<rho>' U" by simp_all
qed

lemma bs_env_agree:
  assumes "bs_env \<rho> e bs" "tagree n \<rho> \<rho>'" "tbelow n (btvars bs)"
  shows "bs_env \<rho>' e bs"
proof -
  have eq: "tsubst \<rho>' T = tsubst \<rho> T" if "(x, T) \<in> set bs" for x T
    using that assms(3) by (intro tsubst_agree[OF assms(2)]) (auto simp: btvars_def tbelow_def)
  have "\<forall>i. 0 \<le> i \<longrightarrow> i < ilength bs \<longrightarrow> snd (bs ! nat_of_integer i) \<in> snd ` set bs"
    by (auto simp: nat_of_integer_less_ilength)
  then show ?thesis using assms(1) eq unfolding bs_env_def by (fastforce split: prod.splits)
qed

lemma cterm_agree:
  assumes "cterm \<rho> env e bs A t T" "tagree (maxidx env) \<rho> \<rho>'" "tvinv A env"
  shows "inst \<rho>' t = inst \<rho> t"
  using assms tvinv_tbelow[OF assms(3)] by (intro inst_agree) (auto simp: cterm_def)

lemma ap_cterm_agree:
  assumes "cterm \<rho> env e bs A t T" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "tvinv A env" "vinv \<rho> env X" "vars t \<subseteq> X"
  shows "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t"
proof (rule ap_agree[OF assms(2,3)])
  show "tbelow (maxidx env) (ttvars t)" using assms(1) tvinv_tbelow[OF assms(4)] by (auto simp: cterm_def)
  show "below (maxidx env) (vars t)" using assms(5,6) by (auto simp: vinv_def below_def)
qed

text \<open>
  After a step, the invariant holds for the extended solution, by soundness of the step: the
  remaining problems are unchanged.
\<close>

lemma cinv_step:
  assumes inv: "cinv \<rho> \<sigma> env e bs X A" and st: "step_ok env bs s t env'"
    and X: "vars s \<union> vars t \<subseteq> X" and s: "cterm \<rho> env e bs A s T" and t: "cterm \<rho> env e bs A t T"
    and sol: "solution \<rho>' \<sigma>' env'" and ag: "tagree (maxidx env) \<rho> \<rho>'"
    and tv: "tvinv A env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "cinv \<rho>' \<sigma>' env' e bs X A"
proof -
  note i = inv[unfolded cinv_def]
  have tv0: "tvinv A env" using i by blast
  have "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A" using i by blast
  then have "tbelow (maxidx env) (btvars bs)" by (rule tvinv_tbelow[OF tv0])
  then have bs': "bs_env \<rho>' e bs" using bs_env_agree[OF _ ag] i by blast
  have wt': "wt_env \<rho>' env" using wt_env_agree i ag by blast
  have XX: "X \<union> vars s \<union> vars t = X" using X by blast
  have "vinv \<rho>' env X" using vinv_agree[OF _ ag tv0] i by blast
  then have vi': "vinv \<rho>' env (X \<union> vars s \<union> vars t)" by (simp only: XX)
  have ts: "e \<turnstile> inst \<rho>' s : T" "e \<turnstile> inst \<rho>' t : T"
    using cterm_agree[OF s ag tv0] cterm_agree[OF t ag tv0] s t by (auto simp: cterm_def)
  have "wt_env \<rho>' env' \<and> vinv \<rho>' env' X \<and> ap \<rho>' \<sigma>' s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t"
    using step_okD(2)[OF st sol extends_refl wt' bs' ts vi'] s t by (auto simp: cterm_def)
  then show ?thesis using sol bs' tv i unfolding cinv_def by blast
qed

lemma cterm_step:
  assumes "cterm \<rho> env e bs A t T" "tagree (maxidx env) \<rho> \<rho>'" "tvinv A env"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "cterm \<rho>' env' e bs A t T"
  using assms cterm_agree[OF assms(1-3)] unfolding cterm_def by auto

text \<open>Composition of the conclusions:\<close>

lemma ccon_trans:
  assumes "solution \<rho>1 \<sigma>1 env1" "tagree (maxidx env) \<rho> \<rho>1" "sagree (maxidx env) \<sigma> \<sigma>1"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "maxidx env \<le> maxidx env1"
    "ccon \<rho>1 \<sigma>1 env1 A r"
  shows "ccon \<rho> \<sigma> env A r"
  using assms unfolding ccon_def by (blast intro: tagree_trans sagree_trans)

subsection \<open>Head normalization\<close>

definition etvars :: "env \<Rightarrow> (indexname \<times> psort) set" where
  "etvars env = (\<Union>(x, U, u)\<in>bnds env. tvars U \<union> ttvars u)"

lemma etvarsI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ttvars u \<subseteq> etvars env"
  unfolding etvars_def bnds_def by blast

lemma tvinv_etvars: "tvinv A env \<Longrightarrow> etvars env \<subseteq> tvars_env (tyenv env) \<union> A"
  unfolding etvars_def bnds_def using tvinvD(2) by blast

lemma typs_incr_bv [simp]: "typs (incr_bv n k t) = typs t"
  by (induction t arbitrary: k) auto

lemma ttvars_simps [simp]:
  "ttvars (s $ t) = ttvars s \<union> ttvars t" "ttvars (Abs a T t) = tvars T \<union> ttvars t"
  "ttvars (Bound i) = {}" "ttvars (Var x T) = tvars T" "ttvars (Const c T) = tvars T"
  "ttvars (Free f T) = tvars T"
  by (auto simp: ttvars_def)

lemma ttvars_apps: "ttvars (s \<degree>\<degree> ts) = ttvars s \<union> \<Union> (ttvars ` set ts)"
  by (induction ts arbitrary: s) auto

lemma ttvars_subst: "ttvars (t[s/k]) \<subseteq> ttvars t \<union> ttvars s"
proof (induction t arbitrary: s k)
  case (Abs a T t)
  then show ?case using Abs.IH[of "lift s 0" "k + 1"] by (auto simp: ttvars_def)
next
  case (App t1 t2)
  have "ttvars (t1[s/k]) \<subseteq> ttvars t1 \<union> ttvars s" "ttvars (t2[s/k]) \<subseteq> ttvars t2 \<union> ttvars s"
    by (rule App.IH(1), rule App.IH(2))
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma head_norm_ttvars:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> ttvars t' \<subseteq> ttvars t \<union> etvars env"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "ttvars u' \<subseteq> ttvars u \<union> etvars env" if "ok (hn env u) u'" for u u'
    using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      with lr obtain U where "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      with IH[of u t'] rest Some show ?thesis by (auto dest: etvarsI)
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h IH show ?thesis by fastforce
  next
    case (App f u)
    have redex: "ttvars t' \<subseteq> ttvars (Abs b U0 body $ u) \<union> etvars env"
      if "ok (hn env (subst_bound u body)) t'" for b U0 body
      using IH[OF that] ttvars_subst[of body u 0] by (auto simp: subst_bound_subst)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF hf] have nf: "ttvars nf \<subseteq> ttvars f \<union> etvars env" .
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from redex[OF this] nf App Abs show ?thesis by auto
      qed (use rest nf App in auto)
    qed
  qed (use h in auto)
qed

lemma vtvars_Un [simp]: "vtvars (X \<union> Y) = vtvars X \<union> vtvars Y"
  by (auto simp: vtvars_def)

lemma vtvars_vars: "vtvars (vars t) \<subseteq> ttvars t"
  by (auto simp: vtvars_def ttvars_def dest: vars_typs)

lemma vtvars_evars: "tvinv A env \<Longrightarrow> vtvars (evars env) \<subseteq> tvars_env (tyenv env) \<union> A"
  using tvinv_evars unfolding vtvars_def by blast

lemma cterm_head_norm:
  assumes "cterm \<rho> env e bs A t T" "ok (head_norm env t) t'" "solution \<rho> \<sigma> env" "wt_env \<rho> env"
    "tvinv A env"
  shows "cterm \<rho> env e bs A t' T" "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
proof -
  note hn = head_norm_sound[OF assms(2) refl assms(3,4)]
  show "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" using hn assms(1) by (auto simp: cterm_def)
  show "cterm \<rho> env e bs A t' T"
    unfolding cterm_def
  proof (intro conjI)
    show "e \<turnstile> inst \<rho> t' : T" using hn assms(1) by (auto simp: cterm_def)
    show "\<not> loose_bvar t' (ilength bs)"
      using head_norm_loose[OF assms(2) refl assms(4)] assms(1) by (simp add: cterm_def)
    show "ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
      using head_norm_ttvars[OF assms(2) refl] tvinv_etvars[OF assms(5)] assms(1) by (auto simp: cterm_def)
  qed
qed

lemma step_cp_head_norm:
  assumes hs: "ok (head_norm env s) s'" and ht: "ok (head_norm env t) t'"
    and st: "step_cp env bs s' t' r"
  shows "step_cp env bs s t r"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars s \<union> vars t \<subseteq> X"
    and cs: "cterm \<rho> env e bs A s T" and ct: "cterm \<rho> env e bs A t T"
    and eq: "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  note i = inv[unfolded cinv_def]
  note s' = cterm_head_norm[OF cs hs, of \<sigma>] and t' = cterm_head_norm[OF ct ht, of \<sigma>]
  let ?X = "X \<union> evars env"
  have "cinv \<rho> \<sigma> env e bs ?X A"
  proof -
    have "vinv \<rho> env (X \<union> evars env)" using vinv_hn[of \<rho> env X "{}" "evars env"] i by simp
    moreover have "vtvars (evars env) \<subseteq> tvars_env (tyenv env) \<union> A" using vtvars_evars i by blast
    ultimately show ?thesis using i unfolding cinv_def by auto
  qed
  moreover have "vars s' \<union> vars t' \<subseteq> ?X"
    using head_norm_vars[OF hs refl] head_norm_vars[OF ht refl] X by blast
  moreover have "ap \<rho> \<sigma> s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
    using s'(2) t'(2) eq i by (meson conv_sym conv_trans)
  ultimately show "ccon \<rho> \<sigma> env A r" using step_cpD[OF st] s'(1) t'(1) i by blast
qed


subsection \<open>Flex terms\<close>

lemma cterm_flex:
  assumes "cterm \<rho> env e bs A (Var F Fty \<degree>\<degree> ss) T" "ok (ints_of' env ss) is" "solution \<rho> \<sigma> env"
    "wt_env \<rho> env"
  shows "cterm \<rho> env e bs A (app (Var F Fty) is) T"
    "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) is)"
proof -
  have ty: "e \<turnstile> inst \<rho> (Var F Fty \<degree>\<degree> ss) : T" using assms(1) by (simp add: cterm_def)
  note f = flex_sound[OF assms(2-4) ty]
  show "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) is)" by (rule f(2))
  have "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)"
    using ints_of'_loose[OF assms(2,4) _] assms(1)
    by (auto simp: app_apps loose_bvar_apps not_le cterm_def)
  moreover have "ttvars (app (Var F Fty) is) \<subseteq> ttvars (Var F Fty \<degree>\<degree> ss)"
    by (simp add: app_apps ttvars_apps)
  ultimately show "cterm \<rho> env e bs A (app (Var F Fty) is) T"
    using assms(1) f(1) unfolding cterm_def by blast
qed

lemma step_cp_flex:
  assumes is_ok: "ok (ints_of' env ss) is" and st: "step_cp env bs (app (Var F Fty) is) t r"
  shows "step_cp env bs (Var F Fty \<degree>\<degree> ss) t r"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (Var F Fty \<degree>\<degree> ss) \<union> vars t \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (Var F Fty \<degree>\<degree> ss) T" and ct: "cterm \<rho> env e bs A t T"
    and eq: "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  note i = inv[unfolded cinv_def]
  note f = cterm_flex[OF cs is_ok, of \<sigma>]
  have "vars (app (Var F Fty) is) \<union> vars t \<subseteq> X" using X by (auto simp: vars_apps)
  moreover have "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
    using f(2) eq i by (meson conv_sym conv_trans)
  ultimately show "ccon \<rho> \<sigma> env A r" using step_cpD[OF st inv] f(1) ct i by blast
qed

end

end
