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
  \<open>(\<rho>, \<sigma>)\<close> on the old variables and keeps the invariant for the pending problems.
\<close>

definition ccon :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env M \<Rightarrow> bool" where
  "ccon \<rho> \<sigma> env e bs X A r \<longleftrightarrow> no_unif r \<and> (\<forall>env'. ok r env' \<longrightarrow> (\<exists>\<rho>' \<sigma>'. cinv \<rho>' \<sigma>' env' e bs X A \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env'))"

text \<open>A step is complete if it is complete for every solution of the problem \<open>s =?= t\<close>:\<close>

definition step_cp :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env M \<Rightarrow> bool" where
  "step_cp env bs s t r \<longleftrightarrow> (\<forall>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<longrightarrow> vars s \<union> vars t \<subseteq> X \<longrightarrow>
    cterm \<rho> env e bs A s T \<longrightarrow> cterm \<rho> env e bs A t T \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<longrightarrow>
    ccon \<rho> \<sigma> env e bs X A r)"

lemma step_cpI:
  assumes "\<And>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> vars s \<union> vars t \<subseteq> X \<Longrightarrow>
    cterm \<rho> env e bs A s T \<Longrightarrow> cterm \<rho> env e bs A t T \<Longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<Longrightarrow>
    ccon \<rho> \<sigma> env e bs X A r"
  shows "step_cp env bs s t r"
  using assms unfolding step_cp_def by blast

lemma step_cpD:
  "step_cp env bs s t r \<Longrightarrow> cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> vars s \<union> vars t \<subseteq> X \<Longrightarrow>
    cterm \<rho> env e bs A s T \<Longrightarrow> cterm \<rho> env e bs A t T \<Longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<Longrightarrow>
    ccon \<rho> \<sigma> env e bs X A r"
  unfolding step_cp_def by blast

lemma step_cp_sym: "step_cp env bs s t r \<Longrightarrow> step_cp env bs t s r"
  unfolding step_cp_def by (blast intro: conv_sym)

lemma cinv_mono: "cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> cinv \<rho> \<sigma> env e bs Y A"
  unfolding cinv_def vtvars_def by (blast intro: vinv_mono)

lemma ccon_Ok:
  assumes "cinv \<rho> \<sigma> env e bs X A"
  shows "ccon \<rho> \<sigma> env e bs X A (return env)"
proof -
  have "cinv \<rho> \<sigma> env e bs X A \<and> tagree (maxidx env) \<rho> \<rho> \<and> sagree (maxidx env) \<sigma> \<sigma>"
    using assms by simp
  then show ?thesis unfolding ccon_def by (auto intro!: exI[of _ \<rho>] exI[of _ \<sigma>])
qed

lemma ccon_mono: "ccon \<rho> \<sigma> env e bs X A r \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> ccon \<rho> \<sigma> env e bs Y A r"
  unfolding ccon_def by (blast intro: cinv_mono)


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
    using step_okD(3)[OF st sol extends_refl wt' bs' ts vi'] s t by (auto simp: cterm_def)
  then show ?thesis using sol bs' tv i unfolding cinv_def by blast
qed

lemma cterm_step:
  assumes "cterm \<rho> env e bs A t T" "tagree (maxidx env) \<rho> \<rho>'" "tvinv A env"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "cterm \<rho>' env' e bs A t T"
  using assms cterm_agree[OF assms(1-3)] unfolding cterm_def by auto

text \<open>Composition of the conclusions:\<close>

lemma ccon_trans:
  assumes "tagree (maxidx env) \<rho> \<rho>1" "sagree (maxidx env) \<sigma> \<sigma>1"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "maxidx env \<le> maxidx env1"
    "ccon \<rho>1 \<sigma>1 env1 e bs X A r"
  shows "ccon \<rho> \<sigma> env e bs X A r"
  using assms unfolding ccon_def by (blast intro: tagree_trans sagree_trans order_trans)

text \<open>Leaving binders:\<close>

lemma ccon_bs:
  assumes "ccon \<rho> \<sigma> env e' bs' X A r" "bs_env \<rho> e bs" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    "tvinv A env" "btvars bs \<subseteq> btvars bs'"
  shows "ccon \<rho> \<sigma> env e bs X A r"
  unfolding ccon_def
proof (intro conjI allI impI)
  show "no_unif r" using assms(1) by (simp add: ccon_def)
  fix env' assume "ok r env'"
  then obtain \<rho>' \<sigma>' where c: "cinv \<rho>' \<sigma>' env' e' bs' X A" "tagree (maxidx env) \<rho> \<rho>'"
    "sagree (maxidx env) \<sigma> \<sigma>'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "maxidx env \<le> maxidx env'"
    using assms(1) unfolding ccon_def by blast
  have "bs_env \<rho>' e bs" using bs_env_agree[OF assms(2) c(2) tvinv_tbelow[OF assms(4,3)]] .
  then have "cinv \<rho>' \<sigma>' env' e bs X A" using c(1) assms(5) unfolding cinv_def by blast
  with c(2-5) show "\<exists>\<rho>' \<sigma>'. cinv \<rho>' \<sigma>' env' e bs X A \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
    sagree (maxidx env) \<sigma> \<sigma>' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env'"
    by blast
qed

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
  note hn = head_norm_sound[OF assms(2) refl solutionD(2)[OF assms(3)] assms(4)]
  show "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" using hn assms(1,3) by (auto simp: cterm_def)
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
  ultimately have "ccon \<rho> \<sigma> env e bs ?X A r" using step_cpD[OF st] s'(1) t'(1) i by blast
  then show "ccon \<rho> \<sigma> env e bs X A r" by (rule ccon_mono) simp
qed


subsection \<open>Flex terms\<close>

lemma cterm_flex:
  assumes "cterm \<rho> env e bs A (Var F Fty \<degree>\<degree> ss) T" "ok (ints_of' env ss) is" "solution \<rho> \<sigma> env"
    "wt_env \<rho> env"
  shows "cterm \<rho> env e bs A (app (Var F Fty) is) T"
    "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) is)"
proof -
  have ty: "e \<turnstile> inst \<rho> (Var F Fty \<degree>\<degree> ss) : T" using assms(1) by (simp add: cterm_def)
  note f = flex_sound[OF assms(2) solutionD(2)[OF assms(3)] assms(4) ty]
  show "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) is)" by (rule f(2)[OF assms(3)])
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
  ultimately show "ccon \<rho> \<sigma> env e bs X A r" using step_cpD[OF st inv] f(1) ct i by blast
qed

subsection \<open>Abstractions\<close>

lemma solution_tyenv:
  assumes sol: "solution \<rho> \<sigma> env" and tv: "tvinv A env" and vi: "vinv \<rho> env X"
    and \<rho>': "wsinst alg \<rho>'" "tsol (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
    and te: "tenv env' = tenv env"
  shows "solution \<rho>' \<sigma> env'"
  unfolding solution_def
proof (intro conjI allI impI)
  show "wsinst alg \<rho>'" "tsol (tyenv env') \<rho>'" by (rule \<rho>'(1), rule \<rho>'(2))
  show "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  fix x U u assume b': "vt_lookup (tenv env') x = Some (U, u)"
  then have b: "vt_lookup (tenv env) x = Some (U, u)" using te by simp
  have "tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" by (rule tvinvD(2)[OF tv b])
  then have "tbelow (maxidx env) (tvars U)" "tbelow (maxidx env) (ttvars u)"
    using tvinv_tbelow[OF tv] by auto
  moreover have "below (maxidx env) (vars u)"
    using vi evarsI2[OF b] unfolding vinv_def below_def by blast
  ultimately have "tsubst \<rho>' U = tsubst \<rho> U" "ap \<rho>' \<sigma> u = ap \<rho> \<sigma> u"
    using tsubst_agree[OF \<rho>'(3)] ap_agree[OF \<rho>'(3) sagree_refl] by blast+
  with solutionD(4)[OF sol b] show "\<sigma> x (tsubst \<rho>' U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma> u" by simp
qed

text \<open>The invariant after unifying types:\<close>

lemma cinv_unify_types:
  assumes inv: "cinv \<rho> \<sigma> env e bs X A" and ut: "ok (unify_types alg T U env) env1"
    and \<rho>1: "wsinst alg \<rho>1" "tsol (tyenv env1) \<rho>1" "tagree (maxidx env) \<rho> \<rho>1"
    and tv: "tvinv A env1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
  shows "cinv \<rho>1 \<sigma> env1 e bs X A"
proof -
  note i = inv[unfolded cinv_def]
  note u = unify_types_sound[OF ut]
  have tv0: "tvinv A env" using i by blast
  have "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A" using i by blast
  then have "bs_env \<rho>1 e bs" using bs_env_agree[OF _ \<rho>1(3) tvinv_tbelow[OF tv0]] i by blast
  moreover have "solution \<rho>1 \<sigma> env1" using solution_tyenv[OF _ tv0 _ \<rho>1 u(1)] i by blast
  moreover have "wt_env \<rho>1 env1" using wt_env_agree[OF _ \<rho>1(3) tv0] wt_env_tenv[OF u(1)] i by blast
  moreover have "vinv \<rho>1 env1 X" using vinv_agree[OF _ \<rho>1(3) tv0] vinv_tenv[OF u(1,2)] i by blast
  ultimately show ?thesis using i tv unfolding cinv_def by blast
qed

lemma cinv_Cons:
  assumes "cinv \<rho> \<sigma> env e bs X A" "cert_typ alg ar (tsubst \<rho> T)" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "cinv \<rho> \<sigma> env (e\<langle>0:tsubst \<rho> T\<rangle>) ((a, T) # bs) X A"
  using assms bs_env_Cons[of \<rho> e bs T a] unfolding cinv_def btvars_def by auto

lemma step_cp_Abs:
  assumes st: "\<And>env1. ok (unify_types alg Ts Tt env) env1 \<Longrightarrow> step_cp env1 ((a, Ts) # bs) ts tt (r env1)"
  shows "step_cp env bs (Abs ns Ts ts) (Abs nt Tt tt) (unify_types alg Ts Tt env \<bind> r)"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (Abs ns Ts ts) \<union> vars (Abs nt Tt tt) \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (Abs ns Ts ts) T" and ct: "cterm \<rho> env e bs A (Abs nt Tt tt) T"
    and eq: "ap \<rho> \<sigma> (Abs ns Ts ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs nt Tt tt)"
  note i = inv[unfolded cinv_def]
  have tys: "e \<turnstile> inst \<rho> (Abs ns Ts ts) : T" and tyt: "e \<turnstile> inst \<rho> (Abs nt Tt tt) : T"
    using cs ct by (simp_all add: cterm_def)
  from tys obtain U where T: "T = tsubst \<rho> Ts \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
    and ts: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U"
    by auto
  from tyt obtain U' where T': "T = tsubst \<rho> Tt \<rightarrow>\<^sub>T U'" and tt': "e\<langle>0:tsubst \<rho> Tt\<rangle> \<turnstile> inst \<rho> tt : U'"
    by auto
  have TT: "tsubst \<rho> Tt = tsubst \<rho> Ts" and UU: "U' = U" using T T' by simp_all
  have tt: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> tt : U" using tt' TT UU by simp
  have sol: "solution \<rho> \<sigma> env" and tv0: "tvinv A env" using i by blast+
  note sd = solutionD[OF sol]
  have "e \<turnstile> Abs ns (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts) : T" "e \<turnstile> Abs nt (tsubst \<rho> Tt) (ap \<rho> \<sigma> tt) : T"
    using typing_ap[OF tys sd(3)] typing_ap[OF tyt sd(3)] by simp_all
  from conv_Abs_inv[OF this] eq have eqb: "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> tt" by simp
  have tvT: "tvars Ts \<subseteq> tvars_env (tyenv env) \<union> A" "tvars Tt \<subseteq> tvars_env (tyenv env) \<union> A"
    using cs ct by (auto simp: cterm_def)
  have wft: "wft ar Ts" "wft ar Tt"
    using typing_inst_wft[OF tys] typing_inst_wft[OF tyt] by auto
  note uc = unify_types_complete[of A env Ts Tt \<rho>, OF tv0 tvT(1) wft(1) tvT(2) wft(2) sd(1,2) TT[symmetric]]
  have nu: "no_unif (unify_types alg Ts Tt env)" by (rule uc(1))
  have "ccon \<rho> \<sigma> env e bs X A (r env1)" if ut: "ok (unify_types alg Ts Tt env) env1" for env1
  proof -
    obtain \<rho>1 where \<rho>1: "wsinst alg \<rho>1" "tsol (tyenv env1) \<rho>1" "tagree (maxidx env) \<rho> \<rho>1"
      and tv1: "tvinv A env1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
      using uc(2)[OF ut] by blast
    note u = unify_types_sound[OF ut]
    have inv1: "cinv \<rho>1 \<sigma> env1 e bs X A" by (rule cinv_unify_types[OF inv ut \<rho>1 tv1])
    have eqT: "tsubst \<rho>1 Ts = tsubst \<rho> Ts"
      using tsubst_agree[OF \<rho>1(3) tvinv_tbelow[OF tv0 tvT(1)]] .
    have inv2: "cinv \<rho>1 \<sigma> env1 (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) X A"
      using cinv_Cons[OF inv1, of Ts a] c eqT tvT(1) tv1(2) by auto
    have ag: "inst \<rho>1 ts = inst \<rho> ts" "inst \<rho>1 tt = inst \<rho> tt"
      "ap \<rho>1 \<sigma> ts = ap \<rho> \<sigma> ts" "ap \<rho>1 \<sigma> tt = ap \<rho> \<sigma> tt"
    proof -
      have tb: "tbelow (maxidx env) (ttvars ts)" "tbelow (maxidx env) (ttvars tt)"
        using cs ct tvinv_tbelow[OF tv0] by (auto simp: cterm_def)
      have vb: "below (maxidx env) (vars ts)" "below (maxidx env) (vars tt)"
        using i X by (auto simp: vinv_def below_def)
      show "inst \<rho>1 ts = inst \<rho> ts" "inst \<rho>1 tt = inst \<rho> tt"
        using inst_agree[OF \<rho>1(3)] tb by blast+
      show "ap \<rho>1 \<sigma> ts = ap \<rho> \<sigma> ts" "ap \<rho>1 \<sigma> tt = ap \<rho> \<sigma> tt"
        using ap_agree[OF \<rho>1(3) sagree_refl] tb vb by blast+
    qed
    have cts: "cterm \<rho>1 env1 (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) A ts U"
      and ctt: "cterm \<rho>1 env1 (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) A tt U"
      using cs ct ts tt ag(1,2) tv1(2) by (auto simp: cterm_def algebra_simps)
    have "vars ts \<union> vars tt \<subseteq> X" using X by simp
    from step_cpD[OF st[OF ut] inv2 this cts ctt] eqb ag(3,4)
    have "ccon \<rho>1 \<sigma> env1 (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) X A (r env1)" by simp
    then have "ccon \<rho>1 \<sigma> env1 e bs X A (r env1)"
      by (rule ccon_bs) (use inv1 in \<open>auto simp: cinv_def btvars_def\<close>)
    moreover have "maxidx env \<le> maxidx env1" using u(2) by (simp add: extends_def)
    ultimately show ?thesis using ccon_trans[OF \<rho>1(3) sagree_refl tv1(2)] by blast
  qed
  with nu show "ccon \<rho> \<sigma> env e bs X A (unify_types alg Ts Tt env \<bind> r)"
    unfolding ccon_def by (auto intro!: no_unif_bindM)
qed

lemma step_cp_eta:
  assumes st: "step_cp env ((a, Ts) # bs) ts (incr t' $ Bound 0) r"
  shows "step_cp env bs (Abs a Ts ts) t' r"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (Abs a Ts ts) \<union> vars t' \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (Abs a Ts ts) T" and ct: "cterm \<rho> env e bs A t' T"
    and eq: "ap \<rho> \<sigma> (Abs a Ts ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
  note i = inv[unfolded cinv_def]
  have \<sigma>: "wt_subst \<sigma>" using i solutionD(3) by blast
  have tys: "e \<turnstile> inst \<rho> (Abs a Ts ts) : T" and tyt: "e \<turnstile> inst \<rho> t' : T"
    using cs ct by (simp_all add: cterm_def)
  from tys obtain U where T: "T = tsubst \<rho> Ts \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
    and ts: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U"
    by auto
  have te: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> (incr t' $ Bound 0) : U"
    using tyt T by (auto simp: incr_def incr_aux_lift intro!: lift_type)
  have tvT: "tvars Ts \<subseteq> tvars_env (tyenv env) \<union> A" using cs by (auto simp: cterm_def)
  have inv1: "cinv \<rho> \<sigma> env (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) X A" by (rule cinv_Cons[OF inv c tvT])
  have cts: "cterm \<rho> env (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) A ts U"
    using cs ts by (auto simp: cterm_def algebra_simps)
  have ctt: "cterm \<rho> env (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) A (incr t' $ Bound 0) U"
    unfolding cterm_def
  proof (intro conjI)
    show "\<not> loose_bvar (incr t' $ Bound 0) (ilength ((a, Ts) # bs))"
      using ct loose_bvar_lift[of 0 "ilength bs" t'] ilength_nonneg[of bs]
      by (simp add: incr_def incr_aux_lift integer_arith cterm_def)
    show "ttvars (incr t' $ Bound 0) \<subseteq> tvars_env (tyenv env) \<union> A"
      using ct by (simp add: incr_def incr_aux_lift cterm_def ttvars_def)
  qed (rule te)
  have ap_e: "ap \<rho> \<sigma> (incr t') = lift (ap \<rho> \<sigma> t') 0"
    using \<sigma> by (simp add: incr_def incr_aux_lift ap_lift)
  have "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> lift (ap \<rho> \<sigma> t') 0 $ Bound 0 : U"
    using typing_ap[OF te \<sigma>] by (simp add: ap_e)
  from typing.Abs[OF c this]
  have tye: "e \<turnstile> Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0) : T" by (simp add: T)
  have "(sup beta eta)\<^sup>*\<^sup>* (Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0)) (ap \<rho> \<sigma> t')"
    by (rule r_into_rtranclp, rule sup2I2, rule eta_lift)
  then have "Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
    by (rule beta_eta_conv) (use tye in \<open>auto simp: wt_def\<close>)
  then have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0)"
    by (rule conv_sym)
  with eq have "Abs a (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0)"
    by (simp add: conv_trans)
  then have "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (ap \<rho> \<sigma> t') 0 $ Bound 0"
    using conv_Abs_inv[OF _ tye] typing_ap[OF tys \<sigma>] by simp
  then have "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (incr t' $ Bound 0)" by (simp add: ap_e)
  moreover have "vars ts \<union> vars (incr t' $ Bound 0) \<subseteq> X" using X by (simp add: incr_def incr_aux_lift)
  ultimately have "ccon \<rho> \<sigma> env (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs) X A r"
    using step_cpD[OF st inv1 _ cts ctt] by blast
  then show "ccon \<rho> \<sigma> env e bs X A r"
    by (rule ccon_bs) (use inv in \<open>auto simp: cinv_def btvars_def\<close>)
qed

subsection \<open>Rigid heads\<close>

lemma ccon_bindM:
  "no_unif m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> ccon \<rho> \<sigma> env e bs X A (g x)) \<Longrightarrow> ccon \<rho> \<sigma> env e bs X A (m \<bind> g)"
  unfolding ccon_def by (auto intro!: no_unif_bindM)

text \<open>A pending problem of the invariant:\<close>

definition cpair :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> pterm \<times> pterm \<Rightarrow> bool" where
  "cpair \<rho> \<sigma> env e bs X A p \<longleftrightarrow> vars (fst p) \<union> vars (snd p) \<subseteq> X \<and>
    (\<exists>U. cterm \<rho> env e bs A (fst p) U \<and> cterm \<rho> env e bs A (snd p) U) \<and>
    ap \<rho> \<sigma> (fst p) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (snd p)"

lemma cpair_step:
  assumes "cpair \<rho> \<sigma> env e bs X A p" "vinv \<rho> env X" "tvinv A env"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "cpair \<rho>' \<sigma>' env' e bs X A p"
proof -
  obtain U where U: "cterm \<rho> env e bs A (fst p) U" "cterm \<rho> env e bs A (snd p) U"
    using assms(1) by (auto simp: cpair_def)
  have X: "vars (fst p) \<subseteq> X" "vars (snd p) \<subseteq> X" using assms(1) by (auto simp: cpair_def)
  have "ap \<rho>' \<sigma>' (fst p) = ap \<rho> \<sigma> (fst p)" "ap \<rho>' \<sigma>' (snd p) = ap \<rho> \<sigma> (snd p)"
    using ap_cterm_agree[OF U(1) assms(4,5,3,2) X(1)] ap_cterm_agree[OF U(2) assms(4,5,3,2) X(2)] .
  moreover have "cterm \<rho>' env' e bs A (fst p) U" "cterm \<rho>' env' e bs A (snd p) U"
    using cterm_step[OF U(1) assms(4,3,6)] cterm_step[OF U(2) assms(4,3,6)] .
  ultimately show ?thesis using assms(1) unfolding cpair_def by auto
qed

lemma ccon_foldM:
  assumes f: "\<And>s t env. step_cp env bs s t (f s t env)"
  shows "cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> \<forall>p\<in>set ps. cpair \<rho> \<sigma> env e bs X A p \<Longrightarrow>
    ccon \<rho> \<sigma> env e bs X A (foldM (\<lambda>(s, t) env. f s t env) ps env)"
proof (induction ps arbitrary: \<rho> \<sigma> env)
  case Nil
  then show ?case by (simp add: ccon_Ok)
next
  case (Cons p ps)
  obtain s t where p: "p = (s, t)" by force
  have cp: "cpair \<rho> \<sigma> env e bs X A (s, t)" using Cons.prems(2) p by simp
  then obtain U where U: "cterm \<rho> env e bs A s U" "cterm \<rho> env e bs A t U"
    and X: "vars s \<union> vars t \<subseteq> X" and eq: "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
    by (auto simp: cpair_def)
  have c1: "ccon \<rho> \<sigma> env e bs X A (f s t env)" by (rule step_cpD[OF f Cons.prems(1) X U eq])
  have fo: "foldM (\<lambda>(s, t) env. f s t env) (p # ps) env =
      f s t env \<bind> (\<lambda>env1. foldM (\<lambda>(s, t) env. f s t env) ps env1)"
    by (simp add: p)
  show ?case unfolding fo
  proof (rule ccon_bindM)
    show "no_unif (f s t env)" using c1 by (simp add: ccon_def)
    fix env1 assume ok1: "ok (f s t env) env1"
    then obtain \<rho>1 \<sigma>1 where r1: "cinv \<rho>1 \<sigma>1 env1 e bs X A" "tagree (maxidx env) \<rho> \<rho>1"
      "sagree (maxidx env) \<sigma> \<sigma>1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "maxidx env \<le> maxidx env1"
      using c1 unfolding ccon_def by blast
    have i0: "vinv \<rho> env X" "tvinv A env" using Cons.prems(1) by (auto simp: cinv_def)
    have "\<forall>p\<in>set ps. cpair \<rho>1 \<sigma>1 env1 e bs X A p"
      using Cons.prems(2) cpair_step[OF _ i0 r1(2,3,4)] by simp
    from Cons.IH[OF r1(1) this]
    have "ccon \<rho>1 \<sigma>1 env1 e bs X A (foldM (\<lambda>(s, t) env. f s t env) ps env1)" .
    then show "ccon \<rho> \<sigma> env e bs X A (foldM (\<lambda>(s, t) env. f s t env) ps env1)"
      by (rule ccon_trans[OF r1(2-5)])
  qed
qed


lemma typs_apps: "typs (s \<degree>\<degree> ts) = typs s \<union> \<Union> (typs ` set ts)"
  by (induction ts arbitrary: s) auto

definition rigid_atom :: "pterm \<Rightarrow> bool" where
  "rigid_atom h \<longleftrightarrow> (case h of Const _ _ \<Rightarrow> True | Free _ _ \<Rightarrow> True | Bound _ \<Rightarrow> True | _ \<Rightarrow> False)"

lemma rigid_atom_simps [simp]:
  "rigid_atom (Const c T)" "rigid_atom (Free f T)" "rigid_atom (Bound i)"
  "\<not> rigid_atom (Var x T)" "\<not> rigid_atom (Abs a T t)" "\<not> rigid_atom (s $ t)"
  by (simp_all add: rigid_atom_def)

lemma rigid_atom_ap: "rigid_atom h \<Longrightarrow> ap \<rho> \<sigma> h = inst \<rho> h"
  by (cases h) (auto simp: ap_def)

lemma rigid_atom_inst: "rigid_atom h \<Longrightarrow> atom (inst \<rho> h)"
  by (cases h) auto

lemma rigid_atom_vars: "rigid_atom h \<Longrightarrow> vars h = {}"
  by (cases h) auto

lemma rigid_args:
  assumes inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (h \<degree>\<degree> ss) \<union> vars (h' \<degree>\<degree> ts) \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (h \<degree>\<degree> ss) T" and ct: "cterm \<rho> env e bs A (h' \<degree>\<degree> ts) T"
    and eq: "ap \<rho> \<sigma> (h \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (h' \<degree>\<degree> ts)" and rh: "rigid_atom h" "rigid_atom h'"
  shows "inst \<rho> h = inst \<rho> h'" and "length ss = length ts"
    and "\<forall>p\<in>set (zip ss ts). cpair \<rho> \<sigma> env e bs X A p"
proof -
  have \<sigma>: "wt_subst \<sigma>" using inv solutionD(3) by (auto simp: cinv_def)
  have tys0: "e \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T" and tyt0: "e \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T"
    using cs ct by (simp_all add: cterm_def)
  then have tys: "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) ss : T" and tyt: "e \<turnstile> inst \<rho> h' \<degree>\<degree> map (inst \<rho>) ts : T"
    by (simp_all add: inst_apps)
  have apss: "ap \<rho> \<sigma> (h \<degree>\<degree> ss) = inst \<rho> h \<degree>\<degree> map (ap \<rho> \<sigma>) ss"
    and apts: "ap \<rho> \<sigma> (h' \<degree>\<degree> ts) = inst \<rho> h' \<degree>\<degree> map (ap \<rho> \<sigma>) ts"
    using rh by (simp_all add: ap_apps rigid_atom_ap)
  have wt: "wt (inst \<rho> h \<degree>\<degree> map (ap \<rho> \<sigma>) ss)" using wt_ap[OF tys0 \<sigma>] apss by simp
  note ci = conv_atom_apps_inv[OF rigid_atom_inst[OF rh(1)] rigid_atom_inst[OF rh(2)] wt eq[unfolded apss apts]]
  show hh: "inst \<rho> h = inst \<rho> h'" by (rule ci(1))
  have l2: "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) ss) (map (ap \<rho> \<sigma>) ts)" by (rule ci(2))
  then show len: "length ss = length ts" using list_all2_lengthD by fastforce
  obtain Us where th: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> T" and tss: "e \<tturnstile> map (inst \<rho>) ss : Us"
    using tys by (rule list_app_typeE)
  obtain Us' where th': "e \<turnstile> inst \<rho> h' : Us' \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us'"
    using tyt by (rule list_app_typeE)
  from typings_nth[OF tss] typings_nth[OF tts] len have lens: "length Us = length Us'" by simp
  from typing_unique[OF th th'[folded hh]] funs_eq[OF lens] have UU: "Us = Us'" by simp
  show "\<forall>p\<in>set (zip ss ts). cpair \<rho> \<sigma> env e bs X A p"
  proof
    fix p assume "p \<in> set (zip ss ts)"
    then obtain k where k: "k < length ss" "p = (ss ! k, ts ! k)" using len by (auto simp: set_zip)
    have kt: "k < length ts" using k(1) len by simp
    have ty: "e \<turnstile> inst \<rho> (ss ! k) : Us ! k" "e \<turnstile> inst \<rho> (ts ! k) : Us ! k"
      using typings_nth[OF tss] typings_nth[OF tts] k(1) kt UU by auto
    have m: "ss ! k \<in> set ss" "ts ! k \<in> set ts" using k(1) kt by simp_all
    have "cterm \<rho> env e bs A (ss ! k) (Us ! k)" "cterm \<rho> env e bs A (ts ! k) (Us ! k)"
      using cs ct ty m by (auto simp: cterm_def loose_bvar_apps ttvars_apps)
    moreover have "vars (ss ! k) \<union> vars (ts ! k) \<subseteq> X" using X m by (auto simp: vars_apps)
    moreover have "ap \<rho> \<sigma> (ss ! k) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (ts ! k)"
      using list_all2_nthD[OF l2, of k] k(1) kt by simp
    ultimately show "cpair \<rho> \<sigma> env e bs X A p" using k(2) unfolding cpair_def by auto
  qed
qed

lemma step_cp_clash:
  assumes "rigid_atom h" "rigid_atom h'" "\<And>\<rho>. inst \<rho> h \<noteq> inst \<rho> h'"
  shows "step_cp env bs (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) r"
  by (rule step_cpI) (use rigid_args(1)[OF _ _ _ _ _ assms(1,2)] assms(3) in blast)

lemma step_cp_rigid_bound:
  assumes f: "\<And>s t env. step_cp env bs s t (f s t env)"
  shows "step_cp env bs (Bound i \<degree>\<degree> ss) (Bound i \<degree>\<degree> ts)
    (zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. f s t env) ps env))"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (Bound i \<degree>\<degree> ss) \<union> vars (Bound i \<degree>\<degree> ts) \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (Bound i \<degree>\<degree> ss) T" and ct: "cterm \<rho> env e bs A (Bound i \<degree>\<degree> ts) T"
    and eq: "ap \<rho> \<sigma> (Bound i \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Bound i \<degree>\<degree> ts)"
  note ra = rigid_args[OF inv X cs ct eq rigid_atom_simps(3) rigid_atom_simps(3)]
  show "ccon \<rho> \<sigma> env e bs X A (zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. f s t env) ps env))"
  proof (rule ccon_bindM)
    show "no_unif (zip_eq ss ts)" by (rule no_unif_zip_eq)
    fix ps assume "ok (zip_eq ss ts) ps"
    then have ps: "ps = zip ss ts" by (simp add: ok_zip_eq)
    show "ccon \<rho> \<sigma> env e bs X A (foldM (\<lambda>(s, t) env. f s t env) ps env)"
      using ccon_foldM[OF f inv] ra(3) ps by simp
  qed
qed

lemma step_cp_rigid_types:
  assumes f: "\<And>s t env. step_cp env bs s t (f s t env)" and c: "c = Const a \<or> c = Free a"
  shows "step_cp env bs (c Ta \<degree>\<degree> ss) (c Tb \<degree>\<degree> ts)
    (unify_types alg Ta Tb env \<bind> (\<lambda>env1. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. f s t env) ps env1)))"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (c Ta \<degree>\<degree> ss) \<union> vars (c Tb \<degree>\<degree> ts) \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (c Ta \<degree>\<degree> ss) T" and ct: "cterm \<rho> env e bs A (c Tb \<degree>\<degree> ts) T"
    and eq: "ap \<rho> \<sigma> (c Ta \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (c Tb \<degree>\<degree> ts)"
  have rc: "rigid_atom (c Ta)" "rigid_atom (c Tb)" using c by auto
  note ra = rigid_args[OF inv X cs ct eq rc]
  have TT: "tsubst \<rho> Ta = tsubst \<rho> Tb" using ra(1) c by auto
  note i = inv[unfolded cinv_def]
  have tv0: "tvinv A env" and sol: "solution \<rho> \<sigma> env" using i by blast+
  note sd = solutionD[OF sol]
  have typs: "typs (c Ta) = {Ta}" "typs (c Tb) = {Tb}" using c by auto
  have Tin: "Ta \<in> typs (c Ta \<degree>\<degree> ss)" "Tb \<in> typs (c Tb \<degree>\<degree> ts)" using typs by (simp_all add: typs_apps)
  have tvT: "tvars Ta \<subseteq> tvars_env (tyenv env) \<union> A" "tvars Tb \<subseteq> tvars_env (tyenv env) \<union> A"
    using cs ct Tin by (auto simp: cterm_def ttvars_def)
  have wft: "wft ar Ta" "wft ar Tb"
    using typing_inst_wft[OF _ Tin(1)] typing_inst_wft[OF _ Tin(2)] cs ct by (auto simp: cterm_def)
  note uc = unify_types_complete[of A env Ta Tb \<rho>, OF tv0 tvT(1) wft(1) tvT(2) wft(2) sd(1,2) TT]
  show "ccon \<rho> \<sigma> env e bs X A
    (unify_types alg Ta Tb env \<bind> (\<lambda>env1. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. f s t env) ps env1)))"
  proof (rule ccon_bindM)
    show "no_unif (unify_types alg Ta Tb env)" by (rule uc(1))
    fix env1 assume ut: "ok (unify_types alg Ta Tb env) env1"
    obtain \<rho>1 where \<rho>1: "wsinst alg \<rho>1" "tsol (tyenv env1) \<rho>1" "tagree (maxidx env) \<rho> \<rho>1"
      and tv1: "tvinv A env1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
      using uc(2)[OF ut] by blast
    have inv1: "cinv \<rho>1 \<sigma> env1 e bs X A" by (rule cinv_unify_types[OF inv ut \<rho>1 tv1])
    have mx: "maxidx env \<le> maxidx env1" using unify_types_sound(2)[OF ut] by (simp add: extends_def)
    have cp1: "\<forall>p\<in>set (zip ss ts). cpair \<rho>1 \<sigma> env1 e bs X A p"
      using ra(3) cpair_step[OF _ _ tv0 \<rho>1(3) sagree_refl tv1(2)] i by blast
    have "ccon \<rho>1 \<sigma> env1 e bs X A (zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. f s t env) ps env1))"
    proof (rule ccon_bindM)
      show "no_unif (zip_eq ss ts)" by (rule no_unif_zip_eq)
      fix ps assume "ok (zip_eq ss ts) ps"
      then have ps: "ps = zip ss ts" by (simp add: ok_zip_eq)
      show "ccon \<rho>1 \<sigma> env1 e bs X A (foldM (\<lambda>(s, t) env. f s t env) ps env1)"
        using ccon_foldM[OF f inv1] cp1 ps by simp
    qed
    then show "ccon \<rho> \<sigma> env e bs X A (zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. f s t env) ps env1))"
      by (rule ccon_trans[OF \<rho>1(3) sagree_refl tv1(2) mx])
  qed
qed

end

end
