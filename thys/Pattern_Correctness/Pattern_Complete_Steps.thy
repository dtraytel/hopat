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

end

end
