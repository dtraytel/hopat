section \<open>The results of \<open>bicompose_aux\<close> are theorems\<close>

theory Bicompose_Thm
  imports Bicompose_Complete
begin

text \<open>
  The results of \<open>bicompose_aux\<close> for a proof state and a rule that satisfy the invariant of
  theorems satisfy it again: they are well-typed, type variables and variables with the same name
  have the same sort and type, and their indices are nonnegative and at most the maximal index of
  the environment of the unifier. The components of a result are normalized by the environment of
  the unifier; a normalized term is a \<open>\<beta>\<close>-reduct of the application of the environment
  (theorem \<open>norm_term_env_apply\<close>), which is an instance by the canonical solution
  (\<open>env_apply_tsol0\<close>).
\<close>


subsection \<open>Normalized terms\<close>

lemma typs_lift: "typs (lift t k) = typs t"
  by (induction t arbitrary: k) auto

lemma typs_subst: "typs (s[t/k]) \<subseteq> typs s \<union> typs t"
proof (induction s arbitrary: t k)
  case (Abs a T s)
  then show ?case using Abs.IH[of "lift t 0" "k + 1"] by (auto simp: typs_lift)
next
  case (App s1 s2)
  have "typs (s1[t/k]) \<subseteq> typs s1 \<union> typs t" "typs (s2[t/k]) \<subseteq> typs s2 \<union> typs t"
    by (rule App.IH)+
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma beta_typs: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> typs t \<subseteq> typs s"
  by (induction rule: beta.induct) (use typs_subst in auto)

lemma beta_reds_typs: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> typs t \<subseteq> typs s"
  by (induction rule: rtranclp_induct) (use beta_typs in auto)

context pure_sig
begin

lemma typing_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (induction rule: rtranclp_induct) (auto intro: subject_reduction_beta)

text \<open>The variables of a theorem after the application of a type environment:\<close>

definition vimg :: "tyenv \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set" where
  "vimg \<theta> S = (\<lambda>(x, T). (x, tnorm \<theta> T)) ` S"

lemma vimg_mono: "S \<subseteq> S' \<Longrightarrow> vimg \<theta> S \<subseteq> vimg \<theta> S'"
  by (auto simp: vimg_def)

lemma vtcons_vimg:
  assumes "vcons (tnorm_inst \<theta>) S"
  shows "vtcons (vimg \<theta> S)"
  unfolding vtcons_def
proof (intro allI impI)
  fix x T U assume "(x, T) \<in> vimg \<theta> S" "(x, U) \<in> vimg \<theta> S"
  then obtain T0 U0 where "(x, T0) \<in> S" "T = tnorm \<theta> T0" "(x, U0) \<in> S" "U = tnorm \<theta> U0"
    by (auto simp: vimg_def)
  with vconsD[OF assms, of x T0 U0] show "T = U" by simp
qed

lemma fst_vimg [simp]: "fst ` vimg \<theta> S = fst ` S"
  by (force simp: vimg_def)

text \<open>Unbound variables with unbound types are fixed by the application:\<close>

lemma vimg_unb: "tacyc (tyenv env) \<Longrightarrow> unb env X \<Longrightarrow> vars X \<subseteq> S \<Longrightarrow> vars X \<subseteq> vimg (tyenv env) S"
proof
  fix v assume ac: "tacyc (tyenv env)" and u: "unb env X" and S: "vars X \<subseteq> S" and v: "v \<in> vars X"
  obtain x T where vT: "v = (x, T)" by (cases v)
  have "\<forall>p\<in>tvars T. vt_lookup (tyenv env) (fst p) = None"
    using u v vT vtvars_ttvars[of x T X] by (auto simp: unb_def)
  then have "tnorm (tyenv env) T = T" by (intro tnorm_unbound_id ac) auto
  with S v vT show "v \<in> vimg (tyenv env) S" by (force simp: vimg_def)
qed

lemma tsol0_unb:
  assumes "\<forall>p\<in>tvars T. vt_lookup \<theta> (fst p) = None"
  shows "tsubst (tsol0 \<theta>) T = T"
proof -
  have "tsubst (tsol0 \<theta>) T = tsubst TVar T"
    by (rule tsubst_cong) (use assms in \<open>auto simp: tsol0_def\<close>)
  then show ?thesis by simp
qed

lemma inst_tsol0_unb: "unb env t \<Longrightarrow> inst (tsol0 (tyenv env)) t = t"
proof -
  assume u: "unb env t"
  have "inst (tsol0 (tyenv env)) t = inst TVar t"
  proof (rule inst_cong)
    fix U assume "U \<in> typs t"
    then have "\<forall>p\<in>tvars U. vt_lookup (tyenv env) (fst p) = None" using u by (auto simp: unb_def ttvars_def)
    then show "tsubst (tsol0 (tyenv env)) U = tsubst TVar U" using tsol0_unb by simp
  qed
  then show ?thesis by simp
qed

text \<open>A normalized term:\<close>

lemma norm_term_props:
  assumes ei: "einv A K env" and wi: "winv env Y" and vX: "vars X \<subseteq> Y \<union> evars env"
    and tX: "ttvars X \<subseteq> tvars_env (tyenv env) \<union> A" and ty: "e \<turnstile> X : T"
    and lb: "\<not> loose_bvar X k" "0 \<le> k" and nt: "ok (norm_term env X) X'"
  shows "ienv (tsol0 (tyenv env)) e \<turnstile> X' : tsubst (tsol0 (tyenv env)) T" "\<not> loose_bvar X' k"
    "vars X' \<subseteq> vimg (tyenv env) (vars X \<union> evars env)" "ttvars X' \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  let ?\<theta> = "tyenv env"
  let ?\<rho> = "tsol0 ?\<theta>" and ?\<sigma> = "esol (tsol0 ?\<theta>) env"
  note e = einvD[OF ei] and c = canonical_solution[OF ei wi]
  have nac: "acyc env" "closed_env env" "tacyc ?\<theta>" using e(3,6) wt_env_closed_env[OF c(2)] by blast+
  have red: "env_apply env X \<rightarrow>\<^sub>\<beta>\<^sup>* X'" by (rule norm_term_env_apply(1)[OF nt nac])
  have app: "env_apply env X = ap ?\<rho> ?\<sigma> X"
  proof (rule env_apply_tsol0[OF e(1) e(3) tX])
    have "vcons ?\<rho> (Y \<union> evars env)" using c(3) by (simp add: vinv_def)
    then show "vcons ?\<rho> (vars X \<union> evars env)" by (rule vcons_mono) (use vX in blast)
  qed
  have ws: "wt_subst ?\<sigma>" by (rule solutionD(3)[OF c(1)])
  show "ienv ?\<rho> e \<turnstile> X' : tsubst ?\<rho> T"
    by (rule typing_beta_reds[OF red]) (simp add: app typing_ap_inst[OF ty c(4) ws])
  have "\<not> loose_bvar (ap ?\<rho> ?\<sigma> X) k" using lb ws by (simp add: gsubst_def)
  then show "\<not> loose_bvar X' k" using mcp_loose_reds[OF red lb(2)] app by simp
  have "vars (env_apply env X) \<subseteq> vimg ?\<theta> (vars X \<union> evars env)"
    using vars_unf_sub[OF nac(1), of X] by (auto simp: env_apply_def vars_inst vimg_def)
  then show "vars X' \<subseteq> vimg ?\<theta> (vars X \<union> evars env)" using beta_reds_vars[OF red] by blast
  have "ttvars (env_apply env X) \<subseteq> tvars_env ?\<theta> \<union> A"
  proof
    fix p assume "p \<in> ttvars (env_apply env X)"
    then obtain U where U: "U \<in> typs (unf env X)" "p \<in> tvars (tnorm ?\<theta> U)"
      by (auto simp: env_apply_def ttvars_def typs_inst)
    have "tvars U \<subseteq> tvars_env ?\<theta> \<union> A"
    proof (cases "U \<in> typs X")
      case True
      with tX show ?thesis by (auto simp: ttvars_def)
    next
      case False
      with U(1) typs_unf[OF nac(1), of X] obtain x V u where "vt_lookup (tenv env) x = Some (V, u)" "U \<in> typs u"
        by blast
      with tvinvD(2)[OF e(1) this(1)] show ?thesis by (auto simp: ttvars_def)
    qed
    with U(2) tvars_tnorm[OF nac(3), of U] show "p \<in> tvars_env ?\<theta> \<union> A" by blast
  qed
  then show "ttvars X' \<subseteq> tvars_env ?\<theta> \<union> A"
    using beta_reds_typs[OF red] by (auto simp: ttvars_def)
qed

end

end
