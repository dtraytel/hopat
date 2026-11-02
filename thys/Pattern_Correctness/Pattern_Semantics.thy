section \<open>Semantics of Environments\<close>

theory Pattern_Semantics
  imports Pattern_Signature "Pure_Pattern.Pure_Pattern"
begin

text \<open>
  A solution of an environment is a pair of a type instantiation \<open>\<rho>\<close> and a substitution \<open>\<sigma>\<close> of
  the schematic variables. \<open>\<rho>\<close> respects sorts, maps to certified types and solves the type
  environment; \<open>\<sigma>\<close> maps to closed well-typed terms. A schematic variable \<open>Var x T\<close> denotes
  \<open>\<sigma> x (\<rho> T)\<close>: as \<open>Envir.lookup\<close> compares types modulo the type environment, a variable is
  identified by its name and its instantiated type. The bindings of the environment hold
  modulo \<open>\<alpha>\<beta>\<eta>\<close>-equivalence.
\<close>

context pure_sig
begin

definition ap :: "tinst \<Rightarrow> vsubst \<Rightarrow> pterm \<Rightarrow> pterm" where
  "ap \<rho> \<sigma> t = vsubst \<sigma> (inst \<rho> t)"

definition solution :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> bool" where
  "solution \<rho> \<sigma> env \<longleftrightarrow> tinst_ok \<rho> \<and> tsol (tyenv env) \<rho> \<and> wt_subst \<sigma> \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> \<sigma> x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"

lemma solutionD:
  assumes "solution \<rho> \<sigma> env"
  shows "tinst_ok \<rho>" "tsol (tyenv env) \<rho>" "wt_subst \<sigma>"
    and "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> \<sigma> x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  using assms unfolding solution_def by blast+


subsection \<open>Extensions of environments\<close>

text \<open>Unification only adds bindings, to the type and the term environment, and new variables.\<close>

definition extends :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "extends env env' \<longleftrightarrow> textends (tyenv env) (tyenv env') \<and>
    (\<forall>x b. vt_lookup (tenv env) x = Some b \<longrightarrow> vt_lookup (tenv env') x = Some b) \<and>
    maxidx env \<le> maxidx env'"

lemma extends_refl [simp]: "extends env env"
  by (simp add: extends_def textends_def)

lemma extends_trans: "extends env env' \<Longrightarrow> extends env' env'' \<Longrightarrow> extends env env''"
  unfolding extends_def textends_def by (meson order_trans)

lemma solution_extends: "solution \<rho> \<sigma> env' \<Longrightarrow> extends env env' \<Longrightarrow> solution \<rho> \<sigma> env"
  unfolding solution_def extends_def by (meson tsol_textends)


subsection \<open>Equivalence in an environment\<close>

definition env_equiv :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool"  (\<open>_ \<Turnstile> _ \<approx> _\<close> [50, 50, 50] 50) where
  "env \<Turnstile> s \<approx> t \<longleftrightarrow> (\<forall>\<rho> \<sigma>. solution \<rho> \<sigma> env \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"

lemma env_equiv_refl [simp]: "env \<Turnstile> t \<approx> t"
  by (simp add: env_equiv_def conv_def)

lemma env_equiv_sym: "env \<Turnstile> s \<approx> t \<Longrightarrow> env \<Turnstile> t \<approx> s"
  unfolding env_equiv_def conv_def by (meson equivclp_sym)

lemma env_equiv_trans [trans]: "env \<Turnstile> r \<approx> s \<Longrightarrow> env \<Turnstile> s \<approx> t \<Longrightarrow> env \<Turnstile> r \<approx> t"
  unfolding env_equiv_def conv_def by (meson equivclp_trans)

lemma env_equiv_extends: "env \<Turnstile> s \<approx> t \<Longrightarrow> extends env env' \<Longrightarrow> env' \<Turnstile> s \<approx> t"
  unfolding env_equiv_def by (meson solution_extends)


subsection \<open>Typing modulo the type environment\<close>

text \<open>
  A term is well-typed in an environment if it is well-typed after normalizing its types by the
  type environment \<open>\<theta>\<close>; then its instances under the solutions of \<open>\<theta>\<close> are well-typed.
\<close>

abbreviation tnorm_inst :: "tyenv \<Rightarrow> tinst" where
  "tnorm_inst \<theta> \<equiv> \<lambda>v S. tnorm \<theta> (TVar v S)"

definition typed :: "env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "typed env e t T \<longleftrightarrow>
    (\<lambda>i. tnorm (tyenv env) (e i)) \<turnstile> inst (tnorm_inst (tyenv env)) t : tnorm (tyenv env) T"

lemma tsubst_tnorm_inst:
  "tacyc \<theta> \<Longrightarrow> tcons_env \<theta> \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tcons \<theta> U \<Longrightarrow>
    tsubst (\<lambda>v S. tsubst \<rho> (tnorm \<theta> (TVar v S))) U = tsubst \<rho> U"
proof -
  assume a: "tacyc \<theta>" "tcons_env \<theta>" "tsol \<theta> \<rho>" "tcons \<theta> U"
  have "tsubst (\<lambda>v S. tsubst \<rho> (tnorm \<theta> (TVar v S))) U = tsubst \<rho> (tsubst (tnorm_inst \<theta>) U)"
    by (simp only: tsubst_tsubst)
  also have "\<dots> = tsubst \<rho> (tnorm \<theta> U)" by (rule arg_cong[of _ _ "tsubst \<rho>"], rule tnorm_tsubst[symmetric])
  also have "\<dots> = tsubst \<rho> U" using tsubst_tnorm[OF a(1-3) a(4)] .
  finally show ?thesis .
qed

lemma typed_solution:
  assumes "typed env e t T" "solution \<rho> \<sigma> env"
    and "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and "\<forall>U\<in>typs t. tcons (tyenv env) U" "\<forall>i. tcons (tyenv env) (e i)" "tcons (tyenv env) T"
  shows "(\<lambda>i. tsubst \<rho> (e i)) \<turnstile> ap \<rho> \<sigma> t : tsubst \<rho> T"
proof -
  let ?\<theta> = "tyenv env"
  note s = solutionD[OF assms(2)]
  have "(\<lambda>i. tinst \<rho> (tnorm ?\<theta> (e i))) \<turnstile> inst \<rho> (inst (tnorm_inst ?\<theta>) t) : tinst \<rho> (tnorm ?\<theta> T)"
    using typing_inst[OF assms(1)[unfolded typed_def] tinst_ok_inst_ok[OF s(1)]] by simp
  moreover have "inst \<rho> (inst (tnorm_inst ?\<theta>) t) = inst \<rho> t"
    unfolding inst_inst tinst_tsubst
    by (rule inst_cong) (use assms(5) in \<open>simp add: tinst_tsubst tsubst_tnorm_inst[OF assms(3,4) s(2)] del: tnorm_TVar\<close>)
  moreover have "tsubst \<rho> (tnorm ?\<theta> (e i)) = tsubst \<rho> (e i)" for i
    using tsubst_tnorm[OF assms(3,4) s(2)] assms(6) by blast
  moreover have "tsubst \<rho> (tnorm ?\<theta> T) = tsubst \<rho> T"
    using tsubst_tnorm[OF assms(3,4) s(2) assms(7)] .
  ultimately have "(\<lambda>i. tsubst \<rho> (e i)) \<turnstile> inst \<rho> t : tsubst \<rho> T" by (simp add: tinst_tsubst)
  then show ?thesis unfolding ap_def by (rule typing_vsubst) (rule s(3))
qed

end

end
