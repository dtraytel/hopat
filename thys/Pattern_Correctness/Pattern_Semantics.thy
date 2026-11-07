section \<open>Semantics of Environments\<close>

theory Pattern_Semantics
  imports Pattern_Signature "Pure_Pattern.Pure_Pattern"
begin

text \<open>
  A solution of an environment is a pair of a type instantiation \<open>\<rho>\<close> and a substitution \<open>\<sigma>\<close> of
  the schematic variables. \<open>\<rho>\<close> respects sorts and solves the type environment; \<open>\<sigma>\<close> maps
  variables of certified types to closed terms of their types. A schematic variable \<open>Var x T\<close> denotes
  \<open>\<sigma> x (\<rho> T)\<close>: as \<open>Envir.lookup\<close> compares types modulo the type environment, a variable is
  identified by its name and its instantiated type. The bindings of the environment hold
  modulo \<open>\<alpha>\<beta>\<eta>\<close>-equivalence.
\<close>

context pure_sig
begin

definition ap :: "tinst \<Rightarrow> vsubst \<Rightarrow> pterm \<Rightarrow> pterm" where
  "ap \<rho> \<sigma> t = vsubst \<sigma> (inst \<rho> t)"

definition solution :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> bool" where
  "solution \<rho> \<sigma> env \<longleftrightarrow> wsinst alg \<rho> \<and> tsol (tyenv env) \<rho> \<and> wt_subst \<sigma> \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> \<sigma> x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"

text \<open>Solutions exist: the identity solves an empty environment.\<close>

lemma solutionD:
  assumes "solution \<rho> \<sigma> env"
  shows "wsinst alg \<rho>" "tsol (tyenv env) \<rho>" "wt_subst \<sigma>"
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

lemma extends_tsol: "tsol (tyenv env') \<rho> \<Longrightarrow> extends env env' \<Longrightarrow> tsol (tyenv env) \<rho>"
  unfolding extends_def by (meson tsol_textends)


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

end

end
