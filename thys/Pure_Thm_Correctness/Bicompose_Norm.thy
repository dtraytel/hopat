section \<open>Normalization and Instances\<close>

theory Bicompose_Norm
  imports Bicompose_Seq
begin

text \<open>
  The new theorem of \<open>bicompose_aux\<close> is normalized by the environment of a unifier, but only
  as much as needed (\<^const>\<open>addth\<close>). An instance \<open>(\<rho>, \<sigma>)\<close> of the new theorem, a ground
  well-sorted type instantiation and a closed substitution, is extended to an instance
  \<open>(\<rho>', \<sigma>')\<close> that solves the environment and agrees with \<open>(\<rho>, \<sigma>)\<close> on the variables that the
  environment does not bind. Normalized terms contain only such variables, so their
  \<open>(\<rho>, \<sigma>)\<close>-instance is equivalent to the \<open>(\<rho>', \<sigma>')\<close>-instance of the original term.
\<close>

subsection \<open>Unbound variables\<close>

definition unb :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "unb env t \<longleftrightarrow> (\<forall>x\<in>vars t. vt_lookup (tenv env) x = None) \<and>
    (\<forall>T\<in>tys t. \<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"

lemma unb_simps[simp]:
  "unb env (Const a T) \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"
  "unb env (Free a T) \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"
  "unb env (Var x T) \<longleftrightarrow> vt_lookup (tenv env) x = None \<and> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"
  "unb env (Bound i)"
  "unb env (Abs a T t) \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None) \<and> unb env t"
  "unb env (s $ t) \<longleftrightarrow> unb env s \<and> unb env t"
  by (auto simp: unb_def)

lemma unb_empty: "env_is_empty env \<Longrightarrow> unb env t"
  by (simp add: unb_def env_is_empty_def vt_is_empty_lookup)

lemma norm_type_aux_unb:
  assumes "norm_type_aux \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> (v, S) \<in> tvars T' \<Longrightarrow> vt_lookup \<theta> v = None"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  show ?case sorry
qed

lemma norm_type_unb: "ok (norm_type \<theta> T) T' \<Longrightarrow> (v, S) \<in> tvars T' \<Longrightarrow> vt_lookup \<theta> v = None"
  sorry

lemma norm_term2_unb:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> unb env t'"
  sorry

lemma norm_term1_unb:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> unb env t'"
  sorry

lemma norm_term_unb: "ok (norm_term env t) t' \<Longrightarrow> unb env t'"
  sorry

text \<open>All variables of a term have an index of at most \<open>m\<close>.\<close>

definition ibelow :: "integer \<Rightarrow> pterm \<Rightarrow> bool" where
  "ibelow m t \<longleftrightarrow> (\<forall>x\<in>vars t. snd x \<le> m) \<and> (\<forall>T\<in>tys t. \<forall>(v, S)\<in>tvars T. snd v \<le> m)"

lemma above_unb: "above env m \<Longrightarrow> ibelow m t \<Longrightarrow> unb env t"
  sorry


subsection \<open>Extending instances\<close>

context wf_algebra
begin

text \<open>Ground well-sorted type instantiations.\<close>

definition gtinst :: "tinst \<Rightarrow> bool" where
  "gtinst \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> (\<forall>v S. ground ar (\<rho> v S))"

text \<open>
  \<open>(\<rho>', \<sigma>')\<close> extends \<open>(\<rho>, \<sigma>)\<close> by the environment \<open>env\<close>: \<open>\<rho>'\<close> is a ground well-sorted solution
  of the type environment, \<open>\<sigma>'\<close> is closed and rigid and, after renaming the constants by
  \<open>\<rho>'\<close>, solves the environment; both agree with \<open>(\<rho>, \<sigma>)\<close> on unbound variables.
\<close>

definition iext :: "env \<Rightarrow> tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longleftrightarrow> gsol alg ar (tyenv env) \<rho>' \<and>
    (\<forall>v S. vt_lookup (tyenv env) v = None \<longrightarrow> \<rho>' v S = \<rho> v S) \<and>
    closed_on UNIV \<sigma>' \<and> rigid_subst \<sigma>' \<and> psat (\<sigma>' \<circ> cren \<rho>') env \<and>
    (\<forall>x. vt_lookup (tenv env) x = None \<longrightarrow> \<sigma>' (code (AVar x)) = \<sigma> (code (AVar x)))"

lemma iext_exists:
  assumes "penv_inv alg ar W env" "gtinst \<rho>" "closed_on UNIV \<sigma>" "rigid_subst \<sigma>"
  obtains \<rho>' \<sigma>' where "iext env \<rho> \<sigma> \<rho>' \<sigma>'"
  sorry

lemma gtinst_gsol: "gsol alg ar \<theta> \<rho> \<Longrightarrow> gtinst \<rho>"
  by (simp add: gsol_def gtinst_def)

lemma iext_unb:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "unb env t"
  shows "sm \<rho>' \<sigma>' t = sm \<rho> \<sigma> t"
  sorry

lemma iext_norm_term:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "swf_env ar env" "swf_tm ar rb t"
    "ok (norm_term env t) t'"
  shows "sm \<rho> \<sigma> t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
  sorry

end


subsection \<open>Skipping lifted assumptions\<close>

text \<open>The assumptions that \<^const>\<open>norm_term_skip\<close> skips are unbound.\<close>

function skip_unb :: "env \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> bool" where
  "skip_unb env n t \<longleftrightarrow>
    n = 0 \<or>
    (case dest_all t of
      Some (a, T, b) \<Rightarrow> skip_unb env n b
    | None \<Rightarrow> (case dest_imp t of Some (A, B) \<Rightarrow> unb env A \<and> skip_unb env (n - 1) B | None \<Rightarrow> True))"
  by auto
termination by (relation "measure (\<lambda>(_, _, t). size t)") (auto dest: dest_size)

declare skip_unb.simps[simp del]

context wf_algebra
begin

lemma iext_norm_term_skip:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "swf_env ar env"
  shows "okT (norm_term_skip env n t) t' \<Longrightarrow> swf_tm ar rb t \<Longrightarrow> cok t \<Longrightarrow> skip_unb env n t \<Longrightarrow>
    sm \<rho> \<sigma> t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
  sorry

end

end
