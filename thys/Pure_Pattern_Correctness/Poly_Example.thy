section \<open>Examples of Polymorphic Unification\<close>

theory Poly_Example
  imports Poly_Correctness
begin

text \<open>
  We consider two polymorphic problems in the empty environment, for an arbitrary well-formed
  algebra, and obtain their outcomes from the results of theory
  \<^theory>\<open>Pure_Pattern_Correctness.Poly_Correctness\<close>. The base types are fixed type variables
  \<open>i\<close> and \<open>o\<close> without sort constraints.
  \<^item> \<open>P\<^sub>'\<^sub>a ?X =?= P\<^sub>i c\<close>, where \<open>P\<close> is used at the types \<open>'a \<Rightarrow> o\<close> and \<open>i \<Rightarrow> o\<close> for a schematic type
    variable \<open>'a\<close>: the problem is unifiable, so \<^const>\<open>unify\<close> returns an environment, and every
    ground solution of its type environment instantiates \<open>'a\<close> to \<open>i\<close>;
  \<^item> \<open>Q\<^sub>'\<^sub>b ?Y =?= Q\<^sub>i c\<close>, where \<open>'b\<close> has sort \<open>{cls}\<close> for a class \<open>cls\<close>: as \<open>i\<close> does not have sort
    \<open>{cls}\<close>, no ground instance is unifiable, so \<^const>\<open>unify\<close> fails with \<open>Unif\<close>.
\<close>

abbreviation \<iota> :: ptyp where "\<iota> \<equiv> TFree STR ''i'' []"
abbreviation \<kappa> :: ptyp where "\<kappa> \<equiv> TFree STR ''o'' []"

definition env0 :: env where "env0 = Envir 0 vt_empty vt_empty"

definition c :: pterm where "c = Const STR ''c'' \<iota>"

lemma env0_simps[simp]: "maxidx env0 = 0" "tyenv env0 = vt_empty" "vt_lookup (tenv env0) x = None"
  "etys env0 = {}" "nacyc env0" "env_ppat env0"
  by (simp_all add: env0_def etys_def nacyc_def ndep_def env_ppat_def acyclic_def)

lemma tnorm_vt_empty[simp]: "tnorm vt_empty T = T" "tnormt vt_empty t = t"
  by (simp_all add: tnorm_empty tnormt_empty)

lemma env0_typed: "env_typed_mod vt_empty W env0" "fresh_env env0" "tsorted alg vt_empty"
  by (simp_all add: env_typed_mod_def fresh_env_def tsorted_empty)

lemma tinv_empty: "scons A \<Longrightarrow> \<forall>p\<in>A. snd (fst p) \<le> 0 \<Longrightarrow> tinv ar 0 vt_empty A"
  by (simp add: tinv_def tacyc_empty tvars_env_def)

lemma gsol_empty_simps: "gsol alg ar vt_empty \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> (\<forall>v S. ground ar (\<rho> v S))"
  by (simp add: gsol_def tsol_def)


subsection \<open>Success: \<open>P\<^sub>'\<^sub>a ?X =?= P\<^sub>i c\<close>\<close>

abbreviation \<alpha> :: ptyp where "\<alpha> \<equiv> TVar (STR ''a'', 0) []"

definition X :: indexname where "X = (STR ''X'', 0)"

definition s\<^sub>1 :: pterm where "s\<^sub>1 = Const STR ''P'' (\<alpha> \<rightarrow>\<^sub>T \<kappa>) $ Var X \<alpha>"
definition t\<^sub>1 :: pterm where "t\<^sub>1 = Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) $ c"

context wf_algebra
begin

text \<open>The variable \<open>?X\<close> has type \<open>'a\<close>, and both sides have type \<open>o\<close>.\<close>

lemma problem\<^sub>1: "poly_problem alg ar (\<lambda>_. \<alpha>) env0 s\<^sub>1 t\<^sub>1 \<kappa>"
proof unfold_locales
  have "ptvars env0 s\<^sub>1 t\<^sub>1 = {((STR ''a'', 0), [])}" by (auto simp: ptvars_def s\<^sub>1_def t\<^sub>1_def c_def)
  moreover have "tinv ar 0 vt_empty {((STR ''a'', 0), [])}" by (rule tinv_empty) (simp_all add: scons_def)
  ultimately show "tinv ar (maxidx env0) (tyenv env0) (ptvars env0 s\<^sub>1 t\<^sub>1)" by simp
  show "pwf_term ar 0 s\<^sub>1" "pwf_term ar 0 t\<^sub>1" by (auto simp: pwf_term_def s\<^sub>1_def t\<^sub>1_def c_def tarity_def)
  show "has_type (\<lambda>_. \<alpha>) [] (tnormt (tyenv env0) s\<^sub>1) \<kappa>" "has_type (\<lambda>_. \<alpha>) [] (tnormt (tyenv env0) t\<^sub>1) \<kappa>"
    by (auto simp: s\<^sub>1_def t\<^sub>1_def c_def intro!: has_type.intros)
  show "below (maxidx env0) s\<^sub>1" "below (maxidx env0) t\<^sub>1"
    by (simp_all add: s\<^sub>1_def t\<^sub>1_def c_def X_def)
qed (simp_all add: env0_typed)

lemma patterns\<^sub>1: "ppat s\<^sub>1" "ppat t\<^sub>1"
proof -
  have "ppat (Var X \<alpha>)" using ppat_flex[of "[]" X \<alpha>] by (simp add: app_def)
  then show "ppat s\<^sub>1"
    using ppat_rigid[of "Const STR ''P'' (\<alpha> \<rightarrow>\<^sub>T \<kappa>)" "[Var X \<alpha>]"] by (simp add: s\<^sub>1_def is_rigid_def list_comb_def)
  have "ppat c" using ppat_rigid[of c "[]"] by (simp add: c_def is_rigid_def)
  then show "ppat t\<^sub>1"
    using ppat_rigid[of "Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)" "[c]"] by (simp add: t\<^sub>1_def c_def is_rigid_def list_comb_def)
qed

text \<open>The instance \<open>'a := i\<close> with \<open>?X := c\<close> is a unifier.\<close>

lemma unifiable\<^sub>1: "poly_problem.unifiable alg ar (\<lambda>_. \<alpha>) env0 s\<^sub>1 t\<^sub>1"
proof -
  define \<rho> :: tinst where "\<rho> = (\<lambda>v S. TFree STR ''i'' S)"
  define W where "W = (\<lambda>x :: indexname. \<iota>)"
  define \<sigma> where "\<sigma> = dB.Var(code (AVar X) := tr c)"
  have g: "gsol alg ar (tyenv env0) \<rho>" by (auto simp: gsol_empty_simps \<rho>_def wsinst_def intro: class_le_refl)
  have W: "(\<lambda>x. tsubst \<rho> \<alpha>) = W" by (simp add: W_def \<rho>_def)
  have "solution (\<lambda>x. tsubst \<rho> \<alpha>) (tau W) \<sigma> (instE \<rho> env0)"
    unfolding W solution_def
  proof (intro conjI)
    show "closed_on UNIV \<sigma>" by (simp add: closed_on_def \<sigma>_def c_def)
    show "typed_on (range code) (tau W) (tau W) \<sigma>"
      by (auto simp: typed_on_def \<sigma>_def c_def W_def)
    show "rigid_subst \<sigma>" by (auto simp: rigid_subst_def rigid_code_def \<sigma>_def)
    show "sat \<sigma> (instE \<rho> env0)" by (simp add: sat_def)
  qed
  moreover have "unifies \<sigma> (tr (inst \<rho> s\<^sub>1)) (tr (inst \<rho> t\<^sub>1))"
    by (simp add: unifies_def s\<^sub>1_def t\<^sub>1_def c_def \<sigma>_def \<rho>_def X_def)
  ultimately show ?thesis using g by blast
qed

text \<open>
  Hence \<^const>\<open>unify\<close> returns an environment \<open>env'\<close>; it is a most general unifier of all ground
  instances, and every ground solution of its type environment instantiates \<open>'a\<close> to \<open>i\<close>.
\<close>

theorem example_Ok:
  obtains env' where "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')"
    and "\<And>\<rho>. gsol alg ar (tyenv env') \<rho> \<Longrightarrow> \<rho> (STR ''a'', 0) [] = \<iota>"
proof -
  interpret ex: poly_problem alg ar "\<lambda>_. \<alpha>" env0 s\<^sub>1 t\<^sub>1 \<kappa> by (rule problem\<^sub>1)
  from ex.decides(1)[OF patterns\<^sub>1 env0_simps(6)] unifiable\<^sub>1 obtain env'
    where un: "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')" by blast
  show thesis
  proof (rule that[OF un])
    fix \<rho> assume g': "gsol alg ar (tyenv env') \<rho>"
    from ex.Ok_inv(7)[OF un g'] obtain W' where i: "env_inv ar W' (instE \<rho> env')" by blast
    note es = env_solution[OF env_invD(1-3)[OF i]]
    have uni: "unifies (env_sol (instE \<rho> env') W') (tr (inst \<rho> s\<^sub>1)) (tr (inst \<rho> t\<^sub>1))"
      by (rule ex.Ok_sound(3)[OF un g' solutionD(1,4)[OF es(1)]])
    have "strip_comb (inst \<rho> s\<^sub>1) = (Const STR ''P'' (tsubst \<rho> \<alpha> \<rightarrow>\<^sub>T \<kappa>), [Var X (tsubst \<rho> \<alpha>)])"
      "strip_comb (inst \<rho> t\<^sub>1) = (Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>), [c])"
      by (simp_all add: s\<^sub>1_def t\<^sub>1_def c_def strip_comb_def)
    from rigid_unifies(1)[OF this _ _ es(1) uni] show "\<rho> (STR ''a'', 0) [] = \<iota>"
      by (simp add: is_rigid_def)
  qed
qed

end


subsection \<open>Failure by sorts: \<open>Q\<^sub>'\<^sub>b ?Y =?= Q\<^sub>i c\<close>\<close>

definition \<beta> :: "pclass \<Rightarrow> ptyp" where "\<beta> cls = TVar (STR ''b'', 0) [cls]"

definition Y :: indexname where "Y = (STR ''Y'', 0)"

definition s\<^sub>2 :: "pclass \<Rightarrow> pterm" where "s\<^sub>2 cls = Const STR ''Q'' (\<beta> cls \<rightarrow>\<^sub>T \<kappa>) $ Var Y (\<beta> cls)"
definition t\<^sub>2 :: pterm where "t\<^sub>2 = Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) $ c"

context wf_algebra
begin

lemma problem\<^sub>2: "poly_problem alg ar (\<lambda>_. \<beta> cls) env0 (s\<^sub>2 cls) t\<^sub>2 \<kappa>"
proof unfold_locales
  have "ptvars env0 (s\<^sub>2 cls) t\<^sub>2 = {((STR ''b'', 0), [cls])}"
    by (auto simp: ptvars_def s\<^sub>2_def t\<^sub>2_def c_def \<beta>_def)
  moreover have "tinv ar 0 vt_empty {((STR ''b'', 0), [cls])}" by (rule tinv_empty) (simp_all add: scons_def)
  ultimately show "tinv ar (maxidx env0) (tyenv env0) (ptvars env0 (s\<^sub>2 cls) t\<^sub>2)" by simp
  show "pwf_term ar 0 (s\<^sub>2 cls)" "pwf_term ar 0 t\<^sub>2"
    by (auto simp: pwf_term_def s\<^sub>2_def t\<^sub>2_def c_def \<beta>_def tarity_def)
  show "has_type (\<lambda>_. \<beta> cls) [] (tnormt (tyenv env0) (s\<^sub>2 cls)) \<kappa>"
    "has_type (\<lambda>_. \<beta> cls) [] (tnormt (tyenv env0) t\<^sub>2) \<kappa>"
    by (auto simp: s\<^sub>2_def t\<^sub>2_def c_def intro!: has_type.intros)
  show "below (maxidx env0) (s\<^sub>2 cls)" "below (maxidx env0) t\<^sub>2"
    by (simp_all add: s\<^sub>2_def t\<^sub>2_def c_def Y_def \<beta>_def)
qed (simp_all add: env0_typed)

lemma patterns\<^sub>2: "ppat (s\<^sub>2 cls)" "ppat t\<^sub>2"
proof -
  have "ppat (Var Y (\<beta> cls))" using ppat_flex[of "[]" Y "\<beta> cls"] by (simp add: app_def)
  then show "ppat (s\<^sub>2 cls)"
    using ppat_rigid[of "Const STR ''Q'' (\<beta> cls \<rightarrow>\<^sub>T \<kappa>)" "[Var Y (\<beta> cls)]"]
    by (simp add: s\<^sub>2_def is_rigid_def list_comb_def)
  have "ppat c" using ppat_rigid[of c "[]"] by (simp add: c_def is_rigid_def)
  then show "ppat t\<^sub>2"
    using ppat_rigid[of "Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)" "[c]"] by (simp add: t\<^sub>2_def c_def is_rigid_def list_comb_def)
qed

text \<open>
  A unifier of a ground instance would identify the instances of the heads, so the instance of
  \<open>'b\<close> would be \<open>i\<close>, which does not have sort \<open>{cls}\<close>.
\<close>

lemma not_unifiable\<^sub>2: "\<not> poly_problem.unifiable alg ar (\<lambda>_. \<beta> cls) env0 (s\<^sub>2 cls) t\<^sub>2"
proof
  assume "poly_problem.unifiable alg ar (\<lambda>_. \<beta> cls) env0 (s\<^sub>2 cls) t\<^sub>2"
  then obtain \<rho> \<tau>' \<sigma> where g: "gsol alg ar (tyenv env0) \<rho>"
    and sol: "solution (\<lambda>x. tsubst \<rho> (\<beta> cls)) \<tau>' \<sigma> (instE \<rho> env0)"
    and uni: "unifies \<sigma> (tr (inst \<rho> (s\<^sub>2 cls))) (tr (inst \<rho> t\<^sub>2))" by blast
  have "strip_comb (inst \<rho> (s\<^sub>2 cls)) = (Const STR ''Q'' (tsubst \<rho> (\<beta> cls) \<rightarrow>\<^sub>T \<kappa>), [Var Y (tsubst \<rho> (\<beta> cls))])"
    "strip_comb (inst \<rho> t\<^sub>2) = (Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>), [c])"
    by (simp_all add: s\<^sub>2_def t\<^sub>2_def c_def strip_comb_def)
  from rigid_unifies(1)[OF this _ _ sol uni] have "\<rho> (STR ''b'', 0) [cls] = \<iota>"
    by (simp add: is_rigid_def \<beta>_def)
  moreover have "has_sort alg (\<rho> (STR ''b'', 0) [cls]) [cls]" using g by (simp add: gsol_def wsinst_def)
  ultimately show False by simp
qed

theorem example_Unif: "\<exists>u. unify alg (s\<^sub>2 cls) t\<^sub>2 env0 = Some (Err (Unif u))"
proof -
  interpret ex: poly_problem alg ar "\<lambda>_. \<beta> cls" env0 "s\<^sub>2 cls" t\<^sub>2 \<kappa> by (rule problem\<^sub>2)
  show ?thesis using ex.decides(2)[OF patterns\<^sub>2 env0_simps(6)] not_unifiable\<^sub>2 by blast
qed

end

end
