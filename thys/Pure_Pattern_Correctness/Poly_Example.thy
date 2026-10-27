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

lemma tinv_empty: "finite A \<Longrightarrow> scons A \<Longrightarrow> \<forall>p\<in>A. snd (fst p) \<le> 0 \<Longrightarrow> tinv ar 0 vt_empty A"
  by (simp add: tinv_def tacyc_empty tvars_env_def)

lemma gsol_empty_simps: "gsol alg ar vt_empty \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> (\<forall>v S. ground ar (\<rho> v S))"
  by (simp add: gsol_def tsol_def)


subsection \<open>Success: \<open>P\<^sub>'\<^sub>a ?X =?= P\<^sub>i c\<close>\<close>

abbreviation \<alpha> :: ptyp where "\<alpha> \<equiv> TVar (STR ''a'', 0) []"

definition X :: indexname where "X = (STR ''X'', 0)"

definition s\<^sub>1 :: pterm where "s\<^sub>1 = Const STR ''P'' (\<alpha> \<rightarrow>\<^sub>T \<kappa>) $ Var X \<alpha>"
definition t\<^sub>1 :: pterm where "t\<^sub>1 = Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) $ c"

definition A\<^sub>1 :: "(indexname \<times> psort) set" where "A\<^sub>1 = {((STR ''a'', 0), [])}"

context wf_algebra
begin

lemma problem\<^sub>1: "poly_problem alg ar A\<^sub>1 env0 s\<^sub>1 t\<^sub>1"
proof unfold_locales
  show "finite A\<^sub>1" "tinv ar (maxidx env0) (tyenv env0) A\<^sub>1" "tsorted alg (tyenv env0)"
    by (auto simp: A\<^sub>1_def scons_def intro!: tinv_empty tsorted_empty)
  show "\<forall>T\<in>tys s\<^sub>1 \<union> tys t\<^sub>1 \<union> etys env0. tyw ar (tyenv env0) A\<^sub>1 T"
    by (auto simp: s\<^sub>1_def t\<^sub>1_def c_def A\<^sub>1_def tarity_def intro!: tyw_tvars)
  show "below (maxidx env0) s\<^sub>1" "below (maxidx env0) t\<^sub>1" "nacyc env0"
    by (simp_all add: s\<^sub>1_def t\<^sub>1_def c_def X_def)
  fix \<rho> assume "gsol alg ar (tyenv env0) \<rho>"
  then have g: "\<forall>v S. ground ar (\<rho> v S)" by (simp add: gsol_def)
  have "inst_ok ar (\<lambda>x. tsubst \<rho> \<alpha>) \<rho> [] s\<^sub>1 t\<^sub>1 env0"
    by (rule inst_ok_typed[OF _ _ _ _ _ _ _ g, where W = "\<lambda>_. \<alpha>" and T = \<kappa>])
      (auto simp: pwf_term_def s\<^sub>1_def t\<^sub>1_def c_def tarity_def env_typed_def fresh_env_def
        intro!: has_type.intros)
  then show "\<exists>W. inst_ok ar W \<rho> [] s\<^sub>1 t\<^sub>1 env0" by blast
qed

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

lemma unifiable\<^sub>1: "poly_problem.unifiable alg ar env0 s\<^sub>1 t\<^sub>1"
proof -
  define \<rho> :: tinst where "\<rho> = (\<lambda>v S. TFree STR ''i'' S)"
  define W where "W = (\<lambda>x :: indexname. \<iota>)"
  define \<sigma> where "\<sigma> = dB.Var(code (AVar X) := tr c)"
  have g: "gsol alg ar (tyenv env0) \<rho>" by (auto simp: gsol_empty_simps \<rho>_def wsinst_def intro: class_le_refl)
  have "inst_ok ar (\<lambda>x. tsubst \<rho> \<alpha>) \<rho> [] s\<^sub>1 t\<^sub>1 env0"
    by (rule inst_ok_typed[where W = "\<lambda>_. \<alpha>" and T = \<kappa>])
      (auto simp: pwf_term_def s\<^sub>1_def t\<^sub>1_def c_def tarity_def env_typed_def fresh_env_def \<rho>_def
        intro!: has_type.intros)
  then have i: "inst_ok ar W \<rho> [] s\<^sub>1 t\<^sub>1 env0" by (simp add: W_def \<rho>_def)
  have "solution W (tau W) \<sigma> (instE \<rho> env0)"
    unfolding solution_def
  proof (intro conjI)
    show "closed_on UNIV \<sigma>" by (simp add: closed_on_def \<sigma>_def c_def)
    show "typed_on (range code) (tau W) (tau W) \<sigma>"
      by (auto simp: typed_on_def \<sigma>_def c_def W_def)
    show "rigid_subst \<sigma>" by (auto simp: rigid_subst_def rigid_code_def \<sigma>_def)
    show "sat \<sigma> (instE \<rho> env0)" by (simp add: sat_def)
  qed
  moreover have "unifies \<sigma> (tr (inst \<rho> s\<^sub>1)) (tr (inst \<rho> t\<^sub>1))"
    by (simp add: unifies_def s\<^sub>1_def t\<^sub>1_def c_def \<sigma>_def \<rho>_def X_def)
  ultimately show ?thesis using g i by blast
qed

text \<open>
  Hence \<^const>\<open>unify\<close> returns an environment \<open>env'\<close>; it is a most general unifier of all ground
  instances, and every ground solution of its type environment instantiates \<open>'a\<close> to \<open>i\<close>.
\<close>

theorem example_Ok:
  obtains env' where "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')"
    and "\<And>\<rho>. gsol alg ar (tyenv env') \<rho> \<Longrightarrow> \<rho> (STR ''a'', 0) [] = \<iota>"
proof -
  interpret ex: poly_problem alg ar A\<^sub>1 env0 s\<^sub>1 t\<^sub>1 by (rule problem\<^sub>1)
  from ex.decides(1)[OF patterns\<^sub>1 env0_simps(6)] unifiable\<^sub>1 obtain env'
    where un: "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')" by blast
  show thesis
  proof (rule that[OF un])
    fix \<rho> assume g': "gsol alg ar (tyenv env') \<rho>"
    note inv = ex.Ok_inv[OF un]
    have g: "gsol alg ar (tyenv env0) \<rho>" by (rule ex.Ok_sound(1)[OF un g'])
    from ex.instances[OF g] obtain W where i: "inst_ok ar W \<rho> [] s\<^sub>1 t\<^sub>1 env0" by blast
    from inv(8)[OF g' i] obtain W' where te: "ty_ext ar W (instE \<rho> env0) W' (instE \<rho> env')" by blast
    have ety: "env_typed W' (instE \<rho> env')" and wf: "wf_env ar (instE \<rho> env')"
      using te by (simp_all add: ty_ext_def)
    have ac: "acyc (instE \<rho> env')" using acyc_instE[OF ety] inv(7) by simp
    note es = env_solution[OF ac wf ety]
    let ?\<sigma> = "env_sol (instE \<rho> env') W'"
    have uni: "unifies ?\<sigma> (tr (inst \<rho> s\<^sub>1)) (tr (inst \<rho> t\<^sub>1))"
      using env_equivD[OF ex.Ok_sound(2)[OF un g'] solutionD(1,4)[OF es(1)]] by (simp add: unifies_def)
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

definition A\<^sub>2 :: "pclass \<Rightarrow> (indexname \<times> psort) set" where "A\<^sub>2 cls = {((STR ''b'', 0), [cls])}"

context wf_algebra
begin

lemma problem\<^sub>2: "poly_problem alg ar (A\<^sub>2 cls) env0 (s\<^sub>2 cls) t\<^sub>2"
proof unfold_locales
  show "finite (A\<^sub>2 cls)" "tinv ar (maxidx env0) (tyenv env0) (A\<^sub>2 cls)" "tsorted alg (tyenv env0)"
    by (auto simp: A\<^sub>2_def scons_def intro!: tinv_empty tsorted_empty)
  show "\<forall>T\<in>tys (s\<^sub>2 cls) \<union> tys t\<^sub>2 \<union> etys env0. tyw ar (tyenv env0) (A\<^sub>2 cls) T"
    by (auto simp: s\<^sub>2_def t\<^sub>2_def c_def A\<^sub>2_def \<beta>_def tarity_def intro!: tyw_tvars)
  show "below (maxidx env0) (s\<^sub>2 cls)" "below (maxidx env0) t\<^sub>2" "nacyc env0"
    by (simp_all add: s\<^sub>2_def t\<^sub>2_def c_def Y_def)
  fix \<rho> assume "gsol alg ar (tyenv env0) \<rho>"
  then have g: "\<forall>v S. ground ar (\<rho> v S)" by (simp add: gsol_def)
  have "inst_ok ar (\<lambda>x. tsubst \<rho> (\<beta> cls)) \<rho> [] (s\<^sub>2 cls) t\<^sub>2 env0"
    by (rule inst_ok_typed[OF _ _ _ _ _ _ _ g, where W = "\<lambda>_. \<beta> cls" and T = \<kappa>])
      (auto simp: pwf_term_def s\<^sub>2_def t\<^sub>2_def c_def \<beta>_def tarity_def env_typed_def fresh_env_def
        intro!: has_type.intros)
  then show "\<exists>W. inst_ok ar W \<rho> [] (s\<^sub>2 cls) t\<^sub>2 env0" by blast
qed

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

lemma not_unifiable\<^sub>2: "\<not> poly_problem.unifiable alg ar env0 (s\<^sub>2 cls) t\<^sub>2"
proof
  assume "poly_problem.unifiable alg ar env0 (s\<^sub>2 cls) t\<^sub>2"
  then obtain \<rho> W \<tau>' \<sigma> where g: "gsol alg ar (tyenv env0) \<rho>" and sol: "solution W \<tau>' \<sigma> (instE \<rho> env0)"
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
  interpret ex: poly_problem alg ar "A\<^sub>2 cls" env0 "s\<^sub>2 cls" t\<^sub>2 by (rule problem\<^sub>2)
  show ?thesis using ex.decides(2)[OF patterns\<^sub>2 env0_simps(6)] not_unifiable\<^sub>2 by blast
qed

end

end
