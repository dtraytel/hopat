section \<open>Examples\<close>

theory Pattern_Example
  imports Pattern_Correctness
begin

text \<open>
  We instantiate the locale \<^locale>\<open>unif_problem\<close> with five problems in the empty environment,
  for an arbitrary well-formed algebra and a signature that declares every constant with the most
  general type, and obtain their outcomes from the results of theory
  \<^theory>\<open>Pure_Pattern_Correctness.Pattern_Correctness\<close>. The base types are fixed type variables
  \<open>i\<close> and \<open>o\<close> without sort constraints.
  \<^item> \<open>\<lambda>x. ?F x =?= \<lambda>x. f x x\<close> is a unifiable pattern problem, so \<^const>\<open>unify\<close> returns a most
    general unifier;
  \<^item> \<open>P\<^sub>'\<^sub>a ?X =?= P\<^sub>i c\<close>, where \<open>P\<close> is used at the types \<open>'a \<Rightarrow> o\<close> and \<open>i \<Rightarrow> o\<close> for a schematic type
    variable \<open>'a\<close>: \<^const>\<open>unify\<close> returns an environment, and every solution of its type
    environment instantiates \<open>'a\<close> to \<open>i\<close>;
  \<^item> \<open>?Z =?= g ?Z\<close> is a pattern problem that is not unifiable (occurs check), so \<^const>\<open>unify\<close>
    fails with \<open>Unif\<close>;
  \<^item> \<open>Q\<^sub>'\<^sub>b ?Y =?= Q\<^sub>i c\<close>, where \<open>'b\<close> has sort \<open>{cls}\<close> for a class \<open>cls\<close>: as \<open>i\<close> does not have sort
    \<open>{cls}\<close>, the problem is not unifiable, so \<^const>\<open>unify\<close> fails with \<open>Unif\<close>;
  \<^item> \<open>?F a =?= b\<close> is not a pattern problem; \<^const>\<open>unify\<close> gives up with \<open>Pattern\<close>, although the
    problem is unifiable. The results cannot force this outcome, so we evaluate \<^const>\<open>unify\<close>.
\<close>

locale ex_csig = csig +
  assumes ctab_any: "ctab c = Some (TVar (STR ''a'', 0) [])"

locale ex_wf_csig = ex_csig ctab + wf_csig ctab alg ar
  for ctab :: "name \<Rightarrow> ptyp option" and alg :: algebra and ar :: "name \<Rightarrow> nat"

context ex_csig
begin

abbreviation \<iota> :: ptyp where "\<iota> \<equiv> TFree STR ''i'' []"
abbreviation \<kappa> :: ptyp where "\<kappa> \<equiv> TFree STR ''o'' []"

text \<open>The constants of the problems are not those of Pure's logic; they have every type.\<close>

lemma const_typ_ok_other[simp]: "c \<noteq> STR ''Pure.imp'' \<Longrightarrow> c \<noteq> STR ''Pure.all'' \<Longrightarrow> const_typ_ok c T"
  by (auto simp: const_typ_ok_def ctab_any intro!: exI[of _ "\<lambda>_ _. T"])

definition env0 :: env where "env0 = Envir 0 vt_empty vt_empty"

lemma env0_simps[simp]: "maxidx env0 = 0" "tyenv env0 = vt_empty" "vt_lookup (tenv env0) x = None"
  "etys env0 = {}" "etvars env0 = {}" "vtyp env0 W = W"
  by (simp_all add: env0_def etys_def etvars_def vtyp_def[abs_def])

lemma env_ppat_env0: "env_ppat env0"
  by (simp add: env_ppat_def)

lemma tnorm_vt_empty[simp]: "tnorm vt_empty T = T" "tnormt vt_empty t = t"
  by (simp_all add: tnorm_empty tnormt_empty)

lemma typed_env0[simp]: "typed env0 W Ts t T \<longleftrightarrow> has_type W Ts t T"
  by (simp add: typed_empty)

lemma vt_map_empty[simp]: "vt_map f vt_empty = vt_empty"
  by transfer auto

lemma instE_env0[simp]: "instE \<rho> env0 = env0"
  by (simp add: instE_def env0_def)

lemma tinv_empty: "scons A \<Longrightarrow> \<forall>p\<in>A. snd (fst p) \<le> 0 \<Longrightarrow> tinv ar 0 vt_empty A"
  by (simp add: tinv_def tacyc_empty tvars_env_def)

lemma gsol_empty_simps: "gsol alg ar vt_empty \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> (\<forall>v S. ground ar (\<rho> v S))"
  by (simp add: gsol_def tsol_def)

text \<open>The type instantiation that maps every type variable to \<open>i\<close>:\<close>

definition \<rho>\<^sub>i :: tinst where "\<rho>\<^sub>i = (\<lambda>v S. TFree STR ''i'' S)"

end

context ex_wf_csig
begin

lemma penv_inv_env0: "penv_inv alg ar W env0"
  by (simp add: penv_inv_def pwf_env_def wt_env_def fresh_env_def nacyc_def ndep_def acyclic_def
      tsorted_empty tinv_empty scons_def)

lemma gsol_\<rho>\<^sub>i: "gsol alg ar (tyenv env0) \<rho>\<^sub>i"
  by (auto simp: gsol_empty_simps \<rho>\<^sub>i_def wsinst_def intro: class_le_refl)

text \<open>Problems in the empty environment are well-formed if their types are:\<close>

lemma problem_env0:
  assumes "scons (ptvars env0 s t)" "\<forall>p\<in>ptvars env0 s t. snd (fst p) \<le> 0"
    and "pwf_term ar 0 s" "pwf_term ar 0 t" "has_type W [] s T" "has_type W [] t T"
    and "below 0 s" "below 0 t"
  shows "unif_problem ctab alg ar W env0 s t T"
  using assms by unfold_locales (simp_all add: penv_inv_env0 tinv_empty)

end


context ex_csig
begin

subsection \<open>Success: \<open>\<lambda>x. ?F x =?= \<lambda>x. f x x\<close>\<close>

definition f :: pterm where "f = Const STR ''f'' (\<iota> \<rightarrow>\<^sub>T \<iota> \<rightarrow>\<^sub>T \<iota>)"
definition F :: indexname where "F = (STR ''F'', 0)"

definition s\<^sub>1 :: pterm where "s\<^sub>1 = Abs STR ''x'' \<iota> (Var F (\<iota> \<rightarrow>\<^sub>T \<iota>) $ Bound 0)"
definition t\<^sub>1 :: pterm where "t\<^sub>1 = Abs STR ''x'' \<iota> (f $ Bound 0 $ Bound 0)"

end

context ex_wf_csig
begin

text \<open>Every schematic variable has type \<open>i \<Rightarrow> i\<close>.\<close>

lemma problem\<^sub>1: "unif_problem ctab alg ar (\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>) env0 s\<^sub>1 t\<^sub>1 (\<iota> \<rightarrow>\<^sub>T \<iota>)"
  by (rule problem_env0)
    (auto simp: ptvars_def scons_def pwf_term_def below_def s\<^sub>1_def t\<^sub>1_def f_def F_def tarity_def
      intro!: has_type.intros)

lemma patterns\<^sub>1: "ppat s\<^sub>1" "ppat t\<^sub>1"
proof -
  show "ppat s\<^sub>1"
    using ppat_flex[of "[0]" F "\<iota> \<rightarrow>\<^sub>T \<iota>"] by (auto simp: s\<^sub>1_def app_def intro: ppat_Abs)
  have "ppat (Bound 0)" using ppat_rigid[of "Bound 0" "[]"] by (simp add: is_rigid_def)
  then show "ppat t\<^sub>1"
    using ppat_rigid[of f "[Bound 0, Bound 0]"] by (auto simp: t\<^sub>1_def f_def is_rigid_def list_comb_def intro: ppat_Abs)
qed

text \<open>The substitution \<open>?F := \<lambda>x. f x x\<close> is a solution of the empty environment that unifies the terms.\<close>

lemma unifiable\<^sub>1: "unif_problem.unifiable ctab alg ar (\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>) env0 s\<^sub>1 t\<^sub>1"
proof -
  define V where "V = (\<lambda>x :: indexname. \<iota> \<rightarrow>\<^sub>T \<iota>)"
  define \<sigma> where "\<sigma> = dB.Var(code (AVar F) := dB.Abs (tr f \<degree> BVar 0 \<degree> BVar 0))"
  have "solution V (tau V) \<sigma> env0"
    unfolding solution_def
  proof (intro conjI)
    show "closed_on UNIV \<sigma>" by (simp add: closed_on_def \<sigma>_def f_def)
    show "typed_on (range code) (tau V) (tau V) \<sigma>"
      by (auto simp: typed_on_def \<sigma>_def f_def V_def)
    show "rigid_subst \<sigma>" by (auto simp: rigid_subst_def rigid_code_def \<sigma>_def)
    show "sat \<sigma> env0" by (simp add: sat_def)
  qed
  moreover have "unifies \<sigma> (tr s\<^sub>1) (tr t\<^sub>1)"
  proof -
    let ?u = "tr f \<degree> BVar 0 \<degree> BVar 0"
    have "dB.Abs ?u \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> ?u" using beta.beta[of ?u "BVar 0"] by (simp add: f_def)
    then have "dB.Abs (dB.Abs ?u \<degree> BVar 0) \<rightarrow>\<^sub>\<beta>\<^sup>* dB.Abs ?u" by (intro rtrancl_beta_Abs r_into_rtranclp)
    then have "mk_subst \<sigma> (tr s\<^sub>1) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst \<sigma> (tr t\<^sub>1)"
      by (simp add: s\<^sub>1_def t\<^sub>1_def f_def \<sigma>_def)
    then show ?thesis by (simp add: unifies_def beta_into_equiv)
  qed
  ultimately show ?thesis using gsol_\<rho>\<^sub>i
    by (intro exI[of _ \<rho>\<^sub>i] exI[of _ "tau V"] exI[of _ \<sigma>])
      (simp add: V_def \<rho>\<^sub>i_def s\<^sub>1_def t\<^sub>1_def f_def)
qed

text \<open>
  Hence \<^const>\<open>unify\<close> returns an environment \<open>env'\<close> with pattern bindings, relative to which the
  problem is well-formed again, and which is a most general unifier.
\<close>

theorem example_Ok\<^sub>1:
  obtains env' where "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')" "env_ppat env'"
    "\<exists>W'. unif_problem ctab alg ar W' env' s\<^sub>1 t\<^sub>1 (\<iota> \<rightarrow>\<^sub>T \<iota>)"
proof -
  interpret ex: unif_problem ctab alg ar "\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>" env0 s\<^sub>1 t\<^sub>1 "\<iota> \<rightarrow>\<^sub>T \<iota>" by (rule problem\<^sub>1)
  from ex.decides(1)[OF patterns\<^sub>1 env_ppat_env0] unifiable\<^sub>1 obtain env'
    where un: "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')" by blast
  show thesis by (rule that[OF un ex.Ok_patterns[OF un patterns\<^sub>1 env_ppat_env0] ex.Ok_inv(1)[OF un]])
qed

end


context ex_csig
begin

subsection \<open>Success with types: \<open>P\<^sub>'\<^sub>a ?X =?= P\<^sub>i c\<close>\<close>

abbreviation \<alpha> :: ptyp where "\<alpha> \<equiv> TVar (STR ''a'', 0) []"

definition c :: pterm where "c = Const STR ''c'' \<iota>"
definition X :: indexname where "X = (STR ''X'', 0)"

definition s\<^sub>2 :: pterm where "s\<^sub>2 = Const STR ''P'' (\<alpha> \<rightarrow>\<^sub>T \<kappa>) $ Var X \<alpha>"
definition t\<^sub>2 :: pterm where "t\<^sub>2 = Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) $ c"

end

context ex_wf_csig
begin

text \<open>The variable \<open>?X\<close> has type \<open>'a\<close>, and both sides have type \<open>o\<close>.\<close>

lemma problem\<^sub>2: "unif_problem ctab alg ar (\<lambda>_. \<alpha>) env0 s\<^sub>2 t\<^sub>2 \<kappa>"
proof (rule problem_env0)
  have "ptvars env0 s\<^sub>2 t\<^sub>2 = {((STR ''a'', 0), [])}" by (auto simp: ptvars_def s\<^sub>2_def t\<^sub>2_def c_def)
  then show "scons (ptvars env0 s\<^sub>2 t\<^sub>2)" "\<forall>p\<in>ptvars env0 s\<^sub>2 t\<^sub>2. snd (fst p) \<le> 0"
    by (simp_all add: scons_def)
qed (auto simp: pwf_term_def below_def s\<^sub>2_def t\<^sub>2_def c_def X_def tarity_def intro!: has_type.intros)

lemma patterns\<^sub>2: "ppat s\<^sub>2" "ppat t\<^sub>2"
proof -
  have "ppat (Var X \<alpha>)" using ppat_flex[of "[]" X \<alpha>] by (simp add: app_def)
  then show "ppat s\<^sub>2"
    using ppat_rigid[of "Const STR ''P'' (\<alpha> \<rightarrow>\<^sub>T \<kappa>)" "[Var X \<alpha>]"] by (simp add: s\<^sub>2_def is_rigid_def list_comb_def)
  have "ppat c" using ppat_rigid[of c "[]"] by (simp add: c_def is_rigid_def)
  then show "ppat t\<^sub>2"
    using ppat_rigid[of "Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)" "[c]"] by (simp add: t\<^sub>2_def c_def is_rigid_def list_comb_def)
qed

text \<open>The instance \<open>'a := i\<close> with \<open>?X := c\<close> is a unifier.\<close>

lemma unifiable\<^sub>2: "unif_problem.unifiable ctab alg ar (\<lambda>_. \<alpha>) env0 s\<^sub>2 t\<^sub>2"
proof -
  define V where "V = (\<lambda>x :: indexname. \<iota>)"
  define \<sigma> where "\<sigma> = dB.Var(code (AVar X) := tr c)"
  have "solution V (tau V) \<sigma> env0"
    unfolding solution_def
  proof (intro conjI)
    show "closed_on UNIV \<sigma>" by (simp add: closed_on_def \<sigma>_def c_def)
    show "typed_on (range code) (tau V) (tau V) \<sigma>"
      by (auto simp: typed_on_def \<sigma>_def c_def V_def)
    show "rigid_subst \<sigma>" by (auto simp: rigid_subst_def rigid_code_def \<sigma>_def)
    show "sat \<sigma> env0" by (simp add: sat_def)
  qed
  moreover have "unifies \<sigma> (tr (inst \<rho>\<^sub>i s\<^sub>2)) (tr (inst \<rho>\<^sub>i t\<^sub>2))"
    by (simp add: unifies_def s\<^sub>2_def t\<^sub>2_def c_def \<sigma>_def \<rho>\<^sub>i_def X_def)
  ultimately show ?thesis using gsol_\<rho>\<^sub>i
    by (intro exI[of _ \<rho>\<^sub>i] exI[of _ "tau V"] exI[of _ \<sigma>]) (simp add: V_def \<rho>\<^sub>i_def)
qed

text \<open>
  Hence \<^const>\<open>unify\<close> returns an environment \<open>env'\<close>, and every solution of its type environment
  instantiates \<open>'a\<close> to \<open>i\<close>.
\<close>

theorem example_Ok\<^sub>2:
  obtains env' where "unify alg s\<^sub>2 t\<^sub>2 env0 = Some (Ok env')"
    and "\<And>\<rho>. gsol alg ar (tyenv env') \<rho> \<Longrightarrow> \<rho> (STR ''a'', 0) [] = \<iota>"
proof -
  interpret ex: unif_problem ctab alg ar "\<lambda>_. \<alpha>" env0 s\<^sub>2 t\<^sub>2 \<kappa> by (rule problem\<^sub>2)
  from ex.decides(1)[OF patterns\<^sub>2 env_ppat_env0] unifiable\<^sub>2 obtain env'
    where un: "unify alg s\<^sub>2 t\<^sub>2 env0 = Some (Ok env')" by blast
  show thesis
  proof (rule that[OF un])
    fix \<rho> assume g': "gsol alg ar (tyenv env') \<rho>"
    from ex.Ok_instances[OF un g'] obtain V' where i: "env_inv ar V' (instE \<rho> env')" by blast
    note es = env_solution[OF env_invD(1-3)[OF i]]
    have "solves alg ar env' \<rho> (env_sol (instE \<rho> env') V')"
      using g' solutionD(1,4)[OF es(1)] by (simp add: solves_def)
    then have uni: "unifies (env_sol (instE \<rho> env') V') (tr (inst \<rho> s\<^sub>2)) (tr (inst \<rho> t\<^sub>2))"
      using ex.Ok_sound[OF un] by blast
    have "strip_comb (inst \<rho> s\<^sub>2) = (Const STR ''P'' (tsubst \<rho> \<alpha> \<rightarrow>\<^sub>T \<kappa>), [Var X (tsubst \<rho> \<alpha>)])"
      "strip_comb (inst \<rho> t\<^sub>2) = (Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>), [c])"
      by (simp_all add: s\<^sub>2_def t\<^sub>2_def c_def strip_comb_def)
    from rigid_unifies(1)[OF this _ _ es(1) uni] show "\<rho> (STR ''a'', 0) [] = \<iota>"
      by (simp add: is_rigid_def)
  qed
qed

end


context ex_csig
begin

subsection \<open>Failure by the occurs check: \<open>?Z =?= g ?Z\<close>\<close>

definition g :: pterm where "g = Const STR ''g'' (\<iota> \<rightarrow>\<^sub>T \<iota>)"
definition Z :: indexname where "Z = (STR ''Z'', 0)"

definition s\<^sub>3 :: pterm where "s\<^sub>3 = Var Z \<iota>"
definition t\<^sub>3 :: pterm where "t\<^sub>3 = g $ Var Z \<iota>"

end

context ex_wf_csig
begin

lemma problem\<^sub>3: "unif_problem ctab alg ar (\<lambda>_. \<iota>) env0 s\<^sub>3 t\<^sub>3 \<iota>"
  by (rule problem_env0)
    (auto simp: ptvars_def scons_def pwf_term_def below_def s\<^sub>3_def t\<^sub>3_def g_def Z_def tarity_def
      intro!: has_type.intros)

lemma patterns\<^sub>3: "ppat s\<^sub>3" "ppat t\<^sub>3"
proof -
  show "ppat s\<^sub>3" using ppat_flex[of "[]" Z \<iota>] by (simp add: s\<^sub>3_def app_def)
  then show "ppat t\<^sub>3"
    using ppat_rigid[of g "[Var Z \<iota>]"] by (simp add: s\<^sub>3_def t\<^sub>3_def g_def is_rigid_def list_comb_def)
qed

text \<open>
  A solution \<open>\<sigma>\<close> would satisfy \<open>\<sigma> ?Z \<equiv>\<^sub>\<beta>\<^sub>\<eta> g (\<sigma> ?Z)\<close>. As \<open>\<sigma> ?Z\<close> is well-typed, it has a normal
  form \<open>w\<close>; then \<open>g w\<close> is normal too, and both normal forms would coincide: \<open>w = g w\<close>.
\<close>

lemma normal_Var_App: "normal w \<Longrightarrow> normal (dB.Var n \<degree> w)"
  by auto

lemma not_unifiable\<^sub>3: "\<not> unif_problem.unifiable ctab alg ar (\<lambda>_. \<iota>) env0 s\<^sub>3 t\<^sub>3"
proof
  assume "unif_problem.unifiable ctab alg ar (\<lambda>_. \<iota>) env0 s\<^sub>3 t\<^sub>3"
  then obtain V \<tau>' \<sigma> where sol: "solution V \<tau>' \<sigma> env0" and uni: "unifies \<sigma> (tr s\<^sub>3) (tr t\<^sub>3)"
    by (auto simp: s\<^sub>3_def t\<^sub>3_def g_def)
  let ?x = "code (AVar Z)" and ?g = "code (AConst STR ''g'' (\<iota> \<rightarrow>\<^sub>T \<iota>))"
  note sd = solutionD[OF sol]
  have "\<sigma> ?g = dB.Var ?g" by (rule rigid_substD[OF sd(3)]) simp
  with uni have eq: "\<sigma> ?x \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var ?g \<degree> \<sigma> ?x" by (simp add: unifies_def s\<^sub>3_def t\<^sub>3_def g_def)
  obtain w where w: "\<beta>\<eta>cl (\<sigma> ?x) w" "normal w"
    using nf_typed[OF typed_onD[OF sd(2) rangeI[of code "AVar Z"]]] by blast
  have "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> ?x" by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]])
  also note eq
  also have "dB.Var ?g \<degree> \<sigma> ?x \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var ?g \<degree> w" by (rule equiv_AppR[OF \<beta>\<eta>cl_into_equiv[OF w(1)]])
  finally have "\<beta>\<eta>cl w (dB.Var ?g \<degree> w)" by (rule equiv_\<beta>\<eta>cl_normal[OF _ normal_Var_App[OF w(2)]])
  then have "w = dB.Var ?g \<degree> w" using w(2) by (cases rule: converse_rtranclpE) auto
  then have "size w = size (dB.Var ?g \<degree> w)" by (rule arg_cong)
  then show False by simp
qed

theorem example_Unif\<^sub>3: "\<exists>u. unify alg s\<^sub>3 t\<^sub>3 env0 = Some (Err (Unif u))"
proof -
  interpret ex: unif_problem ctab alg ar "\<lambda>_. \<iota>" env0 s\<^sub>3 t\<^sub>3 \<iota> by (rule problem\<^sub>3)
  show ?thesis using ex.decides(2)[OF patterns\<^sub>3 env_ppat_env0] not_unifiable\<^sub>3 by blast
qed

end


context ex_csig
begin

subsection \<open>Failure by sorts: \<open>Q\<^sub>'\<^sub>b ?Y =?= Q\<^sub>i c\<close>\<close>

definition \<beta> :: "pclass \<Rightarrow> ptyp" where "\<beta> cls = TVar (STR ''b'', 0) [cls]"

definition Y :: indexname where "Y = (STR ''Y'', 0)"

definition s\<^sub>4 :: "pclass \<Rightarrow> pterm" where "s\<^sub>4 cls = Const STR ''Q'' (\<beta> cls \<rightarrow>\<^sub>T \<kappa>) $ Var Y (\<beta> cls)"
definition t\<^sub>4 :: pterm where "t\<^sub>4 = Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) $ c"

end

context ex_wf_csig
begin

lemma problem\<^sub>4: "unif_problem ctab alg ar (\<lambda>_. \<beta> cls) env0 (s\<^sub>4 cls) t\<^sub>4 \<kappa>"
proof (rule problem_env0)
  have "ptvars env0 (s\<^sub>4 cls) t\<^sub>4 = {((STR ''b'', 0), [cls])}"
    by (auto simp: ptvars_def s\<^sub>4_def t\<^sub>4_def c_def \<beta>_def)
  then show "scons (ptvars env0 (s\<^sub>4 cls) t\<^sub>4)" "\<forall>p\<in>ptvars env0 (s\<^sub>4 cls) t\<^sub>4. snd (fst p) \<le> 0"
    by (simp_all add: scons_def)
qed (auto simp: pwf_term_def below_def s\<^sub>4_def t\<^sub>4_def c_def \<beta>_def Y_def tarity_def intro!: has_type.intros)

lemma patterns\<^sub>4: "ppat (s\<^sub>4 cls)" "ppat t\<^sub>4"
proof -
  have "ppat (Var Y (\<beta> cls))" using ppat_flex[of "[]" Y "\<beta> cls"] by (simp add: app_def)
  then show "ppat (s\<^sub>4 cls)"
    using ppat_rigid[of "Const STR ''Q'' (\<beta> cls \<rightarrow>\<^sub>T \<kappa>)" "[Var Y (\<beta> cls)]"]
    by (simp add: s\<^sub>4_def is_rigid_def list_comb_def)
  have "ppat c" using ppat_rigid[of c "[]"] by (simp add: c_def is_rigid_def)
  then show "ppat t\<^sub>4"
    using ppat_rigid[of "Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)" "[c]"] by (simp add: t\<^sub>4_def c_def is_rigid_def list_comb_def)
qed

text \<open>
  A unifier of a ground instance would identify the instances of the heads, so the instance of
  \<open>'b\<close> would be \<open>i\<close>, which does not have sort \<open>{cls}\<close>.
\<close>

lemma not_unifiable\<^sub>4: "\<not> unif_problem.unifiable ctab alg ar (\<lambda>_. \<beta> cls) env0 (s\<^sub>4 cls) t\<^sub>4"
proof
  assume "unif_problem.unifiable ctab alg ar (\<lambda>_. \<beta> cls) env0 (s\<^sub>4 cls) t\<^sub>4"
  then obtain \<rho> V \<tau>' \<sigma> where g: "gsol alg ar (tyenv env0) \<rho>" and sol: "solution V \<tau>' \<sigma> env0"
    and uni: "unifies \<sigma> (tr (inst \<rho> (s\<^sub>4 cls))) (tr (inst \<rho> t\<^sub>4))" by auto
  have "strip_comb (inst \<rho> (s\<^sub>4 cls)) = (Const STR ''Q'' (tsubst \<rho> (\<beta> cls) \<rightarrow>\<^sub>T \<kappa>), [Var Y (tsubst \<rho> (\<beta> cls))])"
    "strip_comb (inst \<rho> t\<^sub>4) = (Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>), [c])"
    by (simp_all add: s\<^sub>4_def t\<^sub>4_def c_def strip_comb_def)
  from rigid_unifies(1)[OF this _ _ sol uni] have "\<rho> (STR ''b'', 0) [cls] = \<iota>"
    by (simp add: is_rigid_def \<beta>_def)
  moreover have "has_sort alg (\<rho> (STR ''b'', 0) [cls]) [cls]" using g by (simp add: gsol_def wsinst_def)
  ultimately show False by simp
qed

theorem example_Unif\<^sub>4: "\<exists>u. unify alg (s\<^sub>4 cls) t\<^sub>4 env0 = Some (Err (Unif u))"
proof -
  interpret ex: unif_problem ctab alg ar "\<lambda>_. \<beta> cls" env0 "s\<^sub>4 cls" t\<^sub>4 \<kappa> by (rule problem\<^sub>4)
  show ?thesis using ex.decides(2)[OF patterns\<^sub>4 env_ppat_env0] not_unifiable\<^sub>4 by blast
qed

end


context ex_csig
begin

subsection \<open>Giving up: \<open>?F a =?= b\<close>\<close>

definition a :: pterm where "a = Const STR ''a'' \<iota>"
definition b :: pterm where "b = Const STR ''b'' \<iota>"

definition s\<^sub>5 :: pterm where "s\<^sub>5 = Var F (\<iota> \<rightarrow>\<^sub>T \<iota>) $ a"
definition t\<^sub>5 :: pterm where "t\<^sub>5 = b"

end

context ex_wf_csig
begin

lemma problem\<^sub>5: "unif_problem ctab alg ar (\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>) env0 s\<^sub>5 t\<^sub>5 \<iota>"
  by (rule problem_env0)
    (auto simp: ptvars_def scons_def pwf_term_def below_def s\<^sub>5_def t\<^sub>5_def a_def b_def F_def tarity_def
      intro!: has_type.intros)

text \<open>\<^const>\<open>unify\<close> gives up because the argument \<open>a\<close> of \<open>?F\<close> is not a bound variable.\<close>

theorem example_Pattern: "unify alg s\<^sub>5 t\<^sub>5 env0 = Some (Err Pattern)"
  unfolding unify_def s\<^sub>5_def t\<^sub>5_def a_def b_def env0_def
  by (subst unif.simps) (simp add: head_norm.simps[of _ "_ $ _"] head_norm.simps[of _ "pterm.Var _ _"]
    head_norm.simps[of _ "Const _ _"] lookup_def ints_of'_def unified_def bindM_def return_def
    raise_def strip_comb_def)

text \<open>
  This is consistent with @{thm [source] unif_problem.Pattern_not_pattern}: \<open>s\<^sub>5\<close> is not a pattern.
  Yet the problem is unifiable, by \<open>?F := \<lambda>x. b\<close>: giving up is not failure.
\<close>

lemma not_pattern\<^sub>5: "\<not> ppat s\<^sub>5"
proof -
  interpret ex: unif_problem ctab alg ar "\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>" env0 s\<^sub>5 t\<^sub>5 \<iota> by (rule problem\<^sub>5)
  show ?thesis using ex.Pattern_not_pattern[OF example_Pattern] env_ppat_env0
    by (simp add: t\<^sub>5_def b_def is_rigid_def ppat_rigid[of "Const STR ''b'' \<iota>" "[]", simplified])
qed

lemma unifiable\<^sub>5: "unif_problem.unifiable ctab alg ar (\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>) env0 s\<^sub>5 t\<^sub>5"
proof -
  define V where "V = (\<lambda>x :: indexname. \<iota> \<rightarrow>\<^sub>T \<iota>)"
  define \<sigma> where "\<sigma> = dB.Var(code (AVar F) := dB.Abs (tr b))"
  have "solution V (tau V) \<sigma> env0"
    unfolding solution_def
  proof (intro conjI)
    show "closed_on UNIV \<sigma>" by (simp add: closed_on_def \<sigma>_def b_def)
    show "typed_on (range code) (tau V) (tau V) \<sigma>"
      by (auto simp: typed_on_def \<sigma>_def b_def V_def)
    show "rigid_subst \<sigma>" by (auto simp: rigid_subst_def rigid_code_def \<sigma>_def)
    show "sat \<sigma> env0" by (simp add: sat_def)
  qed
  moreover have "unifies \<sigma> (tr s\<^sub>5) (tr t\<^sub>5)"
  proof -
    have "dB.Abs (tr b) \<degree> tr a \<rightarrow>\<^sub>\<beta> tr b" using beta.beta[of "tr b" "tr a"] by (simp add: a_def b_def)
    then have "mk_subst \<sigma> (tr s\<^sub>5) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst \<sigma> (tr t\<^sub>5)"
      by (auto simp: s\<^sub>5_def t\<^sub>5_def a_def b_def \<sigma>_def)
    then show ?thesis by (simp add: unifies_def beta_into_equiv)
  qed
  ultimately show ?thesis using gsol_\<rho>\<^sub>i
    by (intro exI[of _ \<rho>\<^sub>i] exI[of _ "tau V"] exI[of _ \<sigma>])
      (simp add: V_def \<rho>\<^sub>i_def s\<^sub>5_def t\<^sub>5_def a_def b_def)
qed

end

end
