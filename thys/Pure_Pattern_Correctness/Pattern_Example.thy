section \<open>Example\<close>

theory Pattern_Example
  imports Pattern_Correctness
begin

text \<open>
  We instantiate the locale \<^locale>\<open>unif_problem\<close> with three problems in the empty
  environment, over a base type \<open>i\<close>, and obtain their outcomes from the results of theory
  \<^theory>\<open>Pure_Pattern_Correctness.Pattern_Correctness\<close>:
  \<^item> \<open>\<lambda>x. ?F x =?= \<lambda>x. f x x\<close> is a unifiable pattern problem, so \<^const>\<open>unify\<close> returns a most
    general unifier;
  \<^item> \<open>?X =?= g ?X\<close> is a pattern problem that is not unifiable (occurs check), so \<^const>\<open>unify\<close>
    fails with \<open>Unif\<close>;
  \<^item> \<open>?F a =?= b\<close> is not a pattern problem; \<^const>\<open>unify\<close> gives up with \<open>Pattern\<close>, although the
    problem is unifiable.
  The results cannot force the outcome \<open>Pattern\<close>, so in the last case we evaluate \<^const>\<open>unify\<close>.
\<close>

abbreviation \<iota> :: ptyp where "\<iota> \<equiv> Type STR ''i'' []"

text \<open>All type constructors other than \<open>fun\<close> are nullary.\<close>

definition ar :: "name \<Rightarrow> nat" where "ar = (\<lambda>_. 0)"

definition env0 :: env where "env0 = Envir 0 vt_empty vt_empty"

lemma vt_is_empty_vt_empty: "vt_is_empty vt_empty"
  by transfer simp

lemma env_inv_env0: "env_inv ar W env0"
  by (auto simp: env_inv_def acyc_def dep_def lk_def wf_env_def env_typed_def fresh_env_def env0_def
    vt_is_empty_vt_empty acyclic_def)

lemma env_ppat_env0: "env_ppat env0"
  by (simp add: env_ppat_def env0_def)


subsection \<open>Success: \<open>\<lambda>x. ?F x =?= \<lambda>x. f x x\<close>\<close>

definition f :: pterm where "f = Const STR ''f'' (\<iota> \<rightarrow>\<^sub>T \<iota> \<rightarrow>\<^sub>T \<iota>)"
definition F :: indexname where "F = (STR ''F'', 0)"

definition s :: pterm where "s = Abs STR ''x'' \<iota> (Var F (\<iota> \<rightarrow>\<^sub>T \<iota>) $ Bound 0)"
definition t :: pterm where "t = Abs STR ''x'' \<iota> (f $ Bound 0 $ Bound 0)"

text \<open>Every schematic variable has type \<open>i \<Rightarrow> i\<close>.\<close>

definition V :: "indexname \<Rightarrow> ptyp" where "V = (\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>)"

interpretation ex: unif_problem ar V env0 s t "\<iota> \<rightarrow>\<^sub>T \<iota>"
proof
  show "env_inv ar V env0" by (rule env_inv_env0)
  show "wf_term ar 0 s" "wf_term ar 0 t"
    by (simp_all add: wf_term_def s_def t_def f_def ar_def)
  show "has_type V [] s (\<iota> \<rightarrow>\<^sub>T \<iota>)" "has_type V [] t (\<iota> \<rightarrow>\<^sub>T \<iota>)"
    by (auto simp: s_def t_def f_def V_def intro!: has_type.intros)
  show "below (maxidx env0) s" "below (maxidx env0) t"
    by (simp_all add: below_def s_def t_def f_def F_def env0_def)
qed

text \<open>The problem is a pattern problem.\<close>

lemma patterns: "ppat s" "ppat t" "env_ppat env0"
proof -
  show "ppat s"
    using ppat_flex[of "[0]" F "\<iota> \<rightarrow>\<^sub>T \<iota>"] by (auto simp: s_def app_def intro: ppat_Abs)
  have "ppat (Bound 0)" using ppat_rigid[of "Bound 0" "[]"] by (simp add: is_rigid_def)
  then show "ppat t"
    using ppat_rigid[of f "[Bound 0, Bound 0]"] by (auto simp: t_def f_def is_rigid_def list_comb_def intro: ppat_Abs)
  show "env_ppat env0" by (rule env_ppat_env0)
qed

text \<open>The substitution \<open>?F := \<lambda>x. f x x\<close> is a solution of the empty environment that unifies the terms.\<close>

definition \<sigma>\<^sub>0 :: "nat \<Rightarrow> dB" where
  "\<sigma>\<^sub>0 = dB.Var(code (AVar F) := dB.Abs (tr f \<degree> BVar 0 \<degree> BVar 0))"

lemma unifiable: "ex.unifiable"
proof (intro exI conjI)
  show "solution V (tau V) \<sigma>\<^sub>0 env0"
    unfolding solution_def
  proof (intro conjI)
    show "closed_on UNIV \<sigma>\<^sub>0" by (simp add: closed_on_def \<sigma>\<^sub>0_def f_def)
    show "typed_on (range code) (tau V) (tau V) \<sigma>\<^sub>0"
      by (auto simp: typed_on_def \<sigma>\<^sub>0_def f_def V_def)
    show "rigid_subst \<sigma>\<^sub>0" by (auto simp: rigid_subst_def rigid_code_def \<sigma>\<^sub>0_def)
    show "sat \<sigma>\<^sub>0 env0" by (simp add: sat_def env0_def)
  qed
  let ?u = "tr f \<degree> BVar 0 \<degree> BVar 0"
  have "dB.Abs ?u \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> ?u" using beta.beta[of ?u "BVar 0"] by (simp add: f_def)
  then have "dB.Abs (dB.Abs ?u \<degree> BVar 0) \<rightarrow>\<^sub>\<beta>\<^sup>* dB.Abs ?u" by (intro rtrancl_beta_Abs r_into_rtranclp)
  then have "mk_subst \<sigma>\<^sub>0 (tr s) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst \<sigma>\<^sub>0 (tr t)"
    by (simp add: s_def t_def f_def \<sigma>\<^sub>0_def)
  then show "unifies \<sigma>\<^sub>0 (tr s) (tr t)" by (simp add: unifies_def beta_into_equiv)
qed

text \<open>
  Hence \<^const>\<open>unify\<close> returns an environment \<open>env'\<close>, which satisfies the invariant again, has pattern
  bindings, and is a most general unifier: its solutions unify \<open>s\<close> and \<open>t\<close>, and every unifier,
  for example \<^const>\<open>\<sigma>\<^sub>0\<close>, extends to a solution of \<open>env'\<close>.
\<close>

theorem example_Ok:
  obtains env' where "unify alg s t env0 = Some (Ok env')"
    and "extends env' env0" "\<exists>V'. env_inv ar V' env'" "env_ppat env'"
    and "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow> unifies \<sigma> (tr s) (tr t)"
    and "\<And>\<tau>' \<sigma>. solution V \<tau>' \<sigma> env0 \<Longrightarrow> unifies \<sigma> (tr s) (tr t) \<Longrightarrow>
      \<exists>V' \<sigma>'. agree 0 \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' env'"
proof -
  from ex.decides(1)[OF patterns] unifiable obtain env' where un: "unify alg s t env0 = Some (Ok env')"
    by blast
  show thesis
  proof (rule that[OF un])
    from ex.Ok_inv[OF un] show "extends env' env0" "\<exists>V'. env_inv ar V' env'" by auto
    show "env_ppat env'" by (rule ex.Ok_patterns[OF un patterns])
    show "unifies \<sigma> (tr s) (tr t)" if "closed_on UNIV \<sigma>" "sat \<sigma> env'" for \<sigma>
      using ex.Ok_sound[OF un that] by simp
    show "\<exists>V' \<sigma>'. agree 0 \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' env'"
      if "solution V \<tau>' \<sigma> env0" "unifies \<sigma> (tr s) (tr t)" for \<tau>' \<sigma>
      using ex.Ok_most_general[OF un that] by (auto simp: env0_def)
  qed
qed


subsection \<open>Failure: \<open>?X =?= g ?X\<close>\<close>

definition g :: pterm where "g = Const STR ''g'' (\<iota> \<rightarrow>\<^sub>T \<iota>)"
definition X :: indexname where "X = (STR ''X'', 0)"

definition s\<^sub>2 :: pterm where "s\<^sub>2 = Var X \<iota>"
definition t\<^sub>2 :: pterm where "t\<^sub>2 = g $ Var X \<iota>"

definition V\<^sub>2 :: "indexname \<Rightarrow> ptyp" where "V\<^sub>2 = (\<lambda>_. \<iota>)"

interpretation ex\<^sub>2: unif_problem ar V\<^sub>2 env0 s\<^sub>2 t\<^sub>2 \<iota>
proof
  show "env_inv ar V\<^sub>2 env0" by (rule env_inv_env0)
  show "wf_term ar 0 s\<^sub>2" "wf_term ar 0 t\<^sub>2"
    by (simp_all add: wf_term_def s\<^sub>2_def t\<^sub>2_def g_def ar_def)
  show "has_type V\<^sub>2 [] s\<^sub>2 \<iota>" "has_type V\<^sub>2 [] t\<^sub>2 \<iota>"
    by (auto simp: s\<^sub>2_def t\<^sub>2_def g_def V\<^sub>2_def intro!: has_type.intros)
  show "below (maxidx env0) s\<^sub>2" "below (maxidx env0) t\<^sub>2"
    by (simp_all add: below_def s\<^sub>2_def t\<^sub>2_def g_def X_def env0_def)
qed

lemma patterns\<^sub>2: "ppat s\<^sub>2" "ppat t\<^sub>2"
proof -
  show "ppat s\<^sub>2" using ppat_flex[of "[]" X \<iota>] by (simp add: s\<^sub>2_def app_def)
  then show "ppat t\<^sub>2"
    using ppat_rigid[of g "[Var X \<iota>]"] by (simp add: s\<^sub>2_def t\<^sub>2_def g_def is_rigid_def list_comb_def)
qed

text \<open>
  A solution \<open>\<sigma>\<close> would satisfy \<open>\<sigma> ?X \<equiv>\<^sub>\<beta>\<^sub>\<eta> g (\<sigma> ?X)\<close>. As \<open>\<sigma> ?X\<close> is well-typed, it has a normal
  form \<open>w\<close>; then \<open>g w\<close> is normal too, and both normal forms would coincide: \<open>w = g w\<close>.
\<close>

lemma normal_Var_App: "normal w \<Longrightarrow> normal (dB.Var n \<degree> w)"
  by auto

lemma not_unifiable\<^sub>2: "\<not> ex\<^sub>2.unifiable"
proof
  assume "ex\<^sub>2.unifiable"
  then obtain \<tau>' \<sigma> where sol: "solution V\<^sub>2 \<tau>' \<sigma> env0" and uni: "unifies \<sigma> (tr s\<^sub>2) (tr t\<^sub>2)" by blast
  let ?x = "code (AVar X)" and ?g = "code (AConst STR ''g'' (\<iota> \<rightarrow>\<^sub>T \<iota>))"
  note sd = solutionD[OF sol]
  have "\<sigma> ?g = dB.Var ?g" by (rule rigid_substD[OF sd(3)]) simp
  with uni have eq: "\<sigma> ?x \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var ?g \<degree> \<sigma> ?x" by (simp add: unifies_def s\<^sub>2_def t\<^sub>2_def g_def)
  obtain w where w: "\<beta>\<eta>cl (\<sigma> ?x) w" "normal w"
    using nf_typed[OF typed_onD[OF sd(2) rangeI[of code "AVar X"]]] by blast
  have "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> ?x" by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]])
  also note eq
  also have "dB.Var ?g \<degree> \<sigma> ?x \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var ?g \<degree> w" by (rule equiv_AppR[OF \<beta>\<eta>cl_into_equiv[OF w(1)]])
  finally have "\<beta>\<eta>cl w (dB.Var ?g \<degree> w)" by (rule equiv_\<beta>\<eta>cl_normal[OF _ normal_Var_App[OF w(2)]])
  then have "w = dB.Var ?g \<degree> w" using w(2) by (cases rule: converse_rtranclpE) auto
  then have "size w = size (dB.Var ?g \<degree> w)" by (rule arg_cong)
  then show False by simp
qed

theorem example_Unif: "\<exists>u. unify alg s\<^sub>2 t\<^sub>2 env0 = Some (Err (Unif u))"
  using ex\<^sub>2.decides(2)[OF patterns\<^sub>2 env_ppat_env0] not_unifiable\<^sub>2 by blast

subsection \<open>Giving up: \<open>?F a =?= b\<close>\<close>

definition a :: pterm where "a = Const STR ''a'' \<iota>"
definition b :: pterm where "b = Const STR ''b'' \<iota>"

definition s\<^sub>3 :: pterm where "s\<^sub>3 = Var F (\<iota> \<rightarrow>\<^sub>T \<iota>) $ a"
definition t\<^sub>3 :: pterm where "t\<^sub>3 = b"

interpretation ex\<^sub>3: unif_problem ar V env0 s\<^sub>3 t\<^sub>3 \<iota>
proof
  show "env_inv ar V env0" by (rule env_inv_env0)
  show "wf_term ar 0 s\<^sub>3" "wf_term ar 0 t\<^sub>3"
    by (simp_all add: wf_term_def s\<^sub>3_def t\<^sub>3_def a_def b_def ar_def)
  show "has_type V [] s\<^sub>3 \<iota>" "has_type V [] t\<^sub>3 \<iota>"
    by (auto simp: s\<^sub>3_def t\<^sub>3_def a_def b_def V_def intro!: has_type.intros)
  show "below (maxidx env0) s\<^sub>3" "below (maxidx env0) t\<^sub>3"
    by (simp_all add: below_def s\<^sub>3_def t\<^sub>3_def a_def b_def F_def env0_def)
qed

text \<open>\<^const>\<open>unify\<close> gives up because the argument \<open>a\<close> of \<open>?F\<close> is not a bound variable.\<close>

theorem example_Pattern: "unify alg s\<^sub>3 t\<^sub>3 env0 = Some (Err Pattern)"
  unfolding unify_def s\<^sub>3_def t\<^sub>3_def a_def b_def env0_def
  by (subst unif.simps) (simp add: head_norm.simps[of _ "_ $ _"] head_norm.simps[of _ "pterm.Var _ _"]
    head_norm.simps[of _ "Const _ _"] lookup_def ints_of'_def unified_def bindM_def return_def
    raise_def strip_comb_def)

text \<open>
  This is consistent with @{thm [source] ex\<^sub>3.Pattern_not_pattern}: \<open>s\<^sub>3\<close> is not a pattern. Yet the
  problem is unifiable, by \<open>?F := \<lambda>x. b\<close>: giving up is not failure.
\<close>

lemma not_pattern\<^sub>3: "\<not> ppat s\<^sub>3"
  using ex\<^sub>3.Pattern_not_pattern[OF example_Pattern] env_ppat_env0 by (simp add: t\<^sub>3_def b_def is_rigid_def
    ppat_rigid[of "Const STR ''b'' \<iota>" "[]", simplified])

definition \<sigma>\<^sub>1 :: "nat \<Rightarrow> dB" where "\<sigma>\<^sub>1 = dB.Var(code (AVar F) := dB.Abs (tr b))"

lemma unifiable\<^sub>3: "ex\<^sub>3.unifiable"
proof (intro exI conjI)
  show "solution V (tau V) \<sigma>\<^sub>1 env0"
    unfolding solution_def
  proof (intro conjI)
    show "closed_on UNIV \<sigma>\<^sub>1" by (simp add: closed_on_def \<sigma>\<^sub>1_def b_def)
    show "typed_on (range code) (tau V) (tau V) \<sigma>\<^sub>1"
      by (auto simp: typed_on_def \<sigma>\<^sub>1_def b_def V_def)
    show "rigid_subst \<sigma>\<^sub>1" by (auto simp: rigid_subst_def rigid_code_def \<sigma>\<^sub>1_def)
    show "sat \<sigma>\<^sub>1 env0" by (simp add: sat_def env0_def)
  qed
  have "dB.Abs (tr b) \<degree> tr a \<rightarrow>\<^sub>\<beta> tr b" using beta.beta[of "tr b" "tr a"] by (simp add: a_def b_def)
  then have "mk_subst \<sigma>\<^sub>1 (tr s\<^sub>3) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst \<sigma>\<^sub>1 (tr t\<^sub>3)"
    by (auto simp: s\<^sub>3_def t\<^sub>3_def a_def b_def \<sigma>\<^sub>1_def)
  then show "unifies \<sigma>\<^sub>1 (tr s\<^sub>3) (tr t\<^sub>3)" by (simp add: unifies_def beta_into_equiv)
qed

end
