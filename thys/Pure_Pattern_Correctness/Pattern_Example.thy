section \<open>Example\<close>

theory Pattern_Example
  imports Pattern_Correctness
begin

text \<open>
  We instantiate the locale \<^locale>\<open>unif_problem\<close> with the problem \<open>\<lambda>x. ?F x =?= \<lambda>x. f x x\<close>
  in the empty environment, where \<open>f :: i \<Rightarrow> i \<Rightarrow> i\<close> is a constant and \<open>?F :: i \<Rightarrow> i\<close> a
  schematic variable. The problem is a pattern problem and has the unifier
  \<open>?F := \<lambda>x. f x x\<close>, so by the results of theory \<^theory>\<open>Pure_Pattern_Correctness.Pattern_Correctness\<close>,
  \<^const>\<open>unify\<close> returns a most general unifier.
\<close>

abbreviation \<iota> :: ptyp where "\<iota> \<equiv> Type STR ''i'' []"

definition f :: pterm where "f = Const STR ''f'' (\<iota> \<rightarrow>\<^sub>T \<iota> \<rightarrow>\<^sub>T \<iota>)"
definition F :: indexname where "F = (STR ''F'', 0)"

definition s :: pterm where "s = Abs STR ''x'' \<iota> (Var F (\<iota> \<rightarrow>\<^sub>T \<iota>) $ Bound 0)"
definition t :: pterm where "t = Abs STR ''x'' \<iota> (f $ Bound 0 $ Bound 0)"

definition env0 :: env where "env0 = Envir 0 vt_empty vt_empty"

text \<open>All type constructors other than \<open>fun\<close> are nullary, and every schematic variable has type \<open>i \<Rightarrow> i\<close>.\<close>

definition ar :: "name \<Rightarrow> nat" where "ar = (\<lambda>_. 0)"
definition V :: "indexname \<Rightarrow> ptyp" where "V = (\<lambda>_. \<iota> \<rightarrow>\<^sub>T \<iota>)"

lemma vt_is_empty_vt_empty: "vt_is_empty vt_empty"
  by transfer simp

interpretation ex: unif_problem ar V env0 s t "\<iota> \<rightarrow>\<^sub>T \<iota>"
proof
  show "env_inv ar V env0"
    by (auto simp: env_inv_def acyc_def dep_def lk_def wf_env_def env_typed_def fresh_env_def env0_def
      vt_is_empty_vt_empty acyclic_def)
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
  show "env_ppat env0" by (simp add: env_ppat_def env0_def)
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

theorem example:
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

end
