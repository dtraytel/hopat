section \<open>Problems with Type Variables: Semantics\<close>

theory Unify_Poly_Semantics
  imports Unify_Pull "Pure_Pattern_Correctness.Poly_Inst"
begin

text \<open>
  With type variables, the type environment \<open>\<theta>\<close> of an environment constrains the types. A
  solution of a problem is a pair \<open>(\<rho>, \<sigma>)\<close>: a type instantiation \<open>\<rho>\<close> that solves \<open>\<theta>\<close>
  (\<^const>\<open>tsol\<close>), and a closed substitution \<open>\<sigma>\<close> that satisfies the type instance of the
  environment (\<^const>\<open>instE\<close>) and solves the type instances of the pairs. Soundness holds for all
  such instantiations, ground and well-sorted or not.
\<close>

subsection \<open>Type instances\<close>

definition instd :: "tinst \<Rightarrow> dpair \<Rightarrow> dpair" where
  "instd \<rho> dp = (case dp of (rb, t, u) \<Rightarrow> (instb \<rho> rb, inst \<rho> t, inst \<rho> u))"

lemma instd_simp[simp]: "instd \<rho> (rb, t, u) = (instb \<rho> rb, inst \<rho> t, inst \<rho> u)"
  by (simp add: instd_def)

lemma inst_rlist_abs: "inst \<rho> (rlist_abs rb t) = rlist_abs (instb \<rho> rb) (inst \<rho> t)"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma inst_combound: "inst \<rho> (combound t n k) = combound (inst \<rho> t) n k"
  by (induction t n k rule: combound.induct) simp_all

lemma inst_incr_boundvars: "inst \<rho> (incr_boundvars n t) = incr_boundvars n (inst \<rho> t)"
  by (simp add: incr_boundvars_def inst_incr_bv)

lemma head_of_inst: "head_of (inst \<rho> t) = inst \<rho> (head_of t)"
  by (induction t rule: head_of.induct) simp_all

lemma tr_inst_Abs_m: "tr (inst \<rho> (rlist_abs rb t)) = Abs_m (length rb) (tr (inst \<rho> t))"
  by (simp add: inst_rlist_abs tr_rlist_abs)


subsection \<open>Solutions\<close>

definition psol :: "tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> bool" where
  "psol \<rho> \<sigma> env \<longleftrightarrow> tsol (tyenv env) \<rho> \<and> closed_on UNIV \<sigma> \<and> sat \<sigma> (instE \<rho> env)"

lemma psolD:
  assumes "psol \<rho> \<sigma> env"
  shows "tsol (tyenv env) \<rho>" "closed_on UNIV \<sigma>" "sat \<sigma> (instE \<rho> env)"
  using assms by (simp_all add: psol_def)

text \<open>Extensions of environments also extend the type environment.\<close>

definition pextends :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "pextends env' env \<longleftrightarrow> extends env' env \<and> textends (tyenv env) (tyenv env')"

lemma pextends_refl[simp]: "pextends env env"
  by (simp add: pextends_def)

lemma pextends_trans: "pextends env3 env2 \<Longrightarrow> pextends env2 env1 \<Longrightarrow> pextends env3 env1"
  by (auto simp: pextends_def extends_def intro: textends_trans)

lemma extends_instE: "extends env' env \<Longrightarrow> extends (instE \<rho> env') (instE \<rho> env)"
  by (auto simp: extends_def)

lemma psol_pextends: "psol \<rho> \<sigma> env' \<Longrightarrow> pextends env' env \<Longrightarrow> psol \<rho> \<sigma> env"
  by (auto simp: psol_def pextends_def intro: tsol_textends sat_extends extends_instE)

text \<open>Equivalence of terms in all solutions of an environment:\<close>

definition penv_equiv :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" (\<open>_ \<Turnstile>\<^sub>p _ \<approx> _\<close> [50, 50, 50] 50) where
  "env \<Turnstile>\<^sub>p s \<approx> t \<longleftrightarrow>
    (\<forall>\<rho> \<sigma>. psol \<rho> \<sigma> env \<longrightarrow> mk_subst \<sigma> (tr (inst \<rho> s)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> t)))"

lemma penv_equivI:
  "(\<And>\<rho> \<sigma>. psol \<rho> \<sigma> env \<Longrightarrow> mk_subst \<sigma> (tr (inst \<rho> s)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> t))) \<Longrightarrow>
    env \<Turnstile>\<^sub>p s \<approx> t"
  by (simp add: penv_equiv_def)

lemma penv_equivD:
  "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> psol \<rho> \<sigma> env \<Longrightarrow> mk_subst \<sigma> (tr (inst \<rho> s)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> t))"
  by (simp add: penv_equiv_def)

lemma penv_equiv_refl[simp]: "env \<Turnstile>\<^sub>p t \<approx> t"
  by (simp add: penv_equiv_def)

lemma penv_equiv_sym: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p t \<approx> s"
  by (auto simp: penv_equiv_def intro: equiv_sym)

lemma penv_equiv_trans: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p t \<approx> u \<Longrightarrow> env \<Turnstile>\<^sub>p s \<approx> u"
  unfolding penv_equiv_def by (blast intro: equiv_trans)

lemma penv_equiv_pextends: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> pextends env' env \<Longrightarrow> env' \<Turnstile>\<^sub>p s \<approx> t"
  by (auto simp: penv_equiv_def intro: psol_pextends)

text \<open>Equivalence in the type instances, as an equivalence of the monomorphic semantics:\<close>

lemma penv_equiv_env_equiv:
  "(\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> instE \<rho> env \<Turnstile> inst \<rho> s \<approx> inst \<rho> t) \<Longrightarrow> env \<Turnstile>\<^sub>p s \<approx> t"
  by (auto simp: penv_equiv_def psol_def env_equiv_def)

end
