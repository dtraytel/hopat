section \<open>Problems with Type Variables: Semantics\<close>

theory Unify_Poly_Semantics
  imports Unify_Pull "Pure_Pattern_Correctness.Poly_Semantics"
begin

context csig
begin

text \<open>
  With type variables, the type environment \<open>\<theta>\<close> of an environment constrains the types. A
  solution of a problem is a pair \<open>(\<rho>, \<sigma>)\<close>: a type instantiation \<open>\<rho>\<close> that solves \<open>\<theta>\<close>
  (\<^const>\<open>tsol\<close>), and a closed substitution \<open>\<sigma>\<close> that satisfies the type instance of the
  environment (\<^const>\<open>instE\<close>) and solves the type instances of the pairs.

  For a fixed \<open>\<rho>\<close>, the semantics of a type instance is the semantics of the problem itself
  for the substitution \<open>\<sigma> \<circ> cren \<rho>\<close>. The soundness proofs therefore work with the polymorphic
  semantics of \<^theory>\<open>Pure_Pattern_Correctness.Poly_Semantics\<close> (\<^const>\<open>psat\<close>), for substitutions
  that respect the type environment.
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

lemma dsolved_instd: "dsolved \<sigma> (instd \<rho> dp) \<longleftrightarrow> dsolved (\<sigma> \<circ> cren \<rho>) dp"
  by (cases dp) (simp add: dsolved_def inst_rlist_abs[symmetric] mk_subst_inst)

lemma penv_equiv_rlist_abs: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p rlist_abs rb s \<approx> rlist_abs rb t"
  by (auto simp: penv_equiv_def tr_rlist_abs mk_subst_Abs_m intro: equiv_Abs_m)

end

end
