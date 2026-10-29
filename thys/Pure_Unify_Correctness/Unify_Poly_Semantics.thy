section \<open>Problems with Type Variables: Semantics\<close>

theory Unify_Poly_Semantics
  imports Unify_Pull "Pure_Pattern_Correctness.Poly_Inst"
begin

text \<open>
  With type variables, the type environment \<open>\<theta>\<close> of an environment constrains the types. A
  solution of a problem is a pair \<open>(\<rho>, \<sigma>)\<close>: a type instantiation \<open>\<rho>\<close> that solves \<open>\<theta>\<close>
  (\<^const>\<open>tsol\<close>), and a closed substitution \<open>\<sigma>\<close> that satisfies the type instance of the
  environment (\<^const>\<open>instE\<close>) and solves the type instances of the pairs.

  For a fixed \<open>\<rho>\<close>, the semantics of a type instance is the semantics of the problem itself
  for the substitution \<open>\<sigma> \<circ> cren \<rho>\<close>, where \<open>cren\<close> renames the codes of constants and free
  variables by instantiating their types. Such substitutions \<^emph>\<open>respect\<close> \<open>\<theta>\<close> (\<open>tresp\<close>): they identify the
  codes of constants (and free variables) whose types are equal in all solutions of \<open>\<theta>\<close>. The
  soundness proofs therefore work with the semantics of \<^theory>\<open>Pure_Unify_Correctness.Unify_Match\<close>,
  for substitutions that respect the type environment.
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

text \<open>Renaming the codes of constants and free variables:\<close>

fun inst_atom :: "tinst \<Rightarrow> atom \<Rightarrow> atom" where
  "inst_atom \<rho> (AConst a T) = AConst a (tsubst \<rho> T)"
| "inst_atom \<rho> (AFree a T) = AFree a (tsubst \<rho> T)"
| "inst_atom \<rho> (AVar x) = AVar x"

definition cren :: "tinst \<Rightarrow> nat \<Rightarrow> nat" where
  "cren \<rho> n = code (inst_atom \<rho> (atom_of n))"

lemma cren_code[simp]: "cren \<rho> (code a) = code (inst_atom \<rho> a)"
  by (simp add: cren_def)

lemma mk_subst_inst: "mk_subst \<sigma> (tr (inst \<rho> t)) = mk_subst (\<sigma> \<circ> cren \<rho>) (tr t)"
  by (induction t) simp_all

lemma closed_on_cren: "closed_on UNIV \<sigma> \<Longrightarrow> closed_on UNIV (\<sigma> \<circ> cren \<rho>)"
  by (simp add: closed_on_def)

lemma sat_instE: "sat \<sigma> (instE \<rho> env) \<longleftrightarrow> sat (\<sigma> \<circ> cren \<rho>) env"
proof -
  have "\<sigma> (code (AVar x)) = (\<sigma> \<circ> cren \<rho>) (code (AVar x))" for x by simp
  then show ?thesis unfolding sat_def by (fastforce simp: mk_subst_inst)
qed

lemma dsolved_instd: "dsolved \<sigma> (instd \<rho> dp) \<longleftrightarrow> dsolved (\<sigma> \<circ> cren \<rho>) dp"
  by (cases dp) (simp add: dsolved_def inst_rlist_abs[symmetric] mk_subst_inst)


subsection \<open>Substitutions that respect a type environment\<close>

definition tresp :: "tyenv \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "tresp \<theta> \<sigma> \<longleftrightarrow> (\<forall>a T U. (\<forall>\<rho>. tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<longrightarrow>
     \<sigma> (code (AConst a T)) = \<sigma> (code (AConst a U)) \<and> \<sigma> (code (AFree a T)) = \<sigma> (code (AFree a U)))"

lemma trespD:
  "tresp \<theta> \<sigma> \<Longrightarrow> (\<And>\<rho>. tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<Longrightarrow>
    \<sigma> (code (AConst a T)) = \<sigma> (code (AConst a U)) \<and> \<sigma> (code (AFree a T)) = \<sigma> (code (AFree a U))"
  unfolding tresp_def by blast

lemma tresp_textends: "tresp \<theta>' \<sigma> \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> tresp \<theta> \<sigma>"
  unfolding tresp_def by (blast intro: tsol_textends)

lemma tsol_TVar: "vt_is_empty \<theta> \<Longrightarrow> tsol \<theta> TVar"
  by (simp add: tsol_def vt_is_empty_lookup)

lemma tsubst_TVar: "tsubst TVar T = T"
  by (induction T) (simp_all add: map_idI)

lemma tresp_empty: "vt_is_empty \<theta> \<Longrightarrow> tresp \<theta> \<sigma>"
  unfolding tresp_def using tsol_TVar[of \<theta>] by (metis tsubst_TVar)

lemma tresp_cren: "tsol \<theta> \<rho> \<Longrightarrow> tresp \<theta> (\<sigma> \<circ> cren \<rho>)"
  by (simp add: tresp_def)


subsection \<open>Solutions\<close>

definition psat :: "(nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> bool" where
  "psat \<sigma> env \<longleftrightarrow> closed_on UNIV \<sigma> \<and> tresp (tyenv env) \<sigma> \<and> sat \<sigma> env"

lemma psatD:
  assumes "psat \<sigma> env"
  shows "closed_on UNIV \<sigma>" "tresp (tyenv env) \<sigma>" "sat \<sigma> env"
  using assms by (simp_all add: psat_def)

lemma psat_instE: "tsol (tyenv env) \<rho> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> (instE \<rho> env) \<Longrightarrow>
    psat (\<sigma> \<circ> cren \<rho>) env"
  by (simp add: psat_def closed_on_cren tresp_cren sat_instE)

text \<open>Extensions of environments also extend the type environment.\<close>

definition pextends :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "pextends env' env \<longleftrightarrow> extends env' env \<and> textends (tyenv env) (tyenv env')"

lemma pextends_refl[simp]: "pextends env env"
  by (simp add: pextends_def)

lemma pextends_trans: "pextends env3 env2 \<Longrightarrow> pextends env2 env1 \<Longrightarrow> pextends env3 env1"
  by (auto simp: pextends_def intro: extends_trans textends_trans)

lemma pextendsD: "pextends env' env \<Longrightarrow> extends env' env" "pextends env' env \<Longrightarrow> textends (tyenv env) (tyenv env')"
  by (simp_all add: pextends_def)

lemma psat_pextends: "psat \<sigma> env' \<Longrightarrow> pextends env' env \<Longrightarrow> psat \<sigma> env"
  by (auto simp: psat_def pextends_def intro: tresp_textends sat_extends)

text \<open>Equivalence of terms in the solutions of an environment:\<close>

definition penv_equiv :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" (\<open>_ \<Turnstile>\<^sub>p _ \<approx> _\<close> [50, 50, 50] 50) where
  "env \<Turnstile>\<^sub>p s \<approx> t \<longleftrightarrow> (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow> mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t))"

lemma penv_equivI:
  "(\<And>\<sigma>. psat \<sigma> env \<Longrightarrow> mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)) \<Longrightarrow> env \<Turnstile>\<^sub>p s \<approx> t"
  by (simp add: penv_equiv_def)

lemma penv_equivD: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> psat \<sigma> env \<Longrightarrow> mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
  by (simp add: penv_equiv_def)

lemma env_equiv_penv: "env \<Turnstile> s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p s \<approx> t"
  by (auto simp: penv_equiv_def psat_def intro: env_equivD)

lemma penv_equiv_refl[simp]: "env \<Turnstile>\<^sub>p t \<approx> t"
  by (simp add: penv_equiv_def)

lemma penv_equiv_sym: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p t \<approx> s"
  by (auto simp: penv_equiv_def intro: equiv_sym)

lemma penv_equiv_trans: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p t \<approx> u \<Longrightarrow> env \<Turnstile>\<^sub>p s \<approx> u"
  unfolding penv_equiv_def by (blast intro: equiv_trans)

lemma penv_equiv_pextends: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> pextends env' env \<Longrightarrow> env' \<Turnstile>\<^sub>p s \<approx> t"
  by (auto simp: penv_equiv_def intro: psat_pextends)

lemma penv_equiv_rlist_abs: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p rlist_abs rb s \<approx> rlist_abs rb t"
  by (auto simp: penv_equiv_def tr_rlist_abs mk_subst_Abs_m intro: equiv_Abs_m)

end
