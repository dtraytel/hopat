section \<open>Problems with Type Variables: the Polymorphic Semantics\<close>

theory Poly_Semantics
  imports Poly_Typing
begin

text \<open>
  The results so far describe the solutions of a problem with type variables through its ground
  instances: a pair of a ground solution \<open>\<rho>\<close> of the type environment and a substitution \<open>\<sigma>\<close> for
  the ground instance. The \<^emph>\<open>polymorphic semantics\<close> works with the problem itself: a closed
  substitution \<open>\<sigma>\<close> that satisfies the environment and \<^emph>\<open>respects\<close> its type environment \<open>\<theta>\<close>
  (\<open>tresp\<close>): it identifies the codes of constants (and free variables) whose types are equal in
  all solutions of \<open>\<theta>\<close>. A ground instance for \<open>\<rho>\<close> corresponds to the substitution \<open>\<sigma> \<circ> cren \<rho>\<close>,
  where \<open>cren\<close> renames the codes of constants and free variables by instantiating their types.

  Equivalence in all ground instances implies equivalence in the polymorphic semantics
  (\<open>penv_equiv_gsol\<close>): a faithful ground instance identifies only types that are
  equal modulo \<open>\<theta>\<close>, so every substitution that respects \<open>\<theta>\<close> factors through it.
\<close>

subsection \<open>Type instances\<close>

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

text \<open>The translation depends only on the codes of the atoms of a term:\<close>

lemma mk_subst_tr_agree:
  assumes "\<And>a T. T \<in> tys t \<Longrightarrow>
      \<sigma>1 (code (AConst a T)) = \<sigma>2 (code (AConst a T)) \<and> \<sigma>1 (code (AFree a T)) = \<sigma>2 (code (AFree a T))"
    "\<And>x. \<sigma>1 (code (AVar x)) = \<sigma>2 (code (AVar x))"
  shows "mk_subst \<sigma>1 (tr t) = mk_subst \<sigma>2 (tr t)"
  using assms(1) by (induction t) (auto simp: assms(2))


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


subsection \<open>From ground instances to the polymorphic semantics\<close>

context wf_algebra
begin

text \<open>
  Terms that are equivalent in all ground instances of an environment are equivalent in the
  polymorphic semantics: a substitution \<open>\<sigma>\<close> that respects the type environment is \<open>\<sigma>' \<circ> cren \<rho>\<close>
  on the atoms of the terms and of the environment, for a faithful ground solution \<open>\<rho>\<close>.
\<close>

lemma penv_equiv_gsol:
  assumes inv: "tinv ar n (tyenv env) A" and srt: "tsorted alg (tyenv env)"
    and tc: "\<forall>T\<in>tys s \<union> tys t \<union> etys env. tcons (tyenv env) T"
    and gr: "\<And>\<rho>. gsol alg ar (tyenv env) \<rho> \<Longrightarrow> instE \<rho> env \<Turnstile> inst \<rho> s \<approx> inst \<rho> t"
  shows "env \<Turnstile>\<^sub>p s \<approx> t"
proof (rule penv_equivI)
  fix \<sigma> assume ps: "psat \<sigma> env"
  let ?\<theta> = "tyenv env" and ?Ts = "tys s \<union> tys t \<union> etys env"
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF inv] tinv_tcons_env[OF inv] by simp_all
  have fin: "finite ?Ts" using finite_etys by simp
  define Z where "Z = (\<Union>T\<in>?Ts. tvars (tnorm ?\<theta> T))"
  define N where "N = (\<Union>T\<in>?Ts. tfnames (tnorm ?\<theta> T))"
  have "finite Z" "finite N" using fin by (simp_all add: Z_def N_def)
  then obtain \<rho> where g: "gsol alg ar ?\<theta> \<rho>"
    and inj: "\<And>T U. tcons ?\<theta> T \<Longrightarrow> tcons ?\<theta> U \<Longrightarrow> tvars (tnorm ?\<theta> T) \<union> tvars (tnorm ?\<theta> U) \<subseteq> Z \<Longrightarrow>
      tfnames (tnorm ?\<theta> T) \<union> tfnames (tnorm ?\<theta> U) \<subseteq> N \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U \<Longrightarrow>
      tnorm ?\<theta> T = tnorm ?\<theta> U"
    using faithful_exists[OF inv srt] by metis
  define pick where "pick T' = (SOME T. T \<in> ?Ts \<and> tsubst \<rho> T = T')" for T'
  define \<sigma>' where "\<sigma>' n = (case atom_of n of
      AConst a T' \<Rightarrow> if \<exists>T\<in>?Ts. tsubst \<rho> T = T' then \<sigma> (code (AConst a (pick T'))) else \<sigma> n
    | AFree a T' \<Rightarrow> if \<exists>T\<in>?Ts. tsubst \<rho> T = T' then \<sigma> (code (AFree a (pick T'))) else \<sigma> n
    | AVar x \<Rightarrow> \<sigma> n)" for n
  have eqT: "tsubst \<rho>' (pick (tsubst \<rho> T)) = tsubst \<rho>' T" if T: "T \<in> ?Ts" and sl: "tsol ?\<theta> \<rho>'" for T \<rho>'
  proof -
    have p: "pick (tsubst \<rho> T) \<in> ?Ts \<and> tsubst \<rho> (pick (tsubst \<rho> T)) = tsubst \<rho> T"
      unfolding pick_def by (rule someI[of _ T]) (use T in simp)
    have "tnorm ?\<theta> (pick (tsubst \<rho> T)) = tnorm ?\<theta> T"
      by (rule inj) (use p T tc in \<open>auto simp: Z_def N_def\<close>)
    then show ?thesis using tsubst_tnorm[OF ac sl] p T tc by metis
  qed
  have agr: "(\<sigma>' \<circ> cren \<rho>) (code (AConst a T)) = \<sigma> (code (AConst a T)) \<and>
      (\<sigma>' \<circ> cren \<rho>) (code (AFree a T)) = \<sigma> (code (AFree a T))" if "T \<in> ?Ts" for a T
    using trespD[OF psatD(2)[OF ps] eqT[OF that]] that by (auto simp: \<sigma>'_def)
  have agv: "(\<sigma>' \<circ> cren \<rho>) (code (AVar x)) = \<sigma> (code (AVar x))" for x by (simp add: \<sigma>'_def)
  have ms: "mk_subst (\<sigma>' \<circ> cren \<rho>) (tr u) = mk_subst \<sigma> (tr u)" if "tys u \<subseteq> ?Ts" for u
    by (rule mk_subst_tr_agree) (use agr agv that in auto)
  have cl: "closed_on UNIV \<sigma>'"
    using closed_onD[OF psatD(1)[OF ps]] by (auto simp: closed_on_def \<sigma>'_def split: atom.splits)
  have "sat (\<sigma>' \<circ> cren \<rho>) env"
    using psatD(3)[OF ps] ms etysI unfolding sat_def by (metis agv insert_subset le_supI2)
  then have "sat \<sigma>' (instE \<rho> env)" by (simp add: sat_instE)
  from env_equivD[OF gr[OF g] cl this]
  have "mk_subst \<sigma>' (tr (inst \<rho> s)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (inst \<rho> t))" .
  moreover have "tys s \<subseteq> ?Ts" "tys t \<subseteq> ?Ts" by auto
  ultimately show "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)" using ms by (simp add: mk_subst_inst)
qed

text \<open>Hence the environments that pattern unification returns are sound in the polymorphic semantics:\<close>

lemma postok_penv_equiv:
  assumes "postok alg ar A bs s t env env'" "\<forall>T\<in>tys s \<union> tys t. tyw ar (tyenv env) A T"
  shows "pextends env' env" "env' \<Turnstile>\<^sub>p s \<approx> t"
proof -
  note p = assms(1)[unfolded postok_def]
  show "pextends env' env" using p by (simp add: pextends_def)
  have ac: "tacyc (tyenv env')" using tinv_tacyc p by blast
  have "\<forall>T\<in>tys s \<union> tys t \<union> etys env'. tcons (tyenv env') T"
    using assms(2) p tyw_textends[OF ac] tyw_tcons by blast
  with p show "env' \<Turnstile>\<^sub>p s \<approx> t" by (intro penv_equiv_gsol) blast+
qed

end

end
