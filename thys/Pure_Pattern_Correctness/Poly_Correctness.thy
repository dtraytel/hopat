section \<open>Correctness of Polymorphic Pattern Unification\<close>

theory Poly_Correctness
  imports Poly_Unif_Term
begin

text \<open>
  The main results about \<^const>\<open>unify\<close> on problems with schematic type variables (with sorts),
  collected in one place. A polymorphic problem \<open>s =?= t\<close> relative to an environment \<open>env\<close> with
  type environment \<open>\<theta> = tyenv env\<close> stands for the family of its ground instances: for each
  well-sorted ground solution \<open>\<rho>\<close> of \<open>\<theta>\<close> (\<^const>\<open>gsol\<close>), the monomorphic problem
  \<open>inst \<rho> s =?= inst \<rho> t\<close> relative to \<open>instE \<rho> env\<close>. The problem is well-formed if
  \<^item> \<open>\<theta>\<close> satisfies the type invariant \<^const>\<open>tinv\<close> and its bindings respect sorts (\<^const>\<open>tsorted\<close>),
    where the finite set \<open>A\<close> contains the type variables of the problem;
  \<^item> the types of the problem are well-formed and depend only on type variables in \<open>A\<close>
    (\<^const>\<open>tyw\<close>, see \<open>tyw_tvars\<close> below);
  \<^item> the variables of \<open>s\<close>, \<open>t\<close> and \<open>env\<close> are not newer than \<open>maxidx env\<close>, and the bindings of
    \<open>env\<close> are acyclic (\<^const>\<open>nacyc\<close>);
  \<^item> all ground instances are well-formed and well-typed (\<^const>\<open>inst_ok\<close>, see
    \<open>inst_ok_typed\<close> below for a sufficient condition).
  Then \<^const>\<open>unify\<close> terminates, and its results are correct for all ground instances at once:
  a returned environment is a most general unifier of all ground instances, failure with
  \<open>Unif\<close> means that no ground instance is unifiable, and \<open>Pattern\<close> is raised only on
  non-patterns.
\<close>


subsection \<open>Sufficient conditions\<close>

text \<open>Types depending only on type variables in \<open>A\<close>:\<close>

lemma tyw_tvars:
  assumes "tvars T \<subseteq> A" "wft ar T"
  shows "tyw ar \<theta> A T"
proof -
  have "uvars \<theta> T \<subseteq> uvarsA \<theta> A"
  proof
    fix u assume "u \<in> uvars \<theta> T"
    then obtain w S where "(w, S) \<in> tvars T" "u \<in> uvars \<theta> (TVar w S)"
      by (subst (asm) uvars_def, subst (asm) tnorm_tsubst) (force simp: uvars_def tvars_tsubst)
    with assms(1) show "u \<in> uvarsA \<theta> A" by (auto simp: uvarsA_def)
  qed
  with assms show ?thesis by (auto simp: tyw_def)
qed

text \<open>Ground instances of terms whose types are well-formed, and of polymorphically typed problems:\<close>

definition pwf_term :: "(name \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pterm \<Rightarrow> bool" where
  "pwf_term ar n t \<longleftrightarrow> proper t \<and> (\<forall>T\<in>tys t. wft ar T) \<and> no_loose_bound (tr t) n"

lemma typs_ok_inst: "\<forall>T\<in>tys t. wft ar T \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> typs_ok ar (inst \<rho> t)"
  by (induction t) (auto intro: ground_tsubst)

lemma wf_term_inst: "pwf_term ar n t \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> wf_term ar n (inst \<rho> t)"
  by (simp add: pwf_term_def wf_term_def typs_ok_inst)

lemma has_type_inst:
  "has_type W Ts t T \<Longrightarrow> has_type (\<lambda>x. tsubst \<rho> (W x)) (map (tsubst \<rho>) Ts) (inst \<rho> t) (tsubst \<rho> T)"
  by (induction rule: has_type.induct) (auto intro: has_type.intros)

lemma inst_ok_typed:
  assumes s: "pwf_term ar 0 s" "has_type W [] s T" and t: "pwf_term ar 0 t" "has_type W [] t T"
    and env: "\<And>x U u. vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> pwf_term ar 0 u \<and> wft ar U"
      "env_typed W env" "fresh_env env"
    and g: "\<forall>v S. ground ar (\<rho> v S)"
  shows "inst_ok ar (\<lambda>x. tsubst \<rho> (W x)) \<rho> [] s t env"
proof -
  let ?W = "\<lambda>x. tsubst \<rho> (W x)"
  have wfb: "proper u \<and> typs_ok ar u \<and> ground ar U \<and> no_loose_bound (tr u) 0"
    if "vt_lookup (tenv (instE \<rho> env)) x = Some (U, u)" for x U u
  proof -
    from that obtain U0 u0 where b: "vt_lookup (tenv env) x = Some (U0, u0)" and U: "U = tsubst \<rho> U0"
      and u: "u = inst \<rho> u0" by auto
    from env(1)[OF b] have "wf_term ar 0 u" "ground ar U"
      using wf_term_inst[OF _ g] ground_tsubst[OF _ g] by (auto simp: U u)
    then show ?thesis by (simp add: wf_term_def)
  qed
  have "wf_env ar (instE \<rho> env)" unfolding wf_env_def using wfb by auto
  moreover have "env_typed ?W (instE \<rho> env)"
    unfolding env_typed_def
  proof (intro allI impI)
    fix x U u assume "vt_lookup (tenv (instE \<rho> env)) x = Some (U, u)"
    then obtain U0 u0 where b: "vt_lookup (tenv env) x = Some (U0, u0)" and U: "U = tsubst \<rho> U0"
      and u: "u = inst \<rho> u0" by auto
    from env_typedD[OF env(2) b] have "W x = U0" "has_type W [] u0 U0" by simp_all
    then show "?W x = U \<and> has_type ?W [] u U" using has_type_inst[of W "[]" u0 U0 \<rho>] by (simp add: U u)
  qed
  moreover have "fresh_env (instE \<rho> env)"
    using env(3) unfolding fresh_env_def by auto
  moreover have "has_type ?W [] (inst \<rho> s) (tsubst \<rho> T)" "has_type ?W [] (inst \<rho> t) (tsubst \<rho> T)"
    using has_type_inst[OF s(2), of \<rho>] has_type_inst[OF t(2), of \<rho>] by simp_all
  ultimately show ?thesis
    using wf_term_inst[OF s(1) g] wf_term_inst[OF t(1) g] by (auto simp: inst_ok_def binders_ok_def)
qed


subsection \<open>Well-formed polymorphic problems\<close>

locale poly_problem = wf_algebra alg ar for alg :: algebra and ar :: "name \<Rightarrow> nat" +
  fixes A :: "(indexname \<times> psort) set" and env :: env and s t :: pterm
  assumes finite_A: "finite A"
    and tinv: "tinv ar (maxidx env) (tyenv env) A" and tsorted: "tsorted alg (tyenv env)"
    and tyw: "\<forall>T\<in>tys s \<union> tys t \<union> etys env. tyw ar (tyenv env) A T"
    and below_s: "below (maxidx env) s" and below_t: "below (maxidx env) t"
    and acyclic: "nacyc env"
    and instances: "\<And>\<rho>. gsol alg ar (tyenv env) \<rho> \<Longrightarrow> \<exists>W. inst_ok ar W \<rho> [] s t env"
begin

lemma pre: "pre alg ar A [] s t env"
  using tinv tsorted tyw below_s below_t instances by (simp add: pre_def)

text \<open>
  Some ground instance has a unifier: a solution of the instance of the environment (for a typing
  \<open>W\<close> of the instance) that unifies the instances of \<open>s\<close> and \<open>t\<close>.
\<close>

abbreviation unifiable :: bool where
  "unifiable \<equiv> \<exists>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<and> inst_ok ar W \<rho> [] s t env \<and>
    solution W \<tau>' \<sigma> (instE \<rho> env) \<and> unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"

lemma post: "unify alg s t env = Some r \<Longrightarrow> post_all alg ar A [] s t env r"
  unfolding unify_def by (rule unif_post[OF _ refl pre])

lemma tres: "unify alg s t env = Some r \<Longrightarrow> tres A env r"
  using unif_terminates[OF finite_A pre acyclic] by (auto simp: unify_def)


subsection \<open>Termination\<close>

text \<open>\<^const>\<open>unify\<close> terminates; it returns an environment, fails, or gives up.\<close>

theorem terminates: "\<exists>r. unify alg s t env = Some r"
  using unif_terminates[OF finite_A pre acyclic] unfolding unify_def by blast

theorem result:
  assumes "unify alg s t env = Some r"
  shows "(\<exists>env'. r = Ok env') \<or> (\<exists>u. r = Err (Unif u)) \<or> r = Err Pattern"
  using post[OF assms] by (cases r) (auto simp: post_all_def post_def fails_ok_def exn_ok_def)


subsection \<open>Successful unification\<close>

text \<open>
  A returned environment \<open>env'\<close> extends \<open>env\<close>, its type environment extends \<open>\<theta>\<close>, and it
  satisfies the invariants again; the instances of \<open>env'\<close> are well-typed (for a typing that agrees
  with the typing of the instance of the problem on the old variables). Hence problems can be
  chained.
\<close>

theorem Ok_inv:
  assumes "unify alg s t env = Some (Ok env')"
  shows "textends (tyenv env) (tyenv env')" "extends env' env" "maxidx env \<le> maxidx env'"
    "tinv ar (maxidx env') (tyenv env') A" "tsorted alg (tyenv env')"
    "\<forall>T\<in>etys env'. tyw ar (tyenv env') A T" "nacyc env'"
    "\<And>\<rho> W. gsol alg ar (tyenv env') \<rho> \<Longrightarrow> inst_ok ar W \<rho> [] s t env \<Longrightarrow>
      \<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> env')"
  using post[OF assms] tres[OF assms] by (simp_all add: post_all_def postok_def tres_def)

text \<open>
  A returned environment \<open>env'\<close> is a most general unifier of all ground instances: the instances
  of \<open>s\<close> and \<open>t\<close> are equivalent relative to every ground instance of \<open>env'\<close>, and every unifier of a
  ground instance of the problem extends (on the new variables) to a solution of a ground
  instance of \<open>env'\<close> (on the new type variables).
\<close>

theorem Ok_sound:
  assumes "unify alg s t env = Some (Ok env')" "gsol alg ar (tyenv env') \<rho>"
  shows "gsol alg ar (tyenv env) \<rho>" "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t"
  using post[OF assms(1)] assms(2) gsol_textends by (auto simp: post_all_def postok_def)

theorem Ok_most_general:
  assumes "unify alg s t env = Some (Ok env')" "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> [] s t env"
    "solution W \<tau>' \<sigma> (instE \<rho> env)" "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
  shows "\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
    agreeV (maxidx env) W W' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution W' \<tau>' \<sigma>' (instE \<rho>' env')"
proof -
  from post[OF assms(1)] have "postok alg ar A [] s t env env'" by (simp add: post_all_def)
  then obtain \<rho>' W' \<sigma>' where "gsol alg ar (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
    "sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env')"
    using assms(2-) unfolding postok_def by blast
  then show ?thesis by (auto simp: sol_ext_def)
qed

text \<open>Every acyclic environment has a solution, so the problem is unifiable.\<close>

theorem Ok_unifiable:
  assumes un: "unify alg s t env = Some (Ok env')"
  shows unifiable
proof -
  note inv = Ok_inv[OF un]
  obtain \<rho> where g': "gsol alg ar (tyenv env') \<rho>" using gsol_exists[OF inv(4,5)] .
  have g: "gsol alg ar (tyenv env) \<rho>" by (rule gsol_textends[OF inv(1) g'])
  from instances[OF g] obtain W where i: "inst_ok ar W \<rho> [] s t env" by blast
  from inv(8)[OF g' i] obtain W' where te: "ty_ext ar W (instE \<rho> env) W' (instE \<rho> env')" by blast
  have ety: "env_typed W' (instE \<rho> env')" and agV: "agreeV (maxidx env) W W'"
    and wf: "wf_env ar (instE \<rho> env')"
    using te by (simp_all add: ty_ext_def)
  have ac: "acyc (instE \<rho> env')" using acyc_instE[OF ety] inv(7) by simp
  note es = env_solution[OF ac wf ety]
  let ?\<sigma> = "env_sol (instE \<rho> env') W'"
  have sat: "sat ?\<sigma> (instE \<rho> env)"
    using sat_extends[OF solutionD(4)[OF es(1)] extends_instE[OF inv(2)]] .
  have uni: "unifies ?\<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    using env_equivD[OF Ok_sound(2)[OF un g'] solutionD(1,4)[OF es(1)]] by (simp add: unifies_def)
  have rig: "\<forall>n\<in>range code. \<forall>m\<in>FV (?\<sigma> n). rigid_code m" using es(2) by blast
  define \<sigma>'' where "\<sigma>'' = (\<lambda>n. case atom_of n of
    AVar x \<Rightarrow> if n = code (AVar x) \<and> maxidx env < snd x then dB.Var (code (AFree STR '''' (W x)))
      else ?\<sigma> n
  | _ \<Rightarrow> ?\<sigma> n)"
  note rt = solution_retype[OF es(1) rig, of "maxidx env" W, unfolded instE_simps, OF agV, folded \<sigma>''_def]
  have "sat \<sigma>'' (instE \<rho> env)" by (rule sat_agree[OF sat _ ]) (use i rt(4) in \<open>simp_all add: inst_ok_def\<close>)
  moreover have "unifies \<sigma>'' (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    using uni mk_subst_agree[OF below_inst[THEN iffD2, OF below_s] rt(4)]
      mk_subst_agree[OF below_inst[THEN iffD2, OF below_t] rt(4)]
    by (simp add: unifies_def)
  ultimately show ?thesis using g i rt(1-3) by (auto simp: solution_def)
qed

theorem Ok_patterns:
  "unify alg s t env = Some (Ok env') \<Longrightarrow> ppat s \<Longrightarrow> ppat t \<Longrightarrow> env_ppat env \<Longrightarrow> env_ppat env'"
  using post by (auto simp: post_all_def postok_def)


subsection \<open>Failure\<close>

text \<open>Failure with \<open>Unif\<close> is final: no ground instance of the problem is unifiable.\<close>

theorem Unif_not_unifiable:
  assumes "unify alg s t env = Some (Err (Unif u))"
  shows "\<not> unifiable"
  using post[OF assms] by (auto simp: post_all_def post_def no_unif_def)

text \<open>\<^const>\<open>unify\<close> gives up only on problems that are not patterns.\<close>

theorem Pattern_not_pattern:
  assumes "unify alg s t env = Some (Err Pattern)"
  shows "\<not> (ppat s \<and> ppat t \<and> env_ppat env)"
  using post[OF assms] by (auto simp: post_all_def post_def)


subsection \<open>Decidability on patterns\<close>

corollary decides:
  assumes "ppat s" "ppat t" "env_ppat env"
  shows "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow> unifiable"
    and "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow> \<not> unifiable"
proof -
  from terminates obtain r where un: "unify alg s t env = Some r" by blast
  have "r \<noteq> Err Pattern" using Pattern_not_pattern un assms by blast
  with result[OF un] consider env' where "r = Ok env'" | u where "r = Err (Unif u)" by blast
  then show "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow> unifiable"
    and "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow> \<not> unifiable"
    using un Ok_unifiable Unif_not_unifiable by (cases; auto)+
qed

end

end
