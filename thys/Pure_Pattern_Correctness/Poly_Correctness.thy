section \<open>Correctness of Polymorphic Pattern Unification\<close>

theory Poly_Correctness
  imports Poly_Typing
begin

text \<open>
  The main results about \<^const>\<open>unify\<close> on problems with schematic type variables (with sorts),
  collected in one place, in analogy to theory \<^theory>\<open>Pure_Pattern_Correctness.Pattern_Correctness\<close>.
  A polymorphic problem \<open>s =?= t\<close> relative to \<open>env\<close>, with type environment \<open>\<theta> = tyenv env\<close>, is
  well-formed if
  \<^item> \<open>env\<close> satisfies the invariant \<^const>\<open>penv_inv\<close>: \<open>\<theta>\<close> satisfies the invariant \<^const>\<open>tinv\<close> of
    type unification (it is acyclic, its bindings are well-formed, and each type variable has a
    single sort and is not newer than \<open>maxidx env\<close>) and respects sorts, and \<open>env\<close> is acyclic,
    well-formed, typed by \<open>W\<close> modulo \<open>\<theta>\<close> (\<^const>\<open>env_typed_mod\<close>), and fresh;
  \<^item> \<^const>\<open>tinv\<close> also holds for the type variables of \<open>s\<close> and \<open>t\<close> (\<^const>\<open>ptvars\<close>);
  \<^item> \<open>s\<close> and \<open>t\<close> are well-formed closed terms of the same type \<open>T\<close> modulo \<open>\<theta>\<close> (their types
    normalized by \<^const>\<open>tnormt\<close>), whose variables are not newer than \<open>maxidx env\<close>.
  For an empty \<open>\<theta>\<close>, \<^const>\<open>tnormt\<close> is the identity and these are the assumptions of
  \<^locale>\<open>unif_problem\<close>, plus \<^const>\<open>tinv\<close>.

  A polymorphic problem stands for all its ground instances: for each well-sorted ground
  solution \<open>\<rho>\<close> of \<open>\<theta>\<close> (\<^const>\<open>gsol\<close>), the monomorphic problem obtained by instantiating the type
  variables with \<open>\<rho>\<close> (\<open>ground_instance\<close> below). The results are those of the monomorphic case, for all
  ground instances at once.
\<close>

locale poly_problem = wf_algebra alg ar for alg :: algebra and ar :: "name \<Rightarrow> nat" +
  fixes W :: "indexname \<Rightarrow> ptyp" and env :: env and s t :: pterm and T :: ptyp
  assumes env: "penv_inv alg ar W env"
    and tinv: "tinv ar (maxidx env) (tyenv env) (ptvars env s t)"
    and wf_s: "pwf_term ar 0 s" and wf_t: "pwf_term ar 0 t"
    and typed_s: "has_type W [] (tnormt (tyenv env) s) T"
    and typed_t: "has_type W [] (tnormt (tyenv env) t) T"
    and below_s: "below (maxidx env) s" and below_t: "below (maxidx env) t"
begin

text \<open>The typing of the ground instance for \<open>\<rho>\<close>:\<close>

abbreviation W\<^sub>i :: "tinst \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "W\<^sub>i \<rho> \<equiv> \<lambda>x. tsubst \<rho> (W x)"

text \<open>The ground instances are well-formed monomorphic problems:\<close>

lemma ground_instance:
  assumes g: "gsol alg ar (tyenv env) \<rho>"
  shows "unif_problem ar (W\<^sub>i \<rho>) (instE \<rho> env) (inst \<rho> s) (inst \<rho> t) (tsubst \<rho> T)"
proof
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF tinv] tinv_tcons_env[OF tinv] by simp_all
  have sol: "tsol (tyenv env) \<rho>" and gr: "\<forall>v S. ground ar (\<rho> v S)" using g by (simp_all add: gsol_def)
  have it: "inst \<rho> (tnormt (tyenv env) u) = inst \<rho> u" if "u = s \<or> u = t" for u
    by (rule inst_tnormt[OF ac sol]) (use that in \<open>auto intro!: tinv_tcons[OF tinv] simp: ptvars_def\<close>)
  show "env_inv ar (W\<^sub>i \<rho>) (instE \<rho> env)" by (rule penv_inv_inst[OF env g])
  show "wf_term ar 0 (inst \<rho> s)" "wf_term ar 0 (inst \<rho> t)" using wf_term_inst wf_s wf_t gr by blast+
  show "has_type (W\<^sub>i \<rho>) [] (inst \<rho> s) (tsubst \<rho> T)" "has_type (W\<^sub>i \<rho>) [] (inst \<rho> t) (tsubst \<rho> T)"
    using has_type_inst[OF typed_s, of \<rho>] has_type_inst[OF typed_t, of \<rho>] it by simp_all
  show "below (maxidx (instE \<rho> env)) (inst \<rho> s)" "below (maxidx (instE \<rho> env)) (inst \<rho> t)"
    using below_s below_t by simp_all
qed

text \<open>Some ground instance is unifiable:\<close>

abbreviation unifiable :: bool where
  "unifiable \<equiv> \<exists>\<rho>. gsol alg ar (tyenv env) \<rho> \<and>
    unif_problem.unifiable (W\<^sub>i \<rho>) (instE \<rho> env) (inst \<rho> s) (inst \<rho> t)"

text \<open>The results of the inductions over \<^const>\<open>unif\<close>, instantiated to the problem:\<close>

lemma instances: "gsol alg ar (tyenv env) \<rho> \<Longrightarrow> inst_ok ar (W\<^sub>i \<rho>) \<rho> [] s t env"
  by (rule inst_ok_mod[OF env tinv _ wf_s typed_s wf_t typed_t])

lemma pre: "pre alg ar (ptvars env s t) [] s t env"
proof -
  have "\<forall>T\<in>tys s \<union> tys t \<union> etys env. tyw ar (tyenv env) (ptvars env s t) T"
  proof
    fix U assume U: "U \<in> tys s \<union> tys t \<union> etys env"
    then have "wft ar U" using wf_s wf_t pwf_envD[OF penv_invD(4)[OF env]]
      by (auto simp: pwf_term_def etys_def)
    with U show "tyw ar (tyenv env) (ptvars env s t) U"
      by (intro tyw_tvars) (auto simp: ptvars_def etvars_def)
  qed
  then show ?thesis using tinv penv_invD(2)[OF env] below_s below_t instances by (auto simp: pre_def)
qed

lemma post: "unify alg s t env = Some r \<Longrightarrow> post_all alg ar (ptvars env s t) [] s t env r"
  unfolding unify_def by (rule unif_post[OF _ refl pre])

lemma postok: "unify alg s t env = Some (Ok env') \<Longrightarrow> postok alg ar (ptvars env s t) [] s t env env'"
  using post by (simp add: post_all_def)

lemma tres: "unify alg s t env = Some r \<Longrightarrow> tres (ptvars env s t) env r"
  using unif_terminates[OF finite_ptvars pre penv_invD(3)[OF env]] by (auto simp: unify_def)


subsection \<open>Termination\<close>

text \<open>\<^const>\<open>unify\<close> terminates; it returns an environment, fails, or gives up.\<close>

theorem terminates: "\<exists>r. unify alg s t env = Some r"
  using unif_terminates[OF finite_ptvars pre penv_invD(3)[OF env]] unfolding unify_def by blast

theorem result:
  assumes "unify alg s t env = Some r"
  shows "(\<exists>env'. r = Ok env') \<or> (\<exists>u. r = Err (Unif u)) \<or> r = Err Pattern"
  using post[OF assms] by (cases r) (auto simp: post_all_def post_def fails_ok_def exn_ok_def)


subsection \<open>Successful unification\<close>

text \<open>
  A returned environment \<open>env'\<close> extends \<open>env\<close> and its type environment extends \<open>\<theta>\<close>, and the
  problem is well-formed again relative to \<open>env'\<close>, for a typing \<open>W'\<close> and the type \<open>T\<close> normalized
  by the new type environment. Hence unification problems can be chained, as in
  \<open>Unify.unifiers\<close>.
\<close>

theorem Ok_inv:
  assumes "unify alg s t env = Some (Ok env')"
  shows "\<exists>W'. poly_problem alg ar W' env' s t (tnorm (tyenv env') T)"
    and "extends env' env" "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
proof -
  note p = postok[OF assms, unfolded postok_def]
  show "extends env' env" "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
    using p by blast+
  have nac: "nacyc env'" using tres[OF assms] by (simp add: tres_def)
  obtain W' where inv': "penv_inv alg ar W' env'"
    and ts: "has_type W' [] (tnormt (tyenv env') s) (tnorm (tyenv env') T)"
    and tt: "has_type W' [] (tnormt (tyenv env') t) (tnorm (tyenv env') T)"
    by (rule postok_penv_inv[OF env tinv wf_s typed_s below_s wf_t typed_t below_t postok[OF assms] nac])
  have "tinv ar (maxidx env') (tyenv env') (ptvars env' s t)"
  proof (rule tinv_subset)
    show "tinv ar (maxidx env') (tyenv env') (ptvars env s t)" using p by blast
    show "ptvars env' s t \<subseteq> tvars_env (tyenv env') \<union> ptvars env s t"
      using p by (auto simp: ptvars_def etvars_def tyw_def)
  qed
  moreover have "below (maxidx env') s" "below (maxidx env') t"
    using below_s below_t p by (auto intro: below_mono)
  ultimately show "\<exists>W'. poly_problem alg ar W' env' s t (tnorm (tyenv env') T)"
    using inv' ts tt wf_s wf_t by (intro exI[of _ W']) unfold_locales
qed

text \<open>
  A returned environment \<open>env'\<close> is a most general unifier of all ground instances: the solutions
  of a ground instance of \<open>env'\<close> satisfy the corresponding instance of \<open>env\<close> and unify the
  instances of \<open>s\<close> and \<open>t\<close>, and every solution of a ground instance of \<open>env\<close> that unifies them
  extends (on the new variables) to a solution of a ground instance of \<open>env'\<close>, for a type
  instantiation that extends (on the new type variables) the one of the instance.
\<close>

theorem Ok_sound:
  assumes "unify alg s t env = Some (Ok env')" "gsol alg ar (tyenv env') \<rho>"
    "closed_on UNIV \<sigma>" "sat \<sigma> (instE \<rho> env')"
  shows "sat \<sigma> (instE \<rho> env) \<and> unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
proof -
  note p = postok[OF assms(1), unfolded postok_def]
  have "sat \<sigma> (instE \<rho> env)" using sat_extends[OF assms(4) extends_instE] p by blast
  moreover have "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" using p assms(2) by blast
  ultimately show ?thesis using env_equivD[OF _ assms(3,4)] by (simp add: unifies_def)
qed

theorem Ok_most_general:
  assumes "unify alg s t env = Some (Ok env')" "gsol alg ar (tyenv env) \<rho>"
    "solution (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env)" "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
  shows "\<exists>\<rho>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
    (\<exists>V' \<sigma>'. agreeV (maxidx env) (W\<^sub>i \<rho>) V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' (instE \<rho>' env'))"
proof -
  obtain \<rho>' V' \<sigma>' where "gsol alg ar (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
    "sol_ext ar (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env) V' \<sigma>' (instE \<rho>' env')"
    using postok[OF assms(1)] assms(2-) instances[OF assms(2)] unfolding postok_def by blast
  then show ?thesis by (auto simp: sol_ext_def)
qed

text \<open>The ground instances of a returned environment satisfy the monomorphic invariant:\<close>

lemma Ok_instances:
  assumes un: "unify alg s t env = Some (Ok env')" and g': "gsol alg ar (tyenv env') \<rho>"
  shows "\<exists>V'. env_inv ar V' (instE \<rho> env') \<and> agreeV (maxidx env) (W\<^sub>i \<rho>) V'"
proof -
  note p = postok[OF un, unfolded postok_def]
  have "gsol alg ar (tyenv env) \<rho>" using gsol_textends p g' by blast
  with p g' instances obtain V' where te: "ty_ext ar (W\<^sub>i \<rho>) (instE \<rho> env) V' (instE \<rho> env')"
    by blast
  have "nacyc env'" using tres[OF un] by (simp add: tres_def)
  with te show ?thesis using acyc_instE by (fastforce simp: ty_ext_def env_inv_def)
qed

text \<open>Every acyclic environment has a solution, so the problem is unifiable.\<close>

theorem Ok_unifiable:
  assumes un: "unify alg s t env = Some (Ok env')"
  shows unifiable
proof -
  note p = postok[OF un, unfolded postok_def]
  obtain \<rho> where g': "gsol alg ar (tyenv env') \<rho>" using gsol_exists p by blast
  have g: "gsol alg ar (tyenv env) \<rho>" using gsol_textends p g' by blast
  from Ok_instances[OF un g'] obtain V' where i: "env_inv ar V' (instE \<rho> env')"
    and agV: "agreeV (maxidx env) (W\<^sub>i \<rho>) V'" by blast
  note es = env_solution[OF env_invD(1-3)[OF i]]
  let ?\<sigma> = "env_sol (instE \<rho> env') V'"
  from Ok_sound[OF un g' solutionD(1,4)[OF es(1)]]
  have sat: "sat ?\<sigma> (instE \<rho> env)" and uni: "unifies ?\<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))" by blast+
  have rig: "\<forall>n\<in>range code. \<forall>m\<in>FV (?\<sigma> n). rigid_code m" using es(2) by blast
  define \<sigma>'' where "\<sigma>'' = (\<lambda>n. case atom_of n of
    AVar x \<Rightarrow> if n = code (AVar x) \<and> maxidx env < snd x then dB.Var (code (AFree STR '''' (W\<^sub>i \<rho> x)))
      else ?\<sigma> n
  | _ \<Rightarrow> ?\<sigma> n)"
  note rt = solution_retype[OF es(1) rig, of "maxidx env" "W\<^sub>i \<rho>", unfolded instE_simps, OF agV,
    folded \<sigma>''_def]
  have "sat \<sigma>'' (instE \<rho> env)"
    by (rule sat_agree[OF sat _ ]) (use instances[OF g] rt(4) in \<open>simp_all add: inst_ok_def\<close>)
  moreover have "unifies \<sigma>'' (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    using uni mk_subst_agree[OF below_inst[THEN iffD2, OF below_s] rt(4)]
      mk_subst_agree[OF below_inst[THEN iffD2, OF below_t] rt(4)]
    by (simp add: unifies_def)
  ultimately show ?thesis using g rt(1-3) by (auto simp: solution_def)
qed

theorem Ok_patterns:
  "unify alg s t env = Some (Ok env') \<Longrightarrow> ppat s \<Longrightarrow> ppat t \<Longrightarrow> env_ppat env \<Longrightarrow> env_ppat env'"
  using postok by (auto simp: postok_def)


subsection \<open>Failure\<close>

text \<open>Failure with \<open>Unif\<close> is final: no ground instance of the problem is unifiable.\<close>

theorem Unif_not_unifiable:
  assumes "unify alg s t env = Some (Err (Unif u))"
  shows "\<not> unifiable"
  using post[OF assms] instances by (auto simp: post_all_def post_def no_unif_def)

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
