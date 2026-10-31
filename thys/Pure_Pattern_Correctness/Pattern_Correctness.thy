section \<open>Correctness of Pattern Unification\<close>

theory Pattern_Correctness
  imports Poly_Semantics
begin

context csig
begin

text \<open>
  The main results about \<^const>\<open>unify\<close>, collected in one place. A unification problem
  \<open>s =?= t\<close> relative to an environment \<open>env\<close>, with type environment \<open>\<theta> = tyenv env\<close>, may contain
  schematic type variables with sorts. It is well-formed if
  \<^item> \<open>env\<close> satisfies the invariant \<^const>\<open>penv_inv\<close>: \<open>\<theta>\<close> satisfies the invariant \<^const>\<open>tinv\<close> of
    type unification (it is acyclic, its bindings are well-formed, and each type variable has a
    single sort and is not newer than \<open>maxidx env\<close>) and respects sorts, and \<open>env\<close> is acyclic,
    well-formed, typed in itself (\<^const>\<open>wt_env\<close>), and fresh (its variables and bindings are not
    newer than \<open>maxidx env\<close>);
  \<^item> \<^const>\<open>tinv\<close> also holds for the type variables of \<open>s\<close> and \<open>t\<close> (\<^const>\<open>ptvars\<close>);
  \<^item> \<open>s\<close> and \<open>t\<close> are well-formed closed terms of the same type \<open>T\<close> in \<open>env\<close>
    (\<^const>\<open>typed\<close>: bound variables have the types of their bindings, the others the types given
    by \<open>W\<close>, and types are compared modulo \<open>\<theta>\<close>), whose variables are not newer than
    \<open>maxidx env\<close>.
  Neither \<open>s\<close>, \<open>t\<close> nor the bindings of \<open>env\<close> need to be patterns or \<open>\<beta>\<close>-normal.

  Terms are compared via their translation \<^const>\<open>tr\<close> into de Bruijn terms modulo \<open>\<beta>\<eta>\<close>. A
  solution of \<open>env\<close> is a pair of a well-sorted ground instantiation \<open>\<rho>\<close> of the type variables
  that solves \<open>\<theta>\<close> (\<^const>\<open>gsol\<close>) and a substitution \<open>\<sigma>\<close> for the term variables that satisfies the
  bindings of the instance of \<open>env\<close> (\<^const>\<open>solves\<close>). The problem is unifiable if a solution
  unifies the instances of \<open>s\<close> and \<open>t\<close>, where \<open>\<sigma>\<close> is well-typed (\<^const>\<open>solution\<close>).

  Soundness also holds in the polymorphic semantics of \<^theory>\<open>Pure_Pattern_Correctness.Poly_Semantics\<close>,
  without instantiating the type variables: a closed substitution that satisfies the environment
  and respects its type environment (\<^const>\<open>psat\<close>). The other results are about ground
  instances: such a substitution is untyped, so it may unify a problem without a well-typed
  unifier.
\<close>

definition solves :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "solves alg ar env \<rho> \<sigma> \<longleftrightarrow> gsol alg ar (tyenv env) \<rho> \<and> closed_on UNIV \<sigma> \<and> sat \<sigma> (instE \<rho> env)"

end

locale unif_problem = wf_csig ctab alg ar
  for ctab :: "name \<Rightarrow> ptyp option" and alg :: algebra and ar :: "name \<Rightarrow> nat" +
  fixes W :: "indexname \<Rightarrow> ptyp" and env :: env and s t :: pterm and T :: ptyp
  assumes env: "penv_inv alg ar W env"
    and tinv: "tinv ar (maxidx env) (tyenv env) (ptvars env s t)"
    and wf_s: "pwf_term ar 0 s" and wf_t: "pwf_term ar 0 t"
    and typed_s: "typed env W [] s T" and typed_t: "typed env W [] t T"
    and below_s: "below (maxidx env) s" and below_t: "below (maxidx env) t"
    and cert: "tcert alg (tvars_env (tyenv env) \<union> ptvars env s t)"
begin

text \<open>The typing of the variables in the ground instance for \<open>\<rho>\<close>:\<close>

abbreviation W\<^sub>i :: "tinst \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "W\<^sub>i \<rho> \<equiv> \<lambda>x. tsubst \<rho> (tctx env W x)"

abbreviation unifiable :: bool where
  "unifiable \<equiv> \<exists>\<rho> \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<and> solution (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env) \<and>
    unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"

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
  problem is well-formed again relative to \<open>env'\<close>, for a new typing \<open>W'\<close> of the unbound
  variables. Hence unification problems can be chained, as in \<open>Unify.unifiers\<close>.
\<close>

theorem Ok_inv:
  assumes "unify alg s t env = Some (Ok env')"
  shows "\<exists>W'. unif_problem ctab alg ar W' env' s t T"
    and "extends env' env" "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
proof -
  note p = postok[OF assms, unfolded postok_def]
  show "extends env' env" "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
    using p by blast+
  have nac: "nacyc env'" using tres[OF assms] by (simp add: tres_def)
  obtain W' where "penv_inv alg ar W' env'" "typed env' W' [] s T" "typed env' W' [] t T"
    by (rule postok_penv_inv[OF env tinv wf_s typed_s below_s wf_t typed_t below_t postok[OF assms] nac])
  moreover have "tinv ar (maxidx env') (tyenv env') (ptvars env' s t)"
  proof (rule tinv_subset)
    show "tinv ar (maxidx env') (tyenv env') (ptvars env s t)" using p by blast
    show "ptvars env' s t \<subseteq> tvars_env (tyenv env') \<union> ptvars env s t"
      using p by (auto simp: ptvars_def etvars_def tyw_def)
  qed
  moreover have "below (maxidx env') s" "below (maxidx env') t"
    using below_s below_t p by (auto intro: below_mono)
  moreover have "tcert alg (tvars_env (tyenv env') \<union> ptvars env' s t)"
  proof (rule tcert_mono)
    have "tcert alg (tvars_env (tyenv env'))" using p cert by blast
    then show "tcert alg (tvars_env (tyenv env') \<union> ptvars env s t)" using cert by simp
    show "tvars_env (tyenv env') \<union> ptvars env' s t \<subseteq> tvars_env (tyenv env') \<union> ptvars env s t"
      using p by (auto simp: ptvars_def etvars_def tyw_def)
  qed
  ultimately show "\<exists>W'. unif_problem ctab alg ar W' env' s t T"
    using wf_s wf_t by (intro exI[of _ W']) unfold_locales
qed

text \<open>
  A returned environment \<open>env'\<close> is a most general unifier: its solutions are solutions of
  \<open>env\<close> that unify (the instances of) \<open>s\<close> and \<open>t\<close>, and every well-typed solution of \<open>env\<close> that
  unifies them extends to a solution of \<open>env'\<close>: the type instantiation on the new type
  variables, the substitution on the new variables.
\<close>

theorem Ok_sound:
  assumes "unify alg s t env = Some (Ok env')" "solves alg ar env' \<rho> \<sigma>"
  shows "solves alg ar env \<rho> \<sigma> \<and> unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
proof -
  note p = postok[OF assms(1), unfolded postok_def]
  have g': "gsol alg ar (tyenv env') \<rho>" and \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> (instE \<rho> env')"
    using assms(2) by (simp_all add: solves_def)
  have "gsol alg ar (tyenv env) \<rho>" using gsol_textends p g' by blast
  moreover have "sat \<sigma> (instE \<rho> env)" using sat_extends[OF \<sigma>(2) extends_instE] p by blast
  moreover have "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" using p g' by blast
  ultimately show ?thesis using env_equivD[OF _ \<sigma>] \<sigma>(1) by (simp add: solves_def unifies_def)
qed

text \<open>
  The same in the polymorphic semantics: \<open>env'\<close> extends \<open>env\<close> also in its type environment, and its
  solutions are solutions of \<open>env\<close> that unify \<open>s\<close> and \<open>t\<close>.
\<close>

theorem Ok_psound:
  assumes "unify alg s t env = Some (Ok env')"
  shows "pextends env' env" "env' \<Turnstile>\<^sub>p s \<approx> t"
    and "psat \<sigma> env' \<Longrightarrow> psat \<sigma> env \<and> unifies \<sigma> (tr s) (tr t)"
proof -
  have tw: "\<forall>T\<in>tys s \<union> tys t. tyw ar (tyenv env) (ptvars env s t) T" using pre by (simp add: pre_def)
  note pe = postok_penv_equiv[OF postok[OF assms] tw]
  show "pextends env' env" "env' \<Turnstile>\<^sub>p s \<approx> t" by (rule pe)+
  show "psat \<sigma> env' \<Longrightarrow> psat \<sigma> env \<and> unifies \<sigma> (tr s) (tr t)"
    using psat_pextends[OF _ pe(1)] penv_equivD[OF pe(2)] by (simp add: unifies_def)
qed

theorem Ok_most_general:
  assumes "unify alg s t env = Some (Ok env')" "gsol alg ar (tyenv env) \<rho>"
    "solution (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env)" "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
  shows "\<exists>\<rho>' V' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
    agreeV (maxidx env) (W\<^sub>i \<rho>) V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' (instE \<rho>' env')"
proof -
  obtain \<rho>' V' \<sigma>' where "gsol alg ar (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
    "sol_ext ar (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env) V' \<sigma>' (instE \<rho>' env')"
    using postok[OF assms(1)] assms(2-) instances[OF assms(2)] unfolding postok_def by blast
  then show ?thesis by (auto simp: sol_ext_def)
qed

text \<open>The ground instances of a returned environment satisfy the invariant of the core:\<close>

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
  have "solves alg ar env' \<rho> ?\<sigma>" using g' solutionD(1,4)[OF es(1)] by (simp add: solves_def)
  from Ok_sound[OF un this]
  have sat: "sat ?\<sigma> (instE \<rho> env)" and uni: "unifies ?\<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    by (simp_all add: solves_def)
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

text \<open>Bindings that are patterns stay patterns.\<close>

theorem Ok_patterns:
  "unify alg s t env = Some (Ok env') \<Longrightarrow> ppat s \<Longrightarrow> ppat t \<Longrightarrow> env_ppat env \<Longrightarrow> env_ppat env'"
  using postok by (auto simp: postok_def)


subsection \<open>Failure\<close>

text \<open>
  Failure with \<open>Unif\<close> is final: the problem is not unifiable, also when the failure comes from a
  clash of types or sorts.
\<close>

theorem Unif_not_unifiable:
  assumes "unify alg s t env = Some (Err (Unif u))"
  shows "\<not> unifiable"
  using post[OF assms] instances by (auto simp: post_all_def post_def no_unif_def)

text \<open>\<^const>\<open>unify\<close> gives up only if \<open>s\<close>, \<open>t\<close> or a binding of \<open>env\<close> is not a pattern.\<close>

theorem Pattern_not_pattern:
  assumes "unify alg s t env = Some (Err Pattern)"
  shows "\<not> (ppat s \<and> ppat t \<and> env_ppat env)"
  using post[OF assms] by (auto simp: post_all_def post_def)


subsection \<open>Decidability on patterns\<close>

text \<open>
  Hence on \<open>\<beta>\<close>-normal patterns in an environment of patterns, \<^const>\<open>unify\<close> decides
  unifiability. On other problems, it may give up both on unifiable problems
  (\<open>?F =?= c ((\<lambda>x. d) ?F)\<close>) and on non-unifiable ones (\<open>f (?F a) (?F a) =?= f b c\<close>).
\<close>

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
