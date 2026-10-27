section \<open>Correctness of Polymorphic Pattern Unification\<close>

theory Poly_Correctness
  imports Poly_Unif_Term
begin

text \<open>
  The main results about \<^const>\<open>unify\<close> on problems with schematic type variables (with sorts),
  collected in one place. The assumptions are those of the monomorphic locale
  \<^locale>\<open>unif_problem\<close>, read modulo the type environment \<open>\<theta> = tyenv env\<close>, plus the invariant
  of type unification for \<open>\<theta>\<close>.

  A polymorphic problem \<open>s =?= t\<close> relative to \<open>env\<close> stands for all its ground instances: for
  each well-sorted ground solution \<open>\<rho>\<close> of \<open>\<theta>\<close> (\<^const>\<open>gsol\<close>), the monomorphic problem
  \<open>inst \<rho> s =?= inst \<rho> t\<close> relative to \<open>instE \<rho> env\<close>, typed by the instance
  \<open>\<lambda>x. tsubst \<rho> (W x)\<close> of the typing \<open>W\<close> of the problem. \<^const>\<open>unify\<close> terminates, and its
  results are correct for all ground instances at once.
\<close>


subsection \<open>Typing modulo the type environment\<close>

text \<open>Terms with their types normalized by a type environment:\<close>

fun tnormt :: "tyenv \<Rightarrow> pterm \<Rightarrow> pterm" where
  "tnormt \<theta> (Const a T) = Const a (tnorm \<theta> T)"
| "tnormt \<theta> (Free a T) = Free a (tnorm \<theta> T)"
| "tnormt \<theta> (Var x T) = Var x (tnorm \<theta> T)"
| "tnormt \<theta> (Bound i) = Bound i"
| "tnormt \<theta> (Abs a T t) = Abs a (tnorm \<theta> T) (tnormt \<theta> t)"
| "tnormt \<theta> (s $ t) = tnormt \<theta> s $ tnormt \<theta> t"

lemma tnormt_empty: "vt_is_empty \<theta> \<Longrightarrow> tnormt \<theta> t = t"
  by (induction t) (simp_all add: tnorm_empty)

text \<open>An environment typed by \<open>W\<close> modulo \<open>\<theta>\<close>:\<close>

definition env_typed_mod :: "tyenv \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "env_typed_mod \<theta> W env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
    W x = tnorm \<theta> U \<and> has_type W [] (tnormt \<theta> u) (tnorm \<theta> U))"

text \<open>Well-formed terms whose types need not be ground:\<close>

definition pwf_term :: "(name \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pterm \<Rightarrow> bool" where
  "pwf_term ar n t \<longleftrightarrow> proper t \<and> (\<forall>T\<in>tys t. wft ar T) \<and> no_loose_bound (tr t) n"

text \<open>The type variables of a problem:\<close>

definition ptvars :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> (indexname \<times> psort) set" where
  "ptvars env s t = (\<Union>T\<in>tys s \<union> tys t \<union> etys env. tvars T)"

lemma finite_tys[simp]: "finite (tys t)"
  by (induction t) auto

lemma finite_etys: "finite (etys env)"
proof -
  have "etys env = (\<Union>x\<in>{x. vt_lookup (tenv env) x \<noteq> None}.
      insert (fst (the (vt_lookup (tenv env) x))) (tys (snd (the (vt_lookup (tenv env) x)))))"
    by (force simp: etys_def)
  then show ?thesis using finite_vt_lookup[of "tenv env"] by simp
qed

lemma finite_ptvars: "finite (ptvars env s t)"
  using finite_etys by (simp add: ptvars_def)

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


subsection \<open>Ground instances\<close>

lemma typs_ok_inst: "\<forall>T\<in>tys t. wft ar T \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> typs_ok ar (inst \<rho> t)"
  by (induction t) (auto intro: ground_tsubst)

lemma wf_term_inst: "pwf_term ar n t \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> wf_term ar n (inst \<rho> t)"
  by (simp add: pwf_term_def wf_term_def typs_ok_inst)

lemma has_type_inst:
  "has_type W Ts t T \<Longrightarrow> has_type (\<lambda>x. tsubst \<rho> (W x)) (map (tsubst \<rho>) Ts) (inst \<rho> t) (tsubst \<rho> T)"
  by (induction rule: has_type.induct) (auto intro: has_type.intros)

lemma inst_tnormt:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tsol \<theta> \<rho>"
  shows "\<forall>T\<in>tys t. tcons \<theta> T \<Longrightarrow> inst \<rho> (tnormt \<theta> t) = inst \<rho> t"
  by (induction t) (simp_all add: tsubst_tnorm[OF assms])

text \<open>The ground instances of a problem typed modulo the type environment are well-typed:\<close>

lemma inst_ok_typed:
  assumes ac: "tacyc \<theta>" "tcons_env \<theta>" and sol: "tsol \<theta> \<rho>" and g: "\<forall>v S. ground ar (\<rho> v S)"
    and tc: "\<forall>T\<in>tys s \<union> tys t \<union> etys env. tcons \<theta> T"
    and s: "pwf_term ar 0 s" "has_type W [] (tnormt \<theta> s) T"
    and t: "pwf_term ar 0 t" "has_type W [] (tnormt \<theta> t) T"
    and env: "\<And>x U u. vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> pwf_term ar 0 u \<and> wft ar U"
      "env_typed_mod \<theta> W env" "fresh_env env"
  shows "inst_ok ar (\<lambda>x. tsubst \<rho> (W x)) \<rho> [] s t env"
proof -
  let ?W = "\<lambda>x. tsubst \<rho> (W x)"
  note it = inst_tnormt[OF ac sol]
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
    have tU: "tcons \<theta> U0" and tu: "\<forall>T\<in>tys u0. tcons \<theta> T" using tc etysI[OF b] by auto
    from env(2) b have "W x = tnorm \<theta> U0" "has_type W [] (tnormt \<theta> u0) (tnorm \<theta> U0)"
      unfolding env_typed_mod_def by blast+
    then show "?W x = U \<and> has_type ?W [] u U"
      using has_type_inst[of W "[]" "tnormt \<theta> u0" "tnorm \<theta> U0" \<rho>]
      by (simp add: U u it[OF tu] tsubst_tnorm[OF ac sol tU])
  qed
  moreover have "fresh_env (instE \<rho> env)"
    using env(3) unfolding fresh_env_def by auto
  moreover have "has_type ?W [] (inst \<rho> s) (tsubst \<rho> T)" "has_type ?W [] (inst \<rho> t) (tsubst \<rho> T)"
    using has_type_inst[OF s(2), of \<rho>] has_type_inst[OF t(2), of \<rho>] tc by (simp_all add: it)
  ultimately show ?thesis
    using wf_term_inst[OF s(1) g] wf_term_inst[OF t(1) g] by (auto simp: inst_ok_def binders_ok_def)
qed


subsection \<open>Well-formed polymorphic problems\<close>

text \<open>
  A polymorphic problem \<open>s =?= t\<close> relative to \<open>env\<close>, with type environment \<open>\<theta> = tyenv env\<close>, is
  well-formed if
  \<^item> \<open>\<theta>\<close> satisfies the invariant \<^const>\<open>tinv\<close> of type unification for the type variables
    \<^const>\<open>ptvars\<close> of the problem (it is acyclic, its bindings are well-formed, and each type
    variable has a single sort and is not newer than \<open>maxidx env\<close>), and its bindings respect
    sorts (\<^const>\<open>tsorted\<close>);
  \<^item> \<open>env\<close> is acyclic (\<^const>\<open>nacyc\<close>), well-formed, typed by \<open>W\<close> modulo \<open>\<theta>\<close>, and fresh;
  \<^item> \<open>s\<close> and \<open>t\<close> are well-formed closed terms of the same type \<open>T\<close> modulo \<open>\<theta>\<close> whose variables
    are not newer than \<open>maxidx env\<close>.
  For an empty \<open>\<theta>\<close>, the normalization \<^const>\<open>tnormt\<close> is the identity (\<open>tnormt_empty\<close>).
\<close>

locale poly_problem = wf_algebra alg ar for alg :: algebra and ar :: "name \<Rightarrow> nat" +
  fixes W :: "indexname \<Rightarrow> ptyp" and env :: env and s t :: pterm and T :: ptyp
  assumes tinv: "tinv ar (maxidx env) (tyenv env) (ptvars env s t)"
    and tsorted: "tsorted alg (tyenv env)"
    and acyclic: "nacyc env"
    and wf_env: "\<And>x U u. vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> pwf_term ar 0 u \<and> wft ar U"
    and typed_env: "env_typed_mod (tyenv env) W env" and fresh: "fresh_env env"
    and wf_s: "pwf_term ar 0 s" and wf_t: "pwf_term ar 0 t"
    and typed_s: "has_type W [] (tnormt (tyenv env) s) T"
    and typed_t: "has_type W [] (tnormt (tyenv env) t) T"
    and below_s: "below (maxidx env) s" and below_t: "below (maxidx env) t"
begin

text \<open>The typing of the ground instance for \<open>\<rho>\<close>:\<close>

abbreviation W\<^sub>i :: "tinst \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "W\<^sub>i \<rho> \<equiv> \<lambda>x. tsubst \<rho> (W x)"

lemma instances: "gsol alg ar (tyenv env) \<rho> \<Longrightarrow> inst_ok ar (W\<^sub>i \<rho>) \<rho> [] s t env"
proof (rule inst_ok_typed[OF tinv_tacyc[OF tinv] tinv_tcons_env[OF tinv] _ _ _ wf_s typed_s wf_t typed_t
      wf_env typed_env fresh])
  show "\<forall>T\<in>tys s \<union> tys t \<union> etys env. tcons (tyenv env) T"
    by (auto intro!: tinv_tcons[OF tinv] simp: ptvars_def)
qed (simp_all add: gsol_def)

lemma pre: "pre alg ar (ptvars env s t) [] s t env"
proof -
  have "\<forall>T\<in>tys s \<union> tys t \<union> etys env. tyw ar (tyenv env) (ptvars env s t) T"
  proof
    fix U assume U: "U \<in> tys s \<union> tys t \<union> etys env"
    then have "wft ar U" using wf_s wf_t wf_env by (auto simp: pwf_term_def etys_def)
    with U show "tyw ar (tyenv env) (ptvars env s t) U" by (intro tyw_tvars) (auto simp: ptvars_def)
  qed
  then show ?thesis using tinv tsorted below_s below_t instances by (auto simp: pre_def)
qed

lemma post: "unify alg s t env = Some r \<Longrightarrow> post_all alg ar (ptvars env s t) [] s t env r"
  unfolding unify_def by (rule unif_post[OF _ refl pre])

lemma postok: "unify alg s t env = Some (Ok env') \<Longrightarrow> postok alg ar (ptvars env s t) [] s t env env'"
  using post by (simp add: post_all_def)

lemma tres: "unify alg s t env = Some r \<Longrightarrow> tres (ptvars env s t) env r"
  using unif_terminates[OF finite_ptvars pre acyclic] by (auto simp: unify_def)

text \<open>
  Some ground instance has a unifier: a solution of the instance of the environment that unifies
  the instances of \<open>s\<close> and \<open>t\<close>.
\<close>

abbreviation unifiable :: bool where
  "unifiable \<equiv> \<exists>\<rho> \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<and> solution (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env) \<and>
    unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"


subsection \<open>Termination\<close>

text \<open>\<^const>\<open>unify\<close> terminates; it returns an environment, fails, or gives up.\<close>

theorem terminates: "\<exists>r. unify alg s t env = Some r"
  using unif_terminates[OF finite_ptvars pre acyclic] unfolding unify_def by blast

theorem result:
  assumes "unify alg s t env = Some r"
  shows "(\<exists>env'. r = Ok env') \<or> (\<exists>u. r = Err (Unif u)) \<or> r = Err Pattern"
  using post[OF assms] by (cases r) (auto simp: post_all_def post_def fails_ok_def exn_ok_def)


subsection \<open>Successful unification\<close>

text \<open>
  A returned environment \<open>env'\<close> extends \<open>env\<close>, its type environment extends \<open>\<theta>\<close> and satisfies
  the invariants again, and \<open>env'\<close> is acyclic. Its ground instances satisfy the invariant of the
  monomorphic case, for a typing that agrees with the typing of the instance of the problem on
  the old variables.
\<close>

theorem Ok_inv:
  assumes un: "unify alg s t env = Some (Ok env')"
  shows "textends (tyenv env) (tyenv env')" "extends env' env" "maxidx env \<le> maxidx env'"
    and "tinv ar (maxidx env') (tyenv env') (ptvars env s t)" "tsorted alg (tyenv env')"
    and "nacyc env'"
    and "gsol alg ar (tyenv env') \<rho> \<Longrightarrow> \<exists>W'. env_inv ar W' (instE \<rho> env') \<and> agreeV (maxidx env) (W\<^sub>i \<rho>) W'"
proof -
  note p = postok[OF un, unfolded postok_def]
  show "textends (tyenv env) (tyenv env')" "extends env' env" "maxidx env \<le> maxidx env'"
    and "tinv ar (maxidx env') (tyenv env') (ptvars env s t)" "tsorted alg (tyenv env')"
    using p by simp_all
  show nac: "nacyc env'" using tres[OF un] by (simp add: tres_def)
  assume g': "gsol alg ar (tyenv env') \<rho>"
  have "gsol alg ar (tyenv env) \<rho>" using gsol_textends p g' by blast
  with p g' instances obtain W' where te: "ty_ext ar (W\<^sub>i \<rho>) (instE \<rho> env) W' (instE \<rho> env')"
    by blast
  with nac show "\<exists>W'. env_inv ar W' (instE \<rho> env') \<and> agreeV (maxidx env) (W\<^sub>i \<rho>) W'"
    using acyc_instE by (fastforce simp: ty_ext_def env_inv_def)
qed

text \<open>
  A returned environment \<open>env'\<close> is a most general unifier of all ground instances: the solutions
  of a ground instance of \<open>env'\<close> satisfy the corresponding instance of \<open>env\<close> and unify the
  instances of \<open>s\<close> and \<open>t\<close>, and every solution of a ground instance of \<open>env\<close> that unifies them
  extends (on the new variables) to a solution of a ground instance of \<open>env'\<close> (for a type
  instantiation that agrees on the old type variables).
\<close>

theorem Ok_sound:
  assumes un: "unify alg s t env = Some (Ok env')" and g': "gsol alg ar (tyenv env') \<rho>"
    and \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> (instE \<rho> env')"
  shows "gsol alg ar (tyenv env) \<rho>" and "sat \<sigma> (instE \<rho> env)"
    and "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
proof -
  note p = postok[OF un, unfolded postok_def]
  show "gsol alg ar (tyenv env) \<rho>" using gsol_textends p g' by blast
  show "sat \<sigma> (instE \<rho> env)" using sat_extends[OF \<sigma>(2) extends_instE] p by blast
  have "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" using p g' by blast
  from env_equivD[OF this \<sigma>] show "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    by (simp add: unifies_def)
qed

theorem Ok_most_general:
  assumes "unify alg s t env = Some (Ok env')" "gsol alg ar (tyenv env) \<rho>"
    "solution (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env)" "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
  shows "\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
    agreeV (maxidx env) (W\<^sub>i \<rho>) W' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution W' \<tau>' \<sigma>' (instE \<rho>' env')"
proof -
  obtain \<rho>' W' \<sigma>' where "gsol alg ar (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
    "sol_ext ar (W\<^sub>i \<rho>) \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env')"
    using postok[OF assms(1)] assms(2-) instances[OF assms(2)] unfolding postok_def by blast
  then show ?thesis by (auto simp: sol_ext_def)
qed

text \<open>Every acyclic environment has a solution, so the problem is unifiable.\<close>

theorem Ok_unifiable:
  assumes un: "unify alg s t env = Some (Ok env')"
  shows unifiable
proof -
  note inv = Ok_inv[OF un]
  obtain \<rho> where g': "gsol alg ar (tyenv env') \<rho>" using gsol_exists[OF inv(4,5)] .
  from inv(7)[OF g'] obtain W' where i: "env_inv ar W' (instE \<rho> env')"
    and agV: "agreeV (maxidx env) (W\<^sub>i \<rho>) W'" by blast
  note es = env_solution[OF env_invD(1-3)[OF i]]
  let ?\<sigma> = "env_sol (instE \<rho> env') W'"
  note snd = Ok_sound[OF un g' solutionD(1,4)[OF es(1)]]
  have rig: "\<forall>n\<in>range code. \<forall>m\<in>FV (?\<sigma> n). rigid_code m" using es(2) by blast
  define \<sigma>'' where "\<sigma>'' = (\<lambda>n. case atom_of n of
    AVar x \<Rightarrow> if n = code (AVar x) \<and> maxidx env < snd x then dB.Var (code (AFree STR '''' (W\<^sub>i \<rho> x)))
      else ?\<sigma> n
  | _ \<Rightarrow> ?\<sigma> n)"
  note rt = solution_retype[OF es(1) rig, of "maxidx env" "W\<^sub>i \<rho>", unfolded instE_simps, OF agV,
    folded \<sigma>''_def]
  have "sat \<sigma>'' (instE \<rho> env)"
    by (rule sat_agree[OF snd(2)]) (use instances[OF snd(1)] rt(4) in \<open>simp_all add: inst_ok_def\<close>)
  moreover have "unifies \<sigma>'' (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    using snd(3) mk_subst_agree[OF below_inst[THEN iffD2, OF below_s] rt(4)]
      mk_subst_agree[OF below_inst[THEN iffD2, OF below_t] rt(4)]
    by (simp add: unifies_def)
  ultimately show ?thesis using snd(1) rt(1-3) by (auto simp: solution_def)
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
