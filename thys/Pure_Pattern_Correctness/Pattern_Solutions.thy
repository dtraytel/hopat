section \<open>Solutions of Acyclic Environments\<close>

theory Pattern_Solutions
  imports Pattern_Termination
begin

text \<open>
  Every acyclic, well-formed, well-typed environment has a solution: unbound variables are mapped
  to free variables (which are rigid) of the same type, bound variables to the solution of their
  binding. The solution is defined by well-founded recursion along the dependencies between the
  variables. Its values contain only rigid atoms, so it is well-typed for every typing of the free
  variables of the substitution.
\<close>

subsection \<open>Dependencies between variables\<close>

lemma vps_typed: "has_type W Ts u U \<Longrightarrow> y \<in> vars u \<Longrightarrow> (y, W y) \<in> vps u"
  by (induction rule: has_type.induct) auto

definition dvar :: "env \<Rightarrow> (indexname \<times> indexname) set" where
  "dvar env = {(y, x). \<exists>U u. vt_lookup (tenv env) x = Some (U, u) \<and> y \<in> vars u}"

lemma dvarI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> y \<in> vars u \<Longrightarrow> (y, x) \<in> dvar env"
  by (auto simp: dvar_def)

lemma wf_dvar:
  assumes "acyc env" "env_typed W env"
  shows "wf (dvar env)"
proof -
  have "dvar env \<subseteq> inv_image (dep env) (\<lambda>y. (y, W y))"
  proof
    fix p assume "p \<in> dvar env"
    then obtain y x U u where p: "p = (y, x)" "vt_lookup (tenv env) x = Some (U, u)" "y \<in> vars u"
      by (auto simp: dvar_def)
    from env_typedD[OF assms(2) p(2)] have "W x = U" "has_type W [] u U" by auto
    with p show "p \<in> inv_image (dep env) (\<lambda>y. (y, W y))"
      by (auto simp: dep_iff lk_def vps_typed)
  qed
  moreover have "wf (dep env)" by (rule wf_dep[OF fin_env assms(1)])
  ultimately show ?thesis by (meson wf_inv_image wf_subset)
qed

definition dcode :: "env \<Rightarrow> (nat \<times> nat) set" where
  "dcode env = {(code (AVar y), code (AVar x)) | y x. (y, x) \<in> dvar env}"

lemma wf_dcode:
  assumes "acyc env" "env_typed W env"
  shows "wf (dcode env)"
proof -
  let ?f = "\<lambda>n. case atom_of n of AVar x \<Rightarrow> x | _ \<Rightarrow> undefined"
  have "dcode env \<subseteq> inv_image (dvar env) ?f" by (auto simp: dcode_def)
  with wf_dvar[OF assms] show ?thesis by (meson wf_inv_image wf_subset)
qed


subsection \<open>The canonical solution\<close>

definition sol_step :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> nat \<Rightarrow> dB" where
  "sol_step env W f n = (if n \<in> range code then
    (case atom_of n of
      AVar x \<Rightarrow> (case vt_lookup (tenv env) x of
        Some (U, u) \<Rightarrow> mk_subst (\<lambda>m. if rigid_code m then dB.Var m else f m) (tr u)
      | None \<Rightarrow> dB.Var (code (AFree STR '''' (W x))))
    | _ \<Rightarrow> dB.Var n)
    else dB.Var n)"

definition env_sol :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> nat \<Rightarrow> dB" where
  "env_sol env W = wfrec (dcode env) (sol_step env W)"

lemma adm_sol_step: "adm_wf (dcode env) (sol_step env W)"
  unfolding adm_wf_def
proof (intro allI impI)
  fix f g :: "nat \<Rightarrow> dB" and n
  assume eq: "\<forall>z. (z, n) \<in> dcode env \<longrightarrow> f z = g z"
  show "sol_step env W f n = sol_step env W g n"
  proof (cases "n \<in> range code")
    case True
    then obtain a where n: "n = code a" by blast
    show ?thesis
    proof (cases a)
      case (AVar x)
      show ?thesis
      proof (cases "vt_lookup (tenv env) x")
        case (Some b)
        obtain U u where b: "b = (U, u)" by force
        have "mk_subst (\<lambda>m. if rigid_code m then dB.Var m else f m) (tr u) =
          mk_subst (\<lambda>m. if rigid_code m then dB.Var m else g m) (tr u)"
        proof (rule mk_subst_cong)
          fix m assume "m \<in> FV (tr u)"
          from FV_tr[OF this] consider "rigid_code m" | y where "y \<in> vars u" "m = code (AVar y)"
            by blast
          then show "(if rigid_code m then dB.Var m else f m) = (if rigid_code m then dB.Var m else g m)"
          proof cases
            case 2
            from Some b have "vt_lookup (tenv env) x = Some (U, u)" by simp
            from dvarI[OF this 2(1)] have "(m, n) \<in> dcode env" unfolding dcode_def n AVar 2(2) by blast
            with eq show ?thesis by simp
          qed simp
        qed
        with Some b n AVar show ?thesis by (simp add: sol_step_def)
      qed (simp add: sol_step_def n AVar)
    qed (simp_all add: sol_step_def n)
  qed (simp add: sol_step_def)
qed

lemma env_sol_eq:
  assumes "acyc env" "env_typed W env"
  shows "env_sol env W n = sol_step env W (env_sol env W) n"
  unfolding env_sol_def by (subst wfrec_fixpoint[OF wf_dcode[OF assms] adm_sol_step]) (rule refl)

lemma env_sol_rigid:
  assumes "acyc env" "env_typed W env" "rigid_code n"
  shows "env_sol env W n = dB.Var n"
  using assms(3) by (auto simp: env_sol_eq[OF assms(1,2)] sol_step_def rigid_code_def)

lemma env_sol_guard:
  assumes "acyc env" "env_typed W env"
  shows "(\<lambda>m. if rigid_code m then dB.Var m else env_sol env W m) = env_sol env W"
  using env_sol_rigid[OF assms] by auto

lemma env_sol_bound:
  assumes "acyc env" "env_typed W env" "vt_lookup (tenv env) x = Some (U, u)"
  shows "env_sol env W (code (AVar x)) = mk_subst (env_sol env W) (tr u)"
  using assms(3) by (simp add: env_sol_eq[OF assms(1,2), of "code (AVar x)"] sol_step_def env_sol_guard[OF assms(1,2)])

lemma env_sol_unbound:
  assumes "acyc env" "env_typed W env" "vt_lookup (tenv env) x = None"
  shows "env_sol env W (code (AVar x)) = dB.Var (code (AFree STR '''' (W x)))"
  using assms(3) by (simp add: env_sol_eq[OF assms(1,2), of "code (AVar x)"] sol_step_def)

lemma env_sol_noncode:
  assumes "acyc env" "env_typed W env" "n \<notin> range code"
  shows "env_sol env W n = dB.Var n"
  using assms(3) by (simp add: env_sol_eq[OF assms(1,2)] sol_step_def)

lemma env_sol_props:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
  shows "no_loose_bound (env_sol env W (code (AVar x))) 0 \<and>
    (\<forall>e. (e, tau W) \<turnstile> env_sol env W (code (AVar x)) : trty (W x)) \<and>
    (\<forall>m\<in>FV (env_sol env W (code (AVar x))). rigid_code m)"
proof (induction x rule: wf_induct_rule[OF wf_dvar[OF ac ety]])
  case (1 x)
  let ?\<sigma> = "env_sol env W"
  have var: "no_loose_bound (?\<sigma> m) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> ?\<sigma> m : tau W m) \<and> (\<forall>k\<in>FV (?\<sigma> m). rigid_code k)"
    if "m \<in> FV (tr u)" "vt_lookup (tenv env) x = Some (U, u)" for m U u
  proof -
    from FV_tr[OF that(1)] consider "rigid_code m" | y where "y \<in> vars u" "m = code (AVar y)"
      by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by (auto simp: env_sol_rigid[OF ac ety])
    next
      case 2
      with that(2) have "(y, x) \<in> dvar env" by (auto intro: dvarI)
      with "1.IH" 2 show ?thesis by simp
    qed
  qed
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case None
    then show ?thesis by (auto simp: env_sol_unbound[OF ac ety])
  next
    case (Some b)
    obtain U u where lk: "vt_lookup (tenv env) x = Some (U, u)" using Some by (cases b) auto
    note eq = env_sol_bound[OF ac ety lk]
    from env_typedD[OF ety lk] have WU: "W x = U" and tyu: "has_type W [] u U" by auto
    have nlb: "no_loose_bound (tr u) 0" using wf_envD(2)[OF wf lk] by simp
    have "no_loose_bound (?\<sigma> (code (AVar x))) 0"
      unfolding eq by (rule mk_subst_no_loose_bound[OF nlb]) (auto simp: closed_on_def dest: var[OF _ lk])
    moreover have "(e, tau W) \<turnstile> ?\<sigma> (code (AVar x)) : trty (W x)" for e
    proof -
      have "(bnd_env [], tau W) \<turnstile> mk_subst ?\<sigma> (tr u) : trty U"
        by (rule typing_mk_subst[OF has_type_tr[OF tyu]]) (auto simp: typed_on_def dest: var[OF _ lk])
      with calculation show ?thesis by (simp add: eq WU typing_closed)
    qed
    moreover have "\<forall>m\<in>FV (?\<sigma> (code (AVar x))). rigid_code m"
      unfolding eq FV_mk_subst using var[OF _ lk] by blast
    ultimately show ?thesis by blast
  qed
qed

theorem env_solution:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
  shows "solution W (tau W) (env_sol env W) env"
    and "\<And>n m. n \<in> range code \<Longrightarrow> m \<in> FV (env_sol env W n) \<Longrightarrow> rigid_code m"
proof -
  let ?\<sigma> = "env_sol env W"
  have split: "(\<exists>x. n = code (AVar x)) \<or> (rigid_code n \<and> ?\<sigma> n = dB.Var n) \<or>
    (n \<notin> range code \<and> ?\<sigma> n = dB.Var n)" for n
  proof (cases "n \<in> range code")
    case True
    then obtain a where n: "n = code a" by blast
    then show ?thesis by (cases a) (auto simp: env_sol_rigid[OF ac ety])
  qed (simp add: env_sol_noncode[OF ac ety])
  show "rigid_code m" if "n \<in> range code" "m \<in> FV (?\<sigma> n)" for n m
    using split[of n] that env_sol_props[OF ac wf ety] by auto
  have "closed_on UNIV ?\<sigma>"
    unfolding closed_on_def
  proof
    fix n show "no_loose_bound (?\<sigma> n) 0" using split[of n] env_sol_props[OF ac wf ety] by auto
  qed
  moreover have "typed_on (range code) (tau W) (tau W) ?\<sigma>"
    unfolding typed_on_def
  proof (intro ballI allI)
    fix n e assume "n \<in> range code"
    then obtain a where n: "n = code a" by blast
    show "(e, tau W) \<turnstile> ?\<sigma> n : tau W n"
      by (cases a) (use env_sol_props[OF ac wf ety] in \<open>auto simp: n env_sol_rigid[OF ac ety]\<close>)
  qed
  moreover have "rigid_subst ?\<sigma>" by (simp add: rigid_subst_def env_sol_rigid[OF ac ety])
  moreover have "sat ?\<sigma> env" by (auto simp: sat_def env_sol_bound[OF ac ety])
  ultimately show "solution W (tau W) ?\<sigma> env" by (simp add: solution_def)
qed

end
