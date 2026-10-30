section \<open>Solutions of Acyclic Environments\<close>

theory Pattern_Solutions
  imports Pattern_Acyclic
begin

text \<open>
  Every acyclic, well-formed, well-typed environment has a solution: unbound variables are mapped
  to free variables (which are rigid) of the same type, bound variables to the solution of their
  binding. The solution is defined by well-founded recursion along the dependencies between the
  variables. Its values contain only rigid atoms, so it is well-typed for every typing of the free
  variables of the substitution.
\<close>

subsection \<open>Dependencies between variables\<close>

context csig
begin

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
  moreover have "wf (dep env)" by (rule wf_dep[OF assms(1)])
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


subsection \<open>Instances of acyclic environments\<close>

text \<open>
  \<open>env_map env g\<close> maps each variable to the instance of its binding, and unbound variables
  \<open>x\<close> to \<open>g x\<close>.
\<close>

definition map_step :: "env \<Rightarrow> (indexname \<Rightarrow> dB) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> nat \<Rightarrow> dB" where
  "map_step env g f n = (if n \<in> range code then
    (case atom_of n of
      AVar x \<Rightarrow> (case vt_lookup (tenv env) x of
        Some (U, u) \<Rightarrow> mk_subst (\<lambda>m. if rigid_code m then dB.Var m else f m) (tr u)
      | None \<Rightarrow> g x)
    | _ \<Rightarrow> dB.Var n)
    else dB.Var n)"

definition env_map :: "env \<Rightarrow> (indexname \<Rightarrow> dB) \<Rightarrow> nat \<Rightarrow> dB" where
  "env_map env g = wfrec (dcode env) (map_step env g)"

lemma adm_map_step: "adm_wf (dcode env) (map_step env g)"
  unfolding adm_wf_def
proof (intro allI impI)
  fix f h :: "nat \<Rightarrow> dB" and n
  assume eq: "\<forall>z. (z, n) \<in> dcode env \<longrightarrow> f z = h z"
  show "map_step env g f n = map_step env g h n"
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
          mk_subst (\<lambda>m. if rigid_code m then dB.Var m else h m) (tr u)"
        proof (rule mk_subst_cong)
          fix m assume "m \<in> FV (tr u)"
          from FV_tr[OF this] consider "rigid_code m" | y where "y \<in> vars u" "m = code (AVar y)"
            by blast
          then show "(if rigid_code m then dB.Var m else f m) = (if rigid_code m then dB.Var m else h m)"
          proof cases
            case 2
            from Some b have "vt_lookup (tenv env) x = Some (U, u)" by simp
            from dvarI[OF this 2(1)] have "(m, n) \<in> dcode env" unfolding dcode_def n AVar 2(2) by blast
            with eq show ?thesis by simp
          qed simp
        qed
        with Some b n AVar show ?thesis by (simp add: map_step_def)
      qed (simp add: map_step_def n AVar)
    qed (simp_all add: map_step_def n)
  qed (simp add: map_step_def)
qed

context
  fixes env W
  assumes ac: "acyc env" and ety: "env_typed W env"
begin

lemma env_map_eq: "env_map env g n = map_step env g (env_map env g) n"
  unfolding env_map_def by (subst wfrec_fixpoint[OF wf_dcode[OF ac ety] adm_map_step]) (rule refl)

lemma env_map_rigid: "rigid_code n \<Longrightarrow> env_map env g n = dB.Var n"
  by (auto simp: env_map_eq map_step_def rigid_code_def)

lemma env_map_guard: "(\<lambda>m. if rigid_code m then dB.Var m else env_map env g m) = env_map env g"
  using env_map_rigid by auto

lemma env_map_bound:
  "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> env_map env g (code (AVar x)) = mk_subst (env_map env g) (tr u)"
  by (simp add: env_map_eq[of g "code (AVar x)"] map_step_def env_map_guard)

lemma env_map_unbound: "vt_lookup (tenv env) x = None \<Longrightarrow> env_map env g (code (AVar x)) = g x"
  by (simp add: env_map_eq[of g "code (AVar x)"] map_step_def)

lemma env_map_noncode: "n \<notin> range code \<Longrightarrow> env_map env g n = dB.Var n"
  by (simp add: env_map_eq map_step_def)

lemma env_map_props:
  assumes wf: "wf_env ar env"
    and g: "\<And>x. no_loose_bound (g x) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> g x : trty (W x))"
  shows "no_loose_bound (env_map env g (code (AVar x))) 0 \<and>
    (\<forall>e. (e, tau W) \<turnstile> env_map env g (code (AVar x)) : trty (W x)) \<and>
    (\<forall>m\<in>FV (env_map env g (code (AVar x))). rigid_code m \<or>
      (\<exists>y. vt_lookup (tenv env) y = None \<and> m \<in> FV (g y)))"
proof (induction x rule: wf_induct_rule[OF wf_dvar[OF ac ety]])
  case (1 x)
  let ?\<sigma> = "env_map env g"
  have var: "no_loose_bound (?\<sigma> m) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> ?\<sigma> m : tau W m) \<and>
      (\<forall>k\<in>FV (?\<sigma> m). rigid_code k \<or> (\<exists>y. vt_lookup (tenv env) y = None \<and> k \<in> FV (g y)))"
    if "m \<in> FV (tr u)" "vt_lookup (tenv env) x = Some (U, u)" for m U u
  proof -
    from FV_tr[OF that(1)] consider "rigid_code m" | y where "y \<in> vars u" "m = code (AVar y)"
      by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by (auto simp: env_map_rigid)
    next
      case 2
      with that(2) have "(y, x) \<in> dvar env" by (auto intro: dvarI)
      with "1.IH" 2 show ?thesis by simp
    qed
  qed
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case None
    show ?thesis using g[of x] None unfolding env_map_unbound[OF None] by blast
  next
    case (Some b)
    obtain U u where lk: "vt_lookup (tenv env) x = Some (U, u)" using Some by (cases b) auto
    note eq = env_map_bound[OF lk]
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
    moreover have "\<forall>m\<in>FV (?\<sigma> (code (AVar x))). rigid_code m \<or>
        (\<exists>y. vt_lookup (tenv env) y = None \<and> m \<in> FV (g y))"
      unfolding eq FV_mk_subst using var[OF _ lk] by blast
    ultimately show ?thesis by blast
  qed
qed

lemma env_map_split:
  "(\<exists>x. n = code (AVar x)) \<or> (rigid_code n \<and> env_map env g n = dB.Var n) \<or>
    (n \<notin> range code \<and> env_map env g n = dB.Var n)"
proof (cases "n \<in> range code")
  case True
  then obtain a where n: "n = code a" by blast
  then show ?thesis by (cases a) (auto simp: env_map_rigid)
qed (simp add: env_map_noncode)

lemma env_map_closed:
  assumes "wf_env ar env" "\<And>x. no_loose_bound (g x) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> g x : trty (W x))"
  shows "closed_on UNIV (env_map env g)"
  unfolding closed_on_def
proof
  fix n show "no_loose_bound (env_map env g n) 0"
    using env_map_split[of n g] env_map_props[OF assms] by auto
qed

lemma env_map_typed:
  assumes "wf_env ar env" "\<And>x. no_loose_bound (g x) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> g x : trty (W x))"
  shows "typed_on (range code) (tau W) (tau W) (env_map env g)"
  unfolding typed_on_def
proof (intro ballI allI)
  fix n e assume "n \<in> range code"
  then obtain a where n: "n = code a" by blast
  show "(e, tau W) \<turnstile> env_map env g n : tau W n"
    by (cases a) (use env_map_props[OF assms] in \<open>auto simp: n env_map_rigid\<close>)
qed

lemma env_map_sat: "sat (env_map env g) env"
  by (auto simp: sat_def env_map_bound)

lemma env_map_rigid_subst: "rigid_subst (env_map env g)"
  by (simp add: rigid_subst_def env_map_rigid)

end


subsection \<open>The canonical solution\<close>

definition env_sol :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> nat \<Rightarrow> dB" where
  "env_sol env W = env_map env (\<lambda>x. dB.Var (code (AFree STR '''' (W x))))"

theorem env_solution:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
  shows "solution W (tau W) (env_sol env W) env"
    and "\<And>n m. n \<in> range code \<Longrightarrow> m \<in> FV (env_sol env W n) \<Longrightarrow> rigid_code m"
proof -
  let ?g = "\<lambda>x. dB.Var (code (AFree STR '''' (W x)))"
  have g: "no_loose_bound (?g x) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> ?g x : trty (W x))" for x by auto
  show "rigid_code m" if "n \<in> range code" "m \<in> FV (env_sol env W n)" for n m
  proof -
    from env_map_split[OF ac ety, of n ?g] that(1) consider x where "n = code (AVar x)"
      | "rigid_code n" "env_map env ?g n = dB.Var n" by blast
    then show ?thesis
    proof cases
      case 1
      from env_map_props[OF ac ety wf g, of x] that(2) 1 obtain y where
        "rigid_code m \<or> m \<in> FV (?g y)" by (auto simp: env_sol_def)
      then show ?thesis by auto
    qed (use that(2) in \<open>simp add: env_sol_def\<close>)
  qed
  show "solution W (tau W) (env_sol env W) env"
    unfolding solution_def env_sol_def
    using env_map_closed[OF ac ety wf g] env_map_typed[OF ac ety wf g] env_map_rigid_subst[OF ac ety]
      env_map_sat[OF ac ety] by blast
qed

text \<open>
  A solution whose values contain only rigid atoms can be retyped: new variables (beyond \<open>k\<close>) are
  mapped to free variables of the type given by the old typing.
\<close>

lemma solution_retype:
  assumes sol: "solution V' (tau V') \<sigma> env'" and rig: "\<forall>n\<in>range code. \<forall>m\<in>FV (\<sigma> n). rigid_code m"
    and ag: "agreeV k V V'"
  defines "\<sigma>'' \<equiv> \<lambda>n. case atom_of n of
    AVar x \<Rightarrow> if n = code (AVar x) \<and> k < snd x then dB.Var (code (AFree STR '''' (V x))) else \<sigma> n
  | _ \<Rightarrow> \<sigma> n"
  shows "closed_on UNIV \<sigma>''" "typed_on (range code) (tau V) (tau V) \<sigma>''" "rigid_subst \<sigma>''"
    "agree k \<sigma> \<sigma>''"
proof -
  note s = solutionD[OF sol]
  show "closed_on UNIV \<sigma>''"
    unfolding closed_on_def
  proof
    fix n show "no_loose_bound (\<sigma>'' n) 0"
      using closed_onD[OF s(1)] by (auto simp: \<sigma>''_def split: atom.splits)
  qed
  show "rigid_subst \<sigma>''"
    using s(3) by (auto simp: rigid_subst_def rigid_code_def \<sigma>''_def)
  show "agree k \<sigma> \<sigma>''"
    by (auto simp: agree_def \<sigma>''_def split: atom.splits if_splits)
  show "typed_on (range code) (tau V) (tau V) \<sigma>''"
    unfolding typed_on_def
  proof (intro ballI allI)
    fix n e assume "n \<in> range code"
    then obtain a where n: "n = code a" by blast
    have retype: "(e, tau V) \<turnstile> \<sigma> n : U" if "(e, tau V') \<turnstile> \<sigma> n : U" for U
    proof (rule typing_free_cong[OF that])
      fix F assume "F \<in> FV (\<sigma> n)"
      from rig \<open>n \<in> range code\<close> this have "rigid_code F" by blast
      then show "tau V' F = tau V F" by (auto simp: rigid_code_def)
    qed
    show "(e, tau V) \<turnstile> \<sigma>'' n : tau V n"
    proof (cases a)
      case (AVar x)
      show ?thesis
      proof (cases "k < snd x")
        case False
        with ag have "V' x = V x" by (cases x) (simp add: agreeV_def)
        with typed_onD[OF s(2) \<open>n \<in> range code\<close>, of e] retype False show ?thesis
          by (simp add: \<sigma>''_def n AVar)
      qed (auto simp: \<sigma>''_def n AVar)
    qed (use rigid_substD[OF s(3)] in \<open>auto simp: \<sigma>''_def n\<close>)
  qed
qed

end

end
