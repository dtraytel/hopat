section \<open>Normalization and Instances\<close>

theory Bicompose_Norm
  imports Bicompose_Seq
begin

text \<open>
  The new theorem of \<open>bicompose_aux\<close> is normalized by the environment of a unifier, but only
  as much as needed (\<^const>\<open>addth\<close>). An instance \<open>(\<rho>, \<sigma>)\<close> of the new theorem, a ground
  well-sorted type instantiation and a closed substitution, is extended to an instance
  \<open>(\<rho>', \<sigma>')\<close> that solves the environment and agrees with \<open>(\<rho>, \<sigma>)\<close> on the variables that the
  environment does not bind. Normalized terms contain only such variables, so their
  \<open>(\<rho>, \<sigma>)\<close>-instance is equivalent to the \<open>(\<rho>', \<sigma>')\<close>-instance of the original term.
\<close>

subsection \<open>Unbound variables\<close>

definition unb :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "unb env t \<longleftrightarrow> (\<forall>x\<in>vars t. vt_lookup (tenv env) x = None) \<and>
    (\<forall>T\<in>tys t. \<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"

lemma unb_simps[simp]:
  "unb env (Const a T) \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"
  "unb env (Free a T) \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"
  "unb env (Var x T) \<longleftrightarrow> vt_lookup (tenv env) x = None \<and> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None)"
  "unb env (Bound i)"
  "unb env (Abs a T t) \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. vt_lookup (tyenv env) v = None) \<and> unb env t"
  "unb env (s $ t) \<longleftrightarrow> unb env s \<and> unb env t"
  by (auto simp: unb_def)

lemma unb_empty: "env_is_empty env \<Longrightarrow> unb env t"
  by (simp add: unb_def env_is_empty_def vt_is_empty_lookup)

lemma ok_type_lookup_None: "ok (type_lookup \<theta> v S) None \<Longrightarrow> vt_lookup \<theta> v = None"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)

lemma norm_type_aux_unb:
  assumes "norm_type_aux \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> (v, S) \<in> tvars T' \<Longrightarrow> vt_lookup \<theta> v = None"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  note n = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vt_lookup \<theta> v = None" if "nt \<theta> U = Some (Ok U')" "(v, S) \<in> tvars U'" for U U'
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases T)
    case (Type a Ts)
    with n obtain Ts' where l2: "list_all2 (\<lambda>x y. ok (nt \<theta> x) y) Ts Ts'" and T': "T' = Type a Ts'"
      by (auto simp: ok_mapM)
    from "1.prems"(2) T' obtain U' where "U' \<in> set Ts'" "(v, S) \<in> tvars U'" by auto
    moreover from l2 \<open>U' \<in> set Ts'\<close> obtain U where "ok (nt \<theta> U) U'"
      by (induction rule: list_all2_induct) auto
    ultimately show ?thesis using IH by blast
  next
    case (TVar w S')
    with n obtain r' where lk: "ok (type_lookup \<theta> w S') r'"
      and rest: "ok (case r' of Some U \<Rightarrow> nt \<theta> U | None \<Rightarrow> return T) T'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with lk rest TVar "1.prems"(2) show ?thesis by (auto dest: ok_type_lookup_None)
    next
      case (Some U)
      with rest have "ok (nt \<theta> U) T'" by simp
      from this "1.prems"(2) show ?thesis by (rule IH)
    qed
  qed (use n "1.prems"(2) in auto)
qed

lemma ok_norm_type_aux_unb: "ok (norm_type_aux \<theta> T) T' \<Longrightarrow> \<forall>(v, S)\<in>tvars T'. vt_lookup \<theta> v = None"
  using norm_type_aux_unb by blast

lemma norm_type_unb: "ok (norm_type \<theta> T) T' \<Longrightarrow> (v, S) \<in> tvars T' \<Longrightarrow> vt_lookup \<theta> v = None"
  using ok_norm_type_aux_unb[of \<theta> T T'] by (auto simp: norm_type_def vt_is_empty_lookup split: if_splits)

lemma norm_term2_unb:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> unb env t'"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note t' = "1.hyps"[unfolded "1.prems"]
  have IH: "unb env s'" if "nt env s = Some (Ok s')" for s s'
    using "1.IH"[OF that refl] .
  note nta = ok_norm_type_aux_unb[of "tyenv env"]
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (Var xi T'))) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with lk rest nta show ?thesis by (auto dest: ok_lookup_None)
    next
      case (Some u)
      with rest IH show ?thesis by simp
    qed
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      with t' App IH show ?thesis by (cases f) auto
    next
      case False
      with t' App obtain nf where nf: "nt env f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      with IH IH[OF nf] show ?thesis by (cases nf) auto
    qed
  qed (use t' IH nta in auto)
qed

lemma norm_term1_unb:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> unb env t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note t' = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "unb env s'" if "nt te s = Some (Ok s')" for s s'
    using "1.IH"[OF that refl "1.prems"(2,3)] .
  have ty: "vt_lookup (tyenv env) v = None" for v
    using "1.prems"(3) by (rule vt_is_empty_lookup)
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup1 te xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with lk rest Var ty "1.prems"(2) show ?thesis by (auto dest: ok_lookup1_None)
    next
      case (Some u)
      with rest IH show ?thesis by simp
    qed
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      with t' App IH show ?thesis by (cases f) auto
    next
      case False
      with t' App obtain nf where nf: "nt te f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      with IH IH[OF nf] show ?thesis by (cases nf) auto
    qed
  qed (use t' IH ty in auto)
qed

lemma norm_term_unb: "ok (norm_term env t) t' \<Longrightarrow> unb env t'"
  using norm_term1_unb[of "tenv env" t "Ok t'" t' env] norm_term2_unb[of env t "Ok t'" t'] unb_empty[of env t]
  by (auto simp: norm_term_def split: if_splits)

text \<open>All variables of a term have an index of at most \<open>m\<close>.\<close>

definition ibelow :: "integer \<Rightarrow> pterm \<Rightarrow> bool" where
  "ibelow m t \<longleftrightarrow> (\<forall>x\<in>vars t. snd x \<le> m) \<and> (\<forall>T\<in>tys t. \<forall>(v, S)\<in>tvars T. snd v \<le> m)"

lemma vt_above_lookup: "vt_above tab m \<Longrightarrow> snd x \<le> m \<Longrightarrow> vt_lookup tab x = None"
  by transfer force

lemma above_unb: "above env m \<Longrightarrow> ibelow m t \<Longrightarrow> unb env t"
  by (fastforce simp: above_def ibelow_def unb_def intro: vt_above_lookup)


subsection \<open>Extending instances\<close>

context wf_algebra
begin

text \<open>Ground well-sorted type instantiations.\<close>

definition gtinst :: "tinst \<Rightarrow> bool" where
  "gtinst \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> (\<forall>v S. ground ar (\<rho> v S))"

text \<open>
  \<open>(\<rho>', \<sigma>')\<close> extends \<open>(\<rho>, \<sigma>)\<close> by the environment \<open>env\<close>: \<open>\<rho>'\<close> is a ground well-sorted solution
  of the type environment, \<open>\<sigma>'\<close> is closed and rigid and, after renaming the constants by
  \<open>\<rho>'\<close>, solves the environment; both agree with \<open>(\<rho>, \<sigma>)\<close> on unbound variables.
\<close>

definition iext :: "env \<Rightarrow> tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longleftrightarrow> gsol alg ar (tyenv env) \<rho>' \<and>
    (\<forall>v S. vt_lookup (tyenv env) v = None \<longrightarrow> \<rho>' v S = \<rho> v S) \<and>
    closed_on UNIV \<sigma>' \<and> rigid_subst \<sigma>' \<and> psat (\<sigma>' \<circ> cren \<rho>') env \<and>
    (\<forall>x. vt_lookup (tenv env) x = None \<longrightarrow> \<sigma>' (code (AVar x)) = \<sigma> (code (AVar x)))"

lemma iext_exists:
  assumes "penv_inv alg ar W env" "gtinst \<rho>" "closed_on UNIV \<sigma>" "rigid_subst \<sigma>"
  obtains \<rho>' \<sigma>' where "iext env \<rho> \<sigma> \<rho>' \<sigma>'"
proof -
  note i = penv_invD[OF assms(1)]
  from assms(2) have ws: "has_sort alg (\<rho> v S) S" and gr: "ground ar (\<rho> v S)" for v S
    unfolding gtinst_def wsinst_def by blast+
  obtain \<rho>' where g: "gsol alg ar (tyenv env) \<rho>'"
    and "\<And>T. tcons (tyenv env) T \<Longrightarrow> tsubst \<rho>' T = tsubst \<rho> (tnorm (tyenv env) T)"
    and agT: "\<And>v S. vt_lookup (tyenv env) v = None \<Longrightarrow> \<rho>' v S = \<rho> v S"
    by (fact tsol_exists_gen[where \<eta> = \<rho>, OF i(1,2) ws gr])
  let ?E = "instE \<rho>' env"
  note ei = env_invD[OF penv_inv_inst[OF assms(1) g]]
  let ?\<theta> = "env_inst ?E"
  define \<sigma>' where "\<sigma>' = \<sigma> \<circ>\<^sub>s ?\<theta>"
  have cl: "closed_on UNIV \<sigma>'"
    unfolding \<sigma>'_def using inst_closed[OF ei(1-3)] assms(3)
    by (auto intro: closed_on_comp closed_on_mono)
  have rig: "rigid_subst \<sigma>'"
    using assms(4) by (simp add: rigid_subst_def \<sigma>'_def inst_rigid[OF ei(1-3)])
  have unb: "\<sigma>' (code (AVar x)) = \<sigma> (code (AVar x))" if "vt_lookup (tenv env) x = None" for x
    using that by (simp add: \<sigma>'_def inst_unbound[OF ei(1-3)])
  have "sat \<sigma>' ?E"
    by (auto simp: sat_def \<sigma>'_def inst_bound[OF ei(1-3)])
  then have "psat (\<sigma>' \<circ> cren \<rho>') env"
    using g cl by (intro psat_instE) (simp_all add: gsol_def)
  with g agT cl rig unb have "iext env \<rho> \<sigma> \<rho>' \<sigma>'"
    by (simp add: iext_def)
  then show ?thesis by (rule that)
qed

lemma gtinst_gsol: "gsol alg ar \<theta> \<rho> \<Longrightarrow> gtinst \<rho>"
  by (simp add: gsol_def gtinst_def)

lemma iext_unb:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "unb env t"
  shows "sm \<rho>' \<sigma>' t = sm \<rho> \<sigma> t"
proof -
  from assms(1) have agT: "\<And>v S. vt_lookup (tyenv env) v = None \<Longrightarrow> \<rho>' v S = \<rho> v S"
    and rig: "rigid_subst \<sigma>'"
    and agV: "\<And>x. vt_lookup (tenv env) x = None \<Longrightarrow> \<sigma>' (code (AVar x)) = \<sigma> (code (AVar x))"
    unfolding iext_def by blast+
  have "inst \<rho>' t = inst \<rho> t"
  proof (rule inst_tagree, intro ballI)
    fix T assume "T \<in> tys t"
    with assms(3) show "tsubst \<rho>' T = tsubst \<rho> T"
      by (fastforce simp: unb_def intro!: tsubst_cong agT)
  qed
  moreover have "mk_subst \<sigma>' (tr (inst \<rho> t)) = mk_subst \<sigma> (tr (inst \<rho> t))"
  proof (rule mk_subst_cong)
    fix F assume "F \<in> FV (tr (inst \<rho> t))"
    then consider "rigid_code F" | x where "x \<in> vars t" "F = code (AVar x)"
      using FV_tr by fastforce
    then show "\<sigma>' F = \<sigma> F"
    proof cases
      case 1
      then show ?thesis by (simp add: rigid_substD[OF rig] rigid_substD[OF assms(2)])
    next
      case 2
      with assms(3) show ?thesis by (simp add: unb_def agV)
    qed
  qed
  ultimately show ?thesis by (simp add: sm_def)
qed

lemma iext_norm_term:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "swf_env ar env" "swf_tm ar rb t"
    "ok (norm_term env t) t'"
  shows "sm \<rho> \<sigma> t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
proof -
  have "env \<Turnstile>\<^sub>p t \<approx> t'" using norm_term_swf_tm[OF assms(5,3,4)] by simp
  moreover have "psat (\<sigma>' \<circ> cren \<rho>') env" using assms(1) by (simp add: iext_def)
  ultimately have "mk_subst (\<sigma>' \<circ> cren \<rho>') (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma>' \<circ> cren \<rho>') (tr t')"
    by (rule penv_equivD)
  then have "sm \<rho>' \<sigma>' t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
    by (simp add: sm_def mk_subst_inst equiv_sym)
  moreover have "sm \<rho>' \<sigma>' t' = sm \<rho> \<sigma> t'"
    using iext_unb[OF assms(1,2) norm_term_unb[OF assms(5)]] .
  ultimately show ?thesis by simp
qed

end


subsection \<open>Skipping lifted assumptions\<close>

text \<open>The assumptions that \<^const>\<open>norm_term_skip\<close> skips are unbound.\<close>

function skip_unb :: "env \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> bool" where
  "skip_unb env n t \<longleftrightarrow>
    n = 0 \<or>
    (case dest_all t of
      Some (a, T, b) \<Rightarrow> skip_unb env n b
    | None \<Rightarrow> (case dest_imp t of Some (A, B) \<Rightarrow> unb env A \<and> skip_unb env (n - 1) B | None \<Rightarrow> True))"
  by auto
termination by (relation "measure (\<lambda>(_, _, t). size t)") (auto dest: dest_size)

declare skip_unb.simps[simp del]

lemma ok_norm_type_wft: "ok (norm_type \<theta> T) T' \<Longrightarrow> twf ar \<theta> \<Longrightarrow> wft ar T \<Longrightarrow> wft ar T'"
  by (auto simp: norm_type_def split: if_splits dest: ok_norm_type_aux(2))

lemma ok_norm_type_tsol: "ok (norm_type \<theta> T) T' \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T' = tsubst \<rho> T"
  by (auto simp: norm_type_def split: if_splits dest: ok_norm_type_aux(1))

lemma wft_all_type: "wft ar (all_type T) \<Longrightarrow> wft ar T' \<Longrightarrow> wft ar (all_type T')"
  by (simp add: all_type_def)

lemma swf_tm_Abs: "swf_tm ar rb (Abs a T b) \<longleftrightarrow> wft ar T \<and> swf_tm ar ((a, T) # rb) b"
  by (auto simp: swf_tm_def)

lemma norm_term_skip_swf:
  "okT (norm_term_skip env n t) t' \<Longrightarrow> swf_env ar env \<Longrightarrow> swf_tm ar rb t \<Longrightarrow> cok t \<Longrightarrow> swf_tm ar rb t'"
proof (induction env n t arbitrary: rb t' rule: norm_term_skip.induct)
  case (1 env n t)
  show ?case
  proof (cases "n = 0")
    case True
    with "1.prems"(1-3) show ?thesis by (auto simp: norm_term_skip.simps dest: norm_term_swf_tm)
  next
    case n: False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases x) auto
      from cok_dest_all[OF "1.prems"(4) aTb] have t: "t = all_const T $ Abs a T b" and "cok b"
        by auto
      from "1.prems"(1) n aTb obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from "1.prems"(3) t have wf: "wft ar (all_type T)" "wft ar T" "swf_tm ar ((a, T) # rb) b"
        by (simp_all add: swf_tm_App swf_tm_Abs) (simp add: swf_tm_def all_const_all_type)
      have "wft ar T'" using ok_norm_type_wft[OF T' swf_envD(1)[OF "1.prems"(2)] wf(2)] .
      moreover from T' have "okT (liftMT (norm_type (tyenv env) T)) T'" by simp
      from "1.IH"(2)[OF n aTb refl refl this b' "1.prems"(2) wf(3) \<open>cok b\<close>]
      have "swf_tm ar ((a, T') # rb) b'" by (simp add: swf_tm_def)
      ultimately show ?thesis using wft_all_type[OF wf(1)]
        by (simp add: t' swf_tm_App swf_tm_Abs) (simp add: swf_tm_def all_const_all_type)
    next
      case None
      with "1.prems"(1) n obtain A B where AB: "dest_imp t = Some (A, B)"
        by (auto simp: norm_term_skip.simps[of env n t] split: option.splits)
      with "1.prems"(1) n None obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
        and t': "t' = mk_implies A B'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from cok_dest_imp[OF "1.prems"(4) AB] have t: "t = implies $ A $ B" and "cok B" by auto
      with "1.prems"(3) have "swf_tm ar rb implies" "swf_tm ar rb A" "swf_tm ar rb B"
        by (simp_all add: swf_tm_App)
      moreover have "swf_tm ar rb B'"
        by (rule "1.IH"(1)[OF n None AB refl B' "1.prems"(2) \<open>swf_tm ar rb B\<close> \<open>cok B\<close>])
      ultimately show ?thesis by (simp add: t' mk_implies_def swf_tm_App)
    qed
  qed
qed

context wf_algebra
begin

lemma iext_norm_type:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "ok (norm_type (tyenv env) T) T'"
  shows "tsubst \<rho> T' = tsubst \<rho>' T"
proof -
  from assms(1) have "tsol (tyenv env) \<rho>'"
    and agree: "\<And>v S. vt_lookup (tyenv env) v = None \<Longrightarrow> \<rho>' v S = \<rho> v S"
    by (auto simp: iext_def gsol_def)
  have "tsubst \<rho> T' = tsubst \<rho>' T'"
    by (rule tsubst_cong) (simp add: agree norm_type_unb[OF assms(2)])
  also have "\<dots> = tsubst \<rho>' T" by (rule ok_norm_type_tsol[OF assms(2) \<open>tsol _ \<rho>'\<close>])
  finally show ?thesis .
qed

lemma iext_norm_term_skip:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "swf_env ar env"
  shows "okT (norm_term_skip env n t) t' \<Longrightarrow> swf_tm ar rb t \<Longrightarrow> cok t \<Longrightarrow> skip_unb env n t \<Longrightarrow>
    sm \<rho> \<sigma> t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
  using assms
proof (induction env n t arbitrary: rb t' rule: norm_term_skip.induct)
  case (1 env n t)
  note prems = "1.prems"(1-4) and ie = "1.prems"(5-7)
  have rig': "rigid_subst \<sigma>'" using ie(1) by (simp add: iext_def)
  show ?case
  proof (cases "n = 0")
    case True
    with prems(1) have "ok (norm_term env t) t'" by (simp add: norm_term_skip.simps)
    from iext_norm_term[OF ie prems(2) this] show ?thesis .
  next
    case n: False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases x) auto
      from cok_dest_all[OF prems(3) aTb] have t: "t = all_const T $ Abs a T b" and "cok b"
        by auto
      from prems(1) n aTb obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from T' have T'': "okT (liftMT (norm_type (tyenv env) T)) T'" by simp
      from prems(2) t have "swf_tm ar ((a, T) # rb) b" by (simp add: swf_tm_App swf_tm_Abs)
      moreover from prems(4) n aTb have "skip_unb env n b" by (simp add: skip_unb.simps[of env n t])
      ultimately have "sm \<rho> \<sigma> b' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' b"
        by (rule "1.IH"(2)[OF n aTb refl refl T'' b' _ \<open>cok b\<close> _ ie])
      then have "dALL (tsubst \<rho>' T) (sm \<rho> \<sigma> b') \<equiv>\<^sub>\<beta>\<^sub>\<eta> dALL (tsubst \<rho>' T) (sm \<rho>' \<sigma>' b)"
        by (intro equiv_AppR equiv_Abs)
      moreover have "sm \<rho> \<sigma> t' = dALL (tsubst \<rho>' T) (sm \<rho> \<sigma> b')"
        using ie(2) by (simp add: t' iext_norm_type[OF ie(1) T'])
      moreover have "sm \<rho>' \<sigma>' t = dALL (tsubst \<rho>' T) (sm \<rho>' \<sigma>' b)"
        using rig' by (simp add: t)
      ultimately show ?thesis by (simp only:)
    next
      case None
      with prems(1) n obtain A B where AB: "dest_imp t = Some (A, B)"
        by (auto simp: norm_term_skip.simps[of env n t] split: option.splits)
      with prems(1) n None obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
        and t': "t' = mk_implies A B'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from cok_dest_imp[OF prems(3) AB] have t: "t = implies $ A $ B" and "cok B" by auto
      from prems(4) n None AB have "unb env A" "skip_unb env (n - 1) B"
        by (simp_all add: skip_unb.simps[of env n t])
      from prems(2) t have "swf_tm ar rb B" by (simp add: swf_tm_App)
      then have "sm \<rho> \<sigma> B' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' B"
        by (rule "1.IH"(1)[OF n None AB refl B' _ \<open>cok B\<close> \<open>skip_unb env (n - 1) B\<close> ie])
      then have "dIMP (sm \<rho> \<sigma> A) (sm \<rho> \<sigma> B') \<equiv>\<^sub>\<beta>\<^sub>\<eta> dIMP (sm \<rho> \<sigma> A) (sm \<rho>' \<sigma>' B)"
        by (rule equiv_AppR)
      moreover have "sm \<rho> \<sigma> t' = dIMP (sm \<rho> \<sigma> A) (sm \<rho> \<sigma> B')"
        using ie(2) by (simp add: t' mk_implies_def)
      moreover have "sm \<rho>' \<sigma>' t = dIMP (sm \<rho> \<sigma> A) (sm \<rho>' \<sigma>' B)"
        using rig' iext_unb[OF ie(1,2) \<open>unb env A\<close>] by (simp add: t)
      ultimately show ?thesis by (simp only:)
    qed
  qed
qed

end

end
