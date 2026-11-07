section \<open>Normalization and Instances\<close>

theory Bicompose_Norm
  imports Bicompose_Seq
begin

text \<open>
  The new theorem of \<open>bicompose_aux\<close> is normalized by the environment of a unifier, but only
  as much as needed (\<^const>\<open>addth\<close>). An instance \<open>(\<rho>, \<sigma>)\<close> of the new theorem is extended to
  an instance \<open>(\<rho>', \<sigma>')\<close> that solves the environment and agrees with \<open>(\<rho>, \<sigma>)\<close> on the
  variables and type variables that the environment does not bind: \<open>\<rho>'\<close> composes \<open>\<rho>\<close> with the
  normal forms of the type environment (\<open>tsol0\<close>), \<open>\<sigma>'\<close> composes \<open>\<sigma>\<close> with the unfolded
  bindings (\<open>esol\<close>). Normalized terms contain only unbound variables, so their
  \<open>(\<rho>, \<sigma>)\<close>-instance is equivalent to the \<open>(\<rho>', \<sigma>')\<close>-instance of the original term.
\<close>

context pure_sig
begin

subsection \<open>Unbound variables\<close>

definition unb :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "unb env t \<longleftrightarrow> (\<forall>v\<in>vars t. vt_lookup (tenv env) (fst v) = None) \<and>
    (\<forall>p\<in>ttvars t. vt_lookup (tyenv env) (fst p) = None)"

lemma unb_simps [simp]:
  "unb env (Const a T) \<longleftrightarrow> (\<forall>p\<in>tvars T. vt_lookup (tyenv env) (fst p) = None)"
  "unb env (Free a T) \<longleftrightarrow> (\<forall>p\<in>tvars T. vt_lookup (tyenv env) (fst p) = None)"
  "unb env (Var x T) \<longleftrightarrow> vt_lookup (tenv env) x = None \<and> (\<forall>p\<in>tvars T. vt_lookup (tyenv env) (fst p) = None)"
  "unb env (Bound i)"
  "unb env (Abs a T t) \<longleftrightarrow> (\<forall>p\<in>tvars T. vt_lookup (tyenv env) (fst p) = None) \<and> unb env t"
  "unb env (s $ t) \<longleftrightarrow> unb env s \<and> unb env t"
  by (auto simp: unb_def)

lemma unb_empty: "env_is_empty env \<Longrightarrow> unb env t"
  by (simp add: unb_def env_is_empty_def vt_is_empty_lookup)

lemma ok_type_lookup_None: "ok (type_lookup \<theta> v S) None \<Longrightarrow> vt_lookup \<theta> v = None"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)

lemma ok_lookup1_None: "ok (lookup1 te x T) None \<Longrightarrow> vt_lookup te x = None"
  by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)

lemma norm_type_aux_unb:
  assumes "norm_type_aux \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> p \<in> tvars T' \<Longrightarrow> vt_lookup \<theta> (fst p) = None"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  note n = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vt_lookup \<theta> (fst p) = None" if "nt \<theta> U = Some (Ok U')" "p \<in> tvars U'" for U U'
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases T)
    case (Type a Ts)
    with n obtain Ts' where l2: "list_all2 (\<lambda>x y. ok (nt \<theta> x) y) Ts Ts'" and T': "T' = Type a Ts'"
      by (auto simp: ok_mapM)
    from "1.prems"(2) T' obtain U' where "U' \<in> set Ts'" "p \<in> tvars U'" by auto
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

lemma ok_norm_type_aux_unb: "ok (norm_type_aux \<theta> T) T' \<Longrightarrow> \<forall>p\<in>tvars T'. vt_lookup \<theta> (fst p) = None"
  using norm_type_aux_unb by blast

lemma norm_type_unb: "ok (norm_type \<theta> T) T' \<Longrightarrow> p \<in> tvars T' \<Longrightarrow> vt_lookup \<theta> (fst p) = None"
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

text \<open>All variables and type variables of a term have an index of at most \<open>m\<close>.\<close>

definition ibelow :: "integer \<Rightarrow> pterm \<Rightarrow> bool" where
  "ibelow m t \<longleftrightarrow> (\<forall>v\<in>vars t. snd (fst v) \<le> m) \<and> (\<forall>p\<in>ttvars t. snd (fst p) \<le> m)"

lemma vt_above_lookup: "vt_above tab m \<Longrightarrow> snd x \<le> m \<Longrightarrow> vt_lookup tab x = None"
  by transfer force

lemma above_unb: "above env m \<Longrightarrow> ibelow m t \<Longrightarrow> unb env t"
  by (fastforce simp: above_def ibelow_def unb_def intro: vt_above_lookup)


subsection \<open>Extending instances\<close>

text \<open>Composition of substitutions:\<close>

lemma wt_subst_comp:
  assumes "wt_subst \<sigma>" "wt_subst \<tau>"
  shows "wt_subst (\<lambda>x T. vsubst \<sigma> (\<tau> x T))"
proof -
  have "closed (vsubst \<sigma> (\<tau> x T))" for x T
    using assms closed_substD[of \<tau> x T] by (simp add: wt_subst_def closed_def)
  moreover have "e \<turnstile> vsubst \<sigma> (\<tau> x T) : T" if "cert_typ alg ar T" for e x T
    using typing_vsubst[OF wt_subst_typing[OF assms(2) that] assms(1)] .
  ultimately show ?thesis by (auto simp: wt_subst_def closed_subst_def)
qed

text \<open>
  \<open>(\<rho>', \<sigma>')\<close> extends \<open>(\<rho>, \<sigma>)\<close> by the environment \<open>env\<close>: it is a solution of \<open>env\<close> at which
  the bindings are well-typed, and it agrees with \<open>(\<rho>, \<sigma>)\<close> on unbound variables.
\<close>

definition iext :: "env \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> bool" where
  "iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longleftrightarrow> cinst \<rho>' \<and> gsubst \<sigma>' \<and> solution \<rho>' \<sigma>' env \<and> wt_env \<rho>' env \<and>
    (\<forall>v S. vt_lookup (tyenv env) v = None \<longrightarrow> \<rho>' v S = \<rho> v S) \<and>
    (\<forall>x T. vt_lookup (tenv env) x = None \<longrightarrow> \<sigma>' x T = \<sigma> x T)"

lemma iextD:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'"
  shows "cinst \<rho>'" "gsubst \<sigma>'" "solution \<rho>' \<sigma>' env" "wt_env \<rho>' env" "tsol (tyenv env) \<rho>'"
    "vt_lookup (tyenv env) v = None \<Longrightarrow> \<rho>' v S = \<rho> v S"
    "vt_lookup (tenv env) x = None \<Longrightarrow> \<sigma>' x T = \<sigma> x T"
  using assms solutionD(2) unfolding iext_def by blast+

lemma tsol_comp: "tsol \<theta> \<rho>0 \<Longrightarrow> tsol \<theta> (\<lambda>v S. tsubst \<rho> (\<rho>0 v S))"
  by (auto simp: tsol_def tsubst_tsubst)

lemma tsorts_tnorm:
  assumes ac: "tacyc \<theta>"
  shows "tsorts (tnorm \<theta> T) \<subseteq> tsorts T \<union> tyenv_sorts \<theta>"
proof -
  have var: "tsorts (tnorm \<theta> U) \<subseteq> tyenv_sorts \<theta>" if "vt_lookup \<theta> v = Some (S0, U)" for v S0 U
    using that
  proof (induction v arbitrary: S0 U rule: tdep_induct[OF ac])
    case (1 v)
    have "tsorts (tnorm \<theta> T) \<subseteq> tyenv_sorts \<theta>"
      if "\<forall>x\<in>fst ` tvars T. (x, v) \<in> tdep \<theta>" "tsorts T \<subseteq> tyenv_sorts \<theta>" for T
      using that
    proof (induction T)
      case (Type a Ts)
      have "tsorts (tnorm \<theta> T) \<subseteq> tyenv_sorts \<theta>" if "T \<in> set Ts" for T
        by (rule Type.IH[OF that]) (use Type.prems that in auto)
      then show ?case by auto
    next
      case (TVar x S1)
      show ?case
      proof (cases "vt_lookup \<theta> x")
        case None
        with TVar.prems(2) show ?thesis by (simp add: tnorm_TVar[OF ac])
      next
        case (Some b)
        obtain S2 U2 where b: "b = (S2, U2)" by force
        have "(x, v) \<in> tdep \<theta>" using TVar.prems(1) by simp
        from "1.IH"[OF this] Some b show ?thesis by (simp add: tnorm_TVar[OF ac])
      qed
    qed simp
    moreover have "\<forall>x\<in>fst ` tvars U. (x, v) \<in> tdep \<theta>" using "1.prems" unfolding tdep_def by blast
    moreover have "tsorts U \<subseteq> tyenv_sorts \<theta>" using "1.prems" unfolding tyenv_sorts_def by blast
    ultimately show ?case by blast
  qed
  show ?thesis
  proof (induction T)
    case (TVar x S)
    show ?case
    proof (cases "vt_lookup \<theta> x")
      case (Some b)
      obtain S2 U2 where b: "b = (S2, U2)" by force
      with Some var[of x S2 U2] show ?thesis by (auto simp: tnorm_TVar[OF ac])
    qed (simp add: tnorm_TVar[OF ac])
  qed auto
qed

lemma sbound_tsol0: "tacyc \<theta> \<Longrightarrow> sbound (tsol0 \<theta>) (tyenv_sorts \<theta>)"
  unfolding sbound_def tsol0_def
proof (intro allI)
  fix v S assume ac: "tacyc \<theta>"
  show "tsorts (case vt_lookup \<theta> v of Some (S', U) \<Rightarrow> if S = S' then tnorm \<theta> U else TVar v S
      | None \<Rightarrow> TVar v S) \<subseteq> insert S (tyenv_sorts \<theta>)"
  proof (cases "vt_lookup \<theta> v")
    case (Some b)
    obtain S' U where b: "b = (S', U)" by force
    have "tsorts U \<subseteq> tyenv_sorts \<theta>" using Some b unfolding tyenv_sorts_def by blast
    with tsorts_tnorm[OF ac, of U] Some b show ?thesis by auto
  qed simp
qed

lemma iext_exists_sb:
  assumes ei: "einv A K env" and wi: "winv env X" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  obtains \<rho>' \<sigma>' \<rho>0 where "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "cinst \<rho>0" "sbound \<rho>0 (tyenv_sorts (tyenv env))"
    "\<And>v S. \<rho>' v S = tsubst \<rho> (\<rho>0 v S)"
proof -
  note e = einvD[OF ei]
  let ?\<theta> = "tyenv env"
  have t0: "tsol ?\<theta> (tsol0 ?\<theta>)" "wsinst alg (tsol0 ?\<theta>)" "cert_inst (tsol0 ?\<theta>)"
    using tsol0[OF e(2) e(12) e(9)] by blast+
  define \<rho>' where "\<rho>' v S = tsubst \<rho> (tsol0 ?\<theta> v S)" for v S
  have c': "cinst \<rho>'" unfolding \<rho>'_def by (rule cinst_comp[OF \<rho>]) (use t0 in \<open>simp add: cinst_def\<close>)
  have ts': "tsol ?\<theta> \<rho>'" unfolding \<rho>'_def by (rule tsol_comp[OF t0(1)])
  from winvD[OF wi ts' cinstD(2)[OF c']] have wte: "wt_env \<rho>' env" and vi: "vinv \<rho>' env X" by blast+
  have vc: "vcons \<rho>' (evars env)" using vi by (auto simp: vinv_def intro: vcons_mono)
  have sol0: "solution \<rho>' (esol \<rho>' env) env"
    by (rule esol_solution[OF e(3) wte vc cinstD(1)[OF c'] ts'])
  define \<sigma>' where "\<sigma>' = (\<lambda>x T. vsubst \<sigma> (esol \<rho>' env x T))"
  have ws: "wt_subst \<sigma>'"
    unfolding \<sigma>'_def by (rule wt_subst_comp[OF gsubstD(1)[OF \<sigma>] solutionD(3)[OF sol0]])
  have gs: "gsubst \<sigma>'" using ws \<sigma> by (simp add: gsubst_def \<sigma>'_def)
  have "solution \<rho>' \<sigma>' env"
    unfolding solution_def
  proof (intro conjI allI impI)
    show "wsinst alg \<rho>'" "tsol ?\<theta> \<rho>'" "wt_subst \<sigma>'" using c' ts' ws by (simp_all add: cinst_def)
    fix x U u assume b: "vt_lookup (tenv env) x = Some (U, u)"
    have "esol \<rho>' env x (tsubst \<rho>' U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' (esol \<rho>' env) u" by (rule solutionD(4)[OF sol0 b])
    from conv_vsubst[OF this gsubstD(1)[OF \<sigma>]]
    show "\<sigma>' x (tsubst \<rho>' U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" by (simp add: \<sigma>'_def ap_def vsubst_vsubst)
  qed
  moreover have "\<rho>' v S = \<rho> v S" if "vt_lookup ?\<theta> v = None" for v S
    using that by (simp add: \<rho>'_def tsol0_def)
  moreover have "\<sigma>' x T = \<sigma> x T" if "vt_lookup (tenv env) x = None" for x T
    using that by (simp add: \<sigma>'_def esol_def)
  ultimately have "iext env \<rho> \<sigma> \<rho>' \<sigma>'" using c' gs wte by (simp add: iext_def)
  moreover have "cinst (tsol0 ?\<theta>)" using t0 by (simp add: cinst_def)
  ultimately show thesis using sbound_tsol0[OF e(6)] by (rule that) (simp add: \<rho>'_def)
qed

lemma iext_tsubst:
  "iext env \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> (\<forall>p\<in>tvars T. vt_lookup (tyenv env) (fst p) = None) \<Longrightarrow> tsubst \<rho>' T = tsubst \<rho> T"
  by (rule tsubst_cong) (auto dest: iextD(6))

lemma iext_inst: "iext env \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> unb env t \<Longrightarrow> inst \<rho>' t = inst \<rho> t"
  by (rule inst_cong) (auto simp: unb_def ttvars_def intro!: iext_tsubst)

lemma iext_unb:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "unb env t"
  shows "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t"
proof -
  have "vsubst \<sigma>' (inst \<rho> t) = vsubst \<sigma> (inst \<rho> t)"
    using assms(2)
  proof (induction t)
    case (Var x T)
    then show ?case by (simp add: iextD(7)[OF assms(1)])
  qed auto
  with iext_inst[OF assms] show ?thesis by (simp add: ap_def)
qed

text \<open>The instances of a term and of its normal form:\<close>

lemma iext_norm_term:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "ok (norm_term env t) t'" "e \<turnstile> inst \<rho>' t : T"
  shows "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t" "e \<turnstile> inst \<rho> t' : T"
proof -
  note i = iextD[OF assms(1)]
  note ns = nsoundD[OF norm_term_sound[OF assms(2) i(5,4)]]
  have u: "unb env t'" by (rule norm_term_unb[OF assms(2)])
  from ns(4)[OF assms(3) i(3)] iext_unb[OF assms(1) u]
  show "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t" by (simp add: conv_sym)
  from ns(3)[OF assms(3)] iext_inst[OF assms(1) u] show "e \<turnstile> inst \<rho> t' : T" by simp
qed


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

declare skip_unb.simps [simp del]

lemma skip_unb_take:
  "0 \<le> n \<Longrightarrow> \<forall>H\<in>set (take (nat_of_integer n) (spine_hyps t)). unb env H \<Longrightarrow> skip_unb env n t"
proof (induction env n t rule: skip_unb.induct)
  case (1 env n t)
  show ?case
  proof (cases "n = 0")
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
      then have "dest_imp t = None" by (auto simp: dest_all_Some)
      with aTb have "spine_hyps t = spine_hyps b" by (subst spine_hyps.simps) simp
      with "1.IH"(2)[OF aTb refl refl] "1.prems" aTb show ?thesis by (subst skip_unb.simps) simp
    next
      case None
      show ?thesis
      proof (cases "dest_imp t")
        case (Some AB)
        then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
        then have "spine_hyps t = A # spine_hyps B" by (subst spine_hyps.simps) simp
        moreover have "nat_of_integer n = Suc (nat_of_integer (n - 1))" "0 \<le> n - 1"
          using "1.prems"(1) False by (simp_all add: integer_reps)
        ultimately show ?thesis
          using "1.IH"(1)[OF None AB refl] "1.prems"(2) None AB by (subst skip_unb.simps) simp
      next
        case None': None
        with None show ?thesis by (subst skip_unb.simps) simp
      qed
    qed
  qed (subst skip_unb.simps; simp)
qed

lemma iext_norm_term_skip:
  "okT (norm_term_skip env n t) t' \<Longrightarrow> iext env \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> gsubst \<sigma> \<Longrightarrow>
    e \<turnstile> t : propT \<Longrightarrow> skip_unb env n t \<Longrightarrow>
    ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t \<and> ienv \<rho>' e \<turnstile> inst \<rho> t' : propT"
proof (induction env n t arbitrary: e t' rule: norm_term_skip.induct)
  case (1 env n t)
  note ie = "1.prems"(2) and i = iextD[OF "1.prems"(2)]
  note ws = gsubstD(1)[OF "1.prems"(3)] and ws' = gsubstD(1)[OF i(2)]
  have ci: "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
  have tt: "ienv \<rho>' e \<turnstile> inst \<rho>' t : propT"
    using typing_inst[OF "1.prems"(4) cert_inst_inst_ok[OF ci]] by simp
  show ?case
  proof (cases "n = 0")
    case True
    with "1.prems"(1) have "ok (norm_term env t) t'" by (simp add: norm_term_skip.simps)
    from iext_norm_term[OF ie this tt] show ?thesis by blast
  next
    case n: False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases x) auto
      from "1.prems"(1) n aTb obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      note ty = typing_dest_all[OF "1.prems"(4) aTb]
      have sk: "skip_unb env n b" using "1.prems"(5) n aTb by (simp add: skip_unb.simps[of env n t])
      from T' have T'': "okT (liftMT (norm_type (tyenv env) T)) T'" by simp
      from "1.IH"(2)[OF n aTb refl refl T'' b' ie "1.prems"(3) ty(5) sk]
      have cb: "ap \<rho> \<sigma> b' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' b" and tb: "(ienv \<rho>' e)\<langle>0:tsubst \<rho>' T\<rangle> \<turnstile> inst \<rho> b' : propT"
        by (simp_all add: tsubst_shift)
      have tT: "tsubst \<rho> T' = tsubst \<rho>' T"
        using iext_tsubst[OF ie] norm_type_unb[OF T'] norm_type_sound[OF T' i(5)] by metis
      have cT: "cert_typ alg ar (all_type (tsubst \<rho>' T))" "cert_typ alg ar (tsubst \<rho>' T)"
        using cert_typ_tsubst[OF ty(3) ci] cert_typ_tsubst[OF ty(4) ci] by simp_all
      have tt': "ienv \<rho>' e \<turnstile> inst \<rho> t' : propT"
        using cT tb by (simp add: t' tT typing_all_const)
      have aT': "ap \<rho> \<sigma> t' = all_const (tsubst \<rho>' T) $ Abs a (tsubst \<rho>' T) (ap \<rho> \<sigma> b')"
        by (simp add: t' tT)
      have aT: "ap \<rho>' \<sigma>' t = all_const (tsubst \<rho>' T) $ Abs a (tsubst \<rho>' T) (ap \<rho>' \<sigma>' b)"
        by (simp add: ty(1))
      have w': "wt (ap \<rho> \<sigma> t')" by (rule wt_ap[OF tt' ws])
      have w: "wt (ap \<rho>' \<sigma>' t)" by (rule wt_ap[OF tt ws'])
      have "Abs a (tsubst \<rho>' T) (ap \<rho> \<sigma> b') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho>' T) (ap \<rho>' \<sigma>' b)"
        by (rule conv_Abs[OF _ _ cb]) (use w w' aT aT' in \<open>auto dest: wt_AppD\<close>)
      then have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t"
        unfolding aT aT' by (rule conv_App[OF w'[unfolded aT'] w[unfolded aT] conv_refl])
      with tt' show ?thesis by blast
    next
      case None
      with "1.prems"(1) n obtain A B where AB: "dest_imp t = Some (A, B)"
        by (auto simp: norm_term_skip.simps[of env n t] split: option.splits)
      with "1.prems"(1) n None obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
        and t': "t' = mk_implies A B'"
        by (auto simp: norm_term_skip.simps[of env n t])
      note ty = typing_dest_imp[OF "1.prems"(4) AB]
      from "1.prems"(5) n None AB have uA: "unb env A" and sk: "skip_unb env (n - 1) B"
        by (simp_all add: skip_unb.simps[of env n t])
      from "1.IH"(1)[OF n None AB refl B' ie "1.prems"(3) ty(5) sk]
      have cB: "ap \<rho> \<sigma> B' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' B" and tB: "ienv \<rho>' e \<turnstile> inst \<rho> B' : propT" by blast+
      have iA: "inst \<rho> A = inst \<rho>' A" and aA: "ap \<rho> \<sigma> A = ap \<rho>' \<sigma>' A"
        using iext_inst[OF ie uA] iext_unb[OF ie uA] by simp_all
      have tA: "ienv \<rho>' e \<turnstile> inst \<rho> A : propT"
        using typing_inst[OF ty(4) cert_inst_inst_ok[OF ci]] iA by simp
      have tt': "ienv \<rho>' e \<turnstile> inst \<rho> t' : propT"
        using ty(3) tB tA by (simp add: t' mk_implies_def typing_implies)
      have w': "wt (ap \<rho> \<sigma> t')" by (rule wt_ap[OF tt' ws])
      have w: "wt (ap \<rho>' \<sigma>' t)" by (rule wt_ap[OF tt ws'])
      have aT': "ap \<rho> \<sigma> t' = (implies $ ap \<rho>' \<sigma>' A) $ ap \<rho> \<sigma> B'"
        using aA by (simp add: t' mk_implies_def)
      have aT: "ap \<rho>' \<sigma>' t = (implies $ ap \<rho>' \<sigma>' A) $ ap \<rho>' \<sigma>' B"
        by (simp add: ty(1))
      have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t"
        unfolding aT aT' by (rule conv_App[OF w'[unfolded aT'] w[unfolded aT] conv_refl cB])
      with tt' show ?thesis by blast
    qed
  qed
qed

end

end
