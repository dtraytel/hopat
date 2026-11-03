section \<open>Correctness of Pattern Unification\<close>

theory Pattern_Unify_Correctness
  imports Pattern_Term_Unif Pattern_Unify_Patterns
begin

context pure_sig
begin

text \<open>
  The final results on \<open>Pattern.unify\<close> (\<^const>\<open>unify\<close>), for closed terms \<open>s\<close> and \<open>t\<close> in an
  environment that satisfy the invariants of termination (theorem @{thm [source] unify_terminates}).
  A problem is unifiable if some solution of the environment, under which the terms are
  well-typed with the same type, unifies them.
\<close>

definition unifiable :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "unifiable env s t \<longleftrightarrow> (\<exists>\<rho> \<sigma> e T. solution \<rho> \<sigma> env \<and> wt_env \<rho> env \<and> vinv \<rho> env (vars s \<union> vars t) \<and>
    e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"

subsection \<open>Solutions of the resulting environments\<close>

text \<open>
  A sorted type environment has a well-sorted certified solution: it maps a bound variable of the
  sort of its binding to the normal form of the binding, and other variables to themselves.
\<close>

definition tsol0 :: "tyenv \<Rightarrow> tinst" where
  "tsol0 \<theta> v S = (case vt_lookup \<theta> v of
     Some (S', U) \<Rightarrow> if S = S' then tnorm \<theta> U else TVar v S
   | None \<Rightarrow> TVar v S)"

lemma tsubst_tsol0: "tacyc \<theta> \<Longrightarrow> tcons \<theta> T \<Longrightarrow> tsubst (tsol0 \<theta>) T = tnorm \<theta> T"
proof -
  assume ac: "tacyc \<theta>" and tc: "tcons \<theta> T"
  have "tsol0 \<theta> v S = tnorm \<theta> (TVar v S)" if "(v, S) \<in> tvars T" for v S
  proof (cases "vt_lookup \<theta> v")
    case (Some b)
    obtain S' U where b: "b = (S', U)" by force
    with Some tc that have "S' = S" unfolding tcons_def by blast
    with Some b show ?thesis by (simp add: tsol0_def tnorm_TVar[OF ac])
  qed (simp add: tsol0_def tnorm_TVar[OF ac])
  then show ?thesis unfolding tnorm_tsubst[of \<theta> T] by (rule tsubst_cong)
qed

lemma tsol0:
  assumes inv: "tinv ar n \<theta> A" and srt: "tsorted alg \<theta>" and sc: "scert alg \<theta>"
  shows "tsol \<theta> (tsol0 \<theta>)" "wsinst alg (tsol0 \<theta>)" "cert_inst (tsol0 \<theta>)"
proof -
  have ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" by (rule tinv_tacyc[OF inv], rule tinv_tcons_env[OF inv])
  show "tsol \<theta> (tsol0 \<theta>)"
    unfolding tsol_def using tsubst_tsol0[OF ac] tcons_envD[OF tc] by (simp add: tsol0_def)
  show "wsinst alg (tsol0 \<theta>)"
    unfolding wsinst_def
  proof (intro allI)
    fix v S
    have "bsorted alg \<theta> v" using srt by (cases v) (simp add: tsorted_def)
    then show "has_sort alg (tsol0 \<theta> v S) S"
      by (auto simp: tsol0_def bsorted_def simp del: has_sort.simps split: option.splits)
  qed
  have ci: "cert_inst (tnorm_inst \<theta>)"
    by (rule cert_inst_tnorm[OF ac]) (use inv tinv_wft sc in \<open>auto simp: scert_def\<close>)
  show "cert_inst (tsol0 \<theta>)"
    unfolding cert_inst_def
  proof (intro allI impI)
    fix v S assume S: "sort_ok alg S"
    have "tsol0 \<theta> v S = tnorm_inst \<theta> v S \<or> tsol0 \<theta> v S = TVar v S"
      by (auto simp: tsol0_def tnorm_TVar[OF ac] split: option.splits)
    then show "cert_typ alg ar (tsol0 \<theta> v S)"
      using ci[unfolded cert_inst_def, rule_format, OF S, of v] S by (auto simp: cert_typ_def)
  qed
qed

text \<open>
  An acyclic environment is solved by the unfoldings of its bindings, at the instances of the
  types of the bindings.
\<close>

definition esol :: "tinst \<Rightarrow> env \<Rightarrow> vsubst" where
  "esol \<rho> env x T = (case vt_lookup (tenv env) x of
     Some (U, u) \<Rightarrow> if T = tsubst \<rho> U then inst \<rho> (unf env u) else Var x T
   | None \<Rightarrow> Var x T)"

lemma esol_inst:
  assumes ac: "acyc env" and "vars t \<subseteq> evars env" "vcons \<rho> (evars env)"
  shows "vsubst (esol \<rho> env) (inst \<rho> t) = inst \<rho> (unf env t)"
  using assms(2)
proof (induction t)
  case (Var x T)
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case (Some b)
    obtain U u where b: "b = (U, u)" by force
    have "(x, U) \<in> evars env" "(x, T) \<in> evars env" using Var.prems Some b evarsI by auto
    with assms(3) have "tsubst \<rho> T = tsubst \<rho> U" unfolding vcons_def by blast
    with Some b show ?thesis by (simp add: esol_def unf_Var[OF ac])
  qed (simp add: esol_def unf_Var[OF ac])
qed (simp_all add: unf_def)

lemma esol_solution:
  assumes ac: "acyc env" and wte: "wt_env \<rho> env" and vc: "vcons \<rho> (evars env)"
    and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env) \<rho>"
  shows "solution \<rho> (esol \<rho> env) env"
proof -
  have cl: "closed (unf env u)" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using closed_substD[OF closed_usubst[OF ac wt_env_closed_env[OF wte]], of x U] that
    by (simp add: uval_eq[OF ac])
  have ty: "e \<turnstile> inst \<rho> (unf env u) : tsubst \<rho> U" if "vt_lookup (tenv env) x = Some (U, u)" for e x U u
  proof (rule typing_unf[OF ac wte _ wt_envD[OF wte that]])
    have "vars u \<subseteq> evars env" using that by (auto simp: evars_def bnds_def)
    with vc show "vcons \<rho> (vars u \<union> evars env)" by (simp add: Un_absorb1)
  qed
  have "wt_subst (esol \<rho> env)"
    unfolding wt_subst_def closed_subst_def
    using cl ty by (auto simp: esol_def closed_def split: option.splits)
  moreover have "esol \<rho> env x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> (esol \<rho> env) u"
    if "vt_lookup (tenv env) x = Some (U, u)" for x U u
  proof -
    have "vars u \<subseteq> evars env" using that by (auto simp: evars_def bnds_def)
    with that show ?thesis by (simp add: ap_def esol_def esol_inst[OF ac _ vc])
  qed
  ultimately show ?thesis using \<rho> by (simp add: solution_def)
qed

subsection \<open>Main results\<close>

text \<open>The invariants of termination:\<close>

definition uinv :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "uinv A env s t \<longleftrightarrow> finite A \<and> tvinv A env \<and> scert alg (tyenv env) \<and>
    tcert alg (tvars_env (tyenv env) \<union> A) \<and> tsorted alg (tyenv env) \<and> acyc env \<and>
    winv env (vars s \<union> vars t) \<and> ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    closed s \<and> closed t \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T))"

lemma uinvD:
  assumes "uinv A env s t"
  shows "finite A" "tvinv A env" "scert alg (tyenv env)" "tcert alg (tvars_env (tyenv env) \<union> A)"
    "tsorted alg (tyenv env)" "acyc env" "winv env (vars s \<union> vars t)"
    "ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" "closed s" "closed t"
    "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
  using assms unfolding uinv_def by blast+

theorem terminates:
  assumes "uinv A env s t"
  obtains r where "unify alg s t env = Some r" and "\<And>e. r = Err e \<Longrightarrow> (\<exists>u. e = Unif u) \<or> e = Pattern"
proof (rule unify_terminates[OF uinvD[OF assms]])
  fix r assume "unify alg s t env = Some r" "\<And>e. r = Err e \<Longrightarrow> (\<exists>u. e = Unif u) \<or> e = Pattern"
  then show thesis by (rule that)
qed

text \<open>
  A result exists only for unifiable problems; it is most general by completeness
  (theorem @{thm [source] unify_complete}): every unifying solution of \<open>env\<close> extends to a solution
  of the result.
\<close>

theorem Ok_unifiable:
  assumes inv: "uinv A env s t" and un: "unify alg s t env = Some (Ok env')"
  shows "unifiable env s t"
proof (rule unify_terminates[OF uinvD[OF inv]])
  let ?X = "vars s \<union> vars t"
  fix r assume r: "unify alg s t env = Some r"
    and ok: "\<And>env'. r = Ok env' \<Longrightarrow> extends env env' \<and> tvinv A env' \<and> scert alg (tyenv env') \<and>
      tcert alg (tvars_env (tyenv env') \<union> A) \<and> tsorted alg (tyenv env') \<and> acyc env' \<and> winv env' ?X"
  have r': "r = Ok env'" using r un by simp
  note p = ok[OF r']
  let ?\<rho> = "tsol0 (tyenv env')"
  have \<rho>': "tsol (tyenv env') ?\<rho>" "wsinst alg ?\<rho>" "cert_inst ?\<rho>"
    using tsol0[OF tvinvD(1)[of A env']] p by blast+
  have \<rho>0: "tsol (tyenv env) ?\<rho>" using extends_tsol[OF \<rho>'(1)] p by blast
  have w': "wt_env ?\<rho> env'" "vinv ?\<rho> env' ?X" using winvD[OF _ \<rho>'(1,3)] p by blast+
  have w: "wt_env ?\<rho> env" "vinv ?\<rho> env ?X" using winvD[OF uinvD(7)[OF inv] \<rho>0 \<rho>'(3)] by blast+
  have vc: "vcons ?\<rho> (evars env')" using w'(2) vcons_mono by (auto simp: vinv_def)
  have sol: "solution ?\<rho> (esol ?\<rho> env') env'"
    by (rule esol_solution[OF _ w'(1) vc \<rho>'(2,1)]) (use p in blast)
  obtain e T where ty: "e \<turnstile> inst ?\<rho> s : T" "e \<turnstile> inst ?\<rho> t : T"
    using uinvD(11)[OF inv \<rho>0 \<rho>'(3)] by blast
  have cl: "closed s" "closed t" by (rule uinvD(9,10)[OF inv])+
  have "ap ?\<rho> (esol ?\<rho> env') s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap ?\<rho> (esol ?\<rho> env') t"
    using unify_sound(2)[OF un sol w(1) ty w(2) cl] by blast
  moreover have "solution ?\<rho> (esol ?\<rho> env') env" using solution_extends[OF sol] p by blast
  ultimately show ?thesis using w ty unfolding unifiable_def by blast
qed

text \<open>Failure with \<open>Unif\<close> is final: the problem is not unifiable.\<close>

theorem Unif_not_unifiable:
  assumes "uinv A env s t" "unify alg s t env = Some (Err (Unif u))"
  shows "\<not> unifiable env s t"
  using unify_Unif[of s t env u A] assms unfolding unifiable_def uinv_def by (simp add: raise_def)

text \<open>\<^const>\<open>unify\<close> gives up only if \<open>s\<close>, \<open>t\<close> or a binding of \<open>env\<close> is not a pattern.\<close>

lemma bnds_nonneg_inst [simp]: "bnds_nonneg (inst \<rho> t) \<longleftrightarrow> bnds_nonneg t"
  by (induction t) simp_all

theorem Pattern_not_pattern:
  assumes inv: "uinv A env s t" and un: "unify alg s t env = Some (Err Pattern)"
  shows "\<not> (ppat s \<and> ppat t \<and> env_ppat env)"
proof
  assume p: "ppat s \<and> ppat t \<and> env_ppat env"
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  have tv: "tinv ar (maxidx env) ?\<theta> A" "scert alg ?\<theta>" using tvinvD(1)[OF uinvD(2)[OF inv]] uinvD(3)[OF inv] by blast+
  have r0: "tsol ?\<theta> ?\<rho>" "cert_inst ?\<rho>"
    using tsol_tnorm[OF tinv_tacyc[OF tv(1)]] cert_inst_tnorm[OF tinv_tacyc[OF tv(1)]] tinv_wft[OF tv(1)] tv(2)
    by (auto simp: scert_def)
  have w: "wt_env ?\<rho> env" using winvD[OF uinvD(7)[OF inv] r0] by blast
  obtain e T where ty: "e \<turnstile> inst ?\<rho> s : T" "e \<turnstile> inst ?\<rho> t : T" using uinvD(11)[OF inv r0] by blast
  have nn: "env_nonneg env"
    unfolding env_nonneg_def
  proof (intro allI impI)
    fix x U u assume "vt_lookup (tenv env) x = Some (U, u)"
    from typing_bnds_nonneg[OF wt_envD[OF w this, of e]] show "bnds_nonneg u" by simp
  qed
  have bs: "bnds_nonneg s" "bnds_nonneg t"
    using typing_bnds_nonneg[OF ty(1)] typing_bnds_nonneg[OF ty(2)] by simp_all
  have cl: "closed s" "closed t" by (rule uinvD(9,10)[OF inv])+
  from unify_ppat(1)[OF un] p cl wt_env_closed_env[OF w] bs nn show False by simp
qed

subsection \<open>Decidability on patterns\<close>

text \<open>
  Hence on patterns in an environment of patterns, \<^const>\<open>unify\<close> decides unifiability. On other
  problems, it may give up both on unifiable problems (\<open>?F a =?= b\<close>) and on non-unifiable ones.
\<close>

corollary decides:
  assumes inv: "uinv A env s t" and p: "ppat s" "ppat t" "env_ppat env"
  shows "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow> unifiable env s t"
    and "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow> \<not> unifiable env s t"
proof -
  obtain r where un: "unify alg s t env = Some r" and e: "\<And>e. r = Err e \<Longrightarrow> (\<exists>u. e = Unif u) \<or> e = Pattern"
    using terminates[OF inv] by blast
  have "r \<noteq> Err Pattern" using Pattern_not_pattern[OF inv] un p by blast
  with e consider env' where "r = Ok env'" | u where "r = Err (Unif u)" by (cases r) auto
  then show "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow> unifiable env s t"
    and "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow> \<not> unifiable env s t"
    using un Ok_unifiable[OF inv] Unif_not_unifiable[OF inv] by (cases; auto)+
qed

end

end
