section \<open>Applying an Environment: Most General Unifiers\<close>

theory Pattern_Most_General
  imports Pattern_Unify_Correctness
begin

context pure_sig_gen
begin

subsection \<open>The most general solution\<close>

text \<open>Applying the environment is an instance of the canonical solution \<^const>\<open>esol\<close>:\<close>

lemma esol_inst_vcons:
  assumes ac: "acyc env" and vc: "vcons \<rho> (vars t \<union> evars env)" and nf: "nfree env"
  shows "vsubst (esol \<rho> env) (inst \<rho> t) = inst \<rho> (unf env t)"
  using vc
proof (induction t)
  case (Var x T)
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case (Some b)
    obtain U u where b: "b = (U, u)" by force
    have "(x, U) \<in> vars (Var x T) \<union> evars env" "(x, T) \<in> vars (Var x T) \<union> evars env"
      using Some b evarsI by auto
    with Var.prems nfreeD[OF nf Some] have "tsubst \<rho> T = tsubst \<rho> U" unfolding vcons_def by blast
    with Some b show ?thesis by (simp add: esol_def unf_Var[OF ac])
  qed (simp add: esol_def unf_Var[OF ac])
next
  case (Abs a T t)
  then show ?case by simp
next
  case (App s t)
  have "vcons \<rho> (vars s \<union> evars env)" by (rule vcons_mono[OF App.prems]) auto
  moreover have "vcons \<rho> (vars t \<union> evars env)" by (rule vcons_mono[OF App.prems]) auto
  ultimately show ?case using App.IH by simp
qed (simp_all add: unf_def)

end

context pure_sig
begin

lemma esol_inst_vcons:
  assumes "acyc env" "vcons \<rho> (vars t \<union> evars env)"
  shows "vsubst (esol \<rho> env) (inst \<rho> t) = inst \<rho> (unf env t)"
  by (rule esol_inst_vcons[OF assms nfree0])

lemma env_apply_esol:
  assumes "acyc env" "vcons (tnorm_inst (tyenv env)) (vars t \<union> evars env)"
  shows "env_apply env t = ap (tnorm_inst (tyenv env)) (esol (tnorm_inst (tyenv env)) env) t"
  unfolding env_apply_def ap_def by (rule esol_inst_vcons[OF assms, symmetric])

text \<open>
  Every solution \<open>(\<rho>, \<sigma>)\<close> of the environment factors through its application: applying the
  environment first does not change the meaning of a well-typed term.
\<close>

context
  fixes \<rho> \<sigma> env Y
  assumes sol: "solution \<rho> \<sigma> env" and ac: "acyc env" and wte: "wt_env \<rho> env"
    and vc: "vcons \<rho> Y" and eY: "evars env \<subseteq> Y"
begin

lemma ap_unf_struct:
  assumes V: "\<And>y T' e U. (y, T') \<in> vars s \<Longrightarrow> e \<turnstile> inst \<rho> (Var y T') : U \<Longrightarrow>
      ap \<rho> \<sigma> (unf env (Var y T')) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Var y T')"
    and sY: "vars s \<subseteq> Y"
  shows "e \<turnstile> inst \<rho> s : T \<Longrightarrow> ap \<rho> \<sigma> (unf env s) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> s"
  using V sY
proof (induction s arbitrary: e T)
  case (Var x T0)
  then show ?case by simp
next
  case (Abs a T0 b)
  from Abs.prems(1) obtain U where tb: "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> b : U" by auto
  have c: "ap \<rho> \<sigma> (unf env b) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> b" by (rule Abs.IH[OF tb]) (use Abs.prems in auto)
  have vcs: "vcons \<rho> (vars (Abs a T0 b) \<union> evars env)" by (rule vcons_mono[OF vc]) (use Abs.prems(3) eY in blast)
  have w: "wt (ap \<rho> \<sigma> (unf env (Abs a T0 b)))" "wt (ap \<rho> \<sigma> (Abs a T0 b))"
    using wt_ap[OF typing_unf[OF ac wte vcs Abs.prems(1)] solutionD(3)[OF sol]]
      wt_ap[OF Abs.prems(1) solutionD(3)[OF sol]] by blast+
  with conv_Abs[OF _ _ c] show ?case by simp
next
  case (App f u)
  from App.prems(1) obtain U where tf: "e \<turnstile> inst \<rho> f : U \<rightarrow>\<^sub>T T" and tu: "e \<turnstile> inst \<rho> u : U" by auto
  have c: "ap \<rho> \<sigma> (unf env f) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> f" "ap \<rho> \<sigma> (unf env u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    by (rule App.IH(1)[OF tf], use App.prems in auto) (rule App.IH(2)[OF tu], use App.prems in auto)
  have vcs: "vcons \<rho> (vars (f $ u) \<union> evars env)" by (rule vcons_mono[OF vc]) (use App.prems(3) eY in blast)
  have w: "wt (ap \<rho> \<sigma> (unf env (f $ u)))" "wt (ap \<rho> \<sigma> (f $ u))"
    using wt_ap[OF typing_unf[OF ac wte vcs App.prems(1)] solutionD(3)[OF sol]]
      wt_ap[OF App.prems(1) solutionD(3)[OF sol]] by blast+
  with conv_App[OF _ _ c] show ?case by simp
qed (simp_all add: unf_def)

lemma ap_unf_Var:
  "(x, T) \<in> Y \<Longrightarrow> e \<turnstile> inst \<rho> (Var x T) : U \<Longrightarrow> ap \<rho> \<sigma> (unf env (Var x T)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Var x T)"
proof (induction x arbitrary: T e U rule: dep_induct[OF ac])
  case (1 x)
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case (Some b)
    obtain U0 u where b: "b = (U0, u)" by force
    note lk = Some[unfolded b]
    have "(x, U0) \<in> Y" using evarsI[OF lk] eY by blast
    with "1.prems"(1) vc have TU: "tsubst \<rho> T = tsubst \<rho> U0" unfolding vcons_def by blast
    have vu: "vars u \<subseteq> Y" using evarsI2[OF lk] eY by blast
    have "ap \<rho> \<sigma> (unf env u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    proof (rule ap_unf_struct[OF _ vu wt_envD[OF wte lk]])
      fix y T' e' U' assume "(y, T') \<in> vars u" "e' \<turnstile> inst \<rho> (Var y T') : U'"
      moreover from this(1) have "(y, x) \<in> dep env" by (rule depI[OF lk])
      ultimately show "ap \<rho> \<sigma> (unf env (Var y T')) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Var y T')"
        using "1.IH" vu by blast
    qed
    moreover have "\<sigma> x (tsubst \<rho> U0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" by (rule solutionD(4)[OF sol lk])
    ultimately show ?thesis using TU lk by (simp add: unf_Var[OF ac]) (metis conv_sym conv_trans)
  qed (simp add: unf_Var[OF ac])
qed

lemma ap_unf:
  assumes tY: "vars t \<subseteq> Y" and ty: "e \<turnstile> inst \<rho> t : T"
  shows "ap \<rho> \<sigma> (unf env t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
proof (rule ap_unf_struct[OF _ tY ty])
  fix y T' e' U assume "(y, T') \<in> vars t" "e' \<turnstile> inst \<rho> (Var y T') : U"
  with tY show "ap \<rho> \<sigma> (unf env (Var y T')) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Var y T')"
    by (intro ap_unf_Var) auto
qed

lemma ap_env_apply:
  assumes tY: "vars t \<subseteq> Y" and ty: "e \<turnstile> inst \<rho> t : T"
    and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and tc: "\<forall>U\<in>typs (unf env t). tcons (tyenv env) U"
  shows "ap \<rho> \<sigma> (env_apply env t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
proof -
  have "inst \<rho> (inst (tnorm_inst (tyenv env)) (unf env t)) = inst \<rho> (unf env t)"
    unfolding inst_inst
  proof (rule inst_cong)
    fix U assume "U \<in> typs (unf env t)"
    with tc have "tcons (tyenv env) U" by blast
    then show "tsubst (\<lambda>v S. tsubst \<rho> (tnorm_inst (tyenv env) v S)) U = tsubst \<rho> U"
      using tsubst_tnorm[OF tac solutionD(2)[OF sol]] by (simp flip: tsubst_tsubst)
  qed
  then have "ap \<rho> \<sigma> (env_apply env t) = ap \<rho> \<sigma> (unf env t)" by (simp add: env_apply_def ap_def)
  with ap_unf[OF tY ty] show ?thesis by simp
qed

end

end

context pure_sig_gen
begin

text \<open>The types of an application are those of the term and of the bindings:\<close>

lemma typs_unf_struct:
  "(\<And>y T'. (y, T') \<in> vars s \<Longrightarrow> typs (unf env (Var y T')) \<subseteq> {T'} \<union> B) \<Longrightarrow> typs (unf env s) \<subseteq> typs s \<union> B"
  by (induction s) (auto simp: unf_def)

lemma typs_unf:
  assumes ac: "acyc env"
  shows "typs (unf env t) \<subseteq> typs t \<union> {V. \<exists>x U u. vt_lookup (tenv env) x = Some (U, u) \<and> V \<in> typs u}"
    (is "_ \<subseteq> _ \<union> ?B")
proof (rule typs_unf_struct)
  fix y T'
  show "typs (unf env (Var y T')) \<subseteq> {T'} \<union> ?B"
  proof (induction y arbitrary: T' rule: dep_induct[OF ac])
    case (1 x)
    show ?case
    proof (cases "vt_lookup (tenv env) x")
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      note lk = Some[unfolded b]
      have "typs (unf env u) \<subseteq> typs u \<union> ?B"
      proof (rule typs_unf_struct)
        fix y T'' assume "(y, T'') \<in> vars u"
        with "1.IH"[OF depI[OF lk this]] show "typs (unf env (Var y T'')) \<subseteq> {T''} \<union> ?B" by blast
      qed
      moreover have "typs u \<subseteq> ?B" using lk by blast
      ultimately show ?thesis using lk by (simp add: unf_Var[OF ac]) blast
    qed (simp add: unf_Var[OF ac])
  qed
qed

lemma unf_tcons:
  assumes tv: "tvinv A env" and ac: "acyc env" and tt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<forall>U\<in>typs (unf env t). tcons (tyenv env) U"
proof
  fix U assume U: "U \<in> typs (unf env t)"
  have "tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
  proof (cases "U \<in> typs t")
    case True
    with tt show ?thesis by (auto simp: ttvars_def)
  next
    case False
    with U typs_unf[OF ac, of t] obtain x V u where "vt_lookup (tenv env) x = Some (V, u)" "U \<in> typs u"
      by blast
    with tvinvD(2)[OF tv this(1)] show ?thesis by (auto simp: ttvars_def)
  qed
  then show "tcons (tyenv env) U" by (rule tinv_tcons[OF tvinvD(1)[OF tv]])
qed

text \<open>
  For a sorted type environment, the application is the canonical solution at the type
  instantiation \<^const>\<open>tsol0\<close>, which is well-sorted:
\<close>

lemma env_apply_tsol0:
  assumes tv: "tvinv A env" and ac: "acyc env" and tt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and vc: "vcons (tsol0 (tyenv env)) (vars t \<union> evars env)" and nf: "nfree env"
  shows "env_apply env t = ap (tsol0 (tyenv env)) (esol (tsol0 (tyenv env)) env) t"
proof -
  let ?\<theta> = "tyenv env"
  have "inst (tnorm_inst ?\<theta>) (unf env t) = inst (tsol0 ?\<theta>) (unf env t)"
  proof (rule inst_cong)
    fix U assume "U \<in> typs (unf env t)"
    with unf_tcons[OF tv ac tt] have "tcons ?\<theta> U" by blast
    then show "tsubst (tnorm_inst ?\<theta>) U = tsubst (tsol0 ?\<theta>) U"
      by (simp add: tsubst_tsol0[OF tinv_tacyc[OF tvinvD(1)[OF tv]]])
  qed
  then show ?thesis by (simp add: env_apply_def ap_def esol_inst_vcons[OF ac vc nf])
qed

lemma canonical_solution:
  assumes ei: "einv A K env" and wi: "winv env X" and nf: "nfree env"
  shows "solution (tsol0 (tyenv env)) (esol (tsol0 (tyenv env)) env) env"
    "wt_env (tsol0 (tyenv env)) env" "vinv (tsol0 (tyenv env)) env X" "cert_inst (tsol0 (tyenv env))"
    "tsol (tyenv env) (tsol0 (tyenv env))"
proof -
  note e = einvD[OF ei]
  let ?\<rho> = "tsol0 (tyenv env)"
  have \<rho>: "tsol (tyenv env) ?\<rho>" "wsinst alg ?\<rho>" "cert_inst ?\<rho>" by (rule tsol0[OF e(2,12,9)])+
  have w: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi \<rho>(1,3)] by blast+
  show "solution ?\<rho> (esol ?\<rho> env) env"
    by (rule esol_solution[OF e(3) w(1) _ \<rho>(2,1) nf]) (use w(2) vcons_mono in \<open>auto simp: vinv_def\<close>)
  show "wt_env ?\<rho> env" "vinv ?\<rho> env X" "cert_inst ?\<rho>" "tsol (tyenv env) ?\<rho>" by (fact w(1) w(2) \<rho>(3) \<rho>(1))+
qed


end

context pure_sig
begin

lemma env_apply_tsol0:
  assumes "tvinv A env" "acyc env" "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and "vcons (tsol0 (tyenv env)) (vars t \<union> evars env)"
  shows "env_apply env t = ap (tsol0 (tyenv env)) (esol (tsol0 (tyenv env)) env) t"
  by (rule env_apply_tsol0[OF assms nfree0])

lemma canonical_solution:
  assumes "einv A K env" "winv env X"
  shows "solution (tsol0 (tyenv env)) (esol (tsol0 (tyenv env)) env) env"
    "wt_env (tsol0 (tyenv env)) env" "vinv (tsol0 (tyenv env)) env X" "cert_inst (tsol0 (tyenv env))"
    "tsol (tyenv env) (tsol0 (tyenv env))"
  by (rule canonical_solution[OF assms nfree0])+


subsection \<open>Pattern unification\<close>

text \<open>
  The environment computed by \<^const>\<open>unify\<close> unifies the terms when it is applied, and so do the
  results of \<open>Envir.norm_term\<close>:
\<close>

theorem unify_env_apply:
  assumes inv: "uinv A env s t" and un: "unify alg s t env = Some (Ok env')"
  shows "env_apply env' s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> env_apply env' t"
    and "ok (norm_term env' s) s' \<Longrightarrow> ok (norm_term env' t) t' \<Longrightarrow> s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
proof -
  let ?X = "vars s \<union> vars t"
  obtain r where r: "unify alg s t env = Some r"
    and "\<And>e. r = Err e \<Longrightarrow> (\<exists>u. e = Unif u) \<or> e = Pattern"
    and ok: "\<And>env'. r = Ok env' \<Longrightarrow> extends env env' \<and> tvinv A env' \<and> scert alg (tyenv env') \<and>
      tcert alg (tvars_env (tyenv env') \<union> A) \<and> tsorted alg (tyenv env') \<and> acyc env' \<and> winv env' ?X"
    using unify_terminates[OF uinvD[OF inv]] by blast
  have r': "r = Ok env'" using r un by simp
  note p = ok[OF r']
  let ?\<theta> = "tyenv env'"
  let ?\<rho> = "tsol0 ?\<theta>"
  let ?\<sigma> = "esol ?\<rho> env'"
  have tv': "tvinv A env'" and ac': "acyc env'" using p by blast+
  have ti: "tinv ar (maxidx env') ?\<theta> A" by (rule tvinvD(1)[OF tv'])
  have \<rho>': "tsol ?\<theta> ?\<rho>" "wsinst alg ?\<rho>" "cert_inst ?\<rho>"
    using tsol0[OF ti] p by blast+
  have \<rho>0: "tsol (tyenv env) ?\<rho>" using extends_tsol[OF \<rho>'(1)] p by blast
  have w': "wt_env ?\<rho> env'" "vinv ?\<rho> env' ?X" using winvD[OF _ \<rho>'(1,3)] p by blast+
  have w: "wt_env ?\<rho> env" "vinv ?\<rho> env ?X" using winvD[OF uinvD(7)[OF inv] \<rho>0 \<rho>'(3)] by blast+
  have sol: "solution ?\<rho> ?\<sigma> env'"
    by (rule esol_solution[OF ac' w'(1) _ \<rho>'(2,1)]) (use w'(2) vcons_mono in \<open>auto simp: vinv_def\<close>)
  obtain e T where ty: "e \<turnstile> inst ?\<rho> s : T" "e \<turnstile> inst ?\<rho> t : T"
    using uinvD(11)[OF inv \<rho>0 \<rho>'(3)] by blast
  have cl: "closed s" "closed t" by (rule uinvD(9,10)[OF inv])+
  have eq: "ap ?\<rho> ?\<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap ?\<rho> ?\<sigma> t"
    using unify_sound(2)[OF un sol w(1) ty w(2) cl] by blast
  have ext: "tvars_env (tyenv env) \<subseteq> tvars_env ?\<theta>"
    using p tvars_env_textends unfolding extends_def by blast
  have app: "env_apply env' u = ap ?\<rho> ?\<sigma> u" if "u = s \<or> u = t" for u
  proof (rule env_apply_tsol0[OF tv' ac'])
    show "ttvars u \<subseteq> tvars_env ?\<theta> \<union> A" using uinvD(8)[OF inv] ext that by blast
    show "vcons ?\<rho> (vars u \<union> evars env')" using w'(2) that by (auto simp: vinv_def intro: vcons_mono)
  qed
  show "env_apply env' s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> env_apply env' t" using eq app by simp
  assume ns: "ok (norm_term env' s) s'" and nt: "ok (norm_term env' t) t'"
  have nac: "acyc env'" "closed_env env'" "tacyc ?\<theta>"
    using ac' wt_env_closed_env[OF w'(1)] tinv_tacyc[OF ti] by blast+
  have ws: "wt (env_apply env' s)" "wt (env_apply env' t)"
    using wt_ap[OF ty(1) solutionD(3)[OF sol]] wt_ap[OF ty(2) solutionD(3)[OF sol]] app by simp_all
  have "env_apply env' s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s'" "env_apply env' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
    using conv_beta_eta[OF ws(1) norm_term_env_apply(1)[OF ns nac]]
      conv_beta_eta[OF ws(2) norm_term_env_apply(1)[OF nt nac]] .
  with eq app show "s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" by (metis conv_sym conv_trans)
qed

text \<open>
  The result is most general: every unifier \<open>(\<rho>, \<sigma>)\<close> that solves the original environment is,
  up to new variables, an instance of the application of the result.
\<close>

theorem unify_most_general:
  assumes inv: "uinv A env s t" and un: "unify alg s t env = Some (Ok env')"
    and sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and vi: "vinv \<rho> env (vars s \<union> vars t)"
    and ty: "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" and eq: "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  shows "\<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
    ap \<rho>' \<sigma>' (env_apply env' s) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> s \<and> ap \<rho>' \<sigma>' (env_apply env' t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
proof -
  let ?X = "vars s \<union> vars t"
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have tv: "tvinv A env" using uinvD(2)[OF inv] .
  have tvs: "ttvars s \<union> ttvars t \<subseteq> ?KN" by (rule uinvD(8)[OF inv])
  have cl: "closed s" "closed t" by (rule uinvD(9,10)[OF inv])+
  from unify_complete(2)[OF un sol wte vi tv tvs ty cl eq refl] obtain \<rho>' \<sigma>' where
    sol': "solution \<rho>' \<sigma>' env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and wte': "wt_env \<rho>' env'" and tv': "tvinv A env'"
    by blast
  obtain r where r: "unify alg s t env = Some r"
    and "\<And>e. r = Err e \<Longrightarrow> (\<exists>u. e = Unif u) \<or> e = Pattern"
    and ok: "\<And>env'. r = Ok env' \<Longrightarrow> extends env env' \<and> tvinv A env' \<and> scert alg (tyenv env') \<and>
      tcert alg (tvars_env (tyenv env') \<union> A) \<and> tsorted alg (tyenv env') \<and> acyc env' \<and> winv env' ?X"
    using unify_terminates[OF uinvD[OF inv]] by blast
  have p: "extends env env'" "acyc env'" using ok r un by auto
  have ti': "tinv ar (maxidx env') (tyenv env') A" by (rule tvinvD(1)[OF tv'])
  have tb: "tbelow (maxidx env) (ttvars s)" "tbelow (maxidx env) (ttvars t)"
    using tvinv_tbelow[OF tv] tvs by blast+
  have vb: "below (maxidx env) (vars s)" "below (maxidx env) (vars t)"
    using vi unfolding vinv_def below_def by blast+
  have ty': "e \<turnstile> inst \<rho>' s : T" "e \<turnstile> inst \<rho>' t : T"
    using ty inst_agree[OF ag(1) tb(1)] inst_agree[OF ag(1) tb(2)] by simp_all
  have vtX: "vtvars ?X \<subseteq> ?KN" using vtvars_vars[of s] vtvars_vars[of t] tvs by auto
  have st: "step_ok env [] s t env'" using unif_sound[of alg "[]" s t env] un by (simp add: unify_def)
  have "wt_env \<rho>' env' \<and> vinv \<rho>' env' ?X \<and> ap \<rho>' \<sigma>' s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t"
  proof (rule step_okD(3)[OF st sol' extends_refl wt_env_agree[OF wte ag(1) tv] _ ty'])
    show "bs_env \<rho>' e []" by (simp add: bs_env_def)
    show "vinv \<rho>' env (?X \<union> vars s \<union> vars t)"
      using vinv_agree[OF vi ag(1) tv vtX] by (simp add: Un_ac)
  qed (use cl in \<open>simp_all add: closed_def\<close>)
  then have vi': "vinv \<rho>' env' ?X" by blast
  have ext: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    using p tvars_env_textends unfolding extends_def by blast
  have fac: "ap \<rho>' \<sigma>' (env_apply env' u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    if u: "u = s \<or> u = t" and tyu: "e \<turnstile> inst \<rho>' u : T" and tbu: "tbelow (maxidx env) (ttvars u)"
      and vbu: "below (maxidx env) (vars u)" for u
  proof -
    have tt: "ttvars u \<subseteq> tvars_env (tyenv env') \<union> A" using tvs ext u by blast
    have vc: "vcons \<rho>' (?X \<union> evars env')" using vi' by (simp add: vinv_def)
    have "ap \<rho>' \<sigma>' (env_apply env' u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
      by (rule ap_env_apply[OF sol' p(2) wte' vc Un_upper2 _ tyu tinv_tacyc[OF ti'] tinv_tcons_env[OF ti']
        unf_tcons[OF tv' p(2) tt]]) (use u in blast)
    moreover have "ap \<rho>' \<sigma>' u = ap \<rho> \<sigma> u" by (rule ap_agree[OF ag tbu vbu])
    ultimately show ?thesis by simp
  qed
  show ?thesis using sol' ag fac[OF _ ty'(1) tb(1) vb(1)] fac[OF _ ty'(2) tb(2) vb(2)] by blast
qed

end

end
