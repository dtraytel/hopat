section \<open>Completeness of \<open>SIMPL\<close>\<close>

theory Unify_Simpl_Complete
  imports Unify_Simpl_Term "Pattern_Correctness.Pattern_Complete"
begin

text \<open>
  \<^const>\<open>SIMPL0\<close> and \<^const>\<open>SIMPL\<close> are complete for the algebra of the signature: on a problem
  with a solution \<open>(\<rho>, \<sigma>)\<close>, they do not raise \<open>CANTUNIFY\<close>, and every result has a solution that
  agrees with \<open>(\<rho>, \<sigma>)\<close> on the old variables and solves the new pairs.

  The typing of the pairs at \<open>\<rho>\<close> alone does not suffice: \<open>unify.ML\<close> unifies the body types of
  the heads of flex-flex and flex-rigid pairs, which agree only if the pairs are \<open>\<eta>\<close>-long in
  the most general solution of the type environment. For example, \<open>?v =?= c\<close> with
  \<open>?v :: ?'d \<Rightarrow> ?'d\<close> and \<open>c :: (\<alpha> \<Rightarrow> \<alpha>) \<Rightarrow> ?'e\<close> has the solution \<open>?'d, ?'e := \<alpha> \<Rightarrow> \<alpha>\<close>,
  \<open>?v := c\<close>, but \<open>SIMPL\<close> binds \<open>?'d := \<alpha> \<Rightarrow> \<alpha>\<close> when it strips the abstractions of the
  \<open>\<eta>\<close>-expanded pair, and then \<open>?'e := \<alpha>\<close>, the body type of \<open>?'d \<Rightarrow> ?'d\<close>. So we assume the
  invariants of the termination proof (theory \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>), which
  require the pairs to be well-typed in every certified solution of the type environment.
\<close>

context pure_sig
begin

subsection \<open>Computations without \<open>CANTUNIFY\<close>\<close>

definition ncu :: "'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "ncu m P \<longleftrightarrow> (\<forall>evs. m \<noteq> Some (evs, UErr CANTUNIFY)) \<and> (\<forall>x. okW m x \<longrightarrow> P x)"

lemma ncu_simps [simp]:
  "ncu (returnW x) P \<longleftrightarrow> P x" "ncu (raiseW e) P \<longleftrightarrow> e \<noteq> CANTUNIFY" "ncu None P"
  "ncu (liftM m) P \<longleftrightarrow> (\<forall>x. ok m x \<longrightarrow> P x)"
  by (auto simp: ncu_def returnW_def raiseW_def liftM_def split: option.splits res.splits)

lemma ncu_bindW: "ncu m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> ncu (f x) Q) \<Longrightarrow> ncu (bindW m f) Q"
  unfolding ncu_def by (fastforce simp: bindW_def map_option_eq_Some split: option.splits ures.splits)

lemma ncu_mono: "ncu m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> ncu m Q"
  unfolding ncu_def by blast

lemma ncu_mono': "ncu m P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> ncu m Q"
  unfolding ncu_def by blast

lemma ncu_cuok: "ncu m P \<Longrightarrow> cuok m Q \<Longrightarrow> ncu m (\<lambda>x. P x \<and> Q x)"
  unfolding ncu_def xokW_def by auto

lemma ncu_handle_assign:
  assumes "ncu m P" "\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> Q (f x)" "Q r"
  shows "ncu (handleW (bindW m (\<lambda>x. returnW (f x))) (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e)) Q"
  using assms unfolding ncu_def
  by (auto simp: handleW_def bindW_def returnW_def raiseW_def split: option.splits ures.splits uexn.splits)


subsection \<open>The invariant\<close>

text \<open>
  The completeness invariant for a solution \<open>(\<rho>, \<sigma>)\<close>: the soundness invariants at \<open>\<rho>\<close> for the
  variables \<open>X\<close> of the problem, the type invariant, and the pairs are well-typed at \<open>\<rho>\<close> and
  solved by \<open>(\<rho>, \<sigma>)\<close>. It is used together with the invariant \<^const>\<open>sinv\<close> of the termination
  proof.
\<close>

definition scinv :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> bool" where
  "scinv \<rho> \<sigma> env dps X A \<longleftrightarrow> solution \<rho> \<sigma> env \<and> wt_env \<rho> env \<and> vinv \<rho> env X \<and> tvinv A env \<and>
    vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and> dtyped \<rho> dps \<and> dsolved \<rho> \<sigma> dps"

lemma scinvD:
  assumes "scinv \<rho> \<sigma> env dps X A"
  shows "solution \<rho> \<sigma> env" "wt_env \<rho> env" "vinv \<rho> env X" "tvinv A env"
    "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" "dtyped \<rho> dps" "dsolved \<rho> \<sigma> dps"
  using assms unfolding scinv_def by blast+

lemma scinv_mono: "scinv \<rho> \<sigma> env dps X A \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> scinv \<rho> \<sigma> env dps' X A"
  unfolding scinv_def using dtyped_mono dsolved_mono by blast

text \<open>Pairs of the problem keep their meaning in solutions that agree on the old variables:\<close>

lemma sc_pok_agree:
  assumes p: "upok A env rb X t u" and tv: "tvinv A env" and vi: "vinv \<rho> env X"
    and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
  shows "inst \<rho>' t = inst \<rho> t" "inst \<rho>' u = inst \<rho> u" "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t" "ap \<rho>' \<sigma>' u = ap \<rho> \<sigma> u"
    "bs_env \<rho> e rb \<Longrightarrow> bs_env \<rho>' e rb"
proof -
  note pd = upokD[OF p]
  have tb: "tbelow (maxidx env) (ttvars t)" "tbelow (maxidx env) (ttvars u)" "tbelow (maxidx env) (btvars rb)"
    using pd(3-5) tvinv_tbelow[OF tv] by blast+
  have vb: "below (maxidx env) (vars t)" "below (maxidx env) (vars u)"
    using pd(1,2) vi unfolding vinv_def below_def by blast+
  show "inst \<rho>' t = inst \<rho> t" "inst \<rho>' u = inst \<rho> u" using inst_agree[OF ag(1)] tb by blast+
  show "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t" "ap \<rho>' \<sigma>' u = ap \<rho> \<sigma> u" using ap_agree[OF ag] tb vb by blast+
  show "bs_env \<rho> e rb \<Longrightarrow> bs_env \<rho>' e rb" using bs_env_agree[OF _ ag(1) tb(3)] .
qed

lemma sc_dps_agree:
  assumes p: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u" and tv: "tvinv A env" and vi: "vinv \<rho> env X"
    and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
  shows "dtyped \<rho> dps \<Longrightarrow> dtyped \<rho>' dps" and "dsolved \<rho> \<sigma> dps \<Longrightarrow> dsolved \<rho>' \<sigma>' dps"
proof -
  have a: "inst \<rho>' t = inst \<rho> t \<and> inst \<rho>' u = inst \<rho> u \<and> ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t \<and> ap \<rho>' \<sigma>' u = ap \<rho> \<sigma> u \<and>
      (\<forall>e. bs_env \<rho> e rb \<longrightarrow> bs_env \<rho>' e rb)" if "(rb, t, u) \<in> set dps" for rb t u
  proof -
    have pp: "upok A env rb X t u" using p that by auto
    show ?thesis using sc_pok_agree[OF pp tv vi ag] by blast
  qed
  show "dtyped \<rho> dps \<Longrightarrow> dtyped \<rho>' dps"
    unfolding dtyped_def
  proof (intro ballI)
    fix dp assume d: "\<forall>(rb, t, u)\<in>set dps. (\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
        \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb)" and m: "dp \<in> set dps"
    obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
    from d m dp a[of rb t u] show "case dp of (rb, t, u) \<Rightarrow> (\<exists>e T. bs_env \<rho>' e rb \<and> e \<turnstile> inst \<rho>' t : T \<and>
        e \<turnstile> inst \<rho>' u : T) \<and> \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb)"
      by fastforce
  qed
  show "dsolved \<rho> \<sigma> dps \<Longrightarrow> dsolved \<rho>' \<sigma>' dps"
    unfolding dsolved_def using a by fastforce
qed

lemma sc_sinv_pok: "sinv A K X env dps \<Longrightarrow> \<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
  by (simp add: sinv_def)

text \<open>The invariant for the result of a sound step, given a solution of the new environment:\<close>

lemma scinv_step_core:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and p: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    and st: "dstep env dps env' dps'"
    and sol: "solution \<rho>' \<sigma>' env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
  shows "wt_env \<rho>' env' \<and> dtyped \<rho>' dps' \<and> vinv \<rho>' env' (X \<union> dvars dps')"
proof -
  note i = scinvD[OF inv]
  have wte: "wt_env \<rho>' env" by (rule wt_env_agree[OF i(2) ag(1) i(4)])
  have dt: "dtyped \<rho>' dps" by (rule sc_dps_agree(1)[OF p i(4) i(3) ag i(6)])
  have vi: "vinv \<rho>' env X" by (rule vinv_agree[OF i(3) ag(1) i(4) i(5)])
  have dv: "dvars dps \<subseteq> X \<union> evars env"
    using p unfolding dvars_def by (fastforce dest: upokD(1,2))
  have vi': "vinv \<rho>' env (X \<union> dvars dps)" using vinv_hn[of \<rho>' env X X "dvars dps"] vi dv by simp
  show ?thesis using dstepD(2)[OF st solutionD(2)[OF sol] extends_refl wte dt vi'] by blast
qed

lemma scinv_step:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and p: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    and st: "dstep env dps env' dps'"
    and sol: "solution \<rho>' \<sigma>' env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and ds: "dsolved \<rho>' \<sigma>' dps'" and tv: "tvinv A env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "scinv \<rho>' \<sigma>' env' dps' X A"
  using scinv_step_core[OF inv p st sol ag] sol ds tv scinvD(5)[OF inv]
    vinv_mono[of \<rho>' env' "X \<union> dvars dps'" X] unfolding scinv_def by auto


subsection \<open>Normalization of pairs\<close>

text \<open>Types that are equal in the most general solution of the type environment unify without
  changing it:\<close>

lemma sc_cunify_types_same:
  assumes ti: "tinv ar n (tyenv env) A" and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" and eq: "tnorm (tyenv env) T = tnorm (tyenv env) U"
  shows "cunify_types alg' T U env = returnW env"
  by (rule cunify_types_same[OF tinv_tacyc[OF ti] tinv_tcons_env[OF ti] tinv_tcons[OF ti T]
      tinv_tcons[OF ti U] eq])

text \<open>
  A pair whose sides have a common type in the most general solution of the type environment,
  which is not a function type:
\<close>

definition hsat0 :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "hsat0 env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> \<exists>e0 T0. bs_env (rho0 env) e0 rb \<and>
    e0 \<turnstile> inst (rho0 env) t : T0 \<and> e0 \<turnstile> inst (rho0 env) u : T0 \<and> arity T0 = 0)"

lemma new_dpair_complete_base:
  "einv A K env \<Longrightarrow> bs_env (rho0 env) e0 rb \<Longrightarrow> e0 \<turnstile> inst (rho0 env) t : T0 \<Longrightarrow> e0 \<turnstile> inst (rho0 env) u : T0 \<Longrightarrow>
    nabs t = arity T0 \<Longrightarrow> nabs u = arity T0 \<Longrightarrow> ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    \<not> is_Abs t \<Longrightarrow> \<not> is_Abs u \<Longrightarrow>
    ncu (new_dpair al rb t u env) (\<lambda>(dp', env'). env' = env \<and> hsat0 env dp' \<and>
      (\<forall>\<rho> \<sigma> e V. wt_subst \<sigma> \<longrightarrow> e \<turnstile> inst \<rho> t : V \<longrightarrow> e \<turnstile> inst \<rho> u : V \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<longrightarrow>
        dsolved \<rho> \<sigma> [dp']))"
proof -
  assume a: "bs_env (rho0 env) e0 rb" "e0 \<turnstile> inst (rho0 env) t : T0" "e0 \<turnstile> inst (rho0 env) u : T0"
    "nabs t = arity T0" "\<not> is_Abs t" "\<not> is_Abs u"
  have nd: "new_dpair al rb t u env = returnW ((rb, t, u), env)" using a(5,6) by (cases t; cases u) auto
  have "hsat0 env (rb, t, u)" using a(1-4) a(5) unfolding hsat0_def by auto
  then show ?thesis by (simp add: nd)
qed

lemma new_dpair_complete:
  shows "einv A K env \<Longrightarrow> bs_env (rho0 env) e0 rb \<Longrightarrow> e0 \<turnstile> inst (rho0 env) t : T0 \<Longrightarrow> e0 \<turnstile> inst (rho0 env) u : T0 \<Longrightarrow>
    nabs t = arity T0 \<Longrightarrow> nabs u = arity T0 \<Longrightarrow> ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    ncu (new_dpair al rb t u env) (\<lambda>(dp', env'). env' = env \<and> hsat0 env dp' \<and>
      (\<forall>\<rho> \<sigma> e V. wt_subst \<sigma> \<longrightarrow> e \<turnstile> inst \<rho> t : V \<longrightarrow> e \<turnstile> inst \<rho> u : V \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<longrightarrow>
        dsolved \<rho> \<sigma> [dp']))"
proof (induction al rb t u env arbitrary: e0 T0 rule: new_dpair.induct)
  case (1 al rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  let ?\<theta> = "tyenv env"
  note ei = "1.prems"(1)
  note prems = "1.prems"(2-)
  from prems(2) obtain W where T0: "T0 = tnorm ?\<theta> T \<rightarrow>\<^sub>T W" and cT: "cert_typ alg ar (tnorm ?\<theta> T)"
    and tb1: "e0\<langle>0:tnorm ?\<theta> T\<rangle> \<turnstile> inst (rho0 env) body1 : W"
    by auto
  from prems(3) obtain W' where T0': "T0 = tnorm ?\<theta> U \<rightarrow>\<^sub>T W'"
    and tb2: "e0\<langle>0:tnorm ?\<theta> U\<rangle> \<turnstile> inst (rho0 env) body2 : W'"
    by auto
  have TU: "tnorm ?\<theta> T = tnorm ?\<theta> U" and WW: "W' = W" using T0 T0' by simp_all
  have tvT: "tvars T \<subseteq> tvars_env ?\<theta> \<union> A" "tvars U \<subseteq> tvars_env ?\<theta> \<union> A"
    using prems(6) by auto
  have cu: "cunify_types al T U env = returnW env"
    by (rule sc_cunify_types_same[OF einvD(2)[OF ei] tvT TU])
  have r: "new_dpair al rb (Abs a T body1) (Abs b U body2) env = new_dpair al ((c, T) # rb) body1 body2 env"
    by (simp add: cu c_def)
  have okc: "okW (cunify_types al T U env) env" by (simp add: cu)
  have bs1: "bs_env (rho0 env) (e0\<langle>0:tnorm ?\<theta> T\<rangle>) ((c, T) # rb)"
    using bs_env_Cons[OF prems(1), of T c] cT by simp
  have tb2': "e0\<langle>0:tnorm ?\<theta> T\<rangle> \<turnstile> inst (rho0 env) body2 : W" using tb2 TU WW by simp
  have n1: "nabs body1 = arity W" "nabs body2 = arity W" using prems(4,5) T0 by simp_all
  have tv1: "ttvars body1 \<union> ttvars body2 \<subseteq> tvars_env ?\<theta> \<union> A" using prems(6) by auto
  note IH = "1.IH"[OF okc c_def ei bs1 tb1 tb2' n1 tv1]
  show ?case unfolding r
  proof (rule ncu_mono'[OF IH])
    fix x assume x: "case x of (dp', env') \<Rightarrow> env' = env \<and> hsat0 env dp' \<and>
      (\<forall>\<rho> \<sigma> e V. wt_subst \<sigma> \<longrightarrow> e \<turnstile> inst \<rho> body1 : V \<longrightarrow> e \<turnstile> inst \<rho> body2 : V \<longrightarrow>
        ap \<rho> \<sigma> body1 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body2 \<longrightarrow> dsolved \<rho> \<sigma> [dp'])"
    obtain dp' env' where xe: "x = (dp', env')" by (cases x)
    have "dsolved \<rho> \<sigma> [dp']"
      if \<sigma>: "wt_subst \<sigma>" and ty1: "e \<turnstile> inst \<rho> (Abs a T body1) : V" and ty2: "e \<turnstile> inst \<rho> (Abs b U body2) : V"
        and eq: "ap \<rho> \<sigma> (Abs a T body1) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs b U body2)" for \<rho> \<sigma> e V
    proof -
      from ty1 obtain Y where V: "V = tsubst \<rho> T \<rightarrow>\<^sub>T Y" and y1: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> body1 : Y" by auto
      from ty2 obtain Y' where V': "V = tsubst \<rho> U \<rightarrow>\<^sub>T Y'" and y2: "e\<langle>0:tsubst \<rho> U\<rangle> \<turnstile> inst \<rho> body2 : Y'" by auto
      have tu: "tsubst \<rho> U = tsubst \<rho> T" "Y' = Y" using V V' by simp_all
      have "e \<turnstile> Abs a (tsubst \<rho> T) (ap \<rho> \<sigma> body1) : V" "e \<turnstile> Abs b (tsubst \<rho> U) (ap \<rho> \<sigma> body2) : V"
        using typing_ap[OF ty1 \<sigma>] typing_ap[OF ty2 \<sigma>] by simp_all
      from conv_Abs_inv(2)[OF this] eq have "ap \<rho> \<sigma> body1 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body2" by simp
      moreover have "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> body2 : Y" using y2 tu by simp
      ultimately show ?thesis using x xe \<sigma> y1 by blast
    qed
    with x xe show "case x of (dp', env') \<Rightarrow> env' = env \<and> hsat0 env dp' \<and>
      (\<forall>\<rho> \<sigma> e V. wt_subst \<sigma> \<longrightarrow> e \<turnstile> inst \<rho> (Abs a T body1) : V \<longrightarrow> e \<turnstile> inst \<rho> (Abs b U body2) : V \<longrightarrow>
        ap \<rho> \<sigma> (Abs a T body1) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs b U body2) \<longrightarrow> dsolved \<rho> \<sigma> [dp'])"
      by blast
  qed
qed ((rule new_dpair_complete_base, assumption+, simp, simp) | simp)+

lemma head_norm_dpair_complete:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
    and inv: "scinv \<rho> \<sigma> env [(rb, t, u)] X A"
  shows "ncu (head_norm_dpair alg env (rb, t, u)) (\<lambda>(dp', env'). env' = env \<and> hsat0 env dp' \<and> dsolved \<rho> \<sigma> [dp'])"
proof -
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and i = scinvD[OF inv]
  from hn_term[OF ei wi p] obtain t1 u1 where
    h: "head_norm env t = return t1" "head_norm env u = return u1" "upok A env rb X t1 u1" by blast
  note pd1 = upokD[OF h(3)]
  from pd1(9)[OF r0] obtain e0 T where T: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t1 : T" "e0 \<turnstile> inst ?\<rho> u1 : T"
    by blast
  have tv1: "ttvars t1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" "ttvars u1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
    using pd1(3-5) by blast+
  from eta_norm_term[OF e(2) refl T(2) T(1) pd1(7) tv1(1)] obtain t2 where
    t2: "eta_norm env rb t1 = return t2" "ttvars t2 \<subseteq> tvars_env ?\<theta> \<union> A" "nabs t2 = arity T"
    by blast
  from eta_norm_term[OF e(2) refl T(3) T(1) pd1(8) tv1(2)] obtain u2 where
    u2: "eta_norm env rb u1 = return u2" "ttvars u2 \<subseteq> tvars_env ?\<theta> \<union> A" "nabs u2 = arity T"
    by blast
  note Et = eta_norm_sound[OF t2(1)[unfolded return_def]] and Eu = eta_norm_sound[OF u2(1)[unfolded return_def]]
  have ty2: "e0 \<turnstile> inst ?\<rho> t2 : T" "e0 \<turnstile> inst ?\<rho> u2 : T"
    using Et Eu r0(1) T pd1(7,8) by blast+
  have hd: "head_norm_dpair alg env (rb, t, u) = new_dpair alg rb t2 u2 env"
    by (simp add: head_norm_dpair_def h(1,2) t2(1) u2(1))
  have ct: "tconv env rb t t2"
    by (rule tconv_trans[OF head_norm_tconv eta_norm_tconv]) (use h(1) t2(1) in \<open>simp_all add: return_def\<close>)
  have cu: "tconv env rb u u2"
    by (rule tconv_trans[OF head_norm_tconv eta_norm_tconv]) (use h(2) u2(1) in \<open>simp_all add: return_def\<close>)
  from i(6) obtain e' T' where ty: "bs_env \<rho> e' rb" "e' \<turnstile> inst \<rho> t : T'" "e' \<turnstile> inst \<rho> u : T'"
    and lb: "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)"
    by auto
  have tsol: "tsol ?\<theta> \<rho>" by (rule solutionD(2)[OF i(1)])
  from ct tsol i(2) ty(1,2) lb(1) have rt: "e' \<turnstile> inst \<rho> t2 : T'" "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t2"
    using i(1) unfolding tconv_def by blast+
  from cu tsol i(2) ty(1,3) lb(2) have ru: "e' \<turnstile> inst \<rho> u2 : T'" "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2"
    using i(1) unfolding tconv_def by blast+
  have eq2: "ap \<rho> \<sigma> t2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2"
    using rt(2) ru(2) i(7) by (simp, meson conv_sym conv_trans)
  have \<sigma>: "wt_subst \<sigma>" by (rule solutionD(3)[OF i(1)])
  show ?thesis unfolding hd
    by (rule ncu_mono'[OF new_dpair_complete[OF ei T(1) ty2 t2(3) u2(3)]]) (use t2(2) u2(2) \<sigma> rt(1) ru(1) eq2 in auto)
qed


subsection \<open>Pairs and the invariant of pattern unification\<close>

text \<open>A pair of the invariant satisfies the invariant \<^const>\<open>cinv\<close> of the completeness proof of
  pattern unification:\<close>

lemma scinv_cinv:
  assumes inv: "scinv \<rho> \<sigma> env [(rb, t, u)] X A" and p: "upok A env rb X t u"
  obtains e T where "cinv \<rho> \<sigma> env e rb (X \<union> evars env) A" "cterm \<rho> env e rb A t T" "cterm \<rho> env e rb A u T"
    "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" "vars t \<union> vars u \<subseteq> X \<union> evars env"
proof -
  note i = scinvD[OF inv] and pd = upokD[OF p]
  from i(6) obtain e T where ty: "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T" by auto
  have vi: "vinv \<rho> env (X \<union> evars env)" using vinv_hn[of \<rho> env X X "evars env"] i(3) by simp
  have "cinv \<rho> \<sigma> env e rb (X \<union> evars env) A"
    using i(1,2,4) ty(1) vi pd(5,6) vtvars_evars[OF i(4)] unfolding cinv_def by auto
  moreover have "cterm \<rho> env e rb A t T" "cterm \<rho> env e rb A u T"
    using ty pd(3,4,7,8) by (simp_all add: cterm_def)
  moreover have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using i(7) by simp
  ultimately show ?thesis using that pd(1,2) by blast
qed


subsection \<open>Type unification\<close>

lemma sc_cunify_ncu:
  "no_unif (unify_types alg' T U env) \<Longrightarrow> ncu (cunify_types alg' T U env) (\<lambda>env'. ok (unify_types alg' T U env) env')"
  unfolding ncu_def cunify_types_def
  by (auto simp: xok_def emit_def bindW_def raiseW_def returnW_def split: option.splits res.splits exn.splits)

text \<open>Unifying two types that are equal in the solution keeps a solution, and the invariant:\<close>

lemma sc_cunify_complete:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and p: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar T"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar U"
    and eq: "tsubst \<rho> T = tsubst \<rho> U"
  shows "ncu (cunify_types alg T U env) (\<lambda>env'. \<exists>\<rho>'. scinv \<rho>' \<sigma> env' dps X A \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env' \<and> tenv env' = tenv env \<and>
    textends (tyenv env) (tyenv env'))"
proof -
  note i = scinvD[OF inv]
  note sd = solutionD[OF i(1)]
  note uc = unify_types_complete[OF i(4) T U sd(1,2) eq]
  show ?thesis
  proof (rule ncu_mono[OF sc_cunify_ncu[OF uc(1)]])
    fix env' assume cu: "okW (cunify_types alg T U env) env'" and ut: "ok (unify_types alg T U env) env'"
    obtain \<rho>' where \<rho>': "wsinst alg \<rho>'" "tsol (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
      and tv: "tvinv A env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
      using uc(2)[OF ut] by blast
    note us = unify_types_sound[OF ut]
    have sol: "solution \<rho>' \<sigma> env'" by (rule solution_tyenv[OF i(1) i(4) i(3) \<rho>' us(1)])
    have st: "dstep env dps env' dps" by (rule cunify_types_dstep[OF cu])
    have ds: "dsolved \<rho>' \<sigma> dps" by (rule sc_dps_agree(2)[OF p i(4) i(3) \<rho>'(3) sagree_refl i(7)])
    have "scinv \<rho>' \<sigma> env' dps X A" by (rule scinv_step[OF inv p st sol \<rho>'(3) sagree_refl ds tv])
    moreover have "maxidx env \<le> maxidx env'" "textends (tyenv env) (tyenv env')"
      using us(2) by (simp_all add: extends_def)
    ultimately show "\<exists>\<rho>'. scinv \<rho>' \<sigma> env' dps X A \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env' \<and> tenv env' = tenv env \<and>
      textends (tyenv env) (tyenv env')"
      using \<rho>'(3) tv(2) us(1) by blast
  qed
qed

text \<open>The body type of a type, in the most general solution, is not a function type:\<close>

lemma sc_body_type_arity:
  assumes "body_type env T = Some r" "tacyc (tyenv env)"
  shows "r = Ok B \<Longrightarrow> arity (tnorm (tyenv env) B) = 0"
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2)
  show ?case
  proof (cases T)
    case (Type a Us)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Us = [T1, U])")
      case True
      then obtain T1 U where "Us = [T1, U]" "a = STR ''fun''" by blast
      with h Type have "ok (bt env U) B" by simp
      from "1.IH"[OF this refl ac] show ?thesis .
    next
      case False
      with h Type have "B = T" by (auto split: list.splits if_splits)
      with Type False show ?thesis by (simp add: arity_other)
    qed
  next
    case (TVar v S)
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v S) lr"
      and rest: "ok (case lr of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr have "vt_lookup (tyenv env) v = None"
        by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)
      moreover from rest None TVar have "B = TVar v S" by simp
      ultimately show ?thesis by (simp add: tnorm_TVar[OF ac])
    next
      case (Some T')
      with rest have "ok (bt env T') B" by simp
      from "1.IH"[OF this refl ac] show ?thesis .
    qed
  next
    case (TFree a S)
    with h have "B = TFree a S" by simp
    then show ?thesis by simp
  qed
qed

lemma sc_funs_arity_eq: "Us \<Rrightarrow> T = Vs \<Rrightarrow> U \<Longrightarrow> arity T = 0 \<Longrightarrow> arity U = 0 \<Longrightarrow> T = U"
proof (induction Us arbitrary: Vs)
  case Nil
  then show ?case by (cases Vs) auto
next
  case (Cons W Us)
  then show ?case by (cases Vs) auto
qed

text \<open>The body type of the type of a flexible head is the common type of the pair:\<close>

lemma hsat0_body_type:
  assumes ei: "einv A K env" and hs: "hsat0 env (rb, t, u)"
  obtains e0 T0 where "bs_env (rho0 env) e0 rb" "e0 \<turnstile> inst (rho0 env) t : T0" "e0 \<turnstile> inst (rho0 env) u : T0"
    "arity T0 = 0"
    "\<And>F Ft B. head_of t = Var F Ft \<Longrightarrow> tvars Ft \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> ok (body_type env Ft) B \<Longrightarrow>
      tnorm (tyenv env) B = T0"
    "\<And>F Ft B. head_of u = Var F Ft \<Longrightarrow> tvars Ft \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> ok (body_type env Ft) B \<Longrightarrow>
      tnorm (tyenv env) B = T0"
proof -
  let ?\<theta> = "tyenv env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  from hs obtain e0 T0 where h: "bs_env (rho0 env) e0 rb" "e0 \<turnstile> inst (rho0 env) t : T0"
    "e0 \<turnstile> inst (rho0 env) u : T0" "arity T0 = 0"
    unfolding hsat0_def by blast
  have "tnorm ?\<theta> B = T0" if hd: "head_of s = Var F Ft" and tv: "tvars Ft \<subseteq> tvars_env ?\<theta> \<union> A"
    and bt: "ok (body_type env Ft) B" and tys: "e0 \<turnstile> inst (rho0 env) s : T0" for s F Ft B
  proof -
    define ss where "ss = snd (strip_comb s)"
    have tt: "s = Var F Ft \<degree>\<degree> ss" using t_apps[of s] hd by (simp add: ss_def)
    have "inst (rho0 env) s = Var F (tnorm ?\<theta> Ft) \<degree>\<degree> map (inst (rho0 env)) ss"
      by (simp add: tt inst_apps)
    then have "e0 \<turnstile> Var F (tnorm ?\<theta> Ft) \<degree>\<degree> map (inst (rho0 env)) ss : T0"
      using tys by simp
    then obtain Us where "e0 \<turnstile> Var F (tnorm ?\<theta> Ft) : Us \<Rrightarrow> T0" by (rule list_app_typeE)
    then have F1: "tnorm ?\<theta> Ft = Us \<Rrightarrow> T0" by auto
    from binder_types_term[OF e(2) refl tv] obtain Ts where bts: "binder_types env Ft = return Ts" by blast
    have "tsubst (rho0 env) Ft = map (tsubst (rho0 env)) Ts \<Rrightarrow> tsubst (rho0 env) B"
      by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt r0(1)])
    moreover have "map (tsubst (rho0 env)) Ts = map (tnorm ?\<theta>) Ts" by (induction Ts) simp_all
    ultimately have F2: "tnorm ?\<theta> Ft = map (tnorm ?\<theta>) Ts \<Rrightarrow> tnorm ?\<theta> B" by simp
    have "arity (tnorm ?\<theta> B) = 0" by (rule sc_body_type_arity[OF bt e(6) refl])
    with F1 F2 h(4) show ?thesis using sc_funs_arity_eq[of Us T0 "map (tnorm ?\<theta>) Ts" "tnorm ?\<theta> B"] by simp
  qed
  with h that show ?thesis by blast
qed


subsection \<open>The rigid occurs check\<close>

text \<open>
  The rigid occurs check \<^const>\<open>rocc\<close> of \<open>unify.ML\<close> follows the bindings of variables and of
  the heads of applications. A rigid occurrence of \<open>v\<close> bounds the measure \<^const>\<open>ld\<close> of the
  normal forms of the instances of the term from below by that of the value of \<open>v\<close>, as for the
  occurs check of pattern unification (theory \<^theory>\<open>Pattern_Correctness.Pattern_Occurs\<close>).
\<close>

lemma sc_occomb_rigid:
  assumes "\<not> (\<exists>f a. h0 = f $ a)"
  shows "ok (occomb oc seen (h0 \<degree>\<degree> ts)) (Rigid, s') \<Longrightarrow>
    (\<exists>seen' s''. ok (oc seen' h0) (Rigid, s'')) \<or> (\<exists>i<length ts. \<exists>seen' s''. ok (oc seen' (ts ! i)) (Rigid, s''))"
proof (induction ts arbitrary: seen s' rule: rev_induct)
  case Nil
  then show ?case using assms by (cases h0) auto
next
  case (snoc a ts)
  have "occomb oc seen (h0 \<degree>\<degree> (ts @ [a])) = do {
      r \<leftarrow> oc seen a;
      if fst r = Rigid then return (Rigid, snd r)
      else do {r2 \<leftarrow> occomb oc (snd r) (h0 \<degree>\<degree> ts); return (if fst r2 = NoOcc then fst r else fst r2, snd r2)}}"
    by simp
  with snoc.prems obtain r where r: "ok (oc seen a) r"
    and rest: "ok (if fst r = Rigid then return (Rigid, snd r)
      else do {r2 \<leftarrow> occomb oc (snd r) (h0 \<degree>\<degree> ts); return (if fst r2 = NoOcc then fst r else fst r2, snd r2)})
      (Rigid, s')"
    by auto
  show ?case
  proof (cases "fst r = Rigid")
    case True
    with r have "ok (oc seen ((ts @ [a]) ! length ts)) (Rigid, snd r)" by (cases r) simp
    then show ?thesis by fastforce
  next
    case False
    with rest obtain r2 where r2: "ok (occomb oc (snd r) (h0 \<degree>\<degree> ts)) r2"
      and e: "(if fst r2 = NoOcc then fst r else fst r2) = Rigid" by auto
    have "fst r2 = Rigid" using e False by (auto split: if_splits)
    then have "ok (occomb oc (snd r) (h0 \<degree>\<degree> ts)) (Rigid, snd r2)" using r2 by (cases r2) simp
    from snoc.IH[OF this] show ?thesis by (auto simp: nth_append) (metis less_SucI)
  qed
qed

lemma sc_head_of_in_apps: "head_of_in env (s \<degree>\<degree> ts) = head_of_in env s"
proof (induction ts arbitrary: s)
  case (Cons t ts)
  have "head_of_in env (s $ t) = head_of_in env s" by (subst head_of_in.simps) simp
  with Cons.IH[of "s $ t"] show ?case by simp
qed simp

lemma sc_head_of_in_rigid: "rigid h \<Longrightarrow> head_of_in env h = return h"
  by (subst head_of_in.simps) (cases h, simp_all)

lemma sc_nonrigid_not_Rigid: "\<not> ok (nonrigid env v seen t) (Rigid, s)"
  by (auto simp: nonrigid_def split: prod.splits)

lemma typings_nthI: "length ts = length Ts \<Longrightarrow> (\<And>i. i < length ts \<Longrightarrow> e \<turnstile> ts ! i : Ts ! i) \<Longrightarrow> e \<tturnstile> ts : Ts"
proof (induction ts arbitrary: Ts)
  case (Cons t ts)
  then obtain U Us where "Ts = U # Us" by (cases Ts) auto
  with Cons show ?case by (fastforce simp: nth_Cons')
qed simp

text \<open>A term whose head, after following the bindings, is rigid has instances that are equivalent to
  \<open>\<beta>\<close>-normal terms that are not abstractions:\<close>

lemma sc_head_of_in_sem:
  assumes "head_of_in env t = Some r"
  shows "r = Ok h \<Longrightarrow> \<not> is_Var h \<Longrightarrow> \<not> is_Abs h \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow>
    e \<turnstile> inst \<rho> t : T \<Longrightarrow> \<exists>M. no_redex M \<and> \<not> is_Abs M \<and> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M \<and> e \<turnstile> M : T"
  using assms
proof (induction env t r arbitrary: e T rule: head_of_in.raw_induct[rotated, consumes 1])
  case (1 hi env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note sol = "1.prems"(4) and wte = "1.prems"(5) and ty = "1.prems"(6)
  have \<sigma>: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  have IH: "\<exists>M. no_redex M \<and> \<not> is_Abs M \<and> ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M \<and> e' \<turnstile> M : T'"
    if "ok (hi env t') h" "e' \<turnstile> inst \<rho> t' : T'" for t' e' T'
    using "1.IH"[OF that(1) refl "1.prems"(2,3) sol wte that(2)] .
  show ?case
  proof (cases t)
    case (App f a)
    with h have hf: "ok (hi env f) h" by simp
    from ty App obtain U where tf: "e \<turnstile> inst \<rho> f : U \<rightarrow>\<^sub>T T" and ta: "e \<turnstile> inst \<rho> a : U" by auto
    from IH[OF hf tf] obtain Mf where Mf: "no_redex Mf" "\<not> is_Abs Mf" "ap \<rho> \<sigma> f \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Mf"
      "e \<turnstile> Mf : U \<rightarrow>\<^sub>T T" by blast
    have taa: "e \<turnstile> ap \<rho> \<sigma> a : U" by (rule typing_ap[OF ta \<sigma>])
    obtain Ma where Ma: "ap \<rho> \<sigma> a \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Ma" "normal Ma" using normal_form_ex[OF taa] .
    have tMa: "e \<turnstile> Ma : U" by (rule subject_reduction_reds[OF Ma(1) taa])
    have cMa: "ap \<rho> \<sigma> a \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ma" using beta_eta_conv[OF Ma(1)] taa by (auto simp: wt_def)
    have tM: "e \<turnstile> Mf $ Ma : T" using Mf(4) tMa by auto
    have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Mf $ Ma"
      using conv_App[OF _ _ Mf(3) cMa] typing_ap[OF ty \<sigma>] tM App by (auto simp: wt_def)
    moreover have "no_redex (Mf $ Ma)" using Mf(1,2) Ma(2) by (cases Mf) (auto simp: normal_iff)
    moreover have "\<not> is_Abs (Mf $ Ma)" by simp
    ultimately show ?thesis using tM by blast
  next
    case (Var x Tx)
    with h obtain lr where lr: "ok (lookup env x Tx) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hi env u | None \<Rightarrow> return t) h" by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest Var have "h = Var x Tx" by simp
      with "1.prems"(2) show ?thesis by simp
    next
      case (Some u)
      with rest have hu: "ok (hi env u) h" by simp
      note l = lookup_sound[OF lr[unfolded Some] solutionD(2)[OF sol] wte]
      from ty Var have T: "T = tsubst \<rho> Tx" by auto
      from IH[OF hu l(2)[of e, folded T]] obtain M where M: "no_redex M" "\<not> is_Abs M"
        "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M" "e \<turnstile> M : T" by blast
      have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M" using l(1)[OF sol] M(3) Var by (blast intro: conv_trans)
      with M show ?thesis by blast
    qed
  next
    case (Abs a A b)
    with h have "h = t" by simp
    with "1.prems"(3) Abs show ?thesis by simp
  next
    case (Const c Tc)
    have "ap \<rho> \<sigma> t = inst \<rho> t" using Const by simp
    then show ?thesis using ty Const by (intro exI[of _ "inst \<rho> t"]) simp
  next
    case (Free c Tc)
    have "ap \<rho> \<sigma> t = inst \<rho> t" using Free by simp
    then show ?thesis using ty Free by (intro exI[of _ "inst \<rho> t"]) simp
  next
    case (Bound i)
    have "ap \<rho> \<sigma> t = inst \<rho> t" using Bound by simp
    then show ?thesis using ty Bound by (intro exI[of _ "inst \<rho> t"]) simp
  qed
qed

lemma sc_list_all_is_Bound: "list_all is_Bound ts \<Longrightarrow> ts = map Bound (map (\<lambda>t. case t of Bound i \<Rightarrow> i | _ \<Rightarrow> 0) ts)"
  by (induction ts) (auto elim: is_Bound.elims)

lemma sc_rocc_ld:
  assumes "rocc t env v seen = Some r"
  shows "r = Ok (Rigid, s') \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> vinv \<rho> env X \<Longrightarrow> (v, Fty) \<in> X \<Longrightarrow>
    vars t \<subseteq> X \<union> evars env \<Longrightarrow> e \<turnstile> inst \<rho> t : T \<Longrightarrow>
    \<sigma> v (tsubst \<rho> Fty) \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* nF \<Longrightarrow> normal nF \<Longrightarrow> cert_typ alg ar (tsubst \<rho> Fty) \<Longrightarrow>
    normal N \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N \<Longrightarrow> e \<turnstile> N : T \<Longrightarrow> ld e0 nF (tsubst \<rho> Fty) \<le> ld e N T"
  using assms
proof (induction t env v seen r arbitrary: s' e T N rule: rocc.raw_induct[rotated, consumes 1])
  case (1 ro t env v seen r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note sol = "1.prems"(2) and wte = "1.prems"(3) and vi = "1.prems"(4) and FX = "1.prems"(5)
    and Xt = "1.prems"(6) and ty = "1.prems"(7) and nF = "1.prems"(8,9) and cF = "1.prems"(10)
    and N = "1.prems"(11-13)
  have \<sigma>: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  have IH: "ld e0 nF (tsubst \<rho> Fty) \<le> ld e' N' T'"
    if "ok (ro t' env v seen') (Rigid, s'')" "vars t' \<subseteq> X \<union> evars env" "e' \<turnstile> inst \<rho> t' : T'" "normal N'"
      "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N'" "e' \<turnstile> N' : T'" for t' seen' s'' e' T' N'
    using "1.IH"[OF that(1) refl sol wte vi FX that(2,3) nF cF that(4-6)] .
  let ?u = "\<sigma> v (tsubst \<rho> Fty)"
  have cu: "closed ?u" using \<sigma> by (cases v) (simp add: wt_subst_def closed_subst_def)
  have FG: "tsubst \<rho> G = tsubst \<rho> Fty" if "(v, G) \<in> X \<union> evars env" for G
    using vi FX that unfolding vinv_def by (blast dest: vconsD)
  show ?case
  proof (cases t)
    case (Var w Tw)
    show ?thesis
    proof (cases "w \<in> set seen")
      case True
      with h Var show ?thesis by simp
    next
      case nseen: False
      show ?thesis
      proof (cases "v = w")
        case True
        have G: "tsubst \<rho> Tw = tsubst \<rho> Fty" using FG Xt Var True by simp
        from ty Var have T: "T = tsubst \<rho> Tw" by auto
        have tu: "e' \<turnstile> ?u : map e [] \<Rrightarrow> T" for e' using wt_subst_typing[OF \<sigma> cF] G T by simp
        have "?u \<degree>\<degree> map Bound [] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using N(2) Var True G by simp
        from ld_flex[OF cu tu _ nF _ N(1,3) this, of e0] G T show ?thesis by simp
      next
        case vw: False
        with h Var nseen obtain lr where lr: "ok (lookup env w Tw) lr"
          and rest: "ok (case lr of None \<Rightarrow> return (NoOcc, w # seen) | Some u \<Rightarrow> ro u env v (w # seen))
            (Rigid, s')"
          by auto
        show ?thesis
        proof (cases lr)
          case None
          with rest show ?thesis by simp
        next
          case (Some u)
          with rest have ru: "ok (ro u env v (w # seen)) (Rigid, s')" by simp
          from lr Some obtain U where b: "vt_lookup (tenv env) w = Some (U, u)" by (auto elim: ok_lookup_Some)
          note l = lookup_sound[OF lr[unfolded Some] solutionD(2)[OF sol] wte]
          from ty Var have T: "T = tsubst \<rho> Tw" by auto
          have "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using l(1)[OF sol] N(2) Var by (blast intro: conv_sym conv_trans)
          from IH[OF ru _ l(2)[of e, folded T] N(1) this N(3)] evarsI2[OF b] show ?thesis by blast
        qed
      qed
    qed
  next
    case (Abs a A b)
    from h Abs have rb: "ok (ro b env v seen) (Rigid, s')" by simp
    from ty Abs obtain U where T: "T = tsubst \<rho> A \<rightarrow>\<^sub>T U" and cA: "cert_typ alg ar (tsubst \<rho> A)"
      and tb: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> inst \<rho> b : U"
      by auto
    have tab: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> ap \<rho> \<sigma> b : U" by (rule typing_ap[OF tb \<sigma>])
    obtain Nb where Nb: "ap \<rho> \<sigma> b \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Nb" "normal Nb" using normal_form_ex[OF tab] .
    have tNb: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> Nb : U" by (rule subject_reduction_reds[OF Nb(1) tab])
    have cb: "ap \<rho> \<sigma> b \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Nb" using beta_eta_conv[OF Nb(1)] tab by (auto simp: wt_def)
    have K: "ld e0 nF (tsubst \<rho> Fty) \<le> ld (e\<langle>0:tsubst \<rho> A\<rangle>) Nb U"
      by (rule IH[OF rb _ tb Nb(2) cb tNb]) (use Xt Abs in simp)
    have tM: "e \<turnstile> Abs a (tsubst \<rho> A) Nb : T" using tNb cA T by auto
    have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> A) Nb"
      using conv_Abs[OF _ _ cb, of a "tsubst \<rho> A" a] typing_ap[OF ty \<sigma>] tM Abs
      by (auto simp: wt_def)
    then have "N \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> A) Nb" using N(2) by (blast intro: conv_sym conv_trans)
    then have "ld e N T = ld e (Abs a (tsubst \<rho> A) Nb) T"
      by (rule ld_conv[OF _ N(3) tM]) (use N(1) Nb(2) in \<open>simp_all add: normal_iff\<close>)
    with K T show ?thesis by simp
  next
    case (App f a0)
    from h App obtain hd where hd: "ok (head_of_in env f) hd"
      and rest: "ok (case hd of
          Var w _ \<Rightarrow> if v = w \<and> pattern_occ v t then return (Rigid, seen) else nonrigid env v seen t
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen t
        | _ \<Rightarrow> occomb (\<lambda>seen t. ro t env v seen) seen t) (Rigid, s')"
      by (auto simp del: occomb.simps)
    obtain h0 ts where hts: "strip_comb t = (h0, ts)" by force
    have t: "t = h0 \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
    have h0A: "\<not> (\<exists>f a. h0 = f $ a)" by (rule strip_comb_head[OF hts])
    show ?thesis
    proof (cases "is_Var hd")
      case True
      then obtain w Wt where hw: "hd = Var w Wt" by (cases hd) auto
      from rest hw sc_nonrigid_not_Rigid have po: "pattern_occ v t" by (auto split: if_splits)
      then obtain Gty where h0v: "h0 = Var v Gty" and bs: "list_all is_Bound ts"
        using hts by (auto simp: pattern_occ_def split: pterm.splits)
      define js where "js = map (\<lambda>t. case t of Bound i \<Rightarrow> i | _ \<Rightarrow> 0) ts"
      have tj: "t = app (Var v Gty) js" using t h0v sc_list_all_is_Bound[OF bs] by (simp add: js_def app_apps)
      from ty[unfolded tj] obtain Gty_eq: "tsubst \<rho> Gty = map e js \<Rrightarrow> T" and js0: "\<forall>j\<in>set js. 0 \<le> j"
        by (rule typing_appE)
      have G: "tsubst \<rho> Gty = tsubst \<rho> Fty" using FG Xt tj by (simp add: app_apps vars_apps)
      have tu: "e' \<turnstile> ?u : map e js \<Rrightarrow> T" for e' using wt_subst_typing[OF \<sigma> cF] G Gty_eq by simp
      have eqF: "tsubst \<rho> Fty = map e js \<Rrightarrow> T" using G Gty_eq by simp
      have certs: "\<forall>j\<in>set js. cert_typ alg ar (e j)" using cF[unfolded eqF] by (simp add: cert_typ_funs)
      have "ap \<rho> \<sigma> t = ?u \<degree>\<degree> map Bound js" using G tj by (simp add: app_apps ap_apps comp_def)
      then have "?u \<degree>\<degree> map Bound js \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using N(2) by simp
      from ld_flex[OF cu tu certs nF js0 N(1,3) this, of e0] eqF show ?thesis by simp
    next
      case nV: False
      show ?thesis
      proof (cases "is_Abs hd")
        case True
        with rest sc_nonrigid_not_Rigid show ?thesis by (cases hd) auto
      next
        case nA: False
        have oc: "ok (occomb (\<lambda>seen t. ro t env v seen) seen t) (Rigid, s')"
          using rest nV nA by (cases hd) auto
        have hd0: "ok (head_of_in env h0) hd"
        proof -
          have "head_of_in env t = head_of_in env f" using App by (subst head_of_in.simps) simp
          with hd sc_head_of_in_apps[of env h0 ts] t show ?thesis by simp
        qed
        from ty t have "e \<turnstile> inst \<rho> h0 \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: inst_apps)
        then obtain Ts where th0: "e \<turnstile> inst \<rho> h0 : Ts \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Ts"
          by (rule list_app_typeE)
        note tn = typings_nth[OF tts]
        have lenT: "length Ts = length ts" using tn by simp
        from sc_head_of_in_sem[OF hd0 refl nV nA sol wte th0] obtain M where
          M: "no_redex M" "\<not> is_Abs M" "ap \<rho> \<sigma> h0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M" "e \<turnstile> M : Ts \<Rrightarrow> T" by blast
        have tya: "e \<turnstile> ap \<rho> \<sigma> (ts ! i) : Ts ! i" if "i < length ts" for i
          using typing_ap[of e \<rho> "ts ! i" "Ts ! i" \<sigma>] tn that \<sigma> by simp
        have wts: "\<forall>t\<in>set (map (ap \<rho> \<sigma>) ts). wt t"
        proof
          fix t assume "t \<in> set (map (ap \<rho> \<sigma>) ts)"
          then obtain i where "i < length ts" "t = ap \<rho> \<sigma> (ts ! i)" by (auto simp: in_set_conv_nth)
          then show "wt t" using tya by (auto simp: wt_def)
        qed
        obtain Ns where Ns: "list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<and> normal N) (map (ap \<rho> \<sigma>) ts) Ns"
          using normal_forms_list[OF wts] by blast
        have lenN: "length Ns = length ts" using list_all2_lengthD[OF Ns] by simp
        have Nsi: "ap \<rho> \<sigma> (ts ! i) \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Ns ! i" "normal (Ns ! i)" if "i < length ts" for i
          using list_all2_nthD[OF Ns, of i] that by simp_all
        have tNs: "e \<turnstile> Ns ! i : Ts ! i" if "i < length ts" for i
          by (rule subject_reduction_reds[OF Nsi(1)[OF that] tya[OF that]])
        have cNs: "ap \<rho> \<sigma> (ts ! i) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ns ! i" if "i < length ts" for i
          using beta_eta_conv[OF Nsi(1)[OF that]] tya[OF that] by (auto simp: wt_def)
        let ?M = "M \<degree>\<degree> Ns"
        have tyM: "e \<turnstile> ?M : T"
          by (rule list_app_typeI[OF M(4) typings_nthI]) (use lenN lenT tNs in simp_all)
        have nrM: "no_redex ?M"
        proof (subst no_redex_apps[OF M(2)])
          have "\<forall>N\<in>set Ns. normal N" using Nsi lenN by (auto simp: in_set_conv_nth)
          then show "no_redex M \<and> (\<forall>t\<in>set Ns. no_redex t)" using M(1) by (auto simp: normal_iff)
        qed
        have apt: "ap \<rho> \<sigma> t = ap \<rho> \<sigma> h0 \<degree>\<degree> map (ap \<rho> \<sigma>) ts" by (simp add: t ap_apps)
        have cM: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?M" unfolding apt
        proof (rule conv_apps[OF _ _ _ M(3)])
          show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) ts) Ns"
            using cNs lenN by (simp add: list_all2_conv_all_nth)
          show "wt (ap \<rho> \<sigma> h0 \<degree>\<degree> map (ap \<rho> \<sigma>) ts)" using typing_ap[OF ty \<sigma>] apt by (auto simp: wt_def)
          show "wt ?M" using tyM by (auto simp: wt_def)
        qed
        have lN: "ld e N T = ld e ?M T"
          by (rule ld_conv[OF _ N(3) tyM]) (use N(1,2) cM nrM in \<open>auto simp: normal_iff intro: conv_sym conv_trans\<close>)
        have sp: "spine_type e M = Ts \<Rrightarrow> T" by (rule spine_type_typing[OF M(4,1,2)])
        note la = ld_apps[OF M(2) sp, of Ns] lenN lenT
        from sc_occomb_rigid[OF h0A oc[unfolded t]] show ?thesis
        proof (elim disjE exE conjE)
          fix seen' s'' assume r0: "ok (ro h0 env v seen') (Rigid, s'')"
          obtain Nh where Nh: "M \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Nh" "normal Nh" using normal_form_ex[OF M(4)] .
          have tNh: "e \<turnstile> Nh : Ts \<Rrightarrow> T" by (rule subject_reduction_reds[OF Nh(1) M(4)])
          have cNh: "M \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Nh" using beta_eta_conv[OF Nh(1)] M(4) by (auto simp: wt_def)
          have "ld e0 nF (tsubst \<rho> Fty) \<le> ld e Nh (Ts \<Rrightarrow> T)"
            by (rule IH[OF r0 _ th0 Nh(2) _ tNh]) (use Xt t M(3) cNh in \<open>auto simp: vars_apps intro: conv_trans\<close>)
          moreover have "ld e Nh (Ts \<Rrightarrow> T) = ld e M (Ts \<Rrightarrow> T)"
            by (rule ld_conv[OF _ tNh M(4)]) (use Nh(2) M(1) cNh in \<open>auto simp: normal_iff intro: conv_sym\<close>)
          ultimately show ?thesis using la lN by simp
        next
          fix i seen' s'' assume i: "i < length ts" and ri: "ok (ro (ts ! i) env v seen') (Rigid, s'')"
          have tyi: "e \<turnstile> inst \<rho> (ts ! i) : Ts ! i" using tn i by auto
          have "ld e0 nF (tsubst \<rho> Fty) \<le> ld e (Ns ! i) (Ts ! i)"
            by (rule IH[OF ri _ tyi Nsi(2)[OF i] cNs[OF i] tNs[OF i]])
              (use Xt t nth_mem[OF i] in \<open>auto simp: vars_apps\<close>)
          moreover have "Suc (ld e (Ns ! i) (Ts ! i)) \<le> ld e ?M T" using la i by simp
          ultimately show ?thesis using lN by simp
        qed
      qed
    qed
  qed (use h in simp_all)
qed

text \<open>A rigid occurrence makes a flex-rigid pair unsolvable:\<close>

lemma sc_rocc_atom: "rigid h \<Longrightarrow> rocc h env v seen = return (NoOcc, seen)"
  by (subst rocc.simps) (cases h, simp_all)

theorem rigid_occurs_term_Rigid:
  assumes inv: "scinv \<rho> \<sigma> env [(rb, t, u)] X A" and p: "upok A env rb X t u"
    and t: "t = app (Var v T) is" and hu: "rigid (head_of u)" and ro: "ok (rigid_occurs_term env v u) Rigid"
  shows False
proof -
  let ?X = "X \<union> evars env"
  obtain e Tp where ci: "cinv \<rho> \<sigma> env e rb ?X A" and cs: "cterm \<rho> env e rb A t Tp"
    and ct: "cterm \<rho> env e rb A u Tp" and eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and Xv: "vars t \<union> vars u \<subseteq> ?X"
    by (rule scinv_cinv[OF inv p])
  note i = ci[unfolded cinv_def]
  have sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and vi: "vinv \<rho> env ?X" using i by blast+
  have \<sigma>: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  note fd = flex_data[OF ci cs[unfolded t]]
  from ro obtain s where rs: "ok (rocc u env v []) (Rigid, s)"
    by (auto simp: rigid_occurs_term_def)
  define h where "h = head_of u"
  define ts where "ts = snd (strip_comb u)"
  have uu: "u = h \<degree>\<degree> ts" unfolding h_def ts_def by (rule t_apps)
  have rh: "rigid h" using hu by (simp add: h_def)
  have hA: "\<not> (\<exists>f a. h = f $ a)" using rh by (cases h) auto
  have "ts \<noteq> []"
  proof
    assume "ts = []"
    with uu sc_rocc_atom[OF rh, of env v "[]"] rs show False by simp
  qed
  then obtain ts' a where tsa: "ts = ts' @ [a]" by (cases ts rule: rev_exhaust) auto
  have ua: "u = (h \<degree>\<degree> ts') $ a" using uu tsa by simp
  have hi: "head_of_in env (h \<degree>\<degree> ts') = return h" using sc_head_of_in_apps sc_head_of_in_rigid[OF rh] by simp
  have "rocc u env v [] = occomb (\<lambda>seen t. rocc t env v seen) [] u"
    using rh hi unfolding ua by (subst rocc.simps) (cases h, simp_all del: occomb.simps)
  with rs have oc: "ok (occomb (\<lambda>seen t. rocc t env v seen) [] (h \<degree>\<degree> ts)) (Rigid, s)" using uu by simp
  let ?u = "\<sigma> v (tsubst \<rho> T)"
  have tyu: "e0 \<turnstile> ?u : tsubst \<rho> T" for e0 using wt_subst_typing[OF \<sigma> fd(2)] .
  obtain nF where nF: "?u \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* nF" "normal nF" using normal_form_ex[OF tyu] .
  have tyt: "e \<turnstile> inst \<rho> u : Tp" using ct by (simp add: cterm_def)
  have tat: "e \<turnstile> ap \<rho> \<sigma> u : Tp" by (rule typing_ap[OF tyt \<sigma>])
  obtain N where N: "ap \<rho> \<sigma> u \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using normal_form_ex[OF tat] .
  have tN: "e \<turnstile> N : Tp" by (rule subject_reduction_reds[OF N(1) tat])
  have cN: "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using beta_eta_conv[OF N(1)] tat by (auto simp: wt_def)
  have "?u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using eq fd(6) cN t by (metis conv_trans)
  from ld_flex[OF fd(4) fd(5) fd(8) nF _ N(2) tN this, of "(\<lambda>_. TFree STR '''' [])"] fd(1,3)
  have K: "ld e N Tp = ld (\<lambda>_. TFree STR '''' []) nF (tsubst \<rho> T)" by auto
  have tyt': "e \<turnstile> inst \<rho> (h \<degree>\<degree> ts) : Tp" using tyt uu by simp
  obtain Ts where tts: "e \<tturnstile> map (inst \<rho>) ts : Ts"
    and lt: "\<And>i Ni. i < length ts \<Longrightarrow> normal Ni \<Longrightarrow> ap \<rho> \<sigma> (ts ! i) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni \<Longrightarrow>
      Suc (ld e Ni (Ts ! i)) \<le> ld e N Tp"
    using ld_rigid[OF rh tyt' \<sigma> N(2) _ tN] cN uu by blast
  have FX: "(v, T) \<in> ?X" using Xv t by (auto simp: app_apps vars_apps)
  from sc_occomb_rigid[OF hA oc] show False
  proof (elim disjE exE conjE)
    fix seen' s'' assume "ok (rocc h env v seen') (Rigid, s'')"
    with sc_rocc_atom[OF rh] show False by simp
  next
    fix k seen' s'' assume k: "k < length ts" and rk: "ok (rocc (ts ! k) env v seen') (Rigid, s'')"
    have tyi: "e \<turnstile> inst \<rho> (ts ! k) : Ts ! k" using typings_nth[OF tts] k by auto
    have tai: "e \<turnstile> ap \<rho> \<sigma> (ts ! k) : Ts ! k" by (rule typing_ap[OF tyi \<sigma>])
    obtain Ni where Ni: "ap \<rho> \<sigma> (ts ! k) \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Ni" "normal Ni" using normal_form_ex[OF tai] .
    have tNi: "e \<turnstile> Ni : Ts ! k" by (rule subject_reduction_reds[OF Ni(1) tai])
    have cNi: "ap \<rho> \<sigma> (ts ! k) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni" using beta_eta_conv[OF Ni(1)] tai by (auto simp: wt_def)
    have vti: "vars (ts ! k) \<subseteq> ?X \<union> evars env" using Xv uu nth_mem[OF k] by (auto simp: vars_apps)
    have "ld (\<lambda>_. TFree STR '''' []) nF (tsubst \<rho> T) \<le> ld e Ni (Ts ! k)"
      by (rule sc_rocc_ld[OF rk refl sol wte vi FX vti tyi nF fd(2) Ni(2) cNi tNi])
    moreover have "Suc (ld e Ni (Ts ! k)) \<le> ld e N Tp" using lt[OF k Ni(2) cNi] .
    ultimately show False using K by simp
  qed
qed


subsection \<open>Assignments\<close>

lemma sc_bidx_downs: "0 \<le> k \<Longrightarrow> k < integer_of_nat n \<Longrightarrow> bidx (rev (map integer_of_nat [0..<n])) k = k"
proof (induction n)
  case 0
  then show ?case by (simp add: integer_arith)
next
  case (Suc n)
  show ?case
  proof (cases "k = integer_of_nat n")
    case True
    then show ?thesis by (simp add: ilength_eq)
  next
    case False
    with Suc.prems have "k < integer_of_nat n" by (simp add: integer_arith integer_of_nat_eq_of_nat)
    with Suc.IH Suc.prems(1) False show ?thesis by simp
  qed
qed

text \<open>The binding of an assignment is solved by the solution of the pair:\<close>

lemma assign_bind_sol:
  assumes ci: "cinv \<rho> \<sigma> env e rb X A" and cs: "cterm \<rho> env e rb A (app (Var v T) is) V"
    and cu: "cterm \<rho> env e rb A u V" and eq: "ap \<rho> \<sigma> (app (Var v T) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and isd: "is = rev (map integer_of_nat [0..<length rb])"
  shows "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs rb u)"
proof -
  note fd = flex_data[OF ci cs]
  have \<sigma>: "wt_subst \<sigma>" using ci solutionD(3) by (auto simp: cinv_def)
  have mb: "map (\<lambda>i. rb ! nat_of_integer i) is = rev rb"
    by (simp add: isd rev_map[symmetric] map_nth comp_def)
  have dis: "distinct is" by (simp add: isd distinct_map inj_on_def integer_of_nat_eq_of_nat)
  have is0: "\<forall>i\<in>set is. 0 \<le> i" using fd(3) by blast
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. rb ! nat_of_integer i) is)"
  let ?U = "ap \<rho> \<sigma> u"
  have tyu: "e \<turnstile> inst \<rho> u : V" and lbu: "\<not> loose_bvar u (ilength rb)" using cu by (simp_all add: cterm_def)
  have tyU0: "e \<turnstile> ?U : V" by (rule typing_ap[OF tyu \<sigma>])
  have lbU: "\<not> loose_bvar ?U (ilength rb)"
    using lbu closed_substD[of \<sigma>] \<sigma> by (simp add: ap_def wt_subst_def)
  have len: "ilength (map e is) = ilength rb" by (simp add: isd ilength_eq)
  have tyU: "pushes e (map e is) \<turnstile> ?U : V"
  proof (rule typing_env_cong[OF tyU0])
    fix k assume k: "0 \<le> k" "loose_bvar1 ?U k"
    have kl: "k < ilength rb" using loose_bvar1_less[OF lbU k(2)] .
    then have kn: "nat_of_integer k < length rb" using k(1) by (simp add: nat_of_integer_less_ilength)
    have "pushes e (map e is) k = rev (map e is) ! nat_of_integer k" using k(1) kl len by (simp add: pushes_nth)
    also have "\<dots> = e (integer_of_nat (nat_of_integer k))" using kn by (simp add: isd rev_map)
    also have "\<dots> = e k" using integer_of_nat_nat_of_integer[OF k(1)] by simp
    finally show "pushes e (map e is) k = e k" .
  qed
  obtain N0 where N0: "?U \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N0" "normal N0" using normal_form_ex[OF tyU0] .
  have lbN0: "\<not> loose_bvar N0 (ilength rb)" using lbU loose_bvar_reds[OF N0(1)] ilength_nonneg[of rb] by auto
  have c3: "\<sigma> v (tsubst \<rho> T) \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N0"
    using eq fd(6) beta_eta_conv[OF N0(1)] tyU0 by (auto simp: wt_def intro: conv_trans)
  have bF: "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs (rename (bidx is) 0 N0)"
    by (rule body_rename[OF fd(4,5) dis is0 fd(7,8) c3 N0(2)])
  have rN: "rename (bidx is) 0 N0 = N0"
  proof (rule rename_id_on[of "ilength rb"])
    fix k assume "0 \<le> k" "k < ilength rb"
    then show "bidx is k = k" using sc_bidx_downs[of k "length rb"] by (simp add: isd ilength_eq)
  qed (use lbN0 in simp)
  have tyU': "pushes e (map snd ?bs) \<turnstile> ?U : V" using tyU by (simp only: fd(7))
  have certs: "\<forall>U\<in>snd ` set ?bs. cert_typ alg ar U"
  proof -
    have "snd ` set ?bs = set (map snd ?bs)" by (simp only: set_map)
    then show ?thesis using fd(7,8) by auto
  qed
  have "e \<turnstile> abs_list ?bs ?U : map snd ?bs \<Rrightarrow> V" by (rule typing_abs_list[OF tyU' certs])
  then have "abs_list ?bs ?U \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs N0"
    by (intro beta_eta_conv reds_abs_list N0(1)) (auto simp: wt_def)
  with bF rN have "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs ?U" by (auto intro: conv_sym conv_trans)
  also have "abs_list ?bs ?U = ap \<rho> \<sigma> (rlist_abs rb u)"
    by (simp add: rlist_abs_abs_list ap_abs_list mb)
  finally show ?thesis .
qed

theorem assignment_complete:
  assumes ei: "einv A K env" and p: "upok A env rb X t u" and inv: "scinv \<rho> \<sigma> env [(rb, t, u)] X A"
    and hs: "hsat0 env (rb, t, u)" and hu: "rigid (head_of u)"
  shows "ncu (assignment alg rb t u env) (\<lambda>env'. \<exists>\<rho>'. solution \<rho>' \<sigma> env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
    tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env')"
proof (cases "get_eta_var rb 0 t = raiseW ASSIGN")
  case True
  then show ?thesis by (simp add: assignment_def)
next
  case False
  with get_eta_var_cases[of rb 0 t] obtain v T where gv: "get_eta_var rb 0 t = returnW (v, T)" by blast
  then have gev: "okW (get_eta_var rb 0 t) (v, T)" by simp
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p] and i = scinvD[OF inv]
  define "is" where "is = rev (map integer_of_nat [0..<length rb])"
  have t: "t = app (Var v T) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have ht: "head_of t = Var v T" by (simp add: t app_apps head_of_apps)
  have kT: "tvars T \<subseteq> tvars_env ?\<theta> \<union> A" using pd(3) by (simp add: t ttvars_def app_apps typs_apps)
  have asg: "assignment alg rb t u env = bindW (liftM (rigid_occurs_term env v u)) (\<lambda>oc. case oc of
      NoOcc \<Rightarrow> do {
        T1 \<leftarrow> liftM (body_type env T);
        T2 \<leftarrow> liftM (fastype env rb u);
        env' \<leftarrow> cunify_types alg T1 T2 env;
        liftM (update (v, T) (rlist_abs rb u) env')}
    | Nonrigid \<Rightarrow> raiseW ASSIGN
    | Rigid \<Rightarrow> raiseW CANTUNIFY)"
    by (simp add: assignment_def gv)
  obtain e0 T0 where h0: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t : T0" "e0 \<turnstile> inst ?\<rho> u : T0" "arity T0 = 0"
    and bt0: "\<And>F Ft B. head_of t = Var F Ft \<Longrightarrow> tvars Ft \<subseteq> tvars_env ?\<theta> \<union> A \<Longrightarrow> ok (body_type env Ft) B \<Longrightarrow>
      tnorm ?\<theta> B = T0"
    by (rule hsat0_body_type[OF ei hs]) blast
  from body_type_ok[OF ei kT head_Var_cert[OF h0(2) ht]] obtain B1 where
    b1: "body_type env T = return B1" "tvars B1 \<subseteq> tvars_env ?\<theta> \<union> A" "wft ar B1"
    by blast
  have tvu: "ttvars u \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" using pd(4,5) by blast
  from env_fastype_term[OF e(2) refl h0(3,1) pd(8) tvu] obtain B2 where
    b2: "env_fastype env (map snd rb) u = return B2" "tvars B2 \<subseteq> tvars_env ?\<theta> \<union> A" "tnorm ?\<theta> B2 = T0"
    by blast
  have c2: "cert_typ alg ar (tsubst ?\<rho> B2)" using bs_env_cert[OF h0(1,3) pd(8)] b2(3) by simp
  have w2: "wft ar B2" using cert_typ_rev[OF ei c2 b2(2)] by blast
  have n1: "tnorm ?\<theta> B1 = T0" by (rule bt0[OF ht kT]) (use b1(1) in \<open>simp add: return_def\<close>)
  have tsol: "tsol ?\<theta> \<rho>" by (rule solutionD(2)[OF i(1)])
  have eqT: "tsubst \<rho> B1 = tsubst \<rho> B2"
  proof -
    have "tsubst \<rho> B1 = tsubst \<rho> (tnorm ?\<theta> B1)"
      using tsubst_tnorm[OF e(6,7) tsol tinv_tcons[OF e(2) b1(2)]] by simp
    also have "\<dots> = tsubst \<rho> (tnorm ?\<theta> B2)" using n1 b2(3) by simp
    also have "\<dots> = tsubst \<rho> B2" using tsubst_tnorm[OF e(6,7) tsol tinv_tcons[OF e(2) b2(2)]] by simp
    finally show ?thesis .
  qed
  have pl: "\<forall>(rb', t', u')\<in>set [(rb, t, u)]. upok A env rb' X t' u'" using p by simp
  show ?thesis unfolding asg
  proof (rule ncu_bindW[OF ncu_simps(4)[THEN iffD2, OF allI[OF impI[OF TrueI]]]])
    fix oc assume ro: "okW (liftM (rigid_occurs_term env v u)) oc"
    show "ncu (case oc of
        NoOcc \<Rightarrow> do {
          T1 \<leftarrow> liftM (body_type env T);
          T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types alg T1 T2 env;
          liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN
      | Rigid \<Rightarrow> raiseW CANTUNIFY) (\<lambda>env'. \<exists>\<rho>'. solution \<rho>' \<sigma> env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
        tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env')"
    proof (cases oc)
      case Rigid
      with ro rigid_occurs_term_Rigid[OF inv p t hu] show ?thesis by simp
    next
      case Nonrigid
      then show ?thesis by simp
    next
      case NoOcc
      have fu: "fastype env rb u = return B2" using b2(1) by (simp add: fastype_def)
      have "ncu (cunify_types alg B1 B2 env) (\<lambda>env1. \<exists>\<rho>1. scinv \<rho>1 \<sigma> env1 [(rb, t, u)] X A \<and>
          tagree (maxidx env) \<rho> \<rho>1 \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1) \<and>
          maxidx env \<le> maxidx env1 \<and> tenv env1 = tenv env \<and> textends (tyenv env) (tyenv env1))"
        by (rule sc_cunify_complete[OF inv pl b1(2,3) b2(2) w2 eqT])
      then have cu: "ncu (cunify_types alg B1 B2 env) (\<lambda>env1. ncu (liftM (update (v, T) (rlist_abs rb u) env1))
          (\<lambda>env'. \<exists>\<rho>'. solution \<rho>' \<sigma> env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
            tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env'))"
      proof (rule ncu_mono')
        fix env1 assume "\<exists>\<rho>1. scinv \<rho>1 \<sigma> env1 [(rb, t, u)] X A \<and>
          tagree (maxidx env) \<rho> \<rho>1 \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1) \<and>
          maxidx env \<le> maxidx env1 \<and> tenv env1 = tenv env \<and> textends (tyenv env) (tyenv env1)"
        then obtain \<rho>1 where inv1: "scinv \<rho>1 \<sigma> env1 [(rb, t, u)] X A" and ag: "tagree (maxidx env) \<rho> \<rho>1"
          and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" and mx: "maxidx env \<le> maxidx env1"
          and te: "tenv env1 = tenv env" and tx: "textends (tyenv env) (tyenv env1)"
          by blast
        note i1 = scinvD[OF inv1]
        have ext1: "extends env env1" using te tx mx by (simp add: extends_def)
        have p1: "upok A env1 rb X t u" by (rule upok_mono[OF p ext1 tv])
        obtain e1 V where ci: "cinv \<rho>1 \<sigma> env1 e1 rb (X \<union> evars env1) A" and cs: "cterm \<rho>1 env1 e1 rb A t V"
          and ct: "cterm \<rho>1 env1 e1 rb A u V" and eq1: "ap \<rho>1 \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 \<sigma> u"
          by (rule scinv_cinv[OF inv1 p1])
        have bind: "\<sigma> v (tsubst \<rho>1 T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 \<sigma> (rlist_abs rb u)"
          by (rule assign_bind_sol[OF ci cs[unfolded t] ct eq1[unfolded t] is_def])
        show "ncu (liftM (update (v, T) (rlist_abs rb u) env1))
          (\<lambda>env'. \<exists>\<rho>'. solution \<rho>' \<sigma> env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
            tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env')"
        proof (simp only: ncu_simps, intro allI impI)
          fix env' assume upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
          have sol': "solution \<rho>1 \<sigma> env'"
          proof (rule solution_extend[OF i1(1) i1(3) sagree_refl solutionD(3)[OF i1(1)]])
            show "tyenv env' = tyenv env1" using ok_update(3)[OF upd] .
            show "vt_lookup (tenv env') x = Some b" if "vt_lookup (tenv env1) x = Some b" for x b
              using that ok_update(1,2)[OF upd] by auto
            fix x U u0 assume new: "vt_lookup (tenv env') x = Some (U, u0)" "vt_lookup (tenv env1) x = None"
            then have x: "x = v" "U = T" "u0 = rlist_abs rb u" using ok_update(2)[OF upd] by (auto split: if_splits)
            with bind show "\<sigma> x (tsubst \<rho>1 U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 \<sigma> u0" by simp
          qed
          have tv': "tvinv A env'"
          proof (rule tvinv_update[OF upd i1(4)])
            have "btvars (rev rb) = btvars rb" by (simp add: btvars_def)
            then show "tvars T \<union> ttvars (rlist_abs rb u) \<subseteq> tvars_env (tyenv env1) \<union> A"
              using kT pd(4,5) tv by (auto simp: rlist_abs_abs_list ttvars_abs_list)
          qed
          have "tyenv env' = tyenv env1" "maxidx env1 \<le> maxidx env'"
            using ok_update(3,4)[OF upd] by simp_all
          then show "\<exists>\<rho>'. solution \<rho>' \<sigma> env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
            tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env'"
            using sol' ag tv' tv mx by auto
        qed
      qed
      show ?thesis unfolding NoOcc occ.case
        by (simp add: b1(1) fu) (rule ncu_bindW[OF cu], simp)
    qed
  qed
qed


subsection \<open>Results of simplification\<close>

text \<open>
  The conclusion for a computation of \<^const>\<open>SIMPL0\<close> from the state \<open>(env, ffs, frs)\<close> with the
  solution \<open>(\<rho>, \<sigma>)\<close>: the new pairs are added in front, and they have a solution of the new
  environment that agrees with \<open>(\<rho>, \<sigma>)\<close> on the old variables.
\<close>

definition ccon0 :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow>
    dpair list \<Rightarrow> dpair list \<Rightarrow> sstate \<Rightarrow> bool" where
  "ccon0 \<rho> \<sigma> env X A ffs frs st' \<longleftrightarrow> (case st' of (env', ffs', frs') \<Rightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> (\<exists>\<rho>' \<sigma>'. scinv \<rho>' \<sigma>' env' (a @ b) X A \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env'))"

lemma ccon0I:
  "scinv \<rho>' \<sigma>' env' (a @ b) X A \<Longrightarrow> tagree (maxidx env) \<rho> \<rho>' \<Longrightarrow> sagree (maxidx env) \<sigma> \<sigma>' \<Longrightarrow>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow>
    ccon0 \<rho> \<sigma> env X A ffs frs (env', a @ ffs, b @ frs)"
  unfolding ccon0_def by blast

lemma ccon0_refl: "scinv \<rho> \<sigma> env [] X A \<Longrightarrow> ccon0 \<rho> \<sigma> env X A ffs frs (env, ffs, frs)"
  using ccon0I[of \<rho> \<sigma> env "[]" "[]" X A env \<rho> \<sigma> ffs frs] by simp

lemma ccon0_env:
  assumes "ccon0 \<rho>2 \<sigma>2 env2 X A ffs frs st" "tagree (maxidx env) \<rho> \<rho>2" "sagree (maxidx env) \<sigma> \<sigma>2"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" "maxidx env \<le> maxidx env2"
  shows "ccon0 \<rho> \<sigma> env X A ffs frs st"
proof -
  obtain env' ffs' frs' where st: "st = (env', ffs', frs')" by (cases st)
  from assms(1) st obtain a b \<rho>' \<sigma>' where c: "ffs' = a @ ffs" "frs' = b @ frs" "scinv \<rho>' \<sigma>' env' (a @ b) X A"
    "tagree (maxidx env2) \<rho>2 \<rho>'" "sagree (maxidx env2) \<sigma>2 \<sigma>'"
    "tvars_env (tyenv env2) \<subseteq> tvars_env (tyenv env')" "maxidx env2 \<le> maxidx env'"
    unfolding ccon0_def by blast
  have "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    using tagree_trans[OF assms(2) c(4) assms(5)] sagree_trans[OF assms(3) c(5) assms(5)] .
  then show ?thesis using st c assms(4,5) ccon0I[of \<rho>' \<sigma>' env' a b X A env \<rho> \<sigma> ffs frs] by auto
qed

lemma scinv_pairs:
  "scinv \<rho> \<sigma> env dps0 X A \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow> dsolved \<rho> \<sigma> dps \<Longrightarrow> scinv \<rho> \<sigma> env dps X A"
  unfolding scinv_def by blast

lemma ccon0_trans:
  assumes a1: "ffs1 = a1 @ ffs" "frs1 = b1 @ frs" and inv1: "scinv \<rho>1 \<sigma>1 env1 (a1 @ b1) X A"
    and ag: "tagree (maxidx env) \<rho> \<rho>1" "sagree (maxidx env) \<sigma> \<sigma>1"
    and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "maxidx env \<le> maxidx env1"
    and si1: "sinv A K X env1 (a1 @ b1)" and c2: "ccon0 \<rho>1 \<sigma>1 env1 X A ffs1 frs1 st2"
  shows "ccon0 \<rho> \<sigma> env X A ffs frs st2"
proof -
  obtain env2 ffs2 frs2 where st2: "st2 = (env2, ffs2, frs2)" by (cases st2)
  from c2 st2 obtain a2 b2 \<rho>2 \<sigma>2 where a2: "ffs2 = a2 @ ffs1" "frs2 = b2 @ frs1"
    and inv2: "scinv \<rho>2 \<sigma>2 env2 (a2 @ b2) X A" and ag2: "tagree (maxidx env1) \<rho>1 \<rho>2" "sagree (maxidx env1) \<sigma>1 \<sigma>2"
    and tv2: "tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env2)" "maxidx env1 \<le> maxidx env2"
    unfolding ccon0_def by blast
  note i1 = scinvD[OF inv1] and i2 = scinvD[OF inv2]
  have "dtyped \<rho>2 (a1 @ b1)" "dsolved \<rho>2 \<sigma>2 (a1 @ b1)"
    using sc_dps_agree[OF sc_sinv_pok[OF si1] i1(4) i1(3) ag2] i1(6,7) by blast+
  then have "scinv \<rho>2 \<sigma>2 env2 ((a2 @ a1) @ (b2 @ b1)) X A"
    using i2(6,7) by (intro scinv_pairs[OF inv2]) auto
  moreover have "tagree (maxidx env) \<rho> \<rho>2" "sagree (maxidx env) \<sigma> \<sigma>2"
    using tagree_trans[OF ag(1) ag2(1) tv(2)] sagree_trans[OF ag(2) ag2(2) tv(2)] .
  ultimately show ?thesis using st2 a1 a2 tv tv2 ccon0I[of \<rho>2 \<sigma>2 env2 "a2 @ a1" "b2 @ b1" X A env \<rho> \<sigma> ffs frs]
    by auto
qed

lemma scinv_swap: "scinv \<rho> \<sigma> env [(rb, t, u)] X A \<Longrightarrow> scinv \<rho> \<sigma> env [(rb, u, t)] X A"
  unfolding scinv_def by (auto intro: conv_sym)

lemma hsat0_swap: "hsat0 env (rb, t, u) \<Longrightarrow> hsat0 env (rb, u, t)"
  unfolding hsat0_def by blast

text \<open>The decomposition of a rigid-rigid pair, with the termination measure of
  \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>:\<close>

context
  fixes A K X B
  assumes IHc: "\<And>env1 dp1 ffs1 frs1 \<rho>1 \<sigma>1. (smeas K X env1 dp1, B) \<in> ulex \<Longrightarrow> sinv A K X env1 [dp1] \<Longrightarrow>
      scinv \<rho>1 \<sigma>1 env1 [dp1] X A \<Longrightarrow> ncu (SIMPL0 alg dp1 (env1, ffs1, frs1)) (ccon0 \<rho>1 \<sigma>1 env1 X A ffs1 frs1)"
    and finX: "finite X" and finK: "finite K"
begin

lemma sc_IHt: "(smeas K X env1 dp1, B) \<in> ulex \<Longrightarrow> sinv A K X env1 [dp1] \<Longrightarrow>
    cuok (SIMPL0 alg dp1 (env1, ffs1, frs1)) (spost A K X env1 ffs1 frs1)"
  by (rule SIMPL0_term[OF finX finK])

lemma simrands_complete:
  assumes hh: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u. h' = f $ u)"
    and B: "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), d0)"
  shows "length ss = length ts \<Longrightarrow> sinv A K X env (dzip rb ss ts) \<Longrightarrow> sstep A K X env0 env \<Longrightarrow>
    (tyenv env = tyenv env0 \<Longrightarrow> tenv env = tenv env0 \<Longrightarrow> sum_list (map (dm env) (dzip rb ss ts)) < d0) \<Longrightarrow>
    scinv \<rho> \<sigma> env (dzip rb ss ts) X A \<Longrightarrow>
    ncu (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) (env, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
proof (induction ss arbitrary: ts ffs frs env \<rho> \<sigma> rule: rev_induct)
  case Nil
  then have "ts = []" by simp
  with Nil show ?case using simrands_atoms[OF hh] ccon0_refl[OF scinv_mono[OF Nil.prems(5)]] by simp
next
  case (snoc s ss)
  from snoc.prems(1) obtain ts' t where ts: "ts = ts' @ [t]" and len: "length ss = length ts'"
    by (cases ts rule: rev_exhaust) auto
  have dz: "dzip rb (ss @ [s]) ts = dzip rb ss ts' @ [(rb, s, t)]" using len ts by simp
  have si0: "sinv A K X env (dzip rb ss ts')" by (rule sinv_mono[OF snoc.prems(2)[unfolded dz]]) auto
  have lt0: "sum_list (map (dm env) (dzip rb ss ts')) < d0"
    if "tyenv env = tyenv env0" "tenv env = tenv env0" using snoc.prems(4)[OF that, unfolded dz] by simp
  have inv0: "scinv \<rho> \<sigma> env (dzip rb ss ts') X A" by (rule scinv_mono[OF snoc.prems(5)[unfolded dz]]) auto
  have r0: "ncu (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts') (env, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
    by (rule snoc.IH[OF len si0 snoc.prems(3) lt0 inv0])
  have IHt': "\<And>env1 dp1 ffs1 frs1. (smeas K X env1 dp1, B) \<in> ulex \<Longrightarrow> sinv A K X env1 [dp1] \<Longrightarrow>
      cuok (SIMPL0 alg dp1 (env1, ffs1, frs1)) (spost A K X env1 ffs1 frs1)"
    by (rule sc_IHt)
  have t0: "cuok (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts') (env, ffs, frs)) (spost A K X env ffs frs)"
    by (rule simrands_term[OF IHt' finX finK hh B len si0 snoc.prems(3) lt0])
  show ?case unfolding ts simrands_snoc
  proof (rule ncu_bindW[OF ncu_cuok[OF r0 t0]])
    fix st1 assume st1ok: "okW (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts') (env, ffs, frs)) st1"
      and P: "ccon0 \<rho> \<sigma> env X A ffs frs st1 \<and> spost A K X env ffs frs st1"
    obtain env1 ffs1 frs1 where st1: "st1 = (env1, ffs1, frs1)" by (cases st1)
    from P st1 obtain a1 b1 where s1: "ffs1 = a1 @ ffs" "frs1 = b1 @ frs" "sinv A K X env1 (a1 @ b1)"
      "sstep A K X env env1"
      unfolding spost_def by auto
    from P st1 obtain a1' b1' \<rho>1 \<sigma>1 where c1: "ffs1 = a1' @ ffs" "frs1 = b1' @ frs"
      "scinv \<rho>1 \<sigma>1 env1 (a1' @ b1') X A" "tagree (maxidx env) \<rho> \<rho>1" "sagree (maxidx env) \<sigma> \<sigma>1"
      "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "maxidx env \<le> maxidx env1"
      unfolding ccon0_def by blast
    have aa: "a1' = a1" "b1' = b1" using s1(1,2) c1(1,2) by simp_all
    have si1: "sinv A K X env1 [(rb, s, t)]"
    proof (rule sinv_ext[OF sinv_mono[OF snoc.prems(2)] _ _ s1(4)])
      show "set [(rb, s, t)] \<subseteq> set (dzip rb (ss @ [s]) ts)" unfolding dz by simp
    qed (use s1(3) in \<open>simp_all add: sinv_def\<close>)
    have m: "(smeas K X env1 (rb, s, t), B) \<in> ulex" unfolding smeas_def B
    proof (rule ulex_sstep[OF sstep_trans[OF snoc.prems(3) s1(4)]])
      assume e1: "tyenv env1 = tyenv env0" "tenv env1 = tenv env0"
      have e0: "tyenv env = tyenv env0" "tenv env = tenv env0"
        using extends_mid[OF sstepD(1)[OF snoc.prems(3)] sstepD(1)[OF s1(4)]] e1 by auto
      then have "dm env1 = dm env" using e1 dm_same[of env1 env] by simp
      with snoc.prems(4)[OF e0, unfolded dz] show "dm env1 (rb, s, t) < d0" by simp
    qed
    have inv1: "scinv \<rho>1 \<sigma>1 env1 [(rb, s, t)] X A"
    proof (rule scinv_pairs[OF c1(3)])
      note i = scinvD[OF snoc.prems(5)]
      have p: "\<forall>(rb', s', t')\<in>set [(rb, s, t)]. upok A env rb' X s' t'"
        using sc_sinv_pok[OF snoc.prems(2)[unfolded dz]] by simp
      have "dtyped \<rho> [(rb, s, t)]" "dsolved \<rho> \<sigma> [(rb, s, t)]" using i(6,7) dz by simp_all
      then show "dtyped \<rho>1 [(rb, s, t)]" "dsolved \<rho>1 \<sigma>1 [(rb, s, t)]"
        using sc_dps_agree[OF p i(4) i(3) c1(4,5)] by blast+
    qed
    from IHc[OF m si1 inv1, of ffs1 frs1]
    show "ncu (SIMPL0 alg (rb, s, t) st1) (ccon0 \<rho> \<sigma> env X A ffs frs)"
      unfolding st1 by (rule ncu_mono') (rule ccon0_trans[OF c1(1,2) c1(3-7) s1(3)[folded aa]])
  qed
qed

lemma rigid_rigid_complete:
  assumes hp: "hpost A K X env0 dp0 (rb, t, u) env" and B: "B = smeas K X env0 dp0"
    and st2: "sstep A K X env env2" and te2: "tenv env2 = tenv env" and ei2: "einv A K env2" and wi2: "winv env2 X"
    and rh: "rigid (head_of t)" "rigid (head_of u)"
    and hh: "\<And>\<rho>. tsol (tyenv env2) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> inst \<rho> (head_of t) = inst \<rho> (head_of u)"
    and inv: "scinv \<rho> \<sigma> env2 [(rb, t, u)] X A"
  shows "ncu (simrands (SIMPL0 alg) rb u0 t u (env2, ffs, frs)) (ccon0 \<rho> \<sigma> env2 X A ffs frs)"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
    and st0: "sstep A K X env0 env" and dmle: "tyenv env = tyenv env0 \<Longrightarrow> dm env (rb, t, u) \<le> dm env0 dp0"
    by (simp_all add: hpost_def)
  define h where "h = head_of t"
  define ss where "ss = snd (strip_comb t)"
  define h' where "h' = head_of u"
  define ts where "ts = snd (strip_comb u)"
  have tt: "t = h \<degree>\<degree> ss" unfolding h_def ss_def by (rule t_apps)
  have uu: "u = h' \<degree>\<degree> ts" unfolding h'_def ts_def by (rule t_apps)
  have p2: "upok A env2 rb X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)"
    using upok_mono[OF p sstepD(1,2)[OF st2]] tt uu by simp
  note ra = rigid_args_pok[OF p2 rh[folded h_def h'_def] hh[folded h_def h'_def] einv_rho0[OF ei2]]
  have si2: "sinv A K X env2 (dzip rb ss ts)" by (rule sinv_dzip[OF ei2 wi2 ra(2)])
  have B': "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), dm env0 dp0)" by (simp add: B smeas_def)
  have lt: "sum_list (map (dm env2) (dzip rb ss ts)) < dm env0 dp0"
    if e: "tyenv env2 = tyenv env0" "tenv env2 = tenv env0"
  proof -
    have e1: "tyenv env = tyenv env0" by (rule extends_mid(1)[OF sstepD(1)[OF st0] sstepD(1)[OF st2] e(1)])
    then have "dm env2 = dm env" using e(1) dm_same[OF te2] by simp
    moreover have "sum_list (map (dm env) (dzip rb ss ts)) < dm env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)"
      by (rule dm_args[OF ei wi p[unfolded tt uu] rh[folded h_def h'_def] ra(1)])
    ultimately show ?thesis using dmle[OF e1] tt uu by simp
  qed
  have hA: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u'. h' = f $ u')" unfolding h_def h'_def by (simp_all add: head_of_not_App)
  have inv2: "scinv \<rho> \<sigma> env2 (dzip rb ss ts) X A"
  proof (rule scinv_pairs[OF inv])
    obtain e T where ci: "cinv \<rho> \<sigma> env2 e rb (X \<union> evars env2) A" and cs: "cterm \<rho> env2 e rb A t T"
      and ct: "cterm \<rho> env2 e rb A u T" and eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and Xv: "vars t \<union> vars u \<subseteq> X \<union> evars env2"
      by (rule scinv_cinv[OF inv upok_mono[OF p sstepD(1,2)[OF st2]]])
    note rr = rigid_args[OF ci Xv[unfolded tt uu] cs[unfolded tt] ct[unfolded uu] eq[unfolded tt uu]
      rh[folded h_def h'_def]]
    have "cpair \<rho> \<sigma> env2 e rb (X \<union> evars env2) A (a, b)" if "(a, b) \<in> set (zip ss ts)" for a b
      using rr(3) that by blast
    then have pr: "(\<exists>U. e \<turnstile> inst \<rho> a : U \<and> e \<turnstile> inst \<rho> b : U) \<and> \<not> loose_bvar a (ilength rb) \<and>
        \<not> loose_bvar b (ilength rb) \<and> ap \<rho> \<sigma> a \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> b" if "(a, b) \<in> set (zip ss ts)" for a b
      using that unfolding cpair_def cterm_def by fastforce
    have bs: "bs_env \<rho> e rb" using ci by (simp add: cinv_def)
    show "dtyped \<rho> (dzip rb ss ts)" unfolding dtyped_def using pr bs by fastforce
    show "dsolved \<rho> \<sigma> (dzip rb ss ts)" unfolding dsolved_def using pr by fastforce
  qed
  from simrands_complete[OF hA B' ra(1) si2 sstep_trans[OF st0 st2] lt inv2, of u0 ffs frs]
  show ?thesis unfolding tt uu .
qed

text \<open>A flex-rigid pair is solved by assignment, or kept:\<close>

lemma sc_fr_complete:
  assumes ei: "einv A K env" and p: "upok A env rb X t u" and inv: "scinv \<rho> \<sigma> env [(rb, t, u)] X A"
    and hs: "hsat0 env (rb, t, u)" and hr: "rigid (head_of u)"
  shows "ncu (handleW (bindW (assignment alg rb t u env) (\<lambda>env'. returnW (env', ffs, frs)))
    (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
proof (rule ncu_handle_assign[OF assignment_complete[OF ei p inv hs hr]])
  fix env' assume okA: "okW (assignment alg rb t u env) env'" and P: "\<exists>\<rho>'. solution \<rho>' \<sigma> env' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    maxidx env \<le> maxidx env'"
  then obtain \<rho>' where sol: "solution \<rho>' \<sigma> env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" and tv: "tvinv A env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" and mx: "maxidx env \<le> maxidx env'"
    by blast
  have pl: "\<forall>(rb', t', u')\<in>set [(rb, t, u)]. upok A env rb' X t' u'" using p by simp
  have "scinv \<rho>' \<sigma> env' [] X A"
    by (rule scinv_step[OF inv pl assignment_sound[OF okA] sol ag sagree_refl _ tv]) simp
  then show "ccon0 \<rho> \<sigma> env X A ffs frs (env', ffs, frs)"
    using ccon0I[of \<rho>' \<sigma> env' "[]" "[]" X A env \<rho> \<sigma> ffs frs] ag tv(2) mx by simp
next
  show "ccon0 \<rho> \<sigma> env X A ffs frs (env, ffs, (rb, t, u) # frs)"
    using ccon0I[of \<rho> \<sigma> env "[]" "[(rb, t, u)]" X A env \<rho> \<sigma> ffs frs] inv by simp
qed

lemma SIMPL0_rest_complete:
  assumes hp: "hpost A K X env0 dp0 (rb, t, u) env" and B: "B = smeas K X env0 dp0"
    and inv: "scinv \<rho> \<sigma> env [(rb, t, u)] X A" and hs: "hsat0 env (rb, t, u)"
  shows "ncu (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (ccon0 \<rho> \<sigma> env X A ffs frs)"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
    and aht: "ahd env t" and ahu: "ahd env u"
    by (simp_all add: hpost_def)
  let ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p] and i = scinvD[OF inv]
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t : T0" "e0 \<turnstile> inst ?\<rho> u : T0"
    using pd(9)[OF r0] by blast
  have tvh: "ttvars (head_of t) \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars (head_of u) \<subseteq> tvars_env (tyenv env) \<union> A"
    using ttvars_head[of t] ttvars_head[of u] pd(3,4) by blast+
  have pl: "\<forall>(rb', t', u')\<in>set [(rb, t, u)]. upok A env rb' X t' u'" using p by simp
  have hhr: "inst \<rho> (head_of t) = inst \<rho> (head_of u)" if rh: "rigid (head_of t)" "rigid (head_of u)"
  proof -
    obtain e T where ci: "cinv \<rho> \<sigma> env e rb (X \<union> evars env) A" and cs: "cterm \<rho> env e rb A t T"
      and ct: "cterm \<rho> env e rb A u T" and eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and Xv: "vars t \<union> vars u \<subseteq> X \<union> evars env"
      by (rule scinv_cinv[OF inv p])
    define h where "h = head_of t"
    define ss where "ss = snd (strip_comb t)"
    define h' where "h' = head_of u"
    define ts where "ts = snd (strip_comb u)"
    have tt: "t = h \<degree>\<degree> ss" unfolding h_def ss_def by (rule t_apps)
    have uu: "u = h' \<degree>\<degree> ts" unfolding h'_def ts_def by (rule t_apps)
    from rigid_args(1)[OF ci Xv[unfolded tt uu] cs[unfolded tt] ct[unfolded uu] eq[unfolded tt uu]
      rh[folded h_def h'_def]]
    show ?thesis by (simp add: h_def h'_def)
  qed
  have FR: "ncu (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (ccon0 \<rho> \<sigma> env X A ffs frs)"
    if hv: "head_of t = Var F Ft" and hr: "rigid (head_of u)" for F Ft
  proof -
    have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
      handleW (bindW (assignment alg rb t u env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)"
      using hv hr by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    with sc_fr_complete[OF ei p inv hs hr] show ?thesis by simp
  qed
  have RF: "ncu (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (ccon0 \<rho> \<sigma> env X A ffs frs)"
    if hv: "head_of u = Var F Fu" and hr: "rigid (head_of t)" for F Fu
  proof -
    have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
      handleW (bindW (assignment alg rb u t env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)"
      using hv hr by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    moreover have "ncu (handleW (bindW (assignment alg rb u t env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
    proof (rule ncu_handle_assign[OF assignment_complete[OF ei upok_sym[OF p] scinv_swap[OF inv] hsat0_swap[OF hs] hr]])
      fix env' assume okA: "okW (assignment alg rb u t env) env'" and P: "\<exists>\<rho>'. solution \<rho>' \<sigma> env' \<and>
        tagree (maxidx env) \<rho> \<rho>' \<and> tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
        maxidx env \<le> maxidx env'"
      then obtain \<rho>' where sol: "solution \<rho>' \<sigma> env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" and tv: "tvinv A env'"
        "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" and mx: "maxidx env \<le> maxidx env'"
        by blast
      have pl': "\<forall>(rb', t', u')\<in>set [(rb, u, t)]. upok A env rb' X t' u'" using upok_sym[OF p] by simp
      have "scinv \<rho>' \<sigma> env' [] X A"
        by (rule scinv_step[OF scinv_swap[OF inv] pl' assignment_sound[OF okA] sol ag sagree_refl _ tv]) simp
      then show "ccon0 \<rho> \<sigma> env X A ffs frs (env', ffs, frs)"
        using ccon0I[of \<rho>' \<sigma> env' "[]" "[]" X A env \<rho> \<sigma> ffs frs] ag tv(2) mx by simp
    next
      show "ccon0 \<rho> \<sigma> env X A ffs frs (env, ffs, (rb, u, t) # frs)"
        using ccon0I[of \<rho> \<sigma> env "[]" "[(rb, u, t)]" X A env \<rho> \<sigma> ffs frs] scinv_swap[OF inv] by simp
    qed
    ultimately show ?thesis by simp
  qed
  have CF: "ncu (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (ccon0 \<rho> \<sigma> env X A ffs frs)"
    if ht: "head_of t = hc" and hu: "head_of u = hd"
      and c: "(hc = Const a Tc \<and> hd = Const a Tu) \<or> (hc = Free a Tc \<and> hd = Free a Tu)"
      and eq: "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
        bindW (cunify_types alg Tc Tu env) (\<lambda>env'. simrands (SIMPL0 alg) rb u t u (env', ffs, frs))"
    for hc hd a Tc Tu
  proof -
    have cT: "cert_typ alg ar (tsubst ?\<rho> Tc)"
      using c head_Const_cert[OF ty0(2)] head_Free_cert[OF ty0(2)] ht by blast
    have cU: "cert_typ alg ar (tsubst ?\<rho> Tu)"
      using c head_Const_cert[OF ty0(3)] head_Free_cert[OF ty0(3)] hu by blast
    have kT: "tvars Tc \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(1) ht c by auto
    have kU: "tvars Tu \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(2) hu c by auto
    have rh: "rigid (head_of t)" "rigid (head_of u)" using ht hu c by auto
    have eqr: "tsubst \<rho> Tc = tsubst \<rho> Tu" using hhr[OF rh] ht hu c by auto
    note cc = sc_cunify_complete[OF inv pl kT cert_typ_rev(1)[OF ei cT kT] kU cert_typ_rev(1)[OF ei cU kU] eqr]
    note ct = cunify_types_term[OF ei finK kT cert_typ_rev[OF ei cT kT] kU cert_typ_rev[OF ei cU kU]]
    show ?thesis unfolding eq
    proof (rule ncu_bindW[OF ncu_cuok[OF cc ct]])
      fix env2 assume "okW (cunify_types alg Tc Tu env) env2" and P: "(\<exists>\<rho>2. scinv \<rho>2 \<sigma> env2 [(rb, t, u)] X A \<and>
          tagree (maxidx env) \<rho> \<rho>2 \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2) \<and>
          maxidx env \<le> maxidx env2 \<and> tenv env2 = tenv env \<and> textends (tyenv env) (tyenv env2)) \<and>
        (einv A K env2 \<and> tenv env2 = tenv env \<and>
        textends (tyenv env) (tyenv env2) \<and> maxidx env \<le> maxidx env2 \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2) \<and> tnew A env A env2 \<and> (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> Tc = tsubst \<rho> Tu) \<and>
        (tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)))"
      then obtain \<rho>2 where inv2: "scinv \<rho>2 \<sigma> env2 [(rb, t, u)] X A" and ag: "tagree (maxidx env) \<rho> \<rho>2"
        and ei2: "einv A K env2" and te: "tenv env2 = tenv env" and tx: "textends (tyenv env) (tyenv env2)"
        and mx: "maxidx env \<le> maxidx env2" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" and tn: "tnew A env A env2"
        and sol: "\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> Tc = tsubst \<rho> Tu"
        and card: "tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
        by blast
      have hh: "inst \<rho> (head_of t) = inst \<rho> (head_of u)" if "tsol (tyenv env2) \<rho>" for \<rho>
        using sol that ht hu c by auto
      have "ncu (simrands (SIMPL0 alg) rb u t u (env2, ffs, frs)) (ccon0 \<rho>2 \<sigma> env2 X A ffs frs)"
        by (rule rigid_rigid_complete[OF hp B sstep_tyext[OF te tx mx tv tn card] te ei2
          winv_tyext[OF wi te tx mx] rh hh inv2])
      then show "ncu (simrands (SIMPL0 alg) rb u t u (env2, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
        by (rule ncu_mono') (rule ccon0_env[OF _ ag sagree_refl tv mx])
    qed
  qed
  from ahd_head[OF aht] show ?thesis
  proof
    assume rt: "rigid (head_of t)"
    from ahd_head[OF ahu] show ?thesis
    proof
      assume ru: "rigid (head_of u)"
      note hr = hhr[OF rt ru]
      show ?thesis
      proof (cases "head_of t")
        case (Const a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Const a Tb")
          case True
          then obtain Tb where hb: "head_of u = Const a Tb" by blast
          show ?thesis
            by (rule CF[OF Const hb]) (simp_all add: SIMPL0_rest_def Const hb)
        next
          case False
          then show ?thesis using Const ru hr by (cases "head_of u") auto
        qed
      next
        case (Free a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Free a Tb")
          case True
          then obtain Tb where hb: "head_of u = Free a Tb" by blast
          show ?thesis
            by (rule CF[OF Free hb]) (simp_all add: SIMPL0_rest_def Free hb)
        next
          case False
          then show ?thesis using Free ru hr by (cases "head_of u") auto
        qed
      next
        case (Bound j)
        show ?thesis
        proof (cases "head_of u = Bound j")
          case True
          have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs = simrands (SIMPL0 alg) rb u t u (env, ffs, frs)"
            by (simp add: SIMPL0_rest_def Bound True)
          moreover have "ncu (simrands (SIMPL0 alg) rb u t u (env, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
            by (rule rigid_rigid_complete[OF hp B sstep_refl refl ei wi rt ru _ inv]) (simp add: Bound True)
          ultimately show ?thesis by simp
        next
          case False
          then show ?thesis using Bound ru hr by (cases "head_of u") auto
        qed
      qed (use rt in simp_all)
    next
      assume "\<exists>F U. head_of u = Var F U \<and> vt_lookup (tenv env) F = None"
      then obtain F U where "head_of u = Var F U" by blast
      from RF[OF this rt] show ?thesis .
    qed
  next
    assume "\<exists>F U. head_of t = Var F U \<and> vt_lookup (tenv env) F = None"
    then obtain F Ft where ht: "head_of t = Var F Ft" by blast
    from ahd_head[OF ahu] show ?thesis
    proof
      assume "rigid (head_of u)"
      from FR[OF ht this] show ?thesis .
    next
      assume "\<exists>G U. head_of u = Var G U \<and> vt_lookup (tenv env) G = None"
      then obtain G Gu where hu: "head_of u = Var G Gu" by blast
      have kF: "tvars Ft \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(1) ht by simp
      have kG: "tvars Gu \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(2) hu by simp
      from body_type_ok[OF ei kF head_Var_cert[OF ty0(2) ht]] obtain B1 where
        b1: "body_type env Ft = return B1" "tvars B1 \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar B1"
        by blast
      from body_type_ok[OF ei kG head_Var_cert[OF ty0(3) hu]] obtain B2 where
        b2: "body_type env Gu = return B2" "tvars B2 \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar B2"
        by blast
      obtain e1 T1 where bt: "\<And>F Ft B. head_of t = Var F Ft \<Longrightarrow> tvars Ft \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
          ok (body_type env Ft) B \<Longrightarrow> tnorm (tyenv env) B = T1"
        "\<And>F Ft B. head_of u = Var F Ft \<Longrightarrow> tvars Ft \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
          ok (body_type env Ft) B \<Longrightarrow> tnorm (tyenv env) B = T1"
        by (rule hsat0_body_type[OF ei hs]) blast
      have n1: "tnorm (tyenv env) B1 = T1" by (rule bt(1)[OF ht kF]) (use b1(1) in \<open>simp add: return_def\<close>)
      have n2: "tnorm (tyenv env) B2 = T1" by (rule bt(2)[OF hu kG]) (use b2(1) in \<open>simp add: return_def\<close>)
      have tsol: "tsol (tyenv env) \<rho>" by (rule solutionD(2)[OF i(1)])
      have eqT: "tsubst \<rho> B1 = tsubst \<rho> B2"
      proof -
        have "tsubst \<rho> B1 = tsubst \<rho> (tnorm (tyenv env) B1)"
          using tsubst_tnorm[OF e(6,7) tsol tinv_tcons[OF e(2) b1(2)]] by simp
        also have "\<dots> = tsubst \<rho> (tnorm (tyenv env) B2)" using n1 n2 by simp
        also have "\<dots> = tsubst \<rho> B2" using tsubst_tnorm[OF e(6,7) tsol tinv_tcons[OF e(2) b2(2)]] by simp
        finally show ?thesis .
      qed
      have eq: "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
          bindW (cunify_types alg B1 B2 env) (\<lambda>env'. returnW (env', (rb, t, u) # ffs, frs))"
        by (simp add: SIMPL0_rest_def ht hu b1(1) b2(1))
      show ?thesis unfolding eq
      proof (rule ncu_bindW[OF sc_cunify_complete[OF inv pl b1(2,3) b2(2,3) eqT]])
        fix env2 assume "okW (cunify_types alg B1 B2 env) env2" and "\<exists>\<rho>2. scinv \<rho>2 \<sigma> env2 [(rb, t, u)] X A \<and>
          tagree (maxidx env) \<rho> \<rho>2 \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2) \<and>
          maxidx env \<le> maxidx env2 \<and> tenv env2 = tenv env \<and> textends (tyenv env) (tyenv env2)"
        then obtain \<rho>2 where inv2: "scinv \<rho>2 \<sigma> env2 [(rb, t, u)] X A" and ag: "tagree (maxidx env) \<rho> \<rho>2"
          and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" and mx: "maxidx env \<le> maxidx env2"
          by blast
        show "ncu (returnW (env2, (rb, t, u) # ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
          using ccon0I[of \<rho>2 \<sigma> env2 "[(rb, t, u)]" "[]" X A env \<rho> \<sigma> ffs frs] inv2 ag tv mx by simp
      qed
    qed
  qed
qed

lemma SIMPL0_step_complete:
  assumes B: "B = smeas K X env0 dp0" and si: "sinv A K X env0 [dp0]" and inv: "scinv \<rho> \<sigma> env0 [dp0] X A"
  shows "ncu (SIMPL0 alg dp0 (env0, ffs, frs)) (ccon0 \<rho> \<sigma> env0 X A ffs frs)"
proof -
  obtain rb t u where dp0: "dp0 = (rb, t, u)" by (cases dp0)
  from si dp0 have ei: "einv A K env0" and wi: "winv env0 X" and p: "upok A env0 rb X t u"
    by (simp_all add: sinv_def)
  have pl: "\<forall>(rb', t', u')\<in>set [(rb, t, u)]. upok A env0 rb' X t' u'" using p by simp
  note i = scinvD[OF inv]
  show ?thesis unfolding SIMPL0_unfold dp0
  proof (rule ncu_bindW[OF ncu_cuok[OF head_norm_dpair_complete[OF ei wi p inv[unfolded dp0]]
      head_norm_dpair_term[OF finK ei wi p]]])
    fix x assume okx: "okW (head_norm_dpair alg env0 (rb, t, u)) x"
      and P: "(case x of (dp', env') \<Rightarrow> env' = env0 \<and> hsat0 env0 dp' \<and> dsolved \<rho> \<sigma> [dp']) \<and>
        (case x of (dp', env') \<Rightarrow> hpost A K X env0 (rb, t, u) dp' env')"
    obtain rb' t' u' env where x: "x = ((rb', t', u'), env)" by (cases x) auto
    from P x have e: "env = env0" and hs: "hsat0 env (rb', t', u')" and ds: "dsolved \<rho> \<sigma> [(rb', t', u')]"
      and hp: "hpost A K X env0 dp0 (rb', t', u') env" by (auto simp: dp0)
    have inv': "scinv \<rho> \<sigma> env [(rb', t', u')] X A"
      by (rule scinv_step[OF inv[unfolded dp0] pl head_norm_dpair_sound(2)[OF okx[unfolded x]]])
        (use i(1,4) ds e in simp_all)
    have "ncu (SIMPL0_rest SIMPL0 alg rb' t' u' env ffs frs) (ccon0 \<rho> \<sigma> env X A ffs frs)"
      by (rule SIMPL0_rest_complete[OF hp B inv' hs])
    then show "ncu ((\<lambda>(dp, env'). case dp of (rb, t, u) \<Rightarrow> SIMPL0_rest SIMPL0 alg rb t u env' ffs frs) x)
        (ccon0 \<rho> \<sigma> env0 X A ffs frs)" by (simp add: x e)
  qed
qed

end


subsection \<open>Completeness of \<open>SIMPL0\<close>\<close>

text \<open>
  \<^const>\<open>SIMPL0\<close> does not raise \<open>CANTUNIFY\<close> on a pair with a solution \<open>(\<rho>, \<sigma>)\<close> (for the
  invariants \<^const>\<open>sinv\<close> of termination and \<^const>\<open>scinv\<close>), and the new pairs of every result have
  a solution that agrees with \<open>(\<rho>, \<sigma>)\<close> on the old variables. By induction on the measure
  \<^const>\<open>smeas\<close> of the termination proof.
\<close>

theorem SIMPL0_complete:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env [dp]" and inv: "scinv \<rho> \<sigma> env [dp] X A"
  shows "ncu (SIMPL0 alg dp (env, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
proof -
  have "\<forall>env dp ffs frs \<rho> \<sigma>. smeas K X env dp = m \<longrightarrow> sinv A K X env [dp] \<longrightarrow> scinv \<rho> \<sigma> env [dp] X A \<longrightarrow>
      ncu (SIMPL0 alg dp (env, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)" for m
  proof (induction m rule: wf_induct_rule[OF wf_ulex])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix env dp ffs frs \<rho> \<sigma> assume m: "smeas K X env dp = m" and si: "sinv A K X env [dp]"
        and inv: "scinv \<rho> \<sigma> env [dp] X A"
      show "ncu (SIMPL0 alg dp (env, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
      proof (rule SIMPL0_step_complete[OF _ fin m[symmetric] si inv])
        fix env1 dp1 ffs1 frs1 \<rho>1 \<sigma>1 assume "(smeas K X env1 dp1, m) \<in> ulex" "sinv A K X env1 [dp1]"
          "scinv \<rho>1 \<sigma>1 env1 [dp1] X A"
        then show "ncu (SIMPL0 alg dp1 (env1, ffs1, frs1)) (ccon0 \<rho>1 \<sigma>1 env1 X A ffs1 frs1)"
          using "1.IH" by blast
      qed
    qed
  qed
  with si inv show ?thesis by blast
qed

lemma foldrW_SIMPL0_complete:
  assumes fin: "finite X" "finite K"
  shows "sinv A K X env dps \<Longrightarrow> scinv \<rho> \<sigma> env dps X A \<Longrightarrow>
    ncu (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (ccon0 \<rho> \<sigma> env X A ffs frs)"
proof (induction dps)
  case Nil
  then show ?case using ccon0_refl[of \<rho> \<sigma> env X A ffs frs] by simp
next
  case (Cons dp dps)
  have si0: "sinv A K X env dps" by (rule sinv_mono[OF Cons.prems(1)]) auto
  have inv0: "scinv \<rho> \<sigma> env dps X A" by (rule scinv_mono[OF Cons.prems(2)]) auto
  note r0 = Cons.IH[OF si0 inv0] and t0 = foldrW_SIMPL0_term[OF fin si0, of ffs frs]
  show ?case unfolding foldrW.simps
  proof (rule ncu_bindW[OF ncu_cuok[OF r0 t0]])
    fix st1 assume P: "ccon0 \<rho> \<sigma> env X A ffs frs st1 \<and> spost A K X env ffs frs st1"
    obtain env1 ffs1 frs1 where st1: "st1 = (env1, ffs1, frs1)" by (cases st1)
    from P st1 obtain a1 b1 where s1: "ffs1 = a1 @ ffs" "frs1 = b1 @ frs" "sinv A K X env1 (a1 @ b1)"
      "sstep A K X env env1"
      unfolding spost_def by auto
    from P st1 obtain a1' b1' \<rho>1 \<sigma>1 where c1: "ffs1 = a1' @ ffs" "frs1 = b1' @ frs"
      "scinv \<rho>1 \<sigma>1 env1 (a1' @ b1') X A" "tagree (maxidx env) \<rho> \<rho>1" "sagree (maxidx env) \<sigma> \<sigma>1"
      "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "maxidx env \<le> maxidx env1"
      unfolding ccon0_def by blast
    have aa: "a1' = a1" "b1' = b1" using s1(1,2) c1(1,2) by simp_all
    have si1: "sinv A K X env1 [dp]"
      by (rule sinv_ext[OF sinv_mono[OF Cons.prems(1)] _ _ s1(4)]) (use s1(3) in \<open>simp_all add: sinv_def\<close>)
    have inv1: "scinv \<rho>1 \<sigma>1 env1 [dp] X A"
    proof (rule scinv_pairs[OF c1(3)])
      note i = scinvD[OF Cons.prems(2)]
      have p: "\<forall>(rb', s', t')\<in>set [dp]. upok A env rb' X s' t'" using sc_sinv_pok[OF Cons.prems(1)] by simp
      have "dtyped \<rho> [dp]" "dsolved \<rho> \<sigma> [dp]" using i(6,7) dtyped_mono dsolved_mono by auto
      then show "dtyped \<rho>1 [dp]" "dsolved \<rho>1 \<sigma>1 [dp]"
        using sc_dps_agree[OF p i(4) i(3) c1(4,5)] by blast+
    qed
    from SIMPL0_complete[OF fin si1 inv1, of ffs1 frs1]
    show "ncu (SIMPL0 alg dp st1) (ccon0 \<rho> \<sigma> env X A ffs frs)"
      unfolding st1 by (rule ncu_mono') (rule ccon0_trans[OF c1(1,2) c1(3-7) s1(3)[folded aa]])
  qed
qed


subsection \<open>Completeness of \<open>SIMPL\<close>\<close>

definition sccon :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow>
    sstate \<Rightarrow> bool" where
  "sccon \<rho> \<sigma> env X A st' \<longleftrightarrow> (case st' of (env', ffs, frs) \<Rightarrow> \<exists>\<rho>' \<sigma>'. scinv \<rho>' \<sigma>' env' (frs @ ffs) X A \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env')"

lemma ncu_SomeI: "(\<And>r. m = Some r \<Longrightarrow> snd r \<noteq> UErr CANTUNIFY \<and> (\<forall>x. snd r = UOk x \<longrightarrow> P x)) \<Longrightarrow> ncu m P"
  by (cases m) (auto simp: ncu_def)

lemma SIMPL_complete_aux:
  assumes "SIMPL alg' env dps = Some r"
  shows "alg' = alg \<Longrightarrow> finite X \<Longrightarrow> finite K \<Longrightarrow> sinv A K X env dps \<Longrightarrow> scinv \<rho> \<sigma> env dps X A \<Longrightarrow>
    snd r \<noteq> UErr CANTUNIFY \<and> (\<forall>st'. snd r = UOk st' \<longrightarrow> sccon \<rho> \<sigma> env X A st')"
  using assms
proof (induction alg' env dps r arbitrary: \<rho> \<sigma> rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 simpl alg' env dps r)
  note al = "1.prems"(1) and fin = "1.prems"(2,3) and si = "1.prems"(4) and inv = "1.prems"(5)
  have IH: "ncu (simpl alg env1 dps1) (sccon \<rho>1 \<sigma>1 env1 X A)"
    if "sinv A K X env1 dps1" "scinv \<rho>1 \<sigma>1 env1 dps1 X A" for env1 dps1 \<rho>1 \<sigma>1
  proof (rule ncu_SomeI)
    fix r1 assume "simpl alg env1 dps1 = Some r1"
    with "1.IH"[of alg env1 dps1 r1] al fin that
    show "snd r1 \<noteq> UErr CANTUNIFY \<and> (\<forall>x. snd r1 = UOk x \<longrightarrow> sccon \<rho>1 \<sigma>1 env1 X A x)" by blast
  qed
  let ?F = "foldrW (SIMPL0 alg) dps (env, [], [])"
  have body: "ncu (bindW ?F (\<lambda>st. case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then simpl alg env' dps else returnW st})) (sccon \<rho> \<sigma> env X A)"
  proof (rule ncu_bindW[OF ncu_cuok[OF foldrW_SIMPL0_complete[OF fin si inv] foldrW_SIMPL0_term[OF fin si]]])
    fix st assume P: "ccon0 \<rho> \<sigma> env X A [] [] st \<and> spost A K X env [] [] st"
    obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
    from P st have si': "sinv A K X env' (ffs @ frs)" unfolding spost_def by auto
    then have si1: "sinv A K X env' (frs @ ffs)" by (rule sinv_mono) auto
    from P st obtain \<rho>1 \<sigma>1 where c1: "scinv \<rho>1 \<sigma>1 env' (ffs @ frs) X A" "tagree (maxidx env) \<rho> \<rho>1"
      "sagree (maxidx env) \<sigma> \<sigma>1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "maxidx env \<le> maxidx env'"
      unfolding ccon0_def by auto
    have inv1: "scinv \<rho>1 \<sigma>1 env' (frs @ ffs) X A" by (rule scinv_mono[OF c1(1)]) auto
    have rec: "ncu (simpl alg env' (frs @ ffs)) (sccon \<rho> \<sigma> env X A)"
    proof (rule ncu_mono'[OF IH[OF si1 inv1]])
      fix st2 assume "sccon \<rho>1 \<sigma>1 env' X A st2"
      then show "sccon \<rho> \<sigma> env X A st2"
        using c1(2-5) unfolding sccon_def
        by (auto split: prod.splits intro: tagree_trans sagree_trans order_trans dest: tagree_trans[OF c1(2) _ c1(5)]
          sagree_trans[OF c1(3) _ c1(5)])
    qed
    have stop: "sccon \<rho> \<sigma> env X A st" using st inv1 c1(2-5) unfolding sccon_def by auto
    show "ncu (case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then simpl alg env' dps else returnW st}) (sccon \<rho> \<sigma> env X A)"
      unfolding st prod.case Let_def
      by (rule ncu_bindW[OF ncu_simps(4)[THEN iffD2, OF allI[OF impI[OF TrueI]]]])
        (use rec stop st in simp)
  qed
  have "bindW ?F (\<lambda>st. case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then simpl alg env' dps else returnW st}) = Some r"
    using "1.hyps"[unfolded al] by simp
  from body[unfolded this] show ?case by (cases r) (auto simp: ncu_def)
qed

text \<open>
  Completeness of \<^const>\<open>SIMPL\<close> for the algebra of the signature: if \<open>(\<rho>, \<sigma>)\<close> solves the pairs
  \<open>dps\<close> and the environment \<open>env\<close>, with the invariants \<^const>\<open>sinv\<close> of the termination proof (for a
  finite set \<open>X\<close> of variables and a finite set \<open>K\<close> of type variables) and \<^const>\<open>scinv\<close>, then
  \<^const>\<open>SIMPL\<close> does not raise \<open>CANTUNIFY\<close>, and every result \<open>(env', ffs, frs)\<close> has a solution that
  agrees with \<open>(\<rho>, \<sigma>)\<close> on the variables of index at most \<open>maxidx env\<close>, satisfies the invariant
  \<^const>\<open>scinv\<close> and solves \<open>frs @ ffs\<close>. (The invariant \<^const>\<open>sinv\<close> of the result is given by
  @{thm [source] SIMPL_term}.)
\<close>

theorem SIMPL_complete:
  assumes "SIMPL alg env dps = Some r"
    and "finite X" "finite K" "sinv A K X env dps" "scinv \<rho> \<sigma> env dps X A"
  shows "snd r \<noteq> UErr CANTUNIFY \<and> (\<forall>env' ffs frs. snd r = UOk (env', ffs, frs) \<longrightarrow>
    (\<exists>\<rho>' \<sigma>'. scinv \<rho>' \<sigma>' env' (frs @ ffs) X A \<and> dsolved \<rho>' \<sigma>' (frs @ ffs) \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'))"
proof (intro conjI allI impI)
  note c = SIMPL_complete_aux[OF assms(1) refl assms(2-5)]
  show "snd r \<noteq> UErr CANTUNIFY" using c by blast
  fix env' ffs frs assume "snd r = UOk (env', ffs, frs)"
  with c have "sccon \<rho> \<sigma> env X A (env', ffs, frs)" by blast
  then obtain \<rho>' \<sigma>' where "scinv \<rho>' \<sigma>' env' (frs @ ffs) X A" "tagree (maxidx env) \<rho> \<rho>'"
    "sagree (maxidx env) \<sigma> \<sigma>'"
    unfolding sccon_def by blast
  with scinvD(7)[OF this(1)] show "\<exists>\<rho>' \<sigma>'. scinv \<rho>' \<sigma>' env' (frs @ ffs) X A \<and> dsolved \<rho>' \<sigma>' (frs @ ffs) \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'" by blast
qed

end

end
