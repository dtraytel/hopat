section \<open>The Invariants of Environments and Problems\<close>

text \<open>
  The invariants of unification: a well-formed environment (\<open>einv\<close>), well-typed bindings and
  consistent, bounded variables for every solution of the type environment (\<open>winv\<close>),
  well-formed problems (\<open>upok\<close>), new bindings (\<open>newb\<close>) and new type variables (\<open>tnew\<close>),
  with the unification of types on a well-formed type environment. The statements of
  soundness and of termination both use them; this theory contains no measure.
\<close>

theory Pattern_Invariant
  imports Pattern_Known_Types Pattern_Closed_Env Pattern_Type_Reach
begin

subsection \<open>Unbound variables\<close>

context pure_sig_gen
begin

text \<open>The unbound variables of the problem \<open>X\<close> and the environment:\<close>

definition ubv :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> indexname set" where
  "ubv env X = {x \<in> fst ` (X \<union> evars env). vt_lookup (tenv env) x = None}"

subsection \<open>Typing of iterated abstractions\<close>

lemma typing_abs_list_inv:
  "e \<turnstile> abs_list bs t : U \<Longrightarrow> \<exists>V. U = map snd bs \<Rrightarrow> V \<and> pushes e (map snd bs) \<turnstile> t : V"
proof (induction bs arbitrary: e U)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  with Cons.prems obtain U' where U: "U = T \<rightarrow>\<^sub>T U'" "e\<langle>0:T\<rangle> \<turnstile> abs_list bs t : U'" by auto
  from Cons.IH[OF U(2)] obtain V where "U' = map snd bs \<Rrightarrow> V" "pushes (e\<langle>0:T\<rangle>) (map snd bs) \<turnstile> t : V"
    by blast
  with U b show ?case by auto
qed simp

lemma typing_abs_listE:
  assumes "e \<turnstile> abs_list bs t : U"
  obtains V where "U = map snd bs \<Rrightarrow> V" "pushes e (map snd bs) \<turnstile> t : V"
  using typing_abs_list_inv[OF assms] by blast

subsection \<open>New bindings\<close>

text \<open>The new bindings of an extension contain only fresh variables:\<close>

definition newb :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "newb env env' \<longleftrightarrow> extends env env' \<and>
    (\<forall>x U u y T. vt_lookup (tenv env') x = Some (U, u) \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
      (y, T) \<in> vars u \<longrightarrow> maxidx env < snd y)"

definition bbelow :: "env \<Rightarrow> bool" where
  "bbelow env \<longleftrightarrow> (\<forall>x b. vt_lookup (tenv env) x = Some b \<longrightarrow> snd x \<le> maxidx env)"

lemma newbD:
  assumes "newb env env'"
  shows "extends env env'"
    and "vt_lookup (tenv env') x = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> (y, T) \<in> vars u \<Longrightarrow>
      maxidx env < snd y"
  using assms unfolding newb_def by blast+

lemma bbelowD: "bbelow env \<Longrightarrow> vt_lookup (tenv env) x = Some b \<Longrightarrow> snd x \<le> maxidx env"
  unfolding bbelow_def by blast

lemma bbelow_mono:
  assumes "bbelow env" "tenv env' = tenv env" "maxidx env \<le> maxidx env'"
  shows "bbelow env'"
  unfolding bbelow_def
proof (intro allI impI)
  fix x b assume "vt_lookup (tenv env') x = Some b"
  with assms(2) have "vt_lookup (tenv env) x = Some b" by simp
  then have "snd x \<le> maxidx env" by (rule bbelowD[OF assms(1)])
  with assms(3) show "snd x \<le> maxidx env'" by simp
qed

lemma newb_refl [simp]: "newb env env"
  by (simp add: newb_def)

lemma newb_trans:
  assumes "newb env env1" "newb env1 env2"
  shows "newb env env2"
  unfolding newb_def
proof (intro conjI allI impI)
  note e1 = newbD(1)[OF assms(1)] and e2 = newbD(1)[OF assms(2)]
  show "extends env env2" by (rule extends_trans[OF e1 e2])
  fix x U u y T assume x2: "vt_lookup (tenv env2) x = Some (U, u)" and x0: "vt_lookup (tenv env) x = None"
    and y: "(y, T) \<in> vars u"
  have le: "maxidx env \<le> maxidx env1" using e1 by (simp add: extends_def)
  show "maxidx env < snd y"
  proof (cases "vt_lookup (tenv env1) x")
    case None
    with newbD(2)[OF assms(2) x2 _ y] le show ?thesis by simp
  next
    case (Some b)
    with e2 x2 have "vt_lookup (tenv env1) x = Some (U, u)" using extends_lookup by fastforce
    from newbD(2)[OF assms(1) this x0 y] show ?thesis .
  qed
qed

lemma newb_genvar: "genvar a env T = (env', G) \<Longrightarrow> newb env env'"
  by (simp add: newb_def genvar_simps extends_genvar)

lemma newb_update:
  assumes "ok (update (F, T) u env) env'" "\<And>y U. (y, U) \<in> vars u \<Longrightarrow> maxidx env0 < snd y" "newb env0 env"
  shows "newb env0 env'"
  unfolding newb_def
proof (intro conjI allI impI)
  note u = ok_update[OF assms(1)]
  show "extends env0 env'" by (rule extends_trans[OF newbD(1)[OF assms(3)] extends_update[OF assms(1)]])
  fix x U' u' y T' assume x': "vt_lookup (tenv env') x = Some (U', u')" and x0: "vt_lookup (tenv env0) x = None"
    and y: "(y, T') \<in> vars u'"
  show "maxidx env0 < snd y"
  proof (cases "x = F")
    case True
    with x' u(2) have "u' = u" by simp
    with assms(2) y show ?thesis by blast
  next
    case False
    with x' u(2) have "vt_lookup (tenv env) x = Some (U', u')" by simp
    from newbD(2)[OF assms(3) this x0 y] show ?thesis .
  qed
qed

subsection \<open>The most general instantiation\<close>

text \<open>
  Normalization by an acyclic type environment whose bindings are certified is a certified type
  instantiation; it is the most general solution of the type environment.
\<close>

lemma sorts_ok_tsubst:
  "sorts_ok alg T \<Longrightarrow> (\<And>v S. (v, S) \<in> tvars T \<Longrightarrow> sorts_ok alg (\<rho> v S)) \<Longrightarrow> sorts_ok alg (tsubst \<rho> T)"
proof (induction T)
  case (Type a Ts)
  have "sorts_ok alg (tsubst \<rho> T)" if "T \<in> set Ts" for T
  proof (rule Type.IH[OF that])
    show "sorts_ok alg T" using Type.prems(1) that by simp
    fix v S assume "(v, S) \<in> tvars T"
    with that show "sorts_ok alg (\<rho> v S)" by (intro Type.prems(2)) auto
  qed
  then show ?case by simp
qed auto

lemma sorts_ok_tnorm:
  assumes ac: "tacyc \<theta>" and sc: "\<And>v S U. vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> sorts_ok alg U"
    and "sorts_ok alg T"
  shows "sorts_ok alg (tnorm \<theta> T)"
proof -
  have var: "sorts_ok alg (tnorm \<theta> (TVar v S))" if "sort_ok alg S" for v S
    using that
  proof (induction v arbitrary: S rule: tdep_induct[OF ac])
    case (1 v)
    show ?case
    proof (cases "vt_lookup \<theta> v")
      case (Some b)
      obtain S0 U where b: "b = (S0, U)" by force
      have U: "sorts_ok alg U" using sc[of v S0 U] Some b by simp
      have "sorts_ok alg (tnorm \<theta> (TVar w S'))" if "(w, S') \<in> tvars U" for w S'
      proof (rule "1.IH")
        show "(w, v) \<in> tdep \<theta>" using that Some b by (force simp: tdep_def)
        show "sort_ok alg S'" using U that by (induction U) auto
      qed
      then have "sorts_ok alg (tsubst (\<lambda>w S'. tnorm \<theta> (TVar w S')) U)"
        using U by (intro sorts_ok_tsubst) auto
      then have "sorts_ok alg (tnorm \<theta> U)" unfolding tnorm_tsubst[of \<theta> U] .
      then show ?thesis using Some b by (simp add: tnorm_TVar[OF ac])
    qed (use "1.prems" in \<open>simp add: tnorm_TVar[OF ac]\<close>)
  qed
  have "sort_ok alg S" if "(v, S) \<in> tvars T" for v S using assms(3) that by (induction T) auto
  then show ?thesis by (subst tnorm_tsubst) (use var assms(3) in \<open>auto intro: sorts_ok_tsubst\<close>)
qed

lemma cert_inst_tnorm:
  assumes ac: "tacyc \<theta>" and b: "\<And>v S U. vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> wft ar U \<and> sorts_ok alg U"
  shows "cert_inst (tnorm_inst \<theta>)"
  unfolding cert_inst_def cert_typ_def
proof (intro allI impI conjI)
  fix v S assume S: "sort_ok alg S"
  show "wft ar (tnorm \<theta> (TVar v S))" by (rule wft_tnorm[OF ac]) (use b in simp_all)
  show "sorts_ok alg (tnorm \<theta> (TVar v S))" by (rule sorts_ok_tnorm[OF ac]) (use b S in simp_all)
qed

lemma tsol_tnorm:
  assumes ac: "tacyc \<theta>"
  shows "tsol \<theta> (tnorm_inst \<theta>)"
  unfolding tsol_def
proof (intro allI impI)
  fix v S U assume "vt_lookup \<theta> v = Some (S, U)"
  then show "tnorm \<theta> (TVar v S) = tsubst (tnorm_inst \<theta>) U"
    by (subst tnorm_tsubst[symmetric]) (simp add: tnorm_TVar[OF ac])
qed

subsection \<open>Invariants\<close>

text \<open>
  The invariants of the environments, which need not have solutions (the termination proofs
  and the invariant of the unifiers both use them):
  \<^item> \<open>einv A env\<close>: the type environment is acyclic, its type variables (and those of \<open>A\<close>) have
    unique sorts and indices at most \<^const>\<open>maxidx\<close>, and its bindings are certified; the term
    environment is acyclic, its bindings are closed and their variables are known.
  \<^item> \<open>winv env X\<close>: for every certified solution \<open>\<rho>\<close> of the type environment, the bindings are
    well-typed and the variables \<open>X\<close> of the problem are consistent (the invariants of soundness).
\<close>

definition einv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "einv A K env \<longleftrightarrow> tvinv A env \<and> scert alg (tyenv env) \<and> tcert alg (tvars_env (tyenv env) \<union> A) \<and>
    tcovered (tyenv env) K (tvars_env (tyenv env) \<union> A) \<and> acyc env \<and> closed_env env \<and> bbelow env \<and>
    tsorted alg (tyenv env)"

definition winv :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "winv env X \<longleftrightarrow> (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> wt_env \<rho> env \<and> vinv \<rho> env X)"

lemma einvD:
  assumes "einv A K env"
  shows "tvinv A env" "tinv ar (maxidx env) (tyenv env) A" "acyc env" "closed_env env" "bbelow env"
    "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "vt_lookup (tyenv env) v = Some (S, U) \<Longrightarrow> sorts_ok alg U"
    "scert alg (tyenv env)" "tcert alg (tvars_env (tyenv env) \<union> A)"
    "tcovered (tyenv env) K (tvars_env (tyenv env) \<union> A)" "tsorted alg (tyenv env)"
  using assms tvinvD(1)[of A env] tinv_tacyc tinv_tcons_env unfolding einv_def scert_def by blast+

lemma winvD: "winv env X \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> wt_env \<rho> env \<and> vinv \<rho> env X"
  unfolding winv_def by blast

text \<open>The most general solution of the type environment is certified:\<close>

lemma einv_rho0:
  assumes "einv A K env"
  shows "tsol (tyenv env) (tnorm_inst (tyenv env))" "cert_inst (tnorm_inst (tyenv env))"
proof -
  note e = einvD[OF assms]
  show "tsol (tyenv env) (tnorm_inst (tyenv env))" by (rule tsol_tnorm[OF e(6)])
  show "cert_inst (tnorm_inst (tyenv env))"
    by (rule cert_inst_tnorm[OF e(6)]) (use e(2,8) tinv_wft in blast)
qed

lemma tsubst_tnorm_inst [simp]: "tsubst (tnorm_inst \<theta>) T = tnorm \<theta> T"
  by (simp flip: tnorm_tsubst)

lemma size_funs: "size T \<le> size (Ts \<Rrightarrow> T)"
  by (induction Ts) auto

subsection \<open>New type variables\<close>

text \<open>
  From \<open>env\<close> with the known type variables \<open>A\<close> to \<open>env'\<close> with the known type variables \<open>A'\<close>,
  only type variables that are known or have indices above the maximal index of \<open>env\<close> are
  introduced:
\<close>

definition tnew :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "tnew A env A' env' \<longleftrightarrow>
    tvars_env (tyenv env') \<union> A' \<subseteq> tvars_env (tyenv env) \<union> A \<union> {p. maxidx env < snd (fst p)}"

lemma tnew_refl [simp]: "tnew A env A env"
  by (auto simp: tnew_def)

lemma tnew_trans:
  assumes "tnew A env A1 env1" "tnew A1 env1 A2 env2" "maxidx env \<le> maxidx env1"
  shows "tnew A env A2 env2"
  using assms unfolding tnew_def by fastforce

lemma tnew_tyenv: "tyenv env' = tyenv env \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> tnew A env A' env'"
  by (auto simp: tnew_def)

lemma tnewD: "tnew A env A' env' \<Longrightarrow> tvars_env (tyenv env') \<subseteq> tvars_env (tyenv env) \<union> A \<union> {p. maxidx env < snd (fst p)}"
  by (auto simp: tnew_def)

subsection \<open>Type unification\<close>

lemma unify_types_term:
  assumes ei: "einv A K env" and fin: "finite K"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar T" "sorts_ok alg T"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar U" "sorts_ok alg U"
  shows "(\<exists>env'. unify_types alg T U env = return env' \<and> einv A K env' \<and> tenv env' = tenv env \<and>
      textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))) \<or>
    (\<exists>u. unify_types alg T U env = raise (Unif u))"
proof (cases "T = U")
  case True
  then show ?thesis using ei by (simp add: unify_types_def)
next
  case False
  note e = einvD[OF ei]
  note ua = unify_aux_ok[OF e(2) U(1) T(1) U(2) T(2)]
  from ua show ?thesis
  proof (elim disjE exE conjE)
    fix \<theta>' n' assume r: "unify_aux alg U T (tyenv env, maxidx env) = return (\<theta>', n')"
      and st: "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> U = tsubst \<rho> T) (tyenv env) (maxidx env) \<theta>' n'"
      and sol: "\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> tsubst \<rho> U = tsubst \<rho> T"
    let ?env' = "Envir n' (tenv env) \<theta>'"
    have r': "unify_types alg T U env = return ?env'"
      using False r by (simp add: unify_types_def type_unify_def)
    note s = tstepD[OF st]
    have tv: "tvars_env (tyenv env) \<subseteq> tvars_env \<theta>'" by (rule tvars_env_textends[OF s(1)])
    have ac': "tacyc \<theta>'" by (rule tinv_tacyc[OF s(3)])
    have cov: "tcovered (tyenv env) K (tvars_env (tyenv env) \<union> tvars U \<union> tvars T)"
      by (rule tcovered_mono[OF e(11)]) (use T U in blast)
    have "tvinv A ?env'"
      unfolding tvinv_def using s(3) tvinvD(2)[OF e(1)] tv by fastforce
    moreover have "scert alg \<theta>'"
      by (rule unify_aux_scert[OF e(2) U(1) T(1) U(2) T(2) e(9) U(3) T(3) e(10) r])
    moreover have "tcert alg (tvars_env \<theta>' \<union> A)" using s(6)[OF e(10)] e(10) by simp
    moreover have "tcovered \<theta>' K (tvars_env \<theta>' \<union> A)"
    proof -
      have "tcovered \<theta>' K (tvars_env \<theta>')" by (rule unify_aux_covered[OF e(2) U(1) T(1) U(2) T(2) cov r])
      moreover have "tcovered \<theta>' K A" by (rule tcovered_textends[OF ac' s(1)]) (use e(11) in simp)
      ultimately show ?thesis by simp
    qed
    moreover have "bbelow ?env'" by (rule bbelow_mono[OF e(5)]) (use s(2) in simp_all)
    moreover have "tsorted alg \<theta>'" by (rule tsorted_tstep[OF e(12) st])
    ultimately have "einv A K ?env'" using e(3,4) by (simp add: einv_def acyc_def dep_def closed_env_def)
    moreover have "\<theta>' = tyenv env \<or> card (uvarsA \<theta>' K) < card (uvarsA (tyenv env) K)"
      by (rule unify_aux_card[OF e(2) U(1) T(1) U(2) T(2) fin cov r])
    moreover have "tnew A env A ?env'" using s(7) by (auto simp: tnew_def)
    ultimately show ?thesis using r' s(1,2) tv sol by auto
  next
    assume "unify_aux alg U T (tyenv env, maxidx env) = raise TUnify"
    then show ?thesis using False by (simp add: unify_types_def type_unify_def)
  qed
qed

end

subsection \<open>Variables under reduction\<close>

context pure_sig_gen
begin

lemma not_dep_unbound:
  "vt_lookup (tenv env) G = None \<Longrightarrow> F \<noteq> G \<Longrightarrow> (F, G) \<notin> (dep env)\<^sup>*"
  by (auto elim: rtranclE elim!: depE)

lemma beta_vars: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> vars t \<subseteq> vars s"
  by (induction rule: beta.induct) (use vars_subst in auto)

lemma beta_reds_vars: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> vars t \<subseteq> vars s"
  by (induction rule: rtranclp_induct) (use beta_vars in auto)

subsection \<open>Well-formed problems of pattern unification\<close>

text \<open>
  A problem \<open>s =?= t\<close> under the binders \<open>bs\<close> is well-formed for the variables \<open>X\<close> if its
  variables are in \<open>X\<close> or the environment, its type variables are known, its loose bound variables
  are bound by \<open>bs\<close>, and it is well-typed for every certified solution of the type environment.
\<close>

definition upok :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "upok A env bs X s t \<longleftrightarrow> vars s \<union> vars t \<subseteq> X \<union> evars env \<and>
    ttvars s \<union> ttvars t \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    \<not> loose_bvar s (ilength bs) \<and> \<not> loose_bvar t (ilength bs) \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T))"

lemma upokD:
  assumes "upok A env bs X s t"
  shows "vars s \<subseteq> X \<union> evars env" "vars t \<subseteq> X \<union> evars env"
    "ttvars s \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<not> loose_bvar s (ilength bs)" "\<not> loose_bvar t (ilength bs)"
    "tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
  using assms unfolding upok_def by blast+

lemma cert_typ_tsubst_rev:
  assumes "cert_typ alg ar (tsubst \<rho> T)" "tcert alg (tvars T)"
  shows "wft ar T" "sorts_ok alg T"
proof -
  have "wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar T" by (induction T) auto
  then show "wft ar T" using assms(1) by (simp add: cert_typ_def)
  have "sorts_ok alg (tsubst \<rho> T) \<Longrightarrow> tcert alg (tvars T) \<Longrightarrow> sorts_ok alg T"
  proof (induction T)
    case (Type a Ts)
    then show ?case by (auto simp: tcert_def)
  qed (auto simp: tcert_def)
  then show "sorts_ok alg T" using assms by (simp add: cert_typ_def)
qed

lemma lift_rigid: "rigid h \<Longrightarrow> rigid (lift h k)"
  by (cases h) simp_all

end

context pure_sig_gen
begin

abbreviation rho0 :: "env \<Rightarrow> tinst" where
  "rho0 env \<equiv> tnorm_inst (tyenv env)"

end

end
