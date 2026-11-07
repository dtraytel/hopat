section \<open>Termination of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Term
  imports Unify_Simpl_Term Unify_Flexflex_Sound
begin

context pure_sig
begin

text \<open>
  The flex-flex pairs that \<^const>\<open>SIMPL\<close> leaves are treated by \<open>foldrW (add_ffpair alg)\<close>
  (in \<^const>\<open>pull\<close>). This treatment terminates without exceptions on pairs that satisfy the
  invariants of theory \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>, have the shape
  \<^const>\<open>ff_shape\<close>, and are of a base type in the most general solution of the type environment
  (\<open>ffeta\<close> below). The last condition is needed: for \<open>?F a =?= ?H\<close> of a function type
  and \<open>?F B.1 B.0 =?= ?K B.1 B.0\<close>, the assignment \<open>?F := \<lambda>x y. ?K x y\<close> makes the first pair
  normalize to an abstraction, and \<open>add_ffpair\<close> raises \<open>TERM\<close>.

  The type environment does not change: \<open>ff_assign\<close> only unifies types that are equal in the most
  general solution. The new bindings are flexible terms \<open>\<lambda>xs. ?G ts\<close> whose heads are unbound in
  the original environment, so normalization keeps the pairs flexible, and the occurs check and the
  new variables of \<open>clean_term\<close> keep the environment acyclic.
\<close>

subsection \<open>Normalization\<close>

lemma ff_tvars_tnorm:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>"
  shows "tcons \<theta> T \<Longrightarrow> tvars (tnorm \<theta> T) \<subseteq> tvars T \<union> tvars_env \<theta>"
proof (induction rule: tnorm_induct[OF ac tc, consumes 1, case_names TFree Type Unbound Bound])
  case (Type a Ts)
  then show ?case by auto
next
  case (Unbound v S)
  then show ?case by (simp add: tnorm_TVar[OF ac])
next
  case (Bound v S U)
  then show ?case using tvars_envI2[OF Bound(1)] by (auto simp: tnorm_TVar[OF ac])
qed simp

text \<open>The properties of the results of normalization that we need:\<close>

definition npost :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> bool" where
  "npost A env t' \<longleftrightarrow> vok env (vars t' \<union> evars env) \<and> ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    (\<forall>x T. head_of t' = Var x T \<longrightarrow> vt_lookup (tenv env) x = None \<and> tnorm (tyenv env) T = T)"

lemma ff_vok_Var_unbound:
  "vok env (evars env) \<Longrightarrow> tcons (tyenv env) T \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> vok env (vars (Var x T) \<union> evars env)"
  unfolding vok_def by auto

lemma ff_vok_Un: "vok env (X \<union> Y) \<longleftrightarrow> vok env X \<and> vok env Y"
  unfolding vok_def ball_Un by (rule refl)

lemma ff_vok_App: "vok env (vars (f $ u) \<union> evars env) \<longleftrightarrow> vok env (vars f \<union> evars env) \<and> vok env (vars u \<union> evars env)"
  by (auto simp: ff_vok_Un)

lemma ff_lookup1_ok:
  assumes "vt_is_empty (tyenv env)" "vok env ({(x, T)} \<union> evars env)"
  shows "lookup1 (tenv env) x T = return (map_option snd (vt_lookup (tenv env) x))"
proof (cases "vt_lookup (tenv env) x")
  case (Some b)
  obtain U u where b: "b = (U, u)" by force
  have "tnorm (tyenv env) T = tnorm (tyenv env) U" using vokD(2)[OF assms(2), of x T U u] Some b by simp
  then have "T = U" by (simp add: tnorm_empty[OF assms(1)])
  with Some b show ?thesis by (simp add: lookup1_def)
qed (simp add: lookup1_def)

context
  fixes A K env assumes ei: "einv A K env"
begin

lemma ff_tcons: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> tcons (tyenv env) T"
  by (rule tinv_tcons[OF einvD(2)[OF ei]])

lemma ff_norm_type:
  assumes "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "norm_type_aux (tyenv env) T = return (tnorm (tyenv env) T)"
    "tvars (tnorm (tyenv env) T) \<subseteq> tvars_env (tyenv env) \<union> A"
  using norm_type_aux_ok[OF einvD(6,7)[OF ei] ff_tcons[OF assms]]
    ff_tvars_tnorm[OF einvD(6,7)[OF ei] ff_tcons[OF assms]] assms by auto

lemma ff_hrk_less:
  assumes "vt_lookup (tenv env) x = Some (U, u)"
  shows "hrk env u < hrk env (Var x T)"
proof (cases u)
  case (Var y U')
  have "(y, x) \<in> dep env" using depI[OF assms, of y U'] Var by simp
  then show ?thesis using rk_less[OF einvD(3)[OF ei]] Var by (simp add: hrk_def)
qed (simp_all add: hrk_def)

lemma norm_term2_term:
  "vok env (vars t \<union> evars env) \<Longrightarrow> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    termip (sup beta subt) (inst (rho0 env) (unf env t)) \<Longrightarrow>
    \<exists>t'. norm_term2 env t = return t' \<and> npost A env t'"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (inst (rho0 env) (unf env t), hrk env t)"]])
  case (1 t)
  note e = einvD[OF ei]
  let ?M = "\<lambda>t. inst (rho0 env) (unf env t)"
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have sn: "termip (sup beta subt) u" if "(sup beta subt)\<^sup>*\<^sup>* (?M t) u" for u
    by (rule termip_sup_reds[OF that "1.prems"(3)])
  have IH: "\<exists>t'. norm_term2 env u = return t' \<and> npost A env t'"
    if "vok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M u)" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    have "(?M u, ?M t) \<in> sn_less"
      by (simp only: sn_less_def mem_Collect_eq case_prod_conv) (use that(3) "1.prems"(3) in blast)
    then show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (?M t, hrk env t))"
      by simp
    show "termip (sup beta subt) (?M u)" by (rule sn[OF tranclp_into_rtranclp[OF that(3)]])
  qed
  have IH': "\<exists>t'. norm_term2 env u = return t' \<and> npost A env t'"
    if "vok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "?M u = ?M t" "hrk env u < hrk env t" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (?M t, hrk env t))"
      using that(3,4) by simp
    show "termip (sup beta subt) (?M u)" by (subst that(3)) (rule "1.prems"(3))
  qed
  have ve: "vok env (evars env)" using "1.prems"(1) by (rule vok_mono) blast
  have redex: "\<exists>t'. norm_term2 env (subst_bound u body) = return t' \<and> npost A env t'"
    if "(sup beta subt)\<^sup>*\<^sup>* (?M t) (?M (Abs b U body $ u))" "vok env (vars body \<union> vars u \<union> evars env)"
      "ttvars body \<union> ttvars u \<subseteq> ?KN"
    for b U body u
  proof (subst subst_bound_subst, rule IH)
    have r: "?M (Abs b U body $ u) \<rightarrow>\<^sub>\<beta> ?M (body[u/0])"
      using inst_beta[of "rho0 env" b U "unf env body" "unf env u"] by (simp add: unf_subst[OF e(3,4)])
    then show "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M (body[u/0]))"
      using that(1) by (meson rtranclp_into_tranclp1 sup2I1)
    show "vok env (vars (body[u/0]) \<union> evars env)"
      using vok_mono[OF that(2)] vars_subst[of body u 0] by blast
    show "ttvars (body[u/0]) \<subseteq> ?KN" using ttvars_subst[of body u 0] that(3) by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    have lk: "lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
      by (rule lookup_ok[OF e(6,7) vok_mono[OF "1.prems"(1)]]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have u: "?M u = ?M t" using Some p Var by (simp add: unf_Var[OF e(3)])
      have "hrk env u < hrk env t" using ff_hrk_less[OF Some[unfolded p]] Var by simp
      moreover have "vok env (vars u \<union> evars env)" by (rule vok_binding[OF "1.prems"(1) Some[unfolded p]])
      moreover have "ttvars u \<subseteq> ?KN" using tvinvD(2)[OF e(1) Some[unfolded p]] by blast
      ultimately obtain t' where "norm_term2 env u = return t' \<and> npost A env t'" using IH'[of u] u by blast
      then show ?thesis using lk Var Some p by (subst norm_term2.simps) simp
    next
      case None
      have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Var by simp
      note nt = ff_norm_type[OF tv]
      have "npost A env (Var x (tnorm (tyenv env) T))"
        unfolding npost_def using ff_vok_Var_unbound[OF ve ff_tcons[OF nt(2)] None] nt(2) None
        by (simp add: tnorm_idem[OF e(6)])
      then show ?thesis using lk Var None nt(1) by (subst norm_term2.simps) simp
    qed
  next
    case (Abs a T body)
    have "subt (?M t) (?M body)" using Abs by (simp add: subt_def)
    then have "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M body)" by blast
    moreover have "vok env (vars body \<union> evars env)" using "1.prems"(1) Abs by simp
    moreover have "ttvars body \<subseteq> ?KN" using "1.prems"(2) Abs by simp
    ultimately obtain b' where b': "norm_term2 env body = return b'" "npost A env b'" using IH[of body] by blast
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Abs by simp
    note nt = ff_norm_type[OF tv]
    have "npost A env (Abs a (tnorm (tyenv env) T) b')" using b'(2) nt(2) by (simp add: npost_def)
    then show ?thesis using Abs b'(1) nt(1) by (subst norm_term2.simps) simp
  next
    case (App f u)
    have vfu: "vok env (vars f \<union> evars env)" "vok env (vars u \<union> evars env)"
      using "1.prems"(1) App ff_vok_App by blast+
    have tfu: "ttvars f \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" using "1.prems"(2) App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      have "vok env (vars body \<union> vars u \<union> evars env)" using vfu f by (simp add: ff_vok_Un)
      moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using tfu f by simp
      ultimately obtain t' where "norm_term2 env (subst_bound u body) = return t' \<and> npost A env t'"
        using redex[of b U body u] f App by blast
      then show ?thesis using f App by (subst norm_term2.simps) simp
    next
      case False
      have "subt (?M t) (?M f)" using App by (simp add: subt_def)
      then have tf: "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M f)" by blast
      from IH[OF vfu(1) tfu(1) tf] obtain nf where nf: "norm_term2 env f = return nf" "npost A env nf" by blast
      have fnf: "?M f \<rightarrow>\<^sub>\<beta>\<^sup>* ?M nf"
        by (rule norm_term2_unf[OF nf(1)[unfolded return_def] refl e(3,4) einv_rho0(1)[OF ei]])
      have hn: "norm_term2 env t =
          (case nf of Abs _ _ body \<Rightarrow> norm_term2 env (subst_bound u body) | _ \<Rightarrow> do {nu \<leftarrow> norm_term2 env u; return (nf $ nu)})"
        using App False nf(1) by (subst norm_term2.simps) (cases f; simp)
      note nfp = nf(2)[unfolded npost_def]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U body where nfA: "nf = Abs b U body" by (cases nf) auto
        have "(sup beta subt)\<^sup>*\<^sup>* (?M t) (?M (Abs b U body $ u))"
          using App nfA beta_reds_sup[OF rtrancl_beta_AppL[OF fnf, of "?M u"]] by simp
        moreover have "vok env (vars body \<union> vars u \<union> evars env)"
          using nfp vfu(2) nfA by (simp add: ff_vok_Un)
        moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using nfp tfu(2) nfA by simp
        ultimately obtain t' where "norm_term2 env (subst_bound u body) = return t' \<and> npost A env t'"
          using redex[of b U body u] by blast
        then show ?thesis using hn nfA by simp
      next
        case nA: False
        have "subt (?M t) (?M u)" using App by (simp add: subt_def)
        then have "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M u)" by blast
        from IH[OF vfu(2) tfu(2) this] obtain nu where nu: "norm_term2 env u = return nu" "npost A env nu" by blast
        have "norm_term2 env t = return (nf $ nu)" using hn nA nu(1) by (cases nf) auto
        moreover have "npost A env (nf $ nu)" using nf(2) nu(2) by (simp add: npost_def ff_vok_Un)
        ultimately show ?thesis by blast
      qed
    qed
  next
    case (Const a T)
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Const by simp
    note nt = ff_norm_type[OF tv]
    have "npost A env (Const a (tnorm (tyenv env) T))" using ve nt(2) by (simp add: npost_def)
    then show ?thesis using Const nt(1) by (subst norm_term2.simps) simp
  next
    case (Free a T)
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Free by simp
    note nt = ff_norm_type[OF tv]
    have "npost A env (Free a (tnorm (tyenv env) T))" using ve nt(2) by (simp add: npost_def)
    then show ?thesis using Free nt(1) by (subst norm_term2.simps) simp
  next
    case (Bound i)
    have "npost A env t" using ve Bound by (simp add: npost_def)
    then show ?thesis using Bound by (subst norm_term2.simps) simp
  qed
qed

lemma norm_term1_term:
  assumes em: "vt_is_empty (tyenv env)"
  shows "vok env (vars t \<union> evars env) \<Longrightarrow> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    termip (sup beta subt) (unf env t) \<Longrightarrow>
    \<exists>t'. norm_term1 (tenv env) t = return t' \<and> npost A env t'"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (unf env t, hrk env t)"]])
  case (1 t)
  note e = einvD[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have sn: "termip (sup beta subt) u" if "(sup beta subt)\<^sup>*\<^sup>* (unf env t) u" for u
    by (rule termip_sup_reds[OF that "1.prems"(3)])
  have IH: "\<exists>t'. norm_term1 (tenv env) u = return t' \<and> npost A env t'"
    if "vok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env u)" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    have "(unf env u, unf env t) \<in> sn_less"
      by (simp only: sn_less_def mem_Collect_eq case_prod_conv) (use that(3) "1.prems"(3) in blast)
    then show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (unf env t, hrk env t))"
      by simp
    show "termip (sup beta subt) (unf env u)" by (rule sn[OF tranclp_into_rtranclp[OF that(3)]])
  qed
  have IH': "\<exists>t'. norm_term1 (tenv env) u = return t' \<and> npost A env t'"
    if "vok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "unf env u = unf env t" "hrk env u < hrk env t" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (unf env t, hrk env t))"
      using that(3,4) by simp
    show "termip (sup beta subt) (unf env u)" by (subst that(3)) (rule "1.prems"(3))
  qed
  have ve: "vok env (evars env)" using "1.prems"(1) by (rule vok_mono) blast
  have self: "npost A env t" if "\<forall>x T. head_of t = Var x T \<longrightarrow> vt_lookup (tenv env) x = None"
    using that "1.prems"(1,2) by (simp add: npost_def tnorm_empty[OF em])
  have redex: "\<exists>t'. norm_term1 (tenv env) (subst_bound u body) = return t' \<and> npost A env t'"
    if "(sup beta subt)\<^sup>*\<^sup>* (unf env t) (unf env (Abs b U body $ u))" "vok env (vars body \<union> vars u \<union> evars env)"
      "ttvars body \<union> ttvars u \<subseteq> ?KN"
    for b U body u
  proof (subst subst_bound_subst, rule IH)
    have r: "unf env (Abs b U body $ u) \<rightarrow>\<^sub>\<beta> unf env (body[u/0])"
      by (simp add: unf_subst[OF e(3,4)])
    then show "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env (body[u/0]))"
      using that(1) by (meson rtranclp_into_tranclp1 sup2I1)
    show "vok env (vars (body[u/0]) \<union> evars env)"
      using vok_mono[OF that(2)] vars_subst[of body u 0] by blast
    show "ttvars (body[u/0]) \<subseteq> ?KN" using ttvars_subst[of body u 0] that(3) by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    have lk: "lookup1 (tenv env) x T = return (map_option snd (vt_lookup (tenv env) x))"
      by (rule ff_lookup1_ok[OF em vok_mono[OF "1.prems"(1)]]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have u: "unf env u = unf env t" using Some p Var by (simp add: unf_Var[OF e(3)])
      have "hrk env u < hrk env t" using ff_hrk_less[OF Some[unfolded p]] Var by simp
      moreover have "vok env (vars u \<union> evars env)" by (rule vok_binding[OF "1.prems"(1) Some[unfolded p]])
      moreover have "ttvars u \<subseteq> ?KN" using tvinvD(2)[OF e(1) Some[unfolded p]] by blast
      ultimately obtain t' where "norm_term1 (tenv env) u = return t' \<and> npost A env t'" using IH'[of u] u by blast
      then show ?thesis using lk Var Some p by (subst norm_term1.simps) simp
    next
      case None
      have "npost A env t" by (rule self) (use None Var in simp)
      then show ?thesis using lk Var None by (subst norm_term1.simps) simp
    qed
  next
    case (Abs a T body)
    have "subt (unf env t) (unf env body)" using Abs by (simp add: subt_def)
    then have "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env body)" by blast
    moreover have "vok env (vars body \<union> evars env)" using "1.prems"(1) Abs by simp
    moreover have "ttvars body \<subseteq> ?KN" using "1.prems"(2) Abs by simp
    ultimately obtain b' where b': "norm_term1 (tenv env) body = return b'" "npost A env b'" using IH[of body] by blast
    have "npost A env (Abs a T b')" using b'(2) "1.prems"(2) Abs by (simp add: npost_def)
    then show ?thesis using Abs b'(1) by (subst norm_term1.simps) simp
  next
    case (App f u)
    have vfu: "vok env (vars f \<union> evars env)" "vok env (vars u \<union> evars env)"
      using "1.prems"(1) App ff_vok_App by blast+
    have tfu: "ttvars f \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" using "1.prems"(2) App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      have "vok env (vars body \<union> vars u \<union> evars env)" using vfu f by (simp add: ff_vok_Un)
      moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using tfu f by simp
      ultimately obtain t' where "norm_term1 (tenv env) (subst_bound u body) = return t' \<and> npost A env t'"
        using redex[of b U body u] f App by blast
      then show ?thesis using f App by (subst norm_term1.simps) simp
    next
      case False
      have "subt (unf env t) (unf env f)" using App by (simp add: subt_def)
      then have tf: "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env f)" by blast
      from IH[OF vfu(1) tfu(1) tf] obtain nf where nf: "norm_term1 (tenv env) f = return nf" "npost A env nf"
        by blast
      have fnf: "unf env f \<rightarrow>\<^sub>\<beta>\<^sup>* unf env nf"
        by (rule norm_term1_unf[OF nf(1)[unfolded return_def] refl refl e(3,4)])
      have hn: "norm_term1 (tenv env) t =
          (case nf of Abs _ _ body \<Rightarrow> norm_term1 (tenv env) (subst_bound u body)
           | _ \<Rightarrow> do {nu \<leftarrow> norm_term1 (tenv env) u; return (nf $ nu)})"
        using App False nf(1) by (subst norm_term1.simps) (cases f; simp)
      note nfp = nf(2)[unfolded npost_def]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U body where nfA: "nf = Abs b U body" by (cases nf) auto
        have "(sup beta subt)\<^sup>*\<^sup>* (unf env t) (unf env (Abs b U body $ u))"
          using App nfA beta_reds_sup[OF rtrancl_beta_AppL[OF fnf, of "unf env u"]] by simp
        moreover have "vok env (vars body \<union> vars u \<union> evars env)"
          using nfp vfu(2) nfA by (simp add: ff_vok_Un)
        moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using nfp tfu(2) nfA by simp
        ultimately obtain t' where "norm_term1 (tenv env) (subst_bound u body) = return t' \<and> npost A env t'"
          using redex[of b U body u] by blast
        then show ?thesis using hn nfA by simp
      next
        case nA: False
        have "subt (unf env t) (unf env u)" using App by (simp add: subt_def)
        then have "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env u)" by blast
        from IH[OF vfu(2) tfu(2) this] obtain nu where nu: "norm_term1 (tenv env) u = return nu" "npost A env nu"
          by blast
        have "norm_term1 (tenv env) t = return (nf $ nu)" using hn nA nu(1) by (cases nf) auto
        moreover have "npost A env (nf $ nu)" using nf(2) nu(2) by (simp add: npost_def ff_vok_Un)
        ultimately show ?thesis by blast
      qed
    qed
  qed (subst norm_term1.simps; use self in simp)+
qed

text \<open>Normalization terminates on terms that are well-typed in the most general solution:\<close>

theorem norm_term_term:
  assumes vk: "vok env (vars t \<union> evars env)" and tv: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and wte: "wt_env (rho0 env) env" and vc: "vcons (rho0 env) (vars t \<union> evars env)"
    and ty: "e \<turnstile> inst (rho0 env) t : T"
  shows "\<exists>t'. norm_term env t = return t' \<and> npost A env t'"
proof -
  note e = einvD[OF ei]
  have tu: "e \<turnstile> inst (rho0 env) (unf env t) : T" by (rule typing_unf[OF e(3) wte vc ty])
  have sn: "termip beta (inst (rho0 env) (unf env t))" by (rule type_implies_termi[OF tu])
  show ?thesis
  proof (cases "env_is_empty env \<and> \<not> could_beta_contract t")
    case True
    then have em: "vt_is_empty (tenv env)" "vt_is_empty (tyenv env)" by (simp_all add: env_is_empty_def)
    have "npost A env t" using vk tv by (simp add: npost_def tnorm_empty[OF em(2)] vt_is_empty_lookup[OF em(1)])
    with True show ?thesis by (simp add: norm_term_def)
  next
    case nid: False
    show ?thesis
    proof (cases "vt_is_empty (tyenv env)")
      case True
      have "termip (sup beta subt) (unf env t)" by (rule termip_beta_subt[OF termip_inst[OF sn refl]])
      moreover have "norm_term env t = norm_term1 (tenv env) t"
        unfolding norm_term_def by (simp only: if_not_P[OF nid] if_P[OF True])
      ultimately show ?thesis using norm_term1_term[OF True vk tv] by simp
    next
      case False
      have "norm_term env t = norm_term2 env t"
        unfolding norm_term_def by (simp only: if_not_P[OF nid] if_not_P[OF False])
      then show ?thesis using norm_term2_term[OF vk tv termip_beta_subt[OF sn]] by simp
    qed
  qed
qed

end

subsection \<open>Flexible terms\<close>

text \<open>
  The terms \<open>\<lambda>xs. ?G ts\<close> whose head is unbound in an environment \<open>env0\<close>; the bindings that the
  treatment of flex-flex pairs adds to \<open>env0\<close> are such terms:
\<close>

definition flexb :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "flexb env0 t \<longleftrightarrow> (\<exists>bs G V ss. t = abs_list bs (Var G V \<degree>\<degree> ss) \<and> vt_lookup (tenv env0) G = None)"

definition iflex :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "iflex env0 env \<longleftrightarrow>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> vt_lookup (tenv env0) x = None \<longrightarrow> flexb env0 u)"

lemma iflexD: "iflex env0 env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> vt_lookup (tenv env0) x = None \<Longrightarrow> flexb env0 u"
  unfolding iflex_def by blast

lemma iflex_refl: "iflex env env"
  unfolding iflex_def by simp

lemma ff_apps_Var_nonApp: "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> h \<degree>\<degree> ss = Var x T \<longleftrightarrow> ss = [] \<and> h = Var x T"
  by (cases ss rule: rev_exhaust) auto

lemma flexb_Var: "flexb env0 (Var x T) \<longleftrightarrow> vt_lookup (tenv env0) x = None"
proof
  assume "flexb env0 (Var x T)"
  then obtain bs G V ss where e: "Var x T = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  have "bs = []" using e by (cases bs) auto
  with e have "Var G V \<degree>\<degree> ss = Var x T" by simp
  then have "G = x" by (cases ss rule: rev_exhaust) auto
  with G show "vt_lookup (tenv env0) x = None" by simp
next
  assume "vt_lookup (tenv env0) x = None"
  then show "flexb env0 (Var x T)" unfolding flexb_def by (intro exI[of _ "[]"]) auto
qed

lemma flexb_bs_Nil: "abs_list bs (Var G V \<degree>\<degree> ss) = t \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> bs = []"
  by (cases bs) auto

lemma flexb_Abs: "flexb env0 (Abs a T body) \<Longrightarrow> flexb env0 body"
proof -
  assume "flexb env0 (Abs a T body)"
  then obtain bs G V ss where e: "Abs a T body = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  show ?thesis
  proof (cases bs)
    case Nil
    with e not_App_apps_Abs[of "Var G V" ss] show ?thesis by simp
  next
    case (Cons b bs')
    obtain y U where "b = (y, U)" by force
    with e Cons have "body = abs_list bs' (Var G V \<degree>\<degree> ss)" by simp
    with G show ?thesis unfolding flexb_def by blast
  qed
qed

lemma flexb_App: "flexb env0 (f $ u) \<Longrightarrow> flexb env0 f \<and> \<not> is_Abs f"
proof -
  assume "flexb env0 (f $ u)"
  then obtain bs G V ss where e: "f $ u = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  have "bs = []" using flexb_bs_Nil[OF e[symmetric]] by simp
  with e have e': "Var G V \<degree>\<degree> ss = f $ u" by simp
  then obtain ss' where "ss = ss' @ [u]" "f = Var G V \<degree>\<degree> ss'" by (cases ss rule: rev_exhaust) auto
  then have f: "f = abs_list [] (Var G V \<degree>\<degree> ss')" "\<not> is_Abs f" using not_App_apps_Abs[of "Var G V" ss'] by simp_all
  from f(1) G have "flexb env0 f" unfolding flexb_def by blast
  with f(2) show ?thesis by simp
qed

lemma abs_list_flex_neq: "Const c T \<noteq> abs_list bs (Var G V \<degree>\<degree> ss)" "Free a T \<noteq> abs_list bs (Var G V \<degree>\<degree> ss)"
    "Bound i \<noteq> abs_list bs (Var G V \<degree>\<degree> ss)"
  by (cases bs; cases ss rule: rev_exhaust; auto)+

lemma flexb_rigid: "\<not> flexb env0 (Const c T)" "\<not> flexb env0 (Free a T)" "\<not> flexb env0 (Bound i)"
  unfolding flexb_def using abs_list_flex_neq by blast+

lemma flexb_AbsI: "flexb env0 body \<Longrightarrow> flexb env0 (Abs a T body)"
proof -
  assume "flexb env0 body"
  then obtain bs G V ss where e: "body = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  from e have "Abs a T body = abs_list ((a, T) # bs) (Var G V \<degree>\<degree> ss)" by simp
  with G show ?thesis unfolding flexb_def by blast
qed

lemma flexb_AppI: "flexb env0 f \<Longrightarrow> \<not> is_Abs f \<Longrightarrow> flexb env0 (f $ u)"
proof -
  assume "flexb env0 f" "\<not> is_Abs f"
  then obtain bs G V ss where e: "f = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  with \<open>\<not> is_Abs f\<close> have "bs = []" using flexb_bs_Nil by blast
  with e have "f $ u = abs_list [] (Var G V \<degree>\<degree> (ss @ [u]))" by simp
  with G show ?thesis unfolding flexb_def by blast
qed

lemma subst_abs_list_flex: "\<exists>ss'. (abs_list bs (Var G V \<degree>\<degree> ss))[u/k] = abs_list bs (Var G V \<degree>\<degree> ss')"
proof (induction bs arbitrary: u k)
  case Nil
  then show ?case by (simp add: subst_apps)
next
  case (Cons b bs)
  obtain y U where "b = (y, U)" by force
  with Cons.IH[of "lift u 0" "k + 1"] show ?case by auto
qed

lemma flexb_subst: "flexb env0 t \<Longrightarrow> flexb env0 (t[u/k])"
  unfolding flexb_def using subst_abs_list_flex by blast

text \<open>Normalization keeps flexible terms flexible, if the new bindings are flexible:\<close>

lemma norm_term1_flex:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> iflex env0 env \<Longrightarrow> flexb env0 t \<Longrightarrow> flexb env0 t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and fi = "1.prems"(3) and fl = "1.prems"(4)
  have IH: "flexb env0 u'" if "ok (nt te u) u'" "flexb env0 u" for u u'
    using "1.IH"[OF that(1) refl te fi that(2)] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    have x0: "vt_lookup (tenv env0) x = None" using fl Var by (simp add: flexb_Var)
    show ?thesis
    proof (cases lr)
      case (Some u)
      with ok_lookup1[OF lr] te have "vt_lookup (tenv env) x = Some (T, u)" by simp
      from iflexD[OF fi this x0] rest Some IH show ?thesis by simp
    qed (use rest fl in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH[OF this(1) flexb_Abs[OF fl[unfolded Abs]]] show ?thesis by (simp add: flexb_AbsI)
  next
    case (App f u)
    from flexb_App[OF fl[unfolded App]] have ff: "flexb env0 f" "\<not> is_Abs f" by simp_all
    with h App obtain nf where hf: "ok (nt te f) nf"
      and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
      by (cases f) auto
    have fnf: "flexb env0 nf" by (rule IH[OF hf ff(1)])
    show ?thesis
    proof (cases "is_Abs nf")
      case True
      then obtain b U0 body where nfA: "nf = Abs b U0 body" by (cases nf) auto
      with rest have "ok (nt te (subst_bound u body)) t'" by simp
      from IH[OF this] flexb_subst[OF flexb_Abs[OF fnf[unfolded nfA]]] show ?thesis by (simp add: subst_bound_subst)
    next
      case False
      with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
      with flexb_AppI[OF fnf False] show ?thesis by simp
    qed
  qed (use fl flexb_rigid in auto)
qed

lemma norm_term2_flex:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> iflex env0 env \<Longrightarrow> flexb env0 t \<Longrightarrow> flexb env0 t'"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and fi = "1.prems"(2) and fl = "1.prems"(3)
  have IH: "flexb env0 u'" if "ok (nt env u) u'" "flexb env0 u" for u u'
    using "1.IH"[OF that(1) refl fi that(2)] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    have x0: "vt_lookup (tenv env0) x = None" using fl Var by (simp add: flexb_Var)
    show ?thesis
    proof (cases lr)
      case (Some u)
      from lr Some obtain U where lk: "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      from iflexD[OF fi lk x0] rest Some IH show ?thesis by simp
    next
      case None
      from rest None obtain T' where "t' = Var x T'" by auto
      with x0 show ?thesis by (simp add: flexb_Var)
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (nt env body) body'" "t' = Abs a T' body'" by auto
    with IH[OF this(1) flexb_Abs[OF fl[unfolded Abs]]] show ?thesis by (simp add: flexb_AbsI)
  next
    case (App f u)
    from flexb_App[OF fl[unfolded App]] have ff: "flexb env0 f" "\<not> is_Abs f" by simp_all
    with h App obtain nf where hf: "ok (nt env f) nf"
      and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
        | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
      by (cases f) auto
    have fnf: "flexb env0 nf" by (rule IH[OF hf ff(1)])
    show ?thesis
    proof (cases "is_Abs nf")
      case True
      then obtain b U0 body where nfA: "nf = Abs b U0 body" by (cases nf) auto
      with rest have "ok (nt env (subst_bound u body)) t'" by simp
      from IH[OF this] flexb_subst[OF flexb_Abs[OF fnf[unfolded nfA]]] show ?thesis by (simp add: subst_bound_subst)
    next
      case False
      with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
      with flexb_AppI[OF fnf False] show ?thesis by simp
    qed
  qed (use fl flexb_rigid in auto)
qed

lemma norm_term_flex:
  assumes "ok (norm_term env t) t'" "iflex env0 env" "flexb env0 t"
  shows "flexb env0 t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    with assms show ?thesis by (simp add: norm_term_def)
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_flex[OF this refl refl assms(2,3)] show ?thesis .
  next
    case n2
    with assms(1) have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_flex[OF this refl assms(2,3)] show ?thesis .
  qed
qed

lemma norm_term1_head:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> head_of t = Var x T \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
    \<exists>T'. head_of t' = Var x T'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and hd = "1.prems"(3) and x = "1.prems"(4)
  have IH: "\<exists>T'. head_of u' = Var x T'" if "ok (nt te u) u'" "head_of u = Var x T" for u u'
    using "1.IH"[OF that(1) refl te that(2) x] .
  show ?case
  proof (cases t)
    case (Var y T1)
    with hd have y: "y = x" by simp
    with h Var obtain lr where lr: "ok (lookup1 te x T1) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    from ok_lookup1[OF lr] te x have "lr = None" by auto
    with rest hd show ?thesis by simp
  next
    case (App f u)
    from hd App have hf: "head_of f = Var x T" by simp
    then have nA: "\<not> is_Abs f" by (cases f) auto
    with h App obtain nf where nf: "ok (nt te f) nf"
      and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
      by (cases f) auto
    from IH[OF nf hf] obtain T' where hnf: "head_of nf = Var x T'" by blast
    then have "\<not> is_Abs nf" by (cases nf) auto
    with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
    with hnf show ?thesis by simp
  qed (use hd in simp_all)
qed

lemma norm_term2_head:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> head_of t = Var x T \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> \<exists>T'. head_of t' = Var x T'"
  using assms
proof (induction env t r arbitrary: t' T rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and hd = "1.prems"(2) and x = "1.prems"(3)
  have IH: "\<exists>T'. head_of u' = Var x T'" if "ok (nt env u) u'" "head_of u = Var x U" for u u' U
    using "1.IH"[OF that(1) refl that(2) x] .
  show ?case
  proof (cases t)
    case (Var y T1)
    with hd have y: "y = x" by simp
    with h Var obtain lr where lr: "ok (lookup env x T1) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T1; return (Var x T')}) t'"
      by auto
    have "lr = None"
    proof (cases lr)
      case (Some u)
      with lr x show ?thesis by (auto elim: ok_lookup_Some)
    qed
    with rest show ?thesis by auto
  next
    case (App f u)
    from hd App have hf: "head_of f = Var x T" by simp
    then have nA: "\<not> is_Abs f" by (cases f) auto
    with h App obtain nf where nf: "ok (nt env f) nf"
      and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
        | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
      by (cases f) auto
    from IH[OF nf hf] obtain T' where hnf: "head_of nf = Var x T'" by blast
    then have "\<not> is_Abs nf" by (cases nf) auto
    with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
    with hnf show ?thesis by simp
  qed (use hd in simp_all)
qed

lemma norm_term_head:
  assumes "ok (norm_term env t) t'" "head_of t = Var x T" "vt_lookup (tenv env) x = None"
  shows "\<exists>T'. head_of t' = Var x T'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    with assms show ?thesis by (simp add: norm_term_def)
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_head[OF this refl refl assms(2,3)] show ?thesis .
  next
    case n2
    with assms(1) have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_head[OF this refl assms(2,3)] show ?thesis .
  qed
qed

text \<open>A flexible term of a base type has a variable as its head:\<close>

lemma flexb_base:
  assumes "flexb env0 t" "e \<turnstile> inst \<rho> t : T" "arity T = 0"
  shows "\<exists>G V ss. t = Var G V \<degree>\<degree> ss \<and> vt_lookup (tenv env0) G = None"
proof -
  from assms(1) obtain bs G V ss where t: "t = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  have "bs = []"
  proof (cases bs)
    case (Cons b bs')
    obtain y U where "b = (y, U)" by force
    with assms(2,3) t Cons show ?thesis by auto
  qed
  with t G show ?thesis by auto
qed


subsection \<open>Computations that raise at most one exception\<close>

definition xok :: "uexn \<Rightarrow> 'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "xok E m P \<longleftrightarrow> (\<exists>evs. m = Some (evs, UErr E)) \<or> (\<exists>x. okW m x \<and> P x)"

lemma xok_returnW [simp]: "xok E (returnW x) P \<longleftrightarrow> P x"
  by (auto simp: xok_def returnW_def)

lemma xok_raiseW [simp]: "xok E (raiseW E) P"
  by (simp add: xok_def raiseW_def)

lemma xok_bindW:
  "xok E m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> xok E (f x) Q) \<Longrightarrow> xok E (bindW m f) Q"
  unfolding xok_def by (auto simp: bindW_def split: option.splits ures.splits)

lemma ff_liftM_return [simp]: "liftM (return x) = returnW x"
  by (simp add: liftM_def return_def returnW_def)

lemma flexargs_xok: "xok CHANGE_FAIL (flexargs js ts Ts) (\<lambda>_. True)"
  by (induction js ts Ts rule: flexargs.induct) (auto intro: xok_bindW)

lemma change_bnos_xok: "xok CHANGE_FAIL (change_bnos banned lev t) (\<lambda>_. True)"
  by (induction banned lev t rule: change_bnos.induct) (auto intro!: xok_bindW)

lemma foldrW_change_arg_xok: "xok CHANGE_FAIL (foldrW (change_arg del banned) fas acc) (\<lambda>_. True)"
proof (induction fas)
  case (Cons a fas)
  show ?case
  proof (simp, rule xok_bindW[OF Cons.IH])
    fix cas
    obtain j t T where a: "a = Flarg j t T" by (cases a)
    show "xok CHANGE_FAIL (change_arg del banned a cas) (\<lambda>_. True)"
      by (auto simp: change_arg_def a intro!: xok_bindW[OF change_bnos_xok])
  qed
qed simp

lemma ff_ttvars_change_bnos: "okW (change_bnos banned lev s) s' \<Longrightarrow> ttvars s' = ttvars s"
  by (induction banned lev s arbitrary: s' rule: change_bnos.induct) (auto split: if_splits)

subsection \<open>Operations on types\<close>

fun tbody :: "ptyp \<Rightarrow> ptyp" where
  "tbody (Type a [T, U]) = (if a = STR ''fun'' then tbody U else Type a [T, U])"
| "tbody T = T"

lemma tbody_funs: "tbody (Ts \<Rrightarrow> T) = tbody T"
  by (induction Ts) auto

lemma tbody_arity0: "arity T = 0 \<Longrightarrow> tbody T = T"
  by (induction T rule: tbody.induct) auto

lemma tbody_Type: "tbody (Type a Ts) = (if a = STR ''fun'' \<and> length Ts = 2 then tbody (last Ts) else Type a Ts)"
  by (cases "Type a Ts" rule: tbody.cases) auto

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

lemma body_type_tnorm:
  "tyenv env = \<theta> \<Longrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow>
    \<exists>B. body_type env T = return B \<and> tvars B \<subseteq> tvars_env \<theta> \<union> A \<and> tnorm \<theta> B = tbody (tnorm \<theta> T)"
proof -
  assume th: "tyenv env = \<theta>" and tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<exists>B. body_type env T = return B \<and> tvars B \<subseteq> tvars T \<union> tvars_env \<theta> \<and>
      tnorm \<theta> B = tbody (tnorm \<theta> T)"
  proof (induction rule: tnorm_induct[OF ti_ac[OF ti] ti_tc[OF ti], consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst body_type.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
      from Type(1)[of U] Ts obtain B where "body_type env U = return B" "tvars B \<subseteq> tvars U \<union> tvars_env \<theta>"
        "tnorm \<theta> B = tbody (tnorm \<theta> U)"
        by auto
      then show ?thesis using Ts a by (subst body_type.simps) auto
    next
      case False
      then have "\<not> (a = STR ''fun'' \<and> length Ts = 2)" by (auto simp: numeral_2_eq_2 length_Suc_conv)
      then have "tbody (Type a (map (tnorm \<theta>) Ts)) = Type a (map (tnorm \<theta>) Ts)" by (subst tbody_Type) auto
      with False show ?thesis by (subst body_type.simps) (auto split: list.splits)
    qed
  next
    case (Unbound v S)
    then show ?case by (subst body_type.simps) (simp add: type_lookup_ok th tnorm_TVar[OF ti_ac[OF ti]])
  next
    case (Bound v S U)
    then show ?case using tvars_envI2[OF Bound(1)]
      by (subst body_type.simps) (auto simp: type_lookup_ok th tnorm_TVar[OF ti_ac[OF ti]])
  qed
  then show ?thesis using tinv_tcons[OF ti tv] tv by blast
qed

lemma binder_types_tvars:
  "tyenv env = \<theta> \<Longrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow>
    \<exists>Ts. binder_types env T = return Ts \<and> (\<forall>T'\<in>set Ts. tvars T' \<subseteq> tvars_env \<theta> \<union> A)"
proof -
  assume th: "tyenv env = \<theta>" and tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<exists>Ts. binder_types env T = return Ts \<and> (\<forall>T'\<in>set Ts. tvars T' \<subseteq> tvars T \<union> tvars_env \<theta>)"
  proof (induction rule: tnorm_induct[OF ti_ac[OF ti] ti_tc[OF ti], consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst binder_types.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
      from Type(1)[of U] Ts obtain Us where "binder_types env U = return Us"
        "\<forall>T'\<in>set Us. tvars T' \<subseteq> tvars U \<union> tvars_env \<theta>"
        by auto
      then show ?thesis using Ts a by (subst binder_types.simps) auto
    next
      case False
      then show ?thesis by (subst binder_types.simps) (auto split: list.splits)
    qed
  next
    case (Unbound v S)
    then show ?case by (subst binder_types.simps) (simp add: type_lookup_ok th)
  next
    case (Bound v S U)
    then show ?case using tvars_envI2[OF Bound(1)] by (subst binder_types.simps) (fastforce simp: type_lookup_ok th)
  qed
  then show ?thesis using tinv_tcons[OF ti tv] tv by blast
qed

end

text \<open>The occurs check terminates, and a negative answer excludes cycles:\<close>

lemma ff_occurs_terms_term:
  assumes "acyc env" "tacyc (tyenv env)" "tcons_env (tyenv env)" "vok env (vars u \<union> evars env)"
  shows "\<exists>b. occurs_terms env v [u] = return b \<and> (\<not> b \<longrightarrow> (\<forall>y\<in>fst ` vars u. (v, y) \<notin> (dep env)\<^sup>*))"
proof -
  from occur_term[OF assms(1-3) order_refl assms(4), of v "[]"] obtain b s where
    r: "occur u env v [] = return (b, s)" "\<not> b \<longrightarrow> osafe env v [] u s" by blast
  have "occurs_terms env v [u] = return b" using r(1) by (simp add: occurs_terms_def)
  moreover have "(v, y) \<notin> (dep env)\<^sup>*" if "\<not> b" "y \<in> fst ` vars u" for y
    using r(2) that unfolding osafe_def good_def by force
  ultimately show ?thesis by blast
qed

subsection \<open>Assignments\<close>

lemma ff_unbound_extends: "extends env0 env \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> vt_lookup (tenv env0) x = None"
  unfolding extends_def by (metis not_None_eq option.distinct(1))

lemma ff_head_of_vars: "head_of t = Var v T \<Longrightarrow> (v, T) \<in> vars t"
  by (induction t) auto

lemma ff_typed_Var_apps:
  assumes "e \<turnstile> inst \<rho> (Var v T \<degree>\<degree> ts) : V"
  shows "\<exists>Us. tsubst \<rho> T = Us \<Rrightarrow> V \<and> length Us = length ts"
proof -
  from assms have "e \<turnstile> Var v (tsubst \<rho> T) \<degree>\<degree> map (inst \<rho>) ts : V" by (simp add: inst_apps)
  then obtain Us where tv: "e \<turnstile> Var v (tsubst \<rho> T) : Us \<Rrightarrow> V" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us"
    by (rule list_app_typeE)
  from tv have "tsubst \<rho> T = Us \<Rrightarrow> V" by auto
  moreover from typings_nth[OF tts] have "length Us = length ts" by simp
  ultimately show ?thesis by blast
qed

lemma abs_list_flex_Var:
  "abs_list bs (Var w W \<degree>\<degree> us) = Var n T' \<Longrightarrow> bs = [] \<and> us = [] \<and> n = w \<and> T' = W"
proof -
  assume e: "abs_list bs (Var w W \<degree>\<degree> us) = Var n T'"
  then have "bs = []" using flexb_bs_Nil[OF e] by simp
  with e show ?thesis by (simp add: ff_apps_Var_nonApp)
qed

text \<open>An update that keeps the invariants of the environment:\<close>

lemma update_inv:
  assumes ei: "einv A K env" and upd: "ok (update (F, T) s env) env'"
    and acy: "\<And>y U. (y, U) \<in> vars s \<Longrightarrow> (F, y) \<notin> (dep env)\<^sup>*" and cl: "closed s"
    and F: "snd F \<le> maxidx env" and tv: "tvars T \<union> ttvars s \<subseteq> tvars_env (tyenv env) \<union> A"
    and fl: "flexb env0 s" and fi: "iflex env0 env"
  shows "einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and> iflex env0 env'"
proof -
  note o = ok_update[OF upd]
  have "iflex env0 env'"
    unfolding iflex_def
  proof (intro allI impI)
    fix x U u assume x: "vt_lookup (tenv env') x = Some (U, u)" "vt_lookup (tenv env0) x = None"
    show "flexb env0 u"
    proof (cases "x = F")
      case True
      with x(1) o(2) fl show ?thesis by simp
    next
      case False
      with x(1) o(2) have "vt_lookup (tenv env) x = Some (U, u)" by simp
      from iflexD[OF fi this x(2)] show ?thesis .
    qed
  qed
  moreover have "einv A K env'"
  proof (rule einv_update[OF ei upd _ cl F tv])
    fix y U assume "(y, U) \<in> vars s"
    then show "(F, y) \<notin> (dep env)\<^sup>*" by (rule acy)
  qed
  ultimately show ?thesis using o(3) extends_update[OF upd] by blast
qed

text \<open>The invariants of a state of the treatment of flex-flex pairs, relative to the result
  \<open>env0\<close> of the simplification:\<close>

definition finv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "finv A K env0 env \<longleftrightarrow> einv A K env \<and> tyenv env = tyenv env0 \<and> extends env0 env \<and> iflex env0 env"

lemma finv_trans:
  "finv A K env0 env \<Longrightarrow> einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and> iflex env0 env' \<Longrightarrow>
    finv A K env0 env'"
  unfolding finv_def using extends_trans by metis

theorem ff_assign_term:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t u"
    and ar: "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t : T \<and> e \<turnstile> inst (rho0 env) u : T \<and> arity T = 0"
    and ht: "\<And>v T. head_of t = Var v T \<Longrightarrow> vt_lookup (tenv env) v = None"
    and hu: "\<exists>w W us. u = Var w W \<degree>\<degree> us \<and> vt_lookup (tenv env) w = None"
  shows "xok ASSIGN (ff_assign alg env rb t u) (finv A K env0)"
proof -
  have ei: "einv A K env" and fi: "iflex env0 env" and e0: "extends env0 env" using fv by (simp_all add: finv_def)
  note e = einvD[OF ei] and pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  let ?\<rho> = "rho0 env"
  have vk: "vok env (Y \<union> evars env)" by (rule vok_winv[OF ei wi pd(6)])
  have vi: "vinv ?\<rho> env Y" using winvD[OF wi r0] by blast
  have bl: "snd x \<le> maxidx env" if "(x, X) \<in> Y \<union> evars env" for x X
    using belowD[OF _ that] vi by (simp add: vinv_def)
  from ar obtain e T where bs: "bs_env ?\<rho> e rb" and tyt: "e \<turnstile> inst ?\<rho> t : T" and tyu: "e \<turnstile> inst ?\<rho> u : T"
    and a0: "arity T = 0" by blast
  from hu obtain w W us where u: "u = Var w W \<degree>\<degree> us" and w: "vt_lookup (tenv env) w = None" by blast
  show ?thesis
    unfolding ff_assign_def
  proof (rule xok_bindW)
    show "xok ASSIGN (get_eta_var rb 0 t) (\<lambda>_. True)"
      using get_eta_var_cases[of rb 0 t] by auto
  next
    fix vT assume gev: "okW (get_eta_var rb 0 t) vT"
    obtain v Tv where vT: "vT = (v, Tv)" by (cases vT)
    have hdt: "head_of t = Var v Tv" using get_eta_var_head gev vT by simp
    have v: "vt_lookup (tenv env) v = None" by (rule ht[OF hdt])
    have vt: "(v, Tv) \<in> vars t" by (rule ff_head_of_vars[OF hdt])
    have tvT: "tvars Tv \<subseteq> ?KN" using pd(3) vars_typs[OF vt] by (auto simp: ttvars_def)
    have vku: "vok env (vars u \<union> evars env)" using vk pd(2) by (auto intro: vok_mono)
    from ff_occurs_terms_term[OF e(3,6,7) vku, of v] obtain b where
      oc: "occurs_terms env v [u] = return b" "\<not> b \<longrightarrow> (\<forall>y\<in>fst ` vars u. (v, y) \<notin> (dep env)\<^sup>*)" by blast
    show "xok ASSIGN ((\<lambda>(v, T). do {
          b \<leftarrow> liftM (occurs_terms env v [u]);
          if b then raiseW ASSIGN
          else do {
            T1 \<leftarrow> liftM (body_type env T);
            T2 \<leftarrow> liftM (fastype env rb u);
            env' \<leftarrow> cunify_types alg T1 T2 env;
            liftM (vupdate (v, T) (rlist_abs rb u) env')}}) vT) (finv A K env0)"
    proof (cases b)
      case True
      then show ?thesis using oc(1) vT by simp
    next
      case False
      note acy = oc(2)[rule_format, OF False]
      from body_type_tnorm[OF e(2) refl tvT] obtain T1 where
        T1: "body_type env Tv = return T1" "tvars T1 \<subseteq> ?KN" "tnorm (tyenv env) T1 = tbody (tnorm (tyenv env) Tv)"
        by blast
      have ltu: "ttvars u \<union> btvars rb \<subseteq> ?KN" using pd(4,5) by blast
      from env_fastype_term[OF e(2) refl tyu bs pd(8) ltu] obtain T2 where
        T2: "env_fastype env (map snd rb) u = return T2" "tvars T2 \<subseteq> ?KN" "tnorm (tyenv env) T2 = T"
        by blast
      have "tnorm (tyenv env) T1 = T"
      proof -
        have "t = app (Var v Tv) (rev (map (\<lambda>j. 0 + integer_of_nat j) [0..<length rb]))"
          using get_eta_var_app gev vT by blast
        then have "t = Var v Tv \<degree>\<degree> map Bound (rev (map (\<lambda>j. 0 + integer_of_nat j) [0..<length rb]))"
          by (simp add: app_apps)
        from ff_typed_Var_apps[OF tyt[unfolded this]] obtain Us where "tsubst ?\<rho> Tv = Us \<Rrightarrow> T" by blast
        then have "tnorm (tyenv env) Tv = Us \<Rrightarrow> T" by simp
        with T1(3) show ?thesis by (simp add: tbody_funs tbody_arity0[OF a0])
      qed
      then have cu: "cunify_types alg T1 T2 env = returnW env"
        using cunify_types_same[OF e(6,7) ff_tcons[OF ei T1(2)] ff_tcons[OF ei T2(2)]] T2(3) by simp
      let ?s = "rlist_abs rb u"
      have sabs: "?s = abs_list (rev rb) (Var w W \<degree>\<degree> us)" by (simp add: u rlist_abs_abs_list)
      have fls: "flexb env0 ?s" unfolding flexb_def sabs using ff_unbound_extends[OF e0 w] by blast
      have cls: "closed ?s"
        unfolding rlist_abs_abs_list using pd(8) by (intro closed_abs_list) (simp add: ilength_eq)
      have tvs: "ttvars ?s \<subseteq> ?KN" using pd(4,5) by (simp add: rlist_abs_abs_list ttvars_abs_list btvars_def)
      have vu: "\<exists>env'. vupdate (v, Tv) ?s env = return env' \<and> finv A K env0 env'"
      proof -
        have gen: "\<exists>env'. update (F, FT) s env = return env' \<and> finv A K env0 env'"
          if F: "vt_lookup (tenv env) F = None" "(F, FT) \<in> Y \<union> evars env"
            and acs: "\<And>y U. (y, U) \<in> vars s \<Longrightarrow> (F, y) \<notin> (dep env)\<^sup>*" and cl: "closed s"
            and tv: "tvars FT \<union> ttvars s \<subseteq> ?KN" and fl: "flexb env0 s" for F FT s
        proof -
          from update_ok[OF F(1)] obtain env' where upd: "update (F, FT) s env = return env'" by blast
          have "finv A K env0 env'"
            by (rule finv_trans[OF fv update_inv[OF ei upd[unfolded return_def] acs cl bl[OF F(2)] tv fl fi]])
          with upd show ?thesis by blast
        qed
        have vY: "(v, Tv) \<in> Y \<union> evars env" using vt pd(1) by blast
        have main: "\<exists>env'. update (v, Tv) ?s env = return env' \<and> finv A K env0 env'"
        proof (rule gen[OF v vY _ cls _ fls])
          fix y U assume "(y, U) \<in> vars ?s"
          then have "y \<in> fst ` vars u" by (simp add: rev_image_eqI)
          then show "(v, y) \<notin> (dep env)\<^sup>*" by (rule acy)
        next
          show "tvars Tv \<union> ttvars ?s \<subseteq> ?KN" using tvT tvs by blast
        qed
        show ?thesis
        proof (cases "\<exists>n T'. ?s = Var n T'")
          case False
          then have "vupdate (v, Tv) ?s env = update (v, Tv) ?s env"
            by (subst vupdate.simps) (auto split: pterm.splits)
          with main show ?thesis by simp
        next
          case True
          then obtain n T' where sv: "?s = Var n T'" by blast
          from abs_list_flex_Var[OF sv[unfolded sabs]] have nw: "rb = []" "us = []" "n = w" "T' = W"
            by simp_all
          have uw: "u = Var w W" using u nw by simp
          have unf: "vupdate (v, Tv) ?s env = (if v = w then return env
              else if indexname_less v w then do {
                r \<leftarrow> lookup env w W;
                case r of None \<Rightarrow> update (w, W) (Var v W) env | Some u \<Rightarrow> vupdate (v, Tv) u env}
              else update (v, Tv) ?s env)"
            by (subst vupdate.simps) (simp add: uw nw)
          have wY: "(w, W) \<in> Y \<union> evars env" using pd(2) by (auto simp: u nw)
          have lk: "lookup env w W = return None"
            using lookup_ok[OF e(6,7) vok_mono[OF vk], of w W] wY w by auto
          show ?thesis
          proof (cases "v = w")
            case True
            with unf fv show ?thesis by (simp add: finv_def iflex_def)
          next
            case vw: False
            have ww: "\<exists>env'. update (w, W) (Var v W) env = return env' \<and> finv A K env0 env'"
            proof (rule gen[OF w wY])
              show "(w, y) \<notin> (dep env)\<^sup>*" if "(y, U) \<in> vars (Var v W)" for y U
              proof
                assume "(w, y) \<in> (dep env)\<^sup>*"
                moreover from that have "y = v" by simp
                ultimately have "(w, v) \<in> (dep env)\<^sup>+" using vw by (metis rtranclD)
                with dep_bound v show False by blast
              qed
              show "closed (Var v W)" by (simp add: closed_def)
              show "tvars W \<union> ttvars (Var v W) \<subseteq> ?KN" using pd(4) by (simp add: u nw)
              show "flexb env0 (Var v W)" using ff_unbound_extends[OF e0 v] by (simp add: flexb_Var)
            qed
            show ?thesis using unf vw lk ww main by auto
          qed
        qed
      qed
      then obtain env' where "vupdate (v, Tv) ?s env = return env'" "finv A K env0 env'" by blast
      then show ?thesis using oc(1) False vT T1(1) T2(1) cu by (simp add: fastype_def)
    qed
  qed
qed

subsection \<open>Cleaning terms\<close>

lemma ff_evars_known:
  "einv A K env \<Longrightarrow> (x, T) \<in> evars env \<Longrightarrow> tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  assume ei: "einv A K env" "(x, T) \<in> evars env"
  then obtain y U u where yb: "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
    by (auto simp: evars_def bnds_def)
  moreover have "tvars T \<subseteq> ttvars u" if "(x, T) \<in> vars u" using vars_typs[OF that] by (auto simp: ttvars_def)
  ultimately show ?thesis using tvinvD(2)[OF einvD(1)[OF ei(1)] yb(1)] by blast
qed

lemma ff_vok_vcons:
  assumes "\<forall>(x, T)\<in>Z \<union> evars env. tcons (tyenv env) T" "vcons (rho0 env) (Z \<union> evars env)"
  shows "vok env (Z \<union> evars env)"
  unfolding vok_def
proof (intro ballI, clarify, intro conjI allI impI)
  fix x T assume xT: "(x, T) \<in> Z \<union> evars env"
  then show "tcons (tyenv env) T" using assms(1) by blast
  fix U u assume "vt_lookup (tenv env) x = Some (U, u)"
  then have "(x, U) \<in> Z \<union> evars env" using evarsI by blast
  from vconsD[OF assms(2) xT this] show "tnorm (tyenv env) T = tnorm (tyenv env) U" by simp
qed

lemma ff_vinv_vars_evars: "vars t \<subseteq> Y \<union> evars env \<Longrightarrow> vinv \<rho> env Y \<Longrightarrow> vinv \<rho> env (Y \<union> vars t)"
proof -
  assume "vars t \<subseteq> Y \<union> evars env" "vinv \<rho> env Y"
  moreover have "Y \<union> vars t \<union> evars env = Y \<union> evars env" using calculation(1) by blast
  ultimately show ?thesis by (simp add: vinv_def)
qed

lemma ff_types_abs_Abs: "Ts \<noteq> [] \<Longrightarrow> is_Abs (types_abs Ts b)"
  by (cases Ts) auto

lemma ff_tvars_funs: "tvars (Ts \<Rrightarrow> T) = \<Union> (tvars ` set Ts) \<union> tvars T"
  by (induction Ts) auto

theorem clean_term_term:
  assumes fv: "finv A K env0 env" and wi: "winv env Y"
    and t: "t = Var v T0 \<degree>\<degree> ts" and v: "vt_lookup (tenv env) v = None"
    and vt: "vars t \<subseteq> Y \<union> evars env" and tt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and lb: "\<not> loose_bvar t (ilength rb)"
    and bs0: "bs_env (rho0 env) e rb" and ty0: "e \<turnstile> inst (rho0 env) t : T" and a0: "arity T = 0"
    and F: "bren_ok banned rb rb' F"
  shows "xok CHANGE_FAIL (clean_term banned env t) (\<lambda>(env', t'). finv A K env0 env' \<and>
      ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A \<and>
      (\<exists>x X ss. t' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env') x = None \<and> (x = v \<or> maxidx env < snd x)) \<and>
      (\<forall>y. vt_lookup (tenv env) y = None \<longrightarrow> vt_lookup (tenv env') y \<noteq> None \<longrightarrow> y = v))"
proof -
  have ei: "einv A K env" and fi: "iflex env0 env" and e0: "extends env0 env" and th0: "tyenv env = tyenv env0"
    using fv by (simp_all add: finv_def)
  note e = einvD[OF ei] and r00 = einv_rho0[OF ei]
  define \<rho> where "\<rho> = rho0 env"
  have r0: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" unfolding \<rho>_def by (rule r00(1), rule r00(2))
  note bs = bs0[folded \<rho>_def] and ty = ty0[folded \<rho>_def]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  let ?n = "length ts"
  let ?P = "\<lambda>(env', t'). finv A K env0 env' \<and> ttvars t' \<subseteq> ?KN \<and>
      (\<exists>x X ss. t' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env') x = None \<and> (x = v \<or> maxidx env < snd x)) \<and>
      (\<forall>y. vt_lookup (tenv env) y = None \<longrightarrow> vt_lookup (tenv env') y \<noteq> None \<longrightarrow> y = v)"
  have wv: "wt_env \<rho> env" "vinv \<rho> env Y" using winvD[OF wi r0] by blast+
  have sc: "strip_comb t = (Var v T0, ts)" by (simp add: t strip_comb_atom_apps)
  have vT0: "(v, T0) \<in> vars t" by (simp add: t vars_apps)
  have tvT0: "tvars T0 \<subseteq> ?KN" using tt by (simp add: t ttvars_apps)
  have vbl: "snd v \<le> maxidx env" using belowD[of "maxidx env" "Y \<union> evars env" v T0] wv(2) vt vT0
    by (auto simp: vinv_def)
  from binder_types_tvars[OF e(2) refl tvT0] obtain Ts where
    Ts: "binder_types env T0 = return Ts" "\<forall>T'\<in>set Ts. tvars T' \<subseteq> ?KN" by blast
  from body_type_tnorm[OF e(2) refl tvT0] obtain U where U: "body_type env T0 = return U" "tvars U \<subseteq> ?KN"
    by blast
  have st: "strip_type env T0 = return (Ts, U)" by (simp add: strip_type_def Ts(1) U(1))
  have ct: "clean_term banned env t = bindW (flexargs (downto0_list ?n) ts Ts) (\<lambda>fas.
      bindW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) (\<lambda>cas.
        let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T0) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')})))"
    by (simp add: clean_term_def sc st Let_def)
  have lbts: "\<forall>s\<in>set ts. \<not> loose_bvar s (ilength rb)" using lb by (simp add: t loose_bvar_apps)
  have tyd: "cert_typ alg ar (tsubst \<rho> T0) \<and> tsubst \<rho> T0 = map (tsubst \<rho>) Ts \<Rrightarrow> T \<and> tsubst \<rho> U = T \<and>
      (\<forall>k<?n. e \<turnstile> inst \<rho> (ts ! k) : tsubst \<rho> (Ts ! k))" if lTs: "length Ts = ?n"
  proof -
    from ty have "e \<turnstile> Var v (tsubst \<rho> T0) \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: t inst_apps)
    then obtain Us where tv: "e \<turnstile> Var v (tsubst \<rho> T0) : Us \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us"
      by (rule list_app_typeE)
    from tv have c: "cert_typ alg ar (tsubst \<rho> T0)" and eq: "tsubst \<rho> T0 = Us \<Rrightarrow> T" by auto
    from typings_nth[OF tts] have lu: "length Us = ?n" and nth: "\<forall>i<?n. e \<turnstile> inst \<rho> (ts ! i) : Us ! i"
      by simp_all
    from strip_type_sound[OF st[unfolded return_def] r0(1)] eq
    have "map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> U = Us \<Rrightarrow> T" by simp
    with funs_eq[of "map (tsubst \<rho>) Ts" Us] lu lTs have UT: "map (tsubst \<rho>) Ts = Us" "tsubst \<rho> U = T"
      by simp_all
    with c eq nth lTs show ?thesis by auto
  qed
  show ?thesis
    unfolding ct
  proof (rule xok_bindW[OF flexargs_xok])
    fix fas assume fa: "okW (flexargs (downto0_list ?n) ts Ts) fas"
    show "xok CHANGE_FAIL (bindW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) (\<lambda>cas.
        let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T0) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')}))) ?P"
    proof (rule xok_bindW[OF foldrW_change_arg_xok])
      fix cas assume ca: "okW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) cas"
      define args where "args = sort_args cas"
      define ts' where "ts' = map fl_t args"
      have lTs: "length Ts = ?n" using flexargs_ok[OF fa] by simp
      note CA = clean_args[OF fa ca F lbts, folded args_def]
      have a1: "ttvars (fl_t a) \<subseteq> ?KN \<and> vars (fl_t a) \<subseteq> vars t \<and> fl_T a \<in> set Ts" if a: "a \<in> set args" for a
      proof -
        from CA[OF a, where \<rho> = \<rho>] obtain k where k: "k < ?n" "fl_T a = Ts ! k" "vars (fl_t a) = vars (ts ! k)"
          by blast
        from a foldrW_change_arg[OF ca] obtain a0 where a0: "a0 \<in> set fas" "okW (change_bnos banned 0 (fl_t a0)) (fl_t a)"
          by (auto simp: args_def set_sort_args)
        from flexargs_ok[OF fa] a0(1) obtain k' where k': "k' < ?n" "fl_t a0 = ts ! k'" by force
        have "ttvars (fl_t a) = ttvars (ts ! k')" using ff_ttvars_change_bnos[OF a0(2)] k'(2) by simp
        then have "ttvars (fl_t a) \<subseteq> ttvars t" using k'(1) by (auto simp: t ttvars_apps)
        moreover have "vars (fl_t a) \<subseteq> vars t" using k(1,3) by (auto simp: t vars_apps)
        moreover have "fl_T a \<in> set Ts" using k(1,2) lTs by simp
        ultimately show ?thesis using tt by blast
      qed
      have tts': "ttvars (list_comb h ts') \<subseteq> ttvars h \<union> ?KN" for h
        using a1 by (auto simp: ts'_def list_comb_apps ttvars_apps)
      have rest: "xok CHANGE_FAIL (if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
          else (case genvar (fst v) env (foldr fun_type (map fl_T args) U) of (env', v') \<Rightarrow> do {
            env2 \<leftarrow> liftM (vupdate (v, T0) (types_abs Ts (list_comb v' (map (Bound \<circ> fl_j) args))) env');
            t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
            returnW (env2, t')})) ?P"
      proof (cases "decreasing (ilength Ts) args")
        case True
        have p1: "\<exists>x X ss. list_comb (Var v T0) ts' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None \<and>
            (x = v \<or> maxidx env < snd x)"
          using v by (intro exI[of _ v] exI[of _ T0] exI[of _ ts']) (simp add: list_comb_apps)
        have "?P (env, list_comb (Var v T0) ts')"
          unfolding prod.case using fv tts'[of "Var v T0"] tvT0 p1 by auto
        with True show ?thesis by simp
      next
        case False
        have Ts0: "Ts \<noteq> []"
        proof
          assume "Ts = []"
          with lTs have ts0: "ts = []" by simp
          have "fas = []" using flexargs_ok[OF fa] ts0 by (cases fas) auto
          with ca have "cas = []" by simp
          with False \<open>Ts = []\<close> show False by (simp add: args_def)
        qed
        define Gty where "Gty = foldr fun_type (map fl_T args) U"
        obtain env1 v' where g: "genvar (fst v) env Gty = (env1, v')" by (cases "genvar (fst v) env Gty")
        define ks where "ks = map fl_j args"
        define body where "body = v' \<degree>\<degree> map Bound ks"
        note gs = genvar_simps[OF g]
        let ?G = "(fst v, maxidx env + 1)"
        have G: "vt_lookup (tenv env) ?G = None"
        proof (rule ccontr)
          assume "vt_lookup (tenv env) ?G \<noteq> None"
          then obtain b where "vt_lookup (tenv env) ?G = Some b" by blast
          from bbelowD[OF e(5) this] show False by simp
        qed
        have Gv: "?G \<noteq> v"
        proof
          assume "?G = v"
          then have "snd v = maxidx env + 1" by (metis snd_conv)
          with vbl show False by simp
        qed
        have ei1: "einv A K env1" by (rule einv_genvar[OF g ei])
        have fv1: "finv A K env0 env1"
          using ei1 gs fi e0 th0 extends_trans[OF e0 extends_genvar[OF g]] by (simp add: finv_def iflex_def)
        have v1: "vt_lookup (tenv env1) v = None" using v gs by simp
        from update_ok[OF v1] obtain env2 where upd: "update (v, T0) (types_abs Ts body) env1 = return env2"
          by blast
        have vu: "vupdate (v, T0) (types_abs Ts body) env1 = return env2"
          using upd ff_types_abs_Abs[OF Ts0, of body] by (subst vupdate.simps) (auto split: pterm.splits)
        text \<open>The facts on the kept arguments, as in @{thm [source] clean_term_sound}:\<close>
        let ?Us = "map (tsubst \<rho>) Ts"
        note td = tyd[OF lTs]
        have ak: "0 \<le> fl_j a \<and> fl_j a < ilength ts \<and> rev ?Us ! nat_of_integer (fl_j a) = tsubst \<rho> (fl_T a) \<and>
            renv e F 0 \<turnstile> inst \<rho> (fl_t a) : tsubst \<rho> (fl_T a) \<and> \<not> loose_bvar (fl_t a) (ilength rb')"
          if a: "a \<in> set args" for a
        proof -
          from CA[OF a, where \<rho> = \<rho>] obtain k where k: "k < ?n" "fl_j a = integer_of_nat (?n - 1 - k)"
            "fl_T a = Ts ! k" and r: "\<not> loose_bvar (fl_t a) (ilength rb')"
            "\<forall>e T. e \<turnstile> inst \<rho> (ts ! k) : T \<longrightarrow> renv e F 0 \<turnstile> inst \<rho> (fl_t a) : T"
            by blast
          have j: "nat_of_integer (fl_j a) = ?n - 1 - k" using k(2) by (simp add: integer_reps)
          have "0 \<le> fl_j a" "fl_j a < ilength ts" using k(1,2) by (simp_all add: ilength_eq integer_reps)
          moreover have "rev ?Us ! nat_of_integer (fl_j a) = tsubst \<rho> (fl_T a)"
          proof -
            have "rev ?Us ! nat_of_integer (fl_j a) = ?Us ! k" unfolding j using k(1) lTs by (simp add: rev_nth)
            then show ?thesis using k(1,3) lTs by simp
          qed
          moreover have "renv e F 0 \<turnstile> inst \<rho> (fl_t a) : tsubst \<rho> (fl_T a)"
          proof -
            have "e \<turnstile> inst \<rho> (ts ! k) : tsubst \<rho> (Ts ! k)" using td k(1) by blast
            then show ?thesis using r(2) k(3) by simp
          qed
          ultimately show ?thesis using r(1) by blast
        qed
        have tyG: "tsubst \<rho> Gty = map (\<lambda>a. tsubst \<rho> (fl_T a)) args \<Rrightarrow> tsubst \<rho> U"
          by (simp add: Gty_def tsubst_funs comp_def)
        have c0: "cert_typ alg ar (?Us \<Rrightarrow> T)" using td by metis
        then have "(\<forall>V\<in>set ?Us. cert_typ alg ar V) \<and> cert_typ alg ar T"
          using cert_typ_funs[where Ts = ?Us and T = T] by blast
        then have cUs: "\<forall>V\<in>set ?Us. cert_typ alg ar V" and cT: "cert_typ alg ar T" by blast+
        have cA: "\<forall>a\<in>set args. cert_typ alg ar (tsubst \<rho> (fl_T a))"
          using a1 cUs by auto
        have cG: "cert_typ alg ar (tsubst \<rho> Gty)"
          using cA cT td by (simp add: tyG cert_typ_funs)
        let ?bs = "map (\<lambda>T. (STR '''', tsubst \<rho> T)) Ts"
        have iB: "inst \<rho> (types_abs Ts body) = abs_list ?bs (Var ?G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks)"
          by (simp add: types_abs_abs_list inst_abs_list body_def gs(4) inst_apps comp_def)
        have tB: "e' \<turnstile> inst \<rho> (types_abs Ts body) : tsubst \<rho> T0" for e'
        proof -
          have "pushes e' ?Us \<tturnstile> map Bound ks : map (\<lambda>a. tsubst \<rho> (fl_T a)) args"
            unfolding ks_def map_map comp_def
          proof (rule typings_map)
            fix a assume "a \<in> set args"
            note k = ak[OF this]
            then have "pushes e' ?Us (fl_j a) = tsubst \<rho> (fl_T a)"
              using pushes_nth[of "fl_j a" e' ?Us] lTs by (simp add: ilength_eq)
            with k show "pushes e' ?Us \<turnstile> Bound (fl_j a) : tsubst \<rho> (fl_T a)" by auto
          qed
          with cG tyG have "pushes e' (map snd ?bs) \<turnstile> Var ?G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks : tsubst \<rho> U"
            by (auto intro!: list_app_typeI simp: comp_def)
          from typing_abs_list[OF this] cUs have "e' \<turnstile> abs_list ?bs (Var ?G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks) :
              map snd ?bs \<Rrightarrow> tsubst \<rho> U"
            by auto
          then show ?thesis using td by (simp add: iB comp_def)
        qed
        have clB: "closed (types_abs Ts body)"
        proof -
          have "\<not> loose_bvar (v' \<degree>\<degree> map Bound ks) (ilength (map (\<lambda>T. (STR '''', T)) Ts))"
            using ak lTs by (auto simp: gs(4) ks_def loose_bvar_apps ilength_eq not_le)
          then show ?thesis unfolding types_abs_abs_list body_def by (rule closed_abs_list)
        qed
        have vB: "vars (types_abs Ts body) = vars v'"
          by (simp add: types_abs_abs_list body_def vars_apps)
        have tvG: "tvars Gty \<subseteq> ?KN" using a1 Ts(2) U(2) by (auto simp: Gty_def ff_tvars_funs)
        have tvB: "ttvars (types_abs Ts body) \<subseteq> ?KN"
          using Ts(2) tvG by (auto simp: types_abs_abs_list ttvars_abs_list btvars_def body_def gs(4) ttvars_apps)
        have flB: "flexb env0 (types_abs Ts body)"
          unfolding flexb_def types_abs_abs_list body_def gs(4) using ff_unbound_extends[OF e0 G] by blast
        have fv2: "finv A K env0 env2"
        proof (rule finv_trans[OF fv1 update_inv[OF ei1 upd[unfolded return_def] _ clB _ _ flB]])
          fix y W assume "(y, W) \<in> vars (types_abs Ts body)"
          then have y: "y = ?G" by (simp add: vB[simplified] gs(4))
          show "(v, y) \<notin> (dep env1)\<^sup>*"
          proof
            assume "(v, y) \<in> (dep env1)\<^sup>*"
            with y Gv have "(v, ?G) \<in> (dep env1)\<^sup>+" by (metis rtranclD)
            from dep_bound[OF this] G gs(1) show False by simp
          qed
        next
          show "snd v \<le> maxidx env1" using vbl gs(3) by simp
          show "tvars T0 \<union> ttvars (types_abs Ts body) \<subseteq> tvars_env (tyenv env1) \<union> A"
            using tvT0 tvB gs(2) by simp
          show "iflex env0 env1" using fv1 by (simp add: finv_def)
        qed
        have ei2: "einv A K env2" and th2: "tyenv env2 = tyenv env" using fv2 th0 by (simp_all add: finv_def)
        have \<rho>2: "rho0 env2 = \<rho>" using th2 by (simp add: \<rho>_def)
        note o2 = ok_update[OF upd[unfolded return_def]]
        text \<open>The typing in the most general solution, before the normalization:\<close>
        have wte1: "wt_env \<rho> env1" using wv(1) by (simp add: wt_env_genvar[OF g])
        have vi1: "vinv \<rho> env1 (vars v' \<union> (Y \<union> vars t))" by (rule vinv_genvar[OF g ff_vinv_vars_evars[OF vt wv(2)]])
        have wte2: "wt_env \<rho> env2" by (rule wt_env_update[OF upd[unfolded return_def] wte1 clB tB])
        have vi2: "vinv \<rho> env2 (Y \<union> vars t \<union> vars v')"
        proof (rule vinv_update[OF upd[unfolded return_def]])
          show "vinv \<rho> env1 ((Y \<union> vars t \<union> vars v') \<union> insert (v, T0) (vars (types_abs Ts body)))"
            by (rule vinv_mono[OF vi1]) (use vT0 in \<open>auto simp: vB[simplified]\<close>)
        qed
        let ?s = "v' \<degree>\<degree> ts'"
        have vs: "vars ?s \<subseteq> vars t \<union> vars v'" using a1 by (auto simp: ts'_def vars_apps)
        have tts2: "renv e F 0 \<tturnstile> map (inst \<rho>) ts' : map (\<lambda>a. tsubst \<rho> (fl_T a)) args"
          unfolding ts'_def map_map comp_def by (rule typings_map) (use ak in blast)
        have t2: "renv e F 0 \<turnstile> inst \<rho> ?s : T"
          using tts2 cG tyG td by (auto simp: gs(4) inst_apps intro!: list_app_typeI)
        have vc2: "vcons (rho0 env2) (vars ?s \<union> evars env2)"
        proof -
          have "vcons \<rho> (Y \<union> vars t \<union> vars v' \<union> evars env2)" using vi2 by (simp add: vinv_def)
          then have "vcons \<rho> (vars ?s \<union> evars env2)" by (rule vcons_mono) (use vs in blast)
          then show ?thesis by (simp add: \<rho>2)
        qed
        have tvs: "ttvars ?s \<subseteq> tvars_env (tyenv env2) \<union> A"
          using tts'[of v'] th2 tvG by (auto simp: gs(4) list_comb_apps)
        have vk2: "vok env2 (vars ?s \<union> evars env2)"
        proof (rule ff_vok_vcons[OF _ vc2])
          show "\<forall>(x, X)\<in>vars ?s \<union> evars env2. tcons (tyenv env2) X"
          proof (clarify)
            fix x X assume xX: "(x, X) \<in> vars ?s \<union> evars env2"
            have "tvars X \<subseteq> tvars_env (tyenv env2) \<union> A"
            proof (cases "(x, X) \<in> vars ?s")
              case True
              then have "X \<in> typs ?s" by (rule vars_typs)
              then have "tvars X \<subseteq> ttvars ?s" unfolding ttvars_def by blast
              with tvs show ?thesis by blast
            next
              case False
              with xX show ?thesis by (intro ff_evars_known[OF ei2]) blast
            qed
            then show "tcons (tyenv env2) X" by (rule ff_tcons[OF ei2])
          qed
        qed
        have t2': "renv e F 0 \<turnstile> inst (rho0 env2) ?s : T" using t2 by (simp add: \<rho>2)
        from norm_term_term[OF ei2 vk2 tvs _ vc2 t2'] wte2 \<rho>2
        obtain t' where nt: "norm_term env2 ?s = return t'" "npost A env2 t'" by auto
        have tsol2: "tsol (tyenv env2) \<rho>" using r0(1) th2 by simp
        have ty': "renv e F 0 \<turnstile> inst \<rho> t' : T"
          by (rule nsoundD(3)[OF norm_term_sound[OF nt(1)[unfolded return_def] tsol2 wte2] t2])
        have fls: "flexb env0 ?s"
        proof -
          have "?s = abs_list [] (Var ?G Gty \<degree>\<degree> ts')" by (simp add: gs(4))
          then show ?thesis unfolding flexb_def using ff_unbound_extends[OF e0 G] by blast
        qed
        have fl': "flexb env0 t'" by (rule norm_term_flex[OF nt(1)[unfolded return_def] _ fls]) (use fv2 in \<open>simp add: finv_def\<close>)
        from flexb_base[OF fl' ty' a0] obtain x X ss where t': "t' = Var x X \<degree>\<degree> ss" by blast
        have G2: "vt_lookup (tenv env2) ?G = None" using G gs(1) o2(2) Gv by simp
        from norm_term_head[OF nt(1)[unfolded return_def] _ G2, of Gty] obtain X' where
          "head_of t' = Var ?G X'" by (auto simp: gs(4) head_of_apps)
        with t' have xG: "x = ?G" by (simp add: head_of_apps)
        have p1: "\<exists>x X ss. t' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env2) x = None \<and> (x = v \<or> maxidx env < snd x)"
          using t' xG G2 by (intro exI[of _ x] exI[of _ X] exI[of _ ss]) simp
        have "?P (env2, t')"
          unfolding prod.case using fv2 nt(2) th2 p1 o2(2) gs(1) by (auto simp: npost_def)
        moreover have "types_abs Ts (v' \<degree>\<degree> map (Bound \<circ> fl_j) args) = types_abs Ts body"
          by (simp add: body_def ks_def)
        ultimately show ?thesis using False g vu nt(1)
          by (simp add: list_comb_apps Gty_def[symmetric])
      qed
      then show "xok CHANGE_FAIL (let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T0) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')})) ?P"
        using rest unfolding Let_def args_def[symmetric] ts'_def[symmetric] by simp
    qed
  qed
qed

subsection \<open>Cleaning pairs\<close>

lemma ff_okW_xok: "okW m x \<Longrightarrow> Q x \<Longrightarrow> xok E m Q"
  by (auto simp: xok_def)

lemma xok_handleW:
  assumes "xok E m Q" "\<exists>x. okW (h E) x \<and> Q x"
  shows "\<exists>x. okW (handleW m h) x \<and> Q x"
  using assms unfolding xok_def okW_handleW by blast

lemma ff_add_tpair_set:
  "(t', u') \<in> set (add_tpair rb t u tps) \<Longrightarrow> (t', u') \<in> set tps \<or> (t' = rlist_abs rb t \<and> u' = rlist_abs rb u)"
  by (auto simp: add_tpair_def Let_def split: if_splits)

lemma ff_ttvars_rlist_abs: "ttvars (rlist_abs rb t) = btvars rb \<union> ttvars t"
  by (simp add: rlist_abs_abs_list ttvars_abs_list btvars_def)

lemma add_tpair_known:
  assumes "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> B" "btvars rb \<union> ttvars t \<union> ttvars u \<subseteq> B"
  shows "\<forall>(t', u')\<in>set (add_tpair rb t u tps). ttvars t' \<union> ttvars u' \<subseteq> B"
proof -
  have "ttvars t' \<union> ttvars u' \<subseteq> B" if "(t', u') \<in> set (add_tpair rb t u tps)" for t' u'
    using ff_add_tpair_set[OF that] assms by (auto simp: ff_ttvars_rlist_abs)
  then show ?thesis by blast
qed

lemma flexb_VarI: "vt_lookup (tenv env0) x = None \<Longrightarrow> flexb env0 (Var x X \<degree>\<degree> ss)"
proof -
  assume "vt_lookup (tenv env0) x = None"
  moreover have "Var x X \<degree>\<degree> ss = abs_list [] (Var x X \<degree>\<degree> ss)" by simp
  ultimately show ?thesis unfolding flexb_def by blast
qed

lemma ff_abs_list_append: "abs_list (xs @ ys) t = abs_list xs (abs_list ys t)"
  by (simp add: abs_list_def)

lemma flexb_rlist_abs: "flexb env0 t \<Longrightarrow> flexb env0 (rlist_abs rb t)"
proof -
  assume "flexb env0 t"
  then obtain bs G V ss where t: "t = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  have "rlist_abs rb t = abs_list (rev rb @ bs) (Var G V \<degree>\<degree> ss)"
    by (simp add: t rlist_abs_abs_list ff_abs_list_append)
  with G show ?thesis unfolding flexb_def by blast
qed

lemma add_tpair_flex:
  assumes "\<forall>(t', u')\<in>set tps. flexb E t' \<and> flexb E u'" "flexb E t" "flexb E u"
  shows "\<forall>(t', u')\<in>set (add_tpair rb t u tps). flexb E t' \<and> flexb E u'"
proof -
  have "flexb E t' \<and> flexb E u'" if "(t', u') \<in> set (add_tpair rb t u tps)" for t' u'
    using ff_add_tpair_set[OF that] assms flexb_rlist_abs by auto
  then show ?thesis by blast
qed

lemma ff_csoundD:
  assumes "csound env rb F rb' t env' t'" "tsol (tyenv env'') \<rho>" "extends env' env''" "wt_env \<rho> env"
    "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "\<not> loose_bvar t (ilength rb)" "vinv \<rho> env (X \<union> vars t)"
  shows "wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> vars t') \<and> renv e F 0 \<turnstile> inst \<rho> t' : T \<and>
    \<not> loose_bvar t' (ilength rb')"
  using assms unfolding csound_def by blast

lemma bren_ok_btvars: "bren_ok banned rb rb' F \<Longrightarrow> btvars rb' \<subseteq> btvars rb"
proof -
  assume F: "bren_ok banned rb rb' F"
  have "p \<in> set rb" if "p \<in> set rb'" for p
  proof -
    from that obtain q where q: "q < length rb'" "p = rb' ! q" by (auto simp: in_set_conv_nth)
    let ?i = "integer_of_nat q"
    have i: "0 \<le> ?i" "?i < ilength rb'" using q(1) by (simp_all add: ilength_eq integer_of_nat_eq_of_nat)
    with F have Fi: "0 \<le> F ?i" "F ?i < ilength rb" "rb' ! nat_of_integer ?i = rb ! nat_of_integer (F ?i)"
      unfolding bren_ok_def by blast+
    have "rb ! nat_of_integer (F ?i) \<in> set rb" using Fi(1,2) by (simp add: nat_of_integer_less_ilength)
    with Fi(3) q show ?thesis by simp
  qed
  then show ?thesis unfolding btvars_def by blast
qed

lemma var_apps_type_eq:
  assumes "e \<turnstile> inst \<rho> (Var x X \<degree>\<degree> ss) : T" "e' \<turnstile> inst \<rho> (Var x X \<degree>\<degree> ss) : T'"
  shows "T = T'"
proof -
  from ff_typed_Var_apps[OF assms(1)] obtain Us where u: "tsubst \<rho> X = Us \<Rrightarrow> T" "length Us = length ss" by blast
  from ff_typed_Var_apps[OF assms(2)] obtain Us' where u': "tsubst \<rho> X = Us' \<Rrightarrow> T'" "length Us' = length ss" by blast
  from u u' funs_eq[of Us Us' T T'] show ?thesis by simp
qed

text \<open>The invariants of the result of a sound step on a pair:\<close>

lemma dstep_pok:
  assumes ds: "dstep env [(rb, t, u)] env' [(rb', t', u')]" and wi: "winv env Y" and p: "upok A env rb Y t u"
    and ei': "einv A K env'" and th: "tyenv env' = tyenv env"
    and tv: "ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "winv env' (Y \<union> vars t' \<union> vars u') \<and> upok A env' rb' (Y \<union> vars t' \<union> vars u') t' u'"
proof -
  note pd = upokD[OF p]
  have main: "wt_env \<rho> env' \<and> dtyped \<rho> [(rb', t', u')] \<and> vinv \<rho> env' (Y \<union> dvars [(rb', t', u')])"
    if \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    have tsol: "tsol (tyenv env) \<rho>" using \<rho>(1) th by simp
    from winvD[OF wi tsol \<rho>(2)] have w: "wt_env \<rho> env" "vinv \<rho> env Y" by blast+
    have d: "dtyped \<rho> [(rb, t, u)]" using pd(7,8) pd(9)[OF tsol \<rho>(2)] by (auto simp: dtyped_def)
    have v: "vinv \<rho> env (Y \<union> dvars [(rb, t, u)])"
      using w(2) vinv_evars[of t u Y env \<rho>] pd(1,2) by (simp add: Un_assoc)
    from dstepD(2)[OF ds \<rho>(1) extends_refl w(1) d v] show ?thesis by blast
  qed
  have "winv env' (Y \<union> vars t' \<union> vars u')"
    unfolding winv_def using main by (simp add: Un_assoc)
  moreover have "upok A env' rb' (Y \<union> vars t' \<union> vars u') t' u'"
    unfolding upok_def
  proof (intro conjI allI impI)
    show "vars t' \<union> vars u' \<subseteq> Y \<union> vars t' \<union> vars u' \<union> evars env'" by blast
    have "vtvars (Y \<union> vars t' \<union> vars u') \<subseteq> tvars_env (tyenv env) \<union> A"
      using pd(6) vtvars_vars[of t'] vtvars_vars[of u'] tv by (auto simp: vtvars_Un)
    then show "ttvars t' \<union> ttvars u' \<union> btvars rb' \<union> vtvars (Y \<union> vars t' \<union> vars u') \<subseteq> tvars_env (tyenv env') \<union> A"
      using tv th by simp
    have "dtyped (rho0 env') [(rb', t', u')]" using main[OF einv_rho0[OF ei']] by blast
    then show "\<not> loose_bvar t' (ilength rb')" "\<not> loose_bvar u' (ilength rb')" by (simp_all add: dtyped_def)
    fix \<rho> assume "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
    from main[OF this] show "\<exists>e T. bs_env \<rho> e rb' \<and> e \<turnstile> inst \<rho> t' : T \<and> e \<turnstile> inst \<rho> u' : T"
      by (simp add: dtyped_def)
  qed
  ultimately show ?thesis by blast
qed

lemma ff_pok_Y_mono: "upok A env rb Y t u \<Longrightarrow> vtvars Y' \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> Y \<subseteq> Y' \<Longrightarrow> upok A env rb Y' t u"
  unfolding upok_def by blast

theorem clean_ffpair_term:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t u"
    and ar: "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t : T \<and> e \<turnstile> inst (rho0 env) u : T \<and> arity T = 0"
    and t: "t = Var v T0 \<degree>\<degree> ts" and u: "u = Var w U0 \<degree>\<degree> us" and vw: "v \<noteq> w"
    and v: "vt_lookup (tenv env) v = None" and w: "vt_lookup (tenv env) w = None"
    and tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
    and tf: "\<forall>(t', u')\<in>set tps. flexb env0 t' \<and> flexb env0 u'"
  shows "\<exists>env' tps'. okW (clean_ffpair alg rb t u env tps) (env', tps') \<and> finv A K env0 env' \<and>
    (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t', u')\<in>set tps'. flexb env0 t' \<and> flexb env0 u')"
proof -
  have ei: "einv A K env" and th0: "tyenv env = tyenv env0" and e0: "extends env0 env"
    using fv by (simp_all add: finv_def)
  note pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  let ?Q = "\<lambda>(env', tps'). finv A K env0 env' \<and> (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> ?KN) \<and>
    (\<forall>(t', u')\<in>set tps'. flexb env0 t' \<and> flexb env0 u')"
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  from clean_binder[OF fb] obtain F where F: "bren_ok banned rb rb' F" by blast
  have brb: "btvars rb' \<subseteq> ?KN" using bren_ok_btvars[OF F] pd(5) by blast
  from ar obtain e T where bs: "bs_env (rho0 env) e rb" and tyt: "e \<turnstile> inst (rho0 env) t : T"
    and tyu: "e \<turnstile> inst (rho0 env) u : T" and a0: "arity T = 0" by blast
  define FF where "FF = (\<lambda>env2 t1 u1. handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t1 u1; returnW (env3, tps)})
      (\<lambda>e. case e of
        ASSIGN \<Rightarrow>
          handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)})
            (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW e)
      | _ \<Rightarrow> raiseW e))"
  have cf: "clean_ffpair alg rb t u env tps = handleW
      (bindW (clean_term banned env t) (\<lambda>(env1, t1). bindW (clean_term banned env1 u) (\<lambda>(env2, u1). FF env2 t1 u1)))
      (\<lambda>e. case e of CHANGE_FAIL \<Rightarrow> returnW (env, add_tpair rb t u tps) | _ \<Rightarrow> raiseW e)"
    by (simp add: clean_ffpair_def fb Let_def FF_def)
  have qfail: "?Q (env, add_tpair rb t u tps)"
    using fv add_tpair_known[OF tk, of rb t u] pd(3,4,5)
      add_tpair_flex[OF tf flexb_VarI[OF ff_unbound_extends[OF e0 v]] flexb_VarI[OF ff_unbound_extends[OF e0 w]], of rb]
    by (auto simp: t u)
  have inner: "xok CHANGE_FAIL
      (bindW (clean_term banned env t) (\<lambda>(env1, t1). bindW (clean_term banned env1 u) (\<lambda>(env2, u1). FF env2 t1 u1))) ?Q"
  proof (rule xok_bindW[OF clean_term_term[OF fv wi t v pd(1) pd(3) pd(7) bs tyt a0 F]])
    fix r1 assume ct1: "okW (clean_term banned env t) r1"
      and P1: "(\<lambda>(env', t'). finv A K env0 env' \<and> ttvars t' \<subseteq> ?KN \<and>
        (\<exists>x X ss. t' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env') x = None \<and> (x = v \<or> maxidx env < snd x)) \<and>
        (\<forall>y. vt_lookup (tenv env) y = None \<longrightarrow> vt_lookup (tenv env') y \<noteq> None \<longrightarrow> y = v)) r1"
    obtain env1 t1 where r1: "r1 = (env1, t1)" by (cases r1)
    from P1 r1 have fv1: "finv A K env0 env1" and tt1: "ttvars t1 \<subseteq> ?KN"
      and new1: "\<forall>y. vt_lookup (tenv env) y = None \<longrightarrow> vt_lookup (tenv env1) y \<noteq> None \<longrightarrow> y = v" by auto
    from P1 r1 obtain x1 X1 ss1 where t1: "t1 = Var x1 X1 \<degree>\<degree> ss1" and x1: "vt_lookup (tenv env1) x1 = None"
      "x1 = v \<or> maxidx env < snd x1" by auto
    have ei1: "einv A K env1" and th1: "tyenv env1 = tyenv env" using fv1 th0 by (simp_all add: finv_def)
    note cs1 = clean_term_sound[OF ct1[unfolded r1] F]
    have wi1: "winv env1 (Y \<union> vars u \<union> vars t1)"
      unfolding winv_def
    proof (intro allI impI)
      fix \<rho> assume \<rho>: "tsol (tyenv env1) \<rho>" "cert_inst \<rho>"
      have tsol: "tsol (tyenv env) \<rho>" using \<rho>(1) th1 by simp
      from winvD[OF wi tsol \<rho>(2)] have w0: "wt_env \<rho> env" "vinv \<rho> env Y" by blast+
      from pd(9)[OF tsol \<rho>(2)] obtain e' T' where e': "bs_env \<rho> e' rb" "e' \<turnstile> inst \<rho> t : T'" by blast
      have vi: "vinv \<rho> env ((Y \<union> vars u) \<union> vars t)"
        using w0(2) vinv_evars[of u t Y env \<rho>] pd(1,2) by (simp add: Un_ac)
      from ff_csoundD[OF cs1 \<rho>(1) extends_refl w0(1) e' pd(7) vi]
      show "wt_env \<rho> env1 \<and> vinv \<rho> env1 (Y \<union> vars u \<union> vars t1)" by blast
    qed
    have w1: "vt_lookup (tenv env1) w = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env1) w \<noteq> None"
      with spec[OF new1, of w] w have "w = v" by blast
      with vw show False by simp
    qed
    have tsol1: "tsol (tyenv env1) (rho0 env)" using r0(1) th1 by simp
    have ty1: "renv e F 0 \<turnstile> inst (rho0 env) t1 : T"
      using ff_csoundD[OF cs1 tsol1 extends_refl _ bs tyt pd(7), of Y] winvD[OF wi r0] ff_vinv_vars_evars[OF pd(1)]
      by blast
    show "xok CHANGE_FAIL ((\<lambda>(env1, t1). bindW (clean_term banned env1 u) (\<lambda>(env2, u1). FF env2 t1 u1)) r1) ?Q"
      unfolding r1 prod.case
    proof (rule xok_bindW[OF clean_term_term[OF fv1 wi1 u w1]])
      show "vars u \<subseteq> Y \<union> vars u \<union> vars t1 \<union> evars env1" by blast
      show "ttvars u \<subseteq> tvars_env (tyenv env1) \<union> A" using pd(4) th1 by simp
      show "\<not> loose_bvar u (ilength rb)" by (rule pd(8))
      show "bs_env (rho0 env1) e rb" using bs th1 by simp
      show "e \<turnstile> inst (rho0 env1) u : T" using tyu th1 by simp
      show "arity T = 0" by (rule a0)
      show "bren_ok banned rb rb' F" by (rule F)
    next
      fix r2 assume ct2: "okW (clean_term banned env1 u) r2"
        and P2: "(\<lambda>(env', t'). finv A K env0 env' \<and> ttvars t' \<subseteq> tvars_env (tyenv env1) \<union> A \<and>
          (\<exists>x X ss. t' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env') x = None \<and> (x = w \<or> maxidx env1 < snd x)) \<and>
          (\<forall>y. vt_lookup (tenv env1) y = None \<longrightarrow> vt_lookup (tenv env') y \<noteq> None \<longrightarrow> y = w)) r2"
      obtain env2 u1 where r2: "r2 = (env2, u1)" by (cases r2)
      from P2 r2 th1 have fv2: "finv A K env0 env2" and tu1: "ttvars u1 \<subseteq> ?KN"
        and new2: "\<forall>y. vt_lookup (tenv env1) y = None \<longrightarrow> vt_lookup (tenv env2) y \<noteq> None \<longrightarrow> y = w" by auto
      from P2 r2 obtain x2 X2 ss2 where u1: "u1 = Var x2 X2 \<degree>\<degree> ss2" and x2: "vt_lookup (tenv env2) x2 = None"
        by auto
      have ei2: "einv A K env2" and th2: "tyenv env2 = tyenv env" using fv2 th0 by (simp_all add: finv_def)
      note cs2 = clean_term_sound[OF ct2[unfolded r2] F]
      have ds: "dstep env [(rb, t, u)] env2 [(rb', t1, u1)]" by (rule clean_dstep[OF cs1 cs2 F])
      define Y2 where "Y2 = Y \<union> vars t1 \<union> vars u1"
      from dstep_pok[OF ds wi p ei2 th2] tt1 tu1 brb
      have wi2: "winv env2 Y2" and p2: "upok A env2 rb' Y2 t1 u1" by (auto simp: Y2_def)
      have x1': "x1 \<noteq> w"
      proof
        assume "x1 = w"
        moreover have "snd w \<le> maxidx env"
        proof -
          have wU: "(w, U0) \<in> Y \<union> evars env" using pd(2) by (auto simp: u vars_apps)
          have "below (maxidx env) (Y \<union> evars env)" using winvD[OF wi r0] by (simp add: vinv_def)
          from belowD[OF this wU] show ?thesis .
        qed
        ultimately show False using x1(2) vw by auto
      qed
      have x12: "vt_lookup (tenv env2) x1 = None"
      proof (rule ccontr)
        assume "vt_lookup (tenv env2) x1 \<noteq> None"
        with spec[OF new2, of x1] x1(1) have "x1 = w" by blast
        with x1' show False by simp
      qed
      have ty2: "renv e F 0 \<turnstile> inst (rho0 env) u1 : T"
      proof -
        have tsol2: "tsol (tyenv env2) (rho0 env)" using r0(1) th2 by simp
        have wte1: "wt_env (rho0 env) env1" using winvD[OF wi1 tsol1 r0(2)] by blast
        have vi1: "vinv (rho0 env) env1 ((Y \<union> vars t1) \<union> vars u)"
          using winvD[OF wi1 tsol1 r0(2)] by (simp add: Un_ac)
        from ff_csoundD[OF cs2 tsol2 extends_refl wte1 _ tyu pd(8) vi1] bs th1 show ?thesis by simp
      qed
      have ar2: "\<exists>e T. bs_env (rho0 env2) e rb' \<and> e \<turnstile> inst (rho0 env2) t1 : T \<and> e \<turnstile> inst (rho0 env2) u1 : T \<and>
          arity T = 0"
      proof -
        from upokD(9)[OF p2 einv_rho0[OF ei2]] obtain e' T' where
          e': "bs_env (rho0 env2) e' rb'" "e' \<turnstile> inst (rho0 env2) t1 : T'" "e' \<turnstile> inst (rho0 env2) u1 : T'" by blast
        have "e' \<turnstile> inst (rho0 env) t1 : T'" using e'(2) th2 by simp
        from var_apps_type_eq[OF this[unfolded t1] ty1[unfolded t1]] have "T' = T" by simp
        with e' a0 show ?thesis by blast
      qed
      have ht1: "\<And>v T. head_of t1 = Var v T \<Longrightarrow> vt_lookup (tenv env2) v = None"
        using x12 by (simp add: t1 head_of_apps)
      have hu1: "\<And>v T. head_of u1 = Var v T \<Longrightarrow> vt_lookup (tenv env2) v = None"
        using x2 by (simp add: u1 head_of_apps)
      have hu1': "\<exists>w W us. u1 = Var w W \<degree>\<degree> us \<and> vt_lookup (tenv env2) w = None"
        by (rule exI[of _ x2], rule exI[of _ X2], rule exI[of _ ss2]) (simp add: u1 x2)
      have ht1': "\<exists>w W us. t1 = Var w W \<degree>\<degree> us \<and> vt_lookup (tenv env2) w = None"
        by (rule exI[of _ x1], rule exI[of _ X1], rule exI[of _ ss1]) (simp add: t1 x12)
      have ar2': "\<exists>e T. bs_env (rho0 env2) e rb' \<and> e \<turnstile> inst (rho0 env2) u1 : T \<and> e \<turnstile> inst (rho0 env2) t1 : T \<and>
          arity T = 0" using ar2 by blast
      have fa1: "xok ASSIGN (ff_assign alg env2 rb' t1 u1) (finv A K env0)"
        by (rule ff_assign_term[OF fv2 wi2 p2 ar2 ht1 hu1'])
      have fa2: "xok ASSIGN (ff_assign alg env2 rb' u1 t1) (finv A K env0)"
        by (rule ff_assign_term[OF fv2 wi2 upok_sym[OF p2] ar2' hu1 ht1'])
      have e02: "extends env0 env2" using fv2 by (simp add: finv_def)
      have qk: "?Q (env2, add_tpair rb' t1 u1 tps)"
        using fv2 add_tpair_known[OF tk, of rb' t1 u1] brb tt1 tu1
          add_tpair_flex[OF tf flexb_VarI[OF ff_unbound_extends[OF e02 x12]] flexb_VarI[OF ff_unbound_extends[OF e02 x2]], of rb']
        by (auto simp: t1 u1)
      have "\<exists>x. okW (FF env2 t1 u1) x \<and> ?Q x"
        unfolding FF_def
      proof (rule xok_handleW)
        show "xok ASSIGN (do {env3 \<leftarrow> ff_assign alg env2 rb' t1 u1; returnW (env3, tps)}) ?Q"
          by (rule xok_bindW[OF fa1]) (use tk tf in simp)
        show "\<exists>x. okW (case ASSIGN of ASSIGN \<Rightarrow> handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)})
            (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW e) | _ \<Rightarrow> raiseW ASSIGN) x \<and> ?Q x"
        proof (simp only: uexn.case, rule xok_handleW)
          show "xok ASSIGN (do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)}) ?Q"
            by (rule xok_bindW[OF fa2]) (use tk tf in simp)
          show "\<exists>x. okW (case ASSIGN of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW ASSIGN) x \<and> ?Q x"
            using qk by simp
        qed
      qed
      then obtain x where "okW (FF env2 t1 u1) x" "?Q x" by blast
      then show "xok CHANGE_FAIL ((\<lambda>(env2, u1). FF env2 t1 u1) r2) ?Q" unfolding r2 prod.case by (rule ff_okW_xok)
    qed
  qed
  have "\<exists>x. okW (clean_ffpair alg rb t u env tps) x \<and> ?Q x"
    unfolding cf by (rule xok_handleW[OF inner]) (use qfail in simp)
  then show ?thesis by auto
qed

subsection \<open>Flex-flex pairs\<close>

theorem add_ffpair_term:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t0 u0"
    and ar: "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t0 : T \<and> e \<turnstile> inst (rho0 env) u0 : T \<and> arity T = 0"
    and ft: "flexb env0 t0" and fu: "flexb env0 u0"
    and tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
    and tf: "\<forall>(t', u')\<in>set tps. flexb env0 t' \<and> flexb env0 u'"
  shows "\<exists>env' tps'. okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps') \<and> finv A K env0 env' \<and>
    (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t', u')\<in>set tps'. flexb env0 t' \<and> flexb env0 u')"
proof -
  have ei: "einv A K env" and fi: "iflex env0 env" and e0: "extends env0 env" using fv by (simp_all add: finv_def)
  note pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  let ?\<rho> = "rho0 env"
  from ar obtain e T where bs: "bs_env ?\<rho> e rb" and tyt0: "e \<turnstile> inst ?\<rho> t0 : T"
    and tyu0: "e \<turnstile> inst ?\<rho> u0 : T" and a0: "arity T = 0" by blast
  have wv: "wt_env ?\<rho> env" "vinv ?\<rho> env Y" using winvD[OF wi r0] by blast+
  have vk: "vok env (Y \<union> evars env)" by (rule vok_winv[OF ei wi pd(6)])
  have vc: "vcons ?\<rho> (Y \<union> evars env)" using wv(2) by (simp add: vinv_def)
  have nterm: "\<exists>s'. norm_term env s = return s' \<and> npost A env s' \<and> e \<turnstile> inst ?\<rho> s' : T \<and>
      (\<exists>x X ss. s' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None)"
    if vs: "vars s \<subseteq> Y \<union> evars env" and ts: "ttvars s \<subseteq> ?KN" and tys: "e \<turnstile> inst ?\<rho> s : T"
      and fs: "flexb env0 s" for s
  proof -
    have vks: "vok env (vars s \<union> evars env)" using vk vs by (auto intro: vok_mono)
    have vcs: "vcons ?\<rho> (vars s \<union> evars env)" by (rule vcons_mono[OF vc]) (use vs in blast)
    from norm_term_term[OF ei vks ts wv(1) vcs tys] obtain s' where
      ns: "norm_term env s = return s'" "npost A env s'" by blast
    have tys': "e \<turnstile> inst ?\<rho> s' : T"
      by (rule nsoundD(3)[OF norm_term_sound[OF ns(1)[unfolded return_def] r0(1) wv(1)] tys])
    have "flexb env0 s'" by (rule norm_term_flex[OF ns(1)[unfolded return_def] fi fs])
    from flexb_base[OF this tys' a0] obtain x X ss where s': "s' = Var x X \<degree>\<degree> ss" by blast
    from ns(2) s' have "vt_lookup (tenv env) x = None" by (simp add: npost_def head_of_apps)
    with ns tys' s' show ?thesis by blast
  qed
  from nterm[OF pd(1) pd(3) tyt0 ft] obtain t where nt: "norm_term env t0 = return t" "npost A env t"
    "e \<turnstile> inst ?\<rho> t : T" and "\<exists>x X ss. t = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None" by blast
  then obtain v Tv ts where t: "t = Var v Tv \<degree>\<degree> ts" and v: "vt_lookup (tenv env) v = None" by blast
  from nterm[OF pd(2) pd(4) tyu0 fu] obtain u where nu: "norm_term env u0 = return u" "npost A env u"
    "e \<turnstile> inst ?\<rho> u : T" and "\<exists>x X ss. u = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None" by blast
  then obtain w Uw us where u: "u = Var w Uw \<degree>\<degree> us" and w: "vt_lookup (tenv env) w = None" by blast
  have ttu: "ttvars t \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" using nt(2) nu(2) by (simp_all add: npost_def)
  have ds: "dstep env [(rb, t0, u0)] env [(rb, t, u)]"
    by (rule norm_term_dstep[OF nt(1)[unfolded return_def] nu(1)[unfolded return_def]])
  define Y' where "Y' = Y \<union> vars t \<union> vars u"
  from dstep_pok[OF ds wi p ei refl] ttu pd(5) have wi': "winv env Y'" and p': "upok A env rb Y' t u"
    by (auto simp: Y'_def)
  have ar': "\<exists>e T. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> t : T \<and> e \<turnstile> inst ?\<rho> u : T \<and> arity T = 0"
    using bs nt(3) nu(3) a0 by blast
  have ar'': "\<exists>e T. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> u : T \<and> e \<turnstile> inst ?\<rho> t : T \<and> arity T = 0"
    using bs nt(3) nu(3) a0 by blast
  have hds: "head_of t = Var v Tv" "head_of u = Var w Uw" by (simp_all add: t u head_of_apps)
  have af: "add_ffpair alg (rb, t0, u0) (env, tps) =
      (if v = w then
        (if Tv = Uw then returnW (env, add_tpair rb t u tps)
         else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
       else if indexname_less v w then clean_ffpair alg rb u t env tps
       else clean_ffpair alg rb t u env tps)"
    by (simp add: add_ffpair_def nt(1) nu(1) hds)
  show ?thesis
  proof (cases "v = w")
    case True
    have "Tv = Uw"
    proof -
      have "vcons ?\<rho> (Y' \<union> evars env)" using winvD[OF wi' r0] by (simp add: vinv_def)
      moreover have "(v, Tv) \<in> Y'" "(v, Uw) \<in> Y'" using True by (auto simp: Y'_def t u vars_apps)
      ultimately have "tsubst ?\<rho> Tv = tsubst ?\<rho> Uw" using vconsD by blast
      moreover have "tnorm (tyenv env) Tv = Tv" "tnorm (tyenv env) Uw = Uw"
        using nt(2) nu(2) hds by (simp_all add: npost_def)
      ultimately show ?thesis by simp
    qed
    moreover have "\<forall>(t', u')\<in>set (add_tpair rb t u tps). ttvars t' \<union> ttvars u' \<subseteq> ?KN"
      by (rule add_tpair_known[OF tk]) (use pd(5) ttu in blast)
    moreover have "\<forall>(t', u')\<in>set (add_tpair rb t u tps). flexb env0 t' \<and> flexb env0 u'"
      by (rule add_tpair_flex[OF tf]) (simp_all add: t u flexb_VarI ff_unbound_extends[OF e0 v] ff_unbound_extends[OF e0 w])
    ultimately show ?thesis using af True fv by simp
  next
    case vw: False
    show ?thesis
    proof (cases "indexname_less v w")
      case True
      from clean_ffpair_term[OF fv wi' upok_sym[OF p'] ar'' u t _ w v tk tf] vw af True show ?thesis by auto
    next
      case False
      from clean_ffpair_term[OF fv wi' p' ar' t u vw v w tk tf] vw af False show ?thesis by auto
    qed
  qed
qed

text \<open>The invariants after a sound step on a list of pairs:\<close>

lemma dstep_winv:
  assumes ds: "dstep env dps env' dps'" and wi: "winv env X" and pk: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    and th: "tyenv env' = tyenv env"
  shows "winv env' (X \<union> dvars dps')" "tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> dtyped \<rho> dps'"
proof -
  have main: "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps')"
    if \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    have tsol: "tsol (tyenv env) \<rho>" using \<rho>(1) th by simp
    from winvD[OF wi tsol \<rho>(2)] have w: "wt_env \<rho> env" "vinv \<rho> env X" by blast+
    have d: "dtyped \<rho> dps"
      unfolding dtyped_def
    proof (clarify)
      fix rb t u assume "(rb, t, u) \<in> set dps"
      with pk have "upok A env rb X t u" by blast
      from upokD(7,8)[OF this] upokD(9)[OF this tsol \<rho>(2)]
      show "(\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
          \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb)" by blast
    qed
    have "dvars dps \<subseteq> X \<union> evars env"
      unfolding dvars_def using pk upokD(1,2) by fast
    then have "X \<union> dvars dps \<union> evars env = X \<union> evars env" by blast
    with w(2) have v: "vinv \<rho> env (X \<union> dvars dps)" by (simp add: vinv_def)
    from dstepD(2)[OF ds \<rho>(1) extends_refl w(1) d v] show ?thesis by blast
  qed
  show "winv env' (X \<union> dvars dps')" unfolding winv_def using main by blast
  show "tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> dtyped \<rho> dps'" using main by blast
qed

text \<open>The flex-flex pairs that the treatment expects: those left by \<^const>\<open>SIMPL\<close>, of a base type in
  the most general solution of the type environment.\<close>

definition ffeta :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "ffeta env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    \<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t : T \<and> e \<turnstile> inst (rho0 env) u : T \<and> arity T = 0)"

text \<open>The invariant of the results: a well-formed environment and closed well-formed pairs.\<close>

definition ffres :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "ffres A K X env tps \<longleftrightarrow> einv A K env \<and> winv env X \<and> (\<forall>(t, u)\<in>set tps. upok A env [] X t u)"

lemma ffres_sinv: "ffres A K X env tps \<longleftrightarrow> sinv A K X env (tdps tps)"
  unfolding ffres_def sinv_def by auto

lemma ff_shape_flexb:
  assumes "ff_shape env (rb, t, u)"
  shows "flexb env t" "flexb env u"
proof -
  have s: "\<not> is_Abs t" "\<not> is_Abs u" "is_Var (head_of t)" "is_Var (head_of u)"
    "\<forall>F T. head_of t = Var F T \<longrightarrow> vt_lookup (tenv env) F = None"
    "\<forall>F T. head_of u = Var F T \<longrightarrow> vt_lookup (tenv env) F = None"
    using assms by (simp_all add: ff_shape_def ffs0_def hunb_def)
  have fl: "flexb env s" if "is_Var (head_of s)" "\<forall>F T. head_of s = Var F T \<longrightarrow> vt_lookup (tenv env) F = None"
    for s
  proof -
    from that(1) obtain F T where h: "head_of s = Var F T" by (cases "head_of s") auto
    have "s = abs_list [] (Var F T \<degree>\<degree> snd (strip_comb s))" using t_apps[of s] h by simp
    moreover have "vt_lookup (tenv env) F = None" using that(2) h by blast
    ultimately show ?thesis unfolding flexb_def by blast
  qed
  show "flexb env t" by (rule fl[OF s(3,5)])
  show "flexb env u" by (rule fl[OF s(4,6)])
qed

theorem foldrW_add_ffpair_term:
  assumes si: "sinv A K X env ffs" and sh: "\<forall>dp\<in>set ffs. ff_shape env dp \<and> ffeta env dp"
    and tp: "ffres A K X env tps" and tfl: "\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u"
  shows "\<exists>env' tps'. okW (foldrW (add_ffpair alg) ffs (env, tps)) (env', tps') \<and>
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and>
    dstep env (ffs @ tdps tps) env' (tdps tps')"
proof -
  have ei: "einv A K env" and wi: "winv env X" using si by (simp_all add: sinv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have pt: "\<forall>(t, u)\<in>set tps. upok A env [] X t u" using tp by (simp add: ffres_def)
  have tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> ?KN" using pt upokD(3,4) by fast
  have pk: "\<forall>(rb, t, u)\<in>set (ffs @ tdps tps). upok A env rb X t u" using si pt by (auto simp: sinv_def)
  have "\<exists>env' tps'. okW (foldrW (add_ffpair alg) ffs' (env, tps)) (env', tps') \<and> finv A K env env' \<and>
      (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> ?KN) \<and> (\<forall>(t', u')\<in>set tps'. flexb env t' \<and> flexb env u')"
    if "set ffs' \<subseteq> set ffs" for ffs'
    using that
  proof (induction ffs')
    case Nil
    have "finv A K env env" using ei by (simp add: finv_def iflex_refl)
    with tk tfl show ?case by simp
  next
    case (Cons dp ffs')
    from Cons.IH Cons.prems obtain env1 tps1 where
      f1: "okW (foldrW (add_ffpair alg) ffs' (env, tps)) (env1, tps1)" and fv1: "finv A K env env1"
      and tk1: "\<forall>(t', u')\<in>set tps1. ttvars t' \<union> ttvars u' \<subseteq> ?KN"
      and tf1: "\<forall>(t', u')\<in>set tps1. flexb env t' \<and> flexb env u'" by auto
    have ei1: "einv A K env1" and th1: "tyenv env1 = tyenv env" and e1: "extends env env1"
      using fv1 by (simp_all add: finv_def)
    obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
    have dpi: "dp \<in> set ffs" using Cons.prems by simp
    have p0: "upok A env rb X t0 u0" using si dpi dp by (auto simp: sinv_def)
    have ds1: "dstep env (ffs' @ tdps tps) env1 (tdps tps1)" by (rule foldrW_add_ffpair_sound[OF f1])
    have pk1: "\<forall>(rb, t, u)\<in>set (ffs' @ tdps tps). upok A env rb X t u"
    proof (clarify)
      fix rb t u assume "(rb, t, u) \<in> set (ffs' @ tdps tps)"
      then have "(rb, t, u) \<in> set (ffs @ tdps tps)" using Cons.prems by auto
      from bspec[OF pk this] show "upok A env rb X t u" by simp
    qed
    define Y where "Y = X \<union> dvars (tdps tps1)"
    have wi1: "winv env1 Y" unfolding Y_def by (rule dstep_winv(1)[OF ds1 wi pk1 th1])
    have vY: "vtvars Y \<subseteq> tvars_env (tyenv env1) \<union> A"
    proof -
      have "vtvars (dvars (tdps tps1)) \<subseteq> ?KN"
        using tk1 vtvars_vars by (fastforce simp: dvars_def vtvars_def)
      then show ?thesis using upokD(6)[OF p0] th1 by (simp add: Y_def vtvars_Un)
    qed
    have p1: "upok A env1 rb Y t0 u0"
      by (rule ff_pok_Y_mono[OF upok_mono[OF p0 e1] vY]) (simp_all add: th1 Y_def)
    have ar: "\<exists>e T. bs_env (rho0 env1) e rb \<and> e \<turnstile> inst (rho0 env1) t0 : T \<and> e \<turnstile> inst (rho0 env1) u0 : T \<and>
        arity T = 0"
    proof -
      have "ffeta env (rb, t0, u0)" using sh dpi dp by blast
      then show ?thesis using th1 by (simp add: ffeta_def)
    qed
    have shp: "ff_shape env (rb, t0, u0)" using sh dpi dp by simp
    have tk1': "\<forall>(t', u')\<in>set tps1. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env1) \<union> A"
      using tk1 th1 by simp
    from add_ffpair_term[OF fv1 wi1 p1 ar ff_shape_flexb[OF shp] tk1' tf1]
    obtain env' tps' where "okW (add_ffpair alg (rb, t0, u0) (env1, tps1)) (env', tps')" "finv A K env env'"
      "\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env1) \<union> A"
      "\<forall>(t', u')\<in>set tps'. flexb env t' \<and> flexb env u'" by blast
    with f1 dp th1 show ?case by auto
  qed
  from this[OF order_refl] obtain env' tps' where f: "okW (foldrW (add_ffpair alg) ffs (env, tps)) (env', tps')"
    and fv: "finv A K env env'" and tk': "\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> ?KN"
    and tf': "\<forall>(t', u')\<in>set tps'. flexb env t' \<and> flexb env u'" by blast
  have ei': "einv A K env'" and th: "tyenv env' = tyenv env" and e': "extends env env'" and fi': "iflex env env'"
    using fv by (simp_all add: finv_def)
  have ds: "dstep env (ffs @ tdps tps) env' (tdps tps')" by (rule foldrW_add_ffpair_sound[OF f])
  note dw = dstep_winv[OF ds wi pk th]
  let ?X' = "X \<union> dvars (tdps tps')"
  have "upok A env' [] ?X' t u" if tu: "(t, u) \<in> set tps'" for t u
  proof -
    have vX: "vtvars X \<subseteq> ?KN"
    proof (cases ffs)
      case Nil
      with f have "tps' = tps" by simp
      with tu pt show ?thesis using upokD(6) by fast
    next
      case (Cons dp ffs'')
      obtain rb t0 u0 where "dp = (rb, t0, u0)" by (cases dp)
      with si Cons have "upok A env rb X t0 u0" by (auto simp: sinv_def)
      then show ?thesis by (rule upokD(6))
    qed
    have vX': "vtvars ?X' \<subseteq> ?KN"
      using vX tk' vtvars_vars by (fastforce simp: dvars_def vtvars_def)
    have dt: "dtyped \<rho> [([], t, u)]" if "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
      using dw(2)[OF that] tu by (auto simp: dtyped_def)
    show ?thesis
      unfolding upok_def
    proof (intro conjI allI impI)
      show "vars t \<union> vars u \<subseteq> ?X' \<union> evars env'" using tu by (force simp: dvars_def)
      show "ttvars t \<union> ttvars u \<union> btvars [] \<union> vtvars ?X' \<subseteq> tvars_env (tyenv env') \<union> A"
        using tk' tu vX' th by (auto simp: btvars_def)
      show "\<not> loose_bvar t (ilength [])" "\<not> loose_bvar u (ilength [])"
        using dt[OF einv_rho0[OF ei']] by (simp_all add: dtyped_def)
      fix \<rho> assume "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
      from dt[OF this] show "\<exists>e T. bs_env \<rho> e [] \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T"
        by (simp add: dtyped_def)
    qed
  qed
  then have "ffres A K ?X' env' tps'" using ei' dw(1) by (auto simp: ffres_def)
  with f e' th ds fi' tf' show ?thesis by blast
qed

corollary foldrW_add_ffpair_term_Nil:
  assumes "sinv A K X env ffs" "\<forall>dp\<in>set ffs. ff_shape env dp \<and> ffeta env dp"
  shows "\<exists>env' tps'. okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps') \<and>
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and> dstep env ffs env' (tdps tps')"
proof -
  have "ffres A K X env []" using assms(1) by (simp add: ffres_def sinv_def)
  from foldrW_add_ffpair_term[OF assms this] show ?thesis by simp
qed

text \<open>For \<open>smash_flexflex\<close>: the remaining pairs stay flexible under the environment.\<close>

lemma strip_abs_body_abs_list: "strip_abs_body (abs_list bs t) = strip_abs_body t"
  by (induction bs) auto

lemma flexb_strip_abs_body:
  "flexb env0 t \<Longrightarrow> \<exists>G V. head_of (strip_abs_body t) = Var G V \<and> vt_lookup (tenv env0) G = None"
proof -
  assume "flexb env0 t"
  then obtain bs G V ss where t: "t = abs_list bs (Var G V \<degree>\<degree> ss)" and G: "vt_lookup (tenv env0) G = None"
    unfolding flexb_def by blast
  have "strip_abs_body (Var G V \<degree>\<degree> ss) = Var G V \<degree>\<degree> ss"
    using not_App_apps_Abs[of "Var G V" ss] by (cases "Var G V \<degree>\<degree> ss") auto
  then have "head_of (strip_abs_body t) = Var G V" by (simp add: t strip_abs_body_abs_list head_of_apps)
  with G show ?thesis by blast
qed

end

end
