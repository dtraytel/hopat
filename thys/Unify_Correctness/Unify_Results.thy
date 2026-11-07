section \<open>The Results of Higher-Order Unification\<close>

theory Unify_Results
  imports Unify_Pull_Fin Unify_Smash_Sound
begin

context pure_sig
begin

text \<open>
  On a well-formed problem (\<^const>\<open>sinv\<close>), \<^const>\<open>unifiers\<close> returns a sequence whose
  enumeration is finite, and every unifier \<open>El_R env' tps\<close> of it is a step from the input pairs
  to the remaining flex-flex pairs \<open>tps\<close> (\<^const>\<open>dstep\<close>), where \<open>env'\<close> and \<open>tps\<close> are well-formed
  again (\<^const>\<open>ffres\<close>), with flexible pairs (\<open>fflex\<close>). Consequences: smashing the
  flex-flex pairs terminates normally and is sound, terms that are well-typed in the input stay
  well-typed, variables that occur neither in the problem nor in the environment stay fresh, as
  do such type variables, and the maximal index does not decrease.
\<close>

subsection \<open>The invariant of the results\<close>

text \<open>
  The flex-flex pairs of a result are flexible terms whose heads are unbound in an earlier
  environment \<open>e0\<close>, and the bindings added since \<open>e0\<close> are flexible (\<^const>\<open>iflex\<close>), so that
  normalization keeps the pairs flexible:
\<close>

definition fflex :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> env \<Rightarrow>
    (pterm \<times> pterm) list \<Rightarrow> bool" where
  "fflex A K e0 env tps \<longleftrightarrow> finv A K e0 env \<and> (\<forall>(t, u)\<in>set tps. flexb e0 t \<and> flexb e0 u)"

text \<open>
  The invariant of the results, for the type variables \<open>A0\<close> of the problem: the known type
  variables \<open>A\<close> of a result include \<open>A0\<close>, and the result introduces only type variables that are
  known in the problem or have indices above its maximal index (\<^const>\<open>tnew\<close>).
\<close>

definition uresult :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> elem \<Rightarrow> bool" where
  "uresult A0 env tus x \<longleftrightarrow> (\<exists>env' tps. x = El_R env' tps \<and> dstep env (tdps tus) env' (tdps tps) \<and>
    (\<exists>A K X e0. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env A env' \<and> ffres A K X env' tps \<and>
      fflex A K e0 env' tps))"

lemma uresult_El_R:
  "uresult A0 env tus (El_R env' tps) \<longleftrightarrow> dstep env (tdps tus) env' (tdps tps) \<and>
    (\<exists>A K X e0. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env A env' \<and> ffres A K X env' tps \<and>
      fflex A K e0 env' tps)"
  unfolding uresult_def by blast

lemma uresultI:
  assumes "dstep env (tdps tus) env' (tdps tps)" "finite X" "finite K" "A0 \<subseteq> A" "tnew A0 env A env'"
    "ffres A K X env' tps" "fflex A K e0 env' tps"
  shows "uresult A0 env tus (El_R env' tps)"
  unfolding uresult_El_R
  by (rule conjI[OF assms(1)], rule exI[of _ A], rule exI[of _ K], rule exI[of _ X], rule exI[of _ e0])
    (simp add: assms(2-7))

text \<open>The unifiers of the search (\<^const>\<open>rres\<close>) are well-formed:\<close>

lemma rres_ffres:
  assumes "rres A0 env0 x"
  shows "\<exists>env' tps. x = El_R env' tps \<and>
    (\<exists>A K X e0. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env0 A env' \<and> ffres A K X env' tps \<and>
      fflex A K e0 env' tps)"
proof -
  from assms obtain env' tps A K X env ffs where x: "x = El_R env' tps" and fin: "finite X" "finite K"
    and A0: "A0 \<subseteq> A" and tn: "tnew A0 env0 A env"
    and si: "sinv A K X env ffs" and f: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps)"
    and fv: "finv A K env env'"
    and tk: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    and fl: "\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u"
    unfolding rres_def by blast
  have wi: "winv env X" using si by (simp add: sinv_def)
  have ei': "einv A K env'" and th: "tyenv env' = tyenv env" using fv by (simp_all add: finv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have pk: "\<forall>(rb, t, u)\<in>set (ffs @ tdps []). pok A env rb X t u" using si by (simp add: sinv_def)
  have ds: "dstep env (ffs @ tdps []) env' (tdps tps)" by (rule foldrW_add_ffpair_sound[OF f])
  note dw = dstep_winv[OF ds wi pk th]
  let ?X' = "X \<union> dvars (tdps tps)"
  have "pok A env' [] ?X' t u" if tu: "(t, u) \<in> set tps" for t u
  proof -
    have vX: "vtvars X \<subseteq> ?KN"
    proof (cases ffs)
      case Nil
      with f have "tps = []" by simp
      with tu show ?thesis by simp
    next
      case (Cons dp ffs')
      obtain rb t0 u0 where "dp = (rb, t0, u0)" by (cases dp)
      with si Cons have "pok A env rb X t0 u0" by (auto simp: sinv_def)
      then show ?thesis by (rule pokD(6))
    qed
    have vX': "vtvars ?X' \<subseteq> ?KN"
      using vX tk vtvars_vars by (fastforce simp: dvars_def vtvars_def)
    have dt: "dtyped \<rho> [([], t, u)]" if "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
      using dw(2)[OF that] tu by (auto simp: dtyped_def)
    show ?thesis
      unfolding pok_def
    proof (intro conjI allI impI)
      show "vars t \<union> vars u \<subseteq> ?X' \<union> evars env'" using tu by (force simp: dvars_def)
      show "ttvars t \<union> ttvars u \<union> btvars [] \<union> vtvars ?X' \<subseteq> tvars_env (tyenv env') \<union> A"
        using tk tu vX' th by (auto simp: btvars_def)
      show "\<not> loose_bvar t (ilength [])" "\<not> loose_bvar u (ilength [])"
        using dt[OF einv_rho0[OF ei']] by (simp_all add: dtyped_def)
      fix \<rho> assume "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
      from dt[OF this] show "\<exists>e T. bs_env \<rho> e [] \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T"
        by (simp add: dtyped_def)
    qed
  qed
  then have "ffres A K ?X' env' tps" using ei' dw(1) by (auto simp: ffres_def)
  moreover have "finite ?X'" using fin(1) finite_dvars by simp
  moreover have "fflex A K env env' tps" using fv fl by (simp add: fflex_def)
  moreover have "tnew A0 env0 A env'" using tn th by (simp add: tnew_def)
  ultimately have "finite ?X' \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env0 A env' \<and> ffres A K ?X' env' tps \<and>
      fflex A K env env' tps"
    using fin(2) A0 by blast
  note h = this
  show ?thesis unfolding x by (rule exI[of _ env'], rule exI[of _ tps], rule conjI[OF refl], rule exI[of _ A],
      rule exI[of _ K], rule exI[of _ ?X'], rule exI[of _ env]) (rule h)
qed

subsection \<open>Pattern unification of the input pairs\<close>

lemma ur_foldM_unify:
  assumes fin: "finite X" "finite K"
  shows "einv A K env \<Longrightarrow> winv env X \<Longrightarrow> \<forall>(t, u)\<in>set tus. pok A env [] X t u \<Longrightarrow>
    \<exists>r. foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r \<and>
      (\<forall>e. r = Err e \<longrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern) \<and>
      (\<forall>env'. r = Ok env' \<longrightarrow> einv A K env' \<and> winv env' X \<and> tnew A env A env')"
proof (induction tus arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons tu tus)
  obtain t u where tu: "tu = (t, u)" by force
  have p: "pok A env [] X t u" using Cons.prems(3) tu by simp
  from unif_term[OF fin Cons.prems(1,2) p] obtain r1 where
    r1: "unif alg [] t u env = Some r1" "upost A K env X r1" by blast
  show ?case
  proof (cases r1)
    case (Err e)
    with r1 show ?thesis by (simp add: tu unify_def bindM_def)
  next
    case (Ok env1)
    note a = upost_OkD[OF r1(2)[unfolded Ok]]
    have "\<forall>(t, u)\<in>set tus. pok A env1 [] X t u"
      using Cons.prems(3) pok_mono[OF _ a(3,4)] by auto
    from Cons.IH[OF a(1,2) this] obtain r where
      r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env1 = Some r"
        "\<forall>e. r = Err e \<longrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern"
        "\<forall>env'. r = Ok env' \<longrightarrow> einv A K env' \<and> winv env' X \<and> tnew A env1 A env'" by blast
    have "\<forall>env'. r = Ok env' \<longrightarrow> einv A K env' \<and> winv env' X \<and> tnew A env A env'"
      using r(3) tnew_trans[OF a(7) _ extends_maxidx[OF a(3)]] by blast
    with r(1,2) r1(1) Ok show ?thesis by (simp add: tu unify_def bindM_def)
  qed
qed


subsection \<open>Finiteness of the enumeration\<close>

theorem unifiers_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
  obtains s where "unifiers alg env tus = Some (Ok s)" "fin cfg s (uresult A env tus)"
proof -
  have ei: "einv A K env" and wi: "winv env X" and p: "\<forall>(t, u)\<in>set tus. pok A env [] X t u"
    using si by (auto simp: sinv_def)
  from ur_foldM_unify[OF fin ei wi p] obtain r where
    r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r"
      "\<forall>e. r = Err e \<longrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern"
      "\<forall>env'. r = Ok env' \<longrightarrow> einv A K env' \<and> winv env' X \<and> tnew A env A env'" by blast
  show thesis
  proof (cases r)
    case (Ok env')
    with r(1) have u: "unifiers alg env tus = Some (Ok (S_Single (El_R env' [])))"
      by (simp add: unifiers_def handle_def bindM_def return_def)
    have "dstep env (tdps tus) env' []" by (rule foldM_unify_dstep) (use r(1) Ok in simp)
    moreover have "ffres A K X env' []" using r(3) Ok by (simp add: ffres_def)
    moreover have "fflex A K env' env' []" using r(3) Ok by (simp add: fflex_def finv_def iflex_refl)
    moreover have "tnew A env A env'" using r(3) Ok by simp
    ultimately have "uresult A env tus (El_R env' [])" using uresultI[OF _ fin order_refl, of env tus env' "[]"] by simp
    then show thesis by (rule that[OF u fin_Single])
  next
    case (Err e)
    with r(2) consider "e = Pattern" | v where "e = Unif v" by blast
    then show thesis
    proof cases
      case 1
      with r(1) Err have u: "unifiers alg env tus = Some (Ok (hounifiers [] env tus))"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      from hounifiers_fin[OF cfg fin si] obtain xs where es: "evals cfg (hounifiers [] env tus) xs"
        and rs: "\<forall>x\<in>set xs. rres A env x"
        unfolding fin_def by blast
      have "uresult A env tus x" if x: "x \<in> set xs" for x
      proof -
        from unifiers_sound[OF cfg fin si u es x] obtain env' tps where x': "x = El_R env' tps"
          and ds: "dstep env (tdps tus) env' (tdps tps)" by blast
        from rres_ffres[OF bspec[OF rs x]] x' ds show ?thesis unfolding uresult_def by auto
      qed
      with es have "fin cfg (hounifiers [] env tus) (uresult A env tus)" unfolding fin_def by blast
      with u show thesis by (rule that)
    next
      case 2
      with r(1) Err have u: "unifiers alg env tus = Some (Ok S_Empty)"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      show thesis by (rule that[OF u fin_Empty])
    qed
  qed
qed

text \<open>Hence every enumeration of the result consists of well-formed unifiers:\<close>

theorem unifiers_uresult:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "x \<in> set xs"
  shows "uresult A env tus x"
proof -
  from unifiers_fin[OF cfg fin si] u obtain ys where "evals cfg s ys" "\<forall>y\<in>set ys. uresult A env tus y"
    unfolding fin_def by auto
  with evals_det[OF es] x show ?thesis by blast
qed

lemma uresultD:
  assumes "uresult A0 env tus (El_R env' tps)"
  shows "dstep env (tdps tus) env' (tdps tps)" "extends env env'"
    and "\<exists>A K X e0. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env A env' \<and> ffres A K X env' tps \<and>
      fflex A K e0 env' tps"
  using assms dstepD(1) unfolding uresult_def by blast+


subsection \<open>Typing of the input\<close>

lemma ur_vinv_sub: "vinv \<rho> env X \<Longrightarrow> Y \<subseteq> X \<union> evars env \<Longrightarrow> vinv \<rho> env Y"
proof -
  assume v: "vinv \<rho> env X" and Y: "Y \<subseteq> X \<union> evars env"
  then have sub: "Y \<union> evars env \<subseteq> X \<union> evars env" by blast
  from v have "vcons \<rho> (X \<union> evars env)" "below (maxidx env) (X \<union> evars env)" by (simp_all add: vinv_def)
  with sub show ?thesis unfolding vinv_def by (blast intro: vcons_mono below_mono)
qed

lemma ur_winv_sub: "winv env X \<Longrightarrow> Y \<subseteq> X \<union> evars env \<Longrightarrow> winv env Y"
  unfolding winv_def using ur_vinv_sub by blast

lemma sinv_dtyped: "sinv A K X env dps \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> dtyped \<rho> dps"
  unfolding sinv_def dtyped_def by (fastforce dest: pokD(7-9))

text \<open>A well-formed problem is well-typed at the certified solutions of its type environment:\<close>

lemma sinv_gtyped:
  assumes si: "sinv A K X env dps"
  shows "gtyped env dps"
  unfolding gtyped_def
proof (intro allI impI conjI)
  fix \<rho> assume t: "tsol (tyenv env) \<rho>" and c: "cert_inst \<rho>"
  have wi: "winv env X" using si by (simp add: sinv_def)
  from winvD[OF wi t c] have "wt_env \<rho> env" "vinv \<rho> env X" by blast+
  then show "wt_env \<rho> env" "vinv \<rho> env (dvars dps)" using ur_vinv_sub sinv_dvars[OF si] by blast+
  show "dtyped \<rho> dps" by (rule sinv_dtyped[OF si t c])
qed


subsection \<open>Smashing the flex-flex pairs\<close>

lemma ffres_smash:
  assumes "ffres A K X env tps"
  shows "tacyc (tyenv env)" "tcons_env (tyenv env)" "cert_inst (tsol0 (tyenv env))" "gtyped env (tdps tps)"
proof -
  have ei: "einv A K env" using assms by (simp add: ffres_def)
  note e = einvD[OF ei]
  show "tacyc (tyenv env)" "tcons_env (tyenv env)" by (rule e(6), rule e(7))
  show "cert_inst (tsol0 (tyenv env))" by (rule tsol0(3)[OF e(2) e(12) e(9)])
  show "gtyped env (tdps tps)" by (rule sinv_gtyped) (use assms in \<open>simp add: ffres_sinv\<close>)
qed

subsection \<open>Termination of smashing\<close>

text \<open>
  On a result, \<^const>\<open>smash_flexflex\<close> terminates normally. Each pair is normalized to flexible
  terms whose heads are unbound and of normal types (\<open>hnorm\<close>); their heads \<open>?v :: T\<close> and
  \<open>?w :: U\<close> are bound to constant functions over a new variable \<open>?x\<close>. If \<open>?v = ?w\<close>, then
  \<open>T = U\<close>, since the types of a variable agree in the most general solution of the type
  environment; otherwise the binding of \<open>?w\<close> (or of \<open>?x\<close> to \<open>?w\<close>) leaves \<open>?v\<close> unbound. The
  new bindings are flexible, so the invariant \<^const>\<open>finv\<close> of the treatment of flex-flex pairs
  is kept.
\<close>

definition hnorm :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "hnorm env t \<longleftrightarrow> (\<forall>G V. head_of (strip_abs_body t) = Var G V \<longrightarrow>
    vt_lookup (tenv env) G = None \<and> tnorm (tyenv env) V = V)"

lemma hnorm_Abs: "hnorm env b \<Longrightarrow> hnorm env (Abs a T b)"
  by (simp add: hnorm_def)

lemma hnorm_App: "hnorm env nf \<Longrightarrow> \<not> is_Abs nf \<Longrightarrow> hnorm env (nf $ nu)"
  by (simp add: hnorm_def strip_abs_body_nonAbs)

lemma hnorm_rigid: "hnorm env (Const a T)" "hnorm env (Free a T)" "hnorm env (Bound i)"
  by (simp_all add: hnorm_def)

lemma norm_term1_hnorm:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> hnorm env t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and em = "1.prems"(3)
  have IH: "hnorm env u'" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te em] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with ok_lookup1[OF lr] te have x0: "vt_lookup (tenv env) x = None" by simp
      from rest None Var have "t' = Var x T" by simp
      with x0 show ?thesis by (simp add: hnorm_def tnorm_empty[OF em])
    qed (use rest IH in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH[OF this(1)] show ?thesis by (simp add: hnorm_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt te (subst_bound u body)) t'" by simp
      then show ?thesis by (rule IH)
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        then show ?thesis by (rule IH)
      next
        case nA: False
        with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
        with hnorm_App[OF IH[OF hf] nA] show ?thesis by simp
      qed
    qed
  qed (use h hnorm_rigid in auto)
qed

lemma norm_term2_hnorm:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> einv A K env \<Longrightarrow> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    hnorm env t' \<and> ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ei = "1.prems"(2) and tv = "1.prems"(3)
  note e = einvD[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have IH: "hnorm env u' \<and> ttvars u' \<subseteq> ?KN" if "ok (nt env u) u'" "ttvars u \<subseteq> ?KN" for u u'
    using "1.IH"[OF that(1) refl ei that(2)] .
  have nT: "norm_type_aux (tyenv env) T = return (tnorm (tyenv env) T)" "tvars (tnorm (tyenv env) T) \<subseteq> ?KN"
    if "tvars T \<subseteq> ?KN" for T
    using ff_norm_type[OF ei that] by simp_all
  have sb: "ttvars (subst_bound u body) \<subseteq> ?KN" if "ttvars body \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" for u body
    using ttvars_subst[of body u 0] that by (simp add: subst_bound_subst) blast
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      from lr Some obtain U where lk: "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      have "ttvars u \<subseteq> ?KN" using tvinvD(2)[OF e(1) lk] by blast
      with rest Some IH show ?thesis by simp
    next
      case None
      have x0: "vt_lookup (tenv env) x = None" using lr None ok_lookup_None by simp
      have tvT: "tvars T \<subseteq> ?KN" using tv Var by simp
      from rest None nT(1)[OF tvT] have "t' = Var x (tnorm (tyenv env) T)" by (simp add: return_def)
      with x0 nT(2)[OF tvT] show ?thesis by (simp add: hnorm_def tnorm_idem[OF e(6)])
    qed
  next
    case (Abs a T body)
    have tvT: "tvars T \<subseteq> ?KN" and tvb: "ttvars body \<subseteq> ?KN" using tv Abs by simp_all
    with h Abs nT(1)[OF tvT] obtain body' where "ok (nt env body) body'" "t' = Abs a (tnorm (tyenv env) T) body'"
      by (auto simp: return_def)
    with IH[OF this(1) tvb] nT(2)[OF tvT] show ?thesis by (simp add: hnorm_Abs)
  next
    case (App f u)
    have tvf: "ttvars f \<subseteq> ?KN" and tvu: "ttvars u \<subseteq> ?KN" using tv App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      moreover have "ttvars (subst_bound u body) \<subseteq> ?KN" by (rule sb) (use tvf f tvu in simp_all)
      ultimately show ?thesis by (rule IH)
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      note nf = IH[OF hf tvf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfA: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        moreover have "ttvars (subst_bound u body) \<subseteq> ?KN" by (rule sb) (use nf nfA tvu in simp_all)
        ultimately show ?thesis by (rule IH)
      next
        case nA: False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        with hnorm_App[OF conjunct1[OF nf] nA] IH[OF hu tvu] nf show ?thesis by simp
      qed
    qed
  next
    case (Const a T)
    have tvT: "tvars T \<subseteq> ?KN" using tv Const by simp
    with h Const nT[OF tvT] show ?thesis by (auto simp: return_def hnorm_rigid)
  next
    case (Free a T)
    have tvT: "tvars T \<subseteq> ?KN" using tv Free by simp
    with h Free nT[OF tvT] show ?thesis by (auto simp: return_def hnorm_rigid)
  next
    case (Bound i)
    with h show ?thesis by (auto simp: return_def hnorm_rigid)
  qed
qed

lemma norm_term_hnorm:
  assumes "ok (norm_term env t) t'" "einv A K env" "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "hnorm env t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have em: "vt_is_empty (tenv env)" "vt_is_empty (tyenv env)" by (simp_all add: env_is_empty_def)
    from id assms(1) have "t' = t" by (simp add: norm_term_def)
    then show ?thesis by (simp add: hnorm_def vt_is_empty_lookup[OF em(1)] tnorm_empty[OF em(2)])
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_hnorm[OF this refl refl n1(2)] show ?thesis .
  next
    case n2
    with assms(1) have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_hnorm[OF this refl assms(2,3)] show ?thesis by blast
  qed
qed

text \<open>The bindings of smashing:\<close>

lemma ur_dep_chain:
  assumes "vt_lookup (tenv env) x = Some (B, Var w B)" "vt_lookup (tenv env) w = None" "F \<noteq> x" "F \<noteq> w"
  shows "(F, x) \<notin> (dep env)\<^sup>*"
proof
  assume "(F, x) \<in> (dep env)\<^sup>*"
  with assms(3) have "(F, x) \<in> (dep env)\<^sup>+" by (auto dest: rtranclD)
  then obtain z where z: "(F, z) \<in> (dep env)\<^sup>*" "(z, x) \<in> dep env" by (auto dest: tranclD2)
  from z(2) assms(1) have "z = w" by (auto elim: depE)
  with z(1) not_dep_unbound[OF assms(2,4)] show False by simp
qed

lemma ur_flexb_types_abs: "vt_lookup (tenv e0) x = None \<Longrightarrow> flexb e0 (types_abs Ps (Var x B))"
  by (induction Ps) (simp_all add: flexb_Var flexb_AbsI)

lemma ur_closed_types_abs: "closed (types_abs Ps (Var x B))"
  by (simp add: closed_def loose_bvar_types_abs)

lemma ur_ttvars_types_abs: "ttvars (types_abs Ps (Var x B)) = (\<Union>P\<in>set Ps. tvars P) \<union> tvars B"
  by (simp add: ttvars_types_abs)

lemma ur_update:
  assumes fv: "finv A K e0 env" and F: "vt_lookup (tenv env) F = None" "snd F \<le> maxidx env"
    and acy: "\<forall>y\<in>fst ` vars s. (F, y) \<notin> (dep env)\<^sup>*" and cl: "closed s"
    and tv: "tvars FT \<union> ttvars s \<subseteq> tvars_env (tyenv env) \<union> A" and fl: "flexb e0 s"
  shows "\<exists>env'. update (F, FT) s env = return env' \<and> finv A K e0 env' \<and>
    tenv env' = vt_update (F, (FT, s)) (tenv env) \<and> tyenv env' = tyenv env \<and> maxidx env' = maxidx env"
proof -
  have ei: "einv A K env" and fi: "iflex e0 env" using fv by (simp_all add: finv_def)
  from update_ok[OF F(1)] obtain env' where upd: "update (F, FT) s env = return env'" by blast
  then have upd': "ok (update (F, FT) s env) env'" by (simp add: return_def)
  have "einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and> iflex e0 env'"
    by (rule update_inv[OF ei upd' _ cl F(2) tv fl fi]) (use acy in force)
  then have "finv A K e0 env'" by (rule finv_trans[OF fv])
  with upd ok_update(2-4)[OF upd'] show ?thesis by blast
qed

lemma ur_vupdate_nonVar: "\<not> (\<exists>y Y. s = Var y Y) \<Longrightarrow> vupdate aU s env = update aU s env"
  by (subst vupdate.simps) (auto split: pterm.splits)

text \<open>Binding an unbound variable to a constant function over an unbound variable:\<close>

lemma ur_vupdate_fresh:
  assumes fv: "finv A K e0 env"
    and F: "vt_lookup (tenv env) F = None" "snd F \<le> maxidx env" "F \<noteq> x" "vt_lookup (tenv e0) F = None"
    and x: "vt_lookup (tenv env) x = None" "snd x \<le> maxidx env"
    and tv: "tvars FT \<union> tvars B \<union> (\<Union>P\<in>set Ps. tvars P) \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. vupdate (F, FT) (types_abs Ps (Var x B)) env = return env' \<and> finv A K e0 env' \<and>
    tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
    (Ps \<noteq> [] \<or> \<not> indexname_less F x \<longrightarrow> tenv env' = vt_update (F, (FT, types_abs Ps (Var x B))) (tenv env)) \<and>
    (Ps = [] \<longrightarrow> indexname_less F x \<longrightarrow> tenv env' = vt_update (x, (B, Var F B)) (tenv env))"
proof -
  have e0: "extends e0 env" using fv by (simp add: finv_def)
  have x0: "vt_lookup (tenv e0) x = None" by (rule ff_unbound_extends[OF e0 x(1)])
  let ?s = "types_abs Ps (Var x B)"
  show ?thesis
  proof (cases "Ps \<noteq> [] \<or> \<not> indexname_less F x")
    case True
    have vu: "vupdate (F, FT) ?s env = update (F, FT) ?s env"
    proof (cases Ps)
      case Nil
      with True have "\<not> indexname_less F x" by simp
      with Nil F(3) show ?thesis by (subst vupdate.simps) simp
    next
      case (Cons P Ps')
      then show ?thesis by (simp add: ur_vupdate_nonVar)
    qed
    have acy: "\<forall>y\<in>fst ` vars ?s. (F, y) \<notin> (dep env)\<^sup>*" using not_dep_unbound[OF x(1) F(3)] by simp
    have tvs: "tvars FT \<union> ttvars ?s \<subseteq> tvars_env (tyenv env) \<union> A" using tv by (auto simp: ur_ttvars_types_abs)
    from ur_update[where s = ?s and FT = FT, OF fv F(1,2) acy ur_closed_types_abs tvs ur_flexb_types_abs[OF x0]]
    obtain env' where
      "update (F, FT) ?s env = return env'" "finv A K e0 env'"
      "tenv env' = vt_update (F, (FT, ?s)) (tenv env)" "tyenv env' = tyenv env" "maxidx env' = maxidx env"
      by blast
    with vu True show ?thesis by auto
  next
    case False
    then have Ps: "Ps = []" and lt: "indexname_less F x" by auto
    have vu: "vupdate (F, FT) ?s env = update (x, B) (Var F B) env"
      using Ps lt F(3) by (subst vupdate.simps) (simp add: lookup_unbound[OF x(1)])
    have acy: "\<forall>y\<in>fst ` vars (Var F B). (x, y) \<notin> (dep env)\<^sup>*" using not_dep_unbound[OF F(1)] F(3) by auto
    have tvs: "tvars B \<union> ttvars (Var F B) \<subseteq> tvars_env (tyenv env) \<union> A" using tv by auto
    have cls: "closed (Var F B)" by (simp add: closed_def)
    have fls: "flexb e0 (Var F B)" using F(4) by (simp add: flexb_Var)
    from ur_update[where s = "Var F B" and FT = B, OF fv x acy cls tvs fls] obtain env' where
      "update (x, B) (Var F B) env = return env'" "finv A K e0 env'"
      "tenv env' = vt_update (x, (B, Var F B)) (tenv env)" "tyenv env' = tyenv env" "maxidx env' = maxidx env"
      by blast
    with vu Ps lt show ?thesis by auto
  qed
qed

text \<open>Binding an unbound variable when the new variable is bound to a variable:\<close>

lemma ur_vupdate_chain:
  assumes fv: "finv A K e0 env" and lx: "vt_lookup (tenv env) x = Some (B, Var w B)"
    and v: "vt_lookup (tenv env) v = None" "snd v \<le> maxidx env" "vt_lookup (tenv e0) v = None"
    and w: "vt_lookup (tenv env) w = None" "snd w \<le> maxidx env" "vt_lookup (tenv e0) w = None"
    and x0: "vt_lookup (tenv e0) x = None" and ne: "v \<noteq> x" "v \<noteq> w"
    and tv: "tvars T \<union> tvars B \<union> (\<Union>P\<in>set Ps. tvars P) \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. vupdate (v, T) (types_abs Ps (Var x B)) env = return env' \<and> finv A K e0 env'"
proof -
  have ei: "einv A K env" using fv by (simp add: finv_def)
  note e = einvD[OF ei]
  let ?s = "types_abs Ps (Var x B)"
  show ?thesis
  proof (cases "Ps \<noteq> [] \<or> \<not> indexname_less v x")
    case True
    have vu: "vupdate (v, T) ?s env = update (v, T) ?s env"
    proof (cases Ps)
      case Nil
      with True have "\<not> indexname_less v x" by simp
      with Nil ne(1) show ?thesis by (subst vupdate.simps) simp
    next
      case (Cons P Ps')
      then show ?thesis by (simp add: ur_vupdate_nonVar)
    qed
    have acy: "\<forall>y\<in>fst ` vars ?s. (v, y) \<notin> (dep env)\<^sup>*" using ur_dep_chain[OF lx w(1) ne] by simp
    have tvs: "tvars T \<union> ttvars ?s \<subseteq> tvars_env (tyenv env) \<union> A" using tv by (auto simp: ur_ttvars_types_abs)
    from ur_update[where s = ?s and FT = T, OF fv v(1,2) acy ur_closed_types_abs tvs ur_flexb_types_abs[OF x0]]
    obtain env' where "update (v, T) ?s env = return env'" "finv A K e0 env'"
      by blast
    with vu show ?thesis by auto
  next
    case False
    then have Ps: "Ps = []" and lt: "indexname_less v x" by auto
    have tcB: "tcons (tyenv env) B" by (rule ff_tcons[OF ei]) (use tv in blast)
    have lk: "lookup env x B = return (Some (Var w B))"
      by (simp add: lookup_def lx unified_ok[OF e(6,7) tcB tcB])
    have vu: "vupdate (v, T) ?s env = vupdate (v, T) (Var w B) env"
      using Ps lt ne(1) by (subst (1) vupdate.simps) (simp add: lk)
    show ?thesis
    proof (cases "indexname_less v w")
      case True
      have vu': "vupdate (v, T) (Var w B) env = update (w, B) (Var v B) env"
        using True ne(2) by (subst vupdate.simps) (simp add: lookup_unbound[OF w(1)])
      have acy: "\<forall>y\<in>fst ` vars (Var v B). (w, y) \<notin> (dep env)\<^sup>*" using not_dep_unbound[OF v(1)] ne(2) by auto
      have tvs: "tvars B \<union> ttvars (Var v B) \<subseteq> tvars_env (tyenv env) \<union> A" using tv by auto
      have cls: "closed (Var v B)" by (simp add: closed_def)
      have fls: "flexb e0 (Var v B)" using v(3) by (simp add: flexb_Var)
      from ur_update[where s = "Var v B" and FT = B, OF fv w(1,2) acy cls tvs fls] obtain env' where
        "update (w, B) (Var v B) env = return env'" "finv A K e0 env'"
        by blast
      with vu vu' show ?thesis by auto
    next
      case False
      have vu': "vupdate (v, T) (Var w B) env = update (v, T) (Var w B) env"
        using False ne(2) by (subst vupdate.simps) simp
      have acy: "\<forall>y\<in>fst ` vars (Var w B). (v, y) \<notin> (dep env)\<^sup>*" using not_dep_unbound[OF w(1)] ne(2) by auto
      have tvs: "tvars T \<union> ttvars (Var w B) \<subseteq> tvars_env (tyenv env) \<union> A" using tv by auto
      have cls: "closed (Var w B)" by (simp add: closed_def)
      have fls: "flexb e0 (Var w B)" using w(3) by (simp add: flexb_Var)
      from ur_update[where s = "Var w B" and FT = T, OF fv v(1,2) acy cls tvs fls] obtain env' where
        "update (v, T) (Var w B) env = return env'" "finv A K e0 env'"
        by blast
      with vu vu' show ?thesis by auto
    qed
  qed
qed

text \<open>One pair:\<close>

lemma smash_flexflex1_term:
  assumes fv: "finv A K e0 env" and wi: "winv env Y" and p: "pok A env [] Y t u"
    and ft: "flexb e0 t" and fu: "flexb e0 u"
  shows "\<exists>env'. okW (smash_flexflex1 (t, u) env) env' \<and> finv A K e0 env'"
proof -
  have ei: "einv A K env" and fi: "iflex e0 env" and ext0: "extends e0 env"
    using fv by (simp_all add: finv_def)
  note e = einvD[OF ei] and pd = pokD[OF p] and r0 = einv_rho0[OF ei]
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A" and ?\<rho> = "rho0 env"
  from pd(9)[OF r0] obtain e T0 where tyt0: "e \<turnstile> inst ?\<rho> t : T0" and tyu0: "e \<turnstile> inst ?\<rho> u : T0" by auto
  have wv: "wt_env ?\<rho> env" "vinv ?\<rho> env Y" using winvD[OF wi r0] by blast+
  have vk: "vok env (Y \<union> evars env)" by (rule vok_winv[OF ei wi pd(6)])
  have vc: "vcons ?\<rho> (Y \<union> evars env)" using wv(2) by (simp add: vinv_def)
  text \<open>Normalization of both sides:\<close>
  have nterm: "\<exists>s'. norm_term env s = return s' \<and> npost A env s' \<and> hnorm env s' \<and> flexb e0 s'"
    if vs: "vars s \<subseteq> Y \<union> evars env" and ts: "ttvars s \<subseteq> ?KN" and tys: "e \<turnstile> inst ?\<rho> s : T0"
      and fs: "flexb e0 s" for s
  proof -
    have vks: "vok env (vars s \<union> evars env)" using vk vs by (auto intro: vok_mono)
    have vcs: "vcons ?\<rho> (vars s \<union> evars env)" by (rule vcons_mono[OF vc]) (use vs in blast)
    from norm_term_term[OF ei vks ts wv(1) vcs tys] obtain s' where
      ns: "norm_term env s = return s'" "npost A env s'" by blast
    have "hnorm env s'" by (rule norm_term_hnorm[OF ns(1)[unfolded return_def] ei ts])
    moreover have "flexb e0 s'" by (rule norm_term_flex[OF ns(1)[unfolded return_def] fi fs])
    ultimately show ?thesis using ns by blast
  qed
  from nterm[OF pd(1) pd(3) tyt0 ft] obtain t' where nt: "norm_term env t = return t'" "npost A env t'"
    "hnorm env t'" "flexb e0 t'" by blast
  from nterm[OF pd(2) pd(4) tyu0 fu] obtain u' where nu: "norm_term env u = return u'" "npost A env u'"
    "hnorm env u'" "flexb e0 u'" by blast
  from flexb_strip_abs_body[OF nt(4)] obtain v T where ht: "head_of (strip_abs_body t') = Var v T"
    and v0: "vt_lookup (tenv e0) v = None" by blast
  from flexb_strip_abs_body[OF nu(4)] obtain w U where hu: "head_of (strip_abs_body u') = Var w U"
    and w0: "vt_lookup (tenv e0) w = None" by blast
  have vu: "vt_lookup (tenv env) v = None" "tnorm ?\<theta> T = T" using nt(3) ht by (simp_all add: hnorm_def)
  have wu: "vt_lookup (tenv env) w = None" "tnorm ?\<theta> U = U" using nu(3) hu by (simp_all add: hnorm_def)
  have ttu: "ttvars t' \<subseteq> ?KN" "ttvars u' \<subseteq> ?KN" using nt(2) nu(2) by (simp_all add: npost_def)
  have vT: "(v, T) \<in> vars t'" by (rule vars_flex[OF ht])
  have wU: "(w, U) \<in> vars u'" by (rule vars_flex[OF hu])
  have tvT: "tvars T \<subseteq> ?KN" using vT ttu(1) vtvars_vars[of t'] by (auto simp: vtvars_def)
  have tvU: "tvars U \<subseteq> ?KN" using wU ttu(2) vtvars_vars[of u'] by (auto simp: vtvars_def)
  have vh: "var_head_of env t = returnW (v, T)"
    by (simp add: var_head_of_def nt(1) ht liftM_def return_def bindW_def returnW_def)
  have wh: "var_head_of env u = returnW (w, U)"
    by (simp add: var_head_of_def nu(1) hu liftM_def return_def bindW_def returnW_def)
  text \<open>The heads have the same type if they are the same variable, and are below the maximal index:\<close>
  define Y' where "Y' = Y \<union> vars t' \<union> vars u'"
  have ds: "dstep env [([], t, u)] env [([], t', u')]"
    by (rule norm_term_dstep[OF nt(1)[unfolded return_def] nu(1)[unfolded return_def]])
  from dstep_pok[OF ds wi p ei refl] ttu have wi': "winv env Y'" by (auto simp: Y'_def btvars_def)
  have vi': "vinv ?\<rho> env Y'" using winvD[OF wi' r0] by blast
  have vY: "(v, T) \<in> Y' \<union> evars env" "(w, U) \<in> Y' \<union> evars env" using vT wU by (auto simp: Y'_def)
  have TU: "T = U" if "v = w"
  proof -
    have "vcons ?\<rho> (Y' \<union> evars env)" using vi' by (simp add: vinv_def)
    with vY that have "tsubst ?\<rho> T = tsubst ?\<rho> U" using vconsD by blast
    with vu(2) wu(2) show ?thesis by simp
  qed
  have bl: "snd v \<le> maxidx env" "snd w \<le> maxidx env"
    using vi' belowD[OF _ vY(1)] belowD[OF _ vY(2)] by (simp_all add: vinv_def)
  text \<open>The new variable:\<close>
  from body_type_term[OF e(2) refl tvT] obtain B where bB: "body_type env T = return B" "tvars B \<subseteq> ?KN"
    by blast
  obtain env1 var where g: "genvar (fst v) env B = (env1, var)" by force
  note gs = genvar_simps[OF g]
  define x where "x = (fst v, maxidx env + 1)"
  have var: "var = Var x B" using gs(4) by (simp add: x_def)
  have ei1: "einv A K env1" by (rule einv_genvar[OF g ei])
  have fv1: "finv A K e0 env1"
    using fv ei1 gs(1,2) extends_trans[OF ext0 extends_genvar[OF g]] by (simp add: finv_def iflex_def)
  have x1: "vt_lookup (tenv env1) x = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env1) x \<noteq> None"
    then obtain b where "vt_lookup (tenv env) x = Some b" using gs(1) by auto
    with e(5) have "snd x \<le> maxidx env" unfolding bbelow_def by blast
    then show False by (simp add: x_def)
  qed
  have x0: "vt_lookup (tenv e0) x = None" by (rule ff_unbound_extends[OF ext0 x1[unfolded gs(1)]])
  have xne: "v \<noteq> x" "w \<noteq> x" using bl by (auto simp: x_def prod_eq_iff)
  have tvT1: "tvars T \<subseteq> tvars_env (tyenv env1) \<union> A" and tvU1: "tvars U \<subseteq> tvars_env (tyenv env1) \<union> A"
    using tvT tvU gs(2) by simp_all
  from binder_types_tvars[OF einvD(2)[OF ei1] refl tvU1] obtain Us where
    bU: "binder_types env1 U = return Us" "\<forall>T'\<in>set Us. tvars T' \<subseteq> tvars_env (tyenv env1) \<union> A" by blast
  from binder_types_tvars[OF einvD(2)[OF ei1] refl tvT1] obtain Ts where
    bT: "binder_types env1 T = return Ts" "\<forall>T'\<in>set Ts. tvars T' \<subseteq> tvars_env (tyenv env1) \<union> A" by blast
  have taU: "type_abs env1 U var = return (types_abs Us var)" by (simp add: type_abs_def bU(1) return_def bindM_def)
  have taT: "type_abs env1 T var = return (types_abs Ts var)" by (simp add: type_abs_def bT(1) return_def bindM_def)
  text \<open>The binding of \<open>?w\<close>, or of \<open>?x\<close> to \<open>?w\<close>:\<close>
  have w1: "vt_lookup (tenv env1) w = None" using wu(1) gs(1) by simp
  have mx1: "maxidx env1 = maxidx env + 1" by (rule gs(3))
  from ur_vupdate_fresh[OF fv1 w1 _ xne(2) w0 x1, of U B Us] bl(2) mx1 bU(2) tvU1 bB(2) gs(2)
  obtain env2 where u1: "vupdate (w, U) (types_abs Us (Var x B)) env1 = return env2" and fv2: "finv A K e0 env2"
    and ty2: "tyenv env2 = tyenv env1" and mx2: "maxidx env2 = maxidx env1"
    and c1: "Us \<noteq> [] \<or> \<not> indexname_less w x \<Longrightarrow> tenv env2 = vt_update (w, (U, types_abs Us (Var x B))) (tenv env1)"
    and c2: "Us = [] \<Longrightarrow> indexname_less w x \<Longrightarrow> tenv env2 = vt_update (x, (B, Var w B)) (tenv env1)"
    by (auto simp: x_def)
  text \<open>The binding of \<open>?v\<close>:\<close>
  have tvT2: "tvars T \<union> tvars B \<union> (\<Union>P\<in>set Ts. tvars P) \<subseteq> tvars_env (tyenv env2) \<union> A"
    using tvT bB(2) bT(2) ty2 gs(2) by auto
  have bv2: "snd v \<le> maxidx env2" and bw2: "snd w \<le> maxidx env2" using bl mx2 mx1 by simp_all
  have u2: "\<exists>env'. vupdate (v, T) (types_abs Ts (Var x B)) env2 = return env' \<and> finv A K e0 env'"
    if vw: "v \<noteq> w"
  proof (cases "Us \<noteq> [] \<or> \<not> indexname_less w x")
    case True
    have v2: "vt_lookup (tenv env2) v = None" and x2: "vt_lookup (tenv env2) x = None"
      using c1[OF True] vu(1) gs(1) vw x1 xne by simp_all
    have bx2: "snd x \<le> maxidx env2" using mx2 mx1 by (simp add: x_def)
    from ur_vupdate_fresh[OF fv2 v2 bv2 xne(1) v0 x2 bx2 tvT2] show ?thesis by blast
  next
    case False
    then have c: "tenv env2 = vt_update (x, (B, Var w B)) (tenv env1)" using c2 by auto
    have lx: "vt_lookup (tenv env2) x = Some (B, Var w B)" using c by simp
    have v2: "vt_lookup (tenv env2) v = None" and w2: "vt_lookup (tenv env2) w = None"
      using c vu(1) wu(1) gs(1) xne by simp_all
    from ur_vupdate_chain[OF fv2 lx v2 bv2 v0 w2 bw2 w0 x0 xne(1) vw tvT2] show ?thesis .
  qed
  have "\<exists>env'. (v = w \<and> T = U \<longrightarrow> env' = env2) \<and>
      (\<not> (v = w \<and> T = U) \<longrightarrow> vupdate (v, T) (types_abs Ts (Var x B)) env2 = return env') \<and> finv A K e0 env'"
  proof (cases "v = w")
    case True
    with TU fv2 show ?thesis by auto
  next
    case False
    with u2 show ?thesis by auto
  qed
  then obtain env' where r: "v = w \<and> T = U \<Longrightarrow> env' = env2"
    "\<not> (v = w \<and> T = U) \<Longrightarrow> vupdate (v, T) (types_abs Ts (Var x B)) env2 = return env'" "finv A K e0 env'"
    by blast
  have "okW (smash_flexflex1 (t, u) env) env'"
  proof (cases "v = w \<and> T = U")
    case True
    show ?thesis
      by (simp add: smash_flexflex1_def vh wh bB(1) g taU u1[folded var] return_def if_P[OF True] r(1)[OF True])
  next
    case False
    show ?thesis
      by (simp add: smash_flexflex1_def vh wh bB(1) g taU taT u1[folded var] r(2)[OF False, folded var] return_def
          if_not_P[OF False])
  qed
  with r(3) show ?thesis by blast
qed

text \<open>All pairs:\<close>

lemma foldrW_smash_flexflex1_term:
  assumes ff: "ffres A K X env tps" and fl: "fflex A K e0 env tps"
  shows "\<exists>env'. okW (foldrW smash_flexflex1 tps env) env' \<and> finv A K e0 env'"
proof -
  note h = ffres_smash[OF ff]
  have wi: "winv env X" and pk: "\<forall>(t, u)\<in>set tps. pok A env [] X t u" using ff by (simp_all add: ffres_def)
  have fv: "finv A K e0 env" and ft: "\<forall>(t, u)\<in>set tps. flexb e0 t \<and> flexb e0 u"
    using fl by (simp_all add: fflex_def)
  have "\<exists>env'. okW (foldrW smash_flexflex1 xs env) env' \<and> finv A K e0 env'" if "set xs \<subseteq> set tps" for xs
    using that
  proof (induction xs)
    case Nil
    with fv show ?case by simp
  next
    case (Cons tu xs)
    obtain t u where tu: "tu = (t, u)" by force
    from Cons obtain env1 where f1: "okW (foldrW smash_flexflex1 xs env) env1" and fv1: "finv A K e0 env1"
      by auto
    have gt: "gtyped env (tdps xs)" by (rule gtyped_mono[OF h(4)]) (use Cons.prems in auto)
    from foldrW_smash_flexflex1_sound[OF f1 h(1,2) gt h(3)]
    have ds: "dstep env (tdps xs) env1 []" and th: "tyenv env1 = tyenv env" by simp_all
    have pk1: "\<forall>(rb, t, u)\<in>set (tdps xs). pok A env rb X t u" using pk Cons.prems by auto
    have wi1: "winv env1 X" using dstep_winv(1)[OF ds wi pk1 th] by (simp add: dvars_def)
    have tui: "(t, u) \<in> set tps" using Cons.prems tu by simp
    have p1: "pok A env1 [] X t u" using pok_mono[OF _ dstepD(1)[OF ds]] pk tui th by fastforce
    from smash_flexflex1_term[OF fv1 wi1 p1] ft tui obtain env2 where
      "okW (smash_flexflex1 (t, u) env1) env2" "finv A K e0 env2" by blast
    with f1 tu show ?case by auto
  qed
  from this[OF order_refl] show ?thesis .
qed

theorem smash_flexflex_term:
  assumes ff: "ffres A K X env tps" and fl: "fflex A K e0 env tps"
  obtains env' where "okW (smash_flexflex (env, tps)) env'" "dstep env (tdps tps) env' []" "finv A K e0 env'"
    "winv env' X" "tyenv env' = tyenv env"
proof -
  from foldrW_smash_flexflex1_term[OF ff fl] obtain env' where
    f: "okW (foldrW smash_flexflex1 tps env) env'" and fv: "finv A K e0 env'" by blast
  note h = ffres_smash[OF ff]
  from foldrW_smash_flexflex1_sound[OF f h(1,2,4,3)] have ds: "dstep env (tdps tps) env' []"
    and th: "tyenv env' = tyenv env" by simp_all
  have wi: "winv env X" and pk: "\<forall>(rb, t, u)\<in>set (tdps tps). pok A env rb X t u"
    using ff by (auto simp: ffres_def)
  have "winv env' X" using dstep_winv(1)[OF ds wi pk th] by (simp add: dvars_def)
  with f ds fv th show ?thesis using that by (simp add: smash_flexflex_def)
qed

text \<open>
  Hence smashing the flex-flex pairs of a unifier of the enumeration terminates normally, with a
  unifier of the input without flex-flex pairs, in the invariant again:
\<close>

theorem unifiers_smash:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
  obtains env'' where "okW (smash_flexflex (env', tps)) env''" "dstep env (tdps tus) env'' []"
    "tyenv env'' = tyenv env'" "\<exists>A' K' X'. finite X' \<and> finite K' \<and> A \<subseteq> A' \<and> ffres A' K' X' env'' []"
proof -
  note r = unifiers_uresult[OF cfg fin si u es x]
  from uresultD(3)[OF r] obtain A' K' X' e0 where fin': "finite X'" "finite K'" and A': "A \<subseteq> A'"
    and ff: "ffres A' K' X' env' tps" and fl: "fflex A' K' e0 env' tps" by blast
  from smash_flexflex_term[OF ff fl] obtain env'' where sm: "okW (smash_flexflex (env', tps)) env''"
    and ds: "dstep env' (tdps tps) env'' []" and fv: "finv A' K' e0 env''" and wi: "winv env'' X'"
    and th: "tyenv env'' = tyenv env'" by blast
  have "dstep env (tdps tus) env'' []" by (rule dstep_trans[OF uresultD(1)[OF r] ds])
  moreover have "ffres A' K' X' env'' []" using fv wi by (simp add: ffres_def finv_def)
  ultimately show thesis using that sm th fin' A' by blast
qed

text \<open>The hypotheses of @{thm [source] unifiers_smash_sound} hold on well-formed problems:\<close>

corollary unifiers_smash_ok:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and sm: "okW (smash_flexflex (env', tps)) env''"
  shows "dstep env (tdps tus) env'' []"
proof -
  from uresultD(3)[OF unifiers_uresult[OF cfg fin si u es x]] obtain A' K' X' where
    ff: "ffres A' K' X' env' tps" by blast
  note h = ffres_smash[OF ff]
  show ?thesis by (rule unifiers_smash_sound[OF cfg fin si u es x sm sinv_gtyped[OF si] h(1-3)])
qed


subsection \<open>Further terms of the input\<close>

text \<open>
  Terms \<open>rs\<close> with types that are well-typed at the certified solutions of the type environment of
  the input stay well-typed, and their variables stay consistent with the environment and the
  flex-flex pairs of the unifiers.
\<close>

definition rtyped :: "env \<Rightarrow> (pterm \<times> ptyp) list \<Rightarrow> bool" where
  "rtyped env rs \<longleftrightarrow>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<forall>(r, T)\<in>set rs. \<forall>e. e \<turnstile> inst \<rho> r : tsubst \<rho> T))"

definition rvars :: "(pterm \<times> ptyp) list \<Rightarrow> (indexname \<times> ptyp) set" where
  "rvars rs = (\<Union>(r, T)\<in>set rs. vars r)"

lemma rtyped_extends: "rtyped env rs \<Longrightarrow> extends env env' \<Longrightarrow> rtyped env' rs"
  unfolding rtyped_def using extends_tsol by blast

theorem unifiers_winv:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and wy: "winv env (Y \<union> dvars (tdps tus))"
  shows "winv env' (Y \<union> dvars (tdps tps))"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume t': "tsol (tyenv env') \<rho>" and c: "cert_inst \<rho>"
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF unifiers_uresult[OF cfg fin si u es x]])
  have t: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t' dstepD(1)[OF ds]])
  from winvD[OF wy t c] have w: "wt_env \<rho> env" "vinv \<rho> env (Y \<union> dvars (tdps tus))" by blast+
  from dstepD(2)[OF ds t' extends_refl w(1) sinv_dtyped[OF si t c] w(2)]
  show "wt_env \<rho> env' \<and> vinv \<rho> env' (Y \<union> dvars (tdps tps))" by blast
qed

theorem unifiers_rs:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and rt: "rtyped env rs" and rv: "rvars rs \<subseteq> X \<union> evars env"
  shows "rtyped env' rs" "winv env' (rvars rs \<union> dvars (tdps tps))"
proof -
  show "rtyped env' rs"
    by (rule rtyped_extends[OF rt uresultD(2)[OF unifiers_uresult[OF cfg fin si u es x]]])
  have "winv env (rvars rs \<union> dvars (tdps tus))"
    by (rule ur_winv_sub[of _ X]) (use si sinv_dvars[OF si] rv in \<open>auto simp: sinv_def\<close>)
  from unifiers_winv[OF cfg fin si u es x this] show "winv env' (rvars rs \<union> dvars (tdps tps))" .
qed


subsection \<open>Fresh variables and the maximal index\<close>

lemma ur_fun_type_neq: "T \<rightarrow>\<^sub>T T \<noteq> T"
proof
  assume "T \<rightarrow>\<^sub>T T = T"
  then have "size (T \<rightarrow>\<^sub>T T) = size T" by simp
  then show False by simp
qed

lemma ur_vinv_fresh:
  assumes "vinv \<rho> env D" "v \<notin> fst ` (D \<union> evars env)" "snd v \<le> maxidx env"
  shows "vinv \<rho> env ({(v, T)} \<union> D)"
proof -
  have vc: "vcons \<rho> (D \<union> evars env)" and bl: "below (maxidx env) (D \<union> evars env)"
    using assms(1) by (simp_all add: vinv_def)
  have "vcons \<rho> ({(v, T)} \<union> D \<union> evars env)"
    unfolding vcons_def
  proof (intro allI impI)
    fix x T1 T2 assume 1: "(x, T1) \<in> {(v, T)} \<union> D \<union> evars env" and 2: "(x, T2) \<in> {(v, T)} \<union> D \<union> evars env"
    show "tsubst \<rho> T1 = tsubst \<rho> T2"
    proof (cases "x = v")
      case True
      then have "(x, T1) \<notin> D \<union> evars env" "(x, T2) \<notin> D \<union> evars env" using assms(2) by force+
      with 1 2 show ?thesis by simp
    next
      case False
      with 1 2 have "(x, T1) \<in> D \<union> evars env" "(x, T2) \<in> D \<union> evars env" by auto
      from vconsD[OF vc this] show ?thesis .
    qed
  qed
  moreover have "below (maxidx env) ({(v, T)} \<union> D \<union> evars env)"
    using bl assms(3) by (simp add: below_def)
  ultimately show ?thesis by (simp add: vinv_def)
qed

text \<open>
  A variable that occurs neither in the problem nor in the environment, with an index that is
  not above the maximal index, is not bound by the unifiers and does not occur in their
  bindings and flex-flex pairs: it can be given any type in the problem, so its type would be
  inconsistent with a binding or an occurrence (\<^const>\<open>vinv\<close>).
\<close>

theorem unifiers_fresh:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and v: "v \<notin> fst ` (evars env \<union> dvars (tdps tus))" "snd v \<le> maxidx env"
  shows "v \<notin> fst ` (evars env' \<union> dvars (tdps tps))"
proof
  assume vin: "v \<in> fst ` (evars env' \<union> dvars (tdps tps))"
  note r = unifiers_uresult[OF cfg fin si u es x]
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF r])
  from uresultD(3)[OF r] obtain A' K' X' where "ffres A' K' X' env' tps" by blast
  then have ei': "einv A' K' env'" by (simp add: ffres_def)
  let ?\<rho> = "tnorm_inst (tyenv env')"
  note r0 = einv_rho0[OF ei']
  have t: "tsol (tyenv env) ?\<rho>" by (rule extends_tsol[OF r0(1) dstepD(1)[OF ds]])
  from sinv_gtyped[OF si] t r0(2) have w: "wt_env ?\<rho> env" "dtyped ?\<rho> (tdps tus)" "vinv ?\<rho> env (dvars (tdps tus))"
    unfolding gtyped_def by blast+
  have vT: "vinv ?\<rho> env' ({(v, T)} \<union> dvars (tdps tps))" for T
  proof -
    have "vinv ?\<rho> env ({(v, T)} \<union> dvars (tdps tus))" by (rule ur_vinv_fresh[OF w(3)]) (use v in auto)
    from dstepD(2)[OF ds r0(1) extends_refl w(1,2) this] show ?thesis by blast
  qed
  from vin obtain U where U: "(v, U) \<in> evars env' \<union> dvars (tdps tps)" by force
  have "vcons ?\<rho> ({(v, U \<rightarrow>\<^sub>T U)} \<union> dvars (tdps tps) \<union> evars env')"
    using vT[of "U \<rightarrow>\<^sub>T U"] by (simp add: vinv_def)
  from vconsD[OF this, of v "U \<rightarrow>\<^sub>T U" U] U have "tsubst ?\<rho> (U \<rightarrow>\<^sub>T U) = tsubst ?\<rho> U" by blast
  with ur_fun_type_neq[of "tsubst ?\<rho> U"] show False by simp
qed

corollary unifiers_fresh_unbound:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and v: "v \<notin> fst ` (evars env \<union> dvars (tdps tus))" "snd v \<le> maxidx env"
  shows "vt_lookup (tenv env') v = None" "\<forall>(t, u)\<in>set tps. v \<notin> fst ` (vars t \<union> vars u)"
proof -
  note f = unifiers_fresh[OF cfg fin si u es x v]
  show "vt_lookup (tenv env') v = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env') v \<noteq> None"
    then obtain U b where "vt_lookup (tenv env') v = Some (U, b)" by force
    from evarsI[OF this] f show False by force
  qed
  show "\<forall>(t, u)\<in>set tps. v \<notin> fst ` (vars t \<union> vars u)"
    using f by (force simp: dvars_def)
qed

text \<open>The maximal index of the unifiers is at least that of the problem (by soundness):\<close>

theorem unifiers_maxidx:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg' env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
  shows "maxidx env \<le> maxidx env'"
  using unifiers_sound[OF cfg fin si u es x] dstepD(1) extends_maxidx by blast

subsection \<open>Fresh type variables\<close>

text \<open>
  The type environment of a result contains only type variables of the problem (those of \<open>A\<close> and
  of its type environment) and new ones, with indices above the maximal index of the problem
  (by the invariant \<^const>\<open>tnew\<close> of the steps):
\<close>

theorem unifiers_tvars:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
  shows "tvars_env (tyenv env') \<subseteq> tvars_env (tyenv env) \<union> A \<union> {p. maxidx env < snd (fst p)}"
proof -
  from uresultD(3)[OF unifiers_uresult[OF cfg fin si u es x]] obtain A' where "tnew A env A' env'" by blast
  then show ?thesis by (rule tnewD)
qed

text \<open>
  Hence it contains no type variable whose name is not among the type variables of the problem and
  of its type environment, with an index that is not above the maximal index:
\<close>

corollary unifiers_fresh_tvar:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and w: "w \<notin> fst ` (A \<union> tvars_env (tyenv env))" "snd w \<le> maxidx env"
  shows "w \<notin> fst ` tvars_env (tyenv env')"
proof
  assume "w \<in> fst ` tvars_env (tyenv env')"
  then obtain S where "(w, S) \<in> tvars_env (tyenv env')" by force
  with unifiers_tvars[OF cfg fin si u es x] have "(w, S) \<in> tvars_env (tyenv env) \<union> A \<or> maxidx env < snd w"
    by auto
  with w show False by force
qed

text \<open>Smashing the flex-flex pairs keeps the type environment, hence the same holds after smashing:\<close>

corollary unifiers_smash_tvars:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and sm: "okW (smash_flexflex (env', tps)) env''"
  shows "tvars_env (tyenv env'') \<subseteq> tvars_env (tyenv env) \<union> A \<union> {p. maxidx env < snd (fst p)}"
proof -
  from unifiers_smash[OF cfg fin si u es x] obtain e where "okW (smash_flexflex (env', tps)) e"
    "tyenv e = tyenv env'" by blast
  with sm have "tyenv env'' = tyenv env'" by auto
  with unifiers_tvars[OF cfg fin si u es x] show ?thesis by simp
qed

end

end
