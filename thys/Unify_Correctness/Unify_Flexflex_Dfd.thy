section \<open>Termination of the Treatment of Flex-Flex Pairs with Names at Two Types\<close>

theory Unify_Flexflex_Dfd
  imports Unify_Simpl_Dfd Unify_Flexflex_Term
begin

text \<open>
  The counterpart of theory \<^theory>\<open>Unify_Correctness.Unify_Flexflex_Term\<close> without a
  hypothesis on the names: the measures use \<open>unfc\<close>, and the computations may in addition raise
  the exception of \<^const>\<open>var_clash\<close>.
\<close>

context pure_sig_gen
begin

subsection \<open>Definedness with a postcondition\<close>

definition dfdp :: "'a M \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "dfdp m P \<longleftrightarrow> dfd m \<and> (\<forall>x. m = return x \<longrightarrow> P x)"

lemma dfdp_return [simp]: "dfdp (return x) P \<longleftrightarrow> P x"
  by (auto simp: dfdp_def return_def)

lemma dfdp_Ok [simp]: "dfdp (Some (Ok x)) P \<longleftrightarrow> P x"
  by (auto simp: dfdp_def return_def)

lemma dfdp_var_clash: "x \<in> loose \<Longrightarrow> dfdp (var_clash x T U) P"
  by (auto simp: dfdp_def var_clash_def raise_def return_def clashx_def)

lemma dfdp_dfd: "dfdp m P \<Longrightarrow> dfd m"
  by (simp add: dfdp_def)

lemma dfdp_ok: "dfdp m P \<Longrightarrow> m = return x \<Longrightarrow> P x"
  by (simp add: dfdp_def)

lemma dfdp_mono: "dfdp m P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> dfdp m Q"
  by (simp add: dfdp_def)

lemma dfdp_bindM:
  assumes "dfdp m P" "\<And>x. m = return x \<Longrightarrow> P x \<Longrightarrow> dfdp (f x) Q"
  shows "dfdp (bindM m f) Q"
proof (rule dfd_cases[OF dfdp_dfd[OF assms(1)]])
  fix e assume "m = Some (Err e)" "clashx e"
  then show ?thesis by (simp add: dfdp_def bindM_def return_def)
next
  fix x assume m: "m = Some (Ok x)"
  then have "dfdp (f x) Q" using assms dfdp_ok[OF assms(1)] by (simp add: return_def)
  with m show ?thesis by (simp add: bindM_def)
qed

lemma dfdp_cases:
  assumes "dfdp m P"
  obtains (err) e where "m = Some (Err e)" "clashx e" | (ok) x where "m = return x" "P x"
  using assms by (auto simp: dfdp_def return_def elim: dfd_cases)

lemma cxokE_liftM_dfdp: "dfdp m P \<Longrightarrow> cxokE Xe (liftM m) P"
  by (rule cxokE_liftM) (simp_all add: dfdp_def)

subsection \<open>Normalization\<close>

lemma norm_term1_unfc:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> acyc env \<Longrightarrow> closed_env env \<Longrightarrow>
    unfc env t \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and em = "1.prems"(3)
    and ac = "1.prems"(4) and cl = "1.prems"(5)
  have IH: "unfc env u \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env u'" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te em ac cl] .
  have redex: "unfc env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env t'" if "ok (nt te (subst_bound u body)) t'" for b U0 body u
  proof -
    have "unfc env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta> unfc env (body[u/0])"
      by (simp add: unfc_subst[OF ac cl])
    with IH[OF that[unfolded subst_bound_subst]] show ?thesis by (simp add: converse_rtranclp_into_rtranclp)
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      with ok_lookup1[OF lr] te have lk: "vt_lookup (tenv env) x = Some (T, u)" by simp
      have "ok (unified (tyenv env) T T) True" using em by (simp add: unified_def return_def)
      with IH[of u t'] rest Some Var lk show ?thesis by (simp add: unfc_Var_bound[OF ac])
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH Abs show ?thesis by (simp add: rtrancl_beta_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      have fu: "unfc env (f $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env (nf $ u)" using IH[OF hf] by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        from rtranclp_trans[OF fu[unfolded nf] redex[OF this]] App show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt te u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from rtrancl_beta_App[OF IH[OF hf] IH[OF hu]] App t' show ?thesis by simp
      qed
    qed
  qed (use h in auto)
qed

lemma norm_term2_unfc:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> acyc env \<Longrightarrow> closed_env env \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow>
    inst \<rho> (unfc env t) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unfc env t')"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2) and cl = "1.prems"(3) and tsol = "1.prems"(4)
  have IH: "inst \<rho> (unfc env u) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unfc env u')" if "ok (nt env u) u'" for u u'
    using "1.IH"[OF that refl ac cl tsol] .
  have nty: "tsubst \<rho> T' = tsubst \<rho> T" if "ok (norm_type_aux (tyenv env) T) T'" for T T'
    using norm_type_aux_sound[OF that refl tsol] .
  have redex: "inst \<rho> (unfc env (Abs b U0 body $ u)) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unfc env t')"
    if "ok (nt env (subst_bound u body)) t'" for b U0 body u
  proof -
    have "inst \<rho> (unfc env (Abs b U0 body $ u)) \<rightarrow>\<^sub>\<beta> inst \<rho> (unfc env (body[u/0]))"
      using inst_beta[of \<rho> b U0 "unfc env body" "unfc env u"] by (simp add: unfc_subst[OF ac cl])
    with IH[OF that[unfolded subst_bound_subst]] show ?thesis by (simp add: converse_rtranclp_into_rtranclp)
  qed
  show ?case
  proof (cases t)
    case (Const a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Const a T'" by auto
    with nty[OF this(1)] Const show ?thesis by simp
  next
    case (Free a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Free a T'" by auto
    with nty[OF this(1)] Free show ?thesis by simp
  next
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      from lr Some obtain U where lk: "vt_lookup (tenv env) x = Some (U, u)" "ok (unified (tyenv env) T U) True"
        by (auto elim: ok_lookup_Some_unified)
      from rest Some have "ok (nt env u) t'" by simp
      with IH[OF this] lk Var show ?thesis by (simp add: unfc_Var_bound[OF ac])
    next
      case None
      with ok_lookup_None lr have lk: "vt_lookup (tenv env) x = None" by blast
      from rest None obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Var x T'" by auto
      with nty[OF this(1)] lk Var show ?thesis by (simp add: unfc_Var[OF ac])
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (norm_type_aux (tyenv env) T) T'" "ok (nt env body) body'"
      "t' = Abs a T' body'" by auto
    with nty[OF this(1)] IH[OF this(2)] Abs show ?thesis by (simp add: rtrancl_beta_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      have fu: "inst \<rho> (unfc env (f $ u)) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unfc env (nf $ u))"
        using IH[OF hf] by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        from rtranclp_trans[OF fu[unfolded nf] redex[OF this]] App show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from rtrancl_beta_App[OF IH[OF hf] IH[OF hu]] App t' show ?thesis by simp
      qed
    qed
  qed (use h in auto)
qed


definition npostc :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> bool" where
  "npostc A env t' \<longleftrightarrow> tok env (vars t' \<union> evars env) \<and> ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    (\<forall>x T. head_of t' = Var x T \<longrightarrow> vt_lookup (tenv env) x = None \<and> tnorm (tyenv env) T = T)"

lemma tok_Un: "tok env (X \<union> Y) \<longleftrightarrow> tok env X \<and> tok env Y"
  unfolding tok_def ball_Un by (rule refl)

lemma tok_App: "tok env (vars (f $ u) \<union> evars env) \<longleftrightarrow> tok env (vars f \<union> evars env) \<and> tok env (vars u \<union> evars env)"
  by (auto simp: tok_Un)

lemma tok_Var: "tok env (evars env) \<Longrightarrow> tcons (tyenv env) T \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
    tok env (vars (Var x T) \<union> evars env)"
  unfolding tok_def by auto

lemma tok_bnd: "tok env (evars env) \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tok env (vars u \<union> evars env)"
  using evarsI2[of env x U u] by (auto intro: tok_mono)

lemma lookup1_def_tok:
  assumes "vt_is_empty (tyenv env)"
  shows "lookup1 (tenv env) x T = (case vt_lookup (tenv env) x of None \<Rightarrow> return None
    | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash x T U)"
  by (simp add: lookup1_def tnorm_empty[OF assms] split: option.splits)

context
  fixes A K env assumes ei: "einv A K env"
begin

lemma norm_term2_dfd:
  "tok env (vars t \<union> evars env) \<Longrightarrow> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    termip (sup beta subt) (inst (rho0 env) (unfc env t)) \<Longrightarrow>
    dfdp (norm_term2 env t) (npostc A env)"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (inst (rho0 env) (unfc env t), hrk env t)"]])
  case (1 t)
  note e = einvD[OF ei]
  let ?M = "\<lambda>t. inst (rho0 env) (unfc env t)"
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have sn: "termip (sup beta subt) u" if "(sup beta subt)\<^sup>*\<^sup>* (?M t) u" for u
    by (rule termip_sup_reds[OF that "1.prems"(3)])
  have IH: "dfdp (norm_term2 env u) (npostc A env)"
    if "tok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M u)" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    have "(?M u, ?M t) \<in> sn_less"
      by (simp only: sn_less_def mem_Collect_eq case_prod_conv) (use that(3) "1.prems"(3) in blast)
    then show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (?M t, hrk env t))"
      by simp
    show "termip (sup beta subt) (?M u)" by (rule sn[OF tranclp_into_rtranclp[OF that(3)]])
  qed
  have IH': "dfdp (norm_term2 env u) (npostc A env)"
    if "tok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "?M u = ?M t" "hrk env u < hrk env t" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (?M t, hrk env t))"
      using that(3,4) by simp
    show "termip (sup beta subt) (?M u)" by (subst that(3)) (rule "1.prems"(3))
  qed
  have ve: "tok env (evars env)" using "1.prems"(1) by (rule tok_mono) blast
  have redex: "dfdp (norm_term2 env (subst_bound u body)) (npostc A env)"
    if "(sup beta subt)\<^sup>*\<^sup>* (?M t) (?M (Abs b U body $ u))" "tok env (vars body \<union> vars u \<union> evars env)"
      "ttvars body \<union> ttvars u \<subseteq> ?KN"
    for b U body u
  proof (subst subst_bound_subst, rule IH)
    have r: "?M (Abs b U body $ u) \<rightarrow>\<^sub>\<beta> ?M (body[u/0])"
      using inst_beta[of "rho0 env" b U "unfc env body" "unfc env u"] by (simp add: unfc_subst[OF e(3,4)])
    then show "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M (body[u/0]))"
      using that(1) by (meson rtranclp_into_tranclp1 sup2I1)
    show "tok env (vars (body[u/0]) \<union> evars env)"
      using tok_mono[OF that(2)] vars_subst[of body u 0] by blast
    show "ttvars (body[u/0]) \<subseteq> ?KN" using ttvars_subst[of body u 0] that(3) by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    have lk: "lookup env x T = (case vt_lookup (tenv env) x of None \<Rightarrow> return None
      | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash x T U)"
      by (rule lookup_def_tok[OF e(6,7) tok_mono[OF "1.prems"(1)]]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      show ?thesis
      proof (cases "tnorm (tyenv env) T = tnorm (tyenv env) U")
        case True
        have tcU: "tcons (tyenv env) T" "tcons (tyenv env) U"
        proof -
          have "(x, U) \<in> evars env" using evarsI[OF Some[unfolded p]] .
          then show "tcons (tyenv env) T" "tcons (tyenv env) U" using "1.prems"(1) Var by (auto simp: tok_def)
        qed
        have ue: "ok (unified (tyenv env) T U) True"
          using unified_ok[OF e(6,7) tcU] True by (simp add: return_def)
        have u: "?M u = ?M t" using Some p Var ue by (simp add: unfc_Var_bound[OF e(3)])
        have "hrk env u < hrk env t" using ff_hrk_less[OF ei Some[unfolded p]] Var by simp
        moreover have "tok env (vars u \<union> evars env)" by (rule tok_bnd[OF ve Some[unfolded p]])
        moreover have "ttvars u \<subseteq> ?KN" using tvinvD(2)[OF e(1) Some[unfolded p]] by blast
        ultimately have "dfdp (norm_term2 env u) (npostc A env)" using IH'[of u] u by blast
        then show ?thesis using lk Var Some p True by (subst norm_term2.simps) (simp add: bindM_def return_def)
      next
        case False
        have "loose \<noteq> {}" by (rule tok_clash_ne[OF "1.prems"(1) _ Some[unfolded p] False]) (simp add: Var)
        then show ?thesis using lk Var Some p False
          by (subst norm_term2.simps) (simp add: dfdp_def bindM_def var_clash_def raise_def return_def clashx_def)
      qed
    next
      case None
      have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Var by simp
      note nt = ff_norm_type[OF ei tv]
      have "npostc A env (Var x (tnorm (tyenv env) T))"
        unfolding npostc_def using tok_Var[OF ve ff_tcons[OF ei nt(2)] None] nt(2) None
        by (simp add: tnorm_idem[OF e(6)])
      then show ?thesis using lk Var None nt(1) by (subst norm_term2.simps) (simp add: bindM_def return_def)
    qed
  next
    case (Abs a T body)
    have "subt (?M t) (?M body)" using Abs by (simp add: subt_def)
    then have "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M body)" by blast
    moreover have "tok env (vars body \<union> evars env)" using "1.prems"(1) Abs by simp
    moreover have "ttvars body \<subseteq> ?KN" using "1.prems"(2) Abs by simp
    ultimately have b': "dfdp (norm_term2 env body) (npostc A env)" using IH[of body] by blast
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Abs by simp
    note nt = ff_norm_type[OF ei tv]
    have eq: "norm_term2 env t = bindM (norm_term2 env body) (\<lambda>b'. return (Abs a (tnorm (tyenv env) T) b'))"
      by (subst norm_term2.simps) (simp add: Abs nt(1) bindM_def return_def split: option.splits xres.splits)
    show ?thesis unfolding eq
    proof (rule dfdp_bindM[OF b'])
      fix b'' assume "npostc A env b''"
      then show "dfdp (return (Abs a (tnorm (tyenv env) T) b'')) (npostc A env)"
        using nt(2) by (simp add: npostc_def)
    qed
  next
    case (App f u)
    have vfu: "tok env (vars f \<union> evars env)" "tok env (vars u \<union> evars env)"
      using "1.prems"(1) App tok_App by blast+
    have tfu: "ttvars f \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" using "1.prems"(2) App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      have "tok env (vars body \<union> vars u \<union> evars env)" using vfu f by (simp add: tok_Un)
      moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using tfu f by simp
      ultimately have "dfdp (norm_term2 env (subst_bound u body)) (npostc A env)"
        using redex[of b U body u] f App by blast
      then show ?thesis using f App by (subst norm_term2.simps) simp
    next
      case False
      have "subt (?M t) (?M f)" using App by (simp add: subt_def)
      then have tf: "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M f)" by blast
      have hn: "norm_term2 env t = bindM (norm_term2 env f) (\<lambda>nf.
          (case nf of Abs _ _ body \<Rightarrow> norm_term2 env (subst_bound u body) | _ \<Rightarrow> do {nu \<leftarrow> norm_term2 env u; return (nf $ nu)}))"
        using App False by (subst norm_term2.simps) (cases f; simp)
      show ?thesis unfolding hn
      proof (rule dfdp_bindM[OF IH[OF vfu(1) tfu(1) tf]])
        fix nf assume nf: "norm_term2 env f = return nf" "npostc A env nf"
        have fnf: "?M f \<rightarrow>\<^sub>\<beta>\<^sup>* ?M nf"
          by (rule norm_term2_unfc[OF nf(1)[unfolded return_def] refl e(3,4) einv_rho0(1)[OF ei]])
        note nfp = nf(2)[unfolded npostc_def]
        show "dfdp (case nf of Abs _ _ body \<Rightarrow> norm_term2 env (subst_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> norm_term2 env u; return (nf $ nu)}) (npostc A env)"
        proof (cases "is_Abs nf")
          case True
          then obtain b U body where nfA: "nf = Abs b U body" by (cases nf) auto
          have "(sup beta subt)\<^sup>*\<^sup>* (?M t) (?M (Abs b U body $ u))"
            using App nfA beta_reds_sup[OF rtrancl_beta_AppL[OF fnf, of "?M u"]] by simp
          moreover have "tok env (vars body \<union> vars u \<union> evars env)"
            using nfp vfu(2) nfA by (simp add: tok_Un)
          moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using nfp tfu(2) nfA by simp
          ultimately have "dfdp (norm_term2 env (subst_bound u body)) (npostc A env)"
            using redex[of b U body u] by blast
          then show ?thesis using nfA by simp
        next
          case nA: False
          have "subt (?M t) (?M u)" using App by (simp add: subt_def)
          then have "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M u)" by blast
          note nu = IH[OF vfu(2) tfu(2) this]
          have "dfdp (do {nu \<leftarrow> norm_term2 env u; return (nf $ nu)}) (npostc A env)"
          proof (rule dfdp_bindM[OF nu])
            fix nu assume "npostc A env nu"
            then show "dfdp (return (nf $ nu)) (npostc A env)" using nf(2) by (simp add: npostc_def tok_Un)
          qed
          then show ?thesis using nA by (cases nf) auto
        qed
      qed
    qed
  next
    case (Const a T)
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Const by simp
    note nt = ff_norm_type[OF ei tv]
    have "npostc A env (Const a (tnorm (tyenv env) T))" using ve nt(2) by (simp add: npostc_def)
    then show ?thesis using Const nt(1) by (subst norm_term2.simps) (simp add: bindM_def return_def)
  next
    case (Free a T)
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Free by simp
    note nt = ff_norm_type[OF ei tv]
    have "npostc A env (Free a (tnorm (tyenv env) T))" using ve nt(2) by (simp add: npostc_def)
    then show ?thesis using Free nt(1) by (subst norm_term2.simps) (simp add: bindM_def return_def)
  next
    case (Bound i)
    have "npostc A env t" using ve Bound by (simp add: npostc_def)
    then show ?thesis using Bound by (subst norm_term2.simps) simp
  qed
qed

lemma norm_term1_dfd:
  assumes em: "vt_is_empty (tyenv env)"
  shows
  "tok env (vars t \<union> evars env) \<Longrightarrow> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    termip (sup beta subt) (unfc env t) \<Longrightarrow>
    dfdp (norm_term1 (tenv env) t) (npostc A env)"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (unfc env t, hrk env t)"]])
  case (1 t)
  note e = einvD[OF ei]
  let ?M = "\<lambda>t. unfc env t"
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have sn: "termip (sup beta subt) u" if "(sup beta subt)\<^sup>*\<^sup>* (?M t) u" for u
    by (rule termip_sup_reds[OF that "1.prems"(3)])
  have IH: "dfdp (norm_term1 (tenv env) u) (npostc A env)"
    if "tok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M u)" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    have "(?M u, ?M t) \<in> sn_less"
      by (simp only: sn_less_def mem_Collect_eq case_prod_conv) (use that(3) "1.prems"(3) in blast)
    then show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (?M t, hrk env t))"
      by simp
    show "termip (sup beta subt) (?M u)" by (rule sn[OF tranclp_into_rtranclp[OF that(3)]])
  qed
  have IH': "dfdp (norm_term1 (tenv env) u) (npostc A env)"
    if "tok env (vars u \<union> evars env)" "ttvars u \<subseteq> ?KN" "?M u = ?M t" "hrk env u < hrk env t" for u
  proof (rule "1.IH"[OF _ that(1,2)])
    show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (?M t, hrk env t))"
      using that(3,4) by simp
    show "termip (sup beta subt) (?M u)" by (subst that(3)) (rule "1.prems"(3))
  qed
  have ve: "tok env (evars env)" using "1.prems"(1) by (rule tok_mono) blast
  have redex: "dfdp (norm_term1 (tenv env) (subst_bound u body)) (npostc A env)"
    if "(sup beta subt)\<^sup>*\<^sup>* (?M t) (?M (Abs b U body $ u))" "tok env (vars body \<union> vars u \<union> evars env)"
      "ttvars body \<union> ttvars u \<subseteq> ?KN"
    for b U body u
  proof (subst subst_bound_subst, rule IH)
    have r: "?M (Abs b U body $ u) \<rightarrow>\<^sub>\<beta> ?M (body[u/0])"
      by (simp add: unfc_subst[OF e(3,4)])
    then show "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M (body[u/0]))"
      using that(1) by (meson rtranclp_into_tranclp1 sup2I1)
    show "tok env (vars (body[u/0]) \<union> evars env)"
      using tok_mono[OF that(2)] vars_subst[of body u 0] by blast
    show "ttvars (body[u/0]) \<subseteq> ?KN" using ttvars_subst[of body u 0] that(3) by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    have lk: "lookup1 (tenv env) x T = (case vt_lookup (tenv env) x of None \<Rightarrow> return None
      | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash x T U)"
      by (rule lookup1_def_tok[OF em])
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      show ?thesis
      proof (cases "tnorm (tyenv env) T = tnorm (tyenv env) U")
        case True
        have tcU: "tcons (tyenv env) T" "tcons (tyenv env) U"
        proof -
          have "(x, U) \<in> evars env" using evarsI[OF Some[unfolded p]] .
          then show "tcons (tyenv env) T" "tcons (tyenv env) U" using "1.prems"(1) Var by (auto simp: tok_def)
        qed
        have ue: "ok (unified (tyenv env) T U) True"
          using unified_ok[OF e(6,7) tcU] True by (simp add: return_def)
        have u: "?M u = ?M t" using Some p Var ue by (simp add: unfc_Var_bound[OF e(3)])
        have "hrk env u < hrk env t" using ff_hrk_less[OF ei Some[unfolded p]] Var by simp
        moreover have "tok env (vars u \<union> evars env)" by (rule tok_bnd[OF ve Some[unfolded p]])
        moreover have "ttvars u \<subseteq> ?KN" using tvinvD(2)[OF e(1) Some[unfolded p]] by blast
        ultimately have "dfdp (norm_term1 (tenv env) u) (npostc A env)" using IH'[of u] u by blast
        then show ?thesis using lk Var Some p True by (subst norm_term1.simps) (simp add: bindM_def return_def)
      next
        case False
        have "loose \<noteq> {}" by (rule tok_clash_ne[OF "1.prems"(1) _ Some[unfolded p] False]) (simp add: Var)
        then show ?thesis using lk Var Some p False
          by (subst norm_term1.simps) (simp add: dfdp_def bindM_def var_clash_def raise_def return_def clashx_def)
      qed
    next
      case None
      have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Var by simp
      have "npostc A env (Var x T)"
        unfolding npostc_def using tok_Var[OF ve ff_tcons[OF ei tv] None] tv None
        by (simp add: tnorm_empty[OF em])
      then show ?thesis using lk Var None by (subst norm_term1.simps) (simp add: bindM_def return_def)
    qed
  next
    case (Abs a T body)
    have "subt (?M t) (?M body)" using Abs by (simp add: subt_def)
    then have "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M body)" by blast
    moreover have "tok env (vars body \<union> evars env)" using "1.prems"(1) Abs by simp
    moreover have "ttvars body \<subseteq> ?KN" using "1.prems"(2) Abs by simp
    ultimately have b': "dfdp (norm_term1 (tenv env) body) (npostc A env)" using IH[of body] by blast
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Abs by simp
    have eq: "norm_term1 (tenv env) t = bindM (norm_term1 (tenv env) body) (\<lambda>b'. return (Abs a T b'))"
      by (subst norm_term1.simps) (simp add: Abs)
    show ?thesis unfolding eq
    proof (rule dfdp_bindM[OF b'])
      fix b'' assume "npostc A env b''"
      then show "dfdp (return (Abs a T b'')) (npostc A env)"
        using tv by (simp add: npostc_def)
    qed
  next
    case (App f u)
    have vfu: "tok env (vars f \<union> evars env)" "tok env (vars u \<union> evars env)"
      using "1.prems"(1) App tok_App by blast+
    have tfu: "ttvars f \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" using "1.prems"(2) App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      have "tok env (vars body \<union> vars u \<union> evars env)" using vfu f by (simp add: tok_Un)
      moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using tfu f by simp
      ultimately have "dfdp (norm_term1 (tenv env) (subst_bound u body)) (npostc A env)"
        using redex[of b U body u] f App by blast
      then show ?thesis using f App by (subst norm_term1.simps) simp
    next
      case False
      have "subt (?M t) (?M f)" using App by (simp add: subt_def)
      then have tf: "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M f)" by blast
      have hn: "norm_term1 (tenv env) t = bindM (norm_term1 (tenv env) f) (\<lambda>nf.
          (case nf of Abs _ _ body \<Rightarrow> norm_term1 (tenv env) (subst_bound u body) | _ \<Rightarrow> do {nu \<leftarrow> norm_term1 (tenv env) u; return (nf $ nu)}))"
        using App False by (subst norm_term1.simps) (cases f; simp)
      show ?thesis unfolding hn
      proof (rule dfdp_bindM[OF IH[OF vfu(1) tfu(1) tf]])
        fix nf assume nf: "norm_term1 (tenv env) f = return nf" "npostc A env nf"
        have fnf: "?M f \<rightarrow>\<^sub>\<beta>\<^sup>* ?M nf"
          by (rule norm_term1_unfc[OF nf(1)[unfolded return_def] refl refl em e(3,4)])
        note nfp = nf(2)[unfolded npostc_def]
        show "dfdp (case nf of Abs _ _ body \<Rightarrow> norm_term1 (tenv env) (subst_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> norm_term1 (tenv env) u; return (nf $ nu)}) (npostc A env)"
        proof (cases "is_Abs nf")
          case True
          then obtain b U body where nfA: "nf = Abs b U body" by (cases nf) auto
          have "(sup beta subt)\<^sup>*\<^sup>* (?M t) (?M (Abs b U body $ u))"
            using App nfA beta_reds_sup[OF rtrancl_beta_AppL[OF fnf, of "?M u"]] by simp
          moreover have "tok env (vars body \<union> vars u \<union> evars env)"
            using nfp vfu(2) nfA by (simp add: tok_Un)
          moreover have "ttvars body \<union> ttvars u \<subseteq> ?KN" using nfp tfu(2) nfA by simp
          ultimately have "dfdp (norm_term1 (tenv env) (subst_bound u body)) (npostc A env)"
            using redex[of b U body u] by blast
          then show ?thesis using nfA by simp
        next
          case nA: False
          have "subt (?M t) (?M u)" using App by (simp add: subt_def)
          then have "(sup beta subt)\<^sup>+\<^sup>+ (?M t) (?M u)" by blast
          note nu = IH[OF vfu(2) tfu(2) this]
          have "dfdp (do {nu \<leftarrow> norm_term1 (tenv env) u; return (nf $ nu)}) (npostc A env)"
          proof (rule dfdp_bindM[OF nu])
            fix nu assume "npostc A env nu"
            then show "dfdp (return (nf $ nu)) (npostc A env)" using nf(2) by (simp add: npostc_def tok_Un)
          qed
          then show ?thesis using nA by (cases nf) auto
        qed
      qed
    qed
  next
    case (Const a T)
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Const by simp
    have "npostc A env (Const a T)" using ve tv by (simp add: npostc_def)
    then show ?thesis using Const by (subst norm_term1.simps) simp
  next
    case (Free a T)
    have tv: "tvars T \<subseteq> ?KN" using "1.prems"(2) Free by simp
    have "npostc A env (Free a T)" using ve tv by (simp add: npostc_def)
    then show ?thesis using Free by (subst norm_term1.simps) simp
  next
    case (Bound i)
    have "npostc A env t" using ve Bound by (simp add: npostc_def)
    then show ?thesis using Bound by (subst norm_term1.simps) simp
  qed
qed

text \<open>Normalization terminates on terms that are well-typed in the most general solution:\<close>

theorem norm_term_dfd:
  assumes vk: "tok env (vars t \<union> evars env)" and tv: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and wte: "wt_env (rho0 env) env" and ty: "e \<turnstile> inst (rho0 env) t : T"
  shows "dfdp (norm_term env t) (npostc A env)"
proof -
  note e = einvD[OF ei]
  have tu: "e \<turnstile> inst (rho0 env) (unfc env t) : T" by (rule typing_unfc[OF e(3) wte einv_rho0(1)[OF ei] ty])
  have sn: "termip beta (inst (rho0 env) (unfc env t))" by (rule type_implies_termi[OF tu])
  show ?thesis
  proof (cases "env_is_empty env \<and> \<not> could_beta_contract t")
    case True
    then have em: "vt_is_empty (tenv env)" "vt_is_empty (tyenv env)" by (simp_all add: env_is_empty_def)
    have "npostc A env t" using vk tv by (simp add: npostc_def tnorm_empty[OF em(2)] vt_is_empty_lookup[OF em(1)])
    with True show ?thesis by (simp add: norm_term_def)
  next
    case nid: False
    show ?thesis
    proof (cases "vt_is_empty (tyenv env)")
      case True
      have "termip (sup beta subt) (unfc env t)" by (rule termip_beta_subt[OF termip_inst[OF sn refl]])
      moreover have "norm_term env t = norm_term1 (tenv env) t"
        unfolding norm_term_def by (simp only: if_not_P[OF nid] if_P[OF True])
      ultimately show ?thesis using norm_term1_dfd[OF True vk tv] by simp
    next
      case False
      have "norm_term env t = norm_term2 env t"
        unfolding norm_term_def by (simp only: if_not_P[OF nid] if_not_P[OF False])
      then show ?thesis using norm_term2_dfd[OF vk tv termip_beta_subt[OF sn]] by simp
    qed
  qed
qed

end



subsection \<open>Assignments\<close>

theorem ff_assign_dfd:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t u"
    and ar: "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t : T \<and> e \<turnstile> inst (rho0 env) u : T \<and> arity T = 0"
    and ht: "\<And>v T. head_of t = Var v T \<Longrightarrow> vt_lookup (tenv env) v = None"
    and hu: "\<exists>w W us. u = Var w W \<degree>\<degree> us \<and> vt_lookup (tenv env) w = None"
  shows "cxokE (\<lambda>e. e = ASSIGN) (ff_assign alg env rb t u) (finv A K env0)"
proof -
  have ei: "einv A K env" and fi: "iflex env0 env" and e0: "extends env0 env" using fv by (simp_all add: finv_def)
  note e = einvD[OF ei] and pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  let ?\<rho> = "rho0 env"
  have vk: "tok env (Y \<union> evars env)" by (rule tok_einv[OF ei wi pd(6)])
  have vi: "vinv ?\<rho> env Y" using winvD[OF wi r0] by blast
  have bl: "snd x \<le> maxidx env" if "(x, X) \<in> Y \<union> evars env" for x X
    using belowD[OF _ that] vi by (simp add: vinv_def)
  from ar obtain e T where bs: "bs_env ?\<rho> e rb" and tyt: "e \<turnstile> inst ?\<rho> t : T" and tyu: "e \<turnstile> inst ?\<rho> u : T"
    and a0: "arity T = 0" by blast
  from hu obtain w W us where u: "u = Var w W \<degree>\<degree> us" and w: "vt_lookup (tenv env) w = None" by blast
  show ?thesis
    unfolding ff_assign_def
  proof (rule cxokE_bindW)
    show "cxokE (\<lambda>e. e = ASSIGN) (get_eta_var rb 0 t) (\<lambda>_. True)"
      using get_eta_var_cases[of rb 0 t] by auto
  next
    fix vT assume gev: "okW (get_eta_var rb 0 t) vT"
    obtain v Tv where vT: "vT = (v, Tv)" by (cases vT)
    have hdt: "head_of t = Var v Tv" using get_eta_var_head gev vT by simp
    have v: "vt_lookup (tenv env) v = None" by (rule ht[OF hdt])
    have vt: "(v, Tv) \<in> vars t" by (rule ff_head_of_vars[OF hdt])
    have tvT: "tvars Tv \<subseteq> ?KN" using pd(3) vars_typs[OF vt] by (auto simp: ttvars_def)
    have vku: "tok env (\<Union>(vars ` set [u]) \<union> evars env)" using vk pd(2) by (auto intro: tok_mono)
    have doc: "dfd (occurs_terms env v [u])" by (rule occurs_terms_dfd[OF e(6,7,3) vku])
    show "cxokE (\<lambda>e. e = ASSIGN) ((\<lambda>(v, T). do {
          b \<leftarrow> liftM (occurs_terms env v [u]);
          if b then raiseW ASSIGN
          else do {
            T1 \<leftarrow> liftM (body_type env T);
            T2 \<leftarrow> liftM (fastype env rb u);
            env' \<leftarrow> cunify_types alg T1 T2 env;
            liftM (vupdate (v, T) (rlist_abs rb u) env')}}) vT) (finv A K env0)"
    proof (rule dfd_cases[OF doc])
      fix x assume "occurs_terms env v [u] = Some (Err x)" "clashx x"
      then show ?thesis using vT by (simp add: liftM_def bindW_def cxokE_def)
    next
    fix b assume ob: "occurs_terms env v [u] = Some (Ok b)"
    have oc: "occurs_terms env v [u] = return b" "\<not> b \<longrightarrow> (\<forall>y\<in>fst ` vars u. (v, y) \<notin> (dep env)\<^sup>*)"
      using ob occurs_terms_sound[of env v "[u]", OF _ e(3)] by (auto simp: return_def)
    show ?thesis
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
            using w by (simp add: lookup_def)
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
qed



subsection \<open>Cleaning terms\<close>

theorem clean_term_dfd:
  assumes fv: "finv A K env0 env" and wi: "winv env Y"
    and t: "t = Var v T0 \<degree>\<degree> ts" and v: "vt_lookup (tenv env) v = None"
    and vt: "vars t \<subseteq> Y \<union> evars env" and tt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and lb: "\<not> loose_bvar t (ilength rb)"
    and bs0: "bs_env (rho0 env) e rb" and ty0: "e \<turnstile> inst (rho0 env) t : T" and a0: "arity T = 0"
    and F: "bren_ok banned rb rb' F"
  shows "cxokE (\<lambda>e. e = CHANGE_FAIL) (clean_term banned env t) (\<lambda>(env', t'). finv A K env0 env' \<and>
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
  proof (rule cxokE_bindW[OF cxokE_xokW[OF flexargs_xok refl]])
    fix fas assume fa: "okW (flexargs (downto0_list ?n) ts Ts) fas"
    show "cxokE (\<lambda>e. e = CHANGE_FAIL) (bindW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) (\<lambda>cas.
        let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T0) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')}))) ?P"
    proof (rule cxokE_bindW[OF cxokE_xokW[OF foldrW_change_arg_xok refl]])
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
      have rest: "cxokE (\<lambda>e. e = CHANGE_FAIL) (if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
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
        have tb: "types_abs Ts (v' \<degree>\<degree> map (Bound \<circ> fl_j) args) = types_abs Ts body"
          by (simp add: body_def ks_def)
        show ?thesis
        proof -
        have vk2: "tok env2 (vars ?s \<union> evars env2)"
        proof (rule tokI)
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
        next
          show "vcons (tnorm_inst (tyenv env2)) (vars ?s \<union> evars env2 \<union> evars env2)" using vc2 by simp
        qed
        have t2': "renv e F 0 \<turnstile> inst (rho0 env2) ?s : T" using t2 by (simp add: \<rho>2)
        have ndf: "dfdp (norm_term env2 ?s) (npostc A env2)"
          by (rule norm_term_dfd[OF ei2 vk2 tvs _ t2']) (use wte2 \<rho>2 in simp)
        show ?thesis
        proof (rule dfdp_cases[OF ndf])
          fix x assume "norm_term env2 ?s = Some (Err x)" "clashx x"
          then show ?thesis using tb False g vu
            by (simp add: list_comb_apps Gty_def[symmetric] liftM_def bindW_def cxokE_def return_def)
        next
        fix t' assume nt: "norm_term env2 ?s = return t'" "npostc A env2 t'"
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
          unfolding prod.case using fv2 nt(2) th2 p1 o2(2) gs(1) by (auto simp: npostc_def)
        then show ?thesis using tb False g vu nt(1)
          by (simp add: list_comb_apps Gty_def[symmetric])
        qed
        qed
      qed
      then show "cxokE (\<lambda>e. e = CHANGE_FAIL) (let args = sort_args cas; ts' = map fl_t args in
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

lemma dstep_pokc:
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
    from dstepDg(1)[OF ds \<rho>(1) extends_refl w(1) d v] show ?thesis by blast
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

theorem clean_ffpair_dfd:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t u"
    and ar: "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t : T \<and> e \<turnstile> inst (rho0 env) u : T \<and> arity T = 0"
    and t: "t = Var v T0 \<degree>\<degree> ts" and u: "u = Var w U0 \<degree>\<degree> us" and vw: "v \<noteq> w"
    and v: "vt_lookup (tenv env) v = None" and w: "vt_lookup (tenv env) w = None"
    and tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
    and tf: "\<forall>(t', u')\<in>set tps. flexb env0 t' \<and> flexb env0 u'"
  shows "cxokE (\<lambda>_. False) (clean_ffpair alg rb t u env tps) (\<lambda>(env', tps'). finv A K env0 env' \<and>
    (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t', u')\<in>set tps'. flexb env0 t' \<and> flexb env0 u'))"
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
  have fae: "extends e1 e3" if "okW (ff_assign alg e1 bb s1 s2) e3" for e1 bb s1 s2 e3
    using dstepD(1)[OF ff_assign_sound[OF that]] .
  have FFx: "extends env2 (fst y)" if "okW (FF env2 t1 u1) y" for env2 t1 u1 y
  proof -
    let ?h2 = "\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW e"
    let ?m2 = "do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)}"
    let ?m1 = "do {env3 \<leftarrow> ff_assign alg env2 rb' t1 u1; returnW (env3, tps)}"
    let ?h1 = "\<lambda>e. case e of ASSIGN \<Rightarrow> handleW ?m2 ?h2 | _ \<Rightarrow> raiseW e"
    have h2: "z = (env2, add_tpair rb' t1 u1 tps)" if "okW (?h2 e) z" for e z using that by (cases e) auto
    have m2: "extends env2 (fst z)" if "okW ?m2 z" for z
    proof -
      from that obtain env3 where "okW (ff_assign alg env2 rb' u1 t1) env3" "z = (env3, tps)" by auto
      with fae show ?thesis by simp
    qed
    have m1: "extends env2 (fst z)" if "okW ?m1 z" for z
    proof -
      from that obtain env3 where "okW (ff_assign alg env2 rb' t1 u1) env3" "z = (env3, tps)" by auto
      with fae show ?thesis by simp
    qed
    have hm: "extends env2 (fst z)" if "okW (handleW ?m2 ?h2) z" for z
    proof -
      from that[unfolded okW_handleW] consider "okW ?m2 z" | e where "okW (?h2 e) z" by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis by (rule m2)
      next
        case 2
        from h2[OF this] show ?thesis by (simp add: extends_refl)
      qed
    qed
    have h1: "extends env2 (fst z)" if "okW (?h1 e) z" for e z using that hm by (cases e) auto
    from that[unfolded FF_def okW_handleW] consider "okW ?m1 y" | e where "okW (?h1 e) y" by blast
    then show ?thesis using m1 h1 by cases blast+
  qed
  have ctx: "extends env1 env2" if "okW (clean_term banned env1 s) (env2, s')" for env1 env2 s s'
    using clean_term_sound[OF that F] by (simp add: csound_def)
  have inner: "cxokE (\<lambda>e. e = CHANGE_FAIL)
      (bindW (clean_term banned env t) (\<lambda>(env1, t1). bindW (clean_term banned env1 u) (\<lambda>(env2, u1). FF env2 t1 u1))) ?Q"
  proof (rule cxokE_bindW[OF clean_term_dfd[OF fv wi t v pd(1) pd(3) pd(7) bs tyt a0 F]])
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
    show "cxokE (\<lambda>e. e = CHANGE_FAIL) ((\<lambda>(env1, t1). bindW (clean_term banned env1 u) (\<lambda>(env2, u1). FF env2 t1 u1)) r1) ?Q"
      unfolding r1 prod.case
    proof (rule cxokE_bindW[OF clean_term_dfd[OF fv1 wi1 u w1]])
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
      from dstep_pokc[OF ds wi p ei2 th2] tt1 tu1 brb
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
      have fa1: "cxokE (\<lambda>e. e = ASSIGN) (ff_assign alg env2 rb' t1 u1) (finv A K env0)"
        by (rule ff_assign_dfd[OF fv2 wi2 p2 ar2 ht1 hu1'])
      have fa2: "cxokE (\<lambda>e. e = ASSIGN) (ff_assign alg env2 rb' u1 t1) (finv A K env0)"
        by (rule ff_assign_dfd[OF fv2 wi2 upok_sym[OF p2] ar2' hu1 ht1'])
      have e02: "extends env0 env2" using fv2 by (simp add: finv_def)
      have qk: "?Q (env2, add_tpair rb' t1 u1 tps)"
        using fv2 add_tpair_known[OF tk, of rb' t1 u1] brb tt1 tu1
          add_tpair_flex[OF tf flexb_VarI[OF ff_unbound_extends[OF e02 x12]] flexb_VarI[OF ff_unbound_extends[OF e02 x2]], of rb']
        by (auto simp: t1 u1)
      have "cxokE (\<lambda>_. False) (FF env2 t1 u1) ?Q"
        unfolding FF_def
      proof (rule cxokE_handleW)
        show "cxokE (\<lambda>e. e = ASSIGN) (do {env3 \<leftarrow> ff_assign alg env2 rb' t1 u1; returnW (env3, tps)}) ?Q"
          by (rule cxokE_bindW[OF fa1]) (use tk tf in simp)
        show "cxokE (\<lambda>_. False) (case ASSIGN of ASSIGN \<Rightarrow> handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)})
            (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW e) | _ \<Rightarrow> raiseW ASSIGN) ?Q"
        proof (simp only: uexn.case, rule cxokE_handleW)
          show "cxokE (\<lambda>e. e = ASSIGN) (do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)}) ?Q"
            by (rule cxokE_bindW[OF fa2]) (use tk tf in simp)
          show "cxokE (\<lambda>_. False) (case ASSIGN of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW ASSIGN) ?Q"
            using qk by simp
        qed (auto simp: clashW_def)
      qed (auto simp: clashW_def)
      then show "cxokE (\<lambda>e. e = CHANGE_FAIL) ((\<lambda>(env2, u1). FF env2 t1 u1) r2) ?Q" unfolding r2 prod.case
        by (rule cxokE_mono_exn) simp
    qed
  qed
  show ?thesis
    unfolding cf
  proof (rule cxokE_handleW[OF inner])
    show "cxokE (\<lambda>_. False) (case CHANGE_FAIL of CHANGE_FAIL \<Rightarrow> returnW (env, add_tpair rb t u tps) | _ \<Rightarrow> raiseW CHANGE_FAIL) ?Q"
      using qfail by simp
  qed (auto simp: clashW_def)
qed



subsection \<open>Flex-flex pairs\<close>

text \<open>
  With names at two types, normalization may produce a pair whose heads are the same name at two
  types; \<open>add_ffpair\<close> then raises \<open>TERM\<close> (\<open>Var name confusion\<close>).
\<close>

definition confW :: "uexn \<Rightarrow> bool" where
  "confW e \<longleftrightarrow> loose \<noteq> {} \<and> (\<exists>ts. e = PExn (Term_Error (STR ''add_ffpair: Var name confusion'') ts))"

text \<open>Two normalized occurrences of a name that is not loose have the same type:\<close>

lemma winv_same_type:
  assumes ei: "einv A K env" and wi: "winv env Y"
    and vt: "(v, Tv) \<in> Y \<union> evars env" "(v, Uw) \<in> Y \<union> evars env"
    and nT: "tnorm (tyenv env) Tv = Tv" "tnorm (tyenv env) Uw = Uw" and v: "v \<notin> loose"
  shows "Tv = Uw"
proof -
  have "vinv (tnorm_inst (tyenv env)) env Y" using winvD[OF wi einv_rho0[OF ei]] by blast
  then have eq: "tsubst (tnorm_inst (tyenv env)) Tv = tsubst (tnorm_inst (tyenv env)) Uw"
    using vt v unfolding vinv_def vcons_def by blast
  have "tnorm (tyenv env) Tv = tnorm (tyenv env) Uw" by (subst (1 2) tnorm_tsubst) (rule eq)
  then show ?thesis unfolding nT .
qed

lemma dfdp_mono_ok: "dfdp m P \<Longrightarrow> (\<And>x. m = return x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> dfdp m Q"
  by (simp add: dfdp_def)

theorem add_ffpair_dfd:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t0 u0"
    and ar: "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t0 : T \<and> e \<turnstile> inst (rho0 env) u0 : T \<and> arity T = 0"
    and ft: "flexb env0 t0" and fu: "flexb env0 u0"
    and tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
    and tf: "\<forall>(t', u')\<in>set tps. flexb env0 t' \<and> flexb env0 u'"
  shows "cxokE confW (add_ffpair alg (rb, t0, u0) (env, tps)) (\<lambda>(env', tps'). finv A K env0 env' \<and>
    (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t', u')\<in>set tps'. flexb env0 t' \<and> flexb env0 u'))"
proof -
  have ei: "einv A K env" and fi: "iflex env0 env" and e0: "extends env0 env" using fv by (simp_all add: finv_def)
  note pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  let ?\<rho> = "rho0 env"
  from ar obtain e T where bs: "bs_env ?\<rho> e rb" and tyt0: "e \<turnstile> inst ?\<rho> t0 : T"
    and tyu0: "e \<turnstile> inst ?\<rho> u0 : T" and a0: "arity T = 0" by blast
  have wv: "wt_env ?\<rho> env" "vinv ?\<rho> env Y" using winvD[OF wi r0] by blast+
  have vk: "tok env (Y \<union> evars env)" by (rule tok_einv[OF ei wi pd(6)])
  have nterm: "dfdp (norm_term env s) (\<lambda>s'. npostc A env s' \<and> e \<turnstile> inst ?\<rho> s' : T \<and>
      (\<exists>x X ss. s' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None))"
    if vs: "vars s \<subseteq> Y \<union> evars env" and ts: "ttvars s \<subseteq> ?KN" and tys: "e \<turnstile> inst ?\<rho> s : T"
      and fs: "flexb env0 s" for s
  proof -
    have vks: "tok env (vars s \<union> evars env)" using vk vs by (auto intro: tok_mono)
    show ?thesis
    proof (rule dfdp_mono_ok[OF norm_term_dfd[OF ei vks ts wv(1) tys]])
    fix s' assume ns1: "norm_term env s = return s'" and ns2: "npostc A env s'"
    note ns = ns1 ns2
    have tys': "e \<turnstile> inst ?\<rho> s' : T"
      by (rule nsoundD(3)[OF norm_term_sound[OF ns(1)[unfolded return_def] r0(1) wv(1)] tys])
    have "flexb env0 s'" by (rule norm_term_flex[OF ns(1)[unfolded return_def] fi fs])
    from flexb_base[OF this tys' a0] obtain x X ss where s': "s' = Var x X \<degree>\<degree> ss" by blast
    from ns(2) s' have "vt_lookup (tenv env) x = None" by (simp add: npostc_def head_of_apps)
    with ns tys' s' show "npostc A env s' \<and> e \<turnstile> inst ?\<rho> s' : T \<and>
      (\<exists>x X ss. s' = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None)" by blast
    qed
  qed
  show ?thesis
  proof (rule dfdp_cases[OF nterm[OF pd(1) pd(3) tyt0 ft]])
    fix x assume "norm_term env t0 = Some (Err x)" "clashx x"
    then show ?thesis by (simp add: add_ffpair_def liftM_def bindW_def cxokE_def)
  next
  fix t assume nt0: "norm_term env t0 = return t" and nt1: "npostc A env t \<and> e \<turnstile> inst ?\<rho> t : T \<and>
      (\<exists>x X ss. t = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None)"
  have nt: "norm_term env t0 = return t" "npostc A env t" "e \<turnstile> inst ?\<rho> t : T" using nt0 nt1 by blast+
  from nt1 obtain v Tv ts where t: "t = Var v Tv \<degree>\<degree> ts" and v: "vt_lookup (tenv env) v = None" by blast
  show ?thesis
  proof (rule dfdp_cases[OF nterm[OF pd(2) pd(4) tyu0 fu]])
    fix x assume "norm_term env u0 = Some (Err x)" "clashx x"
    then show ?thesis using nt0 by (simp add: add_ffpair_def liftM_def bindW_def cxokE_def return_def)
  next
  fix u assume nu0: "norm_term env u0 = return u" and nu1: "npostc A env u \<and> e \<turnstile> inst ?\<rho> u : T \<and>
      (\<exists>x X ss. u = Var x X \<degree>\<degree> ss \<and> vt_lookup (tenv env) x = None)"
  have nu: "norm_term env u0 = return u" "npostc A env u" "e \<turnstile> inst ?\<rho> u : T" using nu0 nu1 by blast+
  from nu1 obtain w Uw us where u: "u = Var w Uw \<degree>\<degree> us" and w: "vt_lookup (tenv env) w = None" by blast
  have ttu: "ttvars t \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" using nt(2) nu(2) by (simp_all add: npostc_def)
  have ds: "dstep env [(rb, t0, u0)] env [(rb, t, u)]"
    by (rule norm_term_dstep[OF nt(1)[unfolded return_def] nu(1)[unfolded return_def]])
  define Y' where "Y' = Y \<union> vars t \<union> vars u"
  from dstep_pokc[OF ds wi p ei refl] ttu pd(5) have wi': "winv env Y'" and p': "upok A env rb Y' t u"
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
    show ?thesis
    proof (cases "Tv = Uw")
      case eq: True
      have "\<forall>(t', u')\<in>set (add_tpair rb t u tps). ttvars t' \<union> ttvars u' \<subseteq> ?KN"
        by (rule add_tpair_known[OF tk]) (use pd(5) ttu in blast)
      moreover have "\<forall>(t', u')\<in>set (add_tpair rb t u tps). flexb env0 t' \<and> flexb env0 u'"
        by (rule add_tpair_flex[OF tf]) (simp_all add: t u flexb_VarI ff_unbound_extends[OF e0 v] ff_unbound_extends[OF e0 w])
      ultimately show ?thesis using af True eq fv by simp
    next
      case False
      have "v \<in> loose"
      proof (rule ccontr)
        assume "v \<notin> loose"
        moreover have "(v, Tv) \<in> Y' \<union> evars env" "(v, Uw) \<in> Y' \<union> evars env"
          using True by (auto simp: Y'_def t u vars_apps)
        moreover have "tnorm (tyenv env) Tv = Tv" "tnorm (tyenv env) Uw = Uw"
          using nt(2) nu(2) by (auto simp: npostc_def hds)
        ultimately have "Tv = Uw" using winv_same_type[OF ei wi'] True by blast
        with False show False by simp
      qed
      then have "loose \<noteq> {}" by blast
      then show ?thesis using af True False by (simp add: confW_def)
    qed
  next
    case vw: False
    show ?thesis
    proof (cases "indexname_less v w")
      case True
      from cxokE_mono_exn[OF clean_ffpair_dfd[OF fv wi' upok_sym[OF p'] ar'' u t _ w v tk tf]] vw af True show ?thesis by auto
    next
      case False
      from cxokE_mono_exn[OF clean_ffpair_dfd[OF fv wi' p' ar' t u vw v w tk tf]] vw af False show ?thesis by auto
    qed
  qed
  qed
  qed
qed

text \<open>The invariants after a sound step on a list of pairs:\<close>

lemma dstep_winvc:
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
    from dstepDg(1)[OF ds \<rho>(1) extends_refl w(1) d v] show ?thesis by blast
  qed
  show "winv env' (X \<union> dvars dps')" unfolding winv_def using main by blast
  show "tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> dtyped \<rho> dps'" using main by blast
qed

theorem foldrW_add_ffpair_dfd:
  assumes si: "sinv A K X env ffs" and sh: "\<forall>dp\<in>set ffs. ff_shape env dp \<and> ffeta env dp"
    and tp: "ffres A K X env tps" and tfl: "\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u"
  shows "cxokE confW (foldrW (add_ffpair alg) ffs (env, tps)) (\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and>
    dstep env (ffs @ tdps tps) env' (tdps tps'))"
proof -
  have ei: "einv A K env" and wi: "winv env X" using si by (simp_all add: sinv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have pt: "\<forall>(t, u)\<in>set tps. upok A env [] X t u" using tp by (simp add: ffres_def)
  have tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> ?KN" using pt upokD(3,4) by fast
  have pk: "\<forall>(rb, t, u)\<in>set (ffs @ tdps tps). upok A env rb X t u" using si pt by (auto simp: sinv_def)
  let ?I = "\<lambda>(env', tps'). finv A K env env' \<and>
      (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> ?KN) \<and> (\<forall>(t', u')\<in>set tps'. flexb env t' \<and> flexb env u')"
  have "cxokE confW (foldrW (add_ffpair alg) ffs' (env, tps)) ?I"
    if "set ffs' \<subseteq> set ffs" for ffs'
    using that
  proof (induction ffs')
    case Nil
    have "finv A K env env" using ei by (simp add: finv_def iflex_refl)
    with tk tfl show ?case by simp
  next
    case (Cons dp ffs')
    have IH: "cxokE confW (foldrW (add_ffpair alg) ffs' (env, tps)) ?I"
      using Cons.IH Cons.prems by simp
    show ?case unfolding foldrW.simps
    proof (rule cxokE_bindW[OF IH])
    fix r1 assume f1': "okW (foldrW (add_ffpair alg) ffs' (env, tps)) r1" and I1: "?I r1"
    obtain env1 tps1 where r1: "r1 = (env1, tps1)" by (cases r1)
    note f1 = f1'[unfolded r1]
    from I1 r1 have fv1: "finv A K env env1"
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
    have wi1: "winv env1 Y" unfolding Y_def by (rule dstep_winvc(1)[OF ds1 wi pk1 th1])
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
    from add_ffpair_dfd[OF fv1 wi1 p1 ar ff_shape_flexb[OF shp] tk1' tf1]
    show "cxokE confW (add_ffpair alg dp r1) ?I"
      unfolding r1 dp by (rule cxokE_mono) (use th1 in auto)
    qed
  qed
  from this[OF order_refl] show ?thesis
  proof (rule cxokE_mono_ok)
  fix r assume f': "okW (foldrW (add_ffpair alg) ffs (env, tps)) r" and Ir: "?I r"
  obtain env' tps' where r: "r = (env', tps')" by (cases r)
  note f = f'[unfolded r]
  from Ir r have fv: "finv A K env env'" and tk': "\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> ?KN"
    and tf': "\<forall>(t', u')\<in>set tps'. flexb env t' \<and> flexb env u'" by auto
  have ei': "einv A K env'" and th: "tyenv env' = tyenv env" and e': "extends env env'" and fi': "iflex env env'"
    using fv by (simp_all add: finv_def)
  have ds: "dstep env (ffs @ tdps tps) env' (tdps tps')" by (rule foldrW_add_ffpair_sound[OF f])
  note dw = dstep_winvc[OF ds wi pk th]
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
  with e' th ds fi' tf' show "(\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and>
    dstep env (ffs @ tdps tps) env' (tdps tps')) r" unfolding r by blast
  qed
qed

corollary foldrW_add_ffpair_dfd_Nil:
  assumes "sinv A K X env ffs" "\<forall>dp\<in>set ffs. ff_shape env dp \<and> ffeta env dp"
  shows "cxokE confW (foldrW (add_ffpair alg) ffs (env, [])) (\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and> dstep env ffs env' (tdps tps'))"
proof -
  have "ffres A K X env []" using assms(1) by (simp add: ffres_def sinv_def)
  from foldrW_add_ffpair_dfd[OF assms(1,2) this] show ?thesis by simp
qed



subsection \<open>Flex-flex pairs of any type\<close>

text \<open>
  Without a hypothesis on the names, a flex-flex pair of \<open>SIMPL\<close> that is not of a base type may
  have a head that the treatment of an older pair assigned (at a type that differs from the type of
  this occurrence when the pair was made, and agrees with it later), so that it normalizes to an
  abstraction and \<open>add_ffpair\<close> raises \<open>TERM\<close> (\<open>Vars expected\<close>). The treatment of every
  well-formed pair terminates, raising at most these exceptions and the clash.
\<close>

definition ffexn :: "uexn \<Rightarrow> bool" where
  "ffexn e \<longleftrightarrow> confW e \<or> (\<exists>ts. e = PExn (Term_Error (STR ''add_ffpair: Vars expected'') ts))"

lemma confW_ffexn: "confW e \<Longrightarrow> ffexn e"
  by (simp add: ffexn_def)

theorem add_ffpair_gen:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t0 u0"
    and ft: "flexb env0 t0" and fu: "flexb env0 u0"
    and tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
    and tf: "\<forall>(t', u')\<in>set tps. flexb env0 t' \<and> flexb env0 u'"
  shows "cxokE ffexn (add_ffpair alg (rb, t0, u0) (env, tps)) (\<lambda>(env', tps'). finv A K env0 env' \<and>
    (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t', u')\<in>set tps'. flexb env0 t' \<and> flexb env0 u'))"
proof (cases "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t0 : T \<and> e \<turnstile> inst (rho0 env) u0 : T \<and> arity T = 0")
  case True
  show ?thesis by (rule cxokE_mono_exn[OF add_ffpair_dfd[OF fv wi p True ft fu tk tf] confW_ffexn])
next
  case nar: False
  have ei: "einv A K env" and fi: "iflex env0 env" using fv by (simp_all add: finv_def)
  note pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  let ?\<rho> = "rho0 env"
  from pd(9)[OF r0] obtain e T where bs: "bs_env ?\<rho> e rb" and tyt0: "e \<turnstile> inst ?\<rho> t0 : T"
    and tyu0: "e \<turnstile> inst ?\<rho> u0 : T" by blast
  have a0: "arity T \<noteq> 0"
  proof
    assume "arity T = 0"
    with bs tyt0 tyu0 nar show False by blast
  qed
  have wv: "wt_env ?\<rho> env" "vinv ?\<rho> env Y" using winvD[OF wi r0] by blast+
  have vk: "tok env (Y \<union> evars env)" by (rule tok_einv[OF ei wi pd(6)])
  have nterm: "dfdp (norm_term env s) (\<lambda>s'. npostc A env s' \<and> e \<turnstile> inst ?\<rho> s' : T \<and> flexb env0 s')"
    if vs: "vars s \<subseteq> Y \<union> evars env" and ts: "ttvars s \<subseteq> ?KN" and tys: "e \<turnstile> inst ?\<rho> s : T"
      and fs: "flexb env0 s" for s
  proof -
    have vks: "tok env (vars s \<union> evars env)" using vk vs by (auto intro: tok_mono)
    show ?thesis
    proof (rule dfdp_mono_ok[OF norm_term_dfd[OF ei vks ts wv(1) tys]])
      fix s' assume ns: "norm_term env s = return s'" "npostc A env s'"
      have tys': "e \<turnstile> inst ?\<rho> s' : T"
        by (rule nsoundD(3)[OF norm_term_sound[OF ns(1)[unfolded return_def] r0(1) wv(1)] tys])
      have fl: "flexb env0 s'" by (rule norm_term_flex[OF ns(1)[unfolded return_def] fi fs])
      with ns(2) tys' show "npostc A env s' \<and> e \<turnstile> inst ?\<rho> s' : T \<and> flexb env0 s'" by blast
    qed
  qed
  show ?thesis
  proof (rule dfdp_cases[OF nterm[OF pd(1) pd(3) tyt0 ft]])
    fix x assume "norm_term env t0 = Some (Err x)" "clashx x"
    then show ?thesis by (simp add: add_ffpair_def liftM_def bindW_def cxokE_def)
  next
    fix t assume nt0: "norm_term env t0 = return t" and nt: "npostc A env t \<and> e \<turnstile> inst ?\<rho> t : T \<and> flexb env0 t"
    show ?thesis
    proof (rule dfdp_cases[OF nterm[OF pd(2) pd(4) tyu0 fu]])
      fix x assume "norm_term env u0 = Some (Err x)" "clashx x"
      then show ?thesis using nt0 by (simp add: add_ffpair_def liftM_def bindW_def cxokE_def return_def)
    next
      fix u assume nu0: "norm_term env u0 = return u" and nu: "npostc A env u \<and> e \<turnstile> inst ?\<rho> u : T \<and> flexb env0 u"
      have ttu: "ttvars t \<subseteq> ?KN" "ttvars u \<subseteq> ?KN" using nt nu by (simp_all add: npostc_def)
      show ?thesis
      proof (cases "\<exists>F Tv G Uw. head_of t = Var F Tv \<and> head_of u = Var G Uw")
        case False
        then have "add_ffpair alg (rb, t0, u0) (env, tps) =
            raiseW (PExn (Term_Error (STR ''add_ffpair: Vars expected'') [t, u]))"
          by (auto simp: add_ffpair_def nt0 nu0 split: pterm.splits)
        then show ?thesis by (simp add: ffexn_def)
      next
        case True
        then obtain F Tv G Uw where hds: "head_of t = Var F Tv" "head_of u = Var G Uw" by blast
        have t: "t = Var F Tv \<degree>\<degree> snd (strip_comb t)" using t_apps[of t] hds(1) by simp
        have u: "u = Var G Uw \<degree>\<degree> snd (strip_comb u)" using t_apps[of u] hds(2) by simp
        have ct: "clean_term banned env t = raiseW CHANGE_FAIL" for banned
          by (rule clean_term_unsat[OF ei t ttu(1)[unfolded t[symmetric]] conjunct1[OF conjunct2[OF nt], unfolded t[symmetric]] a0])
        have cu: "clean_term banned env u = raiseW CHANGE_FAIL" for banned
          by (rule clean_term_unsat[OF ei u ttu(2)[unfolded u[symmetric]] conjunct1[OF conjunct2[OF nu], unfolded u[symmetric]] a0])
        have af: "add_ffpair alg (rb, t0, u0) (env, tps) =
            (if F = G then
              (if Tv = Uw then returnW (env, add_tpair rb t u tps)
               else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
             else if indexname_less F G then returnW (env, add_tpair rb u t tps)
             else returnW (env, add_tpair rb t u tps))"
          by (simp add: add_ffpair_def nt0 nu0 hds clean_ffpair_CHANGE_FAIL[OF ct] clean_ffpair_CHANGE_FAIL[OF cu])
        have k: "\<forall>(t', u')\<in>set (add_tpair rb s s' tps). ttvars t' \<union> ttvars u' \<subseteq> ?KN" if "{s, s'} = {t, u}" for s s'
          by (rule add_tpair_known[OF tk]) (use pd(5) ttu that in auto)
        have f: "\<forall>(t', u')\<in>set (add_tpair rb s s' tps). flexb env0 t' \<and> flexb env0 u'" if "{s, s'} = {t, u}" for s s'
          by (rule add_tpair_flex[OF tf]) (use nt nu that in auto)
        show ?thesis
        proof (cases "F = G")
          case True
          show ?thesis
          proof (cases "Tv = Uw")
            case eq: True
            with af True k[of t u] f[of t u] fv show ?thesis by auto
          next
            case False
            have ds: "dstep env [(rb, t0, u0)] env [(rb, t, u)]"
              by (rule norm_term_dstep[OF nt0[unfolded return_def] nu0[unfolded return_def]])
            from dstep_pokc[OF ds wi p ei refl] ttu pd(5)
            have wi': "winv env (Y \<union> vars t \<union> vars u)" by auto
            have "F \<in> loose"
            proof (rule ccontr)
              assume "F \<notin> loose"
              moreover have "(F, Tv) \<in> vars t" by (subst t) (simp add: vars_apps)
              moreover have "(G, Uw) \<in> vars u" by (subst u) (simp add: vars_apps)
              ultimately have "(F, Tv) \<in> (Y \<union> vars t \<union> vars u) \<union> evars env"
                "(F, Uw) \<in> (Y \<union> vars t \<union> vars u) \<union> evars env" "F \<notin> loose"
                using True by auto
              moreover have "tnorm (tyenv env) Tv = Tv" "tnorm (tyenv env) Uw = Uw"
                using nt nu True hds by (auto simp: npostc_def)
              ultimately have "Tv = Uw" using winv_same_type[OF ei wi'] True by blast
              with False show False by simp
            qed
            then have "loose \<noteq> {}" by blast
            with af True False show ?thesis by (simp add: ffexn_def confW_def)
          qed
        next
          case False
          show ?thesis
          proof (cases "indexname_less F G")
            case True
            with af False k[of u t] f[of u t] fv show ?thesis by (auto simp: insert_commute)
          next
            case lt: False
            with af False k[of t u] f[of t u] fv show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
qed

theorem foldrW_add_ffpair_gen:
  assumes si: "sinv A K X env ffs" and sh: "\<forall>dp\<in>set ffs. ff_shape env dp"
    and tp: "ffres A K X env tps" and tfl: "\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u"
  shows "cxokE ffexn (foldrW (add_ffpair alg) ffs (env, tps)) (\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and>
    dstep env (ffs @ tdps tps) env' (tdps tps'))"
proof -
  have ei: "einv A K env" and wi: "winv env X" using si by (simp_all add: sinv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have pt: "\<forall>(t, u)\<in>set tps. upok A env [] X t u" using tp by (simp add: ffres_def)
  have tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> ?KN" using pt upokD(3,4) by fast
  have pk: "\<forall>(rb, t, u)\<in>set (ffs @ tdps tps). upok A env rb X t u" using si pt by (auto simp: sinv_def)
  let ?I = "\<lambda>(env', tps'). finv A K env env' \<and>
      (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> ?KN) \<and> (\<forall>(t', u')\<in>set tps'. flexb env t' \<and> flexb env u')"
  have "cxokE ffexn (foldrW (add_ffpair alg) ffs' (env, tps)) ?I"
    if "set ffs' \<subseteq> set ffs" for ffs'
    using that
  proof (induction ffs')
    case Nil
    have "finv A K env env" using ei by (simp add: finv_def iflex_refl)
    with tk tfl show ?case by simp
  next
    case (Cons dp ffs')
    have IH: "cxokE ffexn (foldrW (add_ffpair alg) ffs' (env, tps)) ?I"
      using Cons.IH Cons.prems by simp
    show ?case unfolding foldrW.simps
    proof (rule cxokE_bindW[OF IH])
    fix r1 assume f1': "okW (foldrW (add_ffpair alg) ffs' (env, tps)) r1" and I1: "?I r1"
    obtain env1 tps1 where r1: "r1 = (env1, tps1)" by (cases r1)
    note f1 = f1'[unfolded r1]
    from I1 r1 have fv1: "finv A K env env1"
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
    have wi1: "winv env1 Y" unfolding Y_def by (rule dstep_winvc(1)[OF ds1 wi pk1 th1])
    have vY: "vtvars Y \<subseteq> tvars_env (tyenv env1) \<union> A"
    proof -
      have "vtvars (dvars (tdps tps1)) \<subseteq> ?KN"
        using tk1 vtvars_vars by (fastforce simp: dvars_def vtvars_def)
      then show ?thesis using upokD(6)[OF p0] th1 by (simp add: Y_def vtvars_Un)
    qed
    have p1: "upok A env1 rb Y t0 u0"
      by (rule ff_pok_Y_mono[OF upok_mono[OF p0 e1] vY]) (simp_all add: th1 Y_def)
    have shp: "ff_shape env (rb, t0, u0)" using sh dpi dp by simp
    have tk1': "\<forall>(t', u')\<in>set tps1. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env1) \<union> A"
      using tk1 th1 by simp
    from add_ffpair_gen[OF fv1 wi1 p1 ff_shape_flexb[OF shp] tk1' tf1]
    show "cxokE ffexn (add_ffpair alg dp r1) ?I"
      unfolding r1 dp by (rule cxokE_mono) (use th1 in auto)
    qed
  qed
  from this[OF order_refl] show ?thesis
  proof (rule cxokE_mono_ok)
  fix r assume f': "okW (foldrW (add_ffpair alg) ffs (env, tps)) r" and Ir: "?I r"
  obtain env' tps' where r: "r = (env', tps')" by (cases r)
  note f = f'[unfolded r]
  from Ir r have fv: "finv A K env env'" and tk': "\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> ?KN"
    and tf': "\<forall>(t', u')\<in>set tps'. flexb env t' \<and> flexb env u'" by auto
  have ei': "einv A K env'" and th: "tyenv env' = tyenv env" and e': "extends env env'" and fi': "iflex env env'"
    using fv by (simp_all add: finv_def)
  have ds: "dstep env (ffs @ tdps tps) env' (tdps tps')" by (rule foldrW_add_ffpair_sound[OF f])
  note dw = dstep_winvc[OF ds wi pk th]
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
  with e' th ds fi' tf' show "(\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and>
    dstep env (ffs @ tdps tps) env' (tdps tps')) r" unfolding r by blast
  qed
qed

corollary foldrW_add_ffpair_gen_Nil:
  assumes "sinv A K X env ffs" "\<forall>dp\<in>set ffs. ff_shape env dp"
  shows "cxokE ffexn (foldrW (add_ffpair alg) ffs (env, [])) (\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and> dstep env ffs env' (tdps tps'))"
proof -
  have "ffres A K X env []" using assms(1) by (simp add: ffres_def sinv_def)
  from foldrW_add_ffpair_gen[OF assms(1,2) this] show ?thesis by simp
qed


end


subsection \<open>The statements of theory \<open>Unify_Flexflex_Term\<close>\<close>

context pure_sig_gen
begin

text \<open>
  The old statements, for results that bind no loose name: normalization terminates if the names
  of the term and of the environment have one type modulo the type environment (\<^const>\<open>vok\<close>);
  this is the statement above in the locale without loose names.
\<close>

lemma cxokE_lxokE_loose: "cxokE Xe m P \<Longrightarrow> (\<And>e. Xe e \<Longrightarrow> loose \<noteq> {}) \<Longrightarrow> lxokE (\<lambda>_. False) f m P"
  unfolding cxokE_def lxokE_def by (auto simp: clashW_def clashx_def)


interpretation one: pure_sig alg ar ctab
  by (simp add: pure_sig_iff wf_algebra_axioms)

theorem norm_term_term:
  assumes ei: "einv A K env" and vk: "vok env (vars t \<union> evars env)" and tv: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and wte: "wt_env (rho0 env) env" and vc: "vcons (rho0 env) (vars t \<union> evars env)"
    and ty: "e \<turnstile> inst (rho0 env) t : T" and nf: "nfree env"
  shows "\<exists>t'. norm_term env t = return t' \<and> npost A env t'"
proof -
  have "one.tok env (vars t \<union> evars env)" using vk by (simp add: one.tok_def vok_def)
  from one.norm_term_dfd[OF ei this tv wte ty] show ?thesis
  proof (rule one.dfdp_cases)
    fix x assume "one.clashx x" then show ?thesis by (simp add: one.clashx_def)
  next
    fix t' assume "norm_term env t = return t'" "one.npostc A env t'"
    then show ?thesis by (auto simp: one.npostc_def one.tok_def npost_def vok_def)
  qed
qed


theorem add_ffpair_term:
  assumes fv: "finv A K env0 env" and wi: "winv env Y" and p: "upok A env rb Y t0 u0"
    and ar: "\<exists>e T. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) t0 : T \<and> e \<turnstile> inst (rho0 env) u0 : T \<and> arity T = 0"
    and ft: "flexb env0 t0" and fu: "flexb env0 u0"
    and tk: "\<forall>(t', u')\<in>set tps. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
    and tf: "\<forall>(t', u')\<in>set tps. flexb env0 t' \<and> flexb env0 u'"
    and nf: "nfree env"
  shows "lxokE (\<lambda>_. False) fst (add_ffpair alg (rb, t0, u0) (env, tps)) (\<lambda>(env', tps'). finv A K env0 env' \<and>
    (\<forall>(t', u')\<in>set tps'. ttvars t' \<union> ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t', u')\<in>set tps'. flexb env0 t' \<and> flexb env0 u'))"
  by (rule cxokE_lxokE_loose[OF add_ffpair_dfd[OF fv wi p ar ft fu tk tf]]) (simp add: confW_def)

theorem foldrW_add_ffpair_term:
  assumes si: "sinv A K X env ffs" and sh: "\<forall>dp\<in>set ffs. ff_shape env dp \<and> ffeta env dp"
    and tp: "ffres A K X env tps" and tfl: "\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u"
    and nf: "nfree env"
  shows "lxokE (\<lambda>_. False) fst (foldrW (add_ffpair alg) ffs (env, tps)) (\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and>
    dstep env (ffs @ tdps tps) env' (tdps tps'))"
  by (rule cxokE_lxokE_loose[OF foldrW_add_ffpair_dfd[OF si sh tp tfl]]) (simp add: confW_def)

corollary foldrW_add_ffpair_term_Nil:
  assumes "sinv A K X env ffs" "\<forall>dp\<in>set ffs. ff_shape env dp \<and> ffeta env dp" "nfree env"
  shows "lxokE (\<lambda>_. False) fst (foldrW (add_ffpair alg) ffs (env, [])) (\<lambda>(env', tps').
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env' \<and> tyenv env' = tyenv env \<and>
    iflex env env' \<and> (\<forall>(t, u)\<in>set tps'. flexb env t \<and> flexb env u) \<and> dstep env ffs env' (tdps tps'))"
proof -
  have "ffres A K X env []" using assms(1) by (simp add: ffres_def sinv_def)
  from foldrW_add_ffpair_term[OF assms(1,2) this _ assms(3)] show ?thesis by simp
qed

end

end
