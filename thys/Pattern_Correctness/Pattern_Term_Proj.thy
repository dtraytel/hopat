section \<open>Termination of Projection\<close>

theory Pattern_Term_Proj
  imports Pattern_Term_Flex
begin

context pure_sig
begin

subsection \<open>Auxiliary facts\<close>

lemma beta_vars: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> vars t \<subseteq> vars s"
  by (induction rule: beta.induct) (use vars_subst in auto)

lemma beta_reds_vars: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> vars t \<subseteq> vars s"
  by (induction rule: rtranclp_induct) (use beta_vars in auto)

lemma idx_result: "idx xs j = return (bidx xs j) \<or> idx xs j = raise (Unif No_Trace)"
  by (induction xs) auto

lemma try_trans_return: "\<exists>y. try_trans xs d i = return y"
  using idx_result[of xs "i - d"] by (auto simp: try_trans_def)

lemma trans_result: "(\<exists>j. trans xs d i = return j) \<or> trans xs d i = raise (Unif No_Trace)"
  using idx_result[of xs "i - d"] by (auto simp: trans_def)

text \<open>The head of a head normal form, if a variable, is unbound:\<close>

lemma head_norm_Var_head:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> fst (strip_comb t') = Var F Fty \<Longrightarrow> vt_lookup (tenv env) F = None"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vt_lookup (tenv env) F = None" if "ok (hn env u) u'" "fst (strip_comb u') = Var F Fty" for u u'
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest Var have "t' = Var x T" by simp
      with "1.prems"(2) have "F = x" by (simp add: strip_comb_def)
      with ok_lookup_None[of env x T] lr None show ?thesis by simp
    next
      case (Some u)
      with rest IH "1.prems"(2) show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with h "1.prems"(2) show ?thesis by (auto simp: strip_comb_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where "f = Abs a T body" by (cases f) auto
      with h App IH "1.prems"(2) show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where "nf = Abs a T body" by (cases nf) auto
        with rest IH "1.prems"(2) show ?thesis by simp
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) simp_all
        with IH[OF nf] "1.prems"(2) show ?thesis by (simp add: strip_comb_App)
      qed
    qed
  qed (use h "1.prems"(2) in \<open>auto simp: strip_comb_def\<close>)
qed


subsection \<open>Results of projection\<close>

definition prpost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    pterm \<Rightarrow> (pterm \<times> env) res \<Rightarrow> bool" where
  "prpost A K env X s r \<longleftrightarrow> (case r of
      Ok (u, env') \<Rightarrow> einv A K env' \<and> winv env' X \<and> tyenv env' = tyenv env \<and> extends env env' \<and>
        prunes env env' X \<and> card (ubv env' X) \<le> card (ubv env X) \<and> newb env env' \<and>
        (\<forall>x b. vt_lookup (tenv env') x = Some b \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
           x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}) \<and>
        fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y} \<and>
        ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<and> vars u \<subseteq> X \<union> evars env'
    | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern)"

lemma prpost_Err [simp]: "prpost A K env X s (Err e) \<longleftrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern"
  by (simp add: prpost_def)

lemma prpost_OkD:
  assumes "prpost A K env X s (Ok (u, env'))"
  shows "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunes env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
      x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" "vars u \<subseteq> X \<union> evars env'"
  using assms by (simp_all only: prpost_def xres.case case_prod_conv)

lemma prpost_OkI:
  assumes "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunes env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "\<And>x b. vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
      x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" "vars u \<subseteq> X \<union> evars env'"
  shows "prpost A K env X s (Ok (u, env'))"
  by (simp only: prpost_def xres.case case_prod_conv) (use assms in blast)

text \<open>Results of projecting a list of arguments, with names in \<open>N\<close>:\<close>

definition prspost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    indexname set \<Rightarrow> (pterm list \<times> env) res \<Rightarrow> bool" where
  "prspost A K env X N r \<longleftrightarrow> (case r of
      Ok (us, env') \<Rightarrow> einv A K env' \<and> winv env' X \<and> tyenv env' = tyenv env \<and> extends env env' \<and>
        prunes env env' X \<and> card (ubv env' X) \<le> card (ubv env X) \<and> newb env env' \<and>
        (\<forall>x b. vt_lookup (tenv env') x = Some b \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x \<in> N) \<and>
        (\<forall>u\<in>set us. fst ` vars (unf env' u) \<subseteq> N \<and> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<and>
          vars u \<subseteq> X \<union> evars env')
    | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern)"

lemma prspost_Err [simp]: "prspost A K env X N (Err e) \<longleftrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern"
  by (simp add: prspost_def)

lemma prspost_OkD:
  assumes "prspost A K env X N (Ok (us, env'))"
  shows "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunes env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> N"
    "u \<in> set us \<Longrightarrow> fst ` vars (unf env' u) \<subseteq> N"
    "u \<in> set us \<Longrightarrow> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    "u \<in> set us \<Longrightarrow> vars u \<subseteq> X \<union> evars env'"
  using assms by (simp_all only: prspost_def xres.case case_prod_conv)

lemma prspost_OkI:
  assumes "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunes env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "\<And>x b. vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> N"
    "\<And>u. u \<in> set us \<Longrightarrow> fst ` vars (unf env' u) \<subseteq> N"
    "\<And>u. u \<in> set us \<Longrightarrow> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<And>u. u \<in> set us \<Longrightarrow> vars u \<subseteq> X \<union> evars env'"
  shows "prspost A K env X N (Ok (us, env'))"
  by (simp only: prspost_def xres.case case_prod_conv) (use assms in blast)

text \<open>The well-typedness invariant after projection follows from soundness:\<close>

lemma pr_winv:
  assumes pr: "pr xs s env d bs = Some (Ok (u, env'))" and wi: "winv env X" and vs: "vars s \<subseteq> X \<union> evars env"
    and ty: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T"
    and th: "tyenv env' = tyenv env" and d: "0 \<le> d" and xs: "\<forall>x\<in>set xs. 0 \<le> x"
  shows "winv env' X"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume ts: "tsol (tyenv env') \<rho>" and c: "cert_inst \<rho>"
  have ts0: "tsol (tyenv env) \<rho>" using ts th by simp
  from winvD[OF wi ts0 c] have w: "wt_env \<rho> env" "vinv \<rho> env X" by blast+
  from ty[OF ts0 c] obtain e T where bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> s : T" by blast
  have "X \<union> vars s \<union> evars env = X \<union> evars env" using vs by blast
  then have vi: "vinv \<rho> env (X \<union> vars s)" using w(2) by (simp add: vinv_def)
  note p = pr_sound[OF pr refl d xs]
  from p[unfolded pr_ok_def, THEN conjunct2, THEN conjunct2, rule_format, OF ts extends_refl w(1) bs tys vi]
  have r: "wt_env \<rho> env'" "vinv \<rho> env' (X \<union> vars u)" by blast+
  from r(2) have "vcons \<rho> (X \<union> vars u \<union> evars env')" "below (maxidx env') (X \<union> vars u \<union> evars env')"
    by (simp_all add: vinv_def)
  then have "vinv \<rho> env' X" unfolding vinv_def
    using vcons_mono[of \<rho> "X \<union> vars u \<union> evars env'" "X \<union> evars env'"]
      below_mono[of "maxidx env'" "X \<union> vars u \<union> evars env'" "X \<union> evars env'" "maxidx env'"] by blast
  with r(1) show "wt_env \<rho> env' \<and> vinv \<rho> env' X" by blast
qed

lemma extends_maxidx: "extends env env' \<Longrightarrow> maxidx env \<le> maxidx env'"
  by (simp add: extends_def)

text \<open>Projecting the arguments of a rigid head, threading the environment:\<close>

lemma mapAccM_pr_term:
  assumes ei0: "einv A K env0"
    and "einv A K env" "winv env X" "tyenv env = tyenv env0" "extends env0 env" "prunes env0 env X"
      "newb env0 env"
    and N0: "{y. maxidx env0 < snd y} \<subseteq> N"
    and "\<forall>t\<in>set ts. fst ` vars (unf env0 t) \<subseteq> N"
    and "\<And>t env. t \<in> set ts \<Longrightarrow> einv A K env \<Longrightarrow> winv env X \<Longrightarrow> tyenv env = tyenv env0 \<Longrightarrow>
      extends env0 env \<Longrightarrow> prunes env0 env X \<Longrightarrow> newb env0 env \<Longrightarrow>
      \<exists>r. pr xs t env d bs = Some r \<and> prpost A K env X t r"
  shows "\<exists>r. mapAccM (\<lambda>s env. pr xs s env d bs) ts env = Some r \<and> prspost A K env X N r"
  using assms(2-)
proof (induction ts arbitrary: env)
  case Nil
  have "prspost A K env X N (Ok ([], env))"
    by (rule prspost_OkI) (use Nil.prems(1,2) in \<open>simp_all add: prunes_same\<close>)
  then show ?case by (simp add: return_def)
next
  case (Cons t ts)
  note ei = Cons.prems(1) and wi = Cons.prems(2) and th = Cons.prems(3) and ext0 = Cons.prems(4)
    and pr0 = Cons.prems(5) and nb0 = Cons.prems(6) and Nt = Cons.prems(8) and IH = Cons.prems(9)
  obtain r where r: "pr xs t env d bs = Some r" "prpost A K env X t r"
    using IH[of t env] ei wi th ext0 pr0 nb0 by auto
  have nm: "fst ` vars (unf env t) \<union> {y. maxidx env < snd y} \<subseteq> N"
  proof -
    have "fst ` vars (unf env t) \<subseteq> fst ` vars (unf env0 t) \<union> {y. maxidx env0 < snd y}"
      by (rule names_newb[OF einvD(3)[OF ei0] einvD(3)[OF ei] nb0 einvD(5)[OF ei0]])
    moreover have "{y. maxidx env < snd y} \<subseteq> {y. maxidx env0 < snd y}"
      using extends_maxidx[OF ext0] by auto
    moreover have "fst ` vars (unf env0 t) \<subseteq> N" using Nt by simp
    ultimately show ?thesis using N0 by blast
  qed
  show ?case
  proof (cases r)
    case (Err e)
    then have "mapAccM (\<lambda>s env. pr xs s env d bs) (t # ts) env = raise e"
      using r(1) by (simp add: raise_def[symmetric])
    with r(2) Err show ?thesis by (simp add: raise_def)
  next
    case (Ok p)
    obtain u env1 where p: "p = (u, env1)" by force
    note po = prpost_OkD[OF r(2)[unfolded Ok p]]
    have th1: "tyenv env1 = tyenv env0" using po(3) th by simp
    have ext1: "extends env0 env1" by (rule extends_trans[OF ext0 po(4)])
    have pr1: "prunes env0 env1 X" by (rule prunes_trans[OF pr0 po(5) po(4) ext0])
    have nb1: "newb env0 env1" by (rule newb_trans[OF nb0 po(7)])
    obtain r' where r': "mapAccM (\<lambda>s env. pr xs s env d bs) ts env1 = Some r'" "prspost A K env1 X N r'"
    proof -
      have "\<forall>t\<in>set ts. fst ` vars (unf env0 t) \<subseteq> N" using Nt by simp
      from Cons.IH[OF po(1,2) th1 ext1 pr1 nb1 Cons.prems(7) this IH[OF list.set_intros(2)]]
      show ?thesis using that by blast
    qed
    have m1: "mapAccM (\<lambda>s env. pr xs s env d bs) (t # ts) env =
        mapAccM (\<lambda>s env. pr xs s env d bs) ts env1 \<bind> (\<lambda>(us, env'). return (u # us, env'))"
      using r(1) Ok p by (simp add: return_def[symmetric])
    show ?thesis
    proof (cases r')
      case (Err e)
      then have "mapAccM (\<lambda>s env. pr xs s env d bs) (t # ts) env = raise e"
        using m1 r'(1) by (simp add: raise_def[symmetric])
      with r'(2) Err show ?thesis by (simp add: raise_def)
    next
      case (Ok p')
      obtain us env' where p': "p' = (us, env')" by force
      note qo = prspost_OkD[OF r'(2)[unfolded Ok p']]
      have m: "mapAccM (\<lambda>s env. pr xs s env d bs) (t # ts) env = return (u # us, env')"
        using m1 r'(1) Ok p' by (simp add: return_def[symmetric])
      have "prspost A K env X N (Ok (u # us, env'))"
      proof (rule prspost_OkI)
        show "einv A K env'" "winv env' X" by (rule qo(1), rule qo(2))
        show "tyenv env' = tyenv env" using qo(3) po(3) by simp
        show "extends env env'" by (rule extends_trans[OF po(4) qo(4)])
        show "prunes env env' X" by (rule prunes_trans[OF po(5) qo(5) qo(4) po(4)])
        show "card (ubv env' X) \<le> card (ubv env X)" using qo(6) po(6) by simp
        show "newb env env'" by (rule newb_trans[OF po(7) qo(7)])
      next
        fix x b assume x': "vt_lookup (tenv env') x = Some b" and x0: "vt_lookup (tenv env) x = None"
        show "x \<in> N"
        proof (cases "vt_lookup (tenv env1) x")
          case None
          from qo(8)[OF x' None] show ?thesis .
        next
          case (Some b1)
          from po(8)[OF Some x0] nm show ?thesis by blast
        qed
      next
        fix u' assume u': "u' \<in> set (u # us)"
        show "fst ` vars (unf env' u') \<subseteq> N"
        proof (cases "u' = u")
          case True
          have "fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env1 u) \<union> {y. maxidx env1 < snd y}"
            by (rule names_newb[OF einvD(3)[OF po(1)] einvD(3)[OF qo(1)] qo(7) einvD(5)[OF po(1)]])
          moreover have "{y. maxidx env1 < snd y} \<subseteq> {y. maxidx env < snd y}"
            using extends_maxidx[OF po(4)] by auto
          ultimately show ?thesis using po(9) nm True by blast
        next
          case False
          with u' have "u' \<in> set us" by simp
          from qo(9)[OF this] show ?thesis .
        qed
        show "ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
          using u' po(10) qo(10) po(3) by auto
        show "vars u' \<subseteq> X \<union> evars env'"
          using u' po(11) qo(11) evars_extends[OF qo(4)] by auto
      qed
      with m show ?thesis unfolding return_def by blast
    qed
  qed
qed


subsection \<open>Termination of projection\<close>

lemma pr_unfold: "pr xs s env d bs = head_norm env s \<bind> (\<lambda>s'. pr_step pr xs s' env d bs)"
  unfolding pr_step_def by (rule pr.simps)

lemma pr_term_aux:
  "M (tnorm_inst (tyenv env)) env s = n \<Longrightarrow> einv A K env \<Longrightarrow> winv env X \<Longrightarrow> finite X \<Longrightarrow>
    vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> vars s \<subseteq> X \<union> evars env \<Longrightarrow>
    ttvars s \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> \<not> loose_bvar s (ilength bs) \<Longrightarrow>
    (\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T) \<Longrightarrow>
    0 \<le> d \<Longrightarrow> \<forall>x\<in>set xs. 0 \<le> x \<Longrightarrow> \<exists>r. pr xs s env d bs = Some r \<and> prpost A K env X s r"
proof (induction n arbitrary: s env d bs rule: less_induct)
  case (less n)
  note Mn = less.prems(1) and ei = less.prems(2) and wi = less.prems(3) and fin = less.prems(4)
    and vX = less.prems(5) and vs = less.prems(6) and tvs = less.prems(7) and lb = less.prems(8)
    and ty = less.prems(9) and d = less.prems(10) and xs0 = less.prems(11)
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  have w0: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi r0] by blast+
  have vcX: "vcons ?\<rho> (X \<union> evars env)" using w0(2) by (simp add: vinv_def)
  have vcons: "vcons ?\<rho> (vars t \<union> evars env)" if "vars t \<subseteq> X \<union> evars env" for t
    by (rule vcons_mono[OF vcX]) (use that in blast)
  have vok: "vok env (vars t \<union> evars env)" if "vars t \<subseteq> X \<union> evars env" for t
    by (rule vok_mono[OF vok_winv[OF ei wi vX]]) (use that in blast)
  obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> s : T0" using ty[OF r0] by blast
  have tyu: "e0 \<turnstile> inst ?\<rho> (unf env s) : T0" by (rule typing_unf[OF e(3) w0(1) vcons[OF vs] ty0])
  have sn: "termip (sup beta subt) (unf env s)" by (rule termip_unf[OF e(3) w0(1) vcons[OF vs] ty0])
  obtain s' where hn: "head_norm env s = return s'" using head_norm_term[OF e(3,4,6,7) vok[OF vs] sn] by blast
  note hn' = hn[unfolded return_def]
  have pr_s: "pr xs s env d bs = pr_step pr xs s' env d bs" by (simp add: pr_unfold hn)
  have vs': "vars s' \<subseteq> X \<union> evars env" using head_norm_vars[OF hn' refl] vs by blast
  have tvs': "ttvars s' \<subseteq> tvars_env ?\<theta> \<union> A"
    using head_norm_ttvars[OF hn' refl] tvs tvinv_etvars[OF e(1)] by blast
  have tvbs: "btvars bs \<subseteq> tvars_env ?\<theta> \<union> A" using tvs by blast
  have lb': "\<not> loose_bvar s' (ilength bs)" by (rule head_norm_loose[OF hn' refl w0(1) ilength_nonneg lb])
  have ty': "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s' : T" if "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    from ty[OF that] obtain e T where "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" by blast
    moreover have "wt_env \<rho> env" using winvD[OF wi that] by blast
    ultimately show ?thesis using head_norm_sound[OF hn' refl that(1)] by blast
  qed
  have nm': "fst ` vars (unf env s') \<subseteq> fst ` vars (unf env s)"
    using beta_reds_vars[OF head_norm_unf[OF hn' refl e(3,4)]] by blast
  have Ms': "M ?\<rho> env s' = n" using M_head_norm[OF hn' e(3,4) tyu] Mn by simp
  obtain e1 T1 where ty1: "e1 \<turnstile> inst ?\<rho> s' : T1" using ty'[OF r0] by blast
  have tyu': "e1 \<turnstile> inst ?\<rho> (unf env s') : T1" by (rule typing_unf[OF e(3) w0(1) vcons[OF vs'] ty1])
  have W: "winv env' X" if "pr xs s env d bs = Some (Ok (u, env'))" "tyenv env' = ?\<theta>" for u env'
    by (rule pr_winv[OF that(1) wi vs ty that(2) d xs0])
  show ?case
  proof (cases "is_Abs s'")
    case True
    then obtain a U t where s': "s' = Abs a U t" by (cases s') auto
    have Mt: "M ?\<rho> env t < n" using M_Abs[OF tyu'[unfolded s']] Ms' s' by simp
    have tyt: "\<exists>e T. bs_env \<rho> e ((a, U) # bs) \<and> e \<turnstile> inst \<rho> t : T" if "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
    proof -
      from ty'[OF that] obtain e T where bs: "bs_env \<rho> e bs" and tA: "e \<turnstile> inst \<rho> s' : T" by blast
      from tA s' obtain V where c: "cert_typ alg ar (tsubst \<rho> U)" and tt: "e\<langle>0:tsubst \<rho> U\<rangle> \<turnstile> inst \<rho> t : V"
        by auto
      from bs_env_Cons[OF bs c] tt show ?thesis by blast
    qed
    have vt: "vars t \<subseteq> X \<union> evars env" using vs' s' by simp
    have "btvars ((a, U) # bs) = tvars U \<union> btvars bs" by (simp add: btvars_def)
    then have tvt: "ttvars t \<union> btvars ((a, U) # bs) \<subseteq> tvars_env ?\<theta> \<union> A" using tvs' tvbs s' by auto
    have lbt: "\<not> loose_bvar t (ilength ((a, U) # bs))" using lb' s' by simp
    have d1: "0 \<le> d + 1" using d by simp
    obtain r where r: "pr xs t env (d + 1) ((a, U) # bs) = Some r" "prpost A K env X t r"
      using less.IH[OF Mt refl ei wi fin vX vt tvt lbt tyt d1 xs0] by blast
    have unfAbs: "unf env s' = Abs a U (unf env t)" by (simp add: s')
    show ?thesis
    proof (cases r)
      case (Err ex)
      have "pr xs s env d bs = raise ex"
        using pr_s s' r(1) Err by (simp add: pr_step_def raise_def[symmetric])
      with r(2) Err show ?thesis by (simp add: raise_def)
    next
      case (Ok p)
      obtain t' env' where p: "p = (t', env')" by force
      note po = prpost_OkD[OF r(2)[unfolded Ok p]]
      have pe: "pr xs s env d bs = return (Abs a U t', env')"
        using pr_s s' r(1) Ok p by (simp add: pr_step_def return_def[symmetric])
      have "prpost A K env X s (Ok (Abs a U t', env'))"
      proof (rule prpost_OkI[OF po(1) W[OF pe[unfolded return_def] po(3)] po(3-7)])
        fix x b assume "vt_lookup (tenv env') x = Some b" "vt_lookup (tenv env) x = None"
        from po(8)[OF this] nm' unfAbs
        show "x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" by auto
      next
        show "fst ` vars (unf env' (Abs a U t')) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
          using po(9) nm' unfAbs by auto
        show "ttvars (Abs a U t') \<subseteq> tvars_env (tyenv env) \<union> A" using po(10) tvs' s' by auto
        show "vars (Abs a U t') \<subseteq> X \<union> evars env'" using po(11) by simp
      qed
      with pe show ?thesis unfolding return_def by blast
    qed
  next
    case nAbs: False
    obtain h ts where hts: "strip_comb s' = (h, ts)" by force
    have s': "s' = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
    have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF hts])
    have vts: "vars t \<subseteq> X \<union> evars env" if "t \<in> set ts" for t
      using vs' that unfolding s' vars_apps by blast
    have tvts: "ttvars t \<subseteq> tvars_env ?\<theta> \<union> A" if "t \<in> set ts" for t
      using tvs' that unfolding s' ttvars_apps by blast
    have lbts: "\<not> loose_bvar t (ilength bs)" if "t \<in> set ts" for t
      using lb' that unfolding s' loose_bvar_apps by blast
    have tyts: "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> t : T" if tin: "t \<in> set ts" and tr: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for t \<rho>
    proof -
      from ty'[OF tr] obtain e T where bs: "bs_env \<rho> e bs" and tA: "e \<turnstile> inst \<rho> s' : T" by blast
      from tA have "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: s' inst_apps)
      then obtain U where "e \<turnstile> inst \<rho> t : U"
        using typing_args[of e "inst \<rho> h" "map (inst \<rho>) ts" T "inst \<rho> t"] tin by auto
      with bs show ?thesis by blast
    qed
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain F Fty where h: "h = Var F Fty" by (cases h) auto
      have F0: "vt_lookup (tenv env) F = None" using head_norm_Var_head[OF hn' refl] hts h by simp
      have Fin: "(F, Fty) \<in> X \<union> evars env" using vs' unfolding s' h vars_apps by simp
      have Fb: "snd F \<le> maxidx env" using w0(2) Fin unfolding vinv_def by (blast dest: belowD)
      have tvF: "tvars Fty \<subseteq> tvars_env ?\<theta> \<union> A" using tvs' unfolding s' h ttvars_apps by simp
      have io: "(\<exists>js. ints_of' env ts = return js) \<or> ints_of' env ts = raise Pattern"
      proof (rule ints_of'_result[OF e(3,4,6,7)])
        show "vok env (\<Union> (vars ` set ts) \<union> evars env)"
          by (rule vok_mono[OF vok_winv[OF ei wi vX]]) (use vts in blast)
        show "termip (sup beta subt) (unf env t)" if tin: "t \<in> set ts" for t
        proof -
          from tyts[OF tin r0] obtain e T where "e \<turnstile> inst ?\<rho> t : T" by blast
          then show ?thesis using termip_unf[OF e(3) w0(1) vcons[OF vts[OF tin]]] by blast
        qed
      qed
      then show ?thesis
      proof
        assume "ints_of' env ts = raise Pattern"
        then have "pr xs s env d bs = raise Pattern" using pr_s nAbs hts h by (simp add: pr_step_def)
        then show ?thesis by (simp add: raise_def)
      next
        assume "\<exists>js. ints_of' env ts = return js"
        then obtain js where js: "ints_of' env ts = return js" by blast
        obtain js' where js': "mapM (try_trans xs d) js = return js'"
          using mapM_return[of js "try_trans xs d"] try_trans_return by blast
        let ?ks = "mk_proj_list js'" and ?ls = "List.map_filter id js'"
        have l2: "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) js js'"
          using js' unfolding return_def by (simp only: ok_mapM)
        then have len: "length js = length js'" by (rule list_all2_lengthD)
        have ks: "\<forall>k\<in>set ?ks. 0 \<le> k \<and> k < ilength js" by (rule mk_proj_list_bren(1)[OF len])
        have tyF: "e1 \<turnstile> inst ?\<rho> (app (Var F Fty) js) : T1"
          by (rule flex_sound(1)[OF js[unfolded return_def] r0(1) w0(1) ty1[unfolded s' h]])
        from tyF obtain Fty_eq: "tsubst ?\<rho> Fty = map e1 js \<Rrightarrow> T1" and js0: "\<forall>i\<in>set js. 0 \<le> i"
          by (rule typing_appE)
        have Fn: "tnorm ?\<theta> Fty = map e1 js \<Rrightarrow> T1" using Fty_eq by simp
        have tc: "tcons ?\<theta> Fty" by (rule tinv_tcons[OF e(2) tvF])
        have ks': "\<forall>k\<in>set ?ks. 0 \<le> k \<and> k < ilength (map e1 js)" using ks by (simp add: ilength_eq)
        obtain Hty where tg: "type_of_G env Fty (ilength (map e1 js)) ?ks = return Hty"
          using type_of_G_ok[OF e(6,7) tc Fn ks'] by blast
        have tg': "type_of_G env Fty (ilength js) ?ks = return Hty" using tg by (simp add: ilength_eq)
        have tvH: "tvars Hty \<subseteq> tvars_env ?\<theta> \<union> A" by (rule type_of_G_tvars[OF tg'[unfolded return_def] e(1) tvF])
        obtain env1 H where gv: "genvar (fst F) env Hty = (env1, H)" by force
        have "\<forall>i\<in>set js. i < ilength bs"
          by (rule ints_of'_loose[OF js[unfolded return_def] w0(1) ilength_nonneg]) (use lbts in blast)
        with js0 have xsb: "\<forall>i\<in>set js. 0 \<le> i \<and> i < ilength bs" by blast
        from bind_new_term[OF ei fin F0 Fin Fb gv xsb ks tvF tvbs tvH]
        obtain env'' where bn: "(mk_hnf bs js H ?ks \<bind> (\<lambda>t. update (F, Fty) t env1)) = return env''"
          and post: "einv A K env''" "tyenv env'' = ?\<theta>" "extends env env''" "prunes env env'' X"
            "card (ubv env'' X) \<le> card (ubv env X)" "newb env env''"
          and lkF: "vt_lookup (tenv env'') F = Some (Fty, abs_list (map (\<lambda>i. bs ! nat_of_integer i) js) (app H ?ks))"
          by blast
        let ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) js) (app H ?ks)"
        note g = genvar_simps[OF gv]
        have mk: "mk_hnf bs js H ?ks = return ?u" by (simp add: mk_hnf_def mkabs_ok[OF xsb])
        have upd: "update (F, Fty) ?u env1 = return env''" using bn mk by simp
        have pe: "pr xs s env d bs = return (app H ?ls, env'')"
          using pr_s nAbs hts h js js' tg' gv mk upd by (simp add: pr_step_def Let_def)
        note u = ok_update[OF upd[unfolded return_def]]
        let ?H = "(fst F, maxidx env + 1)"
        have H: "H = Var ?H Hty" by (rule g(4))
        have lk'': "vt_lookup (tenv env'') x = (if x = F then Some (Fty, ?u) else vt_lookup (tenv env) x)" for x
          using u(2) g(1) by simp
        have H0: "vt_lookup (tenv env) ?H = None"
        proof (rule ccontr)
          assume "vt_lookup (tenv env) ?H \<noteq> None"
          then obtain b where "vt_lookup (tenv env) ?H = Some b" by blast
          from bbelowD[OF e(5) this] show False by simp
        qed
        have FH: "?H \<noteq> F" using Fb by (simp add: prod_eq_iff)
        have H'': "vt_lookup (tenv env'') ?H = None" using lk''[of ?H] H0 FH by simp
        have "prpost A K env X s (Ok (app H ?ls, env''))"
        proof (rule prpost_OkI[OF post(1) W[OF pe[unfolded return_def] post(2)] post(2-6)])
          fix x b assume x'': "vt_lookup (tenv env'') x = Some b" and x0: "vt_lookup (tenv env) x = None"
          have "x = F" using lk''[of x] x'' x0 by (cases "x = F") simp_all
          moreover have "F \<in> fst ` vars (unf env s')"
          proof -
            have "(F, Fty) \<in> vars (unf env s')"
              using F0 by (simp add: s' h unf_apps vars_apps unf_Var[OF e(3)])
            then show ?thesis by force
          qed
          ultimately show "x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" using nm' by blast
        next
          have "unf env'' (app H ?ls) = app H ?ls"
            using H'' by (simp add: app_apps unf_apps H unf_Var[OF einvD(3)[OF post(1)]] comp_def)
          then show "fst ` vars (unf env'' (app H ?ls)) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
            by (simp add: H)
          show "ttvars (app H ?ls) \<subseteq> tvars_env (tyenv env) \<union> A" using tvH by (simp add: H)
          show "vars (app H ?ls) \<subseteq> X \<union> evars env''" using evarsI2[OF lkF] by (simp add: H)
        qed
        with pe show ?thesis unfolding return_def by blast
      qed
    next
      case nVar: False
      show ?thesis
      proof (cases "is_Abs h")
        case True
        then have "pr xs s env d bs = raise Pattern" using pr_s nAbs nVar hts by (simp add: pr_step_def)
        then show ?thesis by (simp add: raise_def)
      next
        case nAbs_h: False
        have rh: "rigid h" using nVar nAbs_h nApp by (cases h) auto
        have M_ts: "M ?\<rho> env t < n" if tin: "t \<in> set ts" for t
        proof -
          have "M ?\<rho> env s' = 1 + sum_list (map (M ?\<rho> env) ts)"
            using M_rigid[OF rh tyu'[unfolded s']] s' by simp
          moreover have "M ?\<rho> env t \<le> sum_list (map (M ?\<rho> env) ts)"
            using tin by (simp add: member_le_sum_list)
          ultimately show ?thesis using Ms' by simp
        qed
        let ?hc = "case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h"
        have hd: "(\<exists>h''. ?hc = return h'' \<and> vars h'' = {} \<and> ttvars h'' \<subseteq> ttvars h \<and> rigid h'') \<or>
            (\<exists>v. ?hc = raise (Unif v))"
        proof (cases h)
          case (Bound i)
          then show ?thesis using trans_result[of xs d i] by auto
        qed (use rh in auto)
        then show ?thesis
        proof
          assume "\<exists>v. ?hc = raise (Unif v)"
          then obtain v where hv: "?hc = raise (Unif v)" by blast
          have "pr xs s env d bs = raise (Unif v)"
            using pr_s nAbs nVar nAbs_h hts hv by (simp add: pr_step_def)
          then show ?thesis by (simp add: raise_def)
        next
          assume "\<exists>h''. ?hc = return h'' \<and> vars h'' = {} \<and> ttvars h'' \<subseteq> ttvars h \<and> rigid h''"
          then obtain h'' where hh: "?hc = return h''" "vars h'' = {}" "ttvars h'' \<subseteq> ttvars h" "rigid h''"
            by blast
          let ?N = "fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
          have Nts: "\<forall>t\<in>set ts. fst ` vars (unf env t) \<subseteq> ?N"
          proof
            fix t assume tin: "t \<in> set ts"
            have "vars (unf env t) \<subseteq> vars (unf env s')"
              using tin unfolding s' unf_apps vars_apps by auto
            then have "fst ` vars (unf env t) \<subseteq> fst ` vars (unf env s')" by (rule image_mono)
            with nm' show "fst ` vars (unf env t) \<subseteq> ?N" by blast
          qed
          have "\<exists>r. mapAccM (\<lambda>s env. pr xs s env d bs) ts env = Some r \<and> prspost A K env X ?N r"
          proof (rule mapAccM_pr_term[OF ei ei wi refl extends_refl prunes_same[OF refl refl] newb_refl _ Nts])
            show "{y. maxidx env < snd y} \<subseteq> ?N" by blast
          next
            fix t env2 assume tin: "t \<in> set ts" and ei2: "einv A K env2" and wi2: "winv env2 X"
              and th2: "tyenv env2 = ?\<theta>" and ext2: "extends env env2" and pr2: "prunes env env2 X"
              and nb2: "newb env env2"
            show "\<exists>r. pr xs t env2 d bs = Some r \<and> prpost A K env2 X t r"
            proof (rule less.IH[OF _ refl ei2 wi2 fin _ _ _ lbts[OF tin] _ d xs0])
              have r2: "tsol (tyenv env2) ?\<rho>" "cert_inst ?\<rho>" using einv_rho0[OF ei2] th2 by simp_all
              have w2: "wt_env ?\<rho> env2" "vinv ?\<rho> env2 X" using winvD[OF wi2 r2] by blast+
              have vc2: "vcons ?\<rho> (X \<union> evars env2)" using w2(2) by (simp add: vinv_def)
              obtain e T where tyt: "e \<turnstile> inst ?\<rho> t : T" using tyts[OF tin r0] by blast
              have "M ?\<rho> env2 t = M ?\<rho> env t"
                using pr2 w2(1) vc2 vts[OF tin] tyt unfolding prunes_def by blast
              then show "M (tnorm_inst (tyenv env2)) env2 t < n" using M_ts[OF tin] th2 by simp
              show "vtvars X \<subseteq> tvars_env (tyenv env2) \<union> A" using vX th2 by simp
              show "vars t \<subseteq> X \<union> evars env2" using vts[OF tin] evars_extends[OF ext2] by blast
              show "ttvars t \<union> btvars bs \<subseteq> tvars_env (tyenv env2) \<union> A" using tvts[OF tin] tvbs th2 by simp
            next
              fix \<rho> assume "tsol (tyenv env2) \<rho>" "cert_inst \<rho>"
              then show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> t : T" using tyts[OF tin] th2 by simp
            qed
          qed
          then obtain r where r: "mapAccM (\<lambda>s env. pr xs s env d bs) ts env = Some r" "prspost A K env X ?N r"
            by blast
          show ?thesis
          proof (cases r)
            case (Err ex)
            have "pr xs s env d bs = raise ex"
              using pr_s nAbs nVar nAbs_h hts hh(1) r(1) Err by (simp add: pr_step_def raise_def[symmetric])
            with r(2) Err show ?thesis by (simp add: raise_def)
          next
            case (Ok p)
            obtain us env' where p: "p = (us, env')" by force
            note qo = prspost_OkD[OF r(2)[unfolded Ok p]]
            have pe: "pr xs s env d bs = return (h'' \<degree>\<degree> us, env')"
              using pr_s nAbs nVar nAbs_h hts hh(1) r(1) Ok p
              by (simp add: pr_step_def list_comb_apps return_def[symmetric])
            have "prpost A K env X s (Ok (h'' \<degree>\<degree> us, env'))"
            proof (rule prpost_OkI[OF qo(1) W[OF pe[unfolded return_def] qo(3)] qo(3-7)])
              fix x b assume "vt_lookup (tenv env') x = Some b" "vt_lookup (tenv env) x = None"
              from qo(8)[OF this] show "x \<in> ?N" .
            next
              show "fst ` vars (unf env' (h'' \<degree>\<degree> us)) \<subseteq> ?N"
              proof
                fix x assume "x \<in> fst ` vars (unf env' (h'' \<degree>\<degree> us))"
                then obtain q where q: "q \<in> vars (unf env' (h'' \<degree>\<degree> us))" "x = fst q" by blast
                from q(1) have "q \<in> vars (unf env' h'' \<degree>\<degree> map (unf env') us)" by (simp only: unf_apps)
                then obtain u where u: "u \<in> set us" "q \<in> vars (unf env' u)"
                  using hh(2) unf_rigid[OF hh(4)] unfolding vars_apps by auto
                from u(2) q(2) have "x \<in> fst ` vars (unf env' u)" by blast
                with qo(9)[OF u(1)] show "x \<in> ?N" by blast
              qed
              have "ttvars h \<subseteq> ttvars s'" by (simp add: s' ttvars_apps)
              then show "ttvars (h'' \<degree>\<degree> us) \<subseteq> tvars_env (tyenv env) \<union> A"
                unfolding ttvars_apps using hh(3) tvs' qo(10) by blast
              show "vars (h'' \<degree>\<degree> us) \<subseteq> X \<union> evars env'"
                unfolding vars_apps using hh(2) qo(11) by blast
            qed
            with pe show ?thesis unfolding return_def by blast
          qed
        qed
      qed
    qed
  qed
qed


theorem pr_term:
  assumes "einv A K env" "winv env X" "finite X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and "vars s \<subseteq> X \<union> evars env" "ttvars s \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    and "\<not> loose_bvar s (ilength bs)"
    and "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T"
    and "0 \<le> d" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "\<exists>r. pr xs s env d bs = Some r \<and> prpost A K env X s r"
  by (rule pr_term_aux[OF refl assms])

corollary proj_term:
  assumes "einv A K env" "winv env X" "finite X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and "vars s \<subseteq> X \<union> evars env" "ttvars s \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    and "\<not> loose_bvar s (ilength bs)"
    and "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T"
    and "\<forall>x\<in>set is. 0 \<le> x"
  shows "\<exists>r. proj s env bs is = Some r \<and> prpost A K env X s r"
proof (cases "downto0 is (ilength bs - 1)")
  case True
  have "prpost A K env X s (Ok (s, env))"
  proof (rule prpost_OkI[OF assms(1,2) refl extends_refl prunes_same[OF refl refl] order_refl newb_refl])
    show "\<And>x b. vt_lookup (tenv env) x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
        x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" by simp
    show "fst ` vars (unf env s) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" by blast
    show "ttvars s \<subseteq> tvars_env (tyenv env) \<union> A" using assms(6) by blast
    show "vars s \<subseteq> X \<union> evars env" by (rule assms(5))
  qed
  with True show ?thesis by (simp add: proj_def return_def)
next
  case False
  with pr_term[OF assms(1-8) order_refl assms(9)] show ?thesis by (simp add: proj_def)
qed

end

end
