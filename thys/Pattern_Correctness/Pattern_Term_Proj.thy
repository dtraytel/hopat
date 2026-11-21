section \<open>Auxiliary Facts on Projection\<close>

theory Pattern_Term_Proj
  imports Pattern_Term_Flex
begin

context pure_sig_gen
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

lemma mapAccM_pr_extends:
  assumes "ok (mapAccM (\<lambda>s env. pr xs s env d bs) ts env) (us, env')" "0 \<le> d" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "extends env env'"
proof -
  have "prs_ok xs ts env d bs us env'"
    by (rule mapAccM_pr_ok[where f = pr, OF assms(1)]) (rule pr_sound[OF _ refl assms(2,3)])
  then show ?thesis by (simp add: prs_ok_def)
qed

lemma pr_unfold: "pr xs s env d bs = head_norm env s \<bind> (\<lambda>s'. pr_step pr xs s' env d bs)"
  unfolding pr_step_def by (rule pr.simps)

end

end
