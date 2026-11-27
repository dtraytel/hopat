section \<open>Invariants of the Flex-Flex Treatment\<close>

text \<open>
  The invariant of the results (\<open>ffres\<close>), the typing after a step (\<open>dstep_winv\<close>), and facts on
  the type variables and the heads of the terms that the treatment of flex-flex pairs builds.
\<close>

theory Unify_Flexflex_Base
  imports Unify_Inv_Base Unify_Flexflex_Sound
begin

subsection \<open>Type variables of normalized types\<close>

context pure_sig_gen
begin

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

subsection \<open>Heads of normalized terms\<close>

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

lemma ff_ttvars_change_bnos: "okW (change_bnos banned lev s) s' \<Longrightarrow> ttvars s' = ttvars s"
  by (induction banned lev s arbitrary: s' rule: change_bnos.induct) (auto split: if_splits)

subsection \<open>Type variables of the terms that the treatment builds\<close>

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

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

subsection \<open>Cleaned pairs and the invariant of the results\<close>

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
    from dstepDg(1)[OF ds \<rho>(1) extends_refl w(1) d v] show ?thesis by blast
  qed
  show "winv env' (X \<union> dvars dps')" unfolding winv_def using main by blast
  show "tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> dtyped \<rho> dps'" using main by blast
qed

text \<open>The invariant of the results: a well-formed environment and closed well-formed pairs.\<close>

definition ffres :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "ffres A K X env tps \<longleftrightarrow> einv A K env \<and> winv env X \<and> (\<forall>(t, u)\<in>set tps. upok A env [] X t u)"

lemma ffres_sinv: "ffres A K X env tps \<longleftrightarrow> sinv A K X env (tdps tps)"
  unfolding ffres_def sinv_def by auto

end

end
