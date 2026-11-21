section \<open>Termination of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Term
  imports Unify_Simpl_Term Unify_Flexflex_Sound
begin

context pure_sig_gen
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

lemma ff_liftM_return [simp]: "liftM (return x) = returnW x"
  by (simp add: liftM_def return_def returnW_def)

lemma flexargs_xok: "xokW CHANGE_FAIL (flexargs js ts Ts) (\<lambda>_. True)"
  by (induction js ts Ts rule: flexargs.induct) (auto intro: xokW_bindW)

lemma change_bnos_xok: "xokW CHANGE_FAIL (change_bnos banned lev t) (\<lambda>_. True)"
  by (induction banned lev t rule: change_bnos.induct) (auto intro!: xokW_bindW)

lemma foldrW_change_arg_xok: "xokW CHANGE_FAIL (foldrW (change_arg del banned) fas acc) (\<lambda>_. True)"
proof (induction fas)
  case (Cons a fas)
  show ?case
  proof (simp, rule xokW_bindW[OF Cons.IH])
    fix cas
    obtain j t T where a: "a = Flarg j t T" by (cases a)
    show "xokW CHANGE_FAIL (change_arg del banned a cas) (\<lambda>_. True)"
      by (auto simp: change_arg_def a intro!: xokW_bindW[OF change_bnos_xok])
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
    "nfree env"
  shows "vok env (Z \<union> evars env)"
  unfolding vok_def
proof (intro ballI, clarify, intro conjI allI impI)
  fix x T assume xT: "(x, T) \<in> Z \<union> evars env"
  then show "tcons (tyenv env) T" using assms(1) by blast
  fix U u assume lk: "vt_lookup (tenv env) x = Some (U, u)"
  then have "(x, U) \<in> Z \<union> evars env" using evarsI by blast
  from vconsD[OF assms(2) nfreeD[OF assms(3) lk] xT this] show "tnorm (tyenv env) T = tnorm (tyenv env) U" by simp
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

subsection \<open>Cleaning pairs\<close>

lemma ff_okW_xok: "okW m x \<Longrightarrow> Q x \<Longrightarrow> xokW E m Q"
  by (auto simp: xokW_def)

lemma xok_handleW:
  assumes "xokW E m Q" "\<exists>x. okW (h E) x \<and> Q x"
  shows "\<exists>x. okW (handleW m h) x \<and> Q x"
  using assms unfolding xokW_def okW_handleW by blast

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

text \<open>The invariants after a sound step on a list of pairs:\<close>

lemma dstep_winv:
  assumes ds: "dstep env dps env' dps'" and wi: "winv env X" and pk: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    and th: "tyenv env' = tyenv env" and nf': "nfree env'"
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
    from dstepD(2)[OF ds \<rho>(1) extends_refl w(1) d v nf'] show ?thesis by blast
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


subsection \<open>Heads of flex-flex pairs, and pairs that are kept\<close>

definition hd1 :: "pterm \<Rightarrow> (indexname \<times> nat) set" where
  "hd1 s = {(F, length (snd (strip_comb s))) | F T. head_of s = Var F T}"

definition hds :: "dpair \<Rightarrow> (indexname \<times> nat) set" where
  "hds dp = (case dp of (rb, t, u) \<Rightarrow> hd1 t \<union> hd1 u)"

lemma flexargs_CHANGE_FAIL:
  "length js = length ts \<Longrightarrow> length ts \<noteq> length Ts \<Longrightarrow> flexargs js ts Ts = raiseW CHANGE_FAIL"
  by (induction js ts Ts rule: flexargs.induct) (auto simp: bindW_def raiseW_def)

lemma clean_term_CHANGE_FAIL:
  assumes t: "t = Var v T0 \<degree>\<degree> ts" and st: "strip_type env T0 = return (Ts, U)" and l: "length ts \<noteq> length Ts"
  shows "clean_term banned env t = raiseW CHANGE_FAIL"
proof -
  have sc: "strip_comb t = (Var v T0, ts)" by (simp add: t strip_comb_atom_apps)
  have "flexargs (downto0_list (length ts)) ts Ts = raiseW CHANGE_FAIL"
    by (rule flexargs_CHANGE_FAIL[OF _ l]) (simp add: downto0_list_def)
  then show ?thesis by (simp add: clean_term_def sc st Let_def bindW_def raiseW_def returnW_def)
qed

lemma clean_ffpair_CHANGE_FAIL:
  assumes "\<And>banned. clean_term banned env t = raiseW CHANGE_FAIL"
  shows "clean_ffpair al rb t u env tps = returnW (env, add_tpair rb t u tps)"
  using assms by (simp add: clean_ffpair_def Let_def bindW_def handleW_def raiseW_def returnW_def split: prod.splits)

lemma arity_tbody: "arity (tbody T) = 0"
  by (induction T rule: tbody.induct) auto

text \<open>A flexible term with fewer arguments than the arity of the type of its head is not cleaned:\<close>

lemma clean_term_unsat:
  assumes ei: "einv A K env" and t: "t = Var v T0 \<degree>\<degree> ts"
    and tt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and ty: "e \<turnstile> inst (rho0 env) t : T" and a: "arity T \<noteq> 0"
  shows "clean_term banned env t = raiseW CHANGE_FAIL"
proof -
  note e = einvD[OF ei]
  let ?\<rho> = "rho0 env"
  have tvT0: "tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A" using tt by (simp add: t ttvars_apps)
  from binder_types_tvars[OF e(2) refl tvT0] obtain Ts where Ts: "binder_types env T0 = return Ts" by blast
  from body_type_tnorm[OF e(2) refl tvT0] obtain U where U: "body_type env T0 = return U"
    "tnorm (tyenv env) U = tbody (tnorm (tyenv env) T0)" by blast
  have st: "strip_type env T0 = return (Ts, U)" by (simp add: strip_type_def Ts(1) U(1))
  have eq: "tsubst ?\<rho> T0 = map (tsubst ?\<rho>) Ts \<Rrightarrow> tsubst ?\<rho> U"
    by (rule strip_type_sound[OF st[unfolded return_def] einv_rho0(1)[OF ei]])
  have "arity (tsubst ?\<rho> T0) = length Ts + arity (tsubst ?\<rho> U)"
    unfolding eq arity_funs by simp
  moreover have "arity (tsubst ?\<rho> U) = 0" using U(2) arity_tbody by simp
  ultimately have a1: "arity (tsubst ?\<rho> T0) = length Ts" by simp
  from ff_typed_Var_apps[OF ty[unfolded t]] obtain Us where
    "tsubst ?\<rho> T0 = Us \<Rrightarrow> T" "length Us = length ts" by blast
  then have "arity (tsubst ?\<rho> T0) = length ts + arity T" by (simp add: arity_funs)
  with a1 a have "length ts \<noteq> length Ts" by simp
  from clean_term_CHANGE_FAIL[OF t st this] show ?thesis .
qed


lemma ff_pok_Y_mono: "upok A env rb Y t u \<Longrightarrow> vtvars Y' \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> Y \<subseteq> Y' \<Longrightarrow> upok A env rb Y' t u"
  unfolding upok_def by blast


lemma dstep_pok:
  assumes ds: "dstep env [(rb, t, u)] env' [(rb', t', u')]" and wi: "winv env Y" and p: "upok A env rb Y t u"
    and ei': "einv A K env'" and th: "tyenv env' = tyenv env"
    and tv: "ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env) \<union> A"
    and nf': "nfree env'"
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
    from dstepD(2)[OF ds \<rho>(1) extends_refl w(1) d v nf'] show ?thesis by blast
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

end

end
