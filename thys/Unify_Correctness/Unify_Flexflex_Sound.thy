section \<open>Soundness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Sound
  imports Unify_Simpl_Sound
begin

context pure_sig
begin

text \<open>
  At the end of the search, \<open>add_ffpair\<close> normalizes the remaining flex-flex pairs, deletes
  bound variables that do not occur in both terms (\<open>clean_term\<close>), does the assignments it
  can (\<open>ff_assign\<close>), and returns the other pairs, closed by their binders (\<open>add_tpair\<close>).
  Each of these is a step in the sense of \<^const>\<open>dstep\<close>.
\<close>

subsection \<open>Variables up to the type instantiation\<close>

text \<open>The normalization of types replaces variables by variables of the same instantiated type:\<close>

definition vsim :: "tinst \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vsim \<rho> Y Z \<longleftrightarrow> (\<forall>x T. (x, T) \<in> Y \<longrightarrow> (\<exists>U. (x, U) \<in> Z \<and> tsubst \<rho> T = tsubst \<rho> U))"

lemma vsim_subset: "Y \<subseteq> Z \<Longrightarrow> vsim \<rho> Y Z"
  unfolding vsim_def by blast

lemma vsim_mono: "vsim \<rho> Y Z \<Longrightarrow> Z \<subseteq> Z' \<Longrightarrow> vsim \<rho> Y Z'"
  unfolding vsim_def by blast

lemma vsim_Un: "vsim \<rho> Y Z \<Longrightarrow> vsim \<rho> Y' Z \<Longrightarrow> vsim \<rho> (Y \<union> Y') Z"
  unfolding vsim_def by blast

lemma vsim_trans: "vsim \<rho> Y Z \<Longrightarrow> vsim \<rho> Z W \<Longrightarrow> vsim \<rho> Y W"
  unfolding vsim_def by metis

lemma vinv_vsim:
  assumes "vinv \<rho> env (X \<union> Z)" "vsim \<rho> Y (Z \<union> evars env)"
  shows "vinv \<rho> env (X \<union> Y)"
proof -
  let ?A = "X \<union> Z \<union> evars env"
  from assms(1) have c: "vcons \<rho> ?A" and b: "below (maxidx env) ?A" by (simp_all add: vinv_def)
  have m: "\<exists>U. (x, U) \<in> ?A \<and> tsubst \<rho> T = tsubst \<rho> U" if "(x, T) \<in> X \<union> Y \<union> evars env" for x T
    using that assms(2) unfolding vsim_def by blast
  have "vcons \<rho> (X \<union> Y \<union> evars env)"
    unfolding vcons_def
  proof (intro allI impI)
    fix x T U assume "(x, T) \<in> X \<union> Y \<union> evars env" "(x, U) \<in> X \<union> Y \<union> evars env"
    with m obtain T' U' where "(x, T') \<in> ?A" "tsubst \<rho> T = tsubst \<rho> T'"
      "(x, U') \<in> ?A" "tsubst \<rho> U = tsubst \<rho> U'" by meson
    with vconsD[OF c] show "tsubst \<rho> T = tsubst \<rho> U" by metis
  qed
  moreover have "below (maxidx env) (X \<union> Y \<union> evars env)"
    unfolding below_def
  proof
    fix p assume "p \<in> X \<union> Y \<union> evars env"
    then obtain x T where p: "p = (x, T)" "(x, T) \<in> X \<union> Y \<union> evars env" by (cases p) auto
    with m obtain U where "(x, U) \<in> ?A" by blast
    from belowD[OF b this] p show "snd (fst p) \<le> maxidx env" by simp
  qed
  ultimately show ?thesis by (simp add: vinv_def)
qed


subsection \<open>Normalization\<close>

text \<open>
  A sound normalization step at a type instantiation \<open>\<rho>\<close>: the variables of the result are those
  of the input or of the environment (up to \<open>\<rho>\<close>), loose bound variables are not introduced, and
  typing and meaning in every solution of the environment are kept.
\<close>

definition nsound :: "tinst \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "nsound \<rho> env t t' \<longleftrightarrow> vsim \<rho> (vars t') (vars t \<union> evars env) \<and>
    (\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar t k \<longrightarrow> \<not> loose_bvar t' k) \<and>
    (\<forall>e T. e \<turnstile> inst \<rho> t : T \<longrightarrow> e \<turnstile> inst \<rho> t' : T \<and> (\<forall>\<sigma>. solution \<rho> \<sigma> env \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'))"

lemma nsoundD:
  assumes "nsound \<rho> env t t'"
  shows "vsim \<rho> (vars t') (vars t \<union> evars env)" "0 \<le> k \<Longrightarrow> \<not> loose_bvar t k \<Longrightarrow> \<not> loose_bvar t' k"
    "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> t' : T"
    "e \<turnstile> inst \<rho> t : T \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
  using assms unfolding nsound_def by blast+

lemma nsound_refl: "nsound \<rho> env t t"
  unfolding nsound_def by (auto intro: vsim_subset)

lemma nsound_trans:
  assumes "nsound \<rho> env t1 t2" "nsound \<rho> env t2 t3"
  shows "nsound \<rho> env t1 t3"
proof -
  note a = nsoundD[OF assms(1)] and b = nsoundD[OF assms(2)]
  have "vsim \<rho> (vars t2 \<union> evars env) (vars t1 \<union> evars env)"
    using a(1) by (intro vsim_Un) (auto intro: vsim_subset)
  then have "vsim \<rho> (vars t3) (vars t1 \<union> evars env)" using b(1) by (rule vsim_trans[rotated])
  moreover have "e \<turnstile> inst \<rho> t3 : T \<and> (\<forall>\<sigma>. solution \<rho> \<sigma> env \<longrightarrow> ap \<rho> \<sigma> t1 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t3)"
    if "e \<turnstile> inst \<rho> t1 : T" for e T
    using a(3,4)[OF that] b(3,4)[OF a(3)[OF that]] by (blast intro: conv_trans)
  ultimately show ?thesis unfolding nsound_def using a(2) b(2) by blast
qed

lemma nsound_inst:
  assumes "inst \<rho> t' = inst \<rho> t" "vsim \<rho> (vars t') (vars t)" "\<And>k. \<not> loose_bvar t k \<Longrightarrow> \<not> loose_bvar t' k"
  shows "nsound \<rho> env t t'"
  unfolding nsound_def using assms by (auto simp: ap_def intro: vsim_mono)

lemma nsound_beta: "nsound \<rho> env (Abs b U body $ u) (body[u/0])"
  unfolding nsound_def
proof (intro conjI allI impI)
  show "vsim \<rho> (vars (body[u/0])) (vars (Abs b U body $ u) \<union> evars env)"
    using vars_subst[of body u 0] by (intro vsim_subset) auto
  show "\<not> loose_bvar (body[u/0]) k" if "0 \<le> k" "\<not> loose_bvar (Abs b U body $ u) k" for k
    using that by (intro loose_bvar_subst) simp_all
  fix e T assume ty: "e \<turnstile> inst \<rho> (Abs b U body $ u) : T"
  show "e \<turnstile> inst \<rho> (body[u/0]) : T" using subject_reduction_beta[OF ty inst_beta] .
  show "ap \<rho> \<sigma> (Abs b U body $ u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (body[u/0])" if "solution \<rho> \<sigma> env" for \<sigma>
    using conv_beta[OF wt_ap[OF ty solutionD(3)[OF that]] ap_beta[OF solutionD(3)[OF that]]] .
qed

lemma nsound_Abs:
  assumes "nsound \<rho> env body body'" "tsubst \<rho> T' = tsubst \<rho> T"
  shows "nsound \<rho> env (Abs a T body) (Abs a T' body')"
  unfolding nsound_def
proof (intro conjI allI impI)
  note b = nsoundD[OF assms(1)]
  show "vsim \<rho> (vars (Abs a T' body')) (vars (Abs a T body) \<union> evars env)" using b(1) by simp
  show "\<not> loose_bvar (Abs a T' body') k" if "0 \<le> k" "\<not> loose_bvar (Abs a T body) k" for k
    using b(2)[of "k + 1"] that by (simp add: integer_arith)
  fix e V assume ty: "e \<turnstile> inst \<rho> (Abs a T body) : V"
  then obtain W where c: "cert_typ alg ar (tsubst \<rho> T)"
    and tb: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> body : W" and V: "V = tsubst \<rho> T \<rightarrow>\<^sub>T W"
    by auto
  have ty': "e \<turnstile> inst \<rho> (Abs a T' body') : V" using c b(3)[OF tb] V assms(2) by auto
  then show "e \<turnstile> inst \<rho> (Abs a T' body') : V" .
  show "ap \<rho> \<sigma> (Abs a T body) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs a T' body')" if sol: "solution \<rho> \<sigma> env" for \<sigma>
    using conv_Abs[OF _ _ b(4)[OF tb sol]] wt_ap[OF ty solutionD(3)[OF sol]]
      wt_ap[OF ty' solutionD(3)[OF sol]] assms(2) by simp
qed

lemma nsound_App:
  assumes "nsound \<rho> env f f'" "nsound \<rho> env u u'"
  shows "nsound \<rho> env (f $ u) (f' $ u')"
  unfolding nsound_def
proof (intro conjI allI impI)
  note a = nsoundD[OF assms(1)] and b = nsoundD[OF assms(2)]
  show "vsim \<rho> (vars (f' $ u')) (vars (f $ u) \<union> evars env)"
    using a(1) b(1) by (auto intro: vsim_Un vsim_mono)
  show "\<not> loose_bvar (f' $ u') k" if "0 \<le> k" "\<not> loose_bvar (f $ u) k" for k
    using a(2)[of k] b(2)[of k] that by simp
  fix e T assume ty: "e \<turnstile> inst \<rho> (f $ u) : T"
  then obtain U where tf: "e \<turnstile> inst \<rho> f : U \<rightarrow>\<^sub>T T" and tu: "e \<turnstile> inst \<rho> u : U" by auto
  have ty': "e \<turnstile> inst \<rho> (f' $ u') : T" using a(3)[OF tf] b(3)[OF tu] by auto
  then show "e \<turnstile> inst \<rho> (f' $ u') : T" .
  show "ap \<rho> \<sigma> (f $ u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (f' $ u')" if sol: "solution \<rho> \<sigma> env" for \<sigma>
    using conv_App[OF _ _ a(4)[OF tf sol] b(4)[OF tu sol]] wt_ap[OF ty solutionD(3)[OF sol]]
      wt_ap[OF ty' solutionD(3)[OF sol]] by simp
qed

lemma nsound_lookup:
  assumes "vt_lookup (tenv env) x = Some (U, u)" "tsubst \<rho> T = tsubst \<rho> U" "wt_env \<rho> env"
  shows "nsound \<rho> env (Var x T) u"
  unfolding nsound_def
proof (intro conjI allI impI)
  show "vsim \<rho> (vars u) (vars (Var x T) \<union> evars env)"
    using evarsI2[OF assms(1)] by (intro vsim_subset) auto
  show "\<not> loose_bvar u k" if "0 \<le> k" for k
    using wt_env_closed[OF assms(3,1)] that by (simp add: closed_loose_bvar)
  fix e V assume "e \<turnstile> inst \<rho> (Var x T) : V"
  then have V: "V = tsubst \<rho> T" by auto
  show "e \<turnstile> inst \<rho> u : V" using wt_envD[OF assms(3,1)] V assms(2) by simp
  show "ap \<rho> \<sigma> (Var x T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "solution \<rho> \<sigma> env" for \<sigma>
    using solutionD(4)[OF that assms(1)] assms(2) by simp
qed

lemma nsound_redex:
  "nsound \<rho> env (body[u/0]) t' \<Longrightarrow> nsound \<rho> env (Abs b U body $ u) t'"
  by (rule nsound_trans[OF nsound_beta])

lemma norm_term1_sound:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> nsound \<rho> env t t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and wte = "1.prems"(3)
  have IH: "nsound \<rho> env u u'" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te wte] .
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
      from rest Some have "ok (nt te u) t'" by simp
      from nsound_trans[OF nsound_lookup[OF lk refl wte] IH[OF this]] Var show ?thesis by simp
    qed (use rest in \<open>simp add: nsound_refl\<close>)
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with nsound_Abs[OF IH[OF this(1)] refl] Abs show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (nt te (subst_bound u body)) t'" by simp
      from nsound_redex[OF IH[OF this[unfolded subst_bound_subst]]] App f show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      have c: "nsound \<rho> env (f $ u) (nf $ u)" by (rule nsound_App[OF IH[OF hf] nsound_refl])
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        from nsound_trans[OF c[unfolded nf] nsound_redex[OF IH[OF this[unfolded subst_bound_subst]]]] App
        show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt te u) nu" and t': "t' = nf $ nu"
          by (cases nf) auto
        from nsound_App[OF IH[OF hf] IH[OF hu]] App t' show ?thesis by simp
      qed
    qed
  qed (use h in \<open>simp_all add: nsound_refl\<close>)
qed

lemma nsound_Var_type:
  "tsubst \<rho> T' = tsubst \<rho> T \<Longrightarrow> nsound \<rho> env (Var x T) (Var x T')"
  by (rule nsound_inst) (auto simp: vsim_def)

lemma norm_term2_sound:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> nsound \<rho> env t t'"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and tsol = "1.prems"(2) and wte = "1.prems"(3)
  have IH: "nsound \<rho> env u u'" if "ok (nt env u) u'" for u u'
    using "1.IH"[OF that refl tsol wte] .
  have nty: "tsubst \<rho> T' = tsubst \<rho> T" if "ok (norm_type_aux (tyenv env) T) T'" for T T'
    using norm_type_aux_sound[OF that refl tsol] .
  show ?case
  proof (cases t)
    case (Const a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Const a T'" by auto
    with nty[OF this(1)] Const show ?thesis by (intro nsound_inst) (auto simp: vsim_def)
  next
    case (Free a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Free a T'" by auto
    with nty[OF this(1)] Free show ?thesis by (intro nsound_inst) (auto simp: vsim_def)
  next
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      from lr Some obtain U where lk: "vt_lookup (tenv env) x = Some (U, u)"
        and un: "ok (unified (tyenv env) T U) True" by (auto elim: ok_lookup_Some)
      from rest Some have "ok (nt env u) t'" by simp
      from nsound_trans[OF nsound_lookup[OF lk unified_sound[OF un tsol] wte] IH[OF this]] Var
      show ?thesis by simp
    next
      case None
      with rest obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Var x T'" by auto
      with nsound_Var_type[OF nty[OF this(1)]] Var show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (norm_type_aux (tyenv env) T) T'" "ok (nt env body) body'"
      "t' = Abs a T' body'" by auto
    with nsound_Abs[OF IH[OF this(2)] nty[OF this(1)]] Abs show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      from nsound_redex[OF IH[OF this[unfolded subst_bound_subst]]] App f show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      have c: "nsound \<rho> env (f $ u) (nf $ u)" by (rule nsound_App[OF IH[OF hf] nsound_refl])
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        from nsound_trans[OF c[unfolded nf] nsound_redex[OF IH[OF this[unfolded subst_bound_subst]]]] App
        show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu"
          by (cases nf) auto
        from nsound_App[OF IH[OF hf] IH[OF hu]] App t' show ?thesis by simp
      qed
    qed
  qed (use h in \<open>simp_all add: nsound_refl\<close>)
qed

lemma norm_term_sound:
  assumes "ok (norm_term env t) t'" "tsol (tyenv env) \<rho>" "wt_env \<rho> env"
  shows "nsound \<rho> env t t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    with assms(1) show ?thesis by (simp add: norm_term_def nsound_refl)
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_sound[OF this refl refl assms(3)] show ?thesis .
  next
    case n2
    with assms(1) have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_sound[OF this refl assms(2,3)] show ?thesis .
  qed
qed

text \<open>Normalizing both sides of a pair is a step:\<close>

lemma nsound_dstep:
  assumes "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> nsound \<rho> env t t' \<and> nsound \<rho> env u u'"
  shows "dstep env [(bs, t, u)] env [(bs, t', u')]"
proof (rule dstepI[OF extends_refl])
  fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext: "extends env env''"
    and wte: "wt_env \<rho> env" and d: "dtyped \<rho> [(bs, t, u)]" and v: "vinv \<rho> env (X \<union> dvars [(bs, t, u)])"
  have tsol: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol'' ext])
  note nt = nsoundD[OF conjunct1[OF assms[OF tsol wte]]] and nu = nsoundD[OF conjunct2[OF assms[OF tsol wte]]]
  from d obtain e T where bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
    and lb: "\<not> loose_bvar t (ilength bs)" "\<not> loose_bvar u (ilength bs)"
    by auto
  have "dtyped \<rho> [(bs, t', u')]"
    using bs nt(3)[OF ty(1)] nu(3)[OF ty(2)] nt(2)[OF ilength_nonneg lb(1)] nu(2)[OF ilength_nonneg lb(2)]
    by auto
  moreover have "vinv \<rho> env (X \<union> dvars [(bs, t', u')])"
  proof -
    have "vsim \<rho> (vars t' \<union> vars u') ((vars t \<union> vars u) \<union> evars env)"
      using nt(1) nu(1) by (intro vsim_Un) (auto elim: vsim_mono)
    from vinv_vsim[OF _ this] v show ?thesis by (simp add: Un_ac)
  qed
  moreover have "dsolved \<rho> \<sigma> [(bs, t, u)]" if sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> [(bs, t', u')]"
    for \<sigma>
  proof -
    have sol0: "solution \<rho> \<sigma> env" by (rule solution_extends[OF sol ext])
    from ds have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" by simp
    with nt(4)[OF ty(1) sol0] nu(4)[OF ty(2) sol0] show ?thesis by (simp, meson conv_sym conv_trans)
  qed
  ultimately show "wt_env \<rho> env \<and> dtyped \<rho> [(bs, t', u')] \<and> vinv \<rho> env (X \<union> dvars [(bs, t', u')]) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> [(bs, t', u')] \<longrightarrow> dsolved \<rho> \<sigma> [(bs, t, u)])"
    using wte by blast
qed

lemma norm_term_dstep:
  "ok (norm_term env t) t' \<Longrightarrow> ok (norm_term env u) u' \<Longrightarrow> dstep env [(bs, t, u)] env [(bs, t', u')]"
  by (rule nsound_dstep) (blast intro: norm_term_sound)


subsection \<open>Assignments\<close>

text \<open>The conditions under which an assignment \<open>x := t\<close> is sound at \<open>\<rho>\<close>, and its effect:\<close>

definition asound :: "env \<Rightarrow> indexname \<times> ptyp \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "asound env aU t env' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> env'' X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow> closed t \<longrightarrow>
      (\<forall>e. e \<turnstile> inst \<rho> t : tsubst \<rho> (snd aU)) \<longrightarrow> vinv \<rho> env (X \<union> insert aU (vars t)) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> \<sigma> (fst aU) (tsubst \<rho> (snd aU)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t))"

lemma asoundD:
  assumes "asound env aU t env'"
  shows "extends env env'"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> closed t \<Longrightarrow>
      (\<And>e. e \<turnstile> inst \<rho> t : tsubst \<rho> (snd aU)) \<Longrightarrow> vinv \<rho> env (X \<union> insert aU (vars t)) \<Longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> \<sigma> (fst aU) (tsubst \<rho> (snd aU)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
  using assms unfolding asound_def by blast+

lemma update_asound:
  assumes upd: "ok (update aU t env) env'"
  shows "asound env aU t env'"
proof -
  obtain F T where aU: "aU = (F, T)" by (cases aU)
  note upd = upd[unfolded aU]
  have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> \<sigma> F (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
    if ext': "extends env' env''" and wte: "wt_env \<rho> env" and cl: "closed t"
      and ty: "\<And>e. e \<turnstile> inst \<rho> t : tsubst \<rho> T" and vi: "vinv \<rho> env (X \<union> insert (F, T) (vars t))"
    for \<rho> env'' X
  proof -
    have "wt_env \<rho> env'" using wt_env_update[OF upd wte cl ty] .
    moreover have "vinv \<rho> env' X" using vinv_update[OF upd vi] .
    moreover have "\<sigma> F (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" if "solution \<rho> \<sigma> env''" for \<sigma>
      using solution_update[OF upd solution_extends[OF that ext']] .
    ultimately show ?thesis by blast
  qed
  with extends_update[OF upd] show ?thesis unfolding asound_def aU by simp
qed

lemma vupdate_asound:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> asound env aU t env'"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  obtain v T0 where aU: "aU = (v, T0)" by (cases aU)
  have IH: "asound env aU u env'" if "ok (vu aU u env) env'" for u
    using "1.IH"[OF that refl] .
  have up: "ok (case t of
      Var name' T \<Rightarrow>
        if fst aU = name' then return env
        else if indexname_less (fst aU) name' then lookup env name' T \<bind> (\<lambda>r.
          case r of None \<Rightarrow> update (name', T) (Var (fst aU) T) env | Some u \<Rightarrow> vu aU u env)
        else update aU t env
    | _ \<Rightarrow> update aU t env) env'"
    using "1.hyps" "1.prems" by simp
  show ?case
  proof (cases t)
    case (Var name' T)
    have tyT: "tsubst \<rho> T = tsubst \<rho> T0 \<and> cert_typ alg ar (tsubst \<rho> T)"
      if "\<And>e. e \<turnstile> inst \<rho> t : tsubst \<rho> (snd aU)" for \<rho>
      using that[of undefined] Var aU by auto
    consider "v = name'" | "v \<noteq> name'" "indexname_less v name'" | "v \<noteq> name'" "\<not> indexname_less v name'"
      by blast
    then show ?thesis
    proof cases
      case 1
      with up Var aU have env': "env' = env" by simp
      have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
          (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> \<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
        if "wt_env \<rho> env" "vinv \<rho> env (X \<union> insert aU (vars t))" for \<rho> env'' X
      proof -
        have "vinv \<rho> env (X \<union> {(v, T0), (v, T)})" using that(2) Var aU 1 by (simp add: insert_commute)
        from vinv_FG[OF this] vinv_mono[OF that(2), of X] that(1) env' Var 1 show ?thesis by auto
      qed
      with env' aU show ?thesis unfolding asound_def by simp
    next
      case 2
      with up Var aU obtain lr where lk: "ok (lookup env name' T) lr"
        and rest: "ok (case lr of None \<Rightarrow> update (name', T) (Var v T) env | Some u \<Rightarrow> vu aU u env) env'"
        by auto
      show ?thesis
      proof (cases lr)
        case None
        with rest have upd: "ok (update (name', T) (Var v T) env) env'" by simp
        note a = asoundD[OF update_asound[OF upd]]
        have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
            (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> \<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
          if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
            and ty: "\<And>e. e \<turnstile> inst \<rho> t : tsubst \<rho> (snd aU)"
            and vi: "vinv \<rho> env (X \<union> insert aU (vars t))" for \<rho> env'' X
        proof -
          note TT = tyT[OF ty]
          have ty': "e \<turnstile> inst \<rho> (Var v T) : tsubst \<rho> (snd (name', T))" for e
            using TT by auto
          have "vsim \<rho> (insert (name', T) (vars (Var v T))) (insert aU (vars t) \<union> evars env)"
            using TT Var aU by (auto simp: vsim_def)
          from vinv_vsim[OF vi this] have vi': "vinv \<rho> env (X \<union> insert (name', T) (vars (Var v T)))" .
          from a(2)[OF tsol'' ext' wte _ ty' vi'] have r: "wt_env \<rho> env'" "vinv \<rho> env' X"
            "\<And>\<sigma>. solution \<rho> \<sigma> env'' \<Longrightarrow> \<sigma> name' (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (tsubst \<rho> T)"
            by (auto simp: closed_def)
          have "\<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" if "solution \<rho> \<sigma> env''" for \<sigma>
            using conv_sym[OF r(3)[OF that]] TT Var by simp
          with r(1,2) show ?thesis by blast
        qed
        with a(1) aU show ?thesis unfolding asound_def by simp
      next
        case (Some u)
        from lk Some obtain U where lku: "vt_lookup (tenv env) name' = Some (U, u)"
          and un: "ok (unified (tyenv env) T U) True" by (auto elim: ok_lookup_Some)
        from rest Some have "ok (vu aU u env) env'" by simp
        note a = asoundD[OF IH[OF this]]
        have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
            (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> \<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
          if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
            and ty: "\<And>e. e \<turnstile> inst \<rho> t : tsubst \<rho> (snd aU)"
            and vi: "vinv \<rho> env (X \<union> insert aU (vars t))" for \<rho> env'' X
        proof -
          note TT = tyT[OF ty]
          have ext1: "extends env env''" by (rule extends_trans[OF a(1) ext'])
          have TU: "tsubst \<rho> T = tsubst \<rho> U" by (rule unified_sound[OF un extends_tsol[OF tsol'' ext1]])
          have ty': "e \<turnstile> inst \<rho> u : tsubst \<rho> (snd aU)" for e
            using wt_envD[OF wte lku] TT TU aU by simp
          have "vinv \<rho> env (X \<union> insert aU (vars u))"
            using vinv_hn[OF vi] evarsI2[OF lku] by blast
          from a(2)[OF tsol'' ext' wte wt_env_closed[OF wte lku] ty' this]
          have r: "wt_env \<rho> env'" "vinv \<rho> env' X"
            "\<And>\<sigma>. solution \<rho> \<sigma> env'' \<Longrightarrow> \<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
            using aU by auto
          have "\<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
          proof -
            have "\<sigma> name' (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
              by (rule solutionD(4)[OF solution_extends[OF sol ext1] lku])
            with r(3)[OF sol] TU Var show ?thesis by (simp, meson conv_sym conv_trans)
          qed
          with r(1,2) show ?thesis by blast
        qed
        with a(1) aU show ?thesis unfolding asound_def by simp
      qed
    next
      case 3
      with up Var aU have "ok (update aU t env) env'" by simp
      then show ?thesis by (rule update_asound)
    qed
  qed (use up update_asound in auto)
qed

text \<open>Solving a pair whose left-hand side is \<open>\<eta>\<close>-equivalent to a variable by a sound assignment
  (as @{thm [source] eta_var_step}, for \<^const>\<open>vupdate\<close>):\<close>

lemma eta_var_asound_step:
  assumes gev: "okW (get_eta_var bs 0 s) (F, Fty)" and upd: "asound env (F, Fty) (rlist_abs bs t) env'"
  shows "step_ok env bs s t env'"
proof -
  define "is" where "is = rev (map integer_of_nat [0..<length bs])"
  have s: "s = app (Var F Fty) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have is_ok: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    by (auto simp: is_def ilength_eq integer_of_nat_eq_of_nat)
  have mb: "map (\<lambda>i. bs ! nat_of_integer i) is = rev bs"
    by (simp add: is_def rev_map[symmetric] map_nth comp_def)
  define u' where "u' = rlist_abs bs t"
  have u': "u' = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t"
    by (simp add: u'_def mb rlist_abs_abs_list)
  have pj: "ok (proj t env bs is) (t, env)"
    using downto0_upt[of "length bs"] by (simp add: proj_def is_def ilength_eq)
  note upd = upd[folded u'_def]
  have ext: "extends env env'" using asoundD(1)[OF upd] .
  moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
    if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
      and bs: "bs_env \<rho> e bs" and tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T" and tyt: "e \<turnstile> inst \<rho> t : T"
      and vi: "vinv \<rho> env (X \<union> vars (app (Var F Fty) is) \<union> vars t)"
      and lbt: "\<not> loose_bvar t (ilength bs)"
    for \<rho> env'' e T X
  proof -
    have ext1: "extends env env''" using extends_trans[OF ext ext'] .
    have vi': "vinv \<rho> env ((X \<union> {(F, Fty)}) \<union> vars t)" using vi by (simp add: Un_ac)
    have is0: "\<forall>i\<in>set is. 0 \<le> i" using is_ok by blast
    note r = proj_sound(2)[OF pj is0 tsol'' ext1 wte bs tyt vi' lbt]
    from tyF obtain Fty_eq: "tsubst \<rho> Fty = map e is \<Rrightarrow> T" by (rule typing_appE)
    note bt = bs_types[OF bs is_ok]
    let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)"
    have tu': "e' \<turnstile> inst \<rho> u' : tsubst \<rho> Fty" for e'
    proof -
      from r have "pushes e' (map e is) \<turnstile> inst \<rho> t : T" by blast
      then have "pushes e' (map snd ?bs) \<turnstile> inst \<rho> t : T" by (simp only: bt(1))
      from typing_abs_list[OF this bt(2)] have "e' \<turnstile> abs_list ?bs (inst \<rho> t) : map e is \<Rrightarrow> T"
        by (simp only: bt(1))
      then show ?thesis by (simp only: u' inst_abs_list Fty_eq)
    qed
    have cl: "closed u'" using r by (auto simp: u' intro!: closed_abs_list)
    have "vinv \<rho> env (X \<union> insert (F, Fty) (vars u'))" using vi by (simp add: u' Un_ac)
    from asoundD(2)[OF upd tsol'' ext' wte cl _ this] tu'
    have a: "wt_env \<rho> env'" "vinv \<rho> env' X"
      "\<And>\<sigma>. solution \<rho> \<sigma> env'' \<Longrightarrow> \<sigma> F (tsubst \<rho> Fty) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
      by auto
    have "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
    proof -
      note s = solutionD[OF sol]
      have js: "e \<tturnstile> map Bound is : map e is" by (rule typings_Bounds) (use is0 in auto)
      have tu: "e \<turnstile> ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is : T"
        using typing_ap[OF tu' s(3)] Fty_eq js by (auto intro: list_app_typeI)
      have "ap \<rho> \<sigma> (app (Var F Fty) is) = \<sigma> F (tsubst \<rho> Fty) \<degree>\<degree> map Bound is"
        by (simp add: app_apps ap_apps comp_def)
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is"
      proof (rule conv_apps)
        show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map Bound is) (map Bound is)" by (simp add: list_all2_refl)
        show "wt (\<sigma> F (tsubst \<rho> Fty) \<degree>\<degree> map Bound is)"
          using wt_ap[OF tyF s(3)] by (simp add: app_apps ap_apps comp_def)
        show "wt (ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is)" using tu by (auto simp: wt_def)
        show "\<sigma> F (tsubst \<rho> Fty) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" by (rule a(3)[OF sol])
      qed
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> t)"
      proof (rule conv_beta_eta)
        show "wt (ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is)" using tu by (auto simp: wt_def)
        show "ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev is)) 0 (ap \<rho> \<sigma> t)"
          using beta_abs_list_apps[of "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)" "is"] is0
          by (simp add: u' ap_abs_list)
      qed
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" using r sol by (blast intro: conv_sym)
      finally show ?thesis .
    qed
    with a(1,2) show ?thesis by blast
  qed
  ultimately show ?thesis unfolding step_ok_def s by blast
qed

text \<open>
  A flex-flex assignment solves the pair. As for @{thm [source] assignment_sound}, neither the
  occurs check nor the unification of the types is needed for soundness.
\<close>

theorem ff_assign_sound:
  assumes "okW (ff_assign alg' env bs t u) env'"
  shows "dstep env [(bs, t, u)] env' []"
proof -
  have "\<exists>v T T1 T2 env1. okW (get_eta_var bs 0 t) (v, T) \<and> okW (cunify_types alg' T1 T2 env) env1 \<and>
      ok (vupdate (v, T) (rlist_abs bs u) env1) env'"
    using assms by (auto simp: ff_assign_def split: if_splits)
  then obtain v T T1 T2 env1 where gev: "okW (get_eta_var bs 0 t) (v, T)"
    and cu: "okW (cunify_types alg' T1 T2 env) env1" and upd: "ok (vupdate (v, T) (rlist_abs bs u) env1) env'"
    by blast
  have "dstep env1 [(bs, t, u)] env' []"
    by (rule step_ok_dstep[OF eta_var_asound_step[OF gev vupdate_asound[OF upd refl]]])
  with cunify_types_dstep[OF cu] show ?thesis by (rule dstep_trans)
qed


subsection \<open>Remaining pairs\<close>

text \<open>The remaining flex-flex pairs are closed by their binders:\<close>

abbreviation tdps :: "(pterm \<times> pterm) list \<Rightarrow> dpair list" where
  "tdps tps \<equiv> map (\<lambda>(t, u). ([], t, u)) tps"

lemma aconv_term_ap: "aconv_term s t \<Longrightarrow> aconv_term (ap \<rho> \<sigma> s) (ap \<rho> \<sigma> t)"
  by (induction s t rule: aconv_term.induct) (auto simp: aconv_term_unname)

lemma conv_abs_list_inv:
  "e \<turnstile> abs_list bs s : V \<Longrightarrow> e \<turnstile> abs_list bs t : V \<Longrightarrow> abs_list bs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs t \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
proof (induction bs arbitrary: e V)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by (cases b)
  from Cons.prems(1) b obtain U where V: "V = T \<rightarrow>\<^sub>T U" and ts: "e\<langle>0:T\<rangle> \<turnstile> abs_list bs s : U" by auto
  from Cons.prems(2) b V have tt: "e\<langle>0:T\<rangle> \<turnstile> abs_list bs t : U" by auto
  from conv_Abs_inv(2)[of e x T "abs_list bs s" V x T "abs_list bs t"] Cons.prems b
  have "abs_list bs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs t" by simp
  from Cons.IH[OF ts tt this] show ?case .
qed simp

lemma rlist_abs_typing:
  assumes "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "\<not> loose_bvar t (ilength rb)"
  shows "e' \<turnstile> inst \<rho> (rlist_abs rb t) : map (\<lambda>(x, T). tsubst \<rho> T) (rev rb) \<Rrightarrow> T"
    and "\<not> loose_bvar (rlist_abs rb t) 0"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)"
  have ms: "map snd ?bs = map (\<lambda>(x, T). tsubst \<rho> T) (rev rb)" by (auto simp: split_def)
  have "pushes e' (map snd ?bs) \<turnstile> inst \<rho> t : T"
  proof (rule typing_env_cong[OF assms(2)])
    fix i assume i: "0 \<le> i" "loose_bvar1 (inst \<rho> t) i"
    then have "loose_bvar t i" by (simp add: loose_bvar1_imp)
    with assms(3) have il: "i < ilength rb" using loose_bvar_mono[of t i "ilength rb"] by fastforce
    then have n: "nat_of_integer i < length rb" using i(1) by (simp add: nat_of_integer_less_ilength)
    have "pushes e' (map snd ?bs) i = rev (map snd ?bs) ! nat_of_integer i"
      using pushes_nth[OF i(1)] il by simp
    also have "\<dots> = tsubst \<rho> (snd (rb ! nat_of_integer i))"
      using n by (simp add: ms rev_map split_def)
    also have "\<dots> = e i" using assms(1) i(1) il by (simp add: bs_env_def)
    finally show "pushes e' (map snd ?bs) i = e i" .
  qed
  moreover have "\<forall>U\<in>snd ` set ?bs. cert_typ alg ar U" using assms(1) by (auto simp: bs_env_def)
  ultimately have "e' \<turnstile> abs_list ?bs (inst \<rho> t) : map snd ?bs \<Rrightarrow> T" by (rule typing_abs_list)
  then show "e' \<turnstile> inst \<rho> (rlist_abs rb t) : map (\<lambda>(x, T). tsubst \<rho> T) (rev rb) \<Rrightarrow> T"
    unfolding ms by (simp only: rlist_abs_abs_list inst_abs_list)
  show "\<not> loose_bvar (rlist_abs rb t) 0"
    using assms(3) by (simp add: rlist_abs_abs_list loose_bvar_abs_list)
qed

lemma rlist_abs_conv:
  assumes "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
    "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)" "wt_subst \<sigma>"
    "ap \<rho> \<sigma> (rlist_abs rb t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs rb u)"
  shows "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)"
  have ap: "ap \<rho> \<sigma> (rlist_abs rb s) = abs_list ?bs (ap \<rho> \<sigma> s)" for s
    by (simp add: rlist_abs_abs_list ap_abs_list)
  from rlist_abs_typing(1)[OF assms(1,2,4), of e] rlist_abs_typing(1)[OF assms(1,3,5), of e]
  show ?thesis using conv_abs_list_inv[of e ?bs "ap \<rho> \<sigma> t"] assms(6,7)
    by (simp add: ap) (metis ap typing_ap)
qed

lemma vars_rlist_abs [simp]: "vars (rlist_abs rb t) = vars t"
  by (simp add: rlist_abs_abs_list)

lemma dsolved_tdps: "dsolved \<rho> \<sigma> (tdps tps) \<longleftrightarrow> (\<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"
  by (auto simp: dsolved_def)

theorem add_tpair_sound: "dstep env ((rb, t, u) # tdps tps) env (tdps (add_tpair rb t u tps))"
proof (rule dstepI[OF extends_refl])
  fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext: "extends env env''"
    and wte: "wt_env \<rho> env" and d: "dtyped \<rho> ((rb, t, u) # tdps tps)"
    and v: "vinv \<rho> env (X \<union> dvars ((rb, t, u) # tdps tps))"
  from d obtain e T where bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
    and lb: "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)" and d': "dtyped \<rho> (tdps tps)"
    by auto
  let ?t = "rlist_abs rb t" and ?u = "rlist_abs rb u"
  have sol_closed: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "solution \<rho> \<sigma> env''" "ap \<rho> \<sigma> ?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> ?u" for \<sigma>
    using rlist_abs_conv[OF bs ty lb solutionD(3)[OF that(1)] that(2)] .
  have v': "vinv \<rho> env (X \<union> dvars (tdps tps))" using v by (rule vinv_mono) auto
  consider (ac) "aconv_term t u"
    | (dup) "\<not> aconv_term t u" "\<exists>(t', u')\<in>set tps. aconv_term ?t t' \<and> aconv_term ?u u'"
    | (new) "\<not> aconv_term t u" "\<not> (\<exists>(t', u')\<in>set tps. aconv_term ?t t' \<and> aconv_term ?u u')"
    by blast
  then show "wt_env \<rho> env \<and> dtyped \<rho> (tdps (add_tpair rb t u tps)) \<and>
      vinv \<rho> env (X \<union> dvars (tdps (add_tpair rb t u tps))) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> (tdps (add_tpair rb t u tps)) \<longrightarrow>
        dsolved \<rho> \<sigma> ((rb, t, u) # tdps tps))"
  proof cases
    case ac
    then have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" for \<sigma> by (intro aconv_term_conv aconv_term_ap)
    with ac wte d' v' show ?thesis by (simp add: add_tpair_def)
  next
    case dup
    then obtain t' u' where tu: "(t', u') \<in> set tps" "aconv_term ?t t'" "aconv_term ?u u'" by blast
    have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> (tdps tps)" for \<sigma>
    proof (rule sol_closed[OF sol])
      from ds tu(1) have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" unfolding dsolved_def by force
      with aconv_term_conv[OF aconv_term_ap[OF tu(2)]] aconv_term_conv[OF aconv_term_ap[OF tu(3)]]
      show "ap \<rho> \<sigma> ?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> ?u" by (meson conv_sym conv_trans)
    qed
    with dup wte d' v' show ?thesis by (simp add: add_tpair_def Let_def)
  next
    case new
    then have r: "add_tpair rb t u tps = (?t, ?u) # tps" by (simp add: add_tpair_def Let_def)
    have "dtyped \<rho> [([], ?t, ?u)]"
      using rlist_abs_typing[OF bs ty(1) lb(1)] rlist_abs_typing[OF bs ty(2) lb(2)]
      by (auto simp: bs_env_def)
    moreover have "vinv \<rho> env (X \<union> dvars (tdps (add_tpair rb t u tps)))"
      using v by (simp add: r Un_ac)
    ultimately show ?thesis using wte d' sol_closed by (simp add: r)
  qed
qed


subsection \<open>Deleting bound variables\<close>

text \<open>
  \<open>change_bnos banned\<close> deletes the banned loose bound variables and renames the others by
  \<open>sqz banned\<close>, which subtracts the number of banned variables below. The binders that are
  kept by \<open>clean_ffpair\<close> are those at the positions that are not banned; a renaming \<open>F\<close>
  maps the new positions back to the old ones.
\<close>

definition sqz :: "integer list \<Rightarrow> integer \<Rightarrow> integer" where
  "sqz banned j = j - ilength (filter (\<lambda>i. i < j) banned)"

lemma add_index_fold:
  assumes "foldr (add_index lt lu) (zip (map integer_of_nat [k..<k + length xs]) xs) ([], []) = (bn, rb')"
  shows "\<exists>keep. rb' = map (\<lambda>j. xs ! (j - k)) keep \<and>
    set bn \<union> integer_of_nat ` set keep = integer_of_nat ` {k..<k + length xs} \<and>
    set bn \<inter> integer_of_nat ` set keep = {} \<and>
    (\<forall>p<length keep. sqz bn (integer_of_nat (keep ! p)) = integer_of_nat (k + p))"
  using assms
proof (induction xs arbitrary: k bn rb')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain bn1 rb1 where f: "foldr (add_index lt lu) (zip (map integer_of_nat [Suc k..<Suc k + length xs]) xs)
      ([], []) = (bn1, rb1)"
    by (cases "foldr (add_index lt lu) (zip (map integer_of_nat [Suc k..<Suc k + length xs]) xs) ([], [])")
  from Cons.IH[OF f] obtain keep1 where rb1: "rb1 = map (\<lambda>j. xs ! (j - Suc k)) keep1"
    and un: "set bn1 \<union> integer_of_nat ` set keep1 = integer_of_nat ` {Suc k..<Suc k + length xs}"
    and di: "set bn1 \<inter> integer_of_nat ` set keep1 = {}"
    and sq: "\<forall>p<length keep1. sqz bn1 (integer_of_nat (keep1 ! p)) = integer_of_nat (Suc k + p)"
    by blast
  have z: "zip (map integer_of_nat [k..<k + length (x # xs)]) (x # xs) =
      (integer_of_nat k, x) # zip (map integer_of_nat [Suc k..<Suc k + length xs]) xs"
    by (simp add: upt_conv_Cons del: upt_Suc)
  from Cons.prems have st: "add_index lt lu (integer_of_nat k, x) (bn1, rb1) = (bn, rb')"
    by (simp only: z foldr.simps comp_def f)
  have bn1_ge: "integer_of_nat k < i" if "i \<in> set bn1" for i
  proof -
    from that un have "i \<in> integer_of_nat ` {Suc k..<Suc k + length xs}" by blast
    then obtain j where "j \<in> {Suc k..<Suc k + length xs}" "i = integer_of_nat j" by blast
    then show ?thesis by (simp add: integer_of_nat_eq_of_nat)
  qed
  have keep1_ge: "Suc k \<le> j \<and> j < Suc k + length xs" if "j \<in> set keep1" for j
  proof -
    from that un have "integer_of_nat j \<in> integer_of_nat ` {Suc k..<Suc k + length xs}" by blast
    then obtain j' where "j' \<in> {Suc k..<Suc k + length xs}" "integer_of_nat j = integer_of_nat j'" by blast
    then show ?thesis by (simp add: integer_of_nat_eq_of_nat)
  qed
  have nth: "(x # xs) ! (j - k) = xs ! (j - Suc k)" if "j \<in> set keep1" for j
    using keep1_ge[OF that] by (simp add: nth_Cons')
  have f0: "filter (\<lambda>i. i < integer_of_nat k) bn1 = []"
    using bn1_ge by (auto simp: filter_empty_conv not_less less_imp_le)
  show ?case
  proof (cases "integer_of_nat k \<in> set lt \<and> integer_of_nat k \<in> set lu")
    case True
    with st have bn: "bn = bn1" and rb': "rb' = x # rb1" by (simp_all add: add_index_def)
    show ?thesis
    proof (intro exI[of _ "k # keep1"] conjI allI impI)
      show "rb' = map (\<lambda>j. (x # xs) ! (j - k)) (k # keep1)" using rb' rb1 nth by simp
      show "set bn \<union> integer_of_nat ` set (k # keep1) = integer_of_nat ` {k..<k + length (x # xs)}"
        using un bn by (auto simp: image_iff integer_of_nat_eq_of_nat)
      show "set bn \<inter> integer_of_nat ` set (k # keep1) = {}" using di bn bn1_ge by auto
      fix p assume p: "p < length (k # keep1)"
      show "sqz bn (integer_of_nat ((k # keep1) ! p)) = integer_of_nat (k + p)"
      proof (cases p)
        case 0
        then show ?thesis using bn f0 by (simp add: sqz_def)
      next
        case (Suc q)
        with sq p bn show ?thesis by simp
      qed
    qed
  next
    case False
    with st have bn: "bn = integer_of_nat k # bn1" and rb': "rb' = rb1" by (auto simp: add_index_def)
    show ?thesis
    proof (intro exI[of _ keep1] conjI allI impI)
      show "rb' = map (\<lambda>j. (x # xs) ! (j - k)) keep1" using rb' rb1 nth by simp
      show "set bn \<union> integer_of_nat ` set keep1 = integer_of_nat ` {k..<k + length (x # xs)}"
        using un bn by (auto simp: image_iff integer_of_nat_eq_of_nat)
      show "set bn \<inter> integer_of_nat ` set keep1 = {}"
        using di bn keep1_ge[of k] by (auto simp: integer_of_nat_eq_of_nat)
      fix p assume p: "p < length keep1"
      have lt: "integer_of_nat k < integer_of_nat (keep1 ! p)"
        using keep1_ge[OF nth_mem[OF p]] by (simp add: integer_of_nat_eq_of_nat)
      from sq p have "sqz bn1 (integer_of_nat (keep1 ! p)) = integer_of_nat (Suc k + p)" by blast
      with lt show "sqz bn (integer_of_nat (keep1 ! p)) = integer_of_nat (k + p)"
        by (simp add: sqz_def bn ilength_eq integer_reps)
    qed
  qed
qed

text \<open>The renaming of the kept binders:\<close>

definition bren_ok :: "integer list \<Rightarrow> binders \<Rightarrow> binders \<Rightarrow> (integer \<Rightarrow> integer) \<Rightarrow> bool" where
  "bren_ok banned rb rb' F \<longleftrightarrow> nonneg F \<and>
    (\<forall>j. 0 \<le> j \<longrightarrow> j < ilength rb \<longrightarrow> j \<notin> set banned \<longrightarrow>
      F (sqz banned j) = j \<and> 0 \<le> sqz banned j \<and> sqz banned j < ilength rb') \<and>
    (\<forall>p. 0 \<le> p \<longrightarrow> p < ilength rb' \<longrightarrow>
      0 \<le> F p \<and> F p < ilength rb \<and> rb' ! nat_of_integer p = rb ! nat_of_integer (F p))"

lemma clean_binder:
  assumes "foldr (add_index lt lu) (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
  shows "\<exists>F. bren_ok banned rb rb' F"
proof -
  from add_index_fold[of lt lu 0 rb banned rb'] assms
  obtain keep where rb': "rb' = map (\<lambda>j. rb ! j) keep"
    and un: "set banned \<union> integer_of_nat ` set keep = integer_of_nat ` {0..<length rb}"
    and di: "set banned \<inter> integer_of_nat ` set keep = {}"
    and sq: "\<forall>p<length keep. sqz banned (integer_of_nat (keep ! p)) = integer_of_nat p"
    by (auto simp: upto_list_def)
  define F where "F p = (if 0 \<le> p \<and> p < ilength keep then integer_of_nat (keep ! nat_of_integer p) else p)"
    for p
  have lk: "length rb' = length keep" by (simp add: rb')
  have keep_lt: "j < length rb" if "j \<in> set keep" for j
  proof -
    from that un have "integer_of_nat j \<in> integer_of_nat ` {0..<length rb}" by blast
    then obtain j' where "j' < length rb" "integer_of_nat j = integer_of_nat j'" by auto
    then show ?thesis by (simp add: integer_of_nat_eq_of_nat)
  qed
  have "nonneg F" by (auto simp: nonneg_def F_def integer_of_nat_eq_of_nat)
  moreover have "F (sqz banned j) = j \<and> 0 \<le> sqz banned j \<and> sqz banned j < ilength rb'"
    if j: "0 \<le> j" "j < ilength rb" "j \<notin> set banned" for j
  proof -
    have "j \<in> integer_of_nat ` {0..<length rb}"
      using j(1,2) by (auto simp: image_iff ilength_eq integer_reps intro!: bexI[of _ "nat_of_integer j"])
    with un j(3) have "j \<in> integer_of_nat ` set keep" by blast
    then obtain q where q: "q < length keep" "j = integer_of_nat (keep ! q)"
      by (auto simp: in_set_conv_nth)
    from sq q have s: "sqz banned j = integer_of_nat q" by simp
    have "0 \<le> integer_of_nat q" "integer_of_nat q < ilength keep"
      using q(1) by (simp_all add: ilength_eq integer_of_nat_eq_of_nat)
    then show ?thesis using q s lk by (simp add: F_def ilength_eq)
  qed
  moreover have "0 \<le> F p \<and> F p < ilength rb \<and> rb' ! nat_of_integer p = rb ! nat_of_integer (F p)"
    if p: "0 \<le> p" "p < ilength rb'" for p
  proof -
    have q: "nat_of_integer p < length keep" using nat_of_integer_less_ilength[OF p] lk by simp
    have Fp: "F p = integer_of_nat (keep ! nat_of_integer p)" using p lk by (simp add: F_def ilength_eq)
    have "keep ! nat_of_integer p < length rb" using keep_lt[OF nth_mem[OF q]] .
    then show ?thesis using Fp q by (simp add: rb' ilength_eq integer_of_nat_eq_of_nat)
  qed
  ultimately show ?thesis unfolding bren_ok_def by blast
qed

lemma change_bnos_sound:
  assumes "okW (change_bnos banned lev s) s'" "0 \<le> lev" "0 \<le> m" "nonneg F" "\<not> loose_bvar s (lev + n)"
    "\<forall>j. 0 \<le> j \<longrightarrow> j < n \<longrightarrow> j \<notin> set banned \<longrightarrow> F (sqz banned j) = j \<and> 0 \<le> sqz banned j \<and> sqz banned j < m"
  shows "rename F lev s' = s \<and> \<not> loose_bvar s' (lev + m) \<and> vars s' = vars s \<and>
    (\<forall>e T. e \<turnstile> inst \<rho> s : T \<longrightarrow> renv e F lev \<turnstile> inst \<rho> s' : T)"
  using assms
proof (induction banned lev s arbitrary: s' rule: change_bnos.induct)
  case (1 banned lev i)
  show ?case
  proof (cases "i < lev")
    case True
    with "1.prems"(1) have s': "s' = Bound i" by simp
    show ?thesis using True "1.prems"(3) by (auto simp: s' renv_def integer_arith)
  next
    case False
    let ?j = "i - lev"
    from False "1.prems"(1) have nb: "?j \<notin> set banned" and s': "s' = Bound (sqz banned ?j + lev)"
      by (auto simp: sqz_def split: if_splits)
    have j: "0 \<le> ?j" "?j < n" using False "1.prems"(5) by (simp_all add: integer_arith)
    from "1.prems"(6) j nb have F: "F (sqz banned ?j) = ?j" "0 \<le> sqz banned ?j" "sqz banned ?j < m"
      by blast+
    have "rename F lev s' = Bound i" using F(1,2) by (simp add: s')
    moreover have "\<not> loose_bvar s' (lev + m)" using F(3) by (simp add: s' integer_arith)
    moreover have "renv e F lev \<turnstile> inst \<rho> s' : T" if "e \<turnstile> inst \<rho> (Bound i) : T" for e T
    proof -
      from that have "e i = T" by auto
      moreover have "renv e F lev (sqz banned ?j + lev) = e i"
      proof -
        have "\<not> sqz banned ?j + lev < lev" using F(2) by (simp add: integer_arith)
        then show ?thesis using F(1) by (simp add: renv_def)
      qed
      moreover have "0 \<le> sqz banned ?j + lev" using F(2) "1.prems"(2) by (simp add: integer_arith)
      ultimately show ?thesis by (auto simp: s')
    qed
    ultimately show ?thesis by (simp add: s')
  qed
next
  case (2 banned lev a T t)
  from "2.prems"(1) obtain t' where t': "okW (change_bnos banned (lev + 1) t) t'"
    and s': "s' = Abs a T t'" by auto
  have "\<not> loose_bvar t (lev + 1 + n)" using "2.prems"(5) by (simp add: algebra_simps)
  note IH = "2.IH"[OF t' _ "2.prems"(3,4) this "2.prems"(6)]
  have r: "rename F (lev + 1) t' = t" "\<not> loose_bvar t' (lev + 1 + m)" "vars t' = vars t"
    "\<And>e T. e \<turnstile> inst \<rho> t : T \<Longrightarrow> renv e F (lev + 1) \<turnstile> inst \<rho> t' : T"
    using IH "2.prems"(2) by (simp_all add: integer_arith)
  have "renv e F lev \<turnstile> inst \<rho> s' : V" if "e \<turnstile> inst \<rho> (Abs a T t) : V" for e V
  proof -
    from that obtain W where c: "cert_typ alg ar (tsubst \<rho> T)"
      and tb: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> t : W" and V: "V = tsubst \<rho> T \<rightarrow>\<^sub>T W" by auto
    from r(4)[OF tb] renv_shift[OF "2.prems"(4,2), of e "tsubst \<rho> T"]
    have "(renv e F lev)\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> t' : W" by simp
    with c V show ?thesis by (auto simp: s')
  qed
  with r(1-3) show ?case by (simp add: s' algebra_simps)
next
  case (3 banned lev t u)
  from "3.prems"(1) obtain t' u' where t': "okW (change_bnos banned lev t) t'"
    and u': "okW (change_bnos banned lev u) u'" and s': "s' = t' $ u'" by auto
  have lt: "\<not> loose_bvar t (lev + n)" and lu: "\<not> loose_bvar u (lev + n)" using "3.prems"(5) by simp_all
  note r1 = "3.IH"(1)[OF t' "3.prems"(2-4) lt "3.prems"(6)]
  note r2 = "3.IH"(2)[OF t' u' "3.prems"(2-4) lu "3.prems"(6)]
  have "renv e F lev \<turnstile> inst \<rho> s' : V" if "e \<turnstile> inst \<rho> (t $ u) : V" for e V
    using that r1 r2 by (auto simp: s')
  with r1 r2 show ?case by (simp add: s')
qed auto


subsection \<open>Applying an abstraction to terms\<close>

text \<open>Simultaneous substitution of the arguments for the binders:\<close>

fun ssub :: "pterm \<Rightarrow> pterm list \<Rightarrow> pterm" where
  "ssub u [] = u"
| "ssub u (s # ss) = ssub (u[incr_bv (ilength ss) 0 s/ilength ss]) ss"

lemma incr_bv_add: "0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> incr_bv n k (incr_bv m k t) = incr_bv (n + m) k t"
  by (induction t arbitrary: k) (auto simp: algebra_simps integer_arith)

lemma subst_abs_list:
  "(abs_list bs t)[s/k] = abs_list bs (t[incr_bv (ilength bs) 0 s/k + ilength bs])"
proof (induction bs arbitrary: s k)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by (cases b)
  have "incr_bv (ilength bs) 0 (lift s 0) = incr_bv (ilength bs + 1) 0 s"
    by (simp add: incr_bv_add)
  with Cons.IH[of "lift s 0" "k + 1"] b show ?case by (simp add: algebra_simps)
qed simp

lemma beta_abs_list_ssub: "length bs = length ss \<Longrightarrow> abs_list bs t \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta>\<^sup>* ssub t ss"
proof (induction ss arbitrary: bs t)
  case (Cons s ss)
  then obtain x T bs' where bs: "bs = (x, T) # bs'" and len: "length bs' = length ss"
    by (cases bs) auto
  have il: "ilength bs' = ilength ss" using len by (simp add: ilength_eq)
  have "abs_list bs t \<degree>\<degree> (s # ss) = (Abs x T (abs_list bs' t) $ s) \<degree>\<degree> ss" by (simp add: bs)
  also have "\<dots> \<rightarrow>\<^sub>\<beta> (abs_list bs' t)[s/0] \<degree>\<degree> ss" by (rule apps_preserves_beta) simp
  also have "(abs_list bs' t)[s/0] = abs_list bs' (t[incr_bv (ilength ss) 0 s/ilength ss])"
    by (simp add: subst_abs_list il)
  also have "abs_list bs' (t[incr_bv (ilength ss) 0 s/ilength ss]) \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta>\<^sup>* ssub t (s # ss)"
    using Cons.IH[OF len] by simp
  finally show ?case .
qed simp

lemma subst_incr_bv: "0 \<le> n \<Longrightarrow> 0 \<le> k \<Longrightarrow> (incr_bv (n + 1) k w)[x/n + k] = incr_bv n k w"
proof (induction w arbitrary: k x)
  case (Abs a T w)
  then show ?case using Abs.IH[of "k + 1" "lift x 0"] by (simp add: algebra_simps)
qed (auto simp: subst_Bound integer_arith)

lemma ssub_incr: "ssub (incr_bv (ilength ss) 0 w) ss = w"
proof (induction ss)
  case (Cons s ss)
  have "(incr_bv (ilength ss + 1) 0 w)[incr_bv (ilength ss) 0 s/ilength ss] = incr_bv (ilength ss) 0 w"
    using subst_incr_bv[of "ilength ss" 0 w] by simp
  with Cons.IH show ?case by simp
qed simp

lemma ssub_Bound: "0 \<le> k \<Longrightarrow> k < ilength ss \<Longrightarrow> ssub (Bound k) ss = rev ss ! nat_of_integer k"
proof (induction ss)
  case (Cons s ss)
  show ?case
  proof (cases "k = ilength ss")
    case True
    then have "nat_of_integer k = length (rev ss)" by (simp add: ilength_eq integer_reps)
    with True show ?thesis by (simp add: ssub_incr nth_append)
  next
    case False
    with Cons.prems have k: "k < ilength ss" by (simp add: integer_arith)
    then have "nat_of_integer k < length (rev ss)" using Cons.prems(1) by (simp add: nat_of_integer_less_ilength)
    with k Cons show ?thesis by (simp add: subst_Bound nth_append)
  qed
qed simp

lemma ssub_closed_apps: "closed G \<Longrightarrow> ssub (G \<degree>\<degree> us) ss = G \<degree>\<degree> map (\<lambda>u. ssub u ss) us"
proof (induction ss arbitrary: us)
  case (Cons s ss)
  have "(G \<degree>\<degree> us)[incr_bv (ilength ss) 0 s/ilength ss] = G \<degree>\<degree> map (\<lambda>u. u[incr_bv (ilength ss) 0 s/ilength ss]) us"
    using Cons.prems by (simp add: subst_apps subst_no_loose closed_loose_bvar)
  with Cons.IH[OF Cons.prems] show ?case by (simp add: comp_def)
qed simp

lemma beta_abs_list_select:
  assumes "closed G" "length bs = length ss" "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength ss"
  shows "abs_list bs (G \<degree>\<degree> map Bound ks) \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta>\<^sup>* G \<degree>\<degree> map (\<lambda>k. rev ss ! nat_of_integer k) ks"
proof -
  have m: "map (\<lambda>u. ssub u ss) (map Bound ks) = map (\<lambda>k. rev ss ! nat_of_integer k) ks"
    using assms(3) by (simp add: ssub_Bound)
  from beta_abs_list_ssub[OF assms(2), of "G \<degree>\<degree> map Bound ks"] show ?thesis
    by (simp only: ssub_closed_apps[OF assms(1)] m)
qed

lemma types_abs_abs_list: "types_abs Ts u = abs_list (map (\<lambda>T. (STR '''', T)) Ts) u"
  by (induction Ts) simp_all


subsection \<open>Cleaning terms\<close>

lemma typings_map: "(\<And>x. x \<in> set xs \<Longrightarrow> e \<turnstile> f x : g x) \<Longrightarrow> e \<tturnstile> map f xs : map g xs"
  by (induction xs) auto

lemma typings_nthI: "length xs = length Ys \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> e \<turnstile> xs ! i : Ys ! i) \<Longrightarrow> e \<tturnstile> xs : Ys"
proof (induction xs arbitrary: Ys)
  case (Cons x xs)
  then obtain Y Ys' where Ys: "Ys = Y # Ys'" by (cases Ys) auto
  from Cons.prems(2)[of 0] Cons.prems(2)[of "Suc i" for i] Cons.IH[of Ys'] Cons.prems(1) Ys
  show ?case by auto
qed simp

lemma flexargs_ok:
  "okW (flexargs js ts Ts) fas \<Longrightarrow>
    length js = length ts \<and> length Ts = length ts \<and>
    (\<forall>a\<in>set fas. \<exists>k<length ts. a = Flarg (js ! k) (ts ! k) (Ts ! k))"
proof (induction js ts Ts arbitrary: fas rule: flexargs.induct)
  case (2 j js t ts T Ts)
  then obtain args where "okW (flexargs js ts Ts) args" "fas = Flarg j t T # args" by auto
  with "2.IH"[OF this(1)] show ?case by (fastforce simp: nth_Cons')
qed auto

lemma foldrW_change_arg:
  "okW (foldrW (change_arg del banned) fas acc) cas \<Longrightarrow>
    \<forall>a'\<in>set cas. a' \<in> set acc \<or> (\<exists>a\<in>set fas. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and>
      okW (change_bnos banned 0 (fl_t a)) (fl_t a'))"
proof (induction fas arbitrary: cas)
  case (Cons a fas)
  then obtain cas1 where c1: "okW (foldrW (change_arg del banned) fas acc) cas1"
    and c: "okW (change_arg del banned a cas1) cas" by auto
  obtain j t T where a: "a = Flarg j t T" by (cases a)
  from c a have "cas = cas1 \<or> (\<exists>t'. okW (change_bnos banned 0 t) t' \<and> cas = Flarg j t' T # cas1)"
    by (auto simp: change_arg_def split: if_splits)
  with Cons.IH[OF c1] a show ?case by fastforce
qed simp

lemma set_ins_arg: "set (ins_arg x xs) = insert x (set xs)"
  by (induction xs) auto

lemma set_sort_args: "set (sort_args xs) = set xs"
  by (induction xs) (auto simp: set_ins_arg)

lemma not_decreasing_neg: "k < 0 \<Longrightarrow> \<not> decreasing k args"
  by (induction k args rule: decreasing.induct) auto

lemma decreasing_nth:
  "decreasing (integer_of_nat m) args \<Longrightarrow>
    length args = m \<and> (\<forall>p<m. fl_j (args ! p) = integer_of_nat (m - 1 - p))"
proof (induction args arbitrary: m)
  case Nil
  then show ?case by (simp add: integer_eq_iff)
next
  case (Cons a args)
  show ?case
  proof (cases m)
    case 0
    with Cons.prems not_decreasing_neg[of "-1" args] show ?thesis by (simp add: integer_of_nat_eq_of_nat)
  next
    case (Suc m')
    have m1: "integer_of_nat m - 1 = integer_of_nat m'" using Suc by (simp add: integer_eq_iff)
    with Cons.prems have "fl_j a = integer_of_nat m'" "decreasing (integer_of_nat m') args" by simp_all
    with Cons.IH[of m'] Suc show ?thesis by (auto simp: nth_Cons')
  qed
qed

lemma downto0_list_nth: "k < n \<Longrightarrow> downto0_list n ! k = integer_of_nat (n - 1 - k)"
  by (simp add: downto0_list_def rev_nth)

lemma clean_args:
  assumes fa: "okW (flexargs (downto0_list (length ts)) ts Ts) fas"
    and ca: "okW (foldrW (change_arg del banned) fas []) cas" and F: "bren_ok banned rb rb' F"
    and lb: "\<forall>s\<in>set ts. \<not> loose_bvar s (ilength rb)" and a: "a \<in> set (sort_args cas)"
  shows "\<exists>k<length ts. fl_j a = integer_of_nat (length ts - 1 - k) \<and> fl_T a = Ts ! k \<and>
    rename F 0 (fl_t a) = ts ! k \<and> \<not> loose_bvar (fl_t a) (ilength rb') \<and> vars (fl_t a) = vars (ts ! k) \<and>
    (\<forall>e T. e \<turnstile> inst \<rho> (ts ! k) : T \<longrightarrow> renv e F 0 \<turnstile> inst \<rho> (fl_t a) : T)"
proof -
  from flexargs_ok[OF fa] have fas: "\<forall>a\<in>set fas. \<exists>k<length ts.
      a = Flarg (downto0_list (length ts) ! k) (ts ! k) (Ts ! k)" by blast
  from a foldrW_change_arg[OF ca] obtain a0 where "a0 \<in> set fas" "fl_j a = fl_j a0"
    "fl_T a = fl_T a0" and cb: "okW (change_bnos banned 0 (fl_t a0)) (fl_t a)"
    by (auto simp: set_sort_args)
  with fas obtain k where k: "k < length ts" "fl_j a = integer_of_nat (length ts - 1 - k)"
    "fl_T a = Ts ! k" and cb: "okW (change_bnos banned 0 (ts ! k)) (fl_t a)"
    by (fastforce simp: downto0_list_nth)
  have lbk: "\<not> loose_bvar (ts ! k) (0 + ilength rb)" using lb k(1) by simp
  from F have nF: "nonneg F" and HF: "\<forall>j. 0 \<le> j \<longrightarrow> j < ilength rb \<longrightarrow> j \<notin> set banned \<longrightarrow>
      F (sqz banned j) = j \<and> 0 \<le> sqz banned j \<and> sqz banned j < ilength rb'"
    unfolding bren_ok_def by blast+
  from change_bnos_sound[where \<rho> = \<rho>, OF cb order_refl ilength_nonneg nF lbk HF]
  have "rename F 0 (fl_t a) = ts ! k \<and> \<not> loose_bvar (fl_t a) (ilength rb') \<and> vars (fl_t a) = vars (ts ! k) \<and>
      (\<forall>e T. e \<turnstile> inst \<rho> (ts ! k) : T \<longrightarrow> renv e F 0 \<turnstile> inst \<rho> (fl_t a) : T)"
    by simp
  with k show ?thesis by blast
qed


text \<open>The effect of cleaning a term, with the renaming \<open>F\<close> of the kept binders:\<close>

definition csound :: "env \<Rightarrow> binders \<Rightarrow> (integer \<Rightarrow> integer) \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> bool" where
  "csound env rb F rb' t env' t' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> env'' e T X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow> bs_env \<rho> e rb \<longrightarrow>
      e \<turnstile> inst \<rho> t : T \<longrightarrow> \<not> loose_bvar t (ilength rb) \<longrightarrow> vinv \<rho> env (X \<union> vars t) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> vars t') \<and> renv e F 0 \<turnstile> inst \<rho> t' : T \<and>
      \<not> loose_bvar t' (ilength rb') \<and> (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma> t')))"

lemma clean_term_sound:
  assumes ct: "okW (clean_term banned env t) (env', t')" and F: "bren_ok banned rb rb' F"
  shows "csound env rb F rb' t env' t'"
proof -
  obtain h ts where sc: "strip_comb t = (h, ts)" by (cases "strip_comb t")
  have "\<exists>v T0. h = Var v T0" using ct sc by (cases h) (auto simp: clean_term_def)
  then obtain v T0 where h: "h = Var v T0" by blast
  have t: "t = Var v T0 \<degree>\<degree> ts" using strip_comb_apps[OF sc] h by simp
  let ?n = "length ts"
  from ct sc h obtain Ts U fas cas where st: "ok (strip_type env T0) (Ts, U)"
    and fa: "okW (flexargs (downto0_list ?n) ts Ts) fas"
    and ca: "okW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) cas"
    and rest: "okW (let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T0) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')})) (env', t')"
    by (auto simp: clean_term_def Let_def split: prod.splits)
  define args where "args = sort_args cas"
  define ts' where "ts' = map fl_t args"
  have lTs: "length Ts = ?n" using flexargs_ok[OF fa] by simp
  have nF: "nonneg F" using F by (simp add: bren_ok_def)
  note A = clean_args[OF fa ca F, folded args_def]
  have lbts: "\<forall>s\<in>set ts. \<not> loose_bvar s (ilength rb)" if "\<not> loose_bvar t (ilength rb)"
    using that by (simp add: t loose_bvar_apps)
  have tyd: "cert_typ alg ar (tsubst \<rho> T0) \<and> tsubst \<rho> T0 = map (tsubst \<rho>) Ts \<Rrightarrow> T \<and> tsubst \<rho> U = T \<and>
      (\<forall>k<?n. e \<turnstile> inst \<rho> (ts ! k) : tsubst \<rho> (Ts ! k))"
    if tsol: "tsol (tyenv env) \<rho>" and ty: "e \<turnstile> inst \<rho> t : T" for \<rho> e T
  proof -
    from ty have "e \<turnstile> Var v (tsubst \<rho> T0) \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: t inst_apps)
    then obtain Us where tv: "e \<turnstile> Var v (tsubst \<rho> T0) : Us \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us"
      by (rule list_app_typeE)
    from tv have c: "cert_typ alg ar (tsubst \<rho> T0)" and eq: "tsubst \<rho> T0 = Us \<Rrightarrow> T" by auto
    from typings_nth[OF tts] have lu: "length Us = ?n" and nth: "\<forall>i<?n. e \<turnstile> inst \<rho> (ts ! i) : Us ! i"
      by simp_all
    from strip_type_sound[OF st tsol] eq have "map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> U = Us \<Rrightarrow> T" by simp
    with funs_eq[of "map (tsubst \<rho>) Ts" Us] lu lTs have UT: "map (tsubst \<rho>) Ts = Us" "tsubst \<rho> U = T" by simp_all
    with c eq nth lTs show ?thesis by auto
  qed
  show ?thesis
  proof (cases "decreasing (ilength Ts) args")
    case True
    with rest have env': "env' = env" and t': "t' = Var v T0 \<degree>\<degree> ts'"
      by (simp_all add: Let_def args_def ts'_def list_comb_apps)
    from decreasing_nth[of ?n args] True lTs have la: "length args = ?n"
      and dj: "\<forall>p<?n. fl_j (args ! p) = integer_of_nat (?n - 1 - p)" by (simp_all add: ilength_eq)
    have lts': "length ts' = ?n" using la by (simp add: ts'_def)
    have Ap: "rename F 0 (ts' ! p) = ts ! p \<and> \<not> loose_bvar (ts' ! p) (ilength rb') \<and> vars (ts' ! p) = vars (ts ! p) \<and>
        (\<forall>e T. e \<turnstile> inst \<rho> (ts ! p) : T \<longrightarrow> renv e F 0 \<turnstile> inst \<rho> (ts' ! p) : T)"
      if p: "p < ?n" and lbs: "\<forall>s\<in>set ts. \<not> loose_bvar s (ilength rb)" for p \<rho>
    proof -
      have "args ! p \<in> set args" using p la by simp
      from A[OF lbs this, where \<rho> = \<rho>] obtain k where k: "k < ?n"
        "fl_j (args ! p) = integer_of_nat (?n - 1 - k)"
        and r: "rename F 0 (fl_t (args ! p)) = ts ! k \<and> \<not> loose_bvar (fl_t (args ! p)) (ilength rb') \<and>
          vars (fl_t (args ! p)) = vars (ts ! k) \<and>
          (\<forall>e T. e \<turnstile> inst \<rho> (ts ! k) : T \<longrightarrow> renv e F 0 \<turnstile> inst \<rho> (fl_t (args ! p)) : T)"
        by blast
      from k(2) dj p have "integer_of_nat (?n - 1 - k) = integer_of_nat (?n - 1 - p)" by simp
      then have "?n - 1 - k = ?n - 1 - p" by (simp add: integer_of_nat_eq_of_nat)
      with k(1) p have "k = p" by linarith
      with r p la show ?thesis by (simp add: ts'_def)
    qed
    have rn: "rename F 0 t' = t" if lb: "\<not> loose_bvar t (ilength rb)"
    proof -
      have "map (rename F 0) ts' = ts"
        by (rule nth_equalityI) (use Ap[OF _ lbts[OF lb]] lts' in simp_all)
      then show ?thesis by (simp add: t t' rename_apps)
    qed
    show ?thesis unfolding csound_def
    proof (intro conjI allI impI)
      show "extends env env'" using env' by simp
      fix \<rho> env'' e T X assume tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''"
        and wte: "wt_env \<rho> env" and bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> t : T"
        and lb: "\<not> loose_bvar t (ilength rb)" and vi: "vinv \<rho> env (X \<union> vars t)"
      have tsol: "tsol (tyenv env) \<rho>" using extends_tsol[OF tsol''] ext' env' by simp
      note td = tyd[OF tsol ty] and lbs = lbts[OF lb]
      have vt: "vars t' = vars t" using rn[OF lb] vars_rename[of F 0 t'] by simp
      show "wt_env \<rho> env'" using wte env' by simp
      show "vinv \<rho> env' (X \<union> vars t')" using vi env' vt by simp
      show "renv e F 0 \<turnstile> inst \<rho> t' : T"
      proof -
        have "renv e F 0 \<tturnstile> map (inst \<rho>) ts' : map (tsubst \<rho>) Ts"
          by (rule typings_nthI) (use Ap[OF _ lbs] td lts' lTs in auto)
        moreover have "renv e F 0 \<turnstile> Var v (tsubst \<rho> T0) : map (tsubst \<rho>) Ts \<Rrightarrow> T" using td by auto
        ultimately show ?thesis by (simp add: t' inst_apps list_app_typeI)
      qed
      show "\<not> loose_bvar t' (ilength rb')"
        using Ap[OF _ lbs] lts' by (auto simp: t' loose_bvar_apps in_set_conv_nth)
      show "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma> t')" if "solution \<rho> \<sigma> env''" for \<sigma>
      proof -
        have "closed_subst \<sigma>" using solutionD(3)[OF that] by (simp add: wt_subst_def)
        then have "ap \<rho> \<sigma> (rename F 0 t') = rename F 0 (ap \<rho> \<sigma> t')"
          by (simp add: ap_def inst_rename vsubst_rename)
        with rn[OF lb] show ?thesis by simp
      qed
    qed
  next
    case False
    define Gty where "Gty = foldr fun_type (map fl_T args) U"
    obtain env1 v' where g: "genvar (fst v) env Gty = (env1, v')" by (cases "genvar (fst v) env Gty")
    define ks where "ks = map fl_j args"
    define body where "body = v' \<degree>\<degree> map Bound ks"
    from rest False g obtain env2 where vu: "ok (vupdate (v, T0) (types_abs Ts body) env1) env2"
      and nt: "ok (norm_term env2 (v' \<degree>\<degree> ts')) t'" and env': "env' = env2"
      by (auto simp: Let_def args_def ts'_def body_def ks_def Gty_def list_comb_apps comp_def)
    note gs = genvar_simps[OF g]
    let ?G = "(fst v, maxidx env + 1)"
    note asv = vupdate_asound[OF vu refl]
    have ext: "extends env env2" using extends_trans[OF extends_genvar[OF g] asoundD(1)[OF asv]] .
    show ?thesis unfolding csound_def
    proof (intro conjI allI impI)
      show "extends env env'" using ext env' by simp
      fix \<rho> env'' e T X assume tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''"
        and wte: "wt_env \<rho> env" and bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> t : T"
        and lb: "\<not> loose_bvar t (ilength rb)" and vi: "vinv \<rho> env (X \<union> vars t)"
      have ext2: "extends env2 env''" using ext' env' by simp
      have tsol: "tsol (tyenv env) \<rho>" using extends_tsol[OF tsol'' extends_trans[OF ext ext2]] .
      have tsol2: "tsol (tyenv env2) \<rho>" using extends_tsol[OF tsol'' ext2] .
      note td = tyd[OF tsol ty] and lbs = lbts[OF lb]
      let ?Us = "map (tsubst \<rho>) Ts"
      have ak: "0 \<le> fl_j a \<and> fl_j a < ilength ts \<and> rev ?Us ! nat_of_integer (fl_j a) = tsubst \<rho> (fl_T a) \<and>
          renv e F 0 \<turnstile> inst \<rho> (fl_t a) : tsubst \<rho> (fl_T a) \<and> \<not> loose_bvar (fl_t a) (ilength rb') \<and>
          vars (fl_t a) \<subseteq> vars t \<and>
          (\<forall>\<sigma>. closed_subst \<sigma> \<longrightarrow> rev (map (ap \<rho> \<sigma>) ts) ! nat_of_integer (fl_j a) = rename F 0 (ap \<rho> \<sigma> (fl_t a)))"
        if a: "a \<in> set args" for a
      proof -
        from A[OF lbs a, where \<rho> = \<rho>] obtain k where k: "k < ?n" "fl_j a = integer_of_nat (?n - 1 - k)"
          "fl_T a = Ts ! k" and r: "rename F 0 (fl_t a) = ts ! k" "\<not> loose_bvar (fl_t a) (ilength rb')"
          "vars (fl_t a) = vars (ts ! k)"
          "\<forall>e T. e \<turnstile> inst \<rho> (ts ! k) : T \<longrightarrow> renv e F 0 \<turnstile> inst \<rho> (fl_t a) : T"
          by blast
        have j: "nat_of_integer (fl_j a) = ?n - 1 - k" using k(2) by (simp add: integer_reps)
        have rv: "rev xs ! (?n - 1 - k) = xs ! k" if "length xs = ?n" for xs :: "'b list"
          using k(1) that by (simp add: rev_nth)
        have "0 \<le> fl_j a" "fl_j a < ilength ts" using k(1,2) by (simp_all add: ilength_eq integer_reps)
        moreover have "rev ?Us ! nat_of_integer (fl_j a) = tsubst \<rho> (fl_T a)"
        proof -
          have "rev ?Us ! nat_of_integer (fl_j a) = ?Us ! k" unfolding j by (rule rv) (simp add: lTs)
          then show ?thesis using k(1,3) lTs by simp
        qed
        moreover have "renv e F 0 \<turnstile> inst \<rho> (fl_t a) : tsubst \<rho> (fl_T a)"
        proof -
          have "e \<turnstile> inst \<rho> (ts ! k) : tsubst \<rho> (Ts ! k)" using td k(1) by blast
          then show ?thesis using r(4) k(3) by simp
        qed
        moreover have "vars (fl_t a) \<subseteq> vars t" using r(3) k(1) by (auto simp: t vars_apps)
        moreover have "rev (map (ap \<rho> \<sigma>) ts) ! nat_of_integer (fl_j a) = rename F 0 (ap \<rho> \<sigma> (fl_t a))"
          if "closed_subst \<sigma>" for \<sigma>
        proof -
          have "rev (map (ap \<rho> \<sigma>) ts) ! nat_of_integer (fl_j a) = map (ap \<rho> \<sigma>) ts ! k"
            unfolding j by (rule rv) simp
          also have "\<dots> = ap \<rho> \<sigma> (ts ! k)" using k(1) by simp
          also have "\<dots> = rename F 0 (ap \<rho> \<sigma> (fl_t a))"
            using that by (simp add: r(1)[symmetric] ap_def inst_rename vsubst_rename)
          finally show ?thesis .
        qed
        ultimately show ?thesis using r(2) by blast
      qed
      have tyG: "tsubst \<rho> Gty = map (\<lambda>a. tsubst \<rho> (fl_T a)) args \<Rrightarrow> tsubst \<rho> U"
        by (simp add: Gty_def tsubst_funs comp_def)
      have c0: "cert_typ alg ar (?Us \<Rrightarrow> T)" using td by metis
      then have "(\<forall>V\<in>set ?Us. cert_typ alg ar V) \<and> cert_typ alg ar T"
        using cert_typ_funs[where Ts = ?Us and T = T] by blast
      then have cUs: "\<forall>V\<in>set ?Us. cert_typ alg ar V" and cT: "cert_typ alg ar T" by blast+
      have cA: "\<forall>a\<in>set args. cert_typ alg ar (tsubst \<rho> (fl_T a))"
      proof
        fix a assume "a \<in> set args"
        note k = ak[OF this]
        have "nat_of_integer (fl_j a) < length (rev ?Us)"
          using k lTs nat_of_integer_less_ilength[of "fl_j a" ts] by simp
        then have "rev ?Us ! nat_of_integer (fl_j a) \<in> set ?Us" by (metis nth_mem set_rev)
        then have "tsubst \<rho> (fl_T a) \<in> set ?Us" using conjunct1[OF conjunct2[OF conjunct2[OF k]]] by metis
        with cUs show "cert_typ alg ar (tsubst \<rho> (fl_T a))" by blast
      qed
      have cG: "cert_typ alg ar (tsubst \<rho> Gty)"
        using cA cT td by (simp add: tyG cert_typ_funs)
      text \<open>The binding of the cleaned variable:\<close>
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
      have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_genvar[OF g])
      have vi1: "vinv \<rho> env1 (vars v' \<union> (X \<union> vars t))" by (rule vinv_genvar[OF g vi])
      have "(v, T0) \<in> vars t" by (simp add: t vars_apps)
      then have "vinv \<rho> env1 ((X \<union> vars t \<union> vars v') \<union> insert (v, T0) (vars (types_abs Ts body)))"
        by (intro vinv_mono[OF vi1]) (auto simp: vB)
      from asoundD(2)[OF asv tsol'' ext2 wte1 clB _ this] tB
      have a: "wt_env \<rho> env2" "vinv \<rho> env2 (X \<union> vars t \<union> vars v')"
        "\<And>\<sigma>. solution \<rho> \<sigma> env'' \<Longrightarrow> \<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts body)"
        by auto
      text \<open>The new term, before normalization:\<close>
      have tts': "renv e F 0 \<tturnstile> map (inst \<rho>) ts' : map (\<lambda>a. tsubst \<rho> (fl_T a)) args"
        unfolding ts'_def map_map comp_def by (rule typings_map) (use ak in blast)
      have t2: "renv e F 0 \<turnstile> inst \<rho> (v' \<degree>\<degree> ts') : T"
        using tts' cG tyG td by (auto simp: gs(4) inst_apps intro!: list_app_typeI)
      note ns = nsoundD[OF norm_term_sound[OF nt tsol2 a(1)]]
      show "wt_env \<rho> env'" using a(1) env' by simp
      show "renv e F 0 \<turnstile> inst \<rho> t' : T" using ns(3)[OF t2] .
      show "\<not> loose_bvar t' (ilength rb')"
      proof (rule ns(2)[OF ilength_nonneg])
        show "\<not> loose_bvar (v' \<degree>\<degree> ts') (ilength rb')"
          using ak by (auto simp: gs(4) ts'_def loose_bvar_apps)
      qed
      show "vinv \<rho> env' (X \<union> vars t')"
      proof -
        have sub: "vars (v' \<degree>\<degree> ts') \<subseteq> vars t \<union> vars v'" using ak by (auto simp: ts'_def vars_apps)
        have "vsim \<rho> (vars t') ((vars t \<union> vars v') \<union> evars env2)"
          by (rule vsim_mono[OF ns(1)]) (use sub in blast)
        from vinv_vsim[OF _ this] a(2) env' show ?thesis by (simp add: Un_assoc)
      qed
      show "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma> t')" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
      proof -
        note s = solutionD[OF sol]
        have cs: "closed_subst \<sigma>" using s(3) by (simp add: wt_subst_def)
        have sol2: "solution \<rho> \<sigma> env2" by (rule solution_extends[OF sol ext2])
        let ?H = "\<sigma> ?G (tsubst \<rho> Gty)"
        have cH: "closed ?H" by (rule closed_substD[OF cs])
        have tts: "e \<tturnstile> map (ap \<rho> \<sigma>) ts : ?Us"
          by (rule typings_nthI) (use td lTs typing_ap[OF _ s(3)] in auto)
        have tBs: "e \<turnstile> ap \<rho> \<sigma> (types_abs Ts body) \<degree>\<degree> map (ap \<rho> \<sigma>) ts : T"
          using typing_ap[OF tB s(3)] td tts by (auto intro: list_app_typeI)
        have "ap \<rho> \<sigma> t = \<sigma> v (tsubst \<rho> T0) \<degree>\<degree> map (ap \<rho> \<sigma>) ts" by (simp add: t ap_apps)
        also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts body) \<degree>\<degree> map (ap \<rho> \<sigma>) ts"
        proof (rule conv_apps)
          show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) ts) (map (ap \<rho> \<sigma>) ts)" by (simp add: list_all2_refl)
          show "wt (\<sigma> v (tsubst \<rho> T0) \<degree>\<degree> map (ap \<rho> \<sigma>) ts)"
            using wt_ap[OF ty s(3)] by (simp add: t ap_apps)
          show "wt (ap \<rho> \<sigma> (types_abs Ts body) \<degree>\<degree> map (ap \<rho> \<sigma>) ts)" using tBs by (auto simp: wt_def)
          show "\<sigma> v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts body)" by (rule a(3)[OF sol])
        qed
        also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?H \<degree>\<degree> map (\<lambda>k. rev (map (ap \<rho> \<sigma>) ts) ! nat_of_integer k) ks"
        proof (rule conv_beta_eta)
          show "wt (ap \<rho> \<sigma> (types_abs Ts body) \<degree>\<degree> map (ap \<rho> \<sigma>) ts)" using tBs by (auto simp: wt_def)
          have "ap \<rho> \<sigma> (types_abs Ts body) = abs_list ?bs (?H \<degree>\<degree> map Bound ks)"
            by (simp add: types_abs_abs_list ap_abs_list body_def gs(4) ap_apps comp_def)
          moreover have "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength (map (ap \<rho> \<sigma>) ts)" using ak by (auto simp: ks_def)
          ultimately show "ap \<rho> \<sigma> (types_abs Ts body) \<degree>\<degree> map (ap \<rho> \<sigma>) ts \<rightarrow>\<^sub>\<beta>\<^sup>*
              ?H \<degree>\<degree> map (\<lambda>k. rev (map (ap \<rho> \<sigma>) ts) ! nat_of_integer k) ks"
            using beta_abs_list_select[OF cH, of ?bs "map (ap \<rho> \<sigma>) ts" ks] lTs by simp
        qed
        also have "?H \<degree>\<degree> map (\<lambda>k. rev (map (ap \<rho> \<sigma>) ts) ! nat_of_integer k) ks = rename F 0 (ap \<rho> \<sigma> (v' \<degree>\<degree> ts'))"
        proof -
          have "map (\<lambda>k. rev (map (ap \<rho> \<sigma>) ts) ! nat_of_integer k) ks = map (rename F 0) (map (ap \<rho> \<sigma>) ts')"
            using ak cs by (simp add: ks_def ts'_def)
          then show ?thesis
            by (simp add: gs(4) ap_apps rename_apps rename_closed[OF cH order_refl])
        qed
        also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma> t')"
        proof (rule conv_rename[OF ns(4)[OF t2 sol2] _ _ _ nF order_refl])
          have ty2: "renv e F 0 \<turnstile> ap \<rho> \<sigma> (v' \<degree>\<degree> ts') : T" using typing_ap[OF t2 s(3)] .
          have ty3: "renv e F 0 \<turnstile> ap \<rho> \<sigma> t' : T" using typing_ap[OF ns(3)[OF t2] s(3)] .
          show "wt (ap \<rho> \<sigma> (v' \<degree>\<degree> ts'))" using ty2 by (auto simp: wt_def)
          show "wt (rename F 0 (ap \<rho> \<sigma> (v' \<degree>\<degree> ts')))"
            using typing_rename[OF ty2 refl nF order_refl] by (auto simp: wt_def)
          show "wt (rename F 0 (ap \<rho> \<sigma> t'))"
            using typing_rename[OF ty3 refl nF order_refl] by (auto simp: wt_def)
        qed
        finally show ?thesis .
      qed
    qed
  qed
qed


text \<open>Cleaning both sides of a pair, which removes the banned binders, is a step:\<close>

lemma clean_dstep:
  assumes c1: "csound env rb F rb' t env1 t'" and c2: "csound env1 rb F rb' u env2 u'"
    and F: "bren_ok banned rb rb' F"
  shows "dstep env [(rb, t, u)] env2 [(rb', t', u')]"
proof (rule dstepI)
  have e1: "extends env env1" and e2: "extends env1 env2" using c1 c2 by (simp_all add: csound_def)
  show "extends env env2" by (rule extends_trans[OF e1 e2])
  fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext: "extends env2 env''"
    and wte: "wt_env \<rho> env" and d: "dtyped \<rho> [(rb, t, u)]" and v: "vinv \<rho> env (X \<union> dvars [(rb, t, u)])"
  from d obtain e T where bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
    and lb: "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)"
    by auto
  have ext1: "extends env1 env''" by (rule extends_trans[OF e2 ext])
  have v1: "vinv \<rho> env ((X \<union> vars u) \<union> vars t)" using v by (simp add: Un_ac)
  from c1 tsol'' ext1 wte bs ty(1) lb(1) v1
  have r1: "wt_env \<rho> env1" "vinv \<rho> env1 ((X \<union> vars u) \<union> vars t')" "renv e F 0 \<turnstile> inst \<rho> t' : T"
    "\<not> loose_bvar t' (ilength rb')" "\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma> t')"
    unfolding csound_def by blast+
  have v2: "vinv \<rho> env1 ((X \<union> vars t') \<union> vars u)" using r1(2) by (simp add: Un_ac)
  from c2 tsol'' ext r1(1) bs ty(2) lb(2) v2
  have r2: "wt_env \<rho> env2" "vinv \<rho> env2 ((X \<union> vars t') \<union> vars u')" "renv e F 0 \<turnstile> inst \<rho> u' : T"
    "\<not> loose_bvar u' (ilength rb')" "\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma> u')"
    unfolding csound_def by blast+
  from F have nF: "nonneg F" and FP: "\<forall>p. 0 \<le> p \<longrightarrow> p < ilength rb' \<longrightarrow>
      0 \<le> F p \<and> F p < ilength rb \<and> rb' ! nat_of_integer p = rb ! nat_of_integer (F p)"
    unfolding bren_ok_def by blast+
  have bs': "bs_env \<rho> (renv e F 0) rb'"
    unfolding bs_env_def
  proof (intro conjI allI impI ballI)
    fix i assume i: "0 \<le> i" "i < ilength rb'"
    with FP have Fi: "0 \<le> F i" "F i < ilength rb" "rb' ! nat_of_integer i = rb ! nat_of_integer (F i)" by blast+
    have "renv e F 0 i = e (F i)" using i(1) by (simp add: renv_def)
    also have "\<dots> = tsubst \<rho> (snd (rb ! nat_of_integer (F i)))" using bs Fi(1,2) by (simp add: bs_env_def)
    finally show "renv e F 0 i = tsubst \<rho> (snd (rb' ! nat_of_integer i))" using Fi(3) by simp
  next
    fix p assume "p \<in> set rb'"
    then obtain q where q: "q < length rb'" "p = rb' ! q" by (auto simp: in_set_conv_nth)
    let ?i = "integer_of_nat q"
    have i: "0 \<le> ?i" "?i < ilength rb'" using q(1) by (simp_all add: ilength_eq integer_of_nat_eq_of_nat)
    with FP have Fi: "0 \<le> F ?i" "F ?i < ilength rb" "rb' ! nat_of_integer ?i = rb ! nat_of_integer (F ?i)" by blast+
    have "rb ! nat_of_integer (F ?i) \<in> set rb" using Fi(1,2) by (simp add: nat_of_integer_less_ilength)
    with Fi(3) q have "p \<in> set rb" by simp
    with bs show "case p of (x, T) \<Rightarrow> cert_typ alg ar (tsubst \<rho> T)" by (auto simp: bs_env_def)
  qed
  have "dtyped \<rho> [(rb', t', u')]" using bs' r1(3,4) r2(3,4) by auto
  moreover have "vinv \<rho> env2 (X \<union> dvars [(rb', t', u')])" using r2(2) by (simp add: Un_ac)
  moreover have "dsolved \<rho> \<sigma> [(rb, t, u)]" if sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> [(rb', t', u')]"
    for \<sigma>
  proof -
    note s = solutionD[OF sol]
    have ty1: "renv e F 0 \<turnstile> ap \<rho> \<sigma> t' : T" and ty2: "renv e F 0 \<turnstile> ap \<rho> \<sigma> u' : T"
      using typing_ap[OF r1(3) s(3)] typing_ap[OF r2(3) s(3)] .
    from ds have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" by simp
    then have "rename F 0 (ap \<rho> \<sigma> t') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma> u')"
      by (rule conv_rename)
        (use ty1 typing_rename[OF ty1 refl nF order_refl] typing_rename[OF ty2 refl nF order_refl] nF
          in \<open>auto simp: wt_def\<close>)
    with r1(5) r2(5) sol show ?thesis by (simp, meson conv_sym conv_trans)
  qed
  ultimately show "wt_env \<rho> env2 \<and> dtyped \<rho> [(rb', t', u')] \<and> vinv \<rho> env2 (X \<union> dvars [(rb', t', u')]) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> [(rb', t', u')] \<longrightarrow> dsolved \<rho> \<sigma> [(rb, t, u)])"
    using r2(1) by blast
qed


subsection \<open>Flex-flex pairs\<close>

lemma okW_ASSIGN_handler: "okW (case e of ASSIGN \<Rightarrow> m | _ \<Rightarrow> raiseW e) y \<Longrightarrow> okW m y"
  by (cases e) auto

lemma okW_CHANGE_FAIL_handler: "okW (case e of CHANGE_FAIL \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

lemma okW_ASSIGN_return: "okW (case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

lemma ff_handler:
  assumes "okW (handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' t' u'; returnW (env3, tps)})
    (\<lambda>e. case e of
      ASSIGN \<Rightarrow>
        handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' u' t'; returnW (env3, tps)})
          (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
    | _ \<Rightarrow> raiseW e)) r"
  shows "(\<exists>env3. okW (ff_assign alg' env2 rb' t' u') env3 \<and> r = (env3, tps)) \<or>
    (\<exists>env3. okW (ff_assign alg' env2 rb' u' t') env3 \<and> r = (env3, tps)) \<or>
    r = (env2, add_tpair rb' t' u' tps)"
proof -
  from assms consider (a) "okW (do {env3 \<leftarrow> ff_assign alg' env2 rb' t' u'; returnW (env3, tps)}) r"
    | (b) e where "okW (case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e) r"
    unfolding okW_handleW by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis by auto
  next
    case b
    from okW_ASSIGN_handler[OF b] consider (c) "okW (do {env3 \<leftarrow> ff_assign alg' env2 rb' u' t'; returnW (env3, tps)}) r"
      | (d) e where "okW (case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e) r"
      unfolding okW_handleW by blast
    then show ?thesis
    proof cases
      case c
      then show ?thesis by auto
    next
      case d
      from okW_ASSIGN_return[OF d] show ?thesis by blast
    qed
  qed
qed

theorem clean_ffpair_sound:
  assumes "okW (clean_ffpair alg' rb t u env tps) (env', tps')"
  shows "dstep env ((rb, t, u) # tdps tps) env' (tdps tps')"
proof -
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  from clean_binder[OF fb] obtain F where F: "bren_ok banned rb rb' F" by blast
  have "(\<exists>env1 t' env2 u'. okW (clean_term banned env t) (env1, t') \<and>
      okW (clean_term banned env1 u) (env2, u') \<and>
      okW (handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')) \<or>
      (env', tps') = (env, add_tpair rb t u tps)"
    using assms fb by (auto simp: clean_ffpair_def Let_def okW_handleW dest!: okW_CHANGE_FAIL_handler)
  then consider (fail) "(env', tps') = (env, add_tpair rb t u tps)"
    | (main) env1 t' env2 u' where "okW (clean_term banned env t) (env1, t')"
      "okW (clean_term banned env1 u) (env2, u')" "okW (handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')"
    by blast
  then show ?thesis
  proof cases
    case fail
    then show ?thesis using add_tpair_sound[of env rb t u tps] by simp
  next
    case (main env1 t' env2 u')
    have cl: "dstep env [(rb, t, u)] env2 [(rb', t', u')]"
      by (rule clean_dstep[OF clean_term_sound[OF main(1) F] clean_term_sound[OF main(2) F] F])
    from ff_handler[OF main(3)] consider (fa1) env3 where "okW (ff_assign alg' env2 rb' t' u') env3"
        "(env', tps') = (env3, tps)"
      | (fa2) env3 where "okW (ff_assign alg' env2 rb' u' t') env3" "(env', tps') = (env3, tps)"
      | (keep) "(env', tps') = (env2, add_tpair rb' t' u' tps)"
      by blast
    then show ?thesis
    proof cases
      case (fa1 env3)
      have "dstep env [(rb, t, u)] env3 []" by (rule dstep_trans[OF cl ff_assign_sound[OF fa1(1)]])
      from dstep_frame[OF this, of "tdps tps"] fa1(2) show ?thesis by simp
    next
      case (fa2 env3)
      have "dstep env2 [(rb', t', u')] env3 []" by (rule dstep_swap_in[OF ff_assign_sound[OF fa2(1)]])
      from dstep_frame[OF dstep_trans[OF cl this], of "tdps tps"] fa2(2) show ?thesis by simp
    next
      case keep
      from dstep_frame[OF cl, of "tdps tps"]
      have "dstep env ((rb, t, u) # tdps tps) env2 ((rb', t', u') # tdps tps)" by simp
      from dstep_trans[OF this add_tpair_sound[of env2 rb' t' u' tps]] keep
      show ?thesis by simp
    qed
  qed
qed

theorem add_ffpair_sound:
  assumes "okW (add_ffpair alg' dp (env, tps)) (env', tps')"
  shows "dstep env (dp # tdps tps) env' (tdps tps')"
proof -
  obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
  from assms dp obtain t u where nt: "ok (norm_term env t0) t" and nu: "ok (norm_term env u0) u"
    and rest: "okW (case (head_of t, head_of u) of
        (Var v T, Var w U) \<Rightarrow>
          if v = w then
            (if T = U then returnW (env, add_tpair rb t u tps)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair alg' rb u t env tps
          else clean_ffpair alg' rb t u env tps
      | _ \<Rightarrow> raiseW (PExn (Term_Error (STR ''add_ffpair: Vars expected'') [t, u]))) (env', tps')"
    by (auto simp: add_ffpair_def)
  have n: "dstep env ((rb, t0, u0) # tdps tps) env ((rb, t, u) # tdps tps)"
    using dstep_frame[where fs = "tdps tps", OF norm_term_dstep[where bs = rb, OF nt nu]] by simp
  from rest consider (same) "env' = env" "tps' = add_tpair rb t u tps"
    | (tu) "okW (clean_ffpair alg' rb t u env tps) (env', tps')"
    | (ut) "okW (clean_ffpair alg' rb u t env tps) (env', tps')"
    by (auto split: pterm.splits if_splits)
  then show ?thesis
  proof cases
    case same
    with dstep_trans[OF n add_tpair_sound[of env rb t u tps]] dp show ?thesis by simp
  next
    case tu
    with dstep_trans[OF n clean_ffpair_sound[OF tu]] dp show ?thesis by simp
  next
    case ut
    with dstep_trans[OF n dstep_swap_in[OF clean_ffpair_sound[OF ut]]] dp show ?thesis by simp
  qed
qed

theorem foldrW_add_ffpair_sound:
  "okW (foldrW (add_ffpair alg') ffs (env, tps)) (env', tps') \<Longrightarrow> dstep env (ffs @ tdps tps) env' (tdps tps')"
proof (induction ffs arbitrary: env' tps')
  case Nil
  then show ?case by (simp add: dstep_refl)
next
  case (Cons dp ffs)
  from Cons.prems obtain env1 tps1 where f: "okW (foldrW (add_ffpair alg') ffs (env, tps)) (env1, tps1)"
    and a: "okW (add_ffpair alg' dp (env1, tps1)) (env', tps')" by auto
  have "dstep env ((ffs @ tdps tps) @ [dp]) env1 (tdps tps1 @ [dp])" by (rule dstep_frame[OF Cons.IH[OF f]])
  then have "dstep env ((dp # ffs) @ tdps tps) env1 (dp # tdps tps1)" by (rule dstep_set) auto
  from dstep_trans[OF this add_ffpair_sound[OF a]] show ?case .
qed

end

end
