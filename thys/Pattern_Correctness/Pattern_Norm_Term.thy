section \<open>Normalization, the Pattern Test and Rigid Occurrences\<close>

theory Pattern_Norm_Term
  imports Pattern_Normal Pattern_Patterns
begin

text \<open>
  The occurs check of \<^const>\<open>flexrigid\<close> normalizes the rigid side (\<^const>\<open>norm_term\<close>) and tests
  whether the result is a pattern (\<^const>\<open>pattern\<close>). This theory provides what the proofs need
  about both: the pattern test agrees with \<^const>\<open>ppat\<close> on terms without \<open>\<beta>\<close>-redexes,
  normalization is sound and returns terms without \<open>\<beta>\<close>-redexes whose variables are unbound, and in
  such a pattern every occurrence of a variable is rigid (\<open>rigid_occurs\<close>).
\<close>


subsection \<open>The pattern test\<close>

context pure_sig
begin

lemma has_duplicates_Bounds: "has_duplicates_by aconv_term (map Bound is) \<longleftrightarrow> \<not> distinct is"
  by (induction "is") (auto simp: list_ex_iff)

lemma pattern_Abs: "pattern (Abs a T t) \<longleftrightarrow> pattern t"
  by (subst pattern.simps) simp

lemma pattern_apps:
  assumes "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Abs (h \<degree>\<degree> ts)"
  shows "pattern (h \<degree>\<degree> ts) \<longleftrightarrow>
    (if is_Var h then list_all is_Bound ts \<and> \<not> has_duplicates_by aconv_term ts else list_all pattern ts)"
proof -
  have nonAbs: "pattern t = (let (head, args) = strip_comb t in
      if is_Var head then list_all is_Bound args \<and> \<not> has_duplicates_by aconv_term args
      else list_all (\<lambda>u. pattern u) args)" if "\<not> is_Abs t" for t
    using that by (subst pattern.simps) (cases t; simp)
  have s: "strip_comb (h \<degree>\<degree> ts) = (h, ts)" by (rule strip_comb_atom_apps[OF assms(1)])
  show ?thesis using nonAbs[OF assms(2)] by (simp add: s)
qed

lemma all_Bound_map: "list_all is_Bound ts \<Longrightarrow> \<exists>is. ts = map Bound is"
proof (induction ts)
  case (Cons t ts)
  then obtain i "is" where "t = Bound i" "ts = map Bound is" by (cases t) auto
  then show ?case by (intro exI[of _ "i # is"]) simp
qed simp

theorem ppat_pattern: "ppat t \<Longrightarrow> pattern t"
proof (induction rule: ppat.induct)
  case (ppat_Abs t a T)
  then show ?case by (simp add: pattern_Abs)
next
  case (ppat_rigid h ts)
  have h: "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Var h" "\<not> is_Abs h" using ppat_rigid(1) by (cases h; simp)+
  have "\<not> is_Abs (h \<degree>\<degree> ts)" using h(3) by (simp add: is_Abs_apps)
  with pattern_apps[OF h(1)] h(2) ppat_rigid(2) show ?case by (simp add: list_all_iff)
next
  case (ppat_flex "is" x T)
  have "\<not> is_Abs (Var x T \<degree>\<degree> map Bound is)" by (simp add: is_Abs_apps)
  with pattern_apps[of "Var x T" "map Bound is"] ppat_flex show ?case
    by (simp add: app_apps has_duplicates_Bounds list_all_iff)
qed


lemma no_redex_apps_head: "no_redex (h \<degree>\<degree> ts) \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> \<not> is_Abs h"
proof (induction ts arbitrary: h)
  case (Cons t ts)
  show ?case
  proof (cases "ts = []")
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    from Cons.IH[OF _ False] Cons.prems have "\<not> is_Abs (h $ t)" by simp
    have "no_redex (h $ t)" using Cons.prems(1) no_redex_apps[of "h $ t" ts] by simp
    then show ?thesis by simp
  qed
qed simp

lemma no_redex_strip:
  assumes "no_redex t" "\<not> is_Abs t" "strip_comb t = (h, ts)"
  shows "atom h" "\<forall>u\<in>set ts. no_redex u"
proof -
  have t: "t = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF assms(3)])
  have nh: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF assms(3)])
  have "\<not> is_Abs h"
  proof (cases "ts = []")
    case True
    with assms(2) t show ?thesis by simp
  qed (use no_redex_apps_head assms(1) t in blast)
  with nh show "atom h" by (cases h) auto
  with assms(1) show "\<forall>u\<in>set ts. no_redex u" using no_redex_apps[of h ts] t
    by (cases h) auto
qed

theorem pattern_ppat: "pattern t \<Longrightarrow> no_redex t \<Longrightarrow> ppat t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "is_Abs t")
    case True
    then obtain a T u where t: "t = Abs a T u" by (cases t) auto
    with less show ?thesis by (auto simp: pattern_Abs intro: ppat_Abs)
  next
    case False
    obtain h ts where s: "strip_comb t = (h, ts)" by force
    have t: "t = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF s])
    have h: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF s])
    have sz: "size u < size t" if "u \<in> set ts" for u using strip_comb_acc_size[of t "[]" h ts u] s that by (simp add: strip_comb_def)
    note nr = no_redex_strip[OF less.prems(2) False s]
    have pat: "if is_Var h then list_all is_Bound ts \<and> \<not> has_duplicates_by aconv_term ts else list_all pattern ts"
      using less.prems(1) pattern_apps[OF h] False by (simp add: t)
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain x T where hx: "h = Var x T" by (cases h) auto
      from True pat obtain "is" where ts: "ts = map Bound is" using all_Bound_map by auto
      have "distinct is" using True pat by (simp add: ts has_duplicates_Bounds)
      then show ?thesis using ppat_flex[of "is" x T] by (simp add: t hx ts app_apps)
    next
      case False
      have "rigid h" using nr(1) False by (cases h) simp_all
      moreover have "\<forall>u\<in>set ts. ppat u"
        using less.IH sz nr(2) pat False by (auto simp: list_all_iff)
      ultimately show ?thesis by (simp add: t ppat_rigid)
    qed
  qed
qed

subsection \<open>Normalization\<close>

subsubsection \<open>Variables up to the type instantiation\<close>

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


subsubsection \<open>Sound normalization steps\<close>

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

lemma ok_lookup1:
  "ok (lookup1 te x T) r \<Longrightarrow>
    (r = None \<and> vt_lookup te x = None) \<or> (\<exists>u. r = Some u \<and> vt_lookup te x = Some (T, u))"
  by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)

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

subsubsection \<open>The shape of the results\<close>

text \<open>The results of normalization have no \<open>\<beta>\<close>-redexes, and their variables are unbound:\<close>

end

definition unbound :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "unbound env t \<longleftrightarrow> (\<forall>p\<in>vars t. vt_lookup (tenv env) (fst p) = None)"

context pure_sig
begin

lemma unbound_simps [simp]:
  "unbound env (s $ t) \<longleftrightarrow> unbound env s \<and> unbound env t"
  "unbound env (Abs a T t) \<longleftrightarrow> unbound env t"
  "unbound env (Var x T) \<longleftrightarrow> vt_lookup (tenv env) x = None"
  "unbound env (Bound i)" "unbound env (Const c T)" "unbound env (Free c T)"
  by (auto simp: unbound_def)

lemma unbound_apps: "unbound env (h \<degree>\<degree> ts) \<longleftrightarrow> unbound env h \<and> (\<forall>t\<in>set ts. unbound env t)"
  by (induction ts arbitrary: h) auto

lemma could_beta_contract_no_redex: "\<not> could_beta_contract t \<Longrightarrow> no_redex t"
  by (induction t rule: could_beta_contract.induct) auto

lemma norm_term1_nf:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> no_redex t' \<and> unbound env t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2)
  have IH: "no_redex u' \<and> unbound env u'" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr te have "vt_lookup (tenv env) x = None"
        by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)
      moreover from rest None Var have "t' = Var x T" by simp
      ultimately show ?thesis by simp
    next
      case (Some u)
      with rest have "ok (nt te u) t'" by simp
      then show ?thesis by (rule IH)
    qed
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
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
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        then show ?thesis by (rule IH)
      next
        case False
        with rest obtain nu where hu: "ok (nt te u) nu" and t': "t' = nf $ nu"
          by (cases nf) auto
        with IH[OF hf] IH[OF hu] False show ?thesis by simp
      qed
    qed
  qed (use h in auto)
qed

lemma norm_term2_nf:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> no_redex t' \<and> unbound env t'"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "no_redex u' \<and> unbound env u'" if "ok (nt env u) u'" for u u'
    using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr have "vt_lookup (tenv env) x = None" by (simp add: ok_lookup_None)
      with rest None show ?thesis by auto
    next
      case (Some u)
      with rest have "ok (nt env u) t'" by simp
      then show ?thesis by (rule IH)
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (nt env body) body'" "t' = Abs a T' body'" by auto
    with IH show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      then show ?thesis by (rule IH)
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        then show ?thesis by (rule IH)
      next
        case False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu"
          by (cases nf) auto
        with IH[OF hf] IH[OF hu] False show ?thesis by simp
      qed
    qed
  qed (use h in auto)
qed

lemma norm_term_cases:
  assumes "ok (norm_term env t) t'"
  obtains (id) "env_is_empty env" "\<not> could_beta_contract t" "t' = t"
  | (n1) "norm_term1 (tenv env) t = Some (Ok t')" "vt_is_empty (tyenv env)"
  | (n2) "norm_term2 env t = Some (Ok t')"
  using assms by (auto simp: norm_term_def split: if_splits)

lemma norm_term_nf:
  assumes "ok (norm_term env t) t'"
  shows "no_redex t'" "unbound env t'"
proof -
  have "no_redex t' \<and> unbound env t'"
    using assms
  proof (cases rule: norm_term_cases)
    case id
    then show ?thesis
      using could_beta_contract_no_redex by (auto simp: unbound_def env_is_empty_def vt_is_empty_lookup)
  next
    case n1
    from norm_term1_nf[OF n1(1) refl refl] show ?thesis .
  next
    case n2
    from norm_term2_nf[OF n2 refl] show ?thesis .
  qed
  then show "no_redex t'" "unbound env t'" by blast+
qed

text \<open>Normalization keeps rigid heads:\<close>

lemma norm_term1_rigid:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> rigid h \<Longrightarrow> t = h \<degree>\<degree> ts \<Longrightarrow> \<exists>h' ts'. rigid h' \<and> t' = h' \<degree>\<degree> ts'"
  using assms
proof (induction te t r arbitrary: t' ts rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and rh = "1.prems"(2) and t = "1.prems"(3)
  have IH: "\<exists>h' ts'. rigid h' \<and> u' = h' \<degree>\<degree> ts'" if "ok (nt te (h \<degree>\<degree> us)) u'" for u' us
    using "1.IH"[OF that refl rh refl] .
  show ?case
  proof (cases ts rule: rev_cases)
    case Nil
    with t have th: "t = h" by simp
    with h rh have "t' = h" by (cases h) auto
    with rh show ?thesis by (intro exI[of _ h] exI[of _ "[]"]) simp
  next
    case (snoc us u)
    with t have tu: "t = (h \<degree>\<degree> us) $ u" by simp
    have nA: "\<not> is_Abs (h \<degree>\<degree> us)" using rh by (cases h) (auto simp: is_Abs_apps)
    with h tu obtain nf where hf: "ok (nt te (h \<degree>\<degree> us)) nf"
      and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
      by (cases "h \<degree>\<degree> us") auto
    from IH[OF hf] obtain h' ts' where h': "rigid h'" "nf = h' \<degree>\<degree> ts'" by blast
    then have "\<not> is_Abs nf" by (cases h') (auto simp: is_Abs_apps)
    with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
    with h' show ?thesis by (intro exI[of _ h'] exI[of _ "ts' @ [nu]"]) simp
  qed
qed

lemma norm_term2_rigid:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> rigid h \<Longrightarrow> t = h \<degree>\<degree> ts \<Longrightarrow> \<exists>h' ts'. rigid h' \<and> t' = h' \<degree>\<degree> ts'"
  using assms
proof (induction env t r arbitrary: t' ts rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and rh = "1.prems"(2) and t = "1.prems"(3)
  have IH: "\<exists>h' ts'. rigid h' \<and> u' = h' \<degree>\<degree> ts'" if "ok (nt env (h \<degree>\<degree> us)) u'" for u' us
    using "1.IH"[OF that refl rh refl] .
  show ?case
  proof (cases ts rule: rev_cases)
    case Nil
    with t have th: "t = h" by simp
    with h rh have "rigid t'" by (cases h) auto
    then show ?thesis by (intro exI[of _ t'] exI[of _ "[]"]) simp
  next
    case (snoc us u)
    with t have tu: "t = (h \<degree>\<degree> us) $ u" by simp
    have nA: "\<not> is_Abs (h \<degree>\<degree> us)" using rh by (cases h) (auto simp: is_Abs_apps)
    with h tu obtain nf where hf: "ok (nt env (h \<degree>\<degree> us)) nf"
      and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
        | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
      by (cases "h \<degree>\<degree> us") auto
    from IH[OF hf] obtain h' ts' where h': "rigid h'" "nf = h' \<degree>\<degree> ts'" by blast
    then have "\<not> is_Abs nf" by (cases h') (auto simp: is_Abs_apps)
    with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
    with h' show ?thesis by (intro exI[of _ h'] exI[of _ "ts' @ [nu]"]) simp
  qed
qed

lemma norm_term_rigid:
  assumes "ok (norm_term env t) t'" "rigid h" "t = h \<degree>\<degree> ts"
  obtains h' ts' where "rigid h'" "t' = h' \<degree>\<degree> ts'"
proof -
  have "\<exists>h' ts'. rigid h' \<and> t' = h' \<degree>\<degree> ts'"
    using assms(1)
  proof (cases rule: norm_term_cases)
    case id
    with assms(2,3) show ?thesis by blast
  next
    case n1
    from norm_term1_rigid[OF n1(1) refl assms(2,3)] show ?thesis .
  next
    case n2
    from norm_term2_rigid[OF n2 refl assms(2,3)] show ?thesis .
  qed
  with that show thesis by blast
qed


end


subsection \<open>Rigid occurrences\<close>

text \<open>
  A proof device (the occurs check of an earlier version of the fix of \<^const>\<open>flexrigid\<close>):
  \<open>F\<close> occurs as the head of a pattern \<open>F x\<^sub>1 \<dots> x\<^sub>n\<close> (distinct bound variables) that is
  reached, modulo head normalisation, through abstractions and arguments of rigid heads only.
  Such an occurrence survives in every well-typed instance, so the unification problem
  \<open>F y\<^sub>1 \<dots> y\<^sub>m =?= t\<close> has no solution (theory \<open>Pattern_Occurs\<close>).
\<close>

context
begin

text \<open>The default bound is too small to derive the fixed-point induction rule.\<close>

declare [[unify_search_bound = 100]]

partial_function (option) rigid_occurs :: "indexname \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool M" where
  "rigid_occurs F t env =
    do {
      t' \<leftarrow> head_norm env t;
      (case t' of
        Abs _ _ u \<Rightarrow> rigid_occurs F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              Var G _ \<Rightarrow>
                if G = F then
                  handle (do {_ \<leftarrow> ints_of' env ts; return True})
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)))
    }"

end

context pure_sig
begin

lemma pterm_case_nonAbs: "\<not> is_Abs t \<Longrightarrow> (case t of Abs a T u \<Rightarrow> f a T u | _ \<Rightarrow> g) = g"
  by (cases t) auto

lemma existsM_TrueE: "existsM P xs = Some (Ok True) \<Longrightarrow> \<exists>x\<in>set xs. P x = Some (Ok True)"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits if_splits)

lemma existsM_return_iff:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x = return (Q x)) \<Longrightarrow> existsM P xs = return (\<exists>x\<in>set xs. Q x)"
  by (induction xs) auto

lemma head_norm_rigid_apps: "rigid h \<Longrightarrow> head_norm env (h \<degree>\<degree> ts) = return (h \<degree>\<degree> ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (subst head_norm.simps) (cases h, auto)
next
  case (snoc t ts)
  have nA: "\<not> is_Abs (h \<degree>\<degree> ts)" using snoc.prems is_Abs_apps[of h ts] by (cases h) auto
  have IH: "head_norm env (h \<degree>\<degree> ts) = return (h \<degree>\<degree> ts)" by (rule snoc.IH[OF snoc.prems])
  have "head_norm env ((h \<degree>\<degree> ts) $ t) = return ((h \<degree>\<degree> ts) $ t)"
    using IH nA by (subst head_norm.simps) (cases "h \<degree>\<degree> ts"; simp)
  then show ?case by simp
qed

text \<open>Terms without \<open>\<beta>\<close>-redexes and with unbound variables are normal with respect to \<open>env\<close>:\<close>

lemma head_norm_nf: "no_redex t \<Longrightarrow> unbound env t \<Longrightarrow> head_norm env t = return t"
proof (induction t)
  case (Var x T)
  then show ?case by (subst head_norm.simps) (simp add: lookup_def)
next
  case (Abs a T t)
  then show ?case by (subst head_norm.simps) simp
next
  case (App f u)
  then have nA: "\<not> is_Abs f" and hf: "head_norm env f = return f" by simp_all
  with nA show ?case by (subst head_norm.simps) (cases f; simp)
qed (subst head_norm.simps; simp)+

lemma occurs_unbound: "unbound env t \<Longrightarrow> occurs F t env = return (F \<in> fst ` vars t)"
proof (induction t)
  case (Var x T)
  then show ?case by (subst occurs.simps) (simp add: lookup_def)
next
  case (App s t)
  then show ?case by (subst occurs.simps) (auto simp: image_Un)
qed (subst occurs.simps; simp)+

lemma ppat_no_redex: "ppat t \<Longrightarrow> no_redex t"
  by (induction rule: ppat.induct) (auto simp: no_redex_apps app_apps rigid_def split: pterm.splits)

text \<open>In a pattern with unbound variables, every occurrence of a variable is rigid:\<close>

lemma rigid_occurs_ppat_unbound:
  "ppat t \<Longrightarrow> unbound env t \<Longrightarrow> rigid_occurs F t env = return (F \<in> fst ` vars t)"
proof (induction rule: ppat.induct)
  case (ppat_Abs t a T)
  have "head_norm env (Abs a T t) = return (Abs a T t)"
    using ppat_Abs.prems ppat_no_redex[OF ppat_Abs.hyps] by (intro head_norm_nf) simp_all
  with ppat_Abs show ?case by (subst rigid_occurs.simps) simp
next
  case (ppat_rigid h ts)
  have nA: "\<not> is_Abs (h \<degree>\<degree> ts)" using ppat_rigid.hyps(1) by (cases h) (auto simp: is_Abs_apps)
  have sc: "strip_comb (h \<degree>\<degree> ts) = (h, ts)"
    using rigid_atom[OF ppat_rigid.hyps(1)] by (intro strip_comb_atom_apps) auto
  have ex: "existsM (\<lambda>u. rigid_occurs F u env) ts = return (\<exists>u\<in>set ts. F \<in> fst ` vars u)"
    using ppat_rigid.IH ppat_rigid.prems by (intro existsM_return_iff) (auto simp: unbound_apps)
  have "rigid_occurs F (h \<degree>\<degree> ts) env = existsM (\<lambda>u. rigid_occurs F u env) ts"
    by (subst rigid_occurs.simps)
      (use ppat_rigid.hyps(1) in \<open>simp add: head_norm_rigid_apps pterm_case_nonAbs[OF nA] sc, cases h, auto\<close>)
  moreover have "vars h = {}" using ppat_rigid.hyps(1) by (cases h) auto
  ultimately show ?case using ex by (auto simp: vars_apps)
next
  case (ppat_flex "is" x T)
  have t: "app (Var x T) is = Var x T \<degree>\<degree> map Bound is" by (rule app_apps)
  have nA: "\<not> is_Abs (Var x T \<degree>\<degree> map Bound is)" by (simp add: is_Abs_apps)
  have sc: "strip_comb (Var x T \<degree>\<degree> map Bound is) = (Var x T, map Bound is)"
    by (intro strip_comb_atom_apps) auto
  have hn: "head_norm env (Var x T \<degree>\<degree> map Bound is) = return (Var x T \<degree>\<degree> map Bound is)"
    using ppat_flex.prems by (intro head_norm_nf) (auto simp: t no_redex_apps unbound_apps)
  have "rigid_occurs F (Var x T \<degree>\<degree> map Bound is) env = return (F = x)"
    by (subst rigid_occurs.simps) (simp add: hn pterm_case_nonAbs[OF nA] sc ints_of'_Bounds[OF ppat_flex.hyps])
  then show ?case by (auto simp: t vars_apps)
qed


end


subsection \<open>The occurs check of \<^const>\<open>flexrigid\<close>\<close>

definition fr_occurs :: "indexname \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool M" where
  "fr_occurs F t env = do {t' \<leftarrow> norm_term env t; if pattern t' then occurs F t' env else return False}"

context pure_sig
begin

lemma flexrigid_fr_occurs:
  "flexrigid env bs F Fty is t =
    do {
      b \<leftarrow> occurs F t env;
      if b then do {
        b' \<leftarrow> fr_occurs F t env;
        if b' then raise (Unif (Ocheck_Fail F t bs env)) else raise Pattern}
      else handle
        (do {(u, env') \<leftarrow> proj t env bs is; u' \<leftarrow> mkabs bs is u; update (F, Fty) u' env'})
        (\<lambda>e. case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env bs F is t)) | _ \<Rightarrow> raise e)
    }"
  unfolding flexrigid_def fr_occurs_def by (simp add: bindM_assoc cong: if_cong)

text \<open>
  If the occurs check reports an occurrence, then the normal form of \<open>t\<close> is a pattern with unbound
  variables in which \<open>F\<close> occurs, rigidly:
\<close>

lemma fr_occurs_TrueE:
  assumes "ok (fr_occurs F t env) True"
  obtains t' where "ok (norm_term env t) t'" "ppat t'" "unbound env t'" "F \<in> fst ` vars t'"
    "rigid_occurs F t' env = return True"
proof -
  from assms obtain t' where nt: "ok (norm_term env t) t'"
    and r: "ok (if pattern t' then occurs F t' env else return False) True"
    by (auto simp: fr_occurs_def)
  note nf = norm_term_nf[OF nt]
  from r have p: "pattern t'" by (cases "pattern t'") auto
  have pp: "ppat t'" by (rule pattern_ppat[OF p nf(1)])
  have F: "F \<in> fst ` vars t'" using r p occurs_unbound[OF nf(2), of F] by simp
  have "rigid_occurs F t' env = return True" using rigid_occurs_ppat_unbound[OF pp nf(2), of F] F by simp
  with that nt pp nf(2) F show thesis by blast
qed

end

end
