section \<open>The Occurs Check\<close>

theory Pattern_Occurs
  imports Pattern_Complete_Proj
begin

text \<open>
  A problem \<open>F xs =?= t\<close> where \<open>F\<close> occurs rigidly in \<open>t\<close> (\<^const>\<open>rigid_occurs\<close>) has no
  well-typed solution. Without types this fails, so we use a type-directed measure: the depth of
  the \<open>\<eta>\<close>-long form of a \<open>\<beta>\<close>-normal term (after Grobauer). It is invariant under \<open>\<eta>\<close>-reduction
  of well-typed \<open>\<beta>\<close>-normal terms and hence under \<open>\<alpha>\<beta>\<eta>\<close>-equivalence, but strictly increases
  below a rigid head.
\<close>

subsection \<open>The measure\<close>

fun dom_type :: "ptyp \<Rightarrow> ptyp" where
  "dom_type (Type a [T, U]) = (if a = STR ''fun'' then T else Type a [T, U])"
| "dom_type T = T"

fun rng_type :: "ptyp \<Rightarrow> ptyp" where
  "rng_type (Type a [T, U]) = (if a = STR ''fun'' then U else Type a [T, U])"
| "rng_type T = T"

lemma dom_rng_fun [simp]: "dom_type (T \<rightarrow>\<^sub>T U) = T" "rng_type (T \<rightarrow>\<^sub>T U) = U"
  by simp_all

text \<open>The depth of the \<open>\<eta>\<close>-long form of a variable of a given type:\<close>

fun type_depth :: "ptyp \<Rightarrow> nat" where
  "type_depth (Type a [T, U]) = (if a = STR ''fun'' then max (Suc (type_depth T)) (type_depth U) else 0)"
| "type_depth _ = 0"

lemma type_depth_rng: "type_depth (rng_type T) \<le> type_depth T"
  by (induction T rule: rng_type.induct) auto

text \<open>The type of a term whose head is not an abstraction, computed from the type of its head:\<close>

fun spine_type :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> ptyp" where
  "spine_type e (Bound i) = e i"
| "spine_type e (Var x T) = T"
| "spine_type e (Const c T) = T"
| "spine_type e (Free f T) = T"
| "spine_type e (s $ t) = rng_type (spine_type e s)"
| "spine_type e (Abs a T t) = TFree STR '''' []"

text \<open>The depth of the \<open>\<eta>\<close>-long form of a term of a given type:\<close>

fun ld :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> nat" where
  "ld e (Abs a A t) T = ld (e\<langle>0:dom_type T\<rangle>) t (rng_type T)"
| "ld e (s $ t) T = max (ld e s (spine_type e s)) (Suc (ld e t (dom_type (spine_type e s))))"
| "ld e t T = type_depth T"

lemma ld_ge_type_depth: "\<not> is_Abs s \<Longrightarrow> type_depth (spine_type e s) \<le> ld e s (spine_type e s)"
proof (induction s)
  case (App s t)
  show ?case
  proof (cases "is_Abs s")
    case True
    then show ?thesis by (cases s) auto
  next
    case False
    with App.IH(1) type_depth_rng[of "spine_type e s"] show ?thesis by auto
  qed
qed auto

text \<open>The literal bound variables of a term are not negative (true for typed terms):\<close>

lemma ld_env_cong:
  "bnds_nonneg t \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> loose_bvar1 t i \<Longrightarrow> e' i = e i) \<Longrightarrow>
    spine_type e' t = spine_type e t \<and> ld e' t T = ld e t T"
proof (induction t arbitrary: e e' T)
  case (Abs a A t)
  have "ld (e'\<langle>0:dom_type T\<rangle>) t (rng_type T) = ld (e\<langle>0:dom_type T\<rangle>) t (rng_type T)"
  proof (rule conjunct2[OF Abs.IH])
    show "bnds_nonneg t" using Abs.prems(1) by simp
    fix i assume i: "0 \<le> i" "loose_bvar1 t i"
    show "(e'\<langle>0:dom_type T\<rangle>) i = (e\<langle>0:dom_type T\<rangle>) i"
    proof (cases "i = 0")
      case False
      with i have "loose_bvar1 (Abs a A t) (i - 1)" "0 \<le> i - 1" by (simp_all add: integer_arith)
      from Abs.prems(2)[OF this(2,1)] False i(1) show ?thesis by (simp add: integer_arith)
    qed simp
  qed
  then show ?case by simp
next
  case (App s t)
  have hs: "spine_type e' s = spine_type e s" "\<And>T. ld e' s T = ld e s T"
    using App.IH(1)[of e' e] App.prems by auto
  have ht: "\<And>T. ld e' t T = ld e t T" using App.IH(2)[of e' e] App.prems by auto
  show ?case using hs ht by simp
qed auto

lemma unname_spine_type [simp]: "spine_type e (unname t) = spine_type e t"
  by (induction t) auto

lemma ld_unname [simp]: "ld e (unname t) T = ld e t T"
  by (induction t arbitrary: e T) auto

lemma ld_aconv: "aconv_term s t \<Longrightarrow> ld e s T = ld e t T"
  by (metis aconv_term_unname ld_unname)


subsection \<open>Invariance under \<open>\<eta>\<close>-reduction\<close>

lemma bnds_nonneg_abs_list [simp]: "bnds_nonneg (abs_list bs t) \<longleftrightarrow> bnds_nonneg t"
proof (induction bs)
  case (Cons b bs)
  then show ?case by (cases b) simp
qed simp

lemma bnds_nonneg_app: "bnds_nonneg (app (Var x T) is) \<longleftrightarrow> (\<forall>i\<in>set is. 0 \<le> i)"
  by (auto simp: app_apps bnds_nonneg_apps)

lemma bnds_nonneg_subst: "bnds_nonneg t \<Longrightarrow> bnds_nonneg s \<Longrightarrow> 0 \<le> k \<Longrightarrow> bnds_nonneg (t[s/k])"
proof (induction t arbitrary: s k)
  case (Abs a T t)
  then show ?case by (simp add: bnds_nonneg_incr_bv)
qed (auto simp: subst_Bound integer_arith)

context pure_sig
begin

lemma spine_type_rename:
  "nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> spine_type e (rename f d t) = spine_type (renv e f d) t"
  by (induction t) (auto simp: renv_def nonneg_def integer_arith)

lemma ld_rename:
  "nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> ld e (rename f d t) T = ld (renv e f d) t T"
proof (induction t arbitrary: e d T)
  case (Abs a A t)
  then show ?case by (simp add: renv_shift integer_arith)
next
  case (App s t)
  then show ?case by (simp add: spine_type_rename)
qed auto

lemma spine_type_typing: "e \<turnstile> s : T \<Longrightarrow> no_redex s \<Longrightarrow> \<not> is_Abs s \<Longrightarrow> spine_type e s = T"
proof (induction s arbitrary: T)
  case (App s t)
  then obtain A where "e \<turnstile> s : A \<rightarrow>\<^sub>T T" by auto
  with App show ?case by force
qed auto

lemma ld_subst_dummy:
  "\<not> loose_bvar1 s k \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    spine_type e (s[u/k]) = spine_type (e\<langle>k:A\<rangle>) s \<and> ld e (s[u/k]) T = ld (e\<langle>k:A\<rangle>) s T"
proof (induction s arbitrary: e k u T)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound)
next
  case (Abs a B s)
  have "ld (e\<langle>0:dom_type T\<rangle>) (s[lift u 0/k + 1]) (rng_type T) = ld (e\<langle>0:dom_type T\<rangle>\<langle>k + 1:A\<rangle>) s (rng_type T)"
  proof -
    have IH: "ld e' (s[u'/k']) T' = ld (e'\<langle>k':A\<rangle>) s T'" if "\<not> loose_bvar1 s k'" "0 \<le> k'" for e' k' u' T'
      using Abs.IH that by blast
    show ?thesis using IH Abs.prems by (simp add: integer_arith)
  qed
  with Abs.prems show ?case by simp
next
  case (App s t)
  then show ?case by simp
qed auto

lemma ld_eta:
  assumes "s \<rightarrow>\<^sub>\<eta> t" "e \<turnstile> s : T" "no_redex s"
  shows "ld e t T = ld e s T \<and> no_redex t"
  using assms
proof (induction arbitrary: e T rule: eta.induct)
  case (eta s a A dummy)
  from eta.prems(1) obtain U where T: "T = A \<rightarrow>\<^sub>T U" and ty: "e\<langle>0:A\<rangle> \<turnstile> s : A \<rightarrow>\<^sub>T U"
    by auto
  have nr: "no_redex s" "\<not> is_Abs s" using eta.prems(2) by auto
  have sp: "spine_type (e\<langle>0:A\<rangle>) s = A \<rightarrow>\<^sub>T U" using spine_type_typing[OF ty nr] .
  have "type_depth (A \<rightarrow>\<^sub>T U) \<le> ld (e\<langle>0:A\<rangle>) s (A \<rightarrow>\<^sub>T U)"
    using ld_ge_type_depth[OF nr(2), of "e\<langle>0:A\<rangle>"] sp by simp
  then have "ld e (Abs a A (s $ Bound 0)) T = ld (e\<langle>0:A\<rangle>) s (A \<rightarrow>\<^sub>T U)"
    by (simp add: T sp)
  moreover have "ld e (s[dummy/0]) (A \<rightarrow>\<^sub>T U) = ld (e\<langle>0:A\<rangle>) s (A \<rightarrow>\<^sub>T U)"
    using ld_subst_dummy[OF eta.hyps] by simp
  moreover have "no_redex (s[dummy/0])"
    using no_redex_eta[OF eta.eta[OF eta.hyps, of a A dummy]] eta.prems(2) by simp
  ultimately show ?case by (simp add: T)
next
  case (appL s t u)
  from appL.prems obtain A where tys: "e \<turnstile> s : A \<rightarrow>\<^sub>T T" and tyu: "e \<turnstile> u : A" by auto
  have nr: "no_redex s" "\<not> is_Abs s" "no_redex u" using appL.prems(2) by auto
  from appL.IH[OF tys nr(1)] have IH: "ld e t (A \<rightarrow>\<^sub>T T) = ld e s (A \<rightarrow>\<^sub>T T)" "no_redex t" by auto
  have nAt: "\<not> is_Abs t" using eta_not_Abs[OF appL.hyps nr(2)] .
  moreover have "e \<turnstile> t : A \<rightarrow>\<^sub>T T" using subject_reduction_eta[OF appL.hyps tys] .
  ultimately have "spine_type e t = A \<rightarrow>\<^sub>T T" using spine_type_typing IH(2) by blast
  moreover have "spine_type e s = A \<rightarrow>\<^sub>T T" using spine_type_typing[OF tys nr(1,2)] .
  ultimately show ?case using IH nr nAt by simp
next
  case (appR s t u)
  from appR.prems obtain A where tyu: "e \<turnstile> u : A \<rightarrow>\<^sub>T T" and tys: "e \<turnstile> s : A" by auto
  have nr: "no_redex u" "\<not> is_Abs u" "no_redex s" using appR.prems(2) by auto
  from appR.IH[OF tys nr(3)] have IH: "ld e t A = ld e s A" "no_redex t" by auto
  have "spine_type e u = A \<rightarrow>\<^sub>T T" using spine_type_typing[OF tyu nr(1,2)] .
  then show ?case using IH nr by simp
next
  case (abs s t a A)
  from abs.prems obtain U where T: "T = A \<rightarrow>\<^sub>T U" and ty: "e\<langle>0:A\<rangle> \<turnstile> s : U" by auto
  from abs.IH[OF ty] abs.prems(2) show ?case by (simp add: T)
qed

lemma ld_reds:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t" "e \<turnstile> s : T" "no_redex s"
  shows "ld e t T = ld e s T \<and> no_redex t"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case (step t u)
  have "e \<turnstile> t : T" using subject_reduction_reds[OF step.hyps(1) assms(2)] .
  moreover from step.IH have "no_redex t" by simp
  moreover from this step.hyps(2) have "t \<rightarrow>\<^sub>\<eta> u" by (auto simp: no_redex_iff)
  ultimately show ?case using ld_eta step.IH by metis
qed (simp add: assms(3))

lemma ld_conv:
  assumes "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" "e \<turnstile> s : T" "e \<turnstile> t : T" "no_redex s" "no_redex t"
  shows "ld e s T = ld e t T"
proof -
  obtain u v where uv: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v" "aconv_term u v"
    using church_rosser[OF _ assms(1)] assms(2) by (auto simp: wt_def)
  have "ld e u T = ld e s T" using ld_reds[OF uv(1) assms(2,4)] by simp
  moreover have "ld e v T = ld e t T" using ld_reds[OF uv(2) assms(3,5)] by simp
  ultimately show ?thesis using ld_aconv[OF uv(3)] by simp
qed

lemma ld_abs_list: "ld e (abs_list bs t) (map snd bs \<Rrightarrow> T) = ld (pushes e (map snd bs)) t T"
  by (induction bs arbitrary: e) auto


text \<open>The soundness of the occurs check for a flex-rigid problem:\<close>

definition rocc_ok :: "env \<Rightarrow> binders \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> integer list \<Rightarrow> pterm \<Rightarrow> bool" where
  "rocc_ok env bs F Fty is t \<longleftrightarrow> (\<forall>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<longrightarrow>
    vars (app (Var F Fty) is) \<union> vars t \<subseteq> X \<longrightarrow> cterm \<rho> env e bs A (app (Var F Fty) is) T \<longrightarrow>
    cterm \<rho> env e bs A t T \<longrightarrow> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<longrightarrow>
    \<not> ok (rigid_occurs F t env) True)"

lemma step_cp_flexrigid':
  "distinct is \<Longrightarrow> rocc_ok env bs F Fty is t \<Longrightarrow>
    step_cp env bs (app (Var F Fty) is) t (flexrigid env bs F Fty is t)"
  by (rule step_cp_flexrigid) (auto simp: rocc_ok_def)

subsection \<open>The measure below rigid heads\<close>

lemma ld_apps:
  "\<not> is_Abs H \<Longrightarrow> spine_type e H = Ts \<Rrightarrow> T \<Longrightarrow> length ws = length Ts \<Longrightarrow>
    ld e H (Ts \<Rrightarrow> T) \<le> ld e (H \<degree>\<degree> ws) T \<and> (\<forall>i<length ws. Suc (ld e (ws ! i) (Ts ! i)) \<le> ld e (H \<degree>\<degree> ws) T)"
proof (induction ws arbitrary: H Ts)
  case (Cons w ws)
  then obtain U Us where Ts: "Ts = U # Us" "length ws = length Us" by (cases Ts) auto
  have sp: "spine_type e (H $ w) = Us \<Rrightarrow> T" using Cons.prems(2) Ts by simp
  have IH: "ld e (H $ w) (Us \<Rrightarrow> T) \<le> ld e (H $ w \<degree>\<degree> ws) T"
    "\<forall>i<length ws. Suc (ld e (ws ! i) (Us ! i)) \<le> ld e (H $ w \<degree>\<degree> ws) T"
    using Cons.IH[of "H $ w" Us] sp Ts(2) by auto
  have l: "ld e (H $ w) (Us \<Rrightarrow> T) = max (ld e H (Ts \<Rrightarrow> T)) (Suc (ld e w U))"
    using Cons.prems(2) Ts by simp
  show ?case
  proof (intro conjI allI impI)
    show "ld e H (Ts \<Rrightarrow> T) \<le> ld e (H \<degree>\<degree> (w # ws)) T" using IH(1) l Cons.prems(2) by simp
    fix i assume i: "i < length (w # ws)"
    show "Suc (ld e ((w # ws) ! i) (Ts ! i)) \<le> ld e (H \<degree>\<degree> (w # ws)) T"
    proof (cases i)
      case 0
      then show ?thesis using IH(1) l Ts Cons.prems(2) by simp
    next
      case (Suc j)
      then show ?thesis using IH(2) i Ts by simp
    qed
  qed
qed simp

lemma ld_rigid:
  assumes h: "rigid h" and ty: "e \<turnstile> inst \<rho> (h \<degree>\<degree> ts) : T" and \<sigma>: "wt_subst \<sigma>"
    and N: "normal N" "ap \<rho> \<sigma> (h \<degree>\<degree> ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" "e \<turnstile> N : T"
  obtains Ts where "e \<tturnstile> map (inst \<rho>) ts : Ts"
    "\<And>i Ni. i < length ts \<Longrightarrow> normal Ni \<Longrightarrow> ap \<rho> \<sigma> (ts ! i) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni \<Longrightarrow> Suc (ld e Ni (Ts ! i)) \<le> ld e N T"
proof -
  have ty': "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) ts : T" using ty by (simp add: inst_apps)
  then obtain Ts where th: "e \<turnstile> inst \<rho> h : Ts \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Ts"
    by (rule list_app_typeE)
  note tn = typings_nth[OF tts]
  have tya: "e \<turnstile> ap \<rho> \<sigma> (ts ! i) : Ts ! i" if "i < length ts" for i
    using typing_ap[of e \<rho> "ts ! i" "Ts ! i" \<sigma>] tn that \<sigma> by simp
  have wts: "\<forall>t\<in>set (map (ap \<rho> \<sigma>) ts). wt t"
  proof
    fix t assume "t \<in> set (map (ap \<rho> \<sigma>) ts)"
    then obtain i where "i < length ts" "t = ap \<rho> \<sigma> (ts ! i)" by (auto simp: in_set_conv_nth)
    then show "wt t" using tya by (auto simp: wt_def)
  qed
  obtain Ns where Ns: "list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<and> normal N) (map (ap \<rho> \<sigma>) ts) Ns"
    using normal_forms_list[OF wts] by blast
  have lenN: "length Ns = length ts" using list_all2_lengthD[OF Ns] by simp
  have Nsi: "ap \<rho> \<sigma> (ts ! i) \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Ns ! i" "normal (Ns ! i)" if "i < length ts" for i
    using list_all2_nthD[OF Ns, of i] that by simp_all
  let ?M = "inst \<rho> h \<degree>\<degree> Ns"
  have apeq: "ap \<rho> \<sigma> (h \<degree>\<degree> ts) = inst \<rho> h \<degree>\<degree> map (ap \<rho> \<sigma>) ts"
    using h by (simp add: ap_apps rigid_ap)
  have r: "ap \<rho> \<sigma> (h \<degree>\<degree> ts) \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* ?M"
    unfolding apeq by (rule reds_apps, rule list_all2_mono[OF Ns]) blast
  have tyap: "e \<turnstile> ap \<rho> \<sigma> (h \<degree>\<degree> ts) : T" by (rule typing_ap[OF ty \<sigma>])
  have tyM: "e \<turnstile> ?M : T" by (rule subject_reduction_reds[OF r tyap])
  have cM: "N \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?M"
    using N(2) beta_eta_conv[OF r] tyap by (auto simp: wt_def intro: conv_sym conv_trans)
  have at: "atom (inst \<rho> h)" by (rule rigid_inst[OF h])
  have nrM: "no_redex ?M"
  proof (subst no_redex_apps)
    show "\<not> is_Abs (inst \<rho> h)" using at by (auto elim: atom.elims)
    have "\<forall>N\<in>set Ns. normal N" using Nsi lenN by (auto simp: in_set_conv_nth)
    then show "no_redex (inst \<rho> h) \<and> (\<forall>t\<in>set Ns. no_redex t)"
      using at by (auto simp: normal_iff elim: atom.elims)
  qed
  have lN: "ld e N T = ld e ?M T"
    by (rule ld_conv[OF cM N(3) tyM]) (use N(1) nrM in \<open>simp_all add: normal_iff\<close>)
  have sp: "spine_type e (inst \<rho> h) = Ts \<Rrightarrow> T"
    using spine_type_typing[OF th] at by (auto elim: atom.elims)
  have la: "\<forall>i<length Ns. Suc (ld e (Ns ! i) (Ts ! i)) \<le> ld e ?M T"
    using ld_apps[OF _ sp] at lenN tn by (auto elim: atom.elims)
  show ?thesis
  proof (rule that[OF tts])
    fix i Ni assume i: "i < length ts" and Ni: "normal Ni" "ap \<rho> \<sigma> (ts ! i) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni"
    have wi: "wt (ap \<rho> \<sigma> (ts ! i))" using tya[OF i] by (auto simp: wt_def)
    have "Ni \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ns ! i" using Ni(2) beta_eta_conv[OF Nsi(1)[OF i] wi] by (blast intro: conv_sym conv_trans)
    moreover have "wt Ni" using Ni(2) wi wt_conv by blast
    ultimately have "aconv_term Ni (Ns ! i)" using Ni(1) Nsi(2)[OF i] by (intro conv_normal_aconv)
    then have "ld e Ni (Ts ! i) = ld e (Ns ! i) (Ts ! i)" by (rule ld_aconv)
    with la lenN i lN show "Suc (ld e Ni (Ts ! i)) \<le> ld e N T" by simp
  qed
qed


subsection \<open>Flex occurrences\<close>

text \<open>
  The measure of (a normal form of) \<open>u xs\<close>, for closed \<open>u\<close>, is that of the normal form of \<open>u\<close>:
\<close>

lemma ld_flex:
  assumes u: "closed u" "\<And>e'. e' \<turnstile> u : map e xs \<Rrightarrow> T" and cert: "\<forall>x\<in>set xs. cert_typ alg ar (e x)"
    and nF: "u \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* nF" "normal nF" and xs: "\<forall>x\<in>set xs. 0 \<le> x"
    and N: "normal N" "e \<turnstile> N : T" "u \<degree>\<degree> map Bound xs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N"
  shows "ld e N T = ld e0 nF (map e xs \<Rrightarrow> T)"
proof -
  let ?Us = "map e xs"
  obtain B where B: "normal B" "\<not> loose_bvar B (ilength ?Us)" "\<And>e'. pushes e' ?Us \<turnstile> B : T"
    "\<And>bs. map snd bs = ?Us \<Longrightarrow> \<forall>U\<in>set ?Us. cert_typ alg ar U \<Longrightarrow> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B"
    "\<And>xs'. length xs' = length ?Us \<Longrightarrow> \<forall>i\<in>set xs'. 0 \<le> i \<Longrightarrow>
      u \<degree>\<degree> map Bound xs' \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* rename (bren (rev xs')) 0 B"
    using canonical_body[OF u(1) u(2)] by blast
  let ?bs = "map (\<lambda>U. (STR '''', U)) ?Us"
  have mbs: "map snd ?bs = ?Us" by (simp add: comp_def)
  have certU: "\<forall>U\<in>set ?Us. cert_typ alg ar U" using cert by auto
  have tyu: "e0 \<turnstile> u : ?Us \<Rrightarrow> T" by (rule u(2))
  have "pushes e0 (map snd ?bs) \<turnstile> B : T" using B(3) by (simp only: mbs)
  moreover have "\<forall>U\<in>snd ` set ?bs. cert_typ alg ar U" using certU by auto
  ultimately have "e0 \<turnstile> abs_list ?bs B : map snd ?bs \<Rrightarrow> T" by (rule typing_abs_list)
  then have tyabs: "e0 \<turnstile> abs_list ?bs B : ?Us \<Rrightarrow> T" by (simp only: mbs)
  have tynF: "e0 \<turnstile> nF : ?Us \<Rrightarrow> T" by (rule subject_reduction_reds[OF nF(1) tyu])
  have "nF \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs B"
    using beta_eta_conv[OF nF(1)] tyu B(4)[OF mbs certU] by (auto simp: wt_def intro: conv_sym conv_trans)
  then have l1: "ld e0 nF (?Us \<Rrightarrow> T) = ld e0 (abs_list ?bs B) (?Us \<Rrightarrow> T)"
    by (rule ld_conv[OF _ tynF tyabs]) (use nF(2) B(1) in \<open>simp_all add: normal_iff\<close>)
  have l2: "ld e0 (abs_list ?bs B) (?Us \<Rrightarrow> T) = ld (pushes e0 ?Us) B T"
    using ld_abs_list[of e0 ?bs B T] by (simp only: mbs)
  let ?R = "rename (bren (rev xs)) 0 B"
  have nx: "nonneg (bren (rev xs))" using xs by (simp add: nonneg_bren)
  have lenx: "length xs = length ?Us" by simp
  have r: "u \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* ?R" by (rule B(5)[OF lenx xs])
  have l3: "ld e ?R T = ld (renv e (bren (rev xs)) 0) B T" by (rule ld_rename[OF nx order_refl])
  have l4: "ld (renv e (bren (rev xs)) 0) B T = ld (pushes e0 ?Us) B T"
  proof (rule conjunct2[OF ld_env_cong])
    show "bnds_nonneg B" by (rule typing_bnds_nonneg[OF B(3)])
    fix k assume k: "0 \<le> k" "loose_bvar1 B k"
    have kn: "k < ilength xs" using loose_bvar1_less[OF B(2) k(2)] by simp
    have "renv e (bren (rev xs)) 0 k = e (rev xs ! nat_of_integer k)"
      using k(1) kn by (simp add: renv_def bren_rev)
    also have "\<dots> = rev ?Us ! nat_of_integer k"
      using nat_of_integer_less_ilength[OF k(1) kn] by (simp add: rev_map)
    also have "\<dots> = pushes e0 ?Us k" using k(1) kn by (simp add: pushes_nth)
    finally show "renv e (bren (rev xs)) 0 k = pushes e0 ?Us k" .
  qed
  have tyx: "e \<turnstile> u \<degree>\<degree> map Bound xs : T" by (rule typing_apps_Bounds[OF u(1) u(2) xs])
  have cR: "N \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?R"
    using N(3) beta_eta_conv[OF r] tyx by (auto simp: wt_def intro: conv_sym conv_trans)
  moreover have "wt N" using N(2) by (auto simp: wt_def)
  ultimately have "aconv_term N ?R" using N(1) B(1) nx by (intro conv_normal_aconv) (simp_all add: normal_rename)
  then have "ld e N T = ld e ?R T" by (rule ld_aconv)
  with l1 l2 l3 l4 show ?thesis by simp
qed


subsection \<open>Rigid occurrences\<close>

lemma pterm_case_nonAbs: "\<not> is_Abs t \<Longrightarrow> (case t of Abs a T u \<Rightarrow> f a T u | _ \<Rightarrow> g) = g"
  by (cases t) auto

lemma existsM_TrueE: "existsM P xs = Some (Ok True) \<Longrightarrow> \<exists>x\<in>set xs. P x = Some (Ok True)"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits if_splits)

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

text \<open>
  A rigid occurrence of \<open>F\<close> in \<open>t\<close> bounds the measure of the instances of \<open>t\<close> from below by that of
  the value of \<open>F\<close>.
\<close>

lemma rocc_ld:
  assumes "rigid_occurs F t env = Some r"
  shows "r = Ok True \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> vinv \<rho> env X \<Longrightarrow> (F, Fty) \<in> X \<Longrightarrow>
    vars t \<subseteq> X \<union> evars env \<Longrightarrow> e \<turnstile> inst \<rho> t : T \<Longrightarrow>
    \<sigma> F (tsubst \<rho> Fty) \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* nF \<Longrightarrow> normal nF \<Longrightarrow> cert_typ alg ar (tsubst \<rho> Fty) \<Longrightarrow>
    normal N \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N \<Longrightarrow> e \<turnstile> N : T \<Longrightarrow> ld e0 nF (tsubst \<rho> Fty) \<le> ld e N T"
  using assms
proof (induction F t env r arbitrary: e T N rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note sol = "1.prems"(2) and wte = "1.prems"(3) and vi = "1.prems"(4) and FX = "1.prems"(5)
    and Xt = "1.prems"(6) and ty = "1.prems"(7) and nF = "1.prems"(8,9) and cF = "1.prems"(10)
    and N = "1.prems"(11-13)
  have \<sigma>: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  have IH: "ld e0 nF (tsubst \<rho> Fty) \<le> ld e' N' T'"
    if "ok (ro F t' env) True" "vars t' \<subseteq> X \<union> evars env" "e' \<turnstile> inst \<rho> t' : T'" "normal N'"
      "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N'" "e' \<turnstile> N' : T'" for t' e' T' N'
    using "1.IH"[OF that(1) refl sol wte vi FX that(2,3) nF cF that(4-6)] .
  from h obtain t' where hn: "ok (head_norm env t) t'" and rest: "ok (case t' of
        Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              Var G _ \<Rightarrow>
                if G = F then
                  handle (do {_ \<leftarrow> ints_of' env ts; return True})
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts))) True"
    by auto
  have hs: "e \<turnstile> inst \<rho> t' : T \<and> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
    using head_norm_sound[OF hn refl solutionD(2)[OF sol] wte ty] sol by blast
  have Xt': "vars t' \<subseteq> X \<union> evars env" using head_norm_vars[OF hn refl] Xt by blast
  have Nt': "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using hs N(2) by (blast intro: conv_sym conv_trans)
  show ?case
  proof (cases "is_Abs t'")
    case True
    then obtain a A b where t': "t' = Abs a A b" by (cases t') auto
    from rest t' have rb: "ok (ro F b env) True" by simp
    from hs t' obtain U where T: "T = tsubst \<rho> A \<rightarrow>\<^sub>T U" and cA: "cert_typ alg ar (tsubst \<rho> A)"
      and tb: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> inst \<rho> b : U"
      by auto
    have tab: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> ap \<rho> \<sigma> b : U" by (rule typing_ap[OF tb \<sigma>])
    obtain Nb where Nb: "ap \<rho> \<sigma> b \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Nb" "normal Nb" using normal_form_ex[OF tab] .
    have tNb: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> Nb : U" by (rule subject_reduction_reds[OF Nb(1) tab])
    have cb: "ap \<rho> \<sigma> b \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Nb" using beta_eta_conv[OF Nb(1)] tab by (auto simp: wt_def)
    have K: "ld e0 nF (tsubst \<rho> Fty) \<le> ld (e\<langle>0:tsubst \<rho> A\<rangle>) Nb U"
      by (rule IH[OF rb _ tb Nb(2) cb tNb]) (use Xt' t' in simp)
    have tM: "e \<turnstile> Abs a (tsubst \<rho> A) Nb : T" using tNb cA T by auto
    have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> A) Nb"
      using conv_Abs[OF _ _ cb, of a "tsubst \<rho> A" a] typing_ap[OF conjunct1[OF hs] \<sigma>] tM t'
      by (auto simp: wt_def)
    then have "N \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> A) Nb" using Nt' by (blast intro: conv_sym conv_trans)
    then have "ld e N T = ld e (Abs a (tsubst \<rho> A) Nb) T"
      by (rule ld_conv[OF _ N(3) tM]) (use N(1) Nb(2) in \<open>simp_all add: normal_iff\<close>)
    with K T show ?thesis by simp
  next
    case nAbs: False
    obtain h0 ts where hts: "strip_comb t' = (h0, ts)" by force
    have t': "t' = h0 \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
    have rest': "ok (case h0 of
              Var G _ \<Rightarrow>
                if G = F then
                  handle (do {_ \<leftarrow> ints_of' env ts; return True})
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts) True"
      using rest nAbs hts by (cases t') auto
    show ?thesis
    proof (cases "is_Var h0")
      case True
      then obtain G Gty where hG: "h0 = Var G Gty" by (cases h0) auto
      have nh: False if "ok (case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) True" for e
        using that by (cases e) auto
      from rest' hG obtain js where GF: "G = F" and js: "ok (ints_of' env ts) js"
        by (auto simp: ok_handle split: if_splits dest: nh)
      have tyG: "e \<turnstile> inst \<rho> (Var F Gty \<degree>\<degree> ts) : T" using hs t' hG GF by simp
      note f = flex_sound[OF js solutionD(2)[OF sol] wte tyG]
      have "(F, Gty) \<in> X \<union> evars env" using Xt' t' hG GF by (auto simp: vars_apps)
      then have FG: "tsubst \<rho> Gty = tsubst \<rho> Fty" using vi FX unfolding vinv_def by (blast dest: vconsD)
      from f(1) obtain Gty_eq: "tsubst \<rho> Gty = map e js \<Rrightarrow> T" and js0: "\<forall>j\<in>set js. 0 \<le> j"
        by (rule typing_appE)
      let ?u = "\<sigma> F (tsubst \<rho> Fty)"
      have cu: "closed ?u" using \<sigma> by (cases F) (simp add: wt_subst_def closed_subst_def)
      have tu: "e' \<turnstile> ?u : map e js \<Rrightarrow> T" for e'
        using wt_subst_typing[OF \<sigma> cF] FG Gty_eq by simp
      have eqF: "tsubst \<rho> Fty = map e js \<Rrightarrow> T" using FG Gty_eq by simp
      have certs: "\<forall>j\<in>set js. cert_typ alg ar (e j)"
        using cF[unfolded eqF] by (simp add: cert_typ_funs)
      have "ap \<rho> \<sigma> (app (Var F Gty) js) = ?u \<degree>\<degree> map Bound js"
        using FG by (simp add: app_apps ap_apps comp_def)
      then have "?u \<degree>\<degree> map Bound js \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N"
        using f(2)[OF sol] Nt' t' hG GF by (metis conv_sym conv_trans)
      from ld_flex[OF cu tu certs nF js0 N(1,3) this, of e0]
      show ?thesis using FG Gty_eq by simp
    next
      case nVar: False
      show ?thesis
      proof (cases "is_Abs h0")
        case True
        with rest' show ?thesis by (cases h0) auto
      next
        case nAbsh: False
        have rh: "rigid h0"
          using nVar nAbsh strip_comb_head[OF hts] by (cases h0) auto
        have "existsM (\<lambda>u. ro F u env) ts = Some (Ok True)"
          using rest' rh by (cases h0) auto
        then obtain ti where ti: "ti \<in> set ts" "ok (ro F ti env) True" by (blast dest: existsM_TrueE)
        then obtain i where i: "i < length ts" "ti = ts ! i" by (auto simp: in_set_conv_nth)
        have tyt': "e \<turnstile> inst \<rho> (h0 \<degree>\<degree> ts) : T" using hs t' by simp
        obtain Ts where tts: "e \<tturnstile> map (inst \<rho>) ts : Ts"
          and lt: "\<And>i Ni. i < length ts \<Longrightarrow> normal Ni \<Longrightarrow> ap \<rho> \<sigma> (ts ! i) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni \<Longrightarrow>
            Suc (ld e Ni (Ts ! i)) \<le> ld e N T"
          using ld_rigid[OF rh tyt' \<sigma> N(1) _ N(3)] Nt' t' by blast
        have tyi: "e \<turnstile> inst \<rho> ti : Ts ! i" using typings_nth[OF tts] i by auto
        have tai: "e \<turnstile> ap \<rho> \<sigma> ti : Ts ! i" by (rule typing_ap[OF tyi \<sigma>])
        obtain Ni where Ni: "ap \<rho> \<sigma> ti \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Ni" "normal Ni" using normal_form_ex[OF tai] .
        have tNi: "e \<turnstile> Ni : Ts ! i" by (rule subject_reduction_reds[OF Ni(1) tai])
        have cNi: "ap \<rho> \<sigma> ti \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni" using beta_eta_conv[OF Ni(1)] tai by (auto simp: wt_def)
        have "vars ti \<subseteq> X \<union> evars env" using Xt' t' ti(1) by (auto simp: vars_apps)
        from IH[OF ti(2) this tyi Ni(2) cNi tNi] lt[OF i(1) Ni(2)] cNi i(2)
        show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>The occurs check is sound: a rigid occurrence makes a flex-rigid problem unsolvable.\<close>

theorem rocc_ok_rigid:
  assumes hts: "strip_comb t = (h, ts)" and rh: "rigid h"
  shows "rocc_ok env bs F Fty is t"
  unfolding rocc_ok_def
proof (intro allI impI notI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (app (Var F Fty) is) \<union> vars t \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (app (Var F Fty) is) T" and ct: "cterm \<rho> env e bs A t T"
    and eq: "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
    and ro: "ok (rigid_occurs F t env) True"
  note i = inv[unfolded cinv_def]
  have sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and vi: "vinv \<rho> env X" using i by blast+
  have \<sigma>: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  have t: "t = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
  have nAt: "\<not> is_Abs t" using t rh is_Abs_apps[of h ts] by (cases h) auto
  have hn: "head_norm env t = return t" using head_norm_rigid_apps[OF rh, of env ts] t by simp
  have "rigid_occurs F t env = existsM (\<lambda>u. rigid_occurs F u env) ts"
    by (subst rigid_occurs.simps) (use rh in \<open>simp add: hn pterm_case_nonAbs[OF nAt] hts, cases h, auto\<close>)
  with ro obtain ti where ti: "ti \<in> set ts" "ok (rigid_occurs F ti env) True"
    by (auto dest: existsM_TrueE)
  then obtain k where k: "k < length ts" "ti = ts ! k" by (auto simp: in_set_conv_nth)
  note fd = flex_data[OF inv cs]
  let ?u = "\<sigma> F (tsubst \<rho> Fty)"
  have tyu: "e0 \<turnstile> ?u : tsubst \<rho> Fty" for e0 using wt_subst_typing[OF \<sigma> fd(2)] .
  obtain nF where nF: "?u \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* nF" "normal nF" using normal_form_ex[OF tyu] .
  have tyt: "e \<turnstile> inst \<rho> t : T" using ct by (simp add: cterm_def)
  have tat: "e \<turnstile> ap \<rho> \<sigma> t : T" by (rule typing_ap[OF tyt \<sigma>])
  obtain N where N: "ap \<rho> \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using normal_form_ex[OF tat] .
  have tN: "e \<turnstile> N : T" by (rule subject_reduction_reds[OF N(1) tat])
  have cN: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using beta_eta_conv[OF N(1)] tat by (auto simp: wt_def)
  have "?u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using eq fd(6) cN by (metis conv_trans)
  from ld_flex[OF fd(4) fd(5) fd(8) nF _ N(2) tN this, of "(\<lambda>_. TFree STR '''' [])"] fd(1,3)
  have K: "ld e N T = ld (\<lambda>_. TFree STR '''' []) nF (tsubst \<rho> Fty)" by auto
  have tyt': "e \<turnstile> inst \<rho> (h \<degree>\<degree> ts) : T" using tyt t by simp
  obtain Ts where tts: "e \<tturnstile> map (inst \<rho>) ts : Ts"
    and lt: "\<And>i Ni. i < length ts \<Longrightarrow> normal Ni \<Longrightarrow> ap \<rho> \<sigma> (ts ! i) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni \<Longrightarrow>
      Suc (ld e Ni (Ts ! i)) \<le> ld e N T"
    using ld_rigid[OF rh tyt' \<sigma> N(2) _ tN] cN t by blast
  have tyi: "e \<turnstile> inst \<rho> ti : Ts ! k" using typings_nth[OF tts] k by auto
  have tai: "e \<turnstile> ap \<rho> \<sigma> ti : Ts ! k" by (rule typing_ap[OF tyi \<sigma>])
  obtain Ni where Ni: "ap \<rho> \<sigma> ti \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Ni" "normal Ni" using normal_form_ex[OF tai] .
  have tNi: "e \<turnstile> Ni : Ts ! k" by (rule subject_reduction_reds[OF Ni(1) tai])
  have cNi: "ap \<rho> \<sigma> ti \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ni" using beta_eta_conv[OF Ni(1)] tai by (auto simp: wt_def)
  have FX: "(F, Fty) \<in> X" using X by (auto simp: vars_apps)
  have vti: "vars ti \<subseteq> X \<union> evars env" using X ti(1) t by (auto simp: vars_apps)
  have "ld (\<lambda>_. TFree STR '''' []) nF (tsubst \<rho> Fty) \<le> ld e Ni (Ts ! k)"
    by (rule rocc_ld[OF ti(2) refl sol wte vi FX vti tyi nF fd(2) Ni(2) cNi tNi])
  moreover have "Suc (ld e Ni (Ts ! k)) \<le> ld e N T" using lt[OF k(1) Ni(2)] cNi k(2) by simp
  ultimately show False using K by simp
qed

end

end
