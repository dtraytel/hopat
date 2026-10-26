section \<open>The Occurs Check\<close>

theory Unif_Occurs
  imports Unif_Normal
begin

text \<open>
  Grobauer's Fact 9 (the occurs check): a problem \<open>F(x\<^sub>m) = a(t\<^sub>n)\<close> with a rigid head \<open>a\<close> and
  \<open>F\<close> occurring in some \<open>t\<^sub>i\<close> has no well-typed unifier. Without types this fails, so we use
  a type-directed measure: the depth of the \<open>\<eta>\<close>-long form of a \<open>\<beta>\<close>-normal term. This measure is
  invariant under \<open>\<eta>\<close>-reduction of well-typed \<open>\<beta>\<close>-normal terms and hence under \<open>\<beta>\<eta>\<close>-equivalence,
  but strictly increases when going below a rigid head.
\<close>

subsection \<open>Syntactic \<open>\<beta>\<close>-normality\<close>

fun is_Abs :: "dB \<Rightarrow> bool" where
  "is_Abs (Abs _) = True"
| "is_Abs _ = False"

fun no_redex :: "dB \<Rightarrow> bool" where
  "no_redex (Abs t) = no_redex t"
| "no_redex (s \<degree> t) = (\<not> is_Abs s \<and> no_redex s \<and> no_redex t)"
| "no_redex _ = True"

lemma no_redex_no_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> no_redex s \<Longrightarrow> False"
  by (induction rule: beta.induct) auto

lemma beta_normal_no_redex: "\<beta>_normal t \<Longrightarrow> no_redex t"
proof (induction t)
  case (App s t)
  then show ?case by (cases s) auto
qed auto

lemma normal_no_redex: "normal t \<Longrightarrow> no_redex t"
  by (rule beta_normal_no_redex) blast

lemma is_Abs_map_BVars[simp]: "is_Abs (map_BVars f t) = is_Abs t"
  by (cases t) auto

lemma no_redex_map_BVars[simp]: "no_redex (map_BVars f t) = no_redex t"
  by (induction t arbitrary: f) auto

lemma is_Abs_atom_apps: "is_atom h \<Longrightarrow> \<not> is_Abs (h \<degree>\<degree> ts)"
  by (cases ts rule: rev_cases) (auto simp: is_atom_def)

lemma no_redex_atom_apps: "is_atom h \<Longrightarrow> no_redex (h \<degree>\<degree> ts) \<longleftrightarrow> (\<forall>t\<in>set ts. no_redex t)"
  by (induction ts rule: rev_induct) (auto simp: is_Abs_atom_apps, auto simp: is_atom_def)

lemma eta_not_Abs: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> \<not> is_Abs s \<Longrightarrow> \<not> is_Abs t"
  by (induction rule: eta.induct) auto

lemma subst_dummy_map_BVars: "\<not> free s 0 \<Longrightarrow> s[dummy/0] = map_BVars (\<lambda>j. j - 1) s"
proof -
  assume "\<not> free s 0"
  then have "s[dummy/0] = s[BVar 0/0]" by (rule subst_not_free)
  also have "\<dots> = map_BVars (\<lambda>j. if 0 < j then j - 1 else if j = 0 then 0 else j) s"
    by (rule subst_BVar_map_BVars)
  also have "\<dots> = map_BVars (\<lambda>j. j - 1) s" by (intro map_BVars_cong) auto
  finally show ?thesis .
qed

subsection \<open>The measure\<close>

fun dom_type :: "type \<Rightarrow> type" where
  "dom_type (T \<Rightarrow> _) = T"
| "dom_type T = T"

fun rng_type :: "type \<Rightarrow> type" where
  "rng_type (_ \<Rightarrow> U) = U"
| "rng_type T = T"

text \<open>The depth of the \<open>\<eta>\<close>-long form of a variable of a given type.\<close>

fun type_depth :: "type \<Rightarrow> nat" where
  "type_depth (Atom _) = 0"
| "type_depth (T \<Rightarrow> U) = max (Suc (type_depth T)) (type_depth U)"

lemma type_depth_rng: "type_depth (rng_type T) \<le> type_depth T"
  by (cases T) auto

text \<open>The type of a term whose head is not an abstraction, computed from the type of its head.\<close>

fun spine_type :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type" where
  "spine_type e \<tau> (BVar x) = e x"
| "spine_type e \<tau> (Var F) = \<tau> F"
| "spine_type e \<tau> (s \<degree> t) = rng_type (spine_type e \<tau> s)"
| "spine_type e \<tau> (Abs t) = Atom 0"

text \<open>The depth of the \<open>\<eta>\<close>-long form of a term of a given type.\<close>

fun ld :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> nat" where
  "ld e \<tau> (BVar x) T = type_depth T"
| "ld e \<tau> (Var F) T = type_depth T"
| "ld e \<tau> (Abs t) T = ld (e\<langle>0:dom_type T\<rangle>) \<tau> t (rng_type T)"
| "ld e \<tau> (s \<degree> t) T =
    max (ld e \<tau> s (spine_type e \<tau> s)) (Suc (ld e \<tau> t (dom_type (spine_type e \<tau> s))))"

lemma spine_type_typing:
  "(e, \<tau>) \<turnstile> s : T \<Longrightarrow> no_redex s \<Longrightarrow> \<not> is_Abs s \<Longrightarrow> spine_type e \<tau> s = T"
proof (induction s arbitrary: T)
  case (App s t)
  then show ?case by auto
qed auto

lemma ld_ge_type_depth: "\<not> is_Abs s \<Longrightarrow> type_depth (spine_type e \<tau> s) \<le> ld e \<tau> s (spine_type e \<tau> s)"
proof (induction s)
  case (App s t)
  then show ?case
    using type_depth_rng[of "spine_type e \<tau> s"] by (cases s) auto
qed auto

lemma spine_type_map_BVars:
  "(\<And>v. v \<in> loose_BVars t \<Longrightarrow> e' (f v) = e v) \<Longrightarrow> spine_type e' \<tau> (map_BVars f t) = spine_type e \<tau> t"
  by (induction t) auto

lemma ld_map_BVars:
  "(\<And>v. v \<in> loose_BVars t \<Longrightarrow> e' (f v) = e v) \<Longrightarrow> ld e' \<tau> (map_BVars f t) T = ld e \<tau> t T"
proof (induction t arbitrary: e e' f T)
  case (Abs t)
  have "ld (e'\<langle>0:dom_type T\<rangle>) \<tau> (map_BVars (case_nat 0 (\<lambda>a. Suc (f a))) t) (rng_type T) =
    ld (e\<langle>0:dom_type T\<rangle>) \<tau> t (rng_type T)"
  proof (rule Abs.IH)
    fix v assume "v \<in> loose_BVars t"
    with Abs.prems show "(e'\<langle>0:dom_type T\<rangle>) (case v of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (f a)) = (e\<langle>0:dom_type T\<rangle>) v"
      by (cases v) (auto simp: shift_def)
  qed
  then show ?case by simp
next
  case (App s t)
  then show ?case by (simp add: spine_type_map_BVars)
qed auto

subsection \<open>Invariance under \<open>\<beta>\<eta>\<close>-equivalence\<close>

lemma ld_eta:
  assumes "s \<rightarrow>\<^sub>\<eta> t" "(e, \<tau>) \<turnstile> s : T" "no_redex s"
  shows "ld e \<tau> t T = ld e \<tau> s T \<and> no_redex t"
  using assms
proof (induction arbitrary: e T rule: eta.induct)
  case (eta s dummy)
  from eta.prems(1) obtain A U where T: "T = A \<Rightarrow> U" and ty: "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> s : A \<Rightarrow> U"
    by auto
  have nr: "no_redex s" "\<not> is_Abs s" using eta.prems(2) by auto
  have sp: "spine_type (e\<langle>0:A\<rangle>) \<tau> s = A \<Rightarrow> U" using spine_type_typing[OF ty nr] .
  have "type_depth (A \<Rightarrow> U) \<le> ld (e\<langle>0:A\<rangle>) \<tau> s (A \<Rightarrow> U)"
    using ld_ge_type_depth[OF nr(2), of "e\<langle>0:A\<rangle>" \<tau>] sp by simp
  then have "ld e \<tau> (Abs (s \<degree> BVar 0)) T = ld (e\<langle>0:A\<rangle>) \<tau> s (A \<Rightarrow> U)"
    by (simp add: T sp)
  moreover have "ld e \<tau> (map_BVars (\<lambda>j. j - 1) s) (A \<Rightarrow> U) = ld (e\<langle>0:A\<rangle>) \<tau> s (A \<Rightarrow> U)"
  proof (rule ld_map_BVars)
    fix v assume "v \<in> loose_BVars s"
    with eta.hyps have "v \<noteq> 0" by (auto simp: loose_BVars_free) (metis gr0I)
    then show "e (v - 1) = (e\<langle>0:A\<rangle>) v" by (cases v) (auto simp: shift_def)
  qed
  ultimately show ?case using nr eta.hyps by (simp add: subst_dummy_map_BVars T)
next
  case (appL s t u)
  from appL.prems obtain A where tys: "(e, \<tau>) \<turnstile> s : A \<Rightarrow> T" and tyu: "(e, \<tau>) \<turnstile> u : A" by auto
  have nr: "no_redex s" "\<not> is_Abs s" "no_redex u" using appL.prems(2) by auto
  from appL.IH[OF tys nr(1)] have IH: "ld e \<tau> t (A \<Rightarrow> T) = ld e \<tau> s (A \<Rightarrow> T)" "no_redex t" by auto
  have "\<not> is_Abs t" using eta_not_Abs[OF appL.hyps nr(2)] .
  moreover have "(e, \<tau>) \<turnstile> t : A \<Rightarrow> T" using subject_reduction_eta[OF appL.hyps tys] .
  ultimately have "spine_type e \<tau> t = A \<Rightarrow> T" using spine_type_typing IH(2) by blast
  moreover have "spine_type e \<tau> s = A \<Rightarrow> T" using spine_type_typing[OF tys nr(1,2)] .
  ultimately show ?case using IH nr \<open>\<not> is_Abs t\<close> by simp
next
  case (appR s t u)
  from appR.prems obtain A where tyu: "(e, \<tau>) \<turnstile> u : A \<Rightarrow> T" and tys: "(e, \<tau>) \<turnstile> s : A" by auto
  have nr: "no_redex u" "\<not> is_Abs u" "no_redex s" using appR.prems(2) by auto
  from appR.IH[OF tys nr(3)] have IH: "ld e \<tau> t A = ld e \<tau> s A" "no_redex t" by auto
  have "spine_type e \<tau> u = A \<Rightarrow> T" using spine_type_typing[OF tyu nr(1,2)] .
  then show ?case using IH nr by simp
next
  case (abs s t)
  from abs.prems obtain A U where T: "T = A \<Rightarrow> U" and ty: "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> s : U" by auto
  from abs.IH[OF ty] abs.prems(2) show ?case by (simp add: T)
qed

lemma ld_\<beta>\<eta>cl:
  assumes "\<beta>\<eta>cl s t" "(e, \<tau>) \<turnstile> s : T" "no_redex s"
  shows "ld e \<tau> t T = ld e \<tau> s T \<and> no_redex t"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case (step t u)
  have "(e, \<tau>) \<turnstile> t : T" using subject_reduction_\<beta>\<eta>[OF step.hyps(1) assms(2)] .
  moreover from step.IH have "no_redex t" by simp
  moreover from this step.hyps(2) have "t \<rightarrow>\<^sub>\<eta> u" by (auto dest: no_redex_no_beta)
  ultimately show ?case using ld_eta step.IH by metis
qed (simp add: assms(3))

lemma ld_equiv:
  assumes "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t" "(e, \<tau>) \<turnstile> s : T" "(e, \<tau>) \<turnstile> t : T" "no_redex s" "no_redex t"
  shows "ld e \<tau> s T = ld e \<tau> t T"
proof -
  from normal_form_ex[OF assms(2)] obtain n where n: "\<beta>\<eta>cl s n" "normal n" by blast
  have "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> n" using assms(1) n(1) by (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
  then have "\<beta>\<eta>cl t n" using n(2) by (rule equiv_\<beta>\<eta>cl_normal)
  with n(1) show ?thesis using ld_\<beta>\<eta>cl assms(2-5) by metis
qed

lemma ld_Abs_m: "length Ts = m \<Longrightarrow> ld e \<tau> (Abs_m m t) (Ts \<Rrightarrow> T) = ld (env_ext e Ts) \<tau> t T"
proof (induction Ts arbitrary: e m)
  case (Cons U Ts)
  then show ?case by (cases m) auto
qed simp

lemma no_redex_Abs_m[simp]: "no_redex (Abs_m m t) = no_redex t"
  by (induction m) auto

subsection \<open>Auxiliary lemmas\<close>

lemma typing_Var_app_BVars:
  "(e, \<tau>) \<turnstile> Var F \<degree>\<degree> map BVar xs : T \<longleftrightarrow> \<tau> F = map e xs \<Rrightarrow> T"
  by (auto simp: list_app_typing_iff typings_map_BVar)

lemma typing_BVar_app:
  "(e, \<tau>) \<turnstile> BVar p \<degree>\<degree> as : T \<longleftrightarrow> (\<exists>Us. e p = Us \<Rrightarrow> T \<and> (e, \<tau>) \<tturnstile> as : Us)"
  by (auto simp: list_app_typing_iff)

lemma env_ext_less: "z < length Ts \<Longrightarrow> env_ext e Ts z = Ts ! (length Ts - Suc z)"
  by (simp add: env_ext_nth)

lemma env_ext_downs: "map (env_ext e Ts) (downs (length Ts)) = Ts"
proof -
  have "map (env_ext e Ts) (downs (length Ts)) = map (\<lambda>i. Ts ! (length Ts - Suc i)) (downs (length Ts))"
    by (intro map_cong) (auto simp: env_ext_less)
  also have "\<dots> = Ts" by (rule map_downs) simp
  finally show ?thesis .
qed

lemma env_ext_map: "z < length xs \<Longrightarrow> env_ext e (map E xs) z = E (xs ! (length xs - Suc z))"
  by (simp add: env_ext_less)

lemma loose_BVars_no_loose_bound: "loose_BVars t \<subseteq> {..<b} \<Longrightarrow> no_loose_bound t b"
proof (induction t arbitrary: b)
  case (Abs t)
  have "loose_BVars t \<subseteq> {..<Suc b}"
  proof
    fix v assume "v \<in> loose_BVars t"
    with Abs.prems show "v \<in> {..<Suc b}" by (cases v) auto
  qed
  with Abs.IH show ?case by simp
qed auto

lemma typings_map2:
  assumes "length Hs = length Us" "\<And>i. i < length Hs \<Longrightarrow> e \<turnstile> Hs ! i : Us ! i"
  shows "e \<tturnstile> Hs : Us"
  using assms
proof (induction Hs Us rule: list_induct2)
  case (Cons H Hs U Us)
  have "e \<turnstile> H : U" using Cons.prems[of 0] by simp
  moreover have "e \<tturnstile> Hs : Us"
  proof (rule Cons.IH)
    fix i assume "i < length Hs"
    then show "e \<turnstile> Hs ! i : Us ! i" using Cons.prems[of "Suc i"] by simp
  qed
  ultimately show ?case by simp
qed simp

lemma normal_forms_list:
  assumes "\<And>i. i < length ts \<Longrightarrow> \<exists>w. \<beta>\<eta>cl (ts ! i) w \<and> normal w"
  obtains ws where "length ws = length ts" "\<And>i. i < length ts \<Longrightarrow> \<beta>\<eta>cl (ts ! i) (ws ! i) \<and> normal (ws ! i)"
proof
  let ?ws = "map (\<lambda>t. SOME w. \<beta>\<eta>cl t w \<and> normal w) ts"
  show "length ?ws = length ts" by simp
  fix i assume "i < length ts"
  from someI_ex[OF assms[OF this]] this show "\<beta>\<eta>cl (ts ! i) (?ws ! i) \<and> normal (?ws ! i)" by simp
qed

lemma ld_atom_apps:
  assumes "is_atom h" "(e, \<tau>) \<turnstile> h : Ts \<Rrightarrow> T" "(e, \<tau>) \<tturnstile> ws : Ts" "\<forall>w\<in>set ws. no_redex w"
    "i < length ws"
  shows "Suc (ld e \<tau> (ws ! i) (Ts ! i)) \<le> ld e \<tau> (h \<degree>\<degree> ws) T"
  using assms(2-5)
proof (induction ws arbitrary: Ts T i rule: rev_induct)
  case (snoc w ws)
  from snoc.prems(2) obtain Us U where Ts: "Ts = Us @ [U]" "(e, \<tau>) \<tturnstile> ws : Us" "(e, \<tau>) \<turnstile> w : U"
    by (elim types_snocE)
  have lenUs: "length Us = length ws" using typings_length[OF Ts(2)] .
  have h: "(e, \<tau>) \<turnstile> h : Us \<Rrightarrow> U \<Rightarrow> T" using snoc.prems(1) Ts(1) by simp
  have "(e, \<tau>) \<turnstile> h \<degree>\<degree> ws : U \<Rightarrow> T" using list_app_typeI[OF h Ts(2)] .
  moreover have "no_redex (h \<degree>\<degree> ws)" "\<not> is_Abs (h \<degree>\<degree> ws)"
    using snoc.prems(3) assms(1) by (simp_all add: no_redex_atom_apps is_Abs_atom_apps)
  ultimately have sp: "spine_type e \<tau> (h \<degree>\<degree> ws) = U \<Rightarrow> T" by (rule spine_type_typing)
  have ld: "ld e \<tau> (h \<degree>\<degree> (ws @ [w])) T = max (ld e \<tau> (h \<degree>\<degree> ws) (U \<Rightarrow> T)) (Suc (ld e \<tau> w U))"
    by (simp add: sp)
  show ?case
  proof (cases "i < length ws")
    case True
    have "Suc (ld e \<tau> (ws ! i) (Us ! i)) \<le> ld e \<tau> (h \<degree>\<degree> ws) (U \<Rightarrow> T)"
      using snoc.IH[OF h Ts(2) _ True] snoc.prems(3) by simp
    then show ?thesis using True Ts(1) lenUs ld by (simp add: nth_append)
  next
    case False
    with snoc.prems(4) have "i = length ws" by simp
    then show ?thesis using Ts(1) lenUs ld by (simp add: nth_append)
  qed
qed simp

lemma atom_apps_nf:
  assumes "is_atom h" "(e, \<tau>) \<turnstile> h : Ts \<Rrightarrow> T" "(e, \<tau>) \<tturnstile> ts : Ts"
  obtains ws where "length ws = length ts"
    "\<And>i. i < length ts \<Longrightarrow> \<beta>\<eta>cl (ts ! i) (ws ! i) \<and> normal (ws ! i) \<and> (e, \<tau>) \<turnstile> ws ! i : Ts ! i"
    "h \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ws" "no_redex (h \<degree>\<degree> ws)" "(e, \<tau>) \<turnstile> h \<degree>\<degree> ws : T"
    "\<And>i. i < length ts \<Longrightarrow> Suc (ld e \<tau> (ws ! i) (Ts ! i)) \<le> ld e \<tau> (h \<degree>\<degree> ws) T"
proof -
  have lenTs: "length Ts = length ts" using typings_length[OF assms(3)] .
  have ty: "(e, \<tau>) \<turnstile> ts ! i : Ts ! i" if "i < length ts" for i
    using typings_nth[OF assms(3) that] .
  obtain ws where ws: "length ws = length ts"
    "\<And>i. i < length ts \<Longrightarrow> \<beta>\<eta>cl (ts ! i) (ws ! i) \<and> normal (ws ! i)"
    using normal_forms_list[of ts] normal_form_ex[OF ty] by metis
  have tyws: "(e, \<tau>) \<turnstile> ws ! i : Ts ! i" if "i < length ts" for i
    using subject_reduction_\<beta>\<eta>[OF conjunct1[OF ws(2)[OF that]] ty[OF that]] .
  have tys: "(e, \<tau>) \<tturnstile> ws : Ts" using ws(1) lenTs tyws by (intro typings_map2) auto
  have nr: "\<forall>w\<in>set ws. no_redex w"
  proof
    fix w assume "w \<in> set ws"
    then obtain i where "i < length ts" "w = ws ! i" using ws(1) by (auto simp: in_set_conv_nth)
    moreover from ws(2)[OF this(1)] have "normal (ws ! i)" by simp
    ultimately show "no_redex w" by (metis normal_no_redex)
  qed
  show ?thesis
  proof
    show "\<beta>\<eta>cl (ts ! i) (ws ! i) \<and> normal (ws ! i) \<and> (e, \<tau>) \<turnstile> ws ! i : Ts ! i" if "i < length ts" for i
      using ws(2)[OF that] tyws[OF that] by simp
    show "h \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ws"
      using ws by (intro equiv_list_app) (auto simp: list_all2_conv_all_nth intro: \<beta>\<eta>cl_into_equiv)
    show "no_redex (h \<degree>\<degree> ws)" using no_redex_atom_apps[OF assms(1)] nr by blast
    show "(e, \<tau>) \<turnstile> h \<degree>\<degree> ws : T" using list_app_typeI[OF assms(2) tys] .
    show "Suc (ld e \<tau> (ws ! i) (Ts ! i)) \<le> ld e \<tau> (h \<degree>\<degree> ws) T" if "i < length ts" for i
      using ld_atom_apps[OF assms(1,2) tys nr] that ws(1) by simp
  qed (use ws(1) in simp)
qed

subsection \<open>Occurrences of a flexible variable\<close>

text \<open>Normal forms of a closed term applied to bound variables.\<close>

lemma typed_nf_args:
  assumes "no_loose_bound t 0" "(e, \<tau>) \<turnstile> t : Ts \<Rrightarrow> U" "length Ts = m"
  obtains r where "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (downs m)) r" "normal r" "(env_ext e Ts, \<tau>) \<turnstile> r : U"
    "loose_BVars r \<subseteq> {..<m}"
proof -
  have "(env_ext e Ts, \<tau>) \<turnstile> t : Ts \<Rrightarrow> U" using typing_closed assms(1,2) by blast
  moreover have "(env_ext e Ts, \<tau>) \<tturnstile> map BVar (downs m) : Ts"
    using env_ext_downs[of e Ts] assms(3) by (simp add: typings_map_BVar)
  ultimately have "(env_ext e Ts, \<tau>) \<turnstile> t \<degree>\<degree> map BVar (downs m) : U"
    by (auto simp: list_app_typing_iff)
  then obtain r where r: "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (downs m)) r" "normal r" "(env_ext e Ts, \<tau>) \<turnstile> r : U"
    by (rule typed_normal_form)
  moreover have "loose_BVars r \<subseteq> {..<m}"
    using loose_BVars_\<beta>\<eta>cl[OF r(1)] no_loose_bound_loose_BVars[OF assms(1)] by auto
  ultimately show ?thesis using that by blast
qed

lemma nf_rename_args:
  assumes "no_loose_bound t 0" "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (downs m)) r" "normal r"
    "length xs = m" "distinct xs"
  shows "\<beta>\<eta>cl (t \<degree>\<degree> map BVar xs) (map_BVars (\<lambda>i. xs ! (m - Suc i)) r)"
    "normal (map_BVars (\<lambda>i. xs ! (m - Suc i)) r)"
proof -
  let ?f = "\<lambda>i. xs ! (m - Suc i)"
  have "inj_on ?f (loose_BVars (t \<degree>\<degree> map BVar (downs m)))"
    using no_loose_bound_loose_BVars[OF assms(1)] assms(4,5)
    by (auto simp: inj_on_def nth_eq_iff_index_eq)
  from normal_form_rename[OF assms(2,3) this]
  show "\<beta>\<eta>cl (t \<degree>\<degree> map BVar xs) (map_BVars ?f r)" "normal (map_BVars ?f r)"
    unfolding map_BVars_closed_app[OF assms(1)] map_downs[OF assms(4)] .
qed

text \<open>
  The measure of (any \<open>\<beta>\<close>-normal form of) an occurrence \<open>\<sigma> F (y\<^sub>1, \<dots>, y\<^sub>m)\<close> equals the measure
  of the normal form of \<open>\<sigma> F\<close>.
\<close>

lemma ld_flex_occurrence:
  assumes \<sigma>F: "no_loose_bound (\<sigma> F) 0" "\<And>e'. (e', \<tau>\<sigma>) \<turnstile> \<sigma> F : \<tau> F"
    and nF: "\<beta>\<eta>cl (\<sigma> F) nF" "normal nF"
    and ys: "distinct ys" "(e, \<tau>) \<turnstile> Var F \<degree>\<degree> map BVar ys : T"
    and v: "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F \<degree>\<degree> map BVar ys" "no_redex v" "(e, \<tau>\<sigma>) \<turnstile> v : T"
  shows "ld e \<tau>\<sigma> v T = ld e' \<tau>\<sigma> nF (\<tau> F)"
proof -
  define m where "m = length ys"
  define Ts where "Ts = map e ys"
  define g where "g = (\<lambda>i. ys ! (m - Suc i))"
  have \<tau>F: "\<tau> F = Ts \<Rrightarrow> T" using ys(2) by (simp add: typing_Var_app_BVars Ts_def)
  have lenTs: "length Ts = m" by (simp add: Ts_def m_def)
  have closed: "no_loose_bound nF 0"
    using loose_BVars_\<beta>\<eta>cl[OF nF(1)] no_loose_bound_loose_BVars[OF \<sigma>F(1)]
    by (intro loose_BVars_no_loose_bound) auto
  have tynF: "(e'', \<tau>\<sigma>) \<turnstile> nF : Ts \<Rrightarrow> T" for e''
    using subject_reduction_\<beta>\<eta>[OF nF(1) \<sigma>F(2)] \<tau>F by simp
  obtain w where w: "\<beta>\<eta>cl (nF \<degree>\<degree> map BVar (downs m)) w" "normal w" "(env_ext e' Ts, \<tau>\<sigma>) \<turnstile> w : T"
    "loose_BVars w \<subseteq> {..<m}"
    using typed_nf_args[OF closed tynF lenTs] .
  have "ld e' \<tau>\<sigma> nF (Ts \<Rrightarrow> T) = ld e' \<tau>\<sigma> (Abs_m m w) (Ts \<Rrightarrow> T)"
  proof (rule ld_equiv)
    have "Abs_m m w \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m (nF \<degree>\<degree> map BVar (downs m))"
      using w(1) by (intro equiv_Abs_m equiv_sym[OF \<beta>\<eta>cl_into_equiv])
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> nF" using closed by (rule eta_expand_equiv)
    finally show "nF \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m w" by (rule equiv_sym)
    show "(e', \<tau>\<sigma>) \<turnstile> Abs_m m w : Ts \<Rrightarrow> T" using typing_Abs_m[OF w(3)] lenTs by simp
    show "no_redex nF" "no_redex (Abs_m m w)" using nF(2) w(2) by (simp_all add: normal_no_redex)
  qed (rule tynF)
  also have "\<dots> = ld (env_ext e' Ts) \<tau>\<sigma> w T" using ld_Abs_m[OF lenTs] .
  finally have K: "ld e' \<tau>\<sigma> nF (\<tau> F) = ld (env_ext e' Ts) \<tau>\<sigma> w T" by (simp add: \<tau>F)
  note ren = nf_rename_args[OF closed w(1,2) m_def[symmetric] ys(1), folded g_def]
  have env: "e (g i) = env_ext e' Ts i" if "i \<in> loose_BVars w" for i
  proof -
    have "i < m" using that w(4) by auto
    then have "m - Suc i < m" by arith
    then show ?thesis using \<open>i < m\<close> by (simp add: g_def env_ext_less lenTs Ts_def m_def)
  qed
  have "ld e \<tau>\<sigma> v T = ld e \<tau>\<sigma> (map_BVars g w) T"
  proof (rule ld_equiv)
    have "\<sigma> F \<degree>\<degree> map BVar ys \<equiv>\<^sub>\<beta>\<^sub>\<eta> nF \<degree>\<degree> map BVar ys"
      using nF(1) by (intro equiv_list_app) (auto intro: \<beta>\<eta>cl_into_equiv simp: list_all2_same)
    then show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars g w"
      using v(1) ren(1) by (meson \<beta>\<eta>cl_into_equiv equiv_trans)
    show "(e, \<tau>\<sigma>) \<turnstile> map_BVars g w : T" using typing_map_BVars[OF w(3)] env by blast
    show "no_redex (map_BVars g w)" using ren(2) by (rule normal_no_redex)
  qed (use v in auto)
  also have "\<dots> = ld (env_ext e' Ts) \<tau>\<sigma> w T" using ld_map_BVars env by blast
  finally show ?thesis using K by simp
qed

text \<open>
  The measure of (any \<open>\<beta>\<close>-normal form of) an instance of a pattern containing \<open>F\<close> is at least the
  measure of the normal form of \<open>\<sigma> F\<close>; it is strictly larger for patterns with a rigid head.
\<close>

lemma ld_pat_occurrence:
  assumes "pat u" "F \<in> FV u" "(e, \<tau>) \<turnstile> u : T"
    and \<sigma>: "closed_on (FV u) \<sigma>" "typed_on (FV u) \<tau> \<tau>\<sigma> \<sigma>"
    and nF: "\<beta>\<eta>cl (\<sigma> F) nF" "normal nF"
    and v: "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> u" "no_redex v" "(e, \<tau>\<sigma>) \<turnstile> v : T"
  shows "ld e' \<tau>\<sigma> nF (\<tau> F) \<le> ld e \<tau>\<sigma> v T \<and>
    (\<forall>x ts. u = BVar x \<degree>\<degree> ts \<longrightarrow> ld e' \<tau>\<sigma> nF (\<tau> F) < ld e \<tau>\<sigma> v T)"
  using assms(1-5) v
proof (induction arbitrary: e T v rule: pat.induct)
  case (pat_Abs t)
  from pat_Abs.prems(2) obtain A B where T: "T = A \<Rightarrow> B" and ty: "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> t : B" by auto
  have tyst: "(e\<langle>0:A\<rangle>, \<tau>\<sigma>) \<turnstile> mk_subst \<sigma> t : B"
    using typing_mk_subst[OF ty] pat_Abs.prems(4) by simp
  obtain w where w: "\<beta>\<eta>cl (mk_subst \<sigma> t) w" "normal w" using normal_form_ex[OF tyst] by blast
  have tyw: "(e\<langle>0:A\<rangle>, \<tau>\<sigma>) \<turnstile> w : B" using subject_reduction_\<beta>\<eta>[OF w(1) tyst] .
  have weq: "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t" using w(1) by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv])
  have Ft: "F \<in> FV t" "closed_on (FV t) \<sigma>" "typed_on (FV t) \<tau> \<tau>\<sigma> \<sigma>"
    using pat_Abs.prems(1,3,4) by simp_all
  from pat_Abs.IH[OF Ft(1) ty Ft(2,3) weq normal_no_redex[OF w(2)] tyw]
  have IH: "ld e' \<tau>\<sigma> nF (\<tau> F) \<le> ld (e\<langle>0:A\<rangle>) \<tau>\<sigma> w B" by (rule conjunct1)
  have "ld e \<tau>\<sigma> v T = ld e \<tau>\<sigma> (Abs w) T"
  proof (rule ld_equiv)
    have "Abs (mk_subst \<sigma> t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs w" using w(1) by (intro equiv_Abs \<beta>\<eta>cl_into_equiv)
    moreover have "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs (mk_subst \<sigma> t)" using pat_Abs.prems(5) by (simp only: mk_subst.simps)
    ultimately show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs w" by (metis equiv_trans)
    show "(e, \<tau>\<sigma>) \<turnstile> Abs w : T" using tyw T by auto
    show "no_redex (Abs w)" using normal_no_redex[OF w(2)] by simp
  qed (use pat_Abs.prems in auto)
  moreover have "Abs t \<noteq> BVar x \<degree>\<degree> ts" for x ts
    using is_Abs_atom_apps[of "BVar x" ts] by auto
  ultimately show ?case using IH T by simp
next
  case (pat_BVar ts x)
  from pat_BVar.prems(1) obtain i where i: "i < length ts" "F \<in> FV (ts ! i)"
    by (auto simp: in_set_conv_nth)
  from pat_BVar.prems(2) obtain Ts where tyx: "(e, \<tau>) \<turnstile> BVar x : Ts \<Rrightarrow> T" and tyts: "(e, \<tau>) \<tturnstile> ts : Ts"
    by (elim list_app_typeE)
  have lenTs: "length Ts = length ts" using typings_length[OF tyts] .
  have tyi: "(e, \<tau>) \<turnstile> ts ! j : Ts ! j" if "j < length ts" for j using typings_nth[OF tyts that] .
  have FVj: "FV (ts ! j) \<subseteq> FV (BVar x \<degree>\<degree> ts)" if "j < length ts" for j
    using nth_mem[OF that] by auto
  have tys: "(e, \<tau>\<sigma>) \<tturnstile> map (mk_subst \<sigma>) ts : Ts"
  proof (rule typings_map2)
    fix j assume "j < length (map (mk_subst \<sigma>) ts)"
    then have "j < length ts" by simp
    then show "(e, \<tau>\<sigma>) \<turnstile> map (mk_subst \<sigma>) ts ! j : Ts ! j"
      using typing_mk_subst[OF tyi typed_on_mono[OF pat_BVar.prems(4) FVj]] by simp
  qed (simp add: lenTs)
  have tyx': "(e, \<tau>\<sigma>) \<turnstile> BVar x : Ts \<Rrightarrow> T" using tyx by auto
  obtain ws where ws': "length ws = length (map (mk_subst \<sigma>) ts)"
    "\<And>j. j < length (map (mk_subst \<sigma>) ts) \<Longrightarrow> \<beta>\<eta>cl (map (mk_subst \<sigma>) ts ! j) (ws ! j) \<and>
      normal (ws ! j) \<and> (e, \<tau>\<sigma>) \<turnstile> ws ! j : Ts ! j"
    "BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar x \<degree>\<degree> ws" "no_redex (BVar x \<degree>\<degree> ws)"
    "(e, \<tau>\<sigma>) \<turnstile> BVar x \<degree>\<degree> ws : T"
    "\<And>j. j < length (map (mk_subst \<sigma>) ts) \<Longrightarrow>
      Suc (ld e \<tau>\<sigma> (ws ! j) (Ts ! j)) \<le> ld e \<tau>\<sigma> (BVar x \<degree>\<degree> ws) T"
    by (rule atom_apps_nf[OF is_atom_simps(1) tyx' tys]) blast
  have ws: "\<And>j. j < length ts \<Longrightarrow> \<beta>\<eta>cl (mk_subst \<sigma> (ts ! j)) (ws ! j) \<and> normal (ws ! j) \<and>
      (e, \<tau>\<sigma>) \<turnstile> ws ! j : Ts ! j"
    "\<And>j. j < length ts \<Longrightarrow> Suc (ld e \<tau>\<sigma> (ws ! j) (Ts ! j)) \<le> ld e \<tau>\<sigma> (BVar x \<degree>\<degree> ws) T"
    using ws'(2,6) by simp_all
  have wi: "ws ! i \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (ts ! i)" "no_redex (ws ! i)" "(e, \<tau>\<sigma>) \<turnstile> ws ! i : Ts ! i"
    using ws(1)[OF i(1)] by (auto intro: equiv_sym \<beta>\<eta>cl_into_equiv normal_no_redex)
  have "ld e' \<tau>\<sigma> nF (\<tau> F) \<le> ld e \<tau>\<sigma> (ws ! i) (Ts ! i)"
    using pat_BVar.IH[OF nth_mem[OF i(1)] i(2) tyi[OF i(1)]
        closed_on_mono[OF pat_BVar.prems(3) FVj[OF i(1)]]
        typed_on_mono[OF pat_BVar.prems(4) FVj[OF i(1)]] wi]
    by simp
  also have "\<dots> < ld e \<tau>\<sigma> (BVar x \<degree>\<degree> ws) T" using ws(2)[OF i(1)] by simp
  also have "\<dots> = ld e \<tau>\<sigma> v T"
  proof (rule ld_equiv)
    have "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts"
      using pat_BVar.prems(5) by (simp only: mk_subst_list_app mk_subst.simps)
    from equiv_trans[OF this ws'(3)] show "BVar x \<degree>\<degree> ws \<equiv>\<^sub>\<beta>\<^sub>\<eta> v" by (rule equiv_sym)
  qed (use ws' pat_BVar.prems in auto)
  finally show ?case by simp
next
  case (pat_Var xs G)
  then have G: "G = F" by simp
  have "Var G \<degree>\<degree> map BVar xs \<noteq> BVar x \<degree>\<degree> ts" for x ts
    by (simp add: atom_apps_eq_iff)
  moreover have "ld e \<tau>\<sigma> v T = ld e' \<tau>\<sigma> nF (\<tau> F)"
  proof -
    have \<sigma>F: "no_loose_bound (\<sigma> F) 0" "(e'', \<tau>\<sigma>) \<turnstile> \<sigma> F : \<tau> F" for e''
      using closed_onD[OF pat_Var.prems(3)] typed_onD[OF pat_Var.prems(4)] G by simp_all
    have eq: "mk_subst \<sigma> (Var G \<degree>\<degree> map BVar xs) = \<sigma> F \<degree>\<degree> map BVar xs" using G by simp
    have "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F \<degree>\<degree> map BVar xs" using pat_Var.prems(5) unfolding eq .
    moreover have "(e, \<tau>) \<turnstile> Var F \<degree>\<degree> map BVar xs : T" using pat_Var.prems(2) G by simp
    ultimately show ?thesis
      using ld_flex_occurrence[where \<sigma> = \<sigma> and F = F and \<tau> = \<tau> and \<tau>\<sigma> = \<tau>\<sigma>, OF \<sigma>F nF pat_Var.hyps]
        pat_Var.prems(6,7) by blast
  qed
  ultimately show ?case by simp
qed

subsection \<open>Fact 9\<close>

theorem occurs_check:
  assumes xs: "distinct xs" and ts: "\<forall>t\<in>set ts. pat t" "F \<in> \<Union> (FV ` set ts)"
    and ty: "(e, \<tau>) \<turnstile> Var F \<degree>\<degree> map BVar xs : T" "(e, \<tau>) \<turnstile> BVar p \<degree>\<degree> ts : T"
    and \<sigma>: "closed_on (\<Union> (FV ` set ts)) \<sigma>" "typed_on (\<Union> (FV ` set ts)) \<tau> \<tau>\<sigma> \<sigma>"
  shows "\<not> mk_subst \<sigma> (Var F \<degree>\<degree> map BVar xs) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (BVar p \<degree>\<degree> ts)"
proof
  assume eq: "mk_subst \<sigma> (Var F \<degree>\<degree> map BVar xs) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (BVar p \<degree>\<degree> ts)"
  have pat: "pat (BVar p \<degree>\<degree> ts)" using ts(1) by (auto intro: pat_BVar)
  have FV: "FV (BVar p \<degree>\<degree> ts) = \<Union> (FV ` set ts)" by simp
  have \<sigma>F: "no_loose_bound (\<sigma> F) 0" "(e', \<tau>\<sigma>) \<turnstile> \<sigma> F : \<tau> F" for e'
    using closed_onD[OF \<sigma>(1) ts(2)] typed_onD[OF \<sigma>(2) ts(2)] by auto
  obtain nF where nF: "\<beta>\<eta>cl (\<sigma> F) nF" "normal nF" using normal_form_ex[OF \<sigma>F(2)] by blast
  have ty1: "(e, \<tau>\<sigma>) \<turnstile> mk_subst \<sigma> (Var F \<degree>\<degree> map BVar xs) : T"
    using typing_mk_subst[OF ty(1)] typed_on_mono[OF \<sigma>(2)] ts(2) by simp
  have ty2: "(e, \<tau>\<sigma>) \<turnstile> mk_subst \<sigma> (BVar p \<degree>\<degree> ts) : T"
    using typing_mk_subst[OF ty(2)] \<sigma>(2) FV by simp
  obtain v1 where v1: "\<beta>\<eta>cl (mk_subst \<sigma> (Var F \<degree>\<degree> map BVar xs)) v1" "normal v1"
    using normal_form_ex[OF ty1] by blast
  obtain v2 where v2: "\<beta>\<eta>cl (mk_subst \<sigma> (BVar p \<degree>\<degree> ts)) v2" "normal v2"
    using normal_form_ex[OF ty2] by blast
  have tyv: "(e, \<tau>\<sigma>) \<turnstile> v1 : T" "(e, \<tau>\<sigma>) \<turnstile> v2 : T"
    using subject_reduction_\<beta>\<eta> v1(1) v2(1) ty1 ty2 by blast+
  have "ld e \<tau>\<sigma> v1 T = ld e \<tau>\<sigma> nF (\<tau> F)"
  proof (rule ld_flex_occurrence[where \<sigma> = \<sigma> and F = F, OF \<sigma>F nF xs ty(1)])
    have "mk_subst \<sigma> (Var F \<degree>\<degree> map BVar xs) \<equiv>\<^sub>\<beta>\<^sub>\<eta> v1" using v1(1) by (rule \<beta>\<eta>cl_into_equiv)
    then show "v1 \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F \<degree>\<degree> map BVar xs" by (simp add: equiv_sym)
    show "no_redex v1" using v1(2) by (rule normal_no_redex)
  qed (rule tyv(1))
  moreover have "ld e \<tau>\<sigma> nF (\<tau> F) < ld e \<tau>\<sigma> v2 T"
  proof -
    have "v2 \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (BVar p \<degree>\<degree> ts)" using v2(1) by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv])
    from ld_pat_occurrence[where \<sigma> = \<sigma> and F = F, OF pat _ ty(2) _ _ nF this normal_no_redex[OF v2(2)] tyv(2)]
    show ?thesis using ts(2) \<sigma> FV by simp
  qed
  moreover have "ld e \<tau>\<sigma> v1 T = ld e \<tau>\<sigma> v2 T"
  proof (rule ld_equiv)
    show "v1 \<equiv>\<^sub>\<beta>\<^sub>\<eta> v2" using eq v1(1) v2(1) by (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
  qed (use tyv v1 v2 normal_no_redex in auto)
  ultimately show False by simp
qed

end
