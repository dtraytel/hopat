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

lemma ld_env_cong:
  "(\<And>i. loose_bvar1 t i \<Longrightarrow> 0 \<le> i \<and> e' i = e i) \<Longrightarrow>
    spine_type e' t = spine_type e t \<and> ld e' t T = ld e t T"
proof (induction t arbitrary: e e' T)
  case (Abs a A t)
  have "ld (e'\<langle>0:dom_type T\<rangle>) t (rng_type T) = ld (e\<langle>0:dom_type T\<rangle>) t (rng_type T)"
  proof (rule conjunct2[OF Abs.IH])
    fix i assume i: "loose_bvar1 t i"
    show "0 \<le> i \<and> (e'\<langle>0:dom_type T\<rangle>) i = (e\<langle>0:dom_type T\<rangle>) i"
    proof (cases "i = 0")
      case False
      with i have "loose_bvar1 (Abs a A t) (i - 1)" by simp
      from Abs.prems[OF this] False show ?thesis by (simp add: integer_arith)
    qed simp
  qed
  then show ?case by simp
next
  case (App s t)
  have hs: "spine_type e' s = spine_type e s" "\<And>T. ld e' s T = ld e s T"
    using App.IH(1)[of e e'] App.prems by auto
  have ht: "\<And>T. ld e' t T = ld e t T" using App.IH(2)[of e e'] App.prems by auto
  show ?case using hs ht by simp
qed auto

lemma unname_spine_type [simp]: "spine_type e (unname t) = spine_type e t"
  by (induction t) auto

lemma ld_unname [simp]: "ld e (unname t) T = ld e t T"
  by (induction t arbitrary: e T) auto

lemma ld_aconv: "aconv_term s t \<Longrightarrow> ld e s T = ld e t T"
  by (metis aconv_term_unname ld_unname)


subsection \<open>Invariance under \<open>\<eta>\<close>-reduction\<close>

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

end

end
