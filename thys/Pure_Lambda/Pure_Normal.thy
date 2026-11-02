section \<open>Normal Forms\<close>

theory Pure_Normal
  imports Pure_SN
begin

text \<open>
  Well-typed Pure terms have \<open>\<beta>\<eta>\<close>-normal forms, unique up to \<open>\<alpha>\<close>-equivalence. A \<open>\<beta>\<close>-normal
  form exists by strong normalization; \<open>\<eta>\<close>-reduction then terminates, as it decreases the
  size, and keeps the term \<open>\<beta>\<close>-normal.
\<close>

abbreviation beta_eta :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<close> 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta> t \<equiv> sup beta eta s t"

abbreviation beta_eta_reds :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>*\<close> 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<equiv> (sup beta eta)\<^sup>*\<^sup>* s t"

definition normal :: "pterm \<Rightarrow> bool" where
  "normal t \<longleftrightarrow> \<not> (\<exists>u. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta> u)"


subsection \<open>\<open>\<beta>\<close>-normal forms\<close>

fun no_redex :: "pterm \<Rightarrow> bool" where
  "no_redex (Abs a T t) \<longleftrightarrow> no_redex t"
| "no_redex (s $ t) \<longleftrightarrow> \<not> is_Abs s \<and> no_redex s \<and> no_redex t"
| "no_redex _ \<longleftrightarrow> True"

lemma no_redex_iff: "no_redex t \<longleftrightarrow> \<not> (\<exists>u. t \<rightarrow>\<^sub>\<beta> u)"
proof (induction t)
  case (App s t)
  show ?case
  proof (cases "is_Abs s")
    case True
    then obtain a T r where "s = Abs a T r" by (cases s) auto
    then show ?thesis by auto
  next
    case False
    with App show ?thesis by (auto elim: is_Abs.elims)
  qed
qed auto

lemma beta_normal_ex: "termip beta t \<Longrightarrow> \<exists>u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> no_redex u"
proof (induction rule: accp_induct_rule)
  case (1 t)
  show ?case
  proof (cases "no_redex t")
    case False
    then obtain t' where "t \<rightarrow>\<^sub>\<beta> t'" by (auto simp: no_redex_iff)
    with 1(2) obtain u where "t' \<rightarrow>\<^sub>\<beta>\<^sup>* u" "no_redex u" by blast
    with \<open>t \<rightarrow>\<^sub>\<beta> t'\<close> show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed blast
qed


subsection \<open>\<open>\<eta>\<close>-reduction of \<open>\<beta>\<close>-normal terms\<close>

lemma size_subst_not_free: "\<not> loose_bvar1 s k \<Longrightarrow> size (s[d/k]) = size s"
proof (induction s arbitrary: k d)
  case (Abs a T s)
  then show ?case using Abs.IH[of "k + 1" "lift d 0"] by simp
qed (auto simp: subst_Bound)

lemma eta_size: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> size t < size s"
  by (induction set: eta) (auto simp: size_subst_not_free)

lemma is_Abs_subst_Bound: "is_Abs (s[Bound i/k]) \<longleftrightarrow> is_Abs s"
  by (cases s) (auto simp: subst_Bound)

lemma no_redex_subst_Bound: "no_redex t \<Longrightarrow> no_redex (t[Bound i/k])"
proof (induction t arbitrary: i k)
  case (Abs a T t)
  then show ?case by (auto simp: Abs.IH)
qed (auto simp: subst_Bound is_Abs_subst_Bound)

lemma eta_not_Abs: "s \<rightarrow>\<^sub>\<eta> s' \<Longrightarrow> \<not> is_Abs s \<Longrightarrow> \<not> is_Abs s'"
  by (cases rule: eta.cases) auto

lemma no_redex_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> no_redex s \<Longrightarrow> no_redex t"
proof (induction set: eta)
  case (eta s a T d)
  have "s[d/0] = s[Bound 0/0]" using \<open>\<not> loose_bvar1 s 0\<close> by (rule subst_not_free)
  with eta show ?case by (auto intro: no_redex_subst_Bound)
qed (auto dest: eta_not_Abs)

lemma eta_normal_ex: "\<exists>u. t \<rightarrow>\<^sub>\<eta>\<^sup>* u \<and> \<not> (\<exists>v. u \<rightarrow>\<^sub>\<eta> v)"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "\<exists>v. t \<rightarrow>\<^sub>\<eta> v")
    case True
    then obtain v where "t \<rightarrow>\<^sub>\<eta> v" by blast
    with less[OF eta_size] obtain u where "v \<rightarrow>\<^sub>\<eta>\<^sup>* u" "\<not> (\<exists>w. u \<rightarrow>\<^sub>\<eta> w)" by blast
    with \<open>t \<rightarrow>\<^sub>\<eta> v\<close> show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed blast
qed

lemma no_redex_etas: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> no_redex s \<Longrightarrow> no_redex t"
  by (induction rule: rtranclp_induct) (auto intro: no_redex_eta)


subsection \<open>Existence and uniqueness of \<open>\<beta>\<eta>\<close>-normal forms\<close>

lemma beta_reds_beta_eta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma eta_reds_beta_eta_reds: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma normal_reds: "u \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v \<Longrightarrow> normal u \<Longrightarrow> v = u"
  by (induction rule: converse_rtranclp_induct) (auto simp: normal_def)

lemma aconv_term_refl [simp]: "aconv_term t t"
  by (simp add: aconv_term_unname)

context signature
begin

theorem normal_form_ex:
  assumes "e \<turnstile> t : T"
  obtains u where "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" and "normal u"
proof -
  obtain u1 where u1: "t \<rightarrow>\<^sub>\<beta>\<^sup>* u1" "no_redex u1"
    using beta_normal_ex[OF type_implies_termi[OF assms]] by blast
  obtain u where u: "u1 \<rightarrow>\<^sub>\<eta>\<^sup>* u" "\<not> (\<exists>v. u \<rightarrow>\<^sub>\<eta> v)" using eta_normal_ex by blast
  have "no_redex u" using u(1) u1(2) by (rule no_redex_etas)
  then have "normal u" using u(2) by (auto simp: normal_def no_redex_iff)
  moreover have "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u"
    using u1(1) u(1) by (meson beta_reds_beta_eta_reds eta_reds_beta_eta_reds rtranclp_trans)
  ultimately show ?thesis using that by blast
qed

theorem normal_form_unique:
  assumes "e \<turnstile> t : T" "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v" "normal u" "normal v"
  shows "aconv_term u v"
  using confluent_beta_eta_aconv[OF assms(1) aconv_term_refl assms(2,3)] assms(4,5)
  by (auto dest: normal_reds)

end

end
