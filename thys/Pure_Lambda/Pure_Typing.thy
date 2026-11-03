section \<open>Well-Typed Pure Terms\<close>

theory Pure_Typing
  imports Pure_Lambda
begin

text \<open>
  Well-typed Pure terms in a signature, as \<open>Sign.cert_term\<close> checks them: the types of the
  atoms and binders are certified (\<open>ty_ok\<close>), and constants are instances of their declared
  types (\<open>const_ok\<close>). The judgment follows \<^file>\<open>~~/src/HOL/Proofs/Lambda/LambdaType.thy\<close>;
  the environment \<open>e\<close> gives the types of the loose bound variables.
\<close>

locale signature =
  fixes ty_ok :: "ptyp \<Rightarrow> bool"
    and const_ok :: "name \<Rightarrow> ptyp \<Rightarrow> bool"
begin


subsection \<open>Typing\<close>

inductive typing :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool"  (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50) where
  Const [intro!]: "const_ok c T \<Longrightarrow> ty_ok T \<Longrightarrow> e \<turnstile> Const c T : T"
| Free [intro!]: "ty_ok T \<Longrightarrow> e \<turnstile> Free x T : T"
| Var [intro!]: "ty_ok T \<Longrightarrow> e \<turnstile> Var x T : T"
| Bound [intro!]: "0 \<le> i \<Longrightarrow> e i = T \<Longrightarrow> e \<turnstile> Bound i : T"
| Abs [intro!]: "ty_ok T \<Longrightarrow> e\<langle>0:T\<rangle> \<turnstile> t : U \<Longrightarrow> e \<turnstile> Abs a T t : T \<rightarrow>\<^sub>T U"
| App [intro!]: "e \<turnstile> s : T \<rightarrow>\<^sub>T U \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> s $ t : U"

inductive_cases typing_elims [elim!]:
  "e \<turnstile> Bound i : T"
  "e \<turnstile> Const c U : T"
  "e \<turnstile> Free x U : T"
  "e \<turnstile> Var x U : T"
  "e \<turnstile> s $ t : T"
  "e \<turnstile> Abs a U t : T"

lemma lift_type [intro!]: "e \<turnstile> t : T \<Longrightarrow> 0 \<le> i \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> lift t i : T"
proof (induction arbitrary: i U rule: typing.induct)
  case (Bound j e T)
  then show ?case by (auto simp: integer_arith)
next
  case (Abs T e t U' a)
  then show ?case using Abs.IH[of "i + 1" U] by auto
qed auto

lemma subst_lemma:
  "e \<turnstile> t : T \<Longrightarrow> e' \<turnstile> u : U \<Longrightarrow> e = e'\<langle>i:U\<rangle> \<Longrightarrow> 0 \<le> i \<Longrightarrow> e' \<turnstile> t[u/i] : T"
proof (induction arbitrary: e' i U u rule: typing.induct)
  case (Bound j e T)
  then show ?case by (cases j i rule: linorder_cases) (auto simp: integer_less_iff integer_less_eq_iff)
next
  case (Abs T e t U' a)
  have "e'\<langle>0:T\<rangle> \<turnstile> lift u 0 : U" using Abs.prems by auto
  then show ?case
    using Abs.IH[where e' = "e'\<langle>0:T\<rangle>" and i = "i + 1" and u = "lift u 0" and U = U] Abs.prems Abs.hyps(1)
    by auto
next
  case (App e s T U' t)
  then show ?case by (auto intro!: typing.App)
qed auto

lemma subject_reduction_beta: "e \<turnstile> t : T \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> e \<turnstile> t' : T"
proof (induction arbitrary: t' rule: typing.induct)
  case (App e s T U t)
  from App.prems show ?case
  proof cases
    case (beta a T' r)
    with App.hyps show ?thesis by (auto intro: subst_lemma)
  qed (use App in auto)
qed auto

lemma strengthening:
  "e \<turnstile> s : T \<Longrightarrow> e = e'\<langle>i:U\<rangle> \<Longrightarrow> \<not> loose_bvar1 s i \<Longrightarrow> 0 \<le> i \<Longrightarrow> e' \<turnstile> s[d/i] : T"
proof (induction arbitrary: e' i d rule: typing.induct)
  case (Bound j e T)
  then show ?case by (cases j i rule: linorder_cases) (auto simp: integer_arith)
next
  case (Abs T e t U' a)
  then show ?case by (auto intro!: Abs.IH[of "e'\<langle>0:T\<rangle>" "i + 1"])
qed auto

lemma subject_reduction_eta: "t \<rightarrow>\<^sub>\<eta> t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
proof (induction arbitrary: e T set: eta)
  case (eta s a U d)
  then show ?case by (auto intro: strengthening)
qed auto

lemma typing_unname: "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> unname t : T"
  by (induction rule: typing.induct) auto

lemma typing_unname_iff: "e \<turnstile> unname t : T \<longleftrightarrow> e \<turnstile> t : T"
  by (induction t arbitrary: e T) auto

lemma typing_alpha: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (induction arbitrary: e T set: alpha) auto


subsection \<open>Confluence of \<open>\<beta>\<eta>\<close> for well-typed terms\<close>

text \<open>
  On well-typed terms whose bound variables have the empty name, \<open>\<beta>\<close> and \<open>\<eta>\<close> commute: in the
  critical pair \<open>\<lambda>a:T. (\<lambda>b:U. r) a\<close>, typing forces \<open>U = T\<close>, and the names agree.
\<close>

lemma square_beta_eta_typed:
  "x \<rightarrow>\<^sub>\<beta> y \<Longrightarrow> x \<rightarrow>\<^sub>\<eta> z \<Longrightarrow> e \<turnstile> x : T \<Longrightarrow> unname x = x \<Longrightarrow> \<exists>u. y \<rightarrow>\<^sub>\<eta>\<^sup>* u \<and> beta\<^sup>=\<^sup>= z u"
proof (induction arbitrary: z e T rule: beta.induct)
  case (beta a U s t)
  from beta.prems(1) show ?case
  proof cases
    case (appL z1)
    from \<open>Abs a U s \<rightarrow>\<^sub>\<eta> z1\<close> show ?thesis
    proof cases
      case (eta s0 d)
      then have "s[t/0] = z" using appL by simp
      then show ?thesis by blast
    next
      case (abs s')
      then have "s[t/0] \<rightarrow>\<^sub>\<eta>\<^sup>* s'[t/0]" by (simp add: r_into_rtranclp)
      moreover have "z \<rightarrow>\<^sub>\<beta> s'[t/0]" using abs appL by simp
      ultimately show ?thesis by (meson sup2I1)
    qed
  next
    case (appR t')
    then have "s[t/0] \<rightarrow>\<^sub>\<eta>\<^sup>* s[t'/0]" by (simp add: rtrancl_eta_subst)
    moreover have "z \<rightarrow>\<^sub>\<beta> s[t'/0]" using appR by simp
    ultimately show ?thesis by (meson sup2I1)
  qed
next
  case (appL s t u)
  from appL.prems(1) show ?case
  proof cases
    case (appL s')
    with appL.prems obtain w where "t \<rightarrow>\<^sub>\<eta>\<^sup>* w" "beta\<^sup>=\<^sup>= s' w"
      using appL.IH by fastforce
    then have "t $ u \<rightarrow>\<^sub>\<eta>\<^sup>* w $ u" "beta\<^sup>=\<^sup>= (s' $ u) (w $ u)"
      by (auto simp: rtrancl_eta_AppL)
    with appL show ?thesis by (intro exI[of _ "w $ u"]) simp
  next
    case (appR u')
    then have "t $ u \<rightarrow>\<^sub>\<eta>\<^sup>* t $ u'" "z \<rightarrow>\<^sub>\<beta> t $ u'" using appL.hyps by auto
    then show ?thesis by (meson sup2I1)
  qed
next
  case (appR s t u)
  from appR.prems(1) show ?case
  proof cases
    case (appR s')
    with appR.prems obtain w where "t \<rightarrow>\<^sub>\<eta>\<^sup>* w" "beta\<^sup>=\<^sup>= s' w"
      using appR.IH by fastforce
    then have "u $ t \<rightarrow>\<^sub>\<eta>\<^sup>* u $ w" "beta\<^sup>=\<^sup>= (u $ s') (u $ w)"
      by (auto simp: rtrancl_eta_AppR)
    with appR show ?thesis by (intro exI[of _ "u $ w"]) simp
  next
    case (appL u')
    then have "u $ t \<rightarrow>\<^sub>\<eta>\<^sup>* u' $ t" "z \<rightarrow>\<^sub>\<beta> u' $ t" using appR.hyps by auto
    then show ?thesis by (meson sup2I1)
  qed
next
  case (abs s t a U)
  from abs.prems(1) show ?case
  proof cases
    case (abs s')
    with abs.prems obtain w where "t \<rightarrow>\<^sub>\<eta>\<^sup>* w" "beta\<^sup>=\<^sup>= s' w"
      using abs.IH by fastforce
    then have "Abs a U t \<rightarrow>\<^sub>\<eta>\<^sup>* Abs a U w" "beta\<^sup>=\<^sup>= (Abs a U s') (Abs a U w)"
      by (auto simp: rtrancl_eta_Abs)
    with abs show ?thesis by (intro exI[of _ "Abs a U w"]) simp
  next
    case (eta s0 d)
    from \<open>s \<rightarrow>\<^sub>\<beta> t\<close> \<open>s = s0 $ Bound 0\<close> show ?thesis
    proof (cases rule: beta.cases)
      case (beta b V r)
      then have s0: "s0 = Abs b V r" and t: "t = r[Bound 0/0]" using eta by auto
      have "V = U" "b = a" using abs.prems(2,3) eta s0 by auto
      moreover have "\<not> loose_bvar1 r 1" using eta s0 by simp
      then have "r[Bound 0/1] = r[lift d 0/1]" by (rule subst_not_free)
      ultimately have "Abs a U t = z" using eta s0 t by simp
      then show ?thesis by blast
    next
      case (appL s1 t1 u1)
      then have s1: "s1 = s0" "u1 = Bound 0" using eta by auto
      then have "\<not> loose_bvar1 t1 0" using eta appL free_beta by blast
      then have "Abs a U t \<rightarrow>\<^sub>\<eta> t1[d/0]" using appL s1 by simp
      moreover have "z \<rightarrow>\<^sub>\<beta> t1[d/0]" using eta appL s1 by simp
      ultimately show ?thesis by (meson r_into_rtranclp sup2I1)
    qed auto
  qed
qed

definition wt_unnamed :: "pterm \<Rightarrow> bool" where
  "wt_unnamed t \<longleftrightarrow> (\<exists>e T. e \<turnstile> t : T) \<and> unname t = t"

lemma wt_unnamed_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> wt_unnamed s \<Longrightarrow> wt_unnamed t"
  unfolding wt_unnamed_def by (meson subject_reduction_beta unname_beta_id)

lemma wt_unnamed_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> wt_unnamed s \<Longrightarrow> wt_unnamed t"
  unfolding wt_unnamed_def by (meson subject_reduction_eta unname_eta_id)

lemma square_beta_eta_restr:
  "square (restr wt_unnamed beta) (restr wt_unnamed eta) ((restr wt_unnamed eta)\<^sup>*\<^sup>*) ((restr wt_unnamed beta)\<^sup>=\<^sup>=)"
  unfolding square_def
proof (intro allI impI)
  fix x y z assume "restr wt_unnamed beta x y" "restr wt_unnamed eta x z"
  then have x: "wt_unnamed x" "x \<rightarrow>\<^sub>\<beta> y" "x \<rightarrow>\<^sub>\<eta> z" by (simp_all add: restr_def)
  then obtain e T where "e \<turnstile> x : T" "unname x = x" by (auto simp: wt_unnamed_def)
  with x obtain u where u: "y \<rightarrow>\<^sub>\<eta>\<^sup>* u" "beta\<^sup>=\<^sup>= z u" by (meson square_beta_eta_typed)
  have "wt_unnamed y" "wt_unnamed z" using x wt_unnamed_beta wt_unnamed_eta by blast+
  then show "\<exists>u. (restr wt_unnamed eta)\<^sup>*\<^sup>* y u \<and> (restr wt_unnamed beta)\<^sup>=\<^sup>= z u"
    using u wt_unnamed_eta by (auto simp: restr_rtrancl restr_def)
qed

theorem confluent_beta_eta_typed: "confluent (restr wt_unnamed (sup beta eta))"
  unfolding restr_sup
  by (assumption |
    rule square_rtrancl_reflcl_commute confluent_Un square_beta_eta_restr
      confluent_restr beta_confluent eta_confluent wt_unnamed_beta wt_unnamed_eta)+

lemma confluent_typed:
  assumes "wt_unnamed x" "(sup beta eta)\<^sup>*\<^sup>* x y" "(sup beta eta)\<^sup>*\<^sup>* x z"
  shows "\<exists>w. (sup beta eta)\<^sup>*\<^sup>* y w \<and> (sup beta eta)\<^sup>*\<^sup>* z w"
proof -
  have pres: "\<And>x y. sup beta eta x y \<Longrightarrow> wt_unnamed x \<Longrightarrow> wt_unnamed y"
    using wt_unnamed_beta wt_unnamed_eta by blast
  have "(restr wt_unnamed (sup beta eta))\<^sup>*\<^sup>* x y" "(restr wt_unnamed (sup beta eta))\<^sup>*\<^sup>* x z"
    using assms restr_rtrancl[where R = "sup beta eta" and P = wt_unnamed, OF pres] by simp_all
  then obtain w where "(restr wt_unnamed (sup beta eta))\<^sup>*\<^sup>* y w" "(restr wt_unnamed (sup beta eta))\<^sup>*\<^sup>* z w"
    using confluent_beta_eta_typed unfolding diamond_def commute_def square_def by blast
  then show ?thesis by (blast dest: restr_rtrancl_le)
qed

text \<open>
  Confluence of \<open>\<beta>\<eta>\<close> on well-typed Pure terms modulo \<open>\<alpha>\<close>-equivalence: reductions of
  \<open>\<alpha>\<close>-equivalent terms lead to \<open>\<alpha>\<close>-equivalent terms.
\<close>

theorem confluent_beta_eta_aconv:
  assumes "e \<turnstile> x : T" "aconv_term x x'" "(sup beta eta)\<^sup>*\<^sup>* x y" "(sup beta eta)\<^sup>*\<^sup>* x' z"
  shows "\<exists>u v. (sup beta eta)\<^sup>*\<^sup>* y u \<and> (sup beta eta)\<^sup>*\<^sup>* z v \<and> aconv_term u v"
proof -
  have x: "wt_unnamed (unname x)" using assms(1) by (auto simp: wt_unnamed_def intro: typing_unname)
  have "unname x' = unname x" using assms(2) by (simp add: aconv_term_unname)
  then have "(sup beta eta)\<^sup>*\<^sup>* (unname x) (unname y)" "(sup beta eta)\<^sup>*\<^sup>* (unname x) (unname z)"
    using assms(3,4) by (metis beta_eta_unname)+
  with x obtain w where "(sup beta eta)\<^sup>*\<^sup>* (unname y) w" "(sup beta eta)\<^sup>*\<^sup>* (unname z) w"
    by (blast dest: confluent_typed)
  then obtain u v where "(sup beta eta)\<^sup>*\<^sup>* y u" "unname u = w" "(sup beta eta)\<^sup>*\<^sup>* z v" "unname v = w"
    by (meson beta_eta_unname_back)
  then show ?thesis by (intro exI[of _ u] exI[of _ v]) (auto simp: aconv_term_unname)
qed


subsection \<open>\<open>\<alpha>\<beta>\<eta>\<close>-equivalence\<close>

text \<open>
  \<open>\<alpha>\<beta>\<eta>\<close>-equivalence is the equivalence closure of \<open>\<alpha>\<close>-steps and of \<open>\<beta>\<close>- and \<open>\<eta>\<close>-steps from
  well-typed terms.
\<close>

definition wt :: "pterm \<Rightarrow> bool" where
  "wt t \<longleftrightarrow> (\<exists>e T. e \<turnstile> t : T)"

definition conv_step :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "conv_step s t \<longleftrightarrow> s \<rightarrow>\<^sub>\<alpha> t \<or> wt s \<and> (s \<rightarrow>\<^sub>\<beta> t \<or> s \<rightarrow>\<^sub>\<eta> t)"

definition conv :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infix \<open>\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>\<close> 50) where
  "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<longleftrightarrow> equivclp conv_step s t"

lemma wt_conv_step: "conv_step s t \<Longrightarrow> wt s \<longleftrightarrow> wt t"
  unfolding conv_step_def wt_def
  by (metis alpha_sym typing_alpha subject_reduction_beta subject_reduction_eta)

lemma wt_conv: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> wt s \<longleftrightarrow> wt t"
  unfolding conv_def by (induction rule: equivclp_induct) (auto dest: wt_conv_step)

lemma aconv_term_conv: "aconv_term s t \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
proof -
  have "alpha\<^sup>*\<^sup>* \<le> conv_step\<^sup>*\<^sup>*" by (rule rtranclp_mono) (auto simp: conv_step_def)
  then have "equivclp conv_step t (unname t)" for t
    using alpha_unname[of t] by (blast intro: rtranclp_into_equivclp)
  then show "aconv_term s t \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
    unfolding conv_def aconv_term_unname by (metis equivclp_sym equivclp_trans)
qed

lemma beta_eta_conv: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> wt s \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
proof (induction rule: rtranclp_induct)
  case (step t t')
  then have "wt t" by (meson wt_conv)
  with step have "conv_step t t'" by (auto simp: conv_step_def)
  with step show ?case unfolding conv_def by (blast intro: equivclp_into_equivclp)
qed (simp add: conv_def)

lemma wt_aconv: "aconv_term s t \<Longrightarrow> wt s \<longleftrightarrow> wt t"
  by (simp add: aconv_term_unname wt_def) (metis typing_unname_iff)

text \<open>The Church--Rosser property of \<open>\<alpha>\<beta>\<eta>\<close>-equivalence on well-typed terms.\<close>

theorem church_rosser:
  assumes "wt s" "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "\<exists>u v. (sup beta eta)\<^sup>*\<^sup>* s u \<and> (sup beta eta)\<^sup>*\<^sup>* t v \<and> aconv_term u v"
proof -
  have "wt t \<and> (\<exists>w. (sup beta eta)\<^sup>*\<^sup>* (unname s) w \<and> (sup beta eta)\<^sup>*\<^sup>* (unname t) w)"
    using assms(2) unfolding conv_def
  proof (induction rule: equivclp_induct)
    case base
    with assms(1) show ?case by blast
  next
    case (step y z)
    then obtain w where w: "(sup beta eta)\<^sup>*\<^sup>* (unname s) w" "(sup beta eta)\<^sup>*\<^sup>* (unname y) w"
      and "wt y" by blast
    then have "wt z" using step.hyps(2) wt_conv_step by blast
    have ty: "wt_unnamed (unname y)"
      using \<open>wt y\<close> by (auto simp: wt_def wt_unnamed_def intro: typing_unname)
    from step.hyps(2) consider "unname y = unname z"
      | "sup beta eta (unname y) (unname z)" | "sup beta eta (unname z) (unname y)"
      unfolding conv_step_def by (metis beta_unname eta_unname sup2I1 sup2I2 unname_alpha)
    then show ?case
    proof cases
      case 1
      with w \<open>wt z\<close> show ?thesis by metis
    next
      case 2
      then obtain w' where "(sup beta eta)\<^sup>*\<^sup>* w w'" "(sup beta eta)\<^sup>*\<^sup>* (unname z) w'"
        using confluent_typed[OF ty w(2)] by (meson r_into_rtranclp)
      with w \<open>wt z\<close> show ?thesis by (meson rtranclp_trans)
    next
      case 3
      with w \<open>wt z\<close> show ?thesis by (meson converse_rtranclp_into_rtranclp)
    qed
  qed
  then obtain w where "(sup beta eta)\<^sup>*\<^sup>* (unname s) w" "(sup beta eta)\<^sup>*\<^sup>* (unname t) w" by blast
  then obtain u v where "(sup beta eta)\<^sup>*\<^sup>* s u" "unname u = w" "(sup beta eta)\<^sup>*\<^sup>* t v" "unname v = w"
    by (meson beta_eta_unname_back)
  then show ?thesis by (intro exI[of _ u] exI[of _ v]) (auto simp: aconv_term_unname)
qed

theorem conv_iff:
  assumes "wt s"
  shows "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<longleftrightarrow>
    wt t \<and> (\<exists>u v. (sup beta eta)\<^sup>*\<^sup>* s u \<and> (sup beta eta)\<^sup>*\<^sup>* t v \<and> aconv_term u v)"
proof
  assume "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  with assms show "wt t \<and> (\<exists>u v. (sup beta eta)\<^sup>*\<^sup>* s u \<and> (sup beta eta)\<^sup>*\<^sup>* t v \<and> aconv_term u v)"
    using church_rosser wt_conv by blast
next
  assume "wt t \<and> (\<exists>u v. (sup beta eta)\<^sup>*\<^sup>* s u \<and> (sup beta eta)\<^sup>*\<^sup>* t v \<and> aconv_term u v)"
  then obtain u v where "wt t" "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* t v" "aconv_term u v"
    by blast
  with assms have "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u" "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> v" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> v"
    by (auto intro: beta_eta_conv aconv_term_conv)
  then show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" unfolding conv_def by (metis equivclp_sym equivclp_trans)
qed


lemma wt_AppD: "wt (s $ t) \<Longrightarrow> wt s \<and> wt t"
  unfolding wt_def by blast

lemma wt_AbsD: "wt (Abs a T s) \<Longrightarrow> wt s"
  unfolding wt_def by blast

lemma conv_App:
  assumes "wt (s $ t)" "wt (s' $ t')" "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s'" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
  shows "s $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' $ t'"
proof -
  obtain u u' where u: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* s' u'" "aconv_term u u'"
    using conv_iff[of s s'] assms(1,3) wt_AppD by blast
  obtain v v' where v: "(sup beta eta)\<^sup>*\<^sup>* t v" "(sup beta eta)\<^sup>*\<^sup>* t' v'" "aconv_term v v'"
    using conv_iff[of t t'] assms(1,4) wt_AppD by blast
  have "(sup beta eta)\<^sup>*\<^sup>* (s $ t) (u $ v)" "(sup beta eta)\<^sup>*\<^sup>* (s' $ t') (u' $ v')"
    using u v by (auto intro: rtrancl_beta_eta_App)
  moreover have "aconv_term (u $ v) (u' $ v')" using u(3) v(3) by simp
  ultimately show ?thesis using conv_iff[of "s $ t" "s' $ t'"] assms(1,2) by blast
qed

lemma conv_Abs:
  assumes "wt (Abs a T s)" "wt (Abs b T s')" "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s'"
  shows "Abs a T s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs b T s'"
proof -
  obtain u u' where u: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* s' u'" "aconv_term u u'"
    using conv_iff[of s s'] assms(1,3) wt_AbsD by blast
  have "(sup beta eta)\<^sup>*\<^sup>* (Abs a T s) (Abs a T u)" "(sup beta eta)\<^sup>*\<^sup>* (Abs b T s') (Abs b T u')"
    using u by (auto intro: rtrancl_beta_eta_Abs)
  moreover have "aconv_term (Abs a T u) (Abs b T u')" using u(3) by simp
  ultimately show ?thesis using conv_iff[of "Abs a T s" "Abs b T s'"] assms(1,2) by blast
qed


subsection \<open>Type instantiation\<close>

text \<open>Type instantiations that preserve the certification of types and constants.\<close>

definition inst_ok :: "tinst \<Rightarrow> bool" where
  "inst_ok \<rho> \<longleftrightarrow> (\<forall>U. ty_ok U \<longrightarrow> ty_ok (tsubst \<rho> U)) \<and> (\<forall>c U. const_ok c U \<longrightarrow> const_ok c (tsubst \<rho> U))"

lemma typing_inst:
  "e \<turnstile> t : T \<Longrightarrow> inst_ok \<rho> \<Longrightarrow> (\<lambda>j. tsubst \<rho> (e j)) \<turnstile> inst \<rho> t : tsubst \<rho> T"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  then show ?case by (auto simp: tsubst_shift inst_ok_def)
qed (auto simp: inst_ok_def)

lemma conv_inst: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> inst_ok \<rho> \<Longrightarrow> inst \<rho> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> inst \<rho> t"
proof -
  assume \<rho>: "inst_ok \<rho>"
  have step: "conv_step s t \<Longrightarrow> conv_step (inst \<rho> s) (inst \<rho> t)" for s t
    unfolding conv_step_def wt_def
    by (meson alpha_inst beta_inst eta_inst typing_inst[OF _ \<rho>])
  show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> inst \<rho> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> inst \<rho> t"
    unfolding conv_def by (induction rule: equivclp_induct) (auto intro: equivclp_into_equivclp step)
qed

end

end
