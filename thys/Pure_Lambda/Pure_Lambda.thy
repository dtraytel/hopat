section \<open>The \<open>\<lambda>\<close>-Calculus on Pure Terms\<close>

theory Pure_Lambda
  imports "Pure_Pattern.Pure_Term" "HOL-Proofs-Lambda.Commutation"
begin

text \<open>
  \<open>\<beta>\<close>- and \<open>\<eta>\<close>-reduction and their confluence, directly on the terms \<^typ>\<open>pterm\<close> of
  Pure, following \<^file>\<open>~~/src/HOL/Proofs/Lambda/Lambda.thy\<close>,
  \<^file>\<open>~~/src/HOL/Proofs/Lambda/ParRed.thy\<close> and \<^file>\<open>~~/src/HOL/Proofs/Lambda/Eta.thy\<close>.
  The names and types of abstractions are inert labels. Bound variables with negative indices
  do not occur in Pure, but they need no exclusion: at non-negative levels, lifting and
  substitution leave them unchanged, like constants.
\<close>

lemmas integer_arith = integer_less_iff integer_less_eq_iff integer_eq_iff


subsection \<open>Lifting and substitution\<close>

abbreviation lift :: "pterm \<Rightarrow> integer \<Rightarrow> pterm" where
  "lift t k \<equiv> incr_bv 1 k t"

fun subst :: "pterm \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> pterm"  (\<open>_[_'/_]\<close> [300, 0, 0] 300) where
  subst_Bound: "(Bound i)[s/k] = (if k < i then Bound (i - 1) else if i = k then s else Bound i)"
| subst_App: "(t $ u)[s/k] = t[s/k] $ u[s/k]"
| subst_Abs: "(Abs a T t)[s/k] = Abs a T (t[lift s 0 / k + 1])"
| subst_atom: "t[s/k] = t"

declare subst_Bound [simp del]

lemma subst_eq [simp]: "(Bound k)[u/k] = u"
  by (simp add: subst_Bound)

lemma subst_gt [simp]: "i < j \<Longrightarrow> (Bound j)[u/i] = Bound (j - 1)"
  by (simp add: subst_Bound)

lemma subst_lt [simp]: "j < i \<Longrightarrow> (Bound j)[u/i] = Bound j"
  by (simp add: subst_Bound)

lemma lift_lift:
  "i \<le> k \<Longrightarrow> lift (lift t i) (k + 1) = lift (lift t k) i"
proof (induction t arbitrary: i k)
  case (Abs a T t)
  then show ?case using Abs.IH[of "i + 1" "k + 1"] by simp
qed (auto simp: integer_arith)

lemma lift_subst [simp]:
  "j \<le> i \<Longrightarrow> 0 \<le> i \<Longrightarrow> lift (t[s/j]) i = (lift t (i + 1)) [lift s i / j]"
proof (induction t arbitrary: i j s)
  case (Abs a T t)
  then show ?case
    using Abs.IH[of "j + 1" "i + 1" "lift s 0"] lift_lift[of 0 i s] by simp
qed (auto simp: subst_Bound integer_arith)

lemma lift_subst_lt:
  "i \<le> j \<Longrightarrow> 0 \<le> i \<Longrightarrow> lift (t[s/j]) i = (lift t i) [lift s i / j + 1]"
proof (induction t arbitrary: i j s)
  case (Abs a T t)
  then show ?case
    using Abs.IH[of "i + 1" "j + 1" "lift s 0"] lift_lift[of 0 i s] by simp
qed (auto simp: subst_Bound integer_arith)

lemma subst_lift [simp]: "(lift t k)[s/k] = t"
proof (induction t arbitrary: k s)
  case (Abs a T t)
  then show ?case using Abs.IH[of "k + 1"] by simp
qed (auto simp: subst_Bound integer_arith)

lemma subst_subst:
  "i \<le> j \<Longrightarrow> 0 \<le> i \<Longrightarrow> t[lift v i / j + 1][u[v/j]/i] = t[u/i][v/j]"
proof (induction t arbitrary: i j u v)
  case (Abs a T t)
  then show ?case
    using Abs.IH[of "i + 1" "j + 1" "lift v 0" "lift u 0"] lift_lift[of 0 i v]
      lift_subst_lt[of 0 j u v]
    by simp
qed (auto simp: subst_Bound integer_arith)


subsection \<open>Pure's substitution\<close>

lemma incr_bv_0 [simp]: "incr_bv 0 k t = t"
  by (induction "0::integer" k t rule: incr_bv.induct) auto

lemma incr_bv_Suc: "0 \<le> n \<Longrightarrow> incr_bv (n + 1) k t = lift (incr_bv n k t) k"
  by (induction n k t rule: incr_bv.induct) (auto simp: integer_arith)

lemma subst_bound_aux_subst:
  "0 \<le> lev \<Longrightarrow> subst_bound_aux arg lev t = t[incr_boundvars lev arg / lev]"
proof (induction arg lev t rule: subst_bound_aux.induct)
  case (2 arg lev a T t)
  then show ?case
    using incr_bv_Suc[of lev 0 arg] by (simp add: incr_boundvars_def add.commute)
qed (auto simp: incr_boundvars_def subst_Bound integer_arith)

lemma subst_bound_subst: "subst_bound arg t = t[arg/0]"
  by (simp add: subst_bound_def subst_bound_aux_subst incr_boundvars_def incr_bv_0)


subsection \<open>\<open>\<beta>\<close>-reduction\<close>

inductive beta :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<close> 50) where
  beta [simp, intro!]: "Abs a T s $ t \<rightarrow>\<^sub>\<beta> s[t/0]"
| appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s $ u \<rightarrow>\<^sub>\<beta> t $ u"
| appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> u $ s \<rightarrow>\<^sub>\<beta> u $ t"
| abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Abs a T s \<rightarrow>\<^sub>\<beta> Abs a T t"

abbreviation beta_reds :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<^sup>*\<close> 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<equiv> beta\<^sup>*\<^sup>* s t"

inductive_cases beta_cases [elim!]:
  "Bound i \<rightarrow>\<^sub>\<beta> t"
  "Const c T \<rightarrow>\<^sub>\<beta> t"
  "Free x T \<rightarrow>\<^sub>\<beta> t"
  "Var x T \<rightarrow>\<^sub>\<beta> t"
  "Abs a T r \<rightarrow>\<^sub>\<beta> s"
  "s $ t \<rightarrow>\<^sub>\<beta> u"

lemma rtrancl_beta_Abs [intro!]: "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> Abs a T s \<rightarrow>\<^sub>\<beta>\<^sup>* Abs a T s'"
  by (induction set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL: "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<beta>\<^sup>* s' $ t"
  by (induction set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<beta>\<^sup>* s $ t'"
  by (induction set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]: "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<beta>\<^sup>* s' $ t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)

theorem subst_preserves_beta [simp]: "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> 0 \<le> i \<Longrightarrow> r[t/i] \<rightarrow>\<^sub>\<beta> s[t/i]"
  by (induction arbitrary: t i set: beta) (simp_all add: subst_subst [symmetric])

theorem lift_preserves_beta [simp]: "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> 0 \<le> i \<Longrightarrow> lift r i \<rightarrow>\<^sub>\<beta> lift s i"
  by (induction arbitrary: i set: beta) auto


subsection \<open>Parallel reduction and confluence of \<open>\<beta>\<close>\<close>

inductive par_beta :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<Rightarrow>\<^sub>\<beta>\<close> 50) where
  bound [simp, intro!]: "Bound i \<Rightarrow>\<^sub>\<beta> Bound i"
| const [simp, intro!]: "Const c T \<Rightarrow>\<^sub>\<beta> Const c T"
| free [simp, intro!]: "Free x T \<Rightarrow>\<^sub>\<beta> Free x T"
| var [simp, intro!]: "Var x T \<Rightarrow>\<^sub>\<beta> Var x T"
| abs [simp, intro!]: "s \<Rightarrow>\<^sub>\<beta> t \<Longrightarrow> Abs a T s \<Rightarrow>\<^sub>\<beta> Abs a T t"
| app [simp, intro!]: "s \<Rightarrow>\<^sub>\<beta> s' \<Longrightarrow> t \<Rightarrow>\<^sub>\<beta> t' \<Longrightarrow> s $ t \<Rightarrow>\<^sub>\<beta> s' $ t'"
| beta [simp, intro!]: "s \<Rightarrow>\<^sub>\<beta> s' \<Longrightarrow> t \<Rightarrow>\<^sub>\<beta> t' \<Longrightarrow> Abs a T s $ t \<Rightarrow>\<^sub>\<beta> s'[t'/0]"

inductive_cases par_beta_cases [elim!]:
  "Bound i \<Rightarrow>\<^sub>\<beta> t"
  "Const c T \<Rightarrow>\<^sub>\<beta> t"
  "Free x T \<Rightarrow>\<^sub>\<beta> t"
  "Var x T \<Rightarrow>\<^sub>\<beta> t"
  "Abs a T s \<Rightarrow>\<^sub>\<beta> Abs b U t"
  "Abs a T s $ t \<Rightarrow>\<^sub>\<beta> u"
  "s $ t \<Rightarrow>\<^sub>\<beta> u"
  "Abs a T s \<Rightarrow>\<^sub>\<beta> t"

lemma par_beta_refl [simp]: "t \<Rightarrow>\<^sub>\<beta> t"
  by (induction t) simp_all

lemma beta_subset_par_beta: "beta \<le> par_beta"
  by (rule predicate2I, erule beta.induct) (blast intro!: par_beta_refl)+

lemma par_beta_subset_beta: "par_beta \<le> beta\<^sup>*\<^sup>*"
  by (rule predicate2I, erule par_beta.induct)
    (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma par_beta_lift [simp]: "t \<Rightarrow>\<^sub>\<beta> t' \<Longrightarrow> 0 \<le> n \<Longrightarrow> lift t n \<Rightarrow>\<^sub>\<beta> lift t' n"
  by (induction arbitrary: n rule: par_beta.induct) auto

lemma par_beta_subst:
  "s \<Rightarrow>\<^sub>\<beta> s' \<Longrightarrow> t \<Rightarrow>\<^sub>\<beta> t' \<Longrightarrow> 0 \<le> n \<Longrightarrow> t[s/n] \<Rightarrow>\<^sub>\<beta> t'[s'/n]"
proof (induction t arbitrary: s s' t' n)
  case (App t u)
  from App.prems(2) show ?case
  proof cases
    case (beta r r' u' a T)
    then have "Abs a T r \<Rightarrow>\<^sub>\<beta> Abs a T r'" by auto
    then have "Abs a T (r[lift s 0 / n + 1]) \<Rightarrow>\<^sub>\<beta> Abs a T (r'[lift s' 0 / n + 1])"
      using App.IH(1)[of s s' "Abs a T r'" n] App.prems beta by simp
    moreover have "u[s/n] \<Rightarrow>\<^sub>\<beta> u'[s'/n]"
      using App.IH(2) App.prems beta by simp
    ultimately have "Abs a T (r[lift s 0 / n + 1]) $ u[s/n] \<Rightarrow>\<^sub>\<beta> (r'[lift s' 0 / n + 1])[u'[s'/n] / 0]"
      by blast
    with beta App.prems show ?thesis
      using subst_subst[of 0 n r' s' u'] by simp
  next
    case (app t' u')
    with App show ?thesis by auto
  qed
next
  case (Abs a T t)
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma diamond_par_beta: "diamond par_beta"
  unfolding diamond_def commute_def square_def
  by (rule impI [THEN allI [THEN allI]], erule par_beta.induct) (blast intro!: par_beta_subst)+

theorem beta_confluent: "confluent beta"
  by (rule diamond_par_beta diamond_to_confluence par_beta_subset_beta beta_subset_par_beta)+


subsection \<open>\<open>\<eta>\<close>-reduction\<close>

text \<open>Pure's \<^const>\<open>loose_bvar1\<close> is the test for free occurrences of a bound variable.\<close>

inductive eta :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<eta>\<close> 50) where
  eta [simp, intro]: "\<not> loose_bvar1 s 0 \<Longrightarrow> Abs a T (s $ Bound 0) \<rightarrow>\<^sub>\<eta> s[dummy/0]"
| appL [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> s $ u \<rightarrow>\<^sub>\<eta> t $ u"
| appR [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> u $ s \<rightarrow>\<^sub>\<eta> u $ t"
| abs [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> Abs a T s \<rightarrow>\<^sub>\<eta> Abs a T t"

abbreviation eta_reds :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<eta>\<^sup>*\<close> 50) where
  "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<equiv> eta\<^sup>*\<^sup>* s t"

inductive_cases eta_cases [elim!]:
  "Abs a T s \<rightarrow>\<^sub>\<eta> z"
  "s $ t \<rightarrow>\<^sub>\<eta> u"
  "Bound i \<rightarrow>\<^sub>\<eta> t"
  "Const c T \<rightarrow>\<^sub>\<eta> t"
  "Free x T \<rightarrow>\<^sub>\<eta> t"
  "Var x T \<rightarrow>\<^sub>\<eta> t"

lemma subst_not_free [simp]: "\<not> loose_bvar1 s i \<Longrightarrow> s[t/i] = s[u/i]"
proof (induction s arbitrary: i t u)
  case (Abs a T s)
  then show ?case using Abs.IH[of "i + 1"] by simp
qed (auto simp: subst_Bound)

lemma free_lift [simp]:
  "loose_bvar1 (lift t k) i = (i < k \<and> loose_bvar1 t i \<or> k < i \<and> loose_bvar1 t (i - 1))"
proof (induction t arbitrary: i k)
  case (Abs a T t)
  then show ?case using Abs.IH[where i = "i + 1" and k = "k + 1"] by (simp add: algebra_simps)
qed (auto simp: integer_arith)

lemma free_subst [simp]:
  "0 \<le> i \<Longrightarrow> loose_bvar1 (s[t/k]) i =
    (loose_bvar1 s k \<and> loose_bvar1 t i \<or> loose_bvar1 s (if i < k then i else i + 1))"
proof (induction s arbitrary: i k t)
  case (Abs a T s)
  then show ?case using Abs.IH[where i = "i + 1" and k = "k + 1" and t = "lift t 0"] by (simp add: integer_arith)
qed (auto simp: subst_Bound integer_arith)

lemma free_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> i \<Longrightarrow> loose_bvar1 t i = loose_bvar1 s i"
  by (induction arbitrary: i set: eta) (simp_all cong: conj_cong)

lemma eta_subst [simp]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> i \<Longrightarrow> s[u/i] \<rightarrow>\<^sub>\<eta> t[u/i]"
proof (induction arbitrary: u i set: eta)
  case (eta s a T dummy)
  then show ?case
    using eta.eta[of "s[lift u 0 / i + 1]" a T "dummy[u/i]"] subst_subst[of 0 i s u dummy] by simp
qed simp_all

lemma lift_subst_dummy: "\<not> loose_bvar1 s i \<Longrightarrow> lift (s[dummy/i]) i = s"
proof (induction s arbitrary: i dummy)
  case (Abs a T s)
  then show ?case using Abs.IH[of "i + 1"] by simp
qed (auto simp: subst_Bound integer_arith)


subsection \<open>Confluence of \<open>\<eta>\<close> and of \<open>\<beta>\<eta>\<close>\<close>

lemma eta_refl_appL: "eta\<^sup>=\<^sup>= s t \<Longrightarrow> eta\<^sup>=\<^sup>= (s $ u) (t $ u)"
  by auto

lemma eta_refl_appR: "eta\<^sup>=\<^sup>= s t \<Longrightarrow> eta\<^sup>=\<^sup>= (u $ s) (u $ t)"
  by auto

lemma eta_refl_abs: "eta\<^sup>=\<^sup>= s t \<Longrightarrow> eta\<^sup>=\<^sup>= (Abs a T s) (Abs a T t)"
  by auto

lemma square_eta: "square eta eta (eta\<^sup>=\<^sup>=) (eta\<^sup>=\<^sup>=)"
proof -
  have "\<exists>u. eta\<^sup>=\<^sup>= y u \<and> eta\<^sup>=\<^sup>= z u" if "x \<rightarrow>\<^sub>\<eta> y" "x \<rightarrow>\<^sub>\<eta> z" for x y z
    using that
  proof (induction arbitrary: z rule: eta.induct)
    case (eta s a T d)
    from eta.prems show ?case
    proof cases
      case (eta d')
      with \<open>\<not> loose_bvar1 s 0\<close> show ?thesis by auto
    next
      case (abs z')
      then obtain s' where s': "s \<rightarrow>\<^sub>\<eta> s'" "z = Abs a T (s' $ Bound 0)" by auto
      then have "\<not> loose_bvar1 s' 0" using \<open>\<not> loose_bvar1 s 0\<close> by (simp add: free_eta)
      then have "eta z (s'[d/0])" using s' by simp
      moreover have "eta (s[d/0]) (s'[d/0])" using s' by simp
      ultimately show ?thesis by (meson sup2I1)
    qed
  next
    case (appL s t u)
    from appL.prems show ?case
    proof cases
      case (appL t')
      then obtain w where "eta\<^sup>=\<^sup>= t w" "eta\<^sup>=\<^sup>= t' w" using appL.IH by blast
      with appL show ?thesis by (blast intro: eta_refl_appL)
    next
      case (appR u')
      then have "eta (t $ u) (t $ u')" "eta z (t $ u')" using appL.hyps by auto
      then show ?thesis by (meson sup2I1)
    qed
  next
    case (appR s t u)
    from appR.prems show ?case
    proof cases
      case (appR t')
      then obtain w where "eta\<^sup>=\<^sup>= t w" "eta\<^sup>=\<^sup>= t' w" using appR.IH by blast
      with appR show ?thesis by (blast intro: eta_refl_appR)
    next
      case (appL u')
      then have "eta (u $ t) (u' $ t)" "eta z (u' $ t)" using appR.hyps by auto
      then show ?thesis by blast
    qed
  next
    case (abs s t a T)
    from abs.prems show ?case
    proof cases
      case (eta s0 d)
      with abs.hyps obtain t0 where t0: "s0 \<rightarrow>\<^sub>\<eta> t0" "t = t0 $ Bound 0" by auto
      then have "\<not> loose_bvar1 t0 0" using \<open>\<not> loose_bvar1 s0 0\<close> by (simp add: free_eta)
      then have "eta (Abs a T t) (t0[d/0])" using t0 by simp
      moreover have "eta z (t0[d/0])" using eta t0 by simp
      ultimately show ?thesis by (meson sup2I1)
    next
      case (abs t')
      then obtain w where "eta\<^sup>=\<^sup>= t w" "eta\<^sup>=\<^sup>= t' w" using abs.IH by blast
      with abs show ?thesis by (blast intro: eta_refl_abs)
    qed
  qed
  then show ?thesis unfolding square_def by blast
qed

theorem eta_confluent: "confluent eta"
  by (rule square_eta [THEN square_reflcl_confluent])

lemma rtrancl_eta_Abs: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> Abs a T s \<rightarrow>\<^sub>\<eta>\<^sup>* Abs a T s'"
  by (induction set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_AppL: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<eta>\<^sup>* s' $ t"
  by (induction set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_AppR: "t \<rightarrow>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<eta>\<^sup>* s $ t'"
  by (induction set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_App: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> t \<rightarrow>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<eta>\<^sup>* s' $ t'"
  by (blast intro!: rtrancl_eta_AppL rtrancl_eta_AppR intro: rtranclp_trans)

lemma free_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> 0 \<le> i \<Longrightarrow> loose_bvar1 t i \<Longrightarrow> loose_bvar1 s i"
  by (induction arbitrary: i set: beta) auto

lemma subst_Bound_Suc [simp]: "0 \<le> i \<Longrightarrow> t[Bound i / i] = t[Bound i / i + 1]"
proof (induction t arbitrary: i)
  case (Abs a T t)
  then show ?case using Abs.IH[of "i + 1"] by (simp add: integer_arith)
qed (auto simp: subst_Bound integer_arith)

lemma eta_lift [simp]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> i \<Longrightarrow> lift s i \<rightarrow>\<^sub>\<eta> lift t i"
proof (induction arbitrary: i set: eta)
  case (eta s a T dummy)
  then show ?case
    using eta.eta[of "lift s (i + 1)" a T "lift dummy i"] lift_subst[of 0 i s dummy] by simp
qed simp_all

lemma rtrancl_eta_subst: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> i \<Longrightarrow> u[s/i] \<rightarrow>\<^sub>\<eta>\<^sup>* u[t/i]"
proof (induction u arbitrary: s t i)
  case (App u1 u2)
  then show ?case by (simp add: rtrancl_eta_App)
next
  case (Abs a T u)
  then show ?case using Abs.IH[of "lift s 0" "lift t 0" "i + 1"] by (simp add: rtrancl_eta_Abs)
qed (auto simp: subst_Bound)

text \<open>
  \<open>\<beta>\<close> and \<open>\<eta>\<close> do not commute on labelled terms: in \<open>\<lambda>a:T. (\<lambda>b:U. b) a\<close> the
  \<open>\<beta>\<close>-redex and the \<open>\<eta>\<close>-redex overlap, and the two normal forms differ in their labels.
\<close>

lemma beta_eta_not_confluent:
  fixes a b :: name and T U :: ptyp
  assumes "(a, T) \<noteq> (b, U)"
  shows "\<not> confluent (sup beta eta)"
proof
  let ?x = "Abs a T (Abs b U (Bound 0) $ Bound 0)"
  have nf: "\<not> (sup beta eta) (Abs c V (Bound 0)) w" for c V w
    by auto
  then have nf': "(sup beta eta)\<^sup>*\<^sup>* (Abs c V (Bound 0)) w \<longleftrightarrow> w = Abs c V (Bound 0)" for c V w
    by (metis converse_rtranclpE rtranclp.rtrancl_refl)
  have "(sup beta eta) ?x (Abs a T (Bound 0))"
    using beta.abs[OF beta.beta[of b U "Bound 0" "Bound 0"]] by auto
  moreover have "(sup beta eta) ?x (Abs b U (Bound 0))"
    using eta.eta[of "Abs b U (Bound 0)" a T "Bound 0"] by simp
  moreover assume "confluent (sup beta eta)"
  ultimately obtain w where "(sup beta eta)\<^sup>*\<^sup>* (Abs a T (Bound 0)) w"
      "(sup beta eta)\<^sup>*\<^sup>* (Abs b U (Bound 0)) w"
    unfolding diamond_def commute_def square_def by (meson r_into_rtranclp)
  with nf' assms show False by simp
qed


subsection \<open>Names of bound variables\<close>

text \<open>
  \<open>unname\<close> replaces the names of all bound variables by the empty name: a canonical
  representative of the \<open>\<alpha>\<close>-equivalence class (\<^const>\<open>aconv_term\<close>).
\<close>

fun unname :: "pterm \<Rightarrow> pterm" where
  "unname (Abs a T t) = Abs STR '''' T (unname t)"
| "unname (s $ t) = unname s $ unname t"
| "unname t = t"

lemma unname_unname [simp]: "unname (unname t) = unname t"
  by (induction t) auto

lemma unname_lift [simp]: "unname (incr_bv n k t) = incr_bv n k (unname t)"
  by (induction n k t rule: incr_bv.induct) auto

lemma unname_subst [simp]: "unname (t[s/k]) = (unname t)[unname s/k]"
  by (induction t arbitrary: s k) (auto simp: subst_Bound)

lemma loose_bvar1_unname [simp]: "loose_bvar1 (unname t) k = loose_bvar1 t k"
  by (induction t arbitrary: k) auto

lemma unname_beta_id: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> unname s = s \<Longrightarrow> unname t = t"
  by (induction set: beta) auto

lemma unname_eta_id: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> unname s = s \<Longrightarrow> unname t = t"
proof (induction set: eta)
  case (eta s a T d)
  have "s[unname d/0] = s[d/0]" using \<open>\<not> loose_bvar1 s 0\<close> by (rule subst_not_free)
  with eta show ?case by simp
qed auto

lemma beta_unname: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> unname s \<rightarrow>\<^sub>\<beta> unname t"
  by (induction set: beta) auto

lemma eta_unname: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> unname s \<rightarrow>\<^sub>\<eta> unname t"
  by (induction set: eta) auto

lemma beta_eta_unname: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (unname s) (unname t)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl beta_unname eta_unname)

lemma unname_eq_atom [simp]:
  "unname t = Const c T \<longleftrightarrow> t = Const c T" "Const c T = unname t \<longleftrightarrow> t = Const c T"
  "unname t = Free x T \<longleftrightarrow> t = Free x T" "Free x T = unname t \<longleftrightarrow> t = Free x T"
  "unname t = Var v T \<longleftrightarrow> t = Var v T" "Var v T = unname t \<longleftrightarrow> t = Var v T"
  "unname t = Bound i \<longleftrightarrow> t = Bound i" "Bound i = unname t \<longleftrightarrow> t = Bound i"
  by (cases t; auto)+

lemma unname_eq_Abs:
  "unname t = Abs a T u \<longleftrightarrow> (\<exists>b t'. t = Abs b T t' \<and> a = STR '''' \<and> u = unname t')"
  by (cases t) auto

lemma unname_eq_App: "unname t = u1 $ u2 \<longleftrightarrow> (\<exists>t1 t2. t = t1 $ t2 \<and> u1 = unname t1 \<and> u2 = unname t2)"
  by (cases t) auto

lemma aconv_term_unname: "aconv_term s t \<longleftrightarrow> unname s = unname t"
  by (induction s t rule: aconv_term.induct) (auto elim: unname.elims)

text \<open>Reductions of \<^term>\<open>unname s\<close> are reductions of \<open>s\<close>, up to the names of bound variables.\<close>

lemma beta_unname_back: "unname s \<rightarrow>\<^sub>\<beta> w \<Longrightarrow> \<exists>u. s \<rightarrow>\<^sub>\<beta> u \<and> unname u = w"
proof (induction s arbitrary: w)
  case (App s1 s2)
  from App.prems have "unname s1 $ unname s2 \<rightarrow>\<^sub>\<beta> w" by simp
  then show ?case
  proof cases
    case (beta a T r)
    then obtain b r' where "s1 = Abs b T r'" "r = unname r'" by (auto simp: unname_eq_Abs)
    with beta show ?thesis by (intro exI[of _ "r'[s2/0]"]) auto
  next
    case (appL s1')
    with App.IH(1) obtain u1 where "s1 \<rightarrow>\<^sub>\<beta> u1" "unname u1 = s1'" by blast
    with appL show ?thesis by (intro exI[of _ "u1 $ s2"]) auto
  next
    case (appR s2')
    with App.IH(2) obtain u2 where "s2 \<rightarrow>\<^sub>\<beta> u2" "unname u2 = s2'" by blast
    with appR show ?thesis by (intro exI[of _ "s1 $ u2"]) auto
  qed
next
  case (Abs a T t)
  from Abs.prems obtain w' where "unname t \<rightarrow>\<^sub>\<beta> w'" "w = Abs STR '''' T w'" by auto
  with Abs.IH obtain u where "t \<rightarrow>\<^sub>\<beta> u" "unname u = w'" by blast
  with \<open>w = _\<close> show ?case by (intro exI[of _ "Abs a T u"]) auto
qed auto

lemma eta_unname_back: "unname s \<rightarrow>\<^sub>\<eta> w \<Longrightarrow> \<exists>u. s \<rightarrow>\<^sub>\<eta> u \<and> unname u = w"
proof (induction s arbitrary: w)
  case (App s1 s2)
  from App.prems have "unname s1 $ unname s2 \<rightarrow>\<^sub>\<eta> w" by simp
  then show ?case
  proof cases
    case (appL s1')
    with App.IH(1) obtain u1 where "s1 \<rightarrow>\<^sub>\<eta> u1" "unname u1 = s1'" by blast
    with appL show ?thesis by (intro exI[of _ "u1 $ s2"]) auto
  next
    case (appR s2')
    with App.IH(2) obtain u2 where "s2 \<rightarrow>\<^sub>\<eta> u2" "unname u2 = s2'" by blast
    with appR show ?thesis by (intro exI[of _ "s1 $ u2"]) auto
  qed
next
  case (Abs a T t)
  from Abs.prems have "Abs STR '''' T (unname t) \<rightarrow>\<^sub>\<eta> w" by simp
  then show ?case
  proof cases
    case (eta s0 d)
    then obtain t1 where t: "t = t1 $ Bound 0" "s0 = unname t1" by (auto simp: unname_eq_App)
    with eta have "\<not> loose_bvar1 t1 0" by simp
    moreover have "(unname t1)[unname d/0] = (unname t1)[d/0]"
      using \<open>\<not> loose_bvar1 s0 0\<close> t by (simp add: subst_not_free)
    ultimately show ?thesis using eta t by (intro exI[of _ "t1[d/0]"]) auto
  next
    case (abs w')
    with Abs.IH obtain u where "t \<rightarrow>\<^sub>\<eta> u" "unname u = w'" by blast
    with abs show ?thesis by (intro exI[of _ "Abs a T u"]) auto
  qed
qed auto

lemma beta_eta_unname_back:
  "(sup beta eta)\<^sup>*\<^sup>* (unname s) w \<Longrightarrow> \<exists>u. (sup beta eta)\<^sup>*\<^sup>* s u \<and> unname u = w"
proof (induction rule: rtranclp_induct)
  case (step w w')
  then obtain u where u: "(sup beta eta)\<^sup>*\<^sup>* s u" "unname u = w" by blast
  with step.hyps(2) obtain u' where u': "sup beta eta u u'" "unname u' = w'"
    using beta_unname_back eta_unname_back by (metis sup2E sup2I1 sup2I2)
  have "(sup beta eta)\<^sup>*\<^sup>* s u'" using u(1) u'(1) by (rule rtranclp.rtrancl_into_rtrancl)
  with u'(2) show ?case by blast
qed blast


subsection \<open>Relations restricted to sources with a property that they preserve\<close>

definition restr :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "restr P R x y \<longleftrightarrow> P x \<and> R x y"

lemma restr_rtrancl_preserves:
  assumes "\<And>x y. R x y \<Longrightarrow> P x \<Longrightarrow> P y"
  shows "R\<^sup>*\<^sup>* x y \<Longrightarrow> P x \<Longrightarrow> P y"
  by (induction rule: rtranclp_induct) (use assms in blast)+

lemma restr_rtrancl:
  assumes "\<And>x y. R x y \<Longrightarrow> P x \<Longrightarrow> P y" and "P x"
  shows "(restr P R)\<^sup>*\<^sup>* x y \<longleftrightarrow> R\<^sup>*\<^sup>* x y"
proof
  show "(restr P R)\<^sup>*\<^sup>* x y \<Longrightarrow> R\<^sup>*\<^sup>* x y"
    by (induction rule: rtranclp_induct) (auto simp: restr_def intro: rtranclp.rtrancl_into_rtrancl)
next
  have "R\<^sup>*\<^sup>* x y \<Longrightarrow> (restr P R)\<^sup>*\<^sup>* x y \<and> P y"
    by (induction rule: rtranclp_induct)
      (use assms in \<open>auto simp: restr_def intro: rtranclp.rtrancl_into_rtrancl\<close>)
  then show "R\<^sup>*\<^sup>* x y \<Longrightarrow> (restr P R)\<^sup>*\<^sup>* x y" by blast
qed

lemma restr_rtrancl_le: "(restr P R)\<^sup>*\<^sup>* x y \<Longrightarrow> R\<^sup>*\<^sup>* x y"
  by (induction rule: rtranclp_induct) (auto simp: restr_def intro: rtranclp.rtrancl_into_rtrancl)

lemma confluent_restr:
  assumes pres: "\<And>x y. R x y \<Longrightarrow> P x \<Longrightarrow> P y" and "confluent R"
  shows "confluent (restr P R)"
  unfolding diamond_def commute_def square_def
proof (intro allI impI)
  fix x y z assume xy: "(restr P R)\<^sup>*\<^sup>* x y" and xz: "(restr P R)\<^sup>*\<^sup>* x z"
  show "\<exists>u. (restr P R)\<^sup>*\<^sup>* y u \<and> (restr P R)\<^sup>*\<^sup>* z u"
  proof (cases "P x")
    case True
    with xy xz pres have "R\<^sup>*\<^sup>* x y" "R\<^sup>*\<^sup>* x z" by (simp_all add: restr_rtrancl)
    with \<open>confluent R\<close> obtain u where "R\<^sup>*\<^sup>* y u" "R\<^sup>*\<^sup>* z u"
      unfolding diamond_def commute_def square_def by blast
    moreover have "P y" "P z" using \<open>R\<^sup>*\<^sup>* x y\<close> \<open>R\<^sup>*\<^sup>* x z\<close> True
      by (auto intro: restr_rtrancl_preserves[OF pres])
    ultimately show ?thesis using pres by (auto simp: restr_rtrancl)
  next
    case False
    have "y = x" using xy False by (cases rule: converse_rtranclpE) (auto simp: restr_def)
    moreover have "z = x" using xz False by (cases rule: converse_rtranclpE) (auto simp: restr_def)
    ultimately show ?thesis by blast
  qed
qed

lemma restr_sup: "restr P (sup R S) = sup (restr P R) (restr P S)"
  by (auto simp: restr_def fun_eq_iff)


subsection \<open>\<open>\<alpha>\<close>-steps\<close>

text \<open>An \<open>\<alpha>\<close>-step renames a bound variable.\<close>

inductive alpha :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<alpha>\<close> 50) where
  rename [simp, intro!]: "Abs a T t \<rightarrow>\<^sub>\<alpha> Abs b T t"
| appL [simp, intro!]: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> s $ u \<rightarrow>\<^sub>\<alpha> t $ u"
| appR [simp, intro!]: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> u $ s \<rightarrow>\<^sub>\<alpha> u $ t"
| abs [simp, intro!]: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> Abs a T s \<rightarrow>\<^sub>\<alpha> Abs a T t"

lemma unname_alpha: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> unname s = unname t"
  by (induction set: alpha) auto

lemma alpha_sym: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> t \<rightarrow>\<^sub>\<alpha> s"
  by (induction set: alpha) auto

lemma rtrancl_alpha_Abs: "alpha\<^sup>*\<^sup>* s s' \<Longrightarrow> alpha\<^sup>*\<^sup>* (Abs a T s) (Abs a T s')"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma rtrancl_alpha_App: "alpha\<^sup>*\<^sup>* s s' \<Longrightarrow> alpha\<^sup>*\<^sup>* t t' \<Longrightarrow> alpha\<^sup>*\<^sup>* (s $ t) (s' $ t')"
proof -
  have L: "alpha\<^sup>*\<^sup>* s s' \<Longrightarrow> alpha\<^sup>*\<^sup>* (s $ t) (s' $ t)" for s s' t
    by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)
  have R: "alpha\<^sup>*\<^sup>* t t' \<Longrightarrow> alpha\<^sup>*\<^sup>* (s $ t) (s $ t')" for s t t'
    by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)
  show "alpha\<^sup>*\<^sup>* s s' \<Longrightarrow> alpha\<^sup>*\<^sup>* t t' \<Longrightarrow> alpha\<^sup>*\<^sup>* (s $ t) (s' $ t')"
    using L R by (meson rtranclp_trans)
qed

lemma alpha_unname: "alpha\<^sup>*\<^sup>* t (unname t)"
proof (induction t)
  case (Abs a T t)
  then have "alpha\<^sup>*\<^sup>* (Abs a T t) (Abs a T (unname t))" by (rule rtrancl_alpha_Abs)
  then show ?case by (simp add: rtranclp.rtrancl_into_rtrancl)
qed (auto intro: rtrancl_alpha_App)


subsection \<open>Type instantiation\<close>

text \<open>
  Instantiating type variables (\<open>\<rho>\<close> maps schematic type variables to types) acts on the labels
  and atoms only, so it commutes with lifting, substitution, \<open>\<alpha>\<close>, \<open>\<beta>\<close> and \<open>\<eta>\<close>.
\<close>

fun tinst :: "(indexname \<Rightarrow> psort \<Rightarrow> ptyp) \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "tinst \<rho> (Type c Ts) = Type c (map (tinst \<rho>) Ts)"
| "tinst \<rho> (TFree a S) = TFree a S"
| "tinst \<rho> (TVar x S) = \<rho> x S"

fun inst :: "(indexname \<Rightarrow> psort \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "inst \<rho> (Const c T) = Const c (tinst \<rho> T)"
| "inst \<rho> (Free x T) = Free x (tinst \<rho> T)"
| "inst \<rho> (Var x T) = Var x (tinst \<rho> T)"
| "inst \<rho> (Bound i) = Bound i"
| "inst \<rho> (Abs a T t) = Abs a (tinst \<rho> T) (inst \<rho> t)"
| "inst \<rho> (s $ t) = inst \<rho> s $ inst \<rho> t"

lemma inst_lift [simp]: "inst \<rho> (incr_bv n k t) = incr_bv n k (inst \<rho> t)"
  by (induction n k t rule: incr_bv.induct) auto

lemma inst_subst [simp]: "inst \<rho> (t[s/k]) = (inst \<rho> t)[inst \<rho> s/k]"
  by (induction t arbitrary: s k) (auto simp: subst_Bound)

lemma loose_bvar1_inst [simp]: "loose_bvar1 (inst \<rho> t) k = loose_bvar1 t k"
  by (induction t arbitrary: k) auto

lemma beta_inst: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> inst \<rho> s \<rightarrow>\<^sub>\<beta> inst \<rho> t"
  by (induction rule: beta.induct) auto

lemma eta_inst: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> inst \<rho> s \<rightarrow>\<^sub>\<eta> inst \<rho> t"
  by (induction rule: eta.induct) auto

lemma beta_eta_inst: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (inst \<rho> s) (inst \<rho> t)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl beta_inst eta_inst)

lemma alpha_inst: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> inst \<rho> s \<rightarrow>\<^sub>\<alpha> inst \<rho> t"
  by (induction set: alpha) auto


subsection \<open>Environments of bound variables\<close>

text \<open>The types of the loose bound variables, as in \<^file>\<open>~~/src/HOL/Proofs/Lambda/LambdaType.thy\<close>.\<close>

definition shift :: "(integer \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> ptyp \<Rightarrow> integer \<Rightarrow> ptyp"  (\<open>_\<langle>_:_\<rangle>\<close> [90, 0, 0] 91) where
  "e\<langle>i:a\<rangle> = (\<lambda>j. if j < i then e j else if j = i then a else e (j - 1))"

lemma shift_eq [simp]: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "0 \<le> i \<Longrightarrow> e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>i + 1:U\<rangle>"
  by (rule ext) (simp add: shift_def integer_arith)

lemma tinst_shift: "(\<lambda>j. tinst \<rho> ((e\<langle>i:T\<rangle>) j)) = (\<lambda>j. tinst \<rho> (e j))\<langle>i:tinst \<rho> T\<rangle>"
  by (rule ext) (simp add: shift_def)

end
