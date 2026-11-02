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


subsection \<open>Typing\<close>

text \<open>
  Church-style typing of Pure terms, following \<^file>\<open>~~/src/HOL/Proofs/Lambda/LambdaType.thy\<close>.
  The environment \<open>e\<close> gives the types of the bound variables; the atoms carry their types.
\<close>

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

inductive typing :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool"  (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50) where
  Const [intro!]: "e \<turnstile> Const c T : T"
| Free [intro!]: "e \<turnstile> Free x T : T"
| Var [intro!]: "e \<turnstile> Var x T : T"
| Bound [intro!]: "0 \<le> i \<Longrightarrow> e i = T \<Longrightarrow> e \<turnstile> Bound i : T"
| Abs [intro!]: "e\<langle>0:T\<rangle> \<turnstile> t : U \<Longrightarrow> e \<turnstile> Abs a T t : T \<rightarrow>\<^sub>T U"
| App [intro!]: "e \<turnstile> s : T \<rightarrow>\<^sub>T U \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> s $ t : U"

inductive_cases typing_elims [elim!]:
  "e \<turnstile> Bound i : T"
  "e \<turnstile> Const c U : T"
  "e \<turnstile> Free x U : T"
  "e \<turnstile> Var x U : T"
  "e \<turnstile> s $ t : T"
  "e \<turnstile> Abs a U t : T"

lemma lift_type [intro!]: "e \<turnstile> t : T \<Longrightarrow> 0 \<le> i \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> lift t i : T"
proof (induction arbitrary: i U set: typing)
  case (Bound e j T)
  then show ?case by (auto simp: integer_arith)
next
  case (Abs e T t U' a)
  then show ?case using Abs.IH[of "i + 1" U] by auto
qed auto

lemma subst_lemma:
  "e \<turnstile> t : T \<Longrightarrow> e' \<turnstile> u : U \<Longrightarrow> e = e'\<langle>i:U\<rangle> \<Longrightarrow> 0 \<le> i \<Longrightarrow> e' \<turnstile> t[u/i] : T"
proof (induction arbitrary: e' i U u set: typing)
  case (Bound e j T)
  then show ?case by (cases j i rule: linorder_cases) auto
next
  case (Abs e T t U' a)
  have "e'\<langle>0:T\<rangle> \<turnstile> lift u 0 : U" using Abs.prems by auto
  then show ?case
    using Abs.IH[where e' = "e'\<langle>0:T\<rangle>" and i = "i + 1" and u = "lift u 0" and U = U] Abs.prems
    by auto
next
  case (App e s T U' t)
  then show ?case by (auto intro!: typing.App)
qed auto

lemma subject_reduction_beta: "e \<turnstile> t : T \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> e \<turnstile> t' : T"
proof (induction arbitrary: t' set: typing)
  case (App e s T U t)
  from App.prems show ?case
  proof cases
    case (beta a T' r)
    with App.hyps show ?thesis by (auto intro: subst_lemma)
  qed (use App in auto)
qed auto

lemma strengthening:
  "e \<turnstile> s : T \<Longrightarrow> e = e'\<langle>i:U\<rangle> \<Longrightarrow> \<not> loose_bvar1 s i \<Longrightarrow> 0 \<le> i \<Longrightarrow> e' \<turnstile> s[d/i] : T"
proof (induction arbitrary: e' i d set: typing)
  case (Bound e j T)
  then show ?case by (cases j i rule: linorder_cases) auto
next
  case (Abs e T t U' a)
  then show ?case by (auto intro!: Abs.IH[of "e'\<langle>0:T\<rangle>" "i + 1"])
qed auto

lemma subject_reduction_eta: "t \<rightarrow>\<^sub>\<eta> t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
proof (induction arbitrary: e T set: eta)
  case (eta s a U d)
  then show ?case by (auto intro: strengthening)
qed auto


subsection \<open>Confluence of \<open>\<beta>\<eta>\<close> for well-typed terms\<close>

text \<open>
  The names of bound variables are irrelevant: \<open>unname\<close> replaces them by the empty name,
  giving a canonical representative of the \<open>\<alpha>\<close>-equivalence class (\<^const>\<open>aconv_term\<close>).
  On well-typed terms whose bound variables have the empty name, \<open>\<beta>\<close> and \<open>\<eta>\<close> commute: in the
  critical pair \<open>\<lambda>a:T. (\<lambda>b:U. r) a\<close>, typing forces \<open>U = T\<close>, and the names agree.
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

definition typed :: "pterm \<Rightarrow> bool" where
  "typed t \<longleftrightarrow> (\<exists>e T. e \<turnstile> t : T) \<and> unname t = t"

lemma typed_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> typed s \<Longrightarrow> typed t"
  unfolding typed_def by (meson subject_reduction_beta unname_beta_id)

lemma typed_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> typed s \<Longrightarrow> typed t"
  unfolding typed_def by (meson subject_reduction_eta unname_eta_id)

text \<open>Relations restricted to sources with a property that they preserve.\<close>

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

lemma square_beta_eta_restr:
  "square (restr typed beta) (restr typed eta) ((restr typed eta)\<^sup>*\<^sup>*) ((restr typed beta)\<^sup>=\<^sup>=)"
  unfolding square_def
proof (intro allI impI)
  fix x y z assume "restr typed beta x y" "restr typed eta x z"
  then have x: "typed x" "x \<rightarrow>\<^sub>\<beta> y" "x \<rightarrow>\<^sub>\<eta> z" by (simp_all add: restr_def)
  then obtain e T where "e \<turnstile> x : T" "unname x = x" by (auto simp: typed_def)
  with x obtain u where u: "y \<rightarrow>\<^sub>\<eta>\<^sup>* u" "beta\<^sup>=\<^sup>= z u" by (meson square_beta_eta_typed)
  have "typed y" "typed z" using x typed_beta typed_eta by blast+
  then show "\<exists>u. (restr typed eta)\<^sup>*\<^sup>* y u \<and> (restr typed beta)\<^sup>=\<^sup>= z u"
    using u typed_eta by (auto simp: restr_rtrancl restr_def)
qed

lemma restr_sup: "restr P (sup R S) = sup (restr P R) (restr P S)"
  by (auto simp: restr_def fun_eq_iff)

theorem confluent_beta_eta_typed: "confluent (restr typed (sup beta eta))"
  unfolding restr_sup
  by (assumption |
    rule square_rtrancl_reflcl_commute confluent_Un square_beta_eta_restr
      confluent_restr beta_confluent eta_confluent typed_beta typed_eta)+


subsection \<open>Names of bound variables\<close>

lemma typing_unname: "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> unname t : T"
  by (induction set: typing) auto

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

lemma confluent_typed:
  assumes "typed x" "(sup beta eta)\<^sup>*\<^sup>* x y" "(sup beta eta)\<^sup>*\<^sup>* x z"
  shows "\<exists>w. (sup beta eta)\<^sup>*\<^sup>* y w \<and> (sup beta eta)\<^sup>*\<^sup>* z w"
proof -
  have pres: "\<And>x y. sup beta eta x y \<Longrightarrow> typed x \<Longrightarrow> typed y"
    using typed_beta typed_eta by blast
  have "(restr typed (sup beta eta))\<^sup>*\<^sup>* x y" "(restr typed (sup beta eta))\<^sup>*\<^sup>* x z"
    using assms restr_rtrancl[where R = "sup beta eta" and P = typed, OF pres] by simp_all
  then obtain w where "(restr typed (sup beta eta))\<^sup>*\<^sup>* y w" "(restr typed (sup beta eta))\<^sup>*\<^sup>* z w"
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
  have x: "typed (unname x)" using assms(1) by (auto simp: typed_def intro: typing_unname)
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
  An \<open>\<alpha>\<close>-step renames a bound variable. \<open>\<alpha>\<beta>\<eta>\<close>-equivalence is the equivalence closure of
  \<open>\<alpha>\<close>-steps and of \<open>\<beta>\<close>- and \<open>\<eta>\<close>-steps from well-typed terms.
\<close>

inductive alpha :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<alpha>\<close> 50) where
  rename [simp, intro!]: "Abs a T t \<rightarrow>\<^sub>\<alpha> Abs b T t"
| appL [simp, intro!]: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> s $ u \<rightarrow>\<^sub>\<alpha> t $ u"
| appR [simp, intro!]: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> u $ s \<rightarrow>\<^sub>\<alpha> u $ t"
| abs [simp, intro!]: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> Abs a T s \<rightarrow>\<^sub>\<alpha> Abs a T t"

definition wt :: "pterm \<Rightarrow> bool" where
  "wt t \<longleftrightarrow> (\<exists>e T. e \<turnstile> t : T)"

definition conv_step :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "conv_step s t \<longleftrightarrow> s \<rightarrow>\<^sub>\<alpha> t \<or> wt s \<and> (s \<rightarrow>\<^sub>\<beta> t \<or> s \<rightarrow>\<^sub>\<eta> t)"

definition conv :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infix \<open>\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>\<close> 50) where
  "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<longleftrightarrow> equivclp conv_step s t"

lemma unname_alpha: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> unname s = unname t"
  by (induction set: alpha) auto

lemma alpha_sym: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> t \<rightarrow>\<^sub>\<alpha> s"
  by (induction set: alpha) auto

lemma typing_alpha: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (induction arbitrary: e T set: alpha) auto

lemma wt_conv_step: "conv_step s t \<Longrightarrow> wt s \<longleftrightarrow> wt t"
  unfolding conv_step_def wt_def
  by (metis alpha_sym typing_alpha subject_reduction_beta subject_reduction_eta)

lemma wt_conv: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> wt s \<longleftrightarrow> wt t"
  unfolding conv_def by (induction rule: equivclp_induct) (auto dest: wt_conv_step)

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

lemma typing_unname_iff: "e \<turnstile> unname t : T \<longleftrightarrow> e \<turnstile> t : T"
  by (induction t arbitrary: e T) auto

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
    have ty: "typed (unname y)"
      using \<open>wt y\<close> by (auto simp: wt_def typed_def intro: typing_unname)
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


subsection \<open>Type instantiation\<close>

text \<open>
  Instantiating type variables (\<open>\<rho>\<close> maps schematic type variables to types) acts on the labels
  and atoms only, so it commutes with lifting, substitution, \<open>\<beta>\<close> and \<open>\<eta>\<close>.
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

lemma tinst_shift: "(\<lambda>j. tinst \<rho> ((e\<langle>i:T\<rangle>) j)) = (\<lambda>j. tinst \<rho> (e j))\<langle>i:tinst \<rho> T\<rangle>"
  by (rule ext) (simp add: shift_def)

lemma typing_inst: "e \<turnstile> t : T \<Longrightarrow> (\<lambda>j. tinst \<rho> (e j)) \<turnstile> inst \<rho> t : tinst \<rho> T"
proof (induction set: typing)
  case (Abs e T t U a)
  then show ?case by (auto simp: tinst_shift)
qed auto

lemma alpha_inst: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> inst \<rho> s \<rightarrow>\<^sub>\<alpha> inst \<rho> t"
  by (induction set: alpha) auto

lemma conv_inst: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> inst \<rho> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> inst \<rho> t"
proof -
  have step: "conv_step s t \<Longrightarrow> conv_step (inst \<rho> s) (inst \<rho> t)" for s t
    unfolding conv_step_def wt_def
    by (meson alpha_inst beta_inst eta_inst typing_inst)
  show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> inst \<rho> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> inst \<rho> t"
    unfolding conv_def by (induction rule: equivclp_induct) (auto intro: equivclp_into_equivclp step)
qed

end
