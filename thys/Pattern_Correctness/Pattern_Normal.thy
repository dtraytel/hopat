section \<open>Renaming and Normal Forms\<close>

theory Pattern_Normal
  imports Pattern_Sound
begin

text \<open>
  Completeness reasons about normal forms of solutions applied to distinct bound variables.
  Renaming bound variables commutes with \<open>\<beta>\<close>, \<open>\<eta>\<close> and \<open>\<alpha>\<close>, and keeps terms normal.
\<close>

subsection \<open>Renaming\<close>

lemma nonnegD: "nonneg f \<Longrightarrow> 0 \<le> k \<Longrightarrow> 0 \<le> f k"
  by (simp add: nonneg_def)

lemma rename_comp: "nonneg g \<Longrightarrow> rename f d (rename g d t) = rename (\<lambda>k. f (g k)) d t"
proof (induction g d t rule: rename.induct)
  case (1 g d i)
  show ?case
  proof (cases "i < d")
    case False
    then have "0 \<le> g (i - d)" by (intro nonnegD[OF 1]) simp
    with False show ?thesis by simp
  qed simp
qed simp_all

lemma rename_cong:
  "(\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t (k + d) \<Longrightarrow> f k = g k) \<Longrightarrow> rename f d t = rename g d t"
proof (induction t arbitrary: d)
  case (Bound i)
  then show ?case using Bound[of "i - d"] by (auto simp: integer_arith)
next
  case (Abs a T t)
  then show ?case using Abs.IH[of "d + 1"] by (simp add: algebra_simps)
qed auto

lemma loose_bvar1_rename:
  "nonneg f \<Longrightarrow> loose_bvar1 (rename f d t) j \<longleftrightarrow>
    (j < d \<and> loose_bvar1 t j) \<or> (\<exists>k\<ge>0. loose_bvar1 t (k + d) \<and> j = f k + d)"
proof (induction t arbitrary: d j)
  case (Bound i)
  show ?case
  proof (cases "i < d")
    case False
    then have f0: "0 \<le> f (i - d)" by (intro nonnegD[OF Bound]) simp
    have ex: "(\<exists>k\<ge>0. loose_bvar1 (Bound i) (k + d) \<and> j = f k + d) \<longleftrightarrow> j = f (i - d) + d"
    proof
      assume "\<exists>k\<ge>0. loose_bvar1 (Bound i) (k + d) \<and> j = f k + d"
      then obtain k where "i = k + d" "j = f k + d" by auto
      then show "j = f (i - d) + d" by simp
    next
      assume "j = f (i - d) + d"
      with False show "\<exists>k\<ge>0. loose_bvar1 (Bound i) (k + d) \<and> j = f k + d"
        by (intro exI[of _ "i - d"]) simp
    qed
    from False f0 have "\<not> (j < d \<and> i = j)" by auto
    with False ex show ?thesis by (auto simp: eq_commute[of j])
  qed auto
next
  case (Abs a T t)
  from Abs.IH[OF Abs.prems, of "d + 1" "j + 1"] show ?case by (simp add: algebra_simps)
next
  case (App s u)
  from App.IH(1)[OF App.prems, of d j] App.IH(2)[OF App.prems, of d j] show ?case by auto
qed auto

lemma rename_lift:
  "0 \<le> j \<Longrightarrow> j \<le> d \<Longrightarrow> nonneg f \<Longrightarrow> lift (rename f d u) j = rename f (d + 1) (lift u j)"
proof (induction u arbitrary: j d)
  case (Bound i)
  show ?case
  proof (cases "i < d")
    case False
    then have f0: "0 \<le> f (i - d)" by (intro nonnegD[OF Bound.prems(3)]) simp
    have "j \<le> f (i - d) + d" using f0 Bound.prems(2) by (simp add: integer_arith)
    moreover have "\<not> i + 1 < d + 1" using False by simp
    ultimately show ?thesis using False Bound.prems by (simp add: algebra_simps)
  qed (use Bound.prems in \<open>auto simp: integer_arith\<close>)
next
  case (Abs a T u)
  then show ?case using Abs.IH[of "j + 1" "d + 1"] by (simp add: integer_arith algebra_simps)
qed auto

lemma rename_subst:
  "0 \<le> j \<Longrightarrow> j \<le> d \<Longrightarrow> nonneg f \<Longrightarrow> (rename f (d + 1) s)[rename f d u / j] = rename f d (s[u/j])"
proof (induction s arbitrary: j d u)
  case (Bound i)
  consider "i < j" | "i = j" | "j < i" "i \<le> d" | "d < i" by fastforce
  then show ?case
  proof cases
    case 4
    then have f0: "0 \<le> f (i - (d + 1))" by (intro nonnegD[OF Bound.prems(3)]) (simp add: integer_arith)
    have "j < f (i - (d + 1)) + (d + 1)" using f0 Bound.prems(2) by (simp add: integer_arith)
    moreover have "\<not> i < d + 1" "\<not> i - 1 < d" using 4 by (simp_all add: integer_arith)
    ultimately show ?thesis using 4 Bound.prems by (simp add: subst_Bound algebra_simps)
  qed (use Bound.prems in \<open>auto simp: subst_Bound integer_arith\<close>)
next
  case (Abs a T s)
  have "lift (rename f d u) 0 = rename f (d + 1) (lift u 0)"
    using Abs.prems by (intro rename_lift) simp_all
  with Abs.prems Abs.IH[of "j + 1" "d + 1" "lift u 0"] show ?case
    by (simp add: integer_arith algebra_simps)
qed auto

lemma beta_rename: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> rename f d s \<rightarrow>\<^sub>\<beta> rename f d t"
proof (induction arbitrary: d set: beta)
  case (beta a T s t)
  then show ?case using rename_subst[of 0 d f s t] beta.beta[of a T "rename f (d + 1) s" "rename f d t"]
    by simp
next
  case (abs s t a T)
  then show ?case by (simp add: integer_arith)
qed simp_all

lemma eta_rename: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> rename f d s \<rightarrow>\<^sub>\<eta> rename f d t"
proof (induction arbitrary: d set: eta)
  case (eta s a T dummy)
  have "f k + (d + 1) \<noteq> 0" if "0 \<le> k" for k
    using nonnegD[OF eta.prems(1) that] eta.prems(2) by (simp add: integer_arith)
  then have nf: "\<not> loose_bvar1 (rename f (d + 1) s) 0"
    using eta loose_bvar1_rename[of f "d + 1" s 0] eta.prems(2) by (auto simp: integer_arith)
  have "rename f d (Abs a T (s $ Bound 0)) = Abs a T (rename f (d + 1) s $ Bound 0)"
    using eta.prems by (simp add: integer_arith)
  also have "\<dots> \<rightarrow>\<^sub>\<eta> (rename f (d + 1) s)[rename f d dummy/0]" using nf by (rule eta.eta)
  also have "(rename f (d + 1) s)[rename f d dummy/0] = rename f d (s[dummy/0])"
    using eta.prems by (intro rename_subst) simp_all
  finally show ?case .
next
  case (abs s t a T)
  then show ?case by (simp add: integer_arith)
qed simp_all

lemma alpha_rename: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> rename f d s \<rightarrow>\<^sub>\<alpha> rename f d t"
  by (induction arbitrary: d set: alpha) auto

lemma reds_rename:
  "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (rename f d s) (rename f d t)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl beta_rename eta_rename)

lemma aconv_rename: "aconv_term u v \<Longrightarrow> aconv_term (rename f d u) (rename f d v)"
  by (induction u v arbitrary: d rule: aconv_term.induct) (auto split: if_splits)

lemma aconv_rename_agree:
  "aconv_term (rename f d t) (rename g d t) \<Longrightarrow> nonneg f \<Longrightarrow> nonneg g \<Longrightarrow>
    0 \<le> k \<Longrightarrow> loose_bvar1 t (k + d) \<Longrightarrow> f k = g k"
proof (induction t arbitrary: d)
  case (Bound i)
  from Bound.prems(5) have i: "i = k + d" by simp
  with Bound.prems show ?case by (simp split: if_splits)
next
  case (Abs a T t)
  then show ?case using Abs.IH[of "d + 1"] by (simp add: algebra_simps)
qed auto


subsection \<open>Normal terms\<close>

fun eta_free :: "pterm \<Rightarrow> bool" where
  "eta_free (Abs a T t) \<longleftrightarrow> eta_free t \<and> \<not> (\<exists>s. t = s $ Bound 0 \<and> \<not> loose_bvar1 s 0)"
| "eta_free (s $ t) \<longleftrightarrow> eta_free s \<and> eta_free t"
| "eta_free _ \<longleftrightarrow> True"

lemma eta_free_iff: "eta_free t \<longleftrightarrow> \<not> (\<exists>u. t \<rightarrow>\<^sub>\<eta> u)"
proof (induction t)
  case (Abs a T t)
  then show ?case by (auto elim: eta.cases)
next
  case (App s t)
  then show ?case by (auto elim: eta.cases)
qed (auto elim: eta.cases)

lemma normal_iff: "normal t \<longleftrightarrow> no_redex t \<and> eta_free t"
  by (auto simp: normal_def no_redex_iff eta_free_iff)

lemma is_Abs_rename [simp]: "is_Abs (rename f d t) \<longleftrightarrow> is_Abs t"
  by (cases t) auto

lemma no_redex_rename [simp]: "no_redex (rename f d t) \<longleftrightarrow> no_redex t"
  by (induction f d t rule: rename.induct) auto

lemma rename_Bound0: "nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> rename f (d + 1) u = Bound 0 \<longleftrightarrow> u = Bound 0"
proof (cases u)
  case (Bound i)
  assume f: "nonneg f" and d: "0 \<le> d"
  show ?thesis
  proof (cases "i < d + 1")
    case False
    then have "0 \<le> f (i - (d + 1))" by (intro nonnegD[OF f]) (simp add: integer_arith)
    then have "f (i - (d + 1)) + (d + 1) \<noteq> 0" using d by (simp add: integer_arith)
    with False Bound show ?thesis using d by (auto simp: integer_arith)
  qed (use Bound in auto)
qed auto

lemma eta_free_rename: "nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> eta_free (rename f d t) \<longleftrightarrow> eta_free t"
proof (induction t arbitrary: d)
  case (Abs a T t)
  have "(\<exists>s. rename f (d + 1) t = s $ Bound 0 \<and> \<not> loose_bvar1 s 0) \<longleftrightarrow>
      (\<exists>s. t = s $ Bound 0 \<and> \<not> loose_bvar1 s 0)"
  proof
    assume "\<exists>s. rename f (d + 1) t = s $ Bound 0 \<and> \<not> loose_bvar1 s 0"
    then obtain s u where t: "t = s $ u" and "rename f (d + 1) u = Bound 0"
      "\<not> loose_bvar1 (rename f (d + 1) s) 0"
      by (cases t) auto
    with Abs.prems rename_Bound0[of f d u] loose_bvar1_rename[of f "d + 1" s 0] show
      "\<exists>s. t = s $ Bound 0 \<and> \<not> loose_bvar1 s 0"
      by (auto simp: integer_arith)
  next
    assume "\<exists>s. t = s $ Bound 0 \<and> \<not> loose_bvar1 s 0"
    then obtain s where t: "t = s $ Bound 0" "\<not> loose_bvar1 s 0" by blast
    have "f k + (d + 1) \<noteq> 0" if "0 \<le> k" for k
      using nonnegD[OF Abs.prems(1) that] Abs.prems(2) by (simp add: integer_arith)
    with t Abs.prems loose_bvar1_rename[of f "d + 1" s 0] show
      "\<exists>s. rename f (d + 1) t = s $ Bound 0 \<and> \<not> loose_bvar1 s 0"
      by (auto simp: integer_arith)
  qed
  with Abs.IH[of "d + 1"] Abs.prems show ?case by (simp add: integer_arith)
qed auto

lemma normal_rename: "nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> normal (rename f d t) \<longleftrightarrow> normal t"
  by (simp add: normal_iff eta_free_rename)


subsection \<open>Bound variables of iterated abstractions\<close>

text \<open>\<open>downs n = [n - 1, \<dots>, 0]\<close> are the bound variables of an \<open>n\<close>-fold abstraction, outermost
  first.\<close>

fun downs :: "nat \<Rightarrow> integer list" where
  "downs 0 = []"
| "downs (Suc n) = integer_of_nat n # downs n"

lemma length_downs [simp]: "length (downs n) = n"
  by (induction n) auto

lemma set_downs: "set (downs n) = {k. 0 \<le> k \<and> k < integer_of_nat n}"
proof (induction n)
  case (Suc n)
  have "k < integer_of_nat (Suc n) \<longleftrightarrow> k < integer_of_nat n \<or> k = integer_of_nat n" for k
    by (simp add: integer_reps) arith
  moreover have "0 \<le> integer_of_nat n" by (simp add: integer_reps)
  ultimately show ?case using Suc.IH by auto
qed (simp add: integer_reps)

lemma downs_Suc_snoc: "downs (Suc n) = map (\<lambda>k. k + 1) (downs n) @ [0]"
proof -
  have "map (\<lambda>k. k + 1) (downs n) @ [0] = downs (Suc n)"
    by (induction n) (simp_all add: integer_reps)
  then show ?thesis by simp
qed

lemma map_nth_rev_downs: "map (\<lambda>k. rev xs ! nat_of_integer k) (downs (length xs)) = xs"
proof (induction xs)
  case (Cons x xs)
  have "rev (x # xs) ! nat_of_integer k = rev xs ! nat_of_integer k" if "k \<in> set (downs (length xs))" for k
  proof -
    from that have "nat_of_integer k < length xs" by (simp add: set_downs integer_reps nat_less_iff)
    then show ?thesis by (simp add: nth_append)
  qed
  then have "map (\<lambda>k. rev (x # xs) ! nat_of_integer k) (downs (length xs)) =
      map (\<lambda>k. rev xs ! nat_of_integer k) (downs (length xs))"
    by (rule map_cong[OF refl])
  with Cons.IH have "map (\<lambda>k. rev (x # xs) ! nat_of_integer k) (downs (length xs)) = xs" by simp
  then show ?case by (simp add: nth_append)
qed simp

lemma map_bren_downs: "map (bren (rev xs)) (downs (length xs)) = xs"
proof -
  have "bren (rev xs) k = rev xs ! nat_of_integer k" if "k \<in> set (downs (length xs))" for k
    using that by (intro bren_nth) (simp_all add: set_downs ilength_eq)
  then have "map (bren (rev xs)) (downs (length xs)) = map (\<lambda>k. rev xs ! nat_of_integer k) (downs (length xs))"
    by (rule map_cong[OF refl])
  then show ?thesis by (simp only: map_nth_rev_downs)
qed

lemma loose_bvar_Bounds_downs: "\<not> loose_bvar (u \<degree>\<degree> map Bound (downs n)) (integer_of_nat n) \<longleftrightarrow> \<not> loose_bvar u (integer_of_nat n)"
  by (auto simp: loose_bvar_apps set_downs)

context pure_sig
begin

lemma rtrancl_eta_abs_list: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> abs_list bs s \<rightarrow>\<^sub>\<eta>\<^sup>* abs_list bs t"
  by (induction bs) (auto intro: rtrancl_eta_Abs)

lemma reds_abs_list: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (abs_list bs s) (abs_list bs t)"
  by (induction bs) (auto intro: rtrancl_beta_eta_Abs)

lemma incr_bv_apps: "incr_bv n k (s \<degree>\<degree> ts) = incr_bv n k s \<degree>\<degree> map (incr_bv n k) ts"
  by (induction ts arbitrary: s) auto

lemma incr_bv_closed: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> incr_bv n k t = t"
  by (simp add: incr_bv_no_loose closed_loose_bvar)

text \<open>\<open>\<eta>\<close>-expansion of a closed term:\<close>

lemma eta_abs_list_downs: "closed u \<Longrightarrow> abs_list bs (u \<degree>\<degree> map Bound (downs (length bs))) \<rightarrow>\<^sub>\<eta>\<^sup>* u"
proof (induction bs rule: rev_induct)
  case (snoc b bs)
  obtain x T where b: "b = (x, T)" by force
  have "u \<degree>\<degree> map Bound (downs (Suc (length bs))) = lift (u \<degree>\<degree> map Bound (downs (length bs))) 0 $ Bound 0"
  proof -
    have "map (\<lambda>k. lift (Bound k) 0) (downs (length bs)) = map Bound (map (\<lambda>k. k + 1) (downs (length bs)))"
      by (auto simp: set_downs)
    moreover have "lift (u \<degree>\<degree> map Bound (downs (length bs))) 0 = u \<degree>\<degree> map (\<lambda>k. lift (Bound k) 0) (downs (length bs))"
      using snoc.prems by (simp add: incr_bv_apps incr_bv_closed o_def)
    ultimately show ?thesis by (simp only: downs_Suc_snoc map_append) simp
  qed
  then have "abs_list (bs @ [b]) (u \<degree>\<degree> map Bound (downs (length (bs @ [b])))) =
      abs_list bs (Abs x T (lift (u \<degree>\<degree> map Bound (downs (length bs))) 0 $ Bound 0))"
    by (simp add: b)
  also have "\<dots> \<rightarrow>\<^sub>\<eta>\<^sup>* abs_list bs (u \<degree>\<degree> map Bound (downs (length bs)))"
    by (intro rtrancl_eta_abs_list r_into_rtranclp eta_lift)
  also have "\<dots> \<rightarrow>\<^sub>\<eta>\<^sup>* u" using snoc.IH snoc.prems .
  finally show ?case .
qed simp

lemma conv_rename:
  assumes "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" "wt s" "wt (rename f d s)" "wt (rename f d t)" "nonneg f" "0 \<le> d"
  shows "rename f d s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename f d t"
proof -
  obtain u v where uv: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* t v" "aconv_term u v"
    using church_rosser[OF assms(2,1)] by blast
  have "rename f d s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename f d u"
    using reds_rename[OF uv(1) assms(5,6)] assms(3) by (rule beta_eta_conv)
  also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename f d v" using aconv_rename[OF uv(3)] by (rule aconv_term_conv)
  also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename f d t"
    using reds_rename[OF uv(2) assms(5,6)] assms(4) by (blast intro: beta_eta_conv conv_sym)
  finally show ?thesis .
qed

lemma conv_normal_aconv:
  assumes "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" "wt s" "normal s" "normal t"
  shows "aconv_term s t"
proof -
  obtain u v where uv: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* t v" "aconv_term u v"
    using church_rosser[OF assms(2,1)] by blast
  with normal_reds[OF uv(1) assms(3)] normal_reds[OF uv(2) assms(4)] show ?thesis by simp
qed

subsection \<open>Loose bound variables under reduction\<close>

lemma loose_bvar_iff: "loose_bvar t k \<longleftrightarrow> (\<exists>j\<ge>k. loose_bvar1 t j)"
proof (induction t arbitrary: k)
  case (Abs a T t)
  have "(\<exists>j\<ge>k + 1. loose_bvar1 t j) \<longleftrightarrow> (\<exists>j\<ge>k. loose_bvar1 t (j + 1))"
  proof
    assume "\<exists>j\<ge>k + 1. loose_bvar1 t j"
    then obtain j where "j \<ge> k + 1" "loose_bvar1 t j" by blast
    then show "\<exists>j\<ge>k. loose_bvar1 t (j + 1)" by (intro exI[of _ "j - 1"]) simp
  next
    assume "\<exists>j\<ge>k. loose_bvar1 t (j + 1)"
    then obtain j where "j \<ge> k" "loose_bvar1 t (j + 1)" by blast
    then show "\<exists>j\<ge>k + 1. loose_bvar1 t j" by (intro exI[of _ "j + 1"]) simp
  qed
  with Abs.IH show ?case by simp
qed auto

lemma loose_bvar_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar t k \<Longrightarrow> loose_bvar s k"
  unfolding loose_bvar_iff by (meson free_beta order_trans)

lemma loose_bvar_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar t k \<Longrightarrow> loose_bvar s k"
  unfolding loose_bvar_iff by (meson free_eta order_trans)

lemma loose_bvar_reds: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar t k \<Longrightarrow> loose_bvar s k"
  by (induction rule: rtranclp_induct) (auto dest: loose_bvar_beta loose_bvar_eta)


lemma loose_bvar1_apps: "loose_bvar1 (s \<degree>\<degree> ts) k \<longleftrightarrow> loose_bvar1 s k \<or> (\<exists>t\<in>set ts. loose_bvar1 t k)"
  by (induction ts arbitrary: s) auto

lemma subject_reduction_reds: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (induction rule: rtranclp_induct) (auto intro: subject_reduction_beta subject_reduction_eta)


subsection \<open>Canonical bodies\<close>

text \<open>
  A closed term \<open>u\<close> of type \<open>Ts \<Rrightarrow> T\<close> is equivalent to the abstraction of the normal form \<open>B\<close>
  of its application to \<^term>\<open>downs (length Ts)\<close>, and its applications to bound variables
  \<open>xs\<close> reduce to renamings of \<open>B\<close>, which are normal.
\<close>

lemma canonical_body:
  assumes u: "closed u" "e \<turnstile> u : Ts \<Rrightarrow> T"
  obtains B where "normal B" "\<not> loose_bvar B (ilength Ts)" "\<And>e'. pushes e' Ts \<turnstile> B : T"
    "\<And>bs. map snd bs = Ts \<Longrightarrow> \<forall>U\<in>set Ts. cert_typ alg ar U \<Longrightarrow> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B"
    "\<And>xs. length xs = length Ts \<Longrightarrow> \<forall>i\<in>set xs. 0 \<le> i \<Longrightarrow>
      u \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* rename (bren (rev xs)) 0 B"
proof -
  let ?n = "length Ts"
  let ?t = "u \<degree>\<degree> map Bound (downs ?n)"
  have ty: "pushes e Ts \<turnstile> ?t : T"
  proof (rule list_app_typeI)
    show "pushes e Ts \<turnstile> u : Ts \<Rrightarrow> T" using typing_closed u by blast
    have "pushes e Ts k = rev Ts ! nat_of_integer k" if "k \<in> set (downs ?n)" for k
      using that by (simp add: pushes_nth set_downs ilength_eq)
    then have "map (pushes e Ts) (downs ?n) = map (\<lambda>k. rev Ts ! nat_of_integer k) (downs ?n)"
      by (rule map_cong[OF refl])
    then have "map (pushes e Ts) (downs ?n) = Ts" by (simp only: map_nth_rev_downs)
    moreover have "pushes e Ts \<tturnstile> map Bound (downs ?n) : map (pushes e Ts) (downs ?n)"
      by (rule typings_Bounds) (simp add: set_downs)
    ultimately show "pushes e Ts \<tturnstile> map Bound (downs ?n) : Ts" by simp
  qed
  obtain B where B: "?t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* B" "normal B" using normal_form_ex[OF ty] by blast
  show ?thesis
  proof (rule that[OF B(2)])
    fix e' :: "integer \<Rightarrow> ptyp"
    have "pushes e' Ts \<turnstile> ?t : T"
      using ty by (rule typing_env_cong) (simp add: pushes_nth loose_bvar1_apps set_downs ilength_eq
          closed_loose_bvar1[OF u(1)])
    then show "pushes e' Ts \<turnstile> B : T" by (rule subject_reduction_reds[OF B(1)])
  next
    have "\<not> loose_bvar ?t (ilength Ts)"
      using closed_loose_bvar[OF u(1) ilength_nonneg[of Ts]] by (auto simp: loose_bvar_apps set_downs ilength_eq)
    then show "\<not> loose_bvar B (ilength Ts)" using loose_bvar_reds[OF B(1)] by auto
  next
    fix bs :: binders assume bs: "map snd bs = Ts" "\<forall>U\<in>set Ts. cert_typ alg ar U"
    have len: "length bs = ?n" using bs(1) by auto
    have "e \<turnstile> abs_list bs ?t : map snd bs \<Rrightarrow> T"
      by (rule typing_abs_list) (use ty bs in fastforce)+
    then have wt: "wt (abs_list bs ?t)" by (auto simp: wt_def)
    have "abs_list bs ?t \<rightarrow>\<^sub>\<eta>\<^sup>* u" using eta_abs_list_downs[OF u(1), of bs] len by simp
    then have "abs_list bs ?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u" using wt by (blast intro: beta_eta_conv eta_reds_beta_eta_reds)
    moreover have "abs_list bs ?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B" using reds_abs_list[OF B(1)] wt by (rule beta_eta_conv)
    ultimately show "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B" by (blast intro: conv_sym conv_trans)
  next
    fix xs :: "integer list" assume xs: "length xs = ?n" "\<forall>i\<in>set xs. 0 \<le> i"
    have "map (\<lambda>k. rename (bren (rev xs)) 0 (Bound k)) (downs ?n) = map Bound (map (bren (rev xs)) (downs (length xs)))"
      using xs(1) by (auto simp: set_downs)
    then have "rename (bren (rev xs)) 0 ?t = u \<degree>\<degree> map Bound xs"
      using u(1) by (simp add: rename_apps rename_closed map_bren_downs o_def)
    moreover have "nonneg (bren (rev xs))" using xs(2) by (intro nonneg_bren) simp
    ultimately show "u \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* rename (bren (rev xs)) 0 B"
      using reds_rename[OF B(1), of "bren (rev xs)" 0] by simp
  qed
qed

subsection \<open>Positions in lists of bound variables\<close>

text \<open>\<open>bidx xs j\<close> is the bound variable for \<open>j\<close> in the body of an abstraction over \<open>xs\<close>
  (\<^const>\<open>idx\<close> without exceptions).\<close>

fun bidx :: "integer list \<Rightarrow> integer \<Rightarrow> integer" where
  "bidx [] j = 0"
| "bidx (i # is) j = (if i = j then ilength is else bidx is j)"

lemma ok_idx_bidx: "ok (idx xs j) k \<longleftrightarrow> j \<in> set xs \<and> k = bidx xs j"
  by (induction xs) auto

lemma bidx_nonneg [simp]: "0 \<le> bidx xs j"
  by (induction xs) auto

lemma nonneg_bidx: "nonneg (bidx xs)"
  by (simp add: nonneg_def)

lemma bidx_less: "j \<in> set xs \<Longrightarrow> bidx xs j < ilength xs"
  by (induction xs) (auto simp: integer_arith)

lemma bren_bidx: "j \<in> set xs \<Longrightarrow> bren (rev xs) (bidx xs j) = j"
  using ok_idx[of xs j "bidx xs j"] by (simp add: ok_idx_bidx)

lemma bren_rev_in: "0 \<le> p \<Longrightarrow> p < ilength xs \<Longrightarrow> bren (rev xs) p \<in> set xs"
  using nat_of_integer_less_ilength[of p xs] nth_mem[of "nat_of_integer p" "rev xs"] by (simp add: bren_rev)

lemma bidx_bren: "distinct xs \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < ilength xs \<Longrightarrow> bidx xs (bren (rev xs) p) = p"
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "p = ilength xs")
    case True
    then have "bren (rev (x # xs)) p = x"
      using bren_rev[of p "x # xs"] by (simp add: nth_append ilength_eq integer_reps)
    with True show ?thesis by simp
  next
    case False
    then have p: "p < ilength xs" using Cons.prems by (simp add: integer_arith)
    then have "bren (rev (x # xs)) p = bren (rev xs) p"
      using bren_rev[of p "x # xs"] bren_rev[of p xs] Cons.prems(2)
        nat_of_integer_less_ilength[OF Cons.prems(2) p]
      by (simp add: nth_append)
    moreover have "bren (rev xs) p \<noteq> x" using bren_rev_in[OF Cons.prems(2) p] Cons.prems(1) by auto
    ultimately show ?thesis using Cons.IH[OF _ Cons.prems(2) p] Cons.prems(1) by simp
  qed
qed simp


subsection \<open>Strengthening\<close>

lemma beta_reds_abs_list: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> abs_list bs s \<rightarrow>\<^sub>\<beta>\<^sup>* abs_list bs t"
  by (induction bs) auto

definition sabs :: "(integer \<Rightarrow> ptyp) \<Rightarrow> integer list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "sabs e0 ks N = abs_list (map (\<lambda>k. (STR '''', e0 k)) ks) (rename (bidx ks) 0 N)"

text \<open>
  A term \<open>N\<close> whose loose bound variables are among the distinct \<open>ks\<close> is the body of the closed
  term \<^term>\<open>sabs e0 ks N\<close> applied to \<open>ks\<close>; this gives the values of new variables.
\<close>

lemma strengthen:
  assumes N: "e0 \<turnstile> N : T" and lb: "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 N k \<Longrightarrow> k \<in> set ks"
    and ty: "\<forall>k\<in>set ks. cert_typ alg ar (e0 k)"
  shows "closed (sabs e0 ks N)" and "e \<turnstile> sabs e0 ks N : map e0 ks \<Rrightarrow> T"
    and "length ms = length ks \<Longrightarrow> \<forall>m\<in>set ms. 0 \<le> m \<Longrightarrow>
      sabs e0 ks N \<degree>\<degree> map Bound ms \<rightarrow>\<^sub>\<beta>\<^sup>* rename (\<lambda>k. bren (rev ms) (bidx ks k)) 0 N"
proof -
  let ?bs = "map (\<lambda>k. (STR '''', e0 k)) ks"
  have "\<not> loose_bvar (rename (bidx ks) 0 N) (ilength ?bs)"
  proof
    assume "loose_bvar (rename (bidx ks) 0 N) (ilength ?bs)"
    then obtain j where j: "j \<ge> ilength ks" "loose_bvar1 (rename (bidx ks) 0 N) j"
      by (auto simp: loose_bvar_iff)
    have "0 \<le> j" using ilength_nonneg[of ks] j(1) by (rule order_trans)
    then obtain k where "0 \<le> k" "loose_bvar1 N k" "j = bidx ks k"
      using loose_bvar1_rename[OF nonneg_bidx, of ks 0 N j] j(2) by auto
    with lb bidx_less j(1) show False by force
  qed
  then show "closed (sabs e0 ks N)" unfolding sabs_def by (rule closed_abs_list)
  have "renv (pushes e (map e0 ks)) (bidx ks) 0 \<turnstile> N : T"
  proof (rule typing_env_cong[OF N])
    fix k assume k: "0 \<le> k" "loose_bvar1 N k"
    then have kk: "k \<in> set ks" by (rule lb)
    have "pushes e (map e0 ks) (bidx ks k) = rev (map e0 ks) ! nat_of_integer (bidx ks k)"
      using bidx_less[OF kk] by (simp add: pushes_nth)
    also have "\<dots> = e0 (rev ks ! nat_of_integer (bidx ks k))"
      using nat_of_integer_less_ilength[OF bidx_nonneg bidx_less[OF kk]] by (simp add: rev_map)
    also have "\<dots> = e0 k" using bren_bidx[OF kk] bren_rev[OF bidx_nonneg bidx_less[OF kk]] by simp
    finally show "renv (pushes e (map e0 ks)) (bidx ks) 0 k = e0 k" using k by (simp add: renv_def)
  qed
  then have "pushes e (map e0 ks) \<turnstile> rename (bidx ks) 0 N : T"
    by (rule typing_rename[OF _ refl nonneg_bidx]) simp
  then show "e \<turnstile> sabs e0 ks N : map e0 ks \<Rrightarrow> T"
    unfolding sabs_def using typing_abs_list[of e ?bs] ty by (simp add: o_def)
  assume ms: "length ms = length ks" "\<forall>m\<in>set ms. 0 \<le> m"
  have "sabs e0 ks N \<degree>\<degree> map Bound ms \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev ms)) 0 (rename (bidx ks) 0 N)"
    unfolding sabs_def using ms by (intro beta_abs_list_apps) simp_all
  then show "sabs e0 ks N \<degree>\<degree> map Bound ms \<rightarrow>\<^sub>\<beta>\<^sup>* rename (\<lambda>k. bren (rev ms) (bidx ks k)) 0 N"
    by (simp add: rename_comp nonneg_bidx)
qed

lemma rename_bren_bidx:
  "(\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 N k \<Longrightarrow> k \<in> set ks) \<Longrightarrow> rename (\<lambda>k. bren (rev ks) (bidx ks k)) 0 N = N"
proof -
  assume lb: "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 N k \<Longrightarrow> k \<in> set ks"
  have "rename (\<lambda>k. bren (rev ks) (bidx ks k)) 0 N = rename (\<lambda>k. k) 0 N"
    by (rule rename_cong) (simp add: bren_bidx lb)
  then show ?thesis by (simp add: rename_id)
qed

lemma loose_bvar1_less: "\<not> loose_bvar t n \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k < n"
  by (meson loose_bvar1_imp loose_bvar_mono not_le)


subsection \<open>Flex-flex problems with the same head\<close>

text \<open>
  If \<open>u xs\<close> and \<open>u ys\<close> are equivalent, \<open>u\<close> depends only on the arguments where \<open>xs\<close> and \<open>ys\<close>
  agree.
\<close>

lemma flex_same_sem:
  assumes u: "closed u" "e \<turnstile> u : Ts \<Rrightarrow> T"
    and bs: "map snd bs = Ts" "\<forall>U\<in>set Ts. cert_typ alg ar U"
    and xs: "length xs = length Ts" "\<forall>i\<in>set xs. 0 \<le> i"
    and ys: "length ys = length Ts" "\<forall>i\<in>set ys. 0 \<le> i"
    and eq: "u \<degree>\<degree> map Bound xs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u \<degree>\<degree> map Bound ys" "wt (u \<degree>\<degree> map Bound xs)"
    and ks: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength Ts"
      "\<And>k. 0 \<le> k \<Longrightarrow> k < ilength Ts \<Longrightarrow> bren (rev xs) k = bren (rev ys) k \<Longrightarrow> k \<in> set ks"
  obtains w where "closed w" "\<And>e. e \<turnstile> w : map (\<lambda>k. rev Ts ! nat_of_integer k) ks \<Rrightarrow> T"
    "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (w \<degree>\<degree> map Bound ks)"
proof -
  obtain B where B: "normal B" "\<not> loose_bvar B (ilength Ts)" "\<And>e'. pushes e' Ts \<turnstile> B : T"
    "\<And>bs. map snd bs = Ts \<Longrightarrow> \<forall>U\<in>set Ts. cert_typ alg ar U \<Longrightarrow> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B"
    "\<And>xs. length xs = length Ts \<Longrightarrow> \<forall>i\<in>set xs. 0 \<le> i \<Longrightarrow>
      u \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* rename (bren (rev xs)) 0 B"
    using canonical_body[OF u] by blast
  have nx: "nonneg (bren (rev xs))" and ny: "nonneg (bren (rev ys))"
    using xs(2) ys(2) by (simp_all add: nonneg_bren)
  have wy: "wt (u \<degree>\<degree> map Bound ys)" using eq wt_conv by blast
  have c1: "rename (bren (rev xs)) 0 B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u \<degree>\<degree> map Bound xs"
    using beta_eta_conv[OF B(5)[OF xs] eq(2)] by (rule conv_sym)
  note c1
  also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u \<degree>\<degree> map Bound ys" by (rule eq(1))
  also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev ys)) 0 B" using beta_eta_conv[OF B(5)[OF ys] wy] .
  finally have c: "rename (bren (rev xs)) 0 B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev ys)) 0 B" .
  have "wt (rename (bren (rev xs)) 0 B)" using c1 wt_conv eq(2) by blast
  then have "aconv_term (rename (bren (rev xs)) 0 B) (rename (bren (rev ys)) 0 B)"
    using c by (intro conv_normal_aconv) (simp_all add: normal_rename nx ny B(1))
  then have agree: "bren (rev xs) k = bren (rev ys) k" if "0 \<le> k" "loose_bvar1 B k" for k
    using aconv_rename_agree[of "bren (rev xs)" 0 B "bren (rev ys)" k] that nx ny by simp
  have lb: "k \<in> set ks" if "0 \<le> k" "loose_bvar1 B k" for k
    using ks(2)[OF that(1) loose_bvar1_less[OF B(2) that(2)] agree[OF that]] .
  let ?e0 = "pushes e Ts"
  have e0: "?e0 k = rev Ts ! nat_of_integer k" if "k \<in> set ks" for k
    using ks(1) that by (simp add: pushes_nth)
  have ty: "\<forall>k\<in>set ks. cert_typ alg ar (?e0 k)"
  proof
    fix k assume k: "k \<in> set ks"
    then have "nat_of_integer k < length (rev Ts)" using ks(1) nat_of_integer_less_ilength[of k Ts] by simp
    then have "rev Ts ! nat_of_integer k \<in> set Ts" by (metis nth_mem set_rev)
    then show "cert_typ alg ar (?e0 k)" using bs(2) e0[OF k] by simp
  qed
  note w = strengthen[OF B(3)[of e] lb ty]
  have m: "map ?e0 ks = map (\<lambda>k. rev Ts ! nat_of_integer k) ks" using e0 by simp
  show ?thesis
  proof (rule that)
    show "closed (sabs ?e0 ks B)" by (rule w(1))
    show "e' \<turnstile> sabs ?e0 ks B : map (\<lambda>k. rev Ts ! nat_of_integer k) ks \<Rrightarrow> T" for e'
      using w(2)[of e'] m by simp
    have "sabs ?e0 ks B \<degree>\<degree> map Bound ks \<rightarrow>\<^sub>\<beta>\<^sup>* rename (\<lambda>k. bren (rev ks) (bidx ks k)) 0 B"
      by (rule w(3)) (use ks(1) in auto)
    then have r: "sabs ?e0 ks B \<degree>\<degree> map Bound ks \<rightarrow>\<^sub>\<beta>\<^sup>* B" by (simp only: rename_bren_bidx[OF lb])
    have "pushes e Ts \<turnstile> sabs ?e0 ks B \<degree>\<degree> map Bound ks : T"
    proof (rule list_app_typeI)
      show "pushes e Ts \<turnstile> sabs ?e0 ks B : map ?e0 ks \<Rrightarrow> T" by (rule w(2))
      show "pushes e Ts \<tturnstile> map Bound ks : map ?e0 ks"
        by (rule typings_Bounds) (use ks(1) in auto)
    qed
    then have "e \<turnstile> abs_list bs (sabs ?e0 ks B \<degree>\<degree> map Bound ks) : map snd bs \<Rrightarrow> T"
      using bs by (intro typing_abs_list) force+
    then have "abs_list bs (sabs ?e0 ks B \<degree>\<degree> map Bound ks) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B"
      by (intro conv_beta_eta beta_reds_abs_list r) (auto simp: wt_def)
    then show "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (sabs ?e0 ks B \<degree>\<degree> map Bound ks)"
      using B(4)[OF bs] by (blast intro: conv_sym conv_trans)
  qed
qed

subsection \<open>Flex-flex problems with different heads\<close>

lemma loose_bvar1_reds: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> loose_bvar1 s k"
  by (induction rule: rtranclp_induct) (auto dest: free_beta simp: free_eta)

lemma loose_bvar1_aconv: "aconv_term s t \<Longrightarrow> loose_bvar1 s k \<longleftrightarrow> loose_bvar1 t k"
  by (metis aconv_term_unname loose_bvar1_unname)

lemma aconv_abs_list: "aconv_term s t \<Longrightarrow> aconv_term (abs_list bs s) (abs_list bs t)"
  by (induction bs) auto

lemma bren_rev_map: "0 \<le> p \<Longrightarrow> p < ilength xs \<Longrightarrow> bren (rev (map f xs)) p = f (bren (rev xs) p)"
  using bren_rev[of p "map f xs"] bren_rev[of p xs] nat_of_integer_less_ilength[of p xs]
  by (simp add: rev_map)

lemma pushes_bidx: "y \<in> set xs \<Longrightarrow> pushes e' (map e xs) (bidx xs y) = e y"
proof -
  assume y: "y \<in> set xs"
  have "pushes e' (map e xs) (bidx xs y) = rev (map e xs) ! nat_of_integer (bidx xs y)"
    using bidx_less[OF y] by (simp add: pushes_nth)
  also have "\<dots> = e (rev xs ! nat_of_integer (bidx xs y))"
    using nat_of_integer_less_ilength[OF bidx_nonneg bidx_less[OF y]] by (simp add: rev_map)
  also have "\<dots> = e y" using bren_bidx[OF y] bren_rev[OF bidx_nonneg bidx_less[OF y]] by simp
  finally show ?thesis .
qed

lemma typing_apps_Bounds:
  assumes "closed u" "e' \<turnstile> u : map e xs \<Rrightarrow> T" "\<forall>i\<in>set xs. 0 \<le> i"
  shows "e \<turnstile> u \<degree>\<degree> map Bound xs : T"
proof (rule list_app_typeI)
  show "e \<turnstile> u : map e xs \<Rrightarrow> T" using typing_closed[OF assms(2,1)] .
  show "e \<tturnstile> map Bound xs : map e xs" by (rule typings_Bounds) (use assms(3) in auto)
qed

lemma bs_cert:
  assumes "map snd bs = map e xs" "\<forall>i\<in>set xs. cert_typ alg ar (e i)"
  shows "\<forall>T\<in>snd ` set bs. cert_typ alg ar T"
proof -
  have "snd ` set bs = e ` set xs" using arg_cong[OF assms(1), of set] by simp
  with assms(2) show ?thesis by auto
qed

lemma typing_apps_bidx:
  assumes "closed v" "e' \<turnstile> v : map e ys \<Rrightarrow> T" "set ys \<subseteq> set xs"
  shows "pushes e'' (map e xs) \<turnstile> v \<degree>\<degree> map Bound (map (bidx xs) ys) : T"
proof (rule list_app_typeI)
  have m: "map (pushes e'' (map e xs)) (map (bidx xs) ys) = map e ys"
    unfolding map_map o_def by (rule map_cong[OF refl]) (use assms(3) in \<open>auto simp: pushes_bidx\<close>)
  have "pushes e'' (map e xs) \<tturnstile> map Bound (map (bidx xs) ys) : map (pushes e'' (map e xs)) (map (bidx xs) ys)"
    by (rule typings_Bounds) auto
  then show "pushes e'' (map e xs) \<tturnstile> map Bound (map (bidx xs) ys) : map e ys" by (simp only: m)
  show "pushes e'' (map e xs) \<turnstile> v : map e ys \<Rrightarrow> T" using assms(1,2) by (rule typing_closed[rotated])
qed

text \<open>A closed \<open>u\<close> with \<open>u xs\<close> equivalent to a normal \<open>N\<close> is the abstraction of \<open>N\<close>, renamed:\<close>

lemma body_rename:
  assumes u: "closed u" "e' \<turnstile> u : map e xs \<Rrightarrow> T"
    and xs: "distinct xs" "\<forall>i\<in>set xs. 0 \<le> i"
    and bs: "map snd bs = map e xs" "\<forall>i\<in>set xs. cert_typ alg ar (e i)"
    and N: "u \<degree>\<degree> map Bound xs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" "normal N"
  shows "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (rename (bidx xs) 0 N)"
proof -
  have bs': "\<forall>U\<in>set (map e xs). cert_typ alg ar U" using bs(2) by auto
  obtain B where B: "normal B" "\<not> loose_bvar B (ilength (map e xs))"
    "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B"
    "u \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* rename (bren (rev xs)) 0 B"
    using canonical_body[OF u] bs(1) bs' xs(2) by (metis length_map)
  have nx: "nonneg (bren (rev xs))" using xs(2) by (simp add: nonneg_bren)
  have wt: "wt (u \<degree>\<degree> map Bound xs)" using typing_apps_Bounds[OF u xs(2)] by (auto simp: wt_def)
  have c1: "rename (bren (rev xs)) 0 B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u \<degree>\<degree> map Bound xs"
    using beta_eta_conv[OF B(4) wt] by (rule conv_sym)
  then have "rename (bren (rev xs)) 0 B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using N(1) by (rule conv_trans)
  moreover have "wt (rename (bren (rev xs)) 0 B)" using c1 wt wt_conv by blast
  ultimately have "aconv_term (rename (bren (rev xs)) 0 B) N"
    by (intro conv_normal_aconv) (simp_all add: normal_rename nx B(1) N(2))
  then have a: "aconv_term (rename (bidx xs) 0 (rename (bren (rev xs)) 0 B)) (rename (bidx xs) 0 N)"
    by (rule aconv_rename)
  have "rename (bidx xs) 0 (rename (bren (rev xs)) 0 B) = rename (\<lambda>k. k) 0 B"
    unfolding rename_comp[OF nx]
  proof (rule rename_cong)
    fix k assume "0 \<le> k" "loose_bvar1 B (k + 0)"
    then show "bidx xs (bren (rev xs) k) = k"
      using loose_bvar1_less[OF B(2)] bidx_bren[OF xs(1)] by simp
  qed
  with a have "aconv_term B (rename (bidx xs) 0 N)" by (simp add: rename_id)
  then have "abs_list bs B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (rename (bidx xs) 0 N)"
    by (intro aconv_term_conv aconv_abs_list)
  with B(3) show ?thesis by (rule conv_trans)
qed

text \<open>If the arguments of \<open>v\<close> are among those of \<open>u\<close>, \<open>u\<close> is \<open>v\<close> applied to them:\<close>

lemma flex_sub_sem:
  assumes u: "closed u" "e' \<turnstile> u : map e xs \<Rrightarrow> T" and v: "closed v" "e' \<turnstile> v : map e ys \<Rrightarrow> T"
    and xs: "distinct xs" "\<forall>i\<in>set xs. 0 \<le> i" and ys: "set ys \<subseteq> set xs"
    and bs: "map snd bs = map e xs" "\<forall>i\<in>set xs. cert_typ alg ar (e i)"
    and eq: "u \<degree>\<degree> map Bound xs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> v \<degree>\<degree> map Bound ys"
  shows "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (v \<degree>\<degree> map Bound (map (bidx xs) ys))"
proof -
  have ys0: "\<forall>i\<in>set ys. 0 \<le> i" using xs(2) ys by blast
  have tv: "e \<turnstile> v \<degree>\<degree> map Bound ys : T" by (rule typing_apps_Bounds[OF v ys0])
  obtain N where N: "v \<degree>\<degree> map Bound ys \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using normal_form_ex[OF tv] by blast
  have "u \<degree>\<degree> map Bound xs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N"
    using eq beta_eta_conv[OF N(1)] tv by (auto simp: wt_def intro: conv_trans)
  then have c: "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (rename (bidx xs) 0 N)" by (rule body_rename[OF u xs bs _ N(2)])
  have "map (rename (bidx xs) 0) (map Bound ys) = map Bound (map (bidx xs) ys)"
    unfolding map_map o_def by (rule map_cong[OF refl]) (use ys0 in auto)
  then have "rename (bidx xs) 0 (v \<degree>\<degree> map Bound ys) = v \<degree>\<degree> map Bound (map (bidx xs) ys)"
    using v(1) by (simp only: rename_apps rename_closed order_refl)
  then have r: "v \<degree>\<degree> map Bound (map (bidx xs) ys) \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* rename (bidx xs) 0 N"
    using reds_rename[OF N(1) nonneg_bidx[of xs], of 0] by simp
  have "e \<turnstile> abs_list bs (v \<degree>\<degree> map Bound (map (bidx xs) ys)) : map snd bs \<Rrightarrow> T"
    using typing_apps_bidx[OF v ys, of e] bs bs_cert[OF bs] by (intro typing_abs_list) simp_all
  then have "abs_list bs (v \<degree>\<degree> map Bound (map (bidx xs) ys)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (rename (bidx xs) 0 N)"
    by (intro beta_eta_conv reds_abs_list r) (auto simp: wt_def)
  with c show ?thesis by (blast intro: conv_sym conv_trans)
qed

text \<open>A common normal form \<open>N\<close> whose loose bound variables are among \<open>ks\<close> gives the value of a new
  variable applied to \<open>ks\<close>:\<close>

lemma flex_proj_sem:
  assumes u: "closed u" "e' \<turnstile> u : map e xs \<Rrightarrow> T"
    and xs: "distinct xs" "\<forall>i\<in>set xs. 0 \<le> i"
    and bs: "map snd bs = map e xs" "\<forall>i\<in>set xs. cert_typ alg ar (e i)"
    and N: "u \<degree>\<degree> map Bound xs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" "normal N" "e \<turnstile> N : T"
    and ks: "set ks \<subseteq> set xs" "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 N k \<Longrightarrow> k \<in> set ks"
  shows "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (sabs e ks N \<degree>\<degree> map Bound (map (bidx xs) ks))"
proof -
  have c: "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (rename (bidx xs) 0 N)" by (rule body_rename[OF u xs bs N(1,2)])
  have ty: "\<forall>k\<in>set ks. cert_typ alg ar (e k)" using ks(1) bs(2) by blast
  note w = strengthen[OF N(3) ks(2) ty]
  have "sabs e ks N \<degree>\<degree> map Bound (map (bidx xs) ks) \<rightarrow>\<^sub>\<beta>\<^sup>*
      rename (\<lambda>k. bren (rev (map (bidx xs) ks)) (bidx ks k)) 0 N"
    by (rule w(3)) simp_all
  also have "rename (\<lambda>k. bren (rev (map (bidx xs) ks)) (bidx ks k)) 0 N = rename (bidx xs) 0 N"
  proof (rule rename_cong)
    fix k assume "0 \<le> k" "loose_bvar1 N (k + 0)"
    then have k: "k \<in> set ks" using ks(2) by simp
    show "bren (rev (map (bidx xs) ks)) (bidx ks k) = bidx xs k"
      using bren_rev_map[OF bidx_nonneg bidx_less[OF k]] bren_bidx[OF k] by simp
  qed
  finally have r: "sabs e ks N \<degree>\<degree> map Bound (map (bidx xs) ks) \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bidx xs) 0 N" .
  have "e \<turnstile> abs_list bs (sabs e ks N \<degree>\<degree> map Bound (map (bidx xs) ks)) : map snd bs \<Rrightarrow> T"
    using typing_apps_bidx[OF w(1) w(2) ks(1), of e] bs bs_cert[OF bs] by (intro typing_abs_list) simp_all
  then have "abs_list bs (sabs e ks N \<degree>\<degree> map Bound (map (bidx xs) ks)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs (rename (bidx xs) 0 N)"
    by (intro conv_beta_eta beta_reds_abs_list r) (auto simp: wt_def)
  with c show ?thesis by (blast intro: conv_sym conv_trans)
qed

text \<open>The loose bound variables of a normal form of \<open>u xs\<close>, for closed \<open>u\<close>, are among \<open>xs\<close>:\<close>

lemma loose_bvar1_nf:
  "closed u \<Longrightarrow> u \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar1 N k \<Longrightarrow> k \<in> set xs"
  using loose_bvar1_reds[of "u \<degree>\<degree> map Bound xs" N k] closed_loose_bvar1[of u k]
  by (auto simp: loose_bvar1_apps)

subsection \<open>Loose bound variables of normal forms\<close>

lemma typing_aconv: "aconv_term s t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (metis aconv_term_unname typing_unname_iff)

lemma typing_conv_normal:
  assumes "e \<turnstile> t : T" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" "normal N"
  shows "e \<turnstile> N : T"
proof -
  obtain u v where uv: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" "N \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v" "aconv_term u v"
    using church_rosser[of t N] assms(1,2) by (auto simp: wt_def)
  have "v = N" using normal_reds[OF uv(2) assms(3)] .
  with uv(3) subject_reduction_reds[OF uv(1) assms(1)] show ?thesis by (metis typing_aconv)
qed

lemma no_redex_reds_loose:
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> no_redex s \<Longrightarrow> 0 \<le> k \<Longrightarrow> no_redex t \<and> (loose_bvar1 t k \<longleftrightarrow> loose_bvar1 s k)"
proof (induction rule: rtranclp_induct)
  case (step t u)
  then have nt: "no_redex t" and lt: "loose_bvar1 t k \<longleftrightarrow> loose_bvar1 s k" by simp_all
  from step.hyps(2) nt have "t \<rightarrow>\<^sub>\<eta> u" by (auto simp: no_redex_iff)
  with nt step.prems(2) show ?case using lt by (simp add: no_redex_eta free_eta)
qed simp

lemma is_Abs_apps: "is_Abs (h \<degree>\<degree> ts) \<longleftrightarrow> ts = [] \<and> is_Abs h"
  by (cases ts rule: rev_cases) auto

lemma no_redex_apps: "\<not> is_Abs h \<Longrightarrow> no_redex (h \<degree>\<degree> ts) \<longleftrightarrow> no_redex h \<and> (\<forall>t\<in>set ts. no_redex t)"
  by (induction ts rule: rev_induct) (auto simp: is_Abs_apps)

lemma reds_apps_head: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> s \<degree>\<degree> us \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<degree>\<degree> us"
  by (induction us arbitrary: s s') (auto intro: rtrancl_beta_eta_AppL)

lemma reds_apps:
  "list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N) ts Ns \<Longrightarrow> h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* h \<degree>\<degree> Ns"
proof (induction ts Ns arbitrary: h rule: list_all2_induct)
  case (Cons t ts N Ns)
  have "h $ t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* h $ N" using Cons.hyps(1) by (rule rtrancl_beta_eta_AppR)
  then have "h $ t \<degree>\<degree> Ns \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* h $ N \<degree>\<degree> Ns" by (rule reds_apps_head)
  with Cons.IH[of "h $ t"] have "h $ t \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* h $ N \<degree>\<degree> Ns" by (rule rtranclp_trans)
  then show ?case by (simp only: foldl_Cons)
qed simp

lemma normal_forms_list:
  "\<forall>t\<in>set ts. wt t \<Longrightarrow> \<exists>Ns. list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<and> normal N) ts Ns"
proof (induction ts)
  case (Cons t ts)
  then obtain e T where "e \<turnstile> t : T" by (auto simp: wt_def)
  then obtain N where N: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" by (rule normal_form_ex)
  have "\<forall>t\<in>set ts. wt t" using Cons.prems by simp
  from Cons.IH[OF this] obtain Ns where "list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<and> normal N) ts Ns" ..
  with N have "list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<and> normal N) (t # ts) (N # Ns)"
    by (simp only: list_all2_Cons)
  then show ?case ..
qed (rule exI[of _ "[]"], simp only: list_all2_Nil)

text \<open>
  \<open>nf_bounds t d xs\<close>: the loose bound variables \<open>k \<ge> d\<close> of the normal forms of \<open>t\<close> are \<open>d + x\<close>
  for \<open>x\<close> in \<open>xs\<close>. This holds for the solved rigid side of a flex-rigid problem \<open>F xs =?= t\<close>,
  and propagates along the rigid paths, which \<^const>\<open>pr\<close> follows.
\<close>

definition nf_bounds :: "pterm \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> bool" where
  "nf_bounds t d xs \<longleftrightarrow>
    (\<forall>N. normal N \<longrightarrow> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N \<longrightarrow> (\<forall>k. d \<le> k \<longrightarrow> loose_bvar1 N k \<longrightarrow> k - d \<in> set xs))"

lemma nf_boundsD:
  "nf_bounds t d xs \<Longrightarrow> normal N \<Longrightarrow> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N \<Longrightarrow> d \<le> k \<Longrightarrow> loose_bvar1 N k \<Longrightarrow> k - d \<in> set xs"
  unfolding nf_bounds_def by blast

lemma nf_bounds_conv: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> nf_bounds s d xs \<Longrightarrow> nf_bounds t d xs"
  unfolding nf_bounds_def by (blast intro: conv_trans)

lemma nf_boundsI:
  assumes "wt t" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N0" "normal N0" "\<And>k. d \<le> k \<Longrightarrow> loose_bvar1 N0 k \<Longrightarrow> k - d \<in> set xs"
  shows "nf_bounds t d xs"
  unfolding nf_bounds_def
proof (intro allI impI)
  fix N k assume N: "normal N" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" and k: "d \<le> k" "loose_bvar1 N k"
  have c: "N0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using assms(2) N(2) by (blast intro: conv_sym conv_trans)
  have "wt N0" using assms(1,2) wt_conv by blast
  then have "aconv_term N0 N" using conv_normal_aconv[OF c _ assms(3) N(1)] by blast
  then show "k - d \<in> set xs" using assms(4)[OF k(1)] k(2) loose_bvar1_aconv by blast
qed

text \<open>The solved rigid side of a flex-rigid problem:\<close>

lemma nf_bounds_flex:
  assumes "closed u" "e \<turnstile> u \<degree>\<degree> map Bound xs : T" "u \<degree>\<degree> map Bound xs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "nf_bounds t 0 xs"
proof -
  obtain N0 where N0: "u \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N0" "normal N0" using normal_form_ex[OF assms(2)] .
  have w: "wt (u \<degree>\<degree> map Bound xs)" using assms(2) by (auto simp: wt_def)
  show ?thesis
  proof (rule nf_boundsI)
    show "wt t" using w assms(3) wt_conv by blast
    show "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N0" using assms(3) beta_eta_conv[OF N0(1) w] by (blast intro: conv_sym conv_trans)
    show "k - 0 \<in> set xs" if "0 \<le> k" "loose_bvar1 N0 k" for k
      using loose_bvar1_nf[OF assms(1) N0(1) that] by simp
  qed (rule N0(2))
qed

lemma nf_bounds_Abs:
  assumes "e \<turnstile> Abs a A t : T" "nf_bounds (Abs a A t) d xs" "0 \<le> d"
  shows "nf_bounds t (d + 1) xs"
  unfolding nf_bounds_def
proof (intro allI impI)
  fix N k assume N: "normal N" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" and k: "d + 1 \<le> k" "loose_bvar1 N k"
  from assms(1) obtain U where tyt: "e\<langle>0:A\<rangle> \<turnstile> t : U" and A: "cert_typ alg ar A" by blast
  have tyN: "e\<langle>0:A\<rangle> \<turnstile> N : U" using typing_conv_normal[OF tyt N(2,1)] .
  have tyA: "e \<turnstile> Abs a A N : A \<rightarrow>\<^sub>T U" using A tyN by blast
  obtain N' where N': "Abs a A N \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N'" "normal N'" using normal_form_ex[OF tyA] .
  have "no_redex (Abs a A N)" using N(1) by (simp add: normal_iff)
  then have lb: "loose_bvar1 N' (k - 1) \<longleftrightarrow> loose_bvar1 N k"
    using no_redex_reds_loose[OF N'(1), of "k - 1"] k(1) assms(3) by simp
  have "Abs a A t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a A N"
    using assms(1) tyA N(2) by (intro conv_Abs) (auto simp: wt_def)
  also have "Abs a A N \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N'" using beta_eta_conv[OF N'(1)] tyA by (auto simp: wt_def)
  finally have "k - 1 - d \<in> set xs"
    using nf_boundsD[OF assms(2) N'(2)] lb k by simp
  then show "k - (d + 1) \<in> set xs" by (simp add: algebra_simps)
qed

lemma nf_bounds_apps:
  assumes ty: "e \<turnstile> h \<degree>\<degree> ts : T" and h: "atom h" and nb: "nf_bounds (h \<degree>\<degree> ts) d xs" and d: "0 \<le> d"
  shows "\<forall>t\<in>set ts. nf_bounds t d xs" and "h = Bound i \<Longrightarrow> d \<le> i \<Longrightarrow> i - d \<in> set xs"
proof -
  have "wt (h \<degree>\<degree> ts)" using ty by (auto simp: wt_def)
  then have wts: "\<forall>t\<in>set ts. wt t" using wt_apps_args by blast
  obtain Ns where Ns: "list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<and> normal N) ts Ns"
    using normal_forms_list[OF wts] by blast
  let ?M = "h \<degree>\<degree> Ns"
  have r: "h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* ?M" by (rule reds_apps, rule list_all2_mono[OF Ns]) blast
  have "\<forall>N\<in>set Ns. normal N" using Ns by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
  then have nr: "no_redex ?M" using h by (subst no_redex_apps) (auto simp: normal_iff elim: atom.elims)
  have tyM: "e \<turnstile> ?M : T" by (rule subject_reduction_reds[OF r ty])
  obtain M' where M': "?M \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* M'" "normal M'" using normal_form_ex[OF tyM] .
  have c: "h \<degree>\<degree> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M'" using ty r M'(1) by (intro beta_eta_conv) (auto simp: wt_def)
  have lbM: "k - d \<in> set xs" if "d \<le> k" "0 \<le> d" "loose_bvar1 ?M k" for k
    using nf_boundsD[OF nb M'(2) c that(1)] no_redex_reds_loose[OF M'(1) nr, of k] that by simp
  show "h = Bound i \<Longrightarrow> d \<le> i \<Longrightarrow> i - d \<in> set xs"
    using lbM[of i] d by (simp add: loose_bvar1_apps)
  show "\<forall>t\<in>set ts. nf_bounds t d xs"
  proof
    fix t assume "t \<in> set ts"
    then obtain j where j: "j < length ts" "t = ts ! j" by (auto simp: in_set_conv_nth)
    have Nj: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Ns ! j" "normal (Ns ! j)" using Ns j by (auto simp: list_all2_conv_all_nth)
    have jN: "Ns ! j \<in> set Ns" using Ns j by (auto simp: list_all2_conv_all_nth)
    show "nf_bounds t d xs"
    proof (rule nf_boundsI[OF _ _ Nj(2)])
      show "wt t" using wts j by auto
      then show "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Ns ! j" by (rule beta_eta_conv[OF Nj(1)])
      show "k - d \<in> set xs" if "d \<le> k" "loose_bvar1 (Ns ! j) k" for k
        using lbM[OF that(1) d] that jN by (auto simp: loose_bvar1_apps)
    qed
  qed
qed

end

end
