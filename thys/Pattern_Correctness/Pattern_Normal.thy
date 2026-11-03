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


subsection \<open>Canonical bodies\<close>

text \<open>
  A closed term \<open>u\<close> of type \<open>Ts \<Rrightarrow> T\<close> is equivalent to the abstraction of the normal form \<open>B\<close>
  of its application to \<^term>\<open>downs (length Ts)\<close>, and its applications to bound variables
  \<open>xs\<close> reduce to renamings of \<open>B\<close>, which are normal.
\<close>

lemma canonical_body:
  assumes u: "closed u" "e \<turnstile> u : Ts \<Rrightarrow> T"
  obtains B where "normal B" "\<not> loose_bvar B (ilength Ts)"
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

end

end
