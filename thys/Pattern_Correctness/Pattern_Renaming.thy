section \<open>Renaming of Bound Variables and Types of Terms\<close>

text \<open>
  Renaming of loose bound variables, the type variables of a term, and facts on loose bound
  variables, closed terms and the types computed by \<open>fastype_of\<close>. The soundness of the unifiers
  uses them; normal forms are in theory \<open>Pattern_Normal\<close>, matching in the theories \<open>Match_\<dots>\<close>.
\<close>

theory Pattern_Renaming
  imports Pattern_Sound
begin

subsection \<open>Renaming\<close>

lemma nonnegD: "nonneg f \<Longrightarrow> 0 \<le> k \<Longrightarrow> 0 \<le> f k"
  by (simp add: nonneg_def)

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

lemma reds_rename:
  "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (rename f d s) (rename f d t)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl beta_rename eta_rename)

lemma aconv_rename: "aconv_term u v \<Longrightarrow> aconv_term (rename f d u) (rename f d v)"
  by (induction u v arbitrary: d rule: aconv_term.induct) (auto split: if_splits)

subsection \<open>Types and type variables of terms\<close>

lemma typs_apps: "typs (s \<degree>\<degree> ts) = typs s \<union> \<Union> (typs ` set ts)"
  by (induction ts arbitrary: s) auto

lemma typs_incr_bv [simp]: "typs (incr_bv n k t) = typs t"
  by (induction t arbitrary: k) auto

definition ttvars :: "pterm \<Rightarrow> (indexname \<times> psort) set" where
  "ttvars t = (\<Union>U\<in>typs t. tvars U)"

lemma ttvars_simps [simp]:
  "ttvars (s $ t) = ttvars s \<union> ttvars t" "ttvars (Abs a T t) = tvars T \<union> ttvars t"
  "ttvars (Bound i) = {}" "ttvars (Var x T) = tvars T" "ttvars (Const c T) = tvars T"
  "ttvars (Free f T) = tvars T"
  by (auto simp: ttvars_def)

lemma ttvars_apps: "ttvars (s \<degree>\<degree> ts) = ttvars s \<union> \<Union> (ttvars ` set ts)"
  by (induction ts arbitrary: s) auto

context pure_sig_gen
begin

lemma incr_bv_closed: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> incr_bv n k t = t"
  by (simp add: incr_bv_no_loose closed_loose_bvar)

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

lemma beta_reds_abs_list: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> abs_list bs s \<rightarrow>\<^sub>\<beta>\<^sup>* abs_list bs t"
  by (induction bs) auto

lemma loose_bvar1_less: "\<not> loose_bvar t n \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k < n"
  by (meson loose_bvar1_imp loose_bvar_mono not_le)

lemma loose_bvar1_aconv: "aconv_term s t \<Longrightarrow> loose_bvar1 s k \<longleftrightarrow> loose_bvar1 t k"
  by (metis aconv_term_unname loose_bvar1_unname)

lemma typing_aconv: "aconv_term s t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (metis aconv_term_unname typing_unname_iff)

end

subsection \<open>Closed terms\<close>

context pure_sig_gen
begin

lemma closed_iff_loose_bvar1: "closed t \<longleftrightarrow> (\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar1 t k)"
  by (auto simp: closed_def loose_bvar_iff)

subsection \<open>\<open>\<eta>\<close>-contraction\<close>

lemma decr_subst: "\<not> loose_bvar1 f lev \<Longrightarrow> decr lev f = f[d/lev]"
proof (induction f arbitrary: lev d)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound)
next
  case (Abs a T t)
  then show ?case by simp
qed simp_all

lemma eta_contract_reds: "t \<rightarrow>\<^sub>\<eta>\<^sup>* eta_contract t"
proof (induction t)
  case (Abs a T body)
  let ?b = "eta_contract body"
  have 1: "Abs a T body \<rightarrow>\<^sub>\<eta>\<^sup>* Abs a T ?b" using Abs.IH by (rule rtrancl_eta_Abs)
  have 2: "Abs a T ?b \<rightarrow>\<^sub>\<eta>\<^sup>* eta_contract (Abs a T body)"
  proof (cases "\<exists>f. ?b = f $ Bound 0 \<and> \<not> is_dependent f")
    case True
    then obtain f where b: "?b = f $ Bound 0" "\<not> is_dependent f" by blast
    then have "eta_contract (Abs a T body) = decr 0 f" by simp
    moreover have "Abs a T (f $ Bound 0) \<rightarrow>\<^sub>\<eta> f[Bound 0/0]"
      using b(2) by (intro eta.eta) (simp add: is_dependent_def)
    moreover have "decr 0 f = f[Bound 0/0]"
      using b(2) by (intro decr_subst) (simp add: is_dependent_def)
    ultimately show ?thesis using b(1) by simp
  next
    case False
    then have "eta_contract (Abs a T body) = Abs a T ?b"
      by (auto simp: Let_def split: pterm.splits)
    then show ?thesis by simp
  qed
  from 1 2 show ?case by (rule rtranclp_trans)
next
  case (App s t)
  then show ?case by (simp add: rtrancl_eta_App)
qed simp_all

lemma aeconv_conv: "aeconv s t \<Longrightarrow> wt s \<Longrightarrow> wt t \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  unfolding aeconv_def
proof (elim disjE)
  assume "aconv_term s t"
  then show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" by (rule aconv_term_conv)
next
  assume a: "aconv_term (eta_contract s) (eta_contract t)" and w: "wt s" "wt t"
  have "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract s"
    using w(1) eta_contract_reds[of s] by (intro beta_eta_conv) (simp add: eta_reds_beta_eta_reds)
  also have "eta_contract s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract t" using a by (rule aconv_term_conv)
  also have "eta_contract t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
    using beta_eta_conv[OF eta_reds_beta_eta_reds[OF eta_contract_reds] w(2)] by (rule conv_sym)
  finally show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" .
qed

subsection \<open>The type computed by \<open>fastype_of\<close>\<close>

lemma fastype_of_bound_typed:
  "0 \<le> i \<Longrightarrow> i < ilength Ts \<Longrightarrow> fastype_of_bound Ts i = return (Ts ! nat_of_integer i)"
proof (induction Ts arbitrary: i)
  case (Cons T Ts)
  show ?case
  proof (cases "i = 0")
    case False
    with Cons.prems have i: "0 \<le> i - 1" "i - 1 < ilength Ts" by (simp_all add: integer_arith)
    have "nat_of_integer i = Suc (nat_of_integer (i - 1))"
      using False Cons.prems(1) by (simp add: integer_arith nat_of_integer.rep_eq)
    with Cons.IH[OF i] False show ?thesis by simp
  qed simp
qed (simp add: integer_arith)

lemma fastype_of_typed:
  "e \<turnstile> t : T \<Longrightarrow>
    (\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 t k \<longrightarrow> k < ilength Ts \<and> e k = Ts ! nat_of_integer k) \<Longrightarrow>
    fastype_of_term Ts t = return T \<and> (\<forall>A B. T = A \<rightarrow>\<^sub>T B \<longrightarrow> range_type_of Ts t = return B)"
proof (induction arbitrary: Ts rule: typing.induct)
  case (Bound i e T)
  then have "i < ilength Ts" "T = Ts ! nat_of_integer i" by auto
  with Bound show ?case by (auto simp: fastype_of_bound_typed return_def)
next
  case (Abs T e t U a)
  have "\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 t k \<longrightarrow> k < ilength (T # Ts) \<and> (e\<langle>0:T\<rangle>) k = (T # Ts) ! nat_of_integer k"
  proof (intro allI impI)
    fix k assume k: "0 \<le> k" "loose_bvar1 t k"
    show "k < ilength (T # Ts) \<and> (e\<langle>0:T\<rangle>) k = (T # Ts) ! nat_of_integer k"
    proof (cases "k = 0")
      case False
      with k have k1: "0 \<le> k - 1" "loose_bvar1 (Abs a T t) (k - 1)" by (simp_all add: integer_arith)
      with Abs.prems have "k - 1 < ilength Ts" "e (k - 1) = Ts ! nat_of_integer (k - 1)" by blast+
      moreover have "nat_of_integer k = Suc (nat_of_integer (k - 1))"
        using False k(1) by (simp add: integer_arith nat_of_integer.rep_eq)
      ultimately show ?thesis using False k(1) by (simp add: integer_arith)
    qed (use ilength_nonneg[of Ts] in \<open>simp add: integer_arith\<close>)
  qed
  with Abs.IH show ?case by (simp add: return_def)
next
  case (App e s T U t)
  have "\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 s k \<longrightarrow> k < ilength Ts \<and> e k = Ts ! nat_of_integer k"
    "\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 t k \<longrightarrow> k < ilength Ts \<and> e k = Ts ! nat_of_integer k"
    using App.prems by auto
  with App.IH(1)[of Ts] show ?case by (simp add: return_def)
qed (simp_all add: return_def)

lemma fastype_of_closed: "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> fastype_of t = return T"
  using fastype_of_typed[of e t T "[]"] by (simp add: fastype_of_def closed_iff_loose_bvar1)

subsection \<open>Certified types\<close>

lemma cert_typ_fun: "cert_typ alg ar (T \<rightarrow>\<^sub>T U) \<longleftrightarrow> cert_typ alg ar T \<and> cert_typ alg ar U"
  by (auto simp: cert_typ_def tarity_def)

lemma cert_typ_TVar: "cert_typ alg ar (TVar v S) \<longleftrightarrow> sort_ok alg S"
  by (simp add: cert_typ_def)

lemma typing_cert:
  "e \<turnstile> t : T \<Longrightarrow> (\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 t i \<longrightarrow> cert_typ alg ar (e i)) \<Longrightarrow> cert_typ alg ar T"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  have "\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 t i \<longrightarrow> cert_typ alg ar ((e\<langle>0:T\<rangle>) i)"
  proof (intro allI impI)
    fix i assume i: "0 \<le> i" "loose_bvar1 t i"
    show "cert_typ alg ar ((e\<langle>0:T\<rangle>) i)"
    proof (cases "i = 0")
      case False
      with i have "0 \<le> i - 1" "loose_bvar1 (Abs a T t) (i - 1)" by (simp_all add: integer_arith)
      with Abs.prems False i(1) show ?thesis by (simp add: integer_arith)
    qed (use Abs.hyps(1) in simp)
  qed
  with Abs show ?case by (simp add: cert_typ_fun)
next
  case (App e s T U t)
  then show ?case by (auto simp: cert_typ_fun)
qed auto

lemma typing_cert_closed: "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> cert_typ alg ar T"
  by (erule typing_cert) (simp add: closed_iff_loose_bvar1)

end

end
