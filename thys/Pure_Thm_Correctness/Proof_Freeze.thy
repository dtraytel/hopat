section \<open>Closed instantiations\<close>

theory Proof_Freeze
  imports Proof_Valid
begin

text \<open>
  Validity modulo flex-flex pairs for closed instantiations, which the unifiers and the
  normalization of terms speak about, implies validity for instantiations in a context of bound
  variables: the bound variables are frozen to fresh schematic variables and thawed again by an
  instantiation.
\<close>


subsection \<open>Substitution for loose bound variables\<close>

text \<open>\<open>bsubst cs k\<close> replaces the loose bound variable \<open>k + i\<close> by the free variable \<open>cs ! i\<close>.\<close>

fun bsubst :: "nat list \<Rightarrow> nat \<Rightarrow> dB \<Rightarrow> dB" where
  "bsubst cs k (dB.Var x) = dB.Var x"
| "bsubst cs k (BVar i) =
    (if i < k then BVar i else if i - k < length cs then dB.Var (cs ! (i - k)) else BVar (i - length cs))"
| "bsubst cs k (dB.Abs t) = dB.Abs (bsubst cs (Suc k) t)"
| "bsubst cs k (s \<degree> t) = bsubst cs k s \<degree> bsubst cs k t"

lemma lift_bsubst: "j \<le> k \<Longrightarrow> lift (bsubst cs k s) j = bsubst cs (Suc k) (lift s j)"
  by (induction s arbitrary: j k) auto

lemma subst_bsubst:
  "j \<le> k \<Longrightarrow> subst (bsubst cs (Suc k) s) (bsubst cs k u) j = bsubst cs k (subst s u j)"
proof (induction s arbitrary: j k u)
  case (BVar i)
  then show ?case by (auto simp: subst_BVar)
next
  case (Abs s)
  have "lift (bsubst cs k u) 0 = bsubst cs (Suc k) (lift u 0)" by (rule lift_bsubst) simp
  with Abs.IH[of "Suc j" "Suc k" "lift u 0"] Abs.prems show ?case by simp
qed simp_all

lemma free_bsubst: "i < k \<Longrightarrow> free (bsubst cs k s) i \<longleftrightarrow> free s i"
  by (induction s arbitrary: i k) auto

lemma bsubst_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> bsubst cs k s \<rightarrow>\<^sub>\<beta> bsubst cs k t"
proof (induction arbitrary: k rule: beta.induct)
  case (beta s t)
  have "dB.Abs (bsubst cs (Suc k) s) \<degree> bsubst cs k t \<rightarrow>\<^sub>\<beta> subst (bsubst cs (Suc k) s) (bsubst cs k t) 0"
    by (rule beta.beta)
  then show ?case by (simp add: subst_bsubst)
qed auto

lemma bsubst_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> bsubst cs k s \<rightarrow>\<^sub>\<eta> bsubst cs k t"
proof (induction arbitrary: k rule: eta.induct)
  case (eta s d)
  have "\<not> free (bsubst cs (Suc k) s) 0" using eta free_bsubst[of 0 "Suc k" cs s] by simp
  then have "dB.Abs (bsubst cs (Suc k) s \<degree> BVar 0) \<rightarrow>\<^sub>\<eta> subst (bsubst cs (Suc k) s) (bsubst cs k d) 0"
    by (rule eta.eta)
  then show ?case by (simp add: subst_bsubst)
qed auto

lemma bsubst_equiv: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> bsubst cs k s \<equiv>\<^sub>\<beta>\<^sub>\<eta> bsubst cs k t"
proof (induction rule: rtranclp_induct)
  case (step y z)
  from step.hyps(2) have "symcl \<beta>\<eta> (bsubst cs k y) (bsubst cs k z)"
    unfolding symcl.simps by (auto intro: bsubst_beta bsubst_eta)
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed simp

lemma liftn_bsubst: "liftn n (bsubst cs k s) k = bsubst cs (k + n) (liftn n s k)"
  by (induction s arbitrary: k) auto

subsection \<open>Freezing bound variables\<close>

fun freezeV :: "indexname list \<Rightarrow> ptyp list \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "freezeV fs Us lev (Bound i) =
    (if i < lev then Bound i
     else if nat_of_integer (i - lev) < length fs then Var (fs ! nat_of_integer (i - lev)) (Us ! nat_of_integer (i - lev))
     else Bound (i - integer_of_nat (length fs)))"
| "freezeV fs Us lev (Abs a T t) = Abs a T (freezeV fs Us (lev + 1) t)"
| "freezeV fs Us lev (s $ t) = freezeV fs Us lev s $ freezeV fs Us lev t"
| "freezeV fs Us lev t = t"

context prf_csig
begin

lemma tr_freezeV:
  "proper t \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    tr (freezeV fs Us lev t) = bsubst (map (\<lambda>f. code (AVar f)) fs) (nat_of_integer lev) (tr t)"
proof (induction fs Us lev t rule: freezeV.induct)
  case (1 fs Us lev i)
  then show ?case
    by (auto simp: integer_reps nat_diff_distrib nat_less_iff not_less)
next
  case (2 fs Us lev a T t)
  then show ?case by (simp add: nat_of_integer_plus1)
qed simp_all

lemma vars_freezeV: "vars (freezeV fs Us lev t) \<subseteq> vars t \<union> set fs"
  by (induction fs Us lev t rule: freezeV.induct) auto

lemma has_type_freezeV:
  "has_type V Ts' t T \<Longrightarrow> Ts' = Ts @ Us \<Longrightarrow> length fs = length Us \<Longrightarrow>
    (\<forall>i<length Us. V' (fs ! i) = Us ! i) \<Longrightarrow> (\<forall>x\<in>vars t. V' x = V x) \<Longrightarrow>
    has_type V' Ts (freezeV fs Us (integer_of_nat (length Ts)) t) T"
proof (induction arbitrary: Ts rule: has_type.induct)
  case (Var V x T Ts')
  then show ?case by (auto intro: has_type.Var)
next
  case (Bound i Ts' T V Ts)
  show ?case
  proof (cases "i < integer_of_nat (length Ts)")
    case True
    then have "nat_of_integer i < length Ts" using Bound(1) by (simp add: integer_reps nat_less_iff)
    with True Bound show ?thesis by (auto intro!: has_type.Bound simp: nth_append)
  next
    case False
    let ?k = "nat_of_integer (i - integer_of_nat (length Ts))"
    have k: "?k = nat_of_integer i - length Ts" "length Ts \<le> nat_of_integer i"
      using False Bound(1) by (auto simp: integer_reps nat_diff_distrib not_less)
    then have "?k < length fs" using Bound by simp
    with False Bound k show ?thesis by (auto intro: has_type.Var simp: nth_append)
  qed
next
  case (Abs V T Ts' t U x)
  from Abs.prems Abs.IH[of "T # Ts"] show ?case by (auto intro!: has_type.Abs simp: integer_of_nat_Suc)
qed (auto intro: has_type.intros)

text \<open>Thawing the frozen variables by an instantiation.\<close>

lemma psubst_freezeV:
  "has_type V Ts' t T \<Longrightarrow> Ts' = Ts @ Us \<Longrightarrow> length fs = length Us \<Longrightarrow>
    (\<forall>i<length fs. \<theta> (fs ! i) = Bound (integer_of_nat i)) \<Longrightarrow> (\<forall>x\<in>vars t. \<theta> x = Var x (V x)) \<Longrightarrow>
    psubst TVar \<theta> (integer_of_nat (length Ts)) (freezeV fs Us (integer_of_nat (length Ts)) t) = t"
proof (induction arbitrary: Ts rule: has_type.induct)
  case (Const a T V Ts')
  then show ?case by (simp add: tsubst_TVar)
next
  case (Free V Ts' a T)
  then show ?case by (simp add: tsubst_TVar)
next
  case (Var V x T Ts')
  then show ?case by (simp add: incr_boundvars_eq)
next
  case (Bound i Ts' T V Ts)
  show ?case
  proof (cases "i < integer_of_nat (length Ts)")
    case False
    let ?k = "nat_of_integer (i - integer_of_nat (length Ts))"
    have k: "?k = nat_of_integer i - length Ts" "length Ts \<le> nat_of_integer i"
      using False Bound(1) by (auto simp: integer_reps nat_diff_distrib not_less)
    then have "?k < length fs" using Bound by simp
    moreover have "integer_of_nat ?k + integer_of_nat (length Ts) = i"
      using k Bound(1) by (simp add: integer_eq_iff integer_reps integer_of_nat.rep_eq)
    ultimately show ?thesis using False Bound by (simp add: incr_boundvars_eq add.commute)
  qed simp
next
  case (Abs V T Ts' t U x)
  from Abs.prems Abs.IH[of "T # Ts"] show ?case by (simp add: integer_of_nat_Suc tsubst_TVar)
qed simp


subsection \<open>Composition and congruence of instantiations\<close>

lemma incr_bv_comp: "m \<le> k \<Longrightarrow> k \<le> m + b \<Longrightarrow> 0 \<le> a \<Longrightarrow> incr_bv a k (incr_bv b m v) = incr_bv (a + b) m v"
  by (induction b m v arbitrary: k rule: incr_bv.induct) (auto simp: algebra_simps)

lemma psubst_incr_bv_gen:
  "0 \<le> d \<Longrightarrow> 0 \<le> l \<Longrightarrow> psubst \<rho> \<theta> (d + l) (incr_bv l d v) = incr_bv l d (psubst \<rho> \<theta> d v)"
proof (induction \<rho> \<theta> d v rule: psubst.induct)
  case (1 \<rho> \<theta> lev x T)
  then show ?case by (simp add: incr_boundvars_eq incr_bv_comp add.commute)
next
  case (5 \<rho> \<theta> lev a T t)
  then show ?case by (simp add: algebra_simps)
qed simp_all

lemma psubst_psubst:
  "0 \<le> lev \<Longrightarrow> psubst \<rho>2 \<theta>2 lev (psubst \<rho>1 \<theta>1 lev t) =
    psubst (\<lambda>v S. tsubst \<rho>2 (\<rho>1 v S)) (\<lambda>x. psubst \<rho>2 \<theta>2 0 (\<theta>1 x)) lev t"
proof (induction \<rho>1 \<theta>1 lev t rule: psubst.induct)
  case (1 \<rho> \<theta> lev x T)
  then show ?case using psubst_incr_bv_gen[of 0 lev \<rho>2 \<theta>2 "\<theta> x"] by (simp add: incr_boundvars_eq)
qed (simp_all add: tsubst_tsubst)

fun prf_vars :: "prf \<Rightarrow> indexname set" where
  "prf_vars (Abst a T p) = prf_vars p"
| "prf_vars (AbsP a t p) = (case t of None \<Rightarrow> {} | Some t \<Rightarrow> vars t) \<union> prf_vars p"
| "prf_vars (PAppt p t) = prf_vars p \<union> (case t of None \<Rightarrow> {} | Some t \<Rightarrow> vars t)"
| "prf_vars (PAppp p q) = prf_vars p \<union> prf_vars q"
| "prf_vars p = {}"

lemma finite_vars: "finite (vars t)"
  by (induction t) auto

lemma finite_prf_vars: "finite (prf_vars p)"
  by (induction p rule: prf_vars.induct) (auto simp: finite_vars split: option.split)

lemma psubst_cong: "(\<And>x. x \<in> vars t \<Longrightarrow> \<theta> x = \<theta>' x) \<Longrightarrow> psubst \<rho> \<theta> lev t = psubst \<rho> \<theta>' lev t"
  by (induction \<rho> \<theta> lev t rule: psubst.induct) auto

lemma map_option_psubst_cong:
  "(\<And>x. x \<in> (case t of None \<Rightarrow> {} | Some u \<Rightarrow> vars u) \<Longrightarrow> \<theta> x = \<theta>' x) \<Longrightarrow>
    map_option (psubst \<rho> \<theta> lev) t = map_option (psubst \<rho> \<theta>' lev) t"
  by (cases t) (auto intro: psubst_cong)

lemma prf_inst_cong:
  "(\<And>x. x \<in> prf_vars p \<Longrightarrow> \<theta> x = \<theta>' x) \<Longrightarrow> prf_inst \<rho> \<theta> lev p = prf_inst \<rho> \<theta>' lev p"
  by (induction \<rho> \<theta> lev p rule: prf_inst.induct) (auto intro!: map_option_psubst_cong)

lemma prf_inst_prf_inst:
  "0 \<le> lev \<Longrightarrow> prf_inst \<rho>2 \<theta>2 lev (prf_inst \<rho>1 \<theta>1 lev p) =
    prf_inst (\<lambda>v S. tsubst \<rho>2 (\<rho>1 v S)) (\<lambda>x. psubst \<rho>2 \<theta>2 0 (\<theta>1 x)) lev p"
  by (induction \<rho>1 \<theta>1 lev p rule: prf_inst.induct)
    (simp_all add: psubst_psubst tsubst_tsubst option.map_comp comp_def split: option.split)

lemma tsubst_TVar_comp: "(\<lambda>v S. tsubst TVar (\<rho> v S)) = \<rho>"
  by (simp add: tsubst_TVar)


subsection \<open>Fresh variables\<close>

lemma fresh_vars:
  assumes "finite A"
  obtains fs :: "indexname list" where "length fs = n" "distinct fs" "set fs \<inter> A = {}" "\<forall>f\<in>set fs. 0 \<le> snd f"
proof -
  define M where "M = Max (insert 0 (snd ` A)) + 1"
  have M: "snd x < M" if "x \<in> A" for x
  proof -
    have "snd x \<le> Max (insert 0 (snd ` A))" using assms that by (intro Max_ge) auto
    then show ?thesis by (simp add: M_def)
  qed
  have M0: "0 \<le> M" using assms by (auto simp: M_def intro: add_nonneg_nonneg Max_ge order.trans[rotated])
  let ?fs = "map (\<lambda>i. (STR '''', M + integer_of_nat i)) [0..<n]"
  have "distinct ?fs" by (auto simp: distinct_map inj_on_def integer_of_nat_eq_of_nat)
  moreover have "x \<notin> A" if "x \<in> set ?fs" for x
  proof -
    from that obtain i where x: "x = (STR '''', M + integer_of_nat i)" by auto
    have "\<not> M + integer_of_nat i < M" using integer_of_nat_nonneg[of i] by (simp add: not_less)
    with x M show ?thesis by force
  qed
  then have "set ?fs \<inter> A = {}" by blast
  moreover have "\<forall>f\<in>set ?fs. 0 \<le> snd f" using M0 by auto
  ultimately show thesis by (intro that[of ?fs]) simp_all
qed


subsection \<open>Closed validity\<close>

definition prf_valid :: "algebra \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm set \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> prf \<Rightarrow> pterm \<Rightarrow> bool" where
  "prf_valid alg V H tps p \<phi> \<longleftrightarrow> (\<forall>V' \<rho> \<theta>. wsinst alg \<rho> \<longrightarrow> inst_typed V V' [] \<rho> \<theta> \<longrightarrow>
    (\<forall>(t, u)\<in>set tps. tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)) \<longrightarrow>
    prf_ok V' H [] [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 \<phi>))"

lemma prf_validD:
  "prf_valid alg V H tps p \<phi> \<Longrightarrow> wsinst alg \<rho> \<Longrightarrow> inst_typed V V' [] \<rho> \<theta> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)) \<Longrightarrow>
    prf_ok V' H [] [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 \<phi>)"
  unfolding prf_valid_def by blast

lemma prf_valid_ctx_prf_valid: "prf_valid_ctx alg V H tps p \<phi> \<Longrightarrow> prf_valid alg V H tps p \<phi>"
  unfolding prf_valid_def prf_valid_ctx_def by blast

fun anns_proper :: "prf \<Rightarrow> bool" where
  "anns_proper (Abst a T p) = anns_proper p"
| "anns_proper (AbsP a t p) = ((case t of None \<Rightarrow> True | Some t \<Rightarrow> proper t) \<and> anns_proper p)"
| "anns_proper (PAppt p t) = (anns_proper p \<and> (case t of None \<Rightarrow> True | Some t \<Rightarrow> proper t))"
| "anns_proper (PAppp p q) = (anns_proper p \<and> anns_proper q)"
| "anns_proper p = True"

lemma amatch_proper: "amatch t u \<Longrightarrow> proper u \<Longrightarrow> proper t"
  by (induction rule: amatch.induct) auto

lemma prf_ok_anns_proper: "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> anns_proper p"
  by (induction rule: prf_ok.induct)
    (auto simp: ann_ok_def wty_def split: option.splits dest: amatch_proper has_type_proper)

lemma proper_incr_bv_rev: "proper (incr_bv n k v) \<Longrightarrow> 0 \<le> k \<Longrightarrow> proper v"
  by (induction n k v rule: incr_bv.induct) (auto split: if_splits)

lemma proper_psubst_vars: "proper (psubst \<rho> \<theta> lev t) \<Longrightarrow> 0 \<le> lev \<Longrightarrow> x \<in> vars t \<Longrightarrow> proper (\<theta> x)"
  by (induction \<rho> \<theta> lev t rule: psubst.induct) (auto simp: incr_boundvars_eq dest: proper_incr_bv_rev)

lemma anns_proper_prf_vars:
  "anns_proper (prf_inst \<rho> \<theta> lev p) \<Longrightarrow> 0 \<le> lev \<Longrightarrow> x \<in> prf_vars p \<Longrightarrow> proper (\<theta> x)"
  by (induction \<rho> \<theta> lev p rule: prf_inst.induct) (auto split: option.splits dest: proper_psubst_vars)

lemma has_type_loose_bvar: "has_type V Ts t T \<Longrightarrow> \<not> loose_bvar t (integer_of_nat (length Ts))"
  by (induction rule: has_type.induct) (auto simp: integer_reps integer_of_nat_Suc nat_less_iff)

lemma proper_freezeV: "proper t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> proper (freezeV fs Us lev t)"
  by (induction fs Us lev t rule: freezeV.induct) (auto simp: integer_reps not_less)

lemma tr_psubst_freezeV:
  "proper t \<Longrightarrow> \<not> loose_bvar t lev \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    (\<And>x. x \<in> vars t \<Longrightarrow> \<theta>f x = freezeV fs Us 0 (\<theta> x) \<and> proper (\<theta> x)) \<Longrightarrow>
    tr (psubst \<rho> \<theta>f lev t) = bsubst (map (\<lambda>f. code (AVar f)) fs) (nat_of_integer lev) (tr (psubst \<rho> \<theta> lev t))"
proof (induction \<rho> \<theta> lev t rule: psubst.induct)
  case (1 \<rho> \<theta> lev x T)
  then have pr: "proper (\<theta> x)" and e: "\<theta>f x = freezeV fs Us 0 (\<theta> x)" by auto
  have "tr (incr_boundvars lev (freezeV fs Us 0 (\<theta> x))) =
      liftn (nat_of_integer lev) (bsubst (map (\<lambda>f. code (AVar f)) fs) 0 (tr (\<theta> x))) 0"
    using pr 1(3) by (simp add: tr_incr_boundvars proper_freezeV tr_freezeV integer_reps)
  also have "\<dots> = bsubst (map (\<lambda>f. code (AVar f)) fs) (nat_of_integer lev) (tr (incr_boundvars lev (\<theta> x)))"
    using pr 1(3) liftn_bsubst[of "nat_of_integer lev" _ 0] by (simp add: tr_incr_boundvars)
  finally show ?case by (simp add: e)
next
  case (4 \<rho> \<theta> lev i)
  then show ?case by (simp add: integer_reps nat_less_iff)
next
  case (5 \<rho> \<theta> lev a T t)
  then show ?case by (simp add: nat_of_integer_plus1)
qed simp_all

theorem prf_valid_prf_valid_ctx:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {})"
    and P: "prf_valid alg V H tps p \<phi>"
    and tps: "\<forall>(t, u)\<in>set tps. \<exists>T. wty V [] t T \<and> wty V [] u T"
  shows "prf_valid_ctx alg V H tps p \<phi>"
  unfolding prf_valid_ctx_def
proof (intro allI impI)
  fix V' Us \<rho> \<theta>
  assume ws: "wsinst alg \<rho>" and \<theta>: "inst_typed V V' Us \<rho> \<theta>"
    and sol: "\<forall>(t, u)\<in>set tps. tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)"
  define R where "R = {x \<in> vars \<phi> \<union> prf_vars p \<union> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u). 0 \<le> snd x}"
  define F where "F = (\<Union>x\<in>R. vars (\<theta> x))"
  have fR: "finite R"
    by (rule finite_subset[of _ "vars \<phi> \<union> prf_vars p \<union> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u)"])
      (auto simp: R_def finite_vars finite_prf_vars)
  then have fF: "finite F" by (auto simp: F_def finite_vars)
  obtain fs where fs: "length fs = length Us" "distinct fs" "set fs \<inter> (R \<union> F) = {}" "\<forall>f\<in>set fs. 0 \<le> snd f"
    using fresh_vars[of "R \<union> F" "length Us"] fR fF by blast
  define idx where "idx y = (THE i. i < length fs \<and> fs ! i = y)" for y
  have idx: "idx (fs ! i) = i" if "i < length fs" for i
    using that fs(2) by (auto simp: idx_def intro!: the_equality simp: nth_eq_iff_index_eq)
  define V'' where "V'' y = (if y \<in> set fs then Us ! idx y else V' y)" for y
  have V''fs: "V'' (fs ! i) = Us ! i" if "i < length Us" for i
    using that fs(1) idx by (simp add: V''_def)
  have V''F: "V'' y = V' y" if "y \<in> F" for y using that fs(3) by (auto simp: V''_def)
  have wx: "wty V' Us (\<theta> x) (tsubst \<rho> (V x))" if "x \<in> R" for x
    using inst_typedD[OF \<theta>] that by (simp add: R_def)
  define dflt :: "ptyp \<Rightarrow> pterm" where "dflt T = Free (STR ''u'') T" for T
  define \<theta>f where "\<theta>f x = (if x \<in> R then freezeV fs Us 0 (\<theta> x)
    else if 0 \<le> snd x then dflt (tsubst \<rho> (V x)) else Bound (-1))" for x
  text \<open>The closed instance.\<close>
  have \<theta>f: "inst_typed V V'' [] \<rho> \<theta>f"
    unfolding inst_typed_def
  proof (intro allI impI)
    fix x :: indexname assume x: "0 \<le> snd x"
    show "wty V'' [] (\<theta>f x) (tsubst \<rho> (V x))"
    proof (cases "x \<in> R")
      case True
      have "has_type V'' [] (freezeV fs Us (integer_of_nat (length ([] :: ptyp list))) (\<theta> x)) (tsubst \<rho> (V x))"
        using wx[OF True] V''fs V''F fs(1) True
        by (intro has_type_freezeV[of V' "[] @ Us"]) (auto simp: wty_def F_def)
      moreover have "\<forall>v\<in>vars (freezeV fs Us 0 (\<theta> x)). 0 \<le> snd v"
        using vars_freezeV[of fs Us 0 "\<theta> x"] wx[OF True] fs(4) by (auto simp: wty_def)
      ultimately show ?thesis using True by (simp add: wty_def \<theta>f_def)
    qed (use x in \<open>simp add: \<theta>f_def dflt_def wty_def has_type.Free\<close>)
  qed
  have closed: "prf_ok V'' H [] [] (prf_inst \<rho> \<theta>f 0 p) (psubst \<rho> \<theta>f 0 \<phi>)"
  proof (rule prf_validD[OF P ws \<theta>f])
    fix t u assume tu: "(t, u) \<in> set tps"
    then obtain T where w: "wty V [] t T" "wty V [] u T" using tps by blast
    have tr_f: "tr (psubst \<rho> \<theta>f 0 s) = bsubst (map (\<lambda>f. code (AVar f)) fs) 0 (tr (psubst \<rho> \<theta> 0 s))"
      if "wty V [] s T" "vars s \<subseteq> vars t \<union> vars u" for s
    proof -
      have sR: "vars s \<subseteq> R" using that tu by (fastforce simp: R_def wty_def)
      have prx: "proper (\<theta> x)" if "x \<in> R" for x using wx[OF that] by (auto simp: wty_def intro: has_type_proper)
      have xx: "\<theta>f x = freezeV fs Us 0 (\<theta> x) \<and> proper (\<theta> x)" if "x \<in> vars s" for x
        using that sR prx by (auto simp: \<theta>f_def)
      have pr_s: "proper s" using that(1) by (auto simp: wty_def intro: has_type_proper)
      have lb: "\<not> loose_bvar s 0" using has_type_loose_bvar[of V "[]" s T] that(1) by (simp add: wty_def)
      have "tr (psubst \<rho> \<theta>f 0 s) = bsubst (map (\<lambda>f. code (AVar f)) fs) (nat_of_integer 0) (tr (psubst \<rho> \<theta> 0 s))"
        by (rule tr_psubst_freezeV[OF pr_s lb]) (simp_all add: xx)
      then show ?thesis by simp
    qed
    from sol tu have "tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)" by blast
    then show "tr (psubst \<rho> \<theta>f 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>f 0 u)"
      using tr_f[OF w(1)] tr_f[OF w(2)] by (auto intro: bsubst_equiv)
  qed
  text \<open>Only variables of non-negative index matter.\<close>
  have neg: "\<not> proper (\<theta>f x)" if "x \<notin> R" "snd x < 0" for x using that by (simp add: \<theta>f_def)
  have pv: "x \<in> R" if "x \<in> prf_vars p" for x
  proof (rule ccontr)
    assume "x \<notin> R"
    with that have "snd x < 0" by (auto simp: R_def)
    moreover have "proper (\<theta>f x)"
      using anns_proper_prf_vars[OF prf_ok_anns_proper[OF closed] _ that] by simp
    ultimately show False using neg \<open>x \<notin> R\<close> by blast
  qed
  have fv: "x \<in> R" if "x \<in> vars \<phi>" for x
  proof (rule ccontr)
    assume "x \<notin> R"
    with that have "snd x < 0" by (auto simp: R_def)
    moreover have "proper (\<theta>f x)"
      using prf_ok_wty[OF closed] that by (auto simp: wty_def dest: has_type_proper intro: proper_psubst_vars)
    ultimately show False using neg \<open>x \<notin> R\<close> by blast
  qed
  text \<open>Thawing.\<close>
  define \<theta>u where "\<theta>u y = (if y \<in> set fs then Bound (integer_of_nat (idx y))
    else if y \<in> F then Var y (V' y) else dflt (V'' y))" for y
  have \<theta>u: "inst_typed V'' V' Us TVar \<theta>u"
    unfolding inst_typed_def
  proof (intro allI impI)
    fix y :: indexname assume y: "0 \<le> snd y"
    show "wty V' Us (\<theta>u y) (tsubst TVar (V'' y))"
    proof (cases "y \<in> set fs")
      case True
      then obtain i where i: "i < length fs" "y = fs ! i" by (auto simp: in_set_conv_nth)
      then show ?thesis using fs(1) V''fs[of i] idx[of i]
        by (auto simp: \<theta>u_def wty_def tsubst_TVar has_type_Bound_iff integer_reps)
    next
      case False
      then show ?thesis using y by (auto simp: \<theta>u_def dflt_def wty_def tsubst_TVar V''_def intro: has_type.intros)
    qed
  qed
  from prf_ok_pinst[OF H \<theta>u closed]
  have th: "prf_ok V' H Us [] (prf_inst TVar \<theta>u 0 (prf_inst \<rho> \<theta>f 0 p)) (psubst TVar \<theta>u 0 (psubst \<rho> \<theta>f 0 \<phi>))"
    by simp
  have thaw: "psubst TVar \<theta>u 0 (\<theta>f x) = \<theta> x" if "x \<in> R" for x
  proof -
    have "psubst TVar \<theta>u (integer_of_nat (length ([] :: ptyp list)))
        (freezeV fs Us (integer_of_nat (length ([] :: ptyp list))) (\<theta> x)) = \<theta> x"
    proof (rule psubst_freezeV[of V' "[] @ Us"])
      show "has_type V' ([] @ Us) (\<theta> x) (tsubst \<rho> (V x))" using wx[OF that] by (simp add: wty_def)
      show "\<forall>i<length fs. \<theta>u (fs ! i) = Bound (integer_of_nat i)"
        using idx by (auto simp: \<theta>u_def)
      show "\<forall>y\<in>vars (\<theta> x). \<theta>u y = Var y (V' y)"
        using that fs(3) by (auto simp: \<theta>u_def F_def)
    qed (use fs(1) in simp_all)
    with that show ?thesis by (simp add: \<theta>f_def)
  qed
  have "prf_inst TVar \<theta>u 0 (prf_inst \<rho> \<theta>f 0 p) = prf_inst \<rho> \<theta> 0 p"
    unfolding prf_inst_prf_inst[OF order_refl] tsubst_TVar_comp
    by (rule prf_inst_cong) (simp add: thaw pv)
  moreover have "psubst TVar \<theta>u 0 (psubst \<rho> \<theta>f 0 \<phi>) = psubst \<rho> \<theta> 0 \<phi>"
    unfolding psubst_psubst[OF order_refl] tsubst_TVar_comp
    by (rule psubst_cong) (simp add: thaw fv)
  ultimately show "prf_ok V' H Us [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 \<phi>)" using th by simp
qed

corollary prf_valid_lift:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and inc: "0 \<le> inc" and P: "prf_valid alg V H tps pf (list_implies As B)"
    and tps: "\<forall>(t, u)\<in>set tps. \<exists>T. wty V [] t T \<and> wty V [] u T"
    and wR: "wty V [] (list_implies As B) propT"
    and G: "wty V2 [] G propT" and V2: "lift_venv (rev (lift_Ts [] G)) inc V V2"
  shows "prf_valid alg V2 H (map (\<lambda>(t, u). (lift_abs inc G t, lift_abs inc G u)) tps)
    (lift_proof G inc (map (lift_all inc G) As) pf) (list_implies (map (lift_all inc G) As) (lift_all inc G B))"
proof -
  have H': "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {})" using H by blast
  show ?thesis
    by (rule prf_valid_ctx_prf_valid[OF prf_valid_lift_proof[OF H inc prf_valid_prf_valid_ctx[OF H' P tps] wR G V2]])
qed

end

end
