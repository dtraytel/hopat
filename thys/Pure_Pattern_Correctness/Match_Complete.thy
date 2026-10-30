section \<open>Completeness of Matching\<close>

theory Match_Complete
  imports Match_Exceptions
begin

text \<open>
  If a matcher exists, matching succeeds. For higher-order matching, the matcher is an
  environment \<open>(tye, te)\<close> whose instance \<^const>\<open>minst\<close> of the pattern is \<open>\<beta>\<eta>\<close>-equivalent to
  an object without \<open>\<beta>\<close>-redexes. When a variable occurs again, \<^const>\<open>mtch\<close> compares the object
  with its binding by \<^const>\<open>aeconv\<close>, i.e. up to \<open>\<alpha>\<close>-equivalence after \<open>\<eta>\<close>-contraction, which also
  compares the types of bound variables. Both terms are then \<open>\<beta>\<eta>\<close>-equivalent, as a pattern
  variable applied to distinct bound variables determines its binding up to \<open>\<beta>\<eta>\<close>-conversion;
  their \<open>\<eta>\<close>-contractions are the \<open>\<beta>\<eta>\<close>-normal form, and well-typedness fixes the types of the
  bound variables. For first-order matching, the matcher instantiates the pattern to the object
  up to \<open>\<alpha>\<close>-equivalence, without \<open>\<beta>\<eta>\<close>-conversion.
\<close>

context csig
begin

declare sup_apply[simp del]

subsection \<open>Equivalence of de Bruijn terms\<close>

lemma subst_lift_Suc: "(lift t (Suc k))[BVar k/k] = t"
  by (induction t arbitrary: k) auto

lemma Abs_equiv_Abs: "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
proof -
  assume "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t"
  then have "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (dB.Abs t) 0 \<degree> BVar 0" by (simp add: fact6)
  moreover have "lift (dB.Abs t) 0 \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> t"
    using beta.beta[of "lift t (Suc 0)" "BVar 0"] by (simp add: subst_lift_Suc)
  then have "lift (dB.Abs t) 0 \<degree> BVar 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> t" by (intro beta_into_equiv r_into_rtranclp)
  ultimately show ?thesis by (rule equiv_trans)
qed

text \<open>A term without \<open>\<beta>\<close>-redexes only depends on the bound variables it contains:\<close>

lemma rfree_dep_on: "rfree t \<Longrightarrow> proper t \<Longrightarrow> dep_on Z (tr t) \<Longrightarrow> loose_BVars (tr t) \<subseteq> Z"
proof (induction t arbitrary: Z rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "Pure_Term.is_Abs t")
    case True
    then obtain a T u where t: "t = pterm.Abs a T u" by (cases t) auto
    from less.prems(3) have "dep_on (insert 0 (Suc ` Z)) (tr u)" by (simp add: t Abs_dep_on)
    with less.IH[of u] less.prems(1,2) have "loose_BVars (tr u) \<subseteq> insert 0 (Suc ` Z)" by (simp add: t)
    then show ?thesis by (auto simp: t)
  next
    case False
    obtain h ts where s: "strip_comb t = (h, ts)" by force
    have tc: "t = list_comb h ts" by (rule strip_comb_list_comb[OF s])
    have h: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF s])
    have rf: "\<forall>u\<in>set ts. rfree u" "ts \<noteq> [] \<longrightarrow> \<not> Pure_Term.is_Abs h"
      using less.prems(1) by (simp_all add: tc rfree_list_comb)
    have pr: "proper h" "\<forall>u\<in>set ts. proper u" using less.prems(2) by (simp_all add: tc proper_list_comb)
    have "\<not> Pure_Term.is_Abs h" using False rf(2) by (cases ts) (auto simp: tc)
    then have at: "is_atom (tr h)" using h pr(1) by (cases h) auto
    have dep: "dep_on Z (tr h \<degree>\<degree> map tr ts)" using less.prems(3) by (simp add: tc tr_list_comb)
    note ad = atom_apps_dep_on[OF at dep]
    have "loose_BVars (tr u) \<subseteq> Z" if "u \<in> set ts" for u
      using less.IH[OF strip_comb_arg(2)[OF s that]] rf(1) pr(2) ad(2) that by simp
    with ad(1) show ?thesis by (auto simp: tc tr_list_comb)
  qed
qed

lemma normal_AbsI:
  assumes "normal s" "\<And>f. s = f \<degree> BVar 0 \<Longrightarrow> free f 0"
  shows "normal (dB.Abs s)"
proof
  assume "\<exists>u. \<beta>\<eta> (dB.Abs s) u"
  then obtain u where "dB.Abs s \<rightarrow>\<^sub>\<beta> u \<or> dB.Abs s \<rightarrow>\<^sub>\<eta> u" by (auto simp: sup_apply)
  then show False
  proof
    assume "dB.Abs s \<rightarrow>\<^sub>\<beta> u"
    then show False using assms(1) by (auto simp: sup_apply)
  next
    assume "dB.Abs s \<rightarrow>\<^sub>\<eta> u"
    then show False using assms by (auto simp: sup_apply)
  qed
qed

lemma normal_AppI:
  assumes "normal s" "normal t" "\<And>r. s \<noteq> dB.Abs r"
  shows "normal (s \<degree> t)"
proof
  assume "\<exists>u. \<beta>\<eta> (s \<degree> t) u"
  then obtain u where "s \<degree> t \<rightarrow>\<^sub>\<beta> u \<or> s \<degree> t \<rightarrow>\<^sub>\<eta> u" by (auto simp: sup_apply)
  then show False using assms by (auto simp: sup_apply)
qed

lemma normal_AppD: "normal (s \<degree> t) \<Longrightarrow> normal s \<and> normal t"
  by (auto simp: sup_apply)

lemma normal_lift:
  assumes "normal (lift t k)" shows "normal t"
proof
  assume "\<exists>u. \<beta>\<eta> t u"
  then obtain u where "t \<rightarrow>\<^sub>\<beta> u \<or> t \<rightarrow>\<^sub>\<eta> u" by (auto simp: sup_apply)
  then have "lift t k \<rightarrow>\<^sub>\<beta> lift u k \<or> lift t k \<rightarrow>\<^sub>\<eta> lift u k" by auto
  with assms show False by (auto simp: sup_apply)
qed

lemma normal_equiv_eq: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> normal s \<Longrightarrow> normal t \<Longrightarrow> s = t"
  using equiv_\<beta>\<eta>cl_normal by (metis converse_rtranclpE)

lemma normal_atoms: "normal (dB.Var n)" "normal (BVar i)"
  by (auto simp: sup_apply)

text \<open>A closed term applied to distinct bound variables determines the term:\<close>

lemma apps_BVars_cancel:
  assumes "no_loose_bound s 0" "no_loose_bound s' 0" "distinct ns"
    "s \<degree>\<degree> map BVar ns \<equiv>\<^sub>\<beta>\<^sub>\<eta> s' \<degree>\<degree> map BVar ns"
  shows "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> s'"
proof -
  let ?m = "length ns"
  let ?g = "delta_map (\<lambda>_. True) ns (downs ?m)"
  have g: "map ?g ns = downs ?m" by (rule map_delta_map) (simp_all add: list_all2_iff assms(3))
  have m1: "map_BVars ?g s = s" "map_BVars ?g s' = s'"
    using map_BVars_no_loose assms(1,2) by blast+
  have "map (map_BVars ?g \<circ> BVar) ns = map BVar (map ?g ns)" by simp
  then have m2: "map (map_BVars ?g \<circ> BVar) ns = map BVar (downs ?m)" by (simp only: g)
  have "s \<degree>\<degree> map BVar (downs ?m) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s' \<degree>\<degree> map BVar (downs ?m)"
    using map_BVars_preserves_closure[OF assms(4), of ?g] by (simp add: m1 m2)
  then have "Abs_m ?m (s \<degree>\<degree> map BVar (downs ?m)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (s' \<degree>\<degree> map BVar (downs ?m))"
    by (rule equiv_Abs_m)
  with eta_expand_equiv[OF assms(1)] eta_expand_equiv[OF assms(2)] show ?thesis
    by (meson equiv_sym equiv_trans)
qed


subsection \<open>\<open>\<eta>\<close>-contraction\<close>

lemma loose_bvar1_tr:
  "proper t \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<longleftrightarrow> free (tr t) (nat_of_integer k)"
proof (induction t arbitrary: k)
  case (Bound i)
  then show ?case by (simp add: nat_of_integer_eq_iff)
next
  case (Abs a T t)
  have "nat_of_integer (k + 1) = Suc (nat_of_integer k)"
    using Abs.prems(2) nat_of_integer_add[of k 1] by simp
  with Abs.IH[of "k + 1"] Abs.prems show ?case by simp
qed auto

lemma decr_shape:
  "Pure_Term.is_Abs (Pure_Term.decr lev t) \<longleftrightarrow> Pure_Term.is_Abs t" "rfree (Pure_Term.decr lev t) \<longleftrightarrow> rfree t"
proof -
  have "Pure_Term.is_Abs (Pure_Term.decr lev t) \<longleftrightarrow> Pure_Term.is_Abs t" for lev t by (cases t) auto
  moreover then have "rfree (Pure_Term.decr lev t) \<longleftrightarrow> rfree t" for lev
    by (induction t arbitrary: lev) auto
  ultimately show "Pure_Term.is_Abs (Pure_Term.decr lev t) \<longleftrightarrow> Pure_Term.is_Abs t"
    "rfree (Pure_Term.decr lev t) \<longleftrightarrow> rfree t" by blast+
qed

lemma eta_contract_shape:
  "\<not> Pure_Term.is_Abs t \<Longrightarrow> \<not> Pure_Term.is_Abs (eta_contract t)" "rfree t \<Longrightarrow> rfree (eta_contract t)"
proof -
  show nA: "\<not> Pure_Term.is_Abs (eta_contract t)" if "\<not> Pure_Term.is_Abs t" for t
    using that by (cases t) auto
  show "rfree t \<Longrightarrow> rfree (eta_contract t)"
  proof (induction t)
    case (Abs a T body)
    then have "rfree (eta_contract body)" by simp
    then show ?case by (auto simp: Let_def decr_shape split: pterm.splits)
  qed (use nA in auto)
qed

lemma has_type_decr:
  "has_type W (Us @ A # Ts) f T \<Longrightarrow> \<not> loose_bvar1 f lev \<Longrightarrow> 0 \<le> lev \<Longrightarrow> nat_of_integer lev = length Us \<Longrightarrow>
    has_type W (Us @ Ts) (Pure_Term.decr lev f) T"
proof (induction f arbitrary: Us lev T)
  case (Bound i)
  then have i: "0 \<le> i" "nat_of_integer i < Suc (length Us + length Ts)" "T = (Us @ A # Ts) ! nat_of_integer i"
    by (simp_all add: has_type_Bound_iff)
  show ?case
  proof (cases "lev \<le> i")
    case True
    with Bound.prems(2) have "lev < i" by simp
    with Bound.prems(3,4) i have "length Us < nat_of_integer i" "0 \<le> i - 1"
      "nat_of_integer (i - 1) = nat_of_integer i - 1"
      by (simp_all add: nat_of_integer_less_iff[symmetric] integer_reps nat_of_integer_minus_1)
    with True i show ?thesis
      by (cases "nat_of_integer i") (auto simp: has_type_Bound_iff nth_append)
  next
    case False
    with Bound.prems(3) i(1) have "nat_of_integer i < nat_of_integer lev"
      by (simp add: nat_of_integer_less_iff)
    with Bound.prems(4) have "nat_of_integer i < length Us" by simp
    with False i show ?thesis by (simp add: has_type_Bound_iff nth_append)
  qed
next
  case (Abs a T0 t)
  from Abs.prems(1) obtain U where T: "T = T0 \<rightarrow>\<^sub>T U" and t: "has_type W ((T0 # Us) @ A # Ts) t U"
    by (auto elim: has_type_elims)
  have l: "0 \<le> lev + 1" "nat_of_integer (lev + 1) = length (T0 # Us)"
    using Abs.prems(3,4) nat_of_integer_add[of lev 1] by simp_all
  from Abs.IH[OF t _ l] Abs.prems(2) show ?case by (auto simp: T intro: has_type.Abs)
next
  case (App s u)
  from App.prems(1) obtain B where s: "has_type W (Us @ A # Ts) s (B \<rightarrow>\<^sub>T T)"
    and u: "has_type W (Us @ A # Ts) u B"
    by (auto elim: has_type_elims)
  from App.IH(1)[OF s _ App.prems(3,4)] App.IH(2)[OF u _ App.prems(3,4)] App.prems(2)
  show ?case by (auto intro: has_type.App)
qed (auto elim!: has_type_elims intro: has_type.intros)

lemma has_type_eta_contract: "has_type W Ts t T \<Longrightarrow> has_type W Ts (eta_contract t) T"
proof (induction t arbitrary: Ts T)
  case (Abs a T0 body)
  from Abs.prems obtain U where T: "T = T0 \<rightarrow>\<^sub>T U" and b: "has_type W (T0 # Ts) body U"
    by (auto elim: has_type_elims)
  have b': "has_type W (T0 # Ts) (eta_contract body) U" by (rule Abs.IH[OF b])
  show ?case
  proof (cases "\<exists>f. eta_contract body = f $ Bound 0 \<and> \<not> is_dependent f")
    case True
    then obtain f where e: "eta_contract body = f $ Bound 0" and nd: "\<not> is_dependent f" by blast
    from b' obtain U' where f: "has_type W (T0 # Ts) f (U' \<rightarrow>\<^sub>T U)" and "has_type W (T0 # Ts) (Bound 0) U'"
      by (auto simp: e elim: has_type_elims)
    then have "U' = T0" by (simp add: has_type_Bound_iff)
    with has_type_decr[of W "[]" T0 Ts f "U' \<rightarrow>\<^sub>T U" 0] f nd
    have "has_type W Ts (Pure_Term.decr 0 f) (T0 \<rightarrow>\<^sub>T U)" by (simp add: is_dependent_def)
    with e nd show ?thesis by (simp add: T)
  next
    case False
    then have "eta_contract (pterm.Abs a T0 body) = pterm.Abs a T0 (eta_contract body)"
      by (auto simp: Let_def split: pterm.splits)
    with b' show ?thesis by (simp add: T has_type.Abs del: eta_contract.simps)
  qed
next
  case (App s u)
  from App.prems obtain B where s: "has_type W Ts s (B \<rightarrow>\<^sub>T T)" and u: "has_type W Ts u B"
    by (auto elim: has_type_elims)
  show ?case using has_type.App[OF App.IH(1)[OF s] App.IH(2)[OF u]] by simp
qed simp_all

text \<open>\<open>\<eta>\<close>-contraction computes the \<open>\<beta>\<eta>\<close>-normal form of a term without \<open>\<beta>\<close>-redexes:\<close>

lemma normal_eta_contract: "proper t \<Longrightarrow> rfree t \<Longrightarrow> normal (tr (eta_contract t))"
proof (induction t)
  case (Abs a T body)
  let ?b = "eta_contract body"
  have pb: "proper ?b" and nb: "normal (tr ?b)"
    using Abs tr_eta_contract[of body] by simp_all
  show ?case
  proof (cases "\<exists>f. ?b = f $ Bound 0 \<and> \<not> is_dependent f")
    case True
    then obtain f where b: "?b = f $ Bound 0" and nd: "\<not> is_dependent f" by blast
    have pf: "proper f" using pb by (simp add: b)
    have d: "lift (tr (Pure_Term.decr 0 f)) 0 = tr f"
      using tr_decr[of f 0] pf nd by (simp add: is_dependent_def)
    have "normal (tr f)" using normal_AppD[of "tr f"] nb by (simp add: b)
    then have "normal (tr (Pure_Term.decr 0 f))" using normal_lift d by metis
    with b nd show ?thesis by simp
  next
    case False
    then have e: "eta_contract (pterm.Abs a T body) = pterm.Abs a T ?b"
      by (auto simp: Let_def split: pterm.splits)
    have "free g 0" if "tr ?b = g \<degree> BVar 0" for g
    proof -
      from that obtain f r where b0: "?b = f $ r" "tr f = g" "tr r = BVar 0"
        by (cases ?b) auto
      then obtain i where b: "?b = f $ Bound i" "tr f = g" "nat_of_integer i = 0"
        by (cases r) auto
      with pb have "i = 0" using nat_of_integer_eq_iff[of i 0] by simp
      with False b(1) have "is_dependent f" by blast
      with pb b show ?thesis using loose_bvar1_tr[of f 0] by (simp add: is_dependent_def)
    qed
    with nb e show ?thesis by (simp add: normal_AbsI del: eta_contract.simps)
  qed
next
  case (App s u)
  then have "normal (tr (eta_contract s))" "normal (tr (eta_contract u))" "\<not> Pure_Term.is_Abs s" by simp_all
  moreover have "\<not> Pure_Term.is_Abs (eta_contract s)" using eta_contract_shape(1) calculation(3) .
  then have "tr (eta_contract s) \<noteq> dB.Abs r" for r by (cases "eta_contract s") auto
  ultimately show ?case by (simp add: normal_AppI)
qed (simp_all add: normal_atoms)


subsection \<open>Alpha-equivalence\<close>


lemma aconv_sym: "aconv_term t u \<Longrightarrow> aconv_term u t"
  by (induction t u rule: aconv_term.induct) auto

lemma aconv_trans: "aconv_term t u \<Longrightarrow> aconv_term u v \<Longrightarrow> aconv_term t v"
proof (induction t u arbitrary: v rule: aconv_term.induct)
  case (1 t1 u1 t2 u2)
  then show ?case by (cases v) auto
next
  case (2 a T1 t1 b T2 t2)
  then show ?case by (cases v) auto
qed auto

lemma has_type_aconv: "aconv_term t u \<Longrightarrow> has_type W Ts t T \<Longrightarrow> has_type W Ts u T"
proof (induction t u arbitrary: Ts T rule: aconv_term.induct)
  case (1 t1 u1 t2 u2)
  from "1.prems"(2) obtain A where s: "has_type W Ts t1 (A \<rightarrow>\<^sub>T T)" and u: "has_type W Ts u1 A"
    by (auto elim: has_type_elims)
  from "1.prems"(1) have "aconv_term t1 t2" "aconv_term u1 u2" by simp_all
  from has_type.App[OF "1.IH"(1)[OF this(1) s] "1.IH"(2)[OF this(2) u]] show ?case .
next
  case (2 a T1 t1 b T2 t2)
  then show ?case by (auto elim!: has_type_elims intro: has_type.Abs)
qed auto


lemma aconv_is_open: "aconv_term t u \<Longrightarrow> is_open u \<longleftrightarrow> is_open t"
proof -
  have "aconv_term t u \<Longrightarrow> loose_bvar u k \<longleftrightarrow> loose_bvar t k" for k
    by (induction t u arbitrary: k rule: aconv_term.induct) auto
  then show "aconv_term t u \<Longrightarrow> is_open u \<longleftrightarrow> is_open t" by (simp add: is_open_def)
qed

text \<open>
  The translation forgets the types of bound variables. In a typed term without
  \<open>\<beta>\<close>-redexes they are determined by the type of the term:
\<close>

lemma has_type_tr_aconv:
  "has_type W Ts t T \<Longrightarrow> has_type W Ts u U \<Longrightarrow> tr t = tr u \<Longrightarrow> rfree t \<Longrightarrow>
    (\<not> Pure_Term.is_Abs t \<longrightarrow> T = U) \<and> (T = U \<longrightarrow> aconv_term t u)"
proof (induction t arbitrary: Ts T u U)
  case (Const a T0)
  then show ?case by (cases u) (auto elim!: has_type_elims simp: code_eq_iff)
next
  case (Free a T0)
  then show ?case by (cases u) (auto elim!: has_type_elims simp: code_eq_iff)
next
  case (Var x T0)
  then show ?case by (cases u) (auto elim!: has_type_elims simp: code_eq_iff)
next
  case (Bound i)
  then show ?case
    by (cases u) (auto simp: has_type_Bound_iff nat_of_integer_eq_iff)
next
  case (Abs a T0 t)
  from Abs.prems(3) obtain b T1 t' where u: "u = pterm.Abs b T1 t'" "tr t = tr t'" by (cases u) auto
  from Abs.prems(1) obtain R where T: "T = T0 \<rightarrow>\<^sub>T R" "has_type W (T0 # Ts) t R" by (auto elim: has_type_elims)
  from Abs.prems(2) obtain R' where U: "U = T1 \<rightarrow>\<^sub>T R'" "has_type W (T1 # Ts) t' R'"
    by (auto simp: u elim: has_type_elims)
  have "aconv_term t t'" if "T = U"
  proof -
    from that have e: "T1 = T0" "R' = R" by (simp_all add: T U)
    from U(2) have "has_type W (T0 # Ts) t' R" by (simp add: e)
    from Abs.IH[OF T(2) this u(2)] Abs.prems(4) show ?thesis by simp
  qed
  then show ?case by (simp add: u T U)
next
  case (App s t)
  from App.prems(3) obtain s' t' where u: "u = s' $ t'" "tr s = tr s'" "tr t = tr t'"
    by (cases u) auto
  from App.prems(1) obtain A where s: "has_type W Ts s (A \<rightarrow>\<^sub>T T)" and t: "has_type W Ts t A"
    by (auto elim: has_type_elims)
  from App.prems(2) obtain A' where s': "has_type W Ts s' (A' \<rightarrow>\<^sub>T U)" and t': "has_type W Ts t' A'"
    by (auto simp: u elim: has_type_elims)
  have r: "\<not> Pure_Term.is_Abs s" "rfree s" "rfree t" using App.prems(4) by simp_all
  from App.IH(1)[OF s s' u(2) r(2)] r(1) have "A = A'" "T = U" "aconv_term s s'" by simp_all
  moreover from App.IH(2)[OF t t' u(3) r(3)] this(1) have "aconv_term t t'" by simp
  ultimately show ?case by (simp add: u)
qed

text \<open>Typed terms without \<open>\<beta>\<close>-redexes that are \<open>\<beta>\<eta>\<close>-equivalent pass the test \<^const>\<open>aeconv\<close>:\<close>

lemma aeconv_typed:
  assumes "has_type W Ts t T" "has_type W Ts u T" "rfree t" "rfree u" "tr t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u"
  shows "aeconv t u"
proof -
  have p: "proper t" "proper u" using has_type_proper assms(1,2) by blast+
  have "tr (eta_contract t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (eta_contract u)"
    using tr_eta_contract[OF p(1)] tr_eta_contract[OF p(2)] assms(5) by (meson equiv_sym equiv_trans)
  then have "tr (eta_contract t) = tr (eta_contract u)"
    using normal_equiv_eq normal_eta_contract p assms(3,4) by blast
  then have "aconv_term (eta_contract t) (eta_contract u)"
    using has_type_tr_aconv[OF has_type_eta_contract[OF assms(1)] has_type_eta_contract[OF assms(2)]]
      eta_contract_shape(2)[OF assms(3)] by blast
  then show ?thesis by (simp add: aeconv_def)
qed


subsection \<open>Computed bindings\<close>

lemma has_type_mapbnd:
  assumes "ok (mapbnd f d t) t'" "has_type W (Us @ Ts) t T" "0 \<le> d" "nat_of_integer d = length Us"
    "\<forall>i j. 0 \<le> i \<longrightarrow> nat_of_integer i < length Ts \<longrightarrow> ok (f i) j \<longrightarrow>
      0 \<le> j \<and> nat_of_integer j < length Ts' \<and> Ts' ! nat_of_integer j = Ts ! nat_of_integer i"
  shows "has_type W (Us @ Ts') t' T"
  using assms
proof (induction f d t arbitrary: t' Us T rule: mapbnd.induct)
  case (1 f d i)
  from "1.prems"(2) have i: "0 \<le> i" "nat_of_integer i < length Us + length Ts"
    "T = (Us @ Ts) ! nat_of_integer i" by (simp_all add: has_type_Bound_iff)
  show ?case
  proof (cases "i < d")
    case True
    with "1.prems"(3) i(1) have "nat_of_integer i < nat_of_integer d"
      by (simp add: nat_of_integer_less_iff)
    with True "1.prems"(1,4) have "t' = Bound i" "nat_of_integer i < length Us" by simp_all
    with i show ?thesis by (simp add: has_type_Bound_iff nth_append)
  next
    case False
    with "1.prems"(1) obtain j where j: "ok (f (i - d)) j" "t' = Bound (j + d)" by auto
    have id: "0 \<le> i - d" "nat_of_integer (i - d) = nat_of_integer i - length Us"
      "length Us \<le> nat_of_integer i"
      using False "1.prems"(3,4) by (simp_all add: integer_reps nat_diff_distrib' flip: "1.prems"(4))
    moreover have "nat_of_integer (i - d) < length Ts" using id i(2) by simp
    ultimately have jj: "0 \<le> j" "nat_of_integer j < length Ts'"
      "Ts' ! nat_of_integer j = Ts ! (nat_of_integer i - length Us)"
      using "1.prems"(5)[rule_format, of "i - d" j] j(1) by simp_all
    have "nat_of_integer (j + d) = nat_of_integer j + length Us"
      using jj(1) "1.prems"(3,4) by (simp add: nat_of_integer_add)
    with jj i id(3) show ?thesis
      by (auto simp: j(2) has_type_Bound_iff nth_append intro: add_nonneg_nonneg[OF jj(1) "1.prems"(3)])
  qed
next
  case (2 f d s T0 t)
  from "2.prems"(1) obtain t'' where m: "ok (mapbnd f (d + 1) t) t''" and t': "t' = pterm.Abs s T0 t''"
    by auto
  from "2.prems"(2) obtain U where T: "T = T0 \<rightarrow>\<^sub>T U" and t: "has_type W ((T0 # Us) @ Ts) t U"
    by (auto elim: has_type_elims)
  have d1: "0 \<le> d + 1" "nat_of_integer (d + 1) = length (T0 # Us)"
    using "2.prems"(3,4) nat_of_integer_add[of d 1] by simp_all
  from "2.IH"[OF m t d1 "2.prems"(5)] show ?case by (simp add: t' T has_type.Abs)
next
  case (3 f d u1 u2)
  from "3.prems"(1) obtain v1 v2 where m: "ok (mapbnd f d u1) v1" "ok (mapbnd f d u2) v2"
    and t': "t' = v1 $ v2"
    by auto
  from "3.prems"(2) obtain A where u1: "has_type W (Us @ Ts) u1 (A \<rightarrow>\<^sub>T T)" and u2: "has_type W (Us @ Ts) u2 A"
    by (auto elim: has_type_elims)
  from "3.IH"(1)[OF m(1) u1 "3.prems"(3-5)] "3.IH"(2)[OF m(1)[folded return_def] m(2) u2 "3.prems"(3-5)]
  show ?case by (simp add: t' has_type.App)
qed (auto elim!: has_type_elims intro: has_type.intros)

lemma mapbnd_shape:
  "ok (mapbnd f d t) t' \<Longrightarrow> (Pure_Term.is_Abs t' \<longleftrightarrow> Pure_Term.is_Abs t) \<and> (rfree t' \<longleftrightarrow> rfree t)"
proof (induction f d t arbitrary: t' rule: mapbnd.induct)
  case (3 f d u1 u2)
  from "3.prems" obtain v1 v2 where m: "ok (mapbnd f d u1) v1" "ok (mapbnd f d u2) v2"
    and t': "t' = v1 $ v2"
    by auto
  from "3.IH"(1)[OF m(1)] "3.IH"(2)[OF m(1)[folded return_def] m(2)] show ?case by (simp add: t')
qed (auto split: if_splits)

lemma rfree_app: "rfree (app t is) \<longleftrightarrow> rfree t \<and> (is \<noteq> [] \<longrightarrow> \<not> Pure_Term.is_Abs t)"
  by (simp add: app_list_comb rfree_list_comb)

lemma rfree_mkabs: "ok (mkabs binders is t) u \<Longrightarrow> rfree u \<longleftrightarrow> rfree t"
  by (induction "is" arbitrary: u) (auto split: prod.splits)

text \<open>Typing of \<^const>\<open>red\<close>: the abstractions of \<open>t\<close> consumed so far have the types of \<open>js\<close>.\<close>

lemma has_type_red_other:
  assumes "\<not> (Pure_Term.is_Abs t \<and> is \<noteq> [])" "ok (red t is js) u"
    "\<forall>i\<in>set is \<union> set js. 0 \<le> i \<and> nat_of_integer i < length Ts"
    "has_type W (map (\<lambda>j. Ts ! nat_of_integer j) js) t (foldr fun_type (map (\<lambda>i. Ts ! nat_of_integer i) is) B)"
  shows "has_type W Ts u B"
proof (cases "is = [] \<and> js = []")
  case True
  with assms(2,4) show ?thesis using has_type_weaken[of W "[]" t B Ts] by (simp add: red_other[OF assms(1)])
next
  case False
  with assms(2) obtain t' where m: "ok (mapbnd (nth js) 0 t) t'" and u: "u = app t' is"
    by (auto simp: red_other[OF assms(1)] simp del: mapbnd.simps)
  have "has_type W ([] @ Ts) t' (foldr fun_type (map (\<lambda>i. Ts ! nat_of_integer i) is) B)"
    by (rule has_type_mapbnd[OF m]) (use assms(3,4) in \<open>auto simp: ok_nth\<close>)
  with assms(3) show ?thesis by (simp add: u has_type_app)
qed

lemma has_type_red:
  "ok (red t is js) u \<Longrightarrow> \<forall>i\<in>set is \<union> set js. 0 \<le> i \<and> nat_of_integer i < length Ts \<Longrightarrow>
    has_type W (map (\<lambda>j. Ts ! nat_of_integer j) js) t (foldr fun_type (map (\<lambda>i. Ts ! nat_of_integer i) is) B) \<Longrightarrow>
    has_type W Ts u B"
proof (induction t arbitrary: "is" js u)
  case (Abs a T s)
  show ?case
  proof (cases "is")
    case Nil
    show ?thesis using has_type_red_other[OF _ Abs.prems] Nil by simp
  next
    case (Cons i is')
    from Abs.prems(1) Cons have r: "ok (red s is' (i # js)) u" by simp
    from Abs.prems(3) Cons obtain R where "T = Ts ! nat_of_integer i"
      "has_type W (T # map (\<lambda>j. Ts ! nat_of_integer j) js) s R"
      "R = foldr fun_type (map (\<lambda>i. Ts ! nat_of_integer i) is') B"
      by (auto elim: has_type_elims)
    with Abs.IH[OF r] Abs.prems(2) Cons show ?thesis by simp
  qed
qed (rule has_type_red_other; simp)+

lemma red_shape: "ok (red t is js) u \<Longrightarrow> rfree t \<Longrightarrow> rfree u"
proof (induction t "is" js arbitrary: u rule: red.induct)
  case (1 a T s i "is" js)
  then show ?case by simp
next
  case (2 t)
  then show ?case by simp
qed (auto simp: rfree_app dest: mapbnd_shape simp del: mapbnd.simps)

lemma match_bind_typed:
  assumes "ok (match_bind itms binders x T is t) itms'" "has_type W (map snd binders) t U" "rfree t"
    "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders"
  obtains u where "itms' = vt_update (x, (T, u)) itms" "rfree u"
    "has_type W [] u (foldr fun_type (map (\<lambda>i. snd (binders ! nat_of_integer i)) is) U)"
proof (cases "is = []")
  case True
  have pt: "proper t" using has_type_proper[OF assms(2)] .
  with assms(1) True have "loose_bnos t = []" and up: "ok (update_new (x, (T, t)) itms) itms'"
    by (auto simp: match_bind_def split: if_splits)
  then have "no_loose_bound (tr t) 0"
    using set_loose_bnos[OF pt] loose_BVars_no_loose_bound[of "tr t" 0] by auto
  then have "has_type W [] t U" using has_type_strengthen[of W "[]" "map snd binders" t U] assms(2) by simp
  with ok_update_new[OF up[folded return_def]] True assms(3) that show ?thesis by simp
next
  case False
  let ?C = "rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) is)"
  from assms(1) False obtain t' u
    where t': "ok (if downto0 is (ilength binders - 1) then return t else mapbnd (idx is) 0 t) t'"
      and u: "ok (mkabs binders is t') u" and up: "ok (update_new (x, (T, u)) itms) itms'"
    by (auto simp: match_bind_def Let_def simp del: mapbnd.simps split: if_splits)
  have "has_type W ?C t' U \<and> rfree t'"
  proof (cases "downto0 is (ilength binders - 1)")
    case True
    with t' have tt: "t' = t" by simp
    from downto0_nats[OF True] have n: "nats is = downs (length binders)"
      by (simp add: ilength_eq)
    have "?C = rev (map (\<lambda>k. snd (binders ! k)) (nats is))" by (simp add: rev_map)
    also have "\<dots> = map snd binders" by (rule nth_equalityI) (simp_all add: n rev_map)
    finally have "?C = map snd binders" .
    with assms(2,3) show ?thesis by (simp add: tt)
  next
    case False
    with t' have mb: "ok (mapbnd (idx is) 0 t) t'" by simp
    have "has_type W ([] @ ?C) t' U"
    proof (rule has_type_mapbnd[OF mb])
      show "\<forall>i j. 0 \<le> i \<longrightarrow> nat_of_integer i < length (map snd binders) \<longrightarrow> ok (idx is i) j \<longrightarrow>
          0 \<le> j \<and> nat_of_integer j < length ?C \<and> ?C ! nat_of_integer j = map snd binders ! nat_of_integer i"
      proof (intro allI impI)
        fix i j assume i: "0 \<le> i" "nat_of_integer i < length (map snd binders)" and j: "ok (idx is i) j"
        from ok_idx_ren[OF j _ i(1)] assms(4) have jj: "0 \<le> j" "nat_of_integer j < length is"
          "ren (nats is) (nat_of_integer j) = nat_of_integer i" by auto
        then show "0 \<le> j \<and> nat_of_integer j < length ?C \<and> ?C ! nat_of_integer j = map snd binders ! nat_of_integer i"
          using i(2) by (auto simp: ren_def rev_nth)
      qed
    qed (use assms(2) in simp_all)
    with mapbnd_shape[OF mb] assms(3) show ?thesis by simp
  qed
  then have "has_type W [] u (foldr fun_type (map (\<lambda>i. snd (binders ! nat_of_integer i)) is) U)" "rfree u"
    using has_type_mkabs0[OF u assms(4)] rfree_mkabs[OF u] by simp_all
  with ok_update_new[OF up[folded return_def]] that show ?thesis by blast
qed


subsection \<open>Types of abstractions\<close>

lemma subst_type_bound:
  assumes "ok (subst_type tye T) T'" "\<forall>(v, S)\<in>tvars T. vt_lookup tye v = Some (S, \<rho> v S)"
  shows "T' = tsubst \<rho> T"
proof -
  have "ok (subst_type_aux tye T) T' \<Longrightarrow> T' = tsubst \<rho> T" using assms(2)
  proof (induction tye T arbitrary: T' rule: subst_type_aux.induct)
    case (1 tye a Ts)
    from "1.prems"(1) obtain Ts' where m: "ok (mapM (subst_type_aux tye) Ts) Ts'" and T': "T' = Type a Ts'"
      by auto
    have "Ts' = map (tsubst \<rho>) Ts" using m "1.IH" "1.prems"(2)
    proof (induction Ts arbitrary: Ts')
      case (Cons U Us)
      from Cons.prems(1) obtain U' Us' where "ok (subst_type_aux tye U) U'" "ok (mapM (subst_type_aux tye) Us) Us'"
        "Ts' = U' # Us'" by auto
      with Cons.IH[of Us'] Cons.prems(2,3) show ?case by auto
    qed simp
    then show ?case by (simp add: T')
  qed (auto simp: type_lookup_def split: option.splits if_splits)
  moreover have "T' = T \<and> tsubst \<rho> T = T" if "vt_is_empty tye" "ok (return T) T'"
  proof -
    have "tvars T = {}" using assms(2) that(1) by (fastforce simp: vt_is_empty_def vt_lookup.rep_eq)
    then have "tsubst \<rho> T = tsubst TVar T" by (intro tsubst_cong) auto
    with that(2) show ?thesis by simp
  qed
  ultimately show ?thesis using assms(1) by (auto simp: subst_type_def split: if_splits)
qed

text \<open>
  The type variables of the type of the head of an application, and the condition that the
  binder types of the abstractions that matching visits only contain type variables in \<open>V\<close> or
  in the types of the heads above them.
\<close>

fun htv :: "pterm \<Rightarrow> (indexname \<times> psort) set" where
  "htv (s $ t) = htv s"
| "htv (Const _ T) = tvars T"
| "htv (Free _ T) = tvars T"
| "htv (pterm.Var _ T) = tvars T"
| "htv _ = {}"

fun abs_bound :: "(indexname \<times> psort) set \<Rightarrow> pterm \<Rightarrow> bool" where
  "abs_bound V (pterm.Abs _ T t) \<longleftrightarrow> tvars T \<subseteq> V \<and> abs_bound V t"
| "abs_bound V (s $ t) \<longleftrightarrow> abs_bound V s \<and> abs_bound (V \<union> htv s) t"
| "abs_bound V _ \<longleftrightarrow> True"

lemma abs_bound_mono: "abs_bound V t \<Longrightarrow> V \<subseteq> V' \<Longrightarrow> abs_bound V' t"
proof (induction V t arbitrary: V' rule: abs_bound.induct)
  case (2 V s t)
  then show ?case by (auto intro: "2.IH"(2)[of "V' \<union> htv s"])
qed auto

lemma abs_bound_incr: "abs_bound V (incr t) \<longleftrightarrow> abs_bound V t" and htv_incr: "htv (incr t) = htv t"
proof -
  have "htv (incr_aux d t) = htv t" for d t by (induction d t rule: incr_aux.induct) auto
  moreover then have "abs_bound V (incr_aux d t) \<longleftrightarrow> abs_bound V t" for d
    by (induction d t arbitrary: V rule: incr_aux.induct) auto
  ultimately show "abs_bound V (incr t) \<longleftrightarrow> abs_bound V t" "htv (incr t) = htv t"
    by (simp_all add: incr_def)
qed

lemma htv_list_comb: "htv (list_comb h ts) = htv h"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma abs_bound_list_comb:
  "abs_bound V (list_comb h ts) \<longleftrightarrow> abs_bound V h \<and> (\<forall>t\<in>set ts. abs_bound (V \<union> htv h) t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def htv_list_comb)

lemma has_type_htv:
  "has_type W Ts t T \<Longrightarrow> rfree t \<Longrightarrow> \<not> Pure_Term.is_Abs t \<Longrightarrow> tvars T \<subseteq> htv t \<union> \<Union> (tvars ` set Ts)"
proof (induction t arbitrary: T)
  case (App s u)
  from App.prems(1) obtain A where s: "has_type W Ts s (A \<rightarrow>\<^sub>T T)" by (auto elim: has_type_elims)
  have "tvars (A \<rightarrow>\<^sub>T T) \<subseteq> htv s \<union> \<Union> (tvars ` set Ts)"
    by (rule App.IH(1)[OF s]) (use App.prems(2) in simp_all)
  then show ?case by auto
next
  case (Bound i)
  then have "T \<in> set Ts" by (auto simp: has_type_Bound_iff)
  then show ?case by auto
qed (auto elim!: has_type_elims)

lemma has_type_abs_bound:
  "has_type W Ts t T \<Longrightarrow> rfree t \<Longrightarrow> \<Union> (tvars ` set Ts) \<subseteq> V \<Longrightarrow>
    Pure_Term.is_Abs t \<longrightarrow> tvars T \<subseteq> V \<Longrightarrow> abs_bound V t"
proof (induction t arbitrary: Ts T V)
  case (Abs a T0 b)
  from Abs.prems(1) obtain R where T: "T = T0 \<rightarrow>\<^sub>T R" "has_type W (T0 # Ts) b R" by (auto elim: has_type_elims)
  with Abs.prems Abs.IH[OF T(2)] show ?case using has_type_htv[OF T(2)] by auto
next
  case (App s u)
  from App.prems(1) obtain A where s: "has_type W Ts s (A \<rightarrow>\<^sub>T T)" and u: "has_type W Ts u A"
    by (auto elim: has_type_elims)
  have r: "rfree s" "rfree u" "\<not> Pure_Term.is_Abs s" using App.prems(2) by simp_all
  have "tvars (A \<rightarrow>\<^sub>T T) \<subseteq> htv s \<union> \<Union> (tvars ` set Ts)" using has_type_htv[OF s r(1,3)] .
  then have "tvars A \<subseteq> V \<union> htv s" using App.prems(3) by auto
  with App.IH(1)[OF s r(1) App.prems(3)] App.IH(2)[OF u r(2), of "V \<union> htv s"] r(3) App.prems(3)
  show ?case by auto
qed auto

lemma foldr_fun_type_inj:
  "length Us = length Us' \<Longrightarrow> foldr fun_type Us T = foldr fun_type Us' T' \<Longrightarrow> Us = Us' \<and> T = T'"
  by (induction Us Us' rule: list_induct2) auto

text \<open>The type variables bound in a type environment:\<close>

definition tdom :: "tyenv \<Rightarrow> (indexname \<times> psort) set" where
  "tdom tye = {(v, S). vt_lookup tye v \<noteq> None}"

lemma tdom_mono: "textends tye tye' \<Longrightarrow> tdom tye \<subseteq> tdom tye'"
  by (auto simp: tdom_def textends_def)


subsection \<open>Higher-order matching\<close>

text \<open>
  The bindings of the variables \<open>X\<close> in a term environment are typed instances that agree with
  the matcher \<open>te\<close>:
\<close>

definition magrees :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> tinst \<Rightarrow> tenv \<Rightarrow> tenv \<Rightarrow> indexname set \<Rightarrow> bool" where
  "magrees W \<rho> te itms X \<longleftrightarrow> (\<forall>x\<in>X. \<forall>U u. vt_lookup itms x = Some (U, u) \<longrightarrow>
    U = W x \<and> rfree u \<and> has_type W [] u (tsubst \<rho> (W x)) \<and> tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> msub te (code (AVar x)))"

lemma magrees_mono: "magrees W \<rho> te itms X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> magrees W \<rho> te itms Y"
  unfolding magrees_def by blast

end

context wf_csig
begin

lemma typ_match_agrees:
  assumes "wft ar T" "wft ar (tsubst \<rho> T)" "tvars T \<subseteq> A" "scons A" "tagrees tye \<rho> A"
  shows "\<exists>tye'. typ_match alg T (tsubst \<rho> T) tye = return tye' \<and> tagrees tye' \<rho> A \<and> textends tye tye' \<and>
    tvars T \<subseteq> tdom tye'"
proof -
  have "tmatcher alg tye \<rho> T (tsubst \<rho> T)"
    using tagrees_mono[OF assms(5,3)] by (simp add: tmatcher_tagrees)
  moreover have "scons (tvars T)" using assms(3,4) unfolding scons_def by blast
  ultimately obtain tye' where tm: "typ_match alg T (tsubst \<rho> T) tye = return tye'"
    and "textends tye tye'" "\<forall>(v, S)\<in>tvars T. vt_lookup tye' v = Some (S, \<rho> v S)"
    "\<forall>v. vt_lookup tye' v \<noteq> None \<longrightarrow> vt_lookup tye v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars T)"
    using typ_match_complete[OF assms(1,2)] by blast
  moreover from this(2-4) have tmc: "tmcomplete \<rho> T tye tye'" by (simp add: tmcomplete_def)
  have "tagrees tye' \<rho> A" by (rule tagrees_step[OF assms(5,4,3) tmc])
  ultimately show ?thesis by (auto simp: tdom_def)
qed

lemma mtch_complete:
  assumes "ppat pt" "rfree ob" "no_loose_bound (tr pt) (length binders)"
    "\<forall>T\<in>ctys pt. wft ar T" "\<forall>T\<in>ctys ob. wft ar T" "tvs pt \<subseteq> A" "scons A"
    "tagrees (fst env) (mtinst tye) A" "abs_bound (tdom (fst env)) pt"
    "vtys pt \<subseteq> {(x, W x) | x. True}" "magrees W (mtinst tye) te (snd env) (vars pt)"
    "has_type W (map snd binders) ob Ob"
    "has_type (\<lambda>x. tsubst (mtinst tye) (W x)) (map snd binders) (inst (mtinst tye) pt) Ob"
    "mte_ok te" "minst (tye, te) pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
  shows "\<exists>env'. ok (mtch alg binders pt ob env) env' \<and> tagrees (fst env') (mtinst tye) A \<and>
    textends (fst env) (fst env') \<and> magrees W (mtinst tye) te (snd env') (vars pt) \<and>
    (\<forall>x b. vt_lookup (snd env') x = Some b \<longrightarrow> vt_lookup (snd env) x = Some b \<or> x \<in> vars pt)"
  using assms(1-6,8-13,15)
proof (induction "(pt, ob)" arbitrary: binders pt ob env Ob
    rule: wf_induct[OF wf_measures[of "[\<lambda>(pt, ob). nabs pt + nabs ob, \<lambda>(pt, ob). size pt + size ob]"]])
  case 1
  let ?\<rho> = "mtinst tye" and ?E = "(tye, te)" and ?W = "\<lambda>x. tsubst (mtinst tye) (W x)"
  define post where "post p e e' \<longleftrightarrow> tagrees (fst e') ?\<rho> A \<and> textends (fst e) (fst e') \<and>
    magrees W ?\<rho> te (snd e') (vars p) \<and>
    (\<forall>x b. vt_lookup (snd e') x = Some b \<longrightarrow> vt_lookup (snd e) x = Some b \<or> x \<in> vars p)" for p e e'
  have post_trans: "post p e e2" if "post p e e1" "post p e1 e2" for p e e1 e2
    using that unfolding post_def by (blast intro: textends_trans)
  have post_mono: "post p e e1" if "post q e e1" "vars q \<subseteq> vars p" "magrees W ?\<rho> te (snd e) (vars p)" for p q e e1
    using that unfolding post_def magrees_def by blast
  have IH: "\<exists>e'. ok (mtch alg binders' p q e) e' \<and> post p e e'"
    if "nabs p + nabs q < nabs pt + nabs ob \<or>
        nabs p + nabs q \<le> nabs pt + nabs ob \<and> size p + size q < size pt + size ob"
      "ppat p" "rfree q" "no_loose_bound (tr p) (length binders')"
      "\<forall>T\<in>ctys p. wft ar T" "\<forall>T\<in>ctys q. wft ar T" "tvs p \<subseteq> A" "tagrees (fst e) ?\<rho> A"
      "abs_bound (tdom (fst e)) p" "vtys p \<subseteq> {(x, W x) | x. True}" "magrees W ?\<rho> te (snd e) (vars p)"
      "has_type W (map snd binders') q O'" "has_type ?W (map snd binders') (inst ?\<rho> p) O'"
      "minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q"
    for binders' p q e O'
  proof -
    have "((p, q), (pt, ob)) \<in> measures [\<lambda>(pt, ob). nabs pt + nabs ob, \<lambda>(pt, ob). size pt + size ob]"
      using that(1) by (auto simp: order.order_iff_strict)
    with "1.hyps" that(2-14) show ?thesis unfolding post_def by blast
  qed
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have ppt: "proper pt" by (rule ppat_proper[OF prems(1)])
  have pob: "proper ob" by (rule has_type_proper[OF prems(11)])
  let ?Ts = "map snd binders"
  have "\<exists>env'. ok (mtch alg binders pt ob env) env' \<and> post pt env env'"
  proof (cases "Pure_Term.is_Abs pt")
    case pA: True
    then obtain ns Ts ts where pt: "pt = pterm.Abs ns Ts ts" by (cases pt) auto
    have ts: "ppat ts" "no_loose_bound (tr ts) (Suc (length binders))"
      "\<forall>T\<in>ctys ts. wft ar T" "tvs ts \<subseteq> A" "abs_bound (tdom (fst env)) ts"
      "vtys ts \<subseteq> {(x, W x) | x. True}" "magrees W ?\<rho> te (snd env) (vars ts)"
      and tvT: "tvars Ts \<subseteq> tdom iTs"
      using prems ppat_AbsD[of ns Ts ts] by (auto simp: pt e)
    from prems(12) obtain Ob1 where Ob: "Ob = tsubst ?\<rho> Ts \<rightarrow>\<^sub>T Ob1"
      and ti: "has_type ?W (tsubst ?\<rho> Ts # ?Ts) (inst ?\<rho> ts) Ob1"
      by (auto simp: pt elim: has_type_elims)
    have pv: "post pt env e' \<longleftrightarrow> post ts env e'" for e' by (simp add: post_def pt)
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      from prems(11) obtain Ob2 where "Ob = Tt \<rightarrow>\<^sub>T Ob2" and tt: "has_type W (Tt # ?Ts) tt Ob2"
        by (auto simp: ob elim: has_type_elims)
      with Ob have Tt: "Tt = tsubst ?\<rho> Ts" "Ob2 = Ob1" by simp_all
      have eq: "mtch alg binders pt ob env = mtch alg ((nt, Tt) # binders) ts tt env"
        by (subst mtch.simps) (simp add: e pt ob)
      have q: "rfree tt" "\<forall>T\<in>ctys tt. wft ar T" using prems(2,5) by (simp_all add: ob)
      have eqv: "minst ?E ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr tt"
        using Abs_equiv_Abs[of "minst ?E ts" "tr tt"] prems(13) by (simp add: pt ob minst_simps)
      have "\<exists>e'. ok (mtch alg ((nt, Tt) # binders) ts tt env) e' \<and> post ts env e'"
        by (rule IH[where O' = Ob1]) (use eqv ts q tt ti prems(7) Tt in \<open>simp_all add: pt ob\<close>)
      then show ?thesis unfolding eq pv .
    next
      case oA: False
      have bnd: "\<forall>(v, S)\<in>tvars Ts. vt_lookup iTs v = Some (S, ?\<rho> v S)"
        using tvT prems(6,7) by (fastforce simp: pt e tagrees_def tdom_def split: option.splits)
      then have "\<forall>(v, S)\<in>tvars Ts. \<forall>S' U. vt_lookup iTs v = Some (S', U) \<longrightarrow> S' = S" by auto
      then obtain Tt where st: "ok (subst_type iTs Ts) Tt" using subst_type_ok by blast
      have Tt: "Tt = tsubst ?\<rho> Ts" by (rule subst_type_bound[OF st bnd])
      have eq: "mtch alg binders pt ob env = mtch alg ((ns, Tt) # binders) ts (incr ob $ Bound 0) env"
        by (subst mtch.simps) (simp add: e pt oA st)
      have q: "rfree (incr ob $ Bound 0)" "\<forall>T\<in>ctys (incr ob $ Bound 0). wft ar T"
        using prems(2,5) oA by (simp_all add: rfree_incr is_Abs_incr ctys_incr)
      have tq: "has_type W (Tt # ?Ts) (incr ob $ Bound 0) Ob1"
        using has_type_incr[OF prems(11), of Tt] by (auto simp: Ob Tt intro!: has_type.App has_type.Bound)
      have eqv: "minst ?E ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (incr ob $ Bound 0)"
        using prems(13) by (simp add: pt minst_simps fact6 tr_incr[OF pob])
      have "\<exists>e'. ok (mtch alg ((ns, Tt) # binders) ts (incr ob $ Bound 0) env) e' \<and> post ts env e'"
        by (rule IH[where O' = Ob1]) (use eqv ts q tq ti prems(7) Tt in \<open>simp_all add: pt nabs_incr\<close>)
      then show ?thesis unfolding eq pv .
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      from prems(11) obtain Ob1 where Ob: "Ob = Tt \<rightarrow>\<^sub>T Ob1" and tt: "has_type W (Tt # ?Ts) tt Ob1"
        by (auto simp: ob elim: has_type_elims)
      have eq: "mtch alg binders pt ob env = mtch alg ((nt, Tt) # binders) (incr pt $ Bound 0) tt env"
        by (subst mtch.simps) (simp add: e pA ob)
      have p: "ppat (incr pt $ Bound 0)"
        "no_loose_bound (tr (incr pt $ Bound 0)) (Suc (length binders))"
        "\<forall>T\<in>ctys (incr pt $ Bound 0). wft ar T" "tvs (incr pt $ Bound 0) \<subseteq> A"
        "abs_bound (tdom (fst env)) (incr pt $ Bound 0)" "vtys (incr pt $ Bound 0) \<subseteq> {(x, W x) | x. True}"
        "magrees W ?\<rho> te (snd env) (vars (incr pt $ Bound 0))"
        using ppat_incr_Bound0[OF prems(1) pA] prems(3,4,6,8,9,10) no_loose_bound_lift[OF prems(3) le0]
        by (simp_all add: tr_incr[OF ppt] ctys_incr vars_incr abs_bound_incr)
      have q: "rfree tt" "\<forall>T\<in>ctys tt. wft ar T" using prems(2,5) by (simp_all add: ob)
      have tp: "has_type ?W (Tt # ?Ts) (inst ?\<rho> (incr pt $ Bound 0)) Ob1"
        using has_type_incr[OF prems(12), of Tt]
        by (auto simp: Ob Poly_Inst.inst_incr intro!: has_type.App has_type.Bound)
      have eqv: "minst ?E (incr pt $ Bound 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr tt"
      proof -
        have "minst ?E (incr pt $ Bound 0) = lift (minst ?E pt) 0 \<degree> BVar 0"
          by (simp add: minst_simps minst_incr[OF _ ppt] assms(14))
        moreover have "tr tt \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (minst ?E pt) 0 \<degree> BVar 0"
          using equiv_sym[OF prems(13)] by (simp add: ob fact6)
        ultimately show ?thesis by (simp add: equiv_sym)
      qed
      have "\<exists>e'. ok (mtch alg ((nt, Tt) # binders) (incr pt $ Bound 0) tt env) e' \<and>
          post (incr pt $ Bound 0) env e'"
        by (rule IH[where O' = Ob1]) (use eqv p q tt tp prems(7) in \<open>simp_all add: ob nabs_incr\<close>)
      moreover have "post (incr pt $ Bound 0) env e' \<longleftrightarrow> post pt env e'" for e'
        by (simp add: post_def vars_incr)
      ultimately show ?thesis unfolding eq by simp
    next
      case oA: False
      obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
      have obc: "ob = list_comb oh oargs" by (rule strip_comb_list_comb[OF so])
      have ohh: "\<not> (\<exists>f u. oh = f $ u)" by (rule strip_comb_head[OF so])
      have orf: "\<forall>q\<in>set oargs. rfree q" "oargs \<noteq> [] \<longrightarrow> \<not> Pure_Term.is_Abs oh"
        using prems(2) by (simp_all add: obc rfree_list_comb)
      have opr: "proper oh" "\<forall>q\<in>set oargs. proper q" using pob by (simp_all add: obc proper_list_comb)
      have "\<not> Pure_Term.is_Abs oh" using oA orf(2) by (cases oargs) (auto simp: obc)
      then have oat: "is_atom (tr oh)" using ohh opr(1) by (cases oh) auto
      have ow: "\<forall>q\<in>set oargs. \<forall>T\<in>ctys q. wft ar T" "\<forall>T\<in>ctys oh. wft ar T"
        using prems(5) by (auto simp: obc ctys_list_comb)
      show ?thesis
      proof (cases rule: ppat_nonAbsE[OF prems(1) pA, case_names rigid flex])
        case (flex x T iss)
        have sp: "strip_comb pt = (pterm.Var x T, map Bound iss)"
          by (simp add: flex app_list_comb strip_comb_list_comb_eq)
        have io: "ok (ints_of (map Bound iss)) iss" using flex(2) by (simp add: ok_ints_of)
        have xv: "x \<in> vars pt" by (simp add: flex app_list_comb vars_list_comb)
        have T: "T = W x" using prems(9) by (auto simp: flex app_list_comb vtys_list_comb)
        have lt: "\<forall>i\<in>set iss. 0 \<le> i \<and> nat_of_integer i < length binders"
          using prems(3) flex(3) no_loose_bound_BVars[of "tr pt" "length binders"]
          by (auto simp: flex loose_BVars_tr_app)
        have ty: "tsubst ?\<rho> (W x) = foldr fun_type (map (\<lambda>i. ?Ts ! nat_of_integer i) iss) Ob"
          using prems(12) by (auto simp: flex Poly_Inst.inst_app has_type_app T elim: has_type_elims)
        have mi: "minst ?E pt = msub te (code (AVar x)) \<degree>\<degree> map BVar (nats iss)"
          by (simp add: flex app_list_comb minst_list_comb minst_simps comp_def)
        have cl: "no_loose_bound (msub te (code (AVar x))) 0"
          by (rule closed_onD[OF closed_msub[OF assms(14), of UNIV] UNIV_I])
        have dn: "distinct (nats iss)"
          using flex(2,3) inj_on_nat_of_integer[of "set iss"] by (simp add: distinct_map)
        show ?thesis
        proof (cases "vt_lookup itms x")
          case None
          then have lk: "ok (lookup1 itms x T) None" by (simp add: lookup1_def)
          have "loose_BVars (minst ?E pt) \<subseteq> set (nats iss)" using cl by (auto simp: mi no_loose_bound_loose_BVars)
          then have "dep_on (set (nats iss)) (tr ob)" by (rule dep_onI[OF equiv_sym[OF prems(13)]])
          then have "loose_BVars (tr ob) \<subseteq> set (nats iss)" by (rule rfree_dep_on[OF prems(2) pob])
          then obtain itms' where mb: "ok (match_bind itms binders x T iss ob) itms'"
            using match_bind_ok[OF pob _ lt None] by blast
          obtain u where u: "itms' = vt_update (x, (T, u)) itms" "rfree u"
            "has_type W [] u (foldr fun_type (map (\<lambda>i. snd (binders ! nat_of_integer i)) iss) Ob)"
            using match_bind_typed[OF mb prems(11,2) lt] by blast
          obtain u2 where u2: "itms' = vt_update (x, (T, u2)) itms" "no_loose_bound (tr u2) 0"
            "tr u2 \<degree>\<degree> map BVar (nats iss) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
            using match_bind_sound[OF mb pob flex(3)] by blast
          have "u2 = u" using arg_cong[OF u2(1), of "\<lambda>m. vt_lookup m x"] u(1) by simp
          note u2 = u2[unfolded this]
          have "tr u \<degree>\<degree> map BVar (nats iss) \<equiv>\<^sub>\<beta>\<^sub>\<eta> msub te (code (AVar x)) \<degree>\<degree> map BVar (nats iss)"
            using equiv_trans[OF u2(3) equiv_sym[OF prems(13)]] by (simp add: mi)
          then have ag: "tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> msub te (code (AVar x))" by (rule apps_BVars_cancel[OF u2(2) cl dn])
          have mm: "map (\<lambda>i. snd (binders ! nat_of_integer i)) iss = map (\<lambda>i. ?Ts ! nat_of_integer i) iss"
            using lt by simp
          have "has_type W [] u (tsubst ?\<rho> (W x))" using u(3) unfolding ty mm .
          with u(2) ag T have "magrees W ?\<rho> te itms' (vars pt)"
            using prems(10) by (auto simp: magrees_def e u(1))
          moreover have "ok (mtch alg binders pt ob env) (iTs, itms')"
            by (subst mtch.simps) (simp add: e pA oA sp io lk mb)
          ultimately show ?thesis using prems(7) xv by (auto simp: post_def e u(1))
        next
          case (Some b)
          then obtain U u where lku: "vt_lookup itms x = Some (U, u)" by (cases b) auto
          with prems(10) xv have U: "U = W x" and ru: "rfree u"
            and tu: "has_type W [] u (tsubst ?\<rho> (W x))" and ag: "tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> msub te (code (AVar x))"
            by (auto simp: magrees_def e)
          have lk: "ok (lookup1 itms x T) (Some u)" using lku U T by (simp add: lookup1_def)
          have pu: "proper u" "no_loose_bound (tr u) (length [])"
            using has_type_proper[OF tu] has_type_closed[OF tu] by simp_all
          obtain u' where rd: "ok (red u iss []) u'" using red_ok[OF pu] by blast
          have "has_type W ?Ts u' Ob"
            by (rule has_type_red[OF rd]) (use lt tu ty in simp_all)
          moreover have "rfree u'" by (rule red_shape[OF rd ru])
          moreover have "tr ob \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u'"
          proof -
            have "tr u' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u \<degree>\<degree> map BVar (nats iss)"
              using red_sound[OF rd pu(1)] pu(2) flex(3) by simp
            moreover have "tr u \<degree>\<degree> map BVar (nats iss) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
              using closure\<beta>\<eta>_list_application[OF ag, of "map BVar (nats iss)"] prems(13)
              by (simp add: mi)
            ultimately show ?thesis by (meson equiv_sym equiv_trans)
          qed
          ultimately have ae: "aeconv ob u'" using aeconv_typed[OF prems(11) _ prems(2)] by blast
          have "ok (mtch alg binders pt ob env) env"
            by (subst mtch.simps) (simp add: e pA oA sp io lk rd ae)
          then show ?thesis using prems(7,10) by (auto simp: post_def e)
        qed
      next
        case (rigid h ts)
        have hh: "\<not> (\<exists>f u. h = f $ u)" by (rule is_rigid_not_App[OF rigid(1)])
        have sp: "strip_comb pt = (h, ts)" by (simp add: rigid(2) strip_comb_list_comb_eq[OF hh])
        have hnv: "\<not> is_Var h" using rigid(1) by (auto simp: is_rigid_def)
        have hat: "is_atom (minst ?E h)" using rigid(1) by (auto simp: is_rigid_def minst_simps)
        have "minst ?E h \<degree>\<degree> map (minst ?E) ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr oh \<degree>\<degree> map tr oargs"
          using prems(13) by (simp add: rigid(2) obc minst_list_comb tr_list_comb)
        from atom_apps_equiv[OF hat oat this]
        have hd: "minst ?E h = tr oh" and l2: "list_all2 (\<lambda>p q. minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q) ts oargs"
          by (simp_all add: list_all2_map1 list_all2_map2)
        have len: "length ts = length oargs" using l2 by (rule list_all2_lengthD)
        text \<open>The instance of the head is the head of the object, so the arguments have the same types:\<close>
        have ih: "inst ?\<rho> h = oh"
          using rigid(1) hd opr(1) by (cases h; cases oh) (auto simp: is_rigid_def minst_simps code_eq_iff nat_of_integer_eq_iff)
        from prems(12) obtain Us where hU: "has_type ?W ?Ts oh (foldr fun_type Us Ob)"
          and aU: "list_all2 (has_type ?W ?Ts) (map (inst ?\<rho>) ts) Us"
          by (auto simp: rigid(2) Poly_Inst.inst_list_comb has_type_list_comb ih)
        from prems(11) obtain Us' where hU': "has_type W ?Ts oh (foldr fun_type Us' Ob)"
          and aU': "list_all2 (has_type W ?Ts) oargs Us'"
          by (auto simp: obc has_type_list_comb)
        have "foldr fun_type Us Ob = foldr fun_type Us' Ob"
          using hU hU' ih rigid(1) by (cases h) (auto simp: is_rigid_def elim!: has_type_elims)
        moreover have "length Us = length Us'"
          using aU aU' len by (auto dest!: list_all2_lengthD)
        ultimately have "Us = Us'" using foldr_fun_type_inj by blast
        with aU aU' l2 have l3: "list_all2 (\<lambda>p q. minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q \<and>
            (\<exists>U. has_type ?W ?Ts (inst ?\<rho> p) U \<and> has_type W ?Ts q U)) ts oargs"
          by (fastforce simp: list_all2_conv_all_nth)
        have pts: "ppat p" "no_loose_bound (tr p) (length binders)" "\<forall>T\<in>ctys p. wft ar T"
          "tvs p \<subseteq> A" "vtys p \<subseteq> {(x, W x) | x. True}" "vars p \<subseteq> vars pt"
          "abs_bound (tdom iTs \<union> htv h) p" if "p \<in> set ts" for p
          using that rigid(3) prems(3,4,6,8,9)
          by (auto simp: rigid(2) e tr_list_comb no_loose_bound_list_app ctys_list_comb
            tvs_list_comb vars_list_comb vtys_list_comb abs_bound_list_comb)
        text \<open>The arguments are matched from left to right:\<close>
        have args: "\<exists>e'. ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ps qs) e) e' \<and> post pt e e'"
          if "list_all2 (\<lambda>p q. minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q \<and>
              (\<exists>U. has_type ?W ?Ts (inst ?\<rho> p) U \<and> has_type W ?Ts q U)) ps qs"
            "set ps \<subseteq> set ts" "set qs \<subseteq> set oargs" "tagrees (fst e) ?\<rho> A"
            "tdom iTs \<union> htv h \<subseteq> tdom (fst e)" "magrees W ?\<rho> te (snd e) (vars pt)"
          for ps qs e
          using that
        proof (induction ps qs arbitrary: e rule: list_all2_induct)
          case Nil
          then show ?case by (auto simp: post_def)
        next
          case (Cons p ps q qs)
          have p: "p \<in> set ts" "q \<in> set oargs" using Cons.prems(1,2) by auto
          note ap = strip_comb_arg[OF sp p(1)] and aq = strip_comb_arg[OF so p(2)]
          from Cons.hyps(1) obtain U where U: "has_type ?W ?Ts (inst ?\<rho> p) U" "has_type W ?Ts q U"
            and eqv: "minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q" by blast
          have "\<exists>e1. ok (mtch alg binders p q e) e1 \<and> post p e e1"
          proof (rule IH[where O' = U])
            show "abs_bound (tdom (fst e)) p" using abs_bound_mono[OF pts(7)[OF p(1)] Cons.prems(4)] .
            show "magrees W ?\<rho> te (snd e) (vars p)" using magrees_mono[OF Cons.prems(5) pts(6)[OF p(1)]] .
          qed (use pts[OF p(1)] orf(1) ow(1) p U eqv Cons.prems(3) ap aq in auto)
          then obtain e1 where e1: "ok (mtch alg binders p q e) e1" "post pt e e1"
            using post_mono[OF _ pts(6)[OF p(1)] Cons.prems(5)] by blast
          then have "tagrees (fst e1) ?\<rho> A" "tdom iTs \<union> htv h \<subseteq> tdom (fst e1)"
            "magrees W ?\<rho> te (snd e1) (vars pt)"
            using Cons.prems(4) tdom_mono[of "fst e" "fst e1"] by (auto simp: post_def)
          from Cons.IH[OF _ _ this] Cons.prems(1,2) obtain e' where
            e': "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ps qs) e1) e'" "post pt e1 e'"
            by auto
          have "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip (p # ps) (q # qs)) e) e'"
            using e1(1) e'(1) by auto
          with post_trans[OF e1(2) e'(2)] show ?case by blast
        qed
        have hdl: "ok (handle (zip_eq ts oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). mtch alg binders p q) pqs e))
            (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) e'"
          if "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) e) e'" for e e'
          using that len by (simp add: ok_handle ok_zip_eq)
        text \<open>After matching the type of a constant or free variable head:\<close>
        have head: "\<exists>e'. ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) (iTs', itms)) e' \<and>
            post pt env e'"
          if "tagrees iTs' ?\<rho> A" "textends iTs iTs'" "htv h \<subseteq> tdom iTs'" for iTs'
        proof -
          have "tdom iTs \<union> htv h \<subseteq> tdom iTs'" using that(2,3) tdom_mono by blast
          with args[OF l3 order.refl order.refl, of "(iTs', itms)"] that(1) prems(10) obtain e' where
            "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) (iTs', itms)) e'" "post pt (iTs', itms) e'"
            by (auto simp: e)
          moreover have "post pt env (iTs', itms)" using that(1,2) prems(10) by (simp add: post_def e)
          ultimately show ?thesis using post_trans by blast
        qed
        have tm_head: "\<exists>iTs'. typ_match alg Ta (tsubst ?\<rho> Ta) iTs = return iTs' \<and>
            tagrees iTs' ?\<rho> A \<and> textends iTs iTs' \<and> tvars Ta \<subseteq> tdom iTs'"
          if "wft ar Ta" "wft ar (tsubst ?\<rho> Ta)" "tvars Ta \<subseteq> A" for Ta
          using typ_match_agrees[OF that assms(7)] prems(7) by (simp add: e)
        show ?thesis
        proof (cases h)
          case h: (Const a Ta)
          with ih have oh: "oh = Const a (tsubst ?\<rho> Ta)" by simp
          have w: "wft ar Ta" "wft ar (tsubst ?\<rho> Ta)" "tvars Ta \<subseteq> A"
            using prems(4,6) ow(2) by (auto simp: rigid(2) h oh ctys_list_comb tvs_list_comb)
          from tm_head[OF w] obtain iTs' where tm: "typ_match alg Ta (tsubst ?\<rho> Ta) iTs = return iTs'"
            and r: "tagrees iTs' ?\<rho> A" "textends iTs iTs'" "tvars Ta \<subseteq> tdom iTs'" by blast
          from head[OF r(1,2)] r(3) obtain e' where
            f: "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) (iTs', itms)) e'" "post pt env e'"
            by (auto simp: h)
          have "ok (mtch alg binders pt ob env) e'"
            by (subst mtch.simps) (simp add: e pA oA sp so h oh hnv tm[unfolded return_def] hdl[OF f(1)])
          with f(2) show ?thesis by blast
        next
          case h: (Free a Ta)
          with ih have oh: "oh = Free a (tsubst ?\<rho> Ta)" by simp
          have w: "wft ar Ta" "wft ar (tsubst ?\<rho> Ta)" "tvars Ta \<subseteq> A"
            using prems(4,6) ow(2) by (auto simp: rigid(2) h oh ctys_list_comb tvs_list_comb)
          from tm_head[OF w] obtain iTs' where tm: "typ_match alg Ta (tsubst ?\<rho> Ta) iTs = return iTs'"
            and r: "tagrees iTs' ?\<rho> A" "textends iTs iTs'" "tvars Ta \<subseteq> tdom iTs'" by blast
          from head[OF r(1,2)] r(3) obtain e' where
            f: "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) (iTs', itms)) e'" "post pt env e'"
            by (auto simp: h)
          have "ok (mtch alg binders pt ob env) e'"
            by (subst mtch.simps) (simp add: e pA oA sp so h oh hnv tm[unfolded return_def] hdl[OF f(1)])
          with f(2) show ?thesis by blast
        next
          case h: (Bound i)
          with ih have oh: "oh = Bound i" by simp
          from head[of iTs] prems(7) obtain e' where
            f: "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) env) e'" "post pt env e'"
            by (auto simp: h e)
          have "ok (mtch alg binders pt ob env) e'"
            using hdl[OF f(1)] by (subst mtch.simps) (simp add: e pA oA sp so h oh)
          with f(2) show ?thesis by blast
        qed (use rigid(1) hh in \<open>auto simp: is_rigid_def\<close>)
      qed
    qed
  qed
  then show ?case by (simp only: post_def)
qed

end


subsection \<open>First-order matching\<close>

text \<open>
  The first-order instance of a term under a matching environment substitutes the bindings of
  the variables (without \<open>\<beta>\<close>-reduction) and instantiates the types:
\<close>

context csig
begin

fun finst :: "match_env \<Rightarrow> pterm \<Rightarrow> pterm" where
  "finst env (pterm.Var x T) =
    (case vt_lookup (snd env) x of Some (_, u) \<Rightarrow> u | None \<Rightarrow> pterm.Var x (tsubst (mtinst (fst env)) T))"
| "finst env (Const a T) = Const a (tsubst (mtinst (fst env)) T)"
| "finst env (Free a T) = Free a (tsubst (mtinst (fst env)) T)"
| "finst env (Bound i) = Bound i"
| "finst env (pterm.Abs a T t) = pterm.Abs a (tsubst (mtinst (fst env)) T) (finst env t)"
| "finst env (s $ t) = finst env s $ finst env t"

text \<open>It translates to the instance \<^const>\<open>minst\<close>, i.e. it is a matcher without \<open>\<beta>\<eta>\<close>-conversion:\<close>

lemma tr_finst: "tr (finst env t) = minst env t"
  by (induction t) (simp_all add: minst_simps split: option.splits)

text \<open>The bindings of the variables \<open>X\<close> agree with the first-order instance:\<close>

definition fagrees :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> match_env \<Rightarrow> tenv \<Rightarrow> indexname set \<Rightarrow> bool" where
  "fagrees W E itms X \<longleftrightarrow>
    (\<forall>x\<in>X. \<forall>U u. vt_lookup itms x = Some (U, u) \<longrightarrow> U = W x \<and> aconv_term (finst E (pterm.Var x U)) u)"

end

context wf_csig
begin

lemma fo_mtch_complete:
  assumes "aconv_term (finst (tye, te) pt) ob"
    "\<forall>T\<in>tys pt. wft ar T" "\<forall>T\<in>tys ob. wft ar T" "tvs pt \<subseteq> A" "scons A"
    "tagrees (fst env) (mtinst tye) A" "vtys pt \<subseteq> {(x, W x) | x. True}"
    "fagrees W (tye, te) (snd env) (vars pt)"
    "\<forall>x\<in>vars pt. \<forall>U u. vt_lookup te x = Some (U, u) \<longrightarrow> has_type W [] u (tsubst (mtinst tye) (W x))"
    "mte_ok te"
  shows "\<exists>env'. ok (fo_mtch alg inAbs env pt ob) env' \<and> tagrees (fst env') (mtinst tye) A \<and>
    fagrees W (tye, te) (snd env') (vars pt) \<and>
    (\<forall>x b. vt_lookup (snd env') x = Some b \<longrightarrow> vt_lookup (snd env) x = Some b \<or> x \<in> vars pt)"
  using assms(1-4,6-9)
proof (induction ob arbitrary: inAbs env pt rule: measure_induct_rule[of size])
  case (less ob)
  let ?\<rho> = "mtinst tye" and ?E = "(tye, te)"
  define post where "post p e e' \<longleftrightarrow> tagrees (fst e') ?\<rho> A \<and> fagrees W ?E (snd e') (vars p) \<and>
    (\<forall>x b. vt_lookup (snd e') x = Some b \<longrightarrow> vt_lookup (snd e) x = Some b \<or> x \<in> vars p)"
    for p and e e' :: match_env
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = less.prems
  have tm: "\<exists>iTs'. ok (typ_match_m alg T (tsubst ?\<rho> T) iTs) iTs' \<and> tagrees iTs' ?\<rho> A"
    if "wft ar T" "wft ar (tsubst ?\<rho> T)" "tvars T \<subseteq> A" for T
    using typ_match_agrees[OF that assms(5), of iTs] prems(5) by (auto simp: e return_def)
  have "\<exists>env'. ok (fo_mtch alg inAbs env pt ob) env' \<and> post pt env env'"
  proof (cases pt)
    case pt: (Var x T)
    have T: "T = W x" using prems(6) by (auto simp: pt)
    have wT: "wft ar T" "tvars T \<subseteq> A" using prems(2,4) by (simp_all add: pt)
    text \<open>The object is closed and has the instantiated type of the variable:\<close>
    have "\<not> is_open ob \<and> fastype_of ob = return (tsubst ?\<rho> T) \<and> wft ar (tsubst ?\<rho> T)"
    proof (cases "vt_lookup te x")
      case None
      with prems(1) have "ob = pterm.Var x (tsubst ?\<rho> T)" by (cases ob) (simp_all add: pt)
      with prems(3) show ?thesis by (simp add: is_open_def fastype_of_def return_def)
    next
      case (Some b)
      then obtain U u where lk: "vt_lookup te x = Some (U, u)" by (cases b) auto
      with prems(1) have a: "aconv_term u ob" by (simp add: pt)
      have "has_type W [] u (tsubst ?\<rho> T)" using prems(8) lk T by (simp add: pt)
      then have ty: "has_type W [] ob (tsubst ?\<rho> T)" by (rule has_type_aconv[OF a])
      have "\<not> is_open u" using mte_okD[OF assms(10) lk] closed_iff by blast
      with a ty prems(3) show ?thesis
        using fastype_of_closed[OF ty] has_type_wft[OF ty] by (simp add: aconv_is_open)
    qed
    then have cl: "\<not> is_open ob" and ft: "fastype_of ob = return (tsubst ?\<rho> T)"
      and wo: "wft ar (tsubst ?\<rho> T)" by simp_all
    show ?thesis
    proof (cases "vt_lookup itms x")
      case None
      then have lk: "ok (lookup1 itms x T) None" by (simp add: lookup1_def)
      from tm[OF wT(1) wo wT(2)] obtain iTs' where tm': "ok (typ_match_m alg T (tsubst ?\<rho> T) iTs) iTs'"
        and ag: "tagrees iTs' ?\<rho> A" by blast
      have up: "ok (update_new (x, (T, ob)) itms) (vt_update (x, (T, ob)) itms)"
        using None by (simp add: update_new_def vt_defined_lookup)
      have "ok (fo_mtch alg inAbs env pt ob) (iTs', vt_update (x, (T, ob)) itms)"
        by (subst fo_mtch.simps) (simp add: e pt cl lk ft tm' up del: ok_typ_match_m)
      moreover have "fagrees W ?E (vt_update (x, (T, ob)) itms) (vars pt)"
        using prems(1) T by (simp add: fagrees_def pt)
      ultimately show ?thesis using ag by (auto simp: post_def e pt)
    next
      case (Some b)
      then obtain U u where lku: "vt_lookup itms x = Some (U, u)" by (cases b) auto
      with prems(7) have U: "U = W x" and "aconv_term (finst ?E (pterm.Var x U)) u"
        by (auto simp: fagrees_def e pt)
      with T have "U = T" "aconv_term (finst ?E (pterm.Var x T)) u" by simp_all
      with lku prems(1) have lk: "ok (lookup1 itms x T) (Some u)" and "aeconv ob u"
        by (auto simp: lookup1_def pt aeconv_def intro: aconv_trans aconv_sym)
      then have "ok (fo_mtch alg inAbs env pt ob) env"
        by (subst fo_mtch.simps) (simp add: e pt cl)
      with prems(5,7) show ?thesis by (auto simp: post_def e)
    qed
  next
    case pt: (Const a T)
    with prems(1) have ob: "ob = Const a (tsubst ?\<rho> T)" by (cases ob) simp_all
    have "wft ar T" "wft ar (tsubst ?\<rho> T)" "tvars T \<subseteq> A" using prems(2,3,4) by (simp_all add: pt ob)
    from tm[OF this] obtain iTs' where "ok (typ_match_m alg T (tsubst ?\<rho> T) iTs) iTs'"
      and ag: "tagrees iTs' ?\<rho> A" by blast
    then have "ok (fo_mtch alg inAbs env pt ob) (iTs', itms)"
      by (subst fo_mtch.simps) (simp add: e pt ob del: ok_typ_match_m)
    with ag prems(7) show ?thesis by (auto simp: post_def e)
  next
    case pt: (Free a T)
    with prems(1) have ob: "ob = Free a (tsubst ?\<rho> T)" by (cases ob) simp_all
    have "wft ar T" "wft ar (tsubst ?\<rho> T)" "tvars T \<subseteq> A" using prems(2,3,4) by (simp_all add: pt ob)
    from tm[OF this] obtain iTs' where "ok (typ_match_m alg T (tsubst ?\<rho> T) iTs) iTs'"
      and ag: "tagrees iTs' ?\<rho> A" by blast
    then have "ok (fo_mtch alg inAbs env pt ob) (iTs', itms)"
      by (subst fo_mtch.simps) (simp add: e pt ob del: ok_typ_match_m)
    with ag prems(7) show ?thesis by (auto simp: post_def e)
  next
    case pt: (Bound i)
    with prems(1) have ob: "ob = Bound i" by (cases ob) simp_all
    have "ok (fo_mtch alg inAbs env pt ob) env" by (subst fo_mtch.simps) (simp add: e pt ob)
    with prems(5,7) show ?thesis by (auto simp: post_def e)
  next
    case pt: (Abs a T t)
    with prems(1) obtain b u where ob: "ob = pterm.Abs b (tsubst ?\<rho> T) u"
      and a: "aconv_term (finst ?E t) u"
      by (cases ob) auto
    have "wft ar T" "wft ar (tsubst ?\<rho> T)" "tvars T \<subseteq> A" using prems(2,3,4) by (simp_all add: pt ob)
    from tm[OF this] obtain iTs' where tm': "ok (typ_match_m alg T (tsubst ?\<rho> T) iTs) iTs'"
      and ag: "tagrees iTs' ?\<rho> A" by blast
    have "\<exists>e'. ok (fo_mtch alg True (iTs', itms) t u) e' \<and> post t (iTs', itms) e'"
      unfolding post_def by (rule less.IH) (use a ag prems(2-8) in \<open>auto simp: ob pt e fagrees_def\<close>)
    then obtain e' where m: "ok (fo_mtch alg True (iTs', itms) t u) e'" and p: "post t (iTs', itms) e'"
      by blast
    have "ok (fo_mtch alg inAbs env pt ob) e'"
      using tm' m by (subst fo_mtch.simps) (simp add: e pt ob del: ok_typ_match_m)
    with p show ?thesis by (auto simp: post_def e pt)
  next
    case pt: (App s t)
    with prems(1) obtain g u where ob: "ob = g $ u"
      and a: "aconv_term (finst ?E s) g" "aconv_term (finst ?E t) u"
      by (cases ob) auto
    have "\<exists>e1. ok (fo_mtch alg inAbs env s g) e1 \<and> post s env e1"
      unfolding post_def by (rule less.IH) (use a(1) prems(2-8) in \<open>auto simp: ob pt fagrees_def\<close>)
    then obtain e1 where m1: "ok (fo_mtch alg inAbs env s g) e1" and p1: "post s env e1" by blast
    have "fagrees W ?E (snd e1) (vars t)"
      using p1 prems(7) unfolding post_def fagrees_def by (fastforce simp: pt)
    then have "\<exists>e2. ok (fo_mtch alg inAbs e1 t u) e2 \<and> post t e1 e2"
      unfolding post_def by (intro less.IH) (use a(2) p1 prems(2-8) in \<open>auto simp: ob pt post_def\<close>)
    then obtain e2 where m2: "ok (fo_mtch alg inAbs e1 t u) e2" and p2: "post t e1 e2" by blast
    have "ok (fo_mtch alg inAbs env pt ob) e2"
      using m1 m2 by (subst fo_mtch.simps) (simp add: e pt ob)
    moreover have "post pt env e2"
      using p1 p2 prems(7) unfolding post_def fagrees_def by (fastforce simp: pt)
    ultimately show ?thesis by blast
  qed
  then show ?case by (simp only: post_def)
qed

end

context csig
begin

declare sup_apply[simp]

end

end
