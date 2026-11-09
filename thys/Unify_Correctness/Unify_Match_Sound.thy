section \<open>Soundness of \<open>MATCH\<close>\<close>

theory Unify_Match_Sound
  imports Unify_Simpl_Sound Unify_Seq
begin

text \<open>
  The goals of the elements of the sequences: unifiers (\<open>GR env0 dps0\<close>) and reduced problems
  (\<open>GE env0 dps0\<close>), which are steps from the problem \<open>(env0, dps0)\<close>. \<open>MATCH\<close> binds the
  variable of a flex-rigid pair before the simplification of the new pairs, as in Huet's
  procedure: each binding is a step (\<open>dstep_bind\<close>). The invariant \<open>seqinv\<close> of the sequences
  below covers those of \<open>MATCH\<close>; the search, whose elements are unifiers, is treated in theory
  \<open>Unify_Pull_Sound\<close>, as are the copies of the arguments of an imitation.
\<close>

datatype goal =
  GR env "dpair list"
| GE env "dpair list"

context pure_sig
begin

text \<open>
  The simultaneous substitution of \<open>ts\<close> for the loose bound variables of \<open>u\<close>: the last
  term of \<open>ts\<close> replaces \<open>Bound 0\<close>. It is the \<open>\<beta>\<close>-normal form of the application of an
  abstraction over \<open>length ts\<close> variables to \<open>ts\<close>.
\<close>

fun cpy :: "pterm list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "cpy [] u = u"
| "cpy (t # ts) u = cpy ts (u[incr_bv (ilength ts) 0 t / ilength ts])"

lemma beta_cpy_abs_list: "length bs = length ts \<Longrightarrow> abs_list bs u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* cpy ts u"
proof (induction ts arbitrary: bs u)
  case (Cons t ts)
  then obtain x T bs' where bs: "bs = (x, T) # bs'" and l: "length bs' = length ts" by (cases bs) auto
  have il: "ilength bs' = ilength ts" using l by (simp add: ilength_eq)
  have "Abs x T (abs_list bs' u) $ t \<rightarrow>\<^sub>\<beta> (abs_list bs' u)[t/0]" by (rule beta.beta)
  also have "(abs_list bs' u)[t/0] = abs_list bs' (u[incr_bv (ilength ts) 0 t / ilength ts])"
    by (simp add: subst_abs_list il)
  finally have "abs_list bs u \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta>\<^sup>* abs_list bs' (u[incr_bv (ilength ts) 0 t / ilength ts]) \<degree>\<degree> ts"
    unfolding bs by (simp add: r_into_rtranclp)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* cpy (t # ts) u" using Cons.IH[OF l] by simp
  finally show ?case .
qed simp

lemma beta_cpy: "length Ts = length ts \<Longrightarrow> types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* cpy ts u"
  unfolding types_abs_abs_list by (rule beta_cpy_abs_list) simp

lemma cpy_App: "cpy ts (s $ t) = cpy ts s $ cpy ts t"
  by (induction ts arbitrary: s t) simp_all

lemma cpy_apps: "cpy ts (s \<degree>\<degree> us) = cpy ts s \<degree>\<degree> map (cpy ts) us"
  by (induction us arbitrary: s) (simp_all add: cpy_App)

lemma cpy_closed: "closed h \<Longrightarrow> cpy ts h = h"
  by (induction ts) (simp_all add: subst_no_loose closed_loose_bvar)

lemma subst_incr_bv_Suc:
  "0 \<le> k \<Longrightarrow> 0 \<le> n \<Longrightarrow> (incr_bv (n + 1) k t)[s/k + n] = incr_bv n k t"
proof (induction t arbitrary: k s)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound integer_arith)
next
  case (Abs a T t)
  from Abs.IH[of "k + 1" "lift s 0"] Abs.prems show ?case by (simp add: algebra_simps)
qed auto

lemma cpy_incr: "cpy ts (incr_bv (ilength ts) 0 t) = t"
proof (induction ts arbitrary: t)
  case (Cons s ts)
  have "(incr_bv (ilength ts + 1) 0 t)[incr_bv (ilength ts) 0 s/ilength ts] = incr_bv (ilength ts) 0 t"
    using subst_incr_bv_Suc[of 0 "ilength ts" t] by simp
  with Cons.IH show ?case by simp
qed simp

lemma cpy_Bound:
  "0 \<le> j \<Longrightarrow> j < ilength ts \<Longrightarrow> cpy ts (Bound j) = ts ! (length ts - 1 - nat_of_integer j)"
proof (induction ts)
  case (Cons t ts)
  show ?case
  proof (cases "j = ilength ts")
    case True
    then have "nat_of_integer j = length ts" by (simp add: ilength_eq)
    with True show ?thesis by (simp add: cpy_incr)
  next
    case False
    with Cons.prems have j: "j < ilength ts" by (simp add: integer_arith)
    then have "nat_of_integer j < length ts" using Cons.prems(1) nat_of_integer_less_ilength by blast
    then have "(t # ts) ! (length (t # ts) - 1 - nat_of_integer j) = ts ! (length ts - 1 - nat_of_integer j)"
      by (simp add: nth_Cons' Suc_diff_Suc)
    with j Cons.IH Cons.prems False show ?thesis by (simp add: subst_Bound)
  qed
qed simp

text \<open>The bound variables \<open>Bound (n - 1), \<dots>, Bound 0\<close>:\<close>

abbreviation bvs :: "nat \<Rightarrow> pterm list" where
  "bvs n \<equiv> map (\<lambda>i. Bound (integer_of_nat i)) (rev [0..<n])"

lemma combound_apps: "combound t m k = t \<degree>\<degree> map (\<lambda>i. Bound (m + integer_of_nat i)) (rev [0..<k])"
proof (induction k arbitrary: m)
  case (Suc k)
  have r: "rev [0..<Suc k] = map Suc (rev [0..<k]) @ [0]"
    by (simp add: upt_conv_Cons map_Suc_upt[symmetric] rev_map del: upt_Suc)
  show ?case using Suc.IH[of "m + 1"] by (simp add: r comp_def algebra_simps integer_of_nat_eq_of_nat del: upt_Suc)
qed simp

lemma combound_bvs: "combound t 0 k = t \<degree>\<degree> bvs k"
  by (simp add: combound_apps)

lemma map_cpy_bvs: "map (cpy ts) (bvs (length ts)) = ts"
proof (rule nth_equalityI)
  fix j assume j: "j < length (map (cpy ts) (bvs (length ts)))"
  then have j': "j < length ts" by simp
  have "rev [0..<length ts] ! j = length ts - 1 - j" using j' by (simp add: rev_nth)
  moreover have "0 \<le> integer_of_nat (length ts - 1 - j)" "integer_of_nat (length ts - 1 - j) < ilength ts"
    using j' by (simp_all add: ilength_eq integer_reps)
  ultimately show "map (cpy ts) (bvs (length ts)) ! j = ts ! j"
    using j' by (simp add: cpy_Bound)
qed simp

lemma typings_iff: "e \<tturnstile> ts : Ts \<longleftrightarrow> list_all2 (typing e) ts Ts"
  by (induction ts arbitrary: Ts) (auto split: list.splits simp: list_all2_Cons1)

lemma typings_bvs: "pushes e Ts \<tturnstile> bvs (length Ts) : Ts"
proof -
  let ?ks = "map integer_of_nat (rev [0..<length Ts])"
  have "pushes e Ts \<tturnstile> map Bound ?ks : map (\<lambda>k. rev Ts ! nat_of_integer k) ?ks"
    by (rule typings_Bounds) (auto simp: pushes_nth ilength_eq integer_of_nat_eq_of_nat)
  moreover have "map (\<lambda>k. rev Ts ! nat_of_integer k) ?ks = Ts"
    by (rule nth_equalityI) (simp_all add: rev_nth)
  ultimately show ?thesis by (simp add: comp_def)
qed

text \<open>Applying the abstraction of a copy to the arguments is its simultaneous substitution:\<close>

lemma beta_reds_ap: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> s \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> t"
  unfolding ap_def by (intro beta_reds_vsubst inst_reds) (auto simp: wt_subst_def)

lemma conv_cpy:
  assumes "e \<turnstile> inst \<rho> (types_abs Ts u \<degree>\<degree> ts) : U" "wt_subst \<sigma>" "length Ts = length ts"
  shows "ap \<rho> \<sigma> (types_abs Ts u \<degree>\<degree> ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy ts u)" "e \<turnstile> inst \<rho> (cpy ts u) : U"
proof -
  have b: "types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* cpy ts u" by (rule beta_cpy[OF assms(3)])
  show "ap \<rho> \<sigma> (types_abs Ts u \<degree>\<degree> ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy ts u)"
    by (rule conv_beta_eta[OF wt_ap[OF assms(1,2)] beta_reds_ap[OF b assms(2)]])
  show "e \<turnstile> inst \<rho> (cpy ts u) : U"
    by (rule subject_reduction_beta'[OF inst_reds[OF b] assms(1)])
qed



subsection \<open>Goals, elements and the invariant of sequences\<close>

abbreviation tps_dps :: "(pterm \<times> pterm) list \<Rightarrow> dpair list" where
  "tps_dps tps \<equiv> map (\<lambda>(t, u). ([], t, u)) tps"

abbreviation lvars :: "pterm list \<Rightarrow> (indexname \<times> ptyp) set" where
  "lvars ts \<equiv> \<Union> (vars ` set ts)"

fun elem_ok :: "goal \<Rightarrow> elem \<Rightarrow> bool" where
  "elem_ok (GR env0 dps0) (El_R env tps) \<longleftrightarrow> dstep env0 dps0 env (tps_dps tps)"
| "elem_ok (GE env0 dps0) (El_E env dps) \<longleftrightarrow> dstep env0 dps0 env dps"
| "elem_ok _ _ \<longleftrightarrow> False"

text \<open>
  The invariant of the sequences of \<open>MATCH\<close>. A projection is a step to its pair, after the binding
  of the variable \<open>X\<close>. The copies of an argument \<open>uarg\<close> into its new variable \<open>G\<close>
  (\<^const>\<open>S_Maps\<close>) follow a step to the pair \<open>G targs =?= uarg\<close> and the pairs \<open>dps1\<close>, whose
  elements \<open>xq\<close> are the copies of the further arguments; the copies of \<open>uarg\<close> are treated by the
  soundness of the search (theory \<open>Unify_Pull_Sound\<close>). The arguments are normalized in the
  environment \<open>envM\<close> of \<open>MATCH\<close>.
\<close>

inductive seqinv :: "goal \<Rightarrow> seq \<Rightarrow> bool" where
  Empty: "seqinv G S_Empty"
| Single: "elem_ok G x \<Longrightarrow> seqinv G (S_Single x)"
| Append: "seqinv G xq \<Longrightarrow> seqinv G yq \<Longrightarrow> seqinv G (S_Append xq yq)"
| Proj: "\<forall>env1 args env2. make_args vname Ts env' Us = (env1, args) \<longrightarrow>
      ok (update X (types_abs Ts (list_comb head args)) env1) env2 \<longrightarrow>
      dstep env0 dps0 env2 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps) \<Longrightarrow>
    seqinv (GE env0 dps0) tail \<Longrightarrow>
    seqinv (GE env0 dps0) (S_Proj vname env' Ts Us targs rb u dps head targ X tail)"
| Maps: "dstep env0 dps0 env1 ((rb, G \<degree>\<degree> targs, uarg) # dps1) \<Longrightarrow> seqinv (GE env1 dps1) xq \<Longrightarrow>
    extends envM env1 \<Longrightarrow> \<exists>x U. G = Var x U \<Longrightarrow>
    seqinv (GE env0 dps0) (S_Maps vname envM rb targs G uarg xq)"

text \<open>Reduced problems compose with steps before them:\<close>

lemma seqinv_GE_dstep: "seqinv G s \<Longrightarrow> G = GE env1 dps1 \<Longrightarrow> dstep env0 dps0 env1 dps1 \<Longrightarrow> seqinv (GE env0 dps0) s"
proof (induction arbitrary: env1 dps1 rule: seqinv.induct)
  case (Single G x)
  then show ?case by (cases x) (auto intro!: seqinv.Single intro: dstep_trans)
next
  case (Proj vname Ts env' Us X head rb targ targs u dps env0' dps0' tail)
  then show ?case by (intro seqinv.Proj) (auto intro: dstep_trans)
next
  case (Maps env0' dps0' env1' rb G targs uarg dps1' xq envM vname)
  then show ?case by (intro seqinv.Maps) (auto intro: dstep_trans)
qed (auto intro: seqinv.intros)


subsection \<open>Typings of copies\<close>

lemma cert_targs:
  assumes "bs_env \<rho> e rb" "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
  shows "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
proof
  fix T assume "T \<in> set Ts"
  then obtain i where i: "i < length Ts" "T = Ts ! i" by (auto simp: in_set_conv_nth)
  from typings_nth[OF assms(2)] i have l: "i < length targs" "e \<turnstile> inst \<rho> (targs ! i) : tsubst \<rho> T"
    by auto
  show "cert_typ alg ar (tsubst \<rho> T)"
    by (rule bs_env_cert[OF assms(1) l(2)]) (use assms(3) l(1) in auto)
qed

lemma typing_tabs_app:
  assumes "pushes e (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> u' : U" "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
  shows "e \<turnstile> inst \<rho> (types_abs Ts u' \<degree>\<degree> targs) : U"
proof -
  have "e \<turnstile> types_abs (map (tsubst \<rho>) Ts) (inst \<rho> u') : map (tsubst \<rho>) Ts \<Rrightarrow> U"
    by (rule typing_types_abs[OF assms(1)]) (use assms(3) in auto)
  then show ?thesis using assms(2) by (simp add: inst_apps inst_types_abs list_app_typeI)
qed

lemma conv_eta_lift: "wt (Abs a T (lift w 0 $ Bound 0)) \<Longrightarrow> Abs a T (lift w 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> w"
proof -
  assume w: "wt (Abs a T (lift w 0 $ Bound 0))"
  have "Abs a T (lift w 0 $ Bound 0) \<rightarrow>\<^sub>\<eta> (lift w 0)[d/0]" for d by (rule eta.eta) simp
  then have "Abs a T (lift w 0 $ Bound 0) \<rightarrow>\<^sub>\<eta> w" by simp
  then show ?thesis using w by (intro beta_eta_conv) auto
qed

lemma ilength_append [simp]: "ilength (xs @ ys) = ilength xs + ilength ys"
  by (induction xs) simp_all

lemma closed_inst: "closed h \<Longrightarrow> closed (inst \<rho> h)"
  by (simp add: closed_def)


subsection \<open>New variables\<close>

text \<open>\<^const>\<open>genvars\<close> creates distinct names: \<^const>\<open>radixstring\<close> is
  injective.\<close>

lemma radix26_append: "radix26 n ds = radix26 n [] @ ds"
proof (induction n arbitrary: ds rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have "n div 26 < n" by simp
    from less.IH[OF this, of "(n mod 26) # ds"] less.IH[OF this, of "[n mod 26]"] False show ?thesis
      by (subst (1 2) radix26.simps) simp
  qed (subst (1 2) radix26.simps; simp)
qed

lemma radix26_step: "\<not> n < 26 \<Longrightarrow> radix26 n [] = radix26 (n div 26) [] @ [n mod 26]"
  by (subst radix26.simps) (simp add: radix26_append[of "n div 26" "[n mod 26]"])

lemma radix26_small: "n < 26 \<Longrightarrow> radix26 n [] = [n]"
  by (subst radix26.simps) simp

lemma radix26_digits: "d \<in> set (radix26 n []) \<Longrightarrow> d < 26"
proof (induction n arbitrary: d rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have lt: "n div 26 < n" by simp
    have "d \<in> set (radix26 (n div 26) []) \<or> d = n mod 26" using less.prems False by (auto simp: radix26_step)
    then show ?thesis using less.IH[OF lt] by auto
  qed (use less in \<open>simp add: radix26_small\<close>)
qed

lemma radix26_val: "foldl (\<lambda>a d. a * 26 + d) 0 (radix26 n []) = n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have "n div 26 < n" by simp
    with less False show ?thesis by (simp add: radix26_step)
  qed (simp add: radix26_small)
qed

lemma radix26_inj: "radix26 n [] = radix26 m [] \<Longrightarrow> n = m"
  by (metis radix26_val)

lemma radix26_nonempty: "radix26 n [] \<noteq> []"
  by (cases "n < 26") (simp_all add: radix26_step radix26_small)

lemma radix_char_inj:
  fixes d d' :: nat
  assumes "d < 26" "d' < 26" "String.ascii_of (char_of (97 + d)) = String.ascii_of (char_of (97 + d'))"
  shows "d = d'"
proof -
  have "of_char (String.ascii_of (char_of (97 + x))) = (97 + x :: nat)" if "x < 26" for x :: nat
    using that by (simp add: String.ascii_of_char_of of_char_of take_bit_eq_mod)
  from this[OF assms(1)] this[OF assms(2)] assms(3) show ?thesis by simp
qed

lemma radixstring_inj:
  assumes "0 \<le> n" "0 \<le> m" "radixstring n = radixstring m"
  shows "n = m"
proof -
  let ?f = "\<lambda>d::nat. String.ascii_of (char_of (97 + d))"
  from assms(3) have "String.explode (radixstring n) = String.explode (radixstring m)" by simp
  then have eq: "map ?f (radix26 (nat_of_integer n) []) = map ?f (radix26 (nat_of_integer m) [])"
    unfolding radixstring_def by (simp add: String.explode_implode_eq comp_def)
  have "inj_on ?f {d. d < 26}" by (auto intro!: inj_onI radix_char_inj)
  moreover have "set (radix26 (nat_of_integer n) []) \<union> set (radix26 (nat_of_integer m) []) \<subseteq> {d. d < 26}"
    using radix26_digits by blast
  ultimately have "inj_on ?f (set (radix26 (nat_of_integer n) []) \<union> set (radix26 (nat_of_integer m) []))"
    by (rule inj_on_subset)
  with eq have "radix26 (nat_of_integer n) [] = radix26 (nat_of_integer m) []"
    by (simp add: inj_on_map_eq_map)
  then have "nat_of_integer n = nat_of_integer m" by (rule radix26_inj)
  with assms(1,2) show ?thesis by (simp add: integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq eq_nat_nat_iff)
qed

lemma radixstring_nonempty: "radixstring n \<noteq> STR ''''"
proof
  assume "radixstring n = STR ''''"
  then have "String.explode (radixstring n) = []" by (simp add: String.zero_literal.rep_eq)
  then show False unfolding radixstring_def using radix26_nonempty by (simp add: String.explode_implode_eq)
qed

lemma plus_literal_cancel: "(a :: String.literal) + b = a + c \<longleftrightarrow> b = c"
  by (metis String.plus_literal.rep_eq literal.explode_inject same_append_eq)

lemma plus_literal_neq: "b \<noteq> STR '''' \<Longrightarrow> (a :: String.literal) + b \<noteq> a"
  by (metis String.plus_literal.rep_eq literal.explode_inject append_self_conv zero_literal.rep_eq
      String.zero_literal_def)

fun var_of :: "pterm \<Rightarrow> indexname" where
  "var_of (Var x T) = x"
| "var_of _ = undefined"

lemma genvs_names:
  "0 \<le> n \<Longrightarrow> v \<in> set (genvs name i n Ts) \<Longrightarrow>
    \<exists>T. v = Var (name, i) T \<or> (\<exists>k\<ge>n. v = Var (name + radixstring k, i) T)"
proof (induction name i n Ts rule: genvs.induct)
  case (3 name i n T v va)
  then show ?case by (fastforce dest: order_trans[of n "n + 1", rotated])
qed auto

lemma genvs_distinct: "0 \<le> n \<Longrightarrow> distinct (map var_of (genvs name i n Ts))"
proof (induction name i n Ts rule: genvs.induct)
  case (3 name i n T v va)
  have "(name + radixstring n, i) \<notin> var_of ` set (genvs name i (n + 1) (v # va))"
  proof
    assume "(name + radixstring n, i) \<in> var_of ` set (genvs name i (n + 1) (v # va))"
    then obtain w where w: "w \<in> set (genvs name i (n + 1) (v # va))" "var_of w = (name + radixstring n, i)"
      by (auto simp: image_iff)
    from genvs_names[OF _ w(1)] "3.prems" obtain U where
      "w = Var (name, i) U \<or> (\<exists>k\<ge>n + 1. w = Var (name + radixstring k, i) U)" by fastforce
    then show False
    proof (elim disjE exE conjE)
      assume "w = Var (name, i) U"
      with w(2) plus_literal_neq[OF radixstring_nonempty, of name n] show False by simp
    next
      fix k assume "n + 1 \<le> k" "w = Var (name + radixstring k, i) U"
      with w(2) "3.prems" radixstring_inj[of k n] show False by (auto simp: plus_literal_cancel)
    qed
  qed
  with "3.IH" "3.prems" show ?case by simp
qed auto

lemma genvs_vars: "list_all2 (\<lambda>v T. \<exists>a. v = Var (a, i) T) (genvs name i n Ts) Ts"
  by (induction name i n Ts rule: genvs.induct) auto

lemma genvars_props:
  assumes "genvars name env Ts = (env', vs)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env' = maxidx env + 1"
    "list_all2 (\<lambda>v T. \<exists>a. v = Var (a, maxidx env + 1) T) vs Ts" "distinct (map var_of vs)"
  using assms genvs_vars genvs_distinct[of 0] by (auto simp: genvars_def split: env.splits)

lemma vinv_genvars:
  assumes g: "genvars name env Ts = (env', vs)" and vi: "vinv \<rho> env X"
  shows "vinv \<rho> env' (lvars vs \<union> X)"
proof -
  note g' = genvars_props[OF g]
  have ev: "evars env' = evars env" by (simp add: evars_def bnds_def g'(1))
  have b: "below (maxidx env) (X \<union> evars env)" and c: "vcons \<rho> (X \<union> evars env)"
    using vi by (simp_all add: vinv_def)
  have new: "\<exists>k < length vs. vs ! k = Var x W \<and> snd x = maxidx env + 1" if "(x, W) \<in> lvars vs" for x W
  proof -
    from that obtain v where v: "v \<in> set vs" "(x, W) \<in> vars v" by blast
    then obtain k where k: "k < length vs" "vs ! k = v" by (auto simp: in_set_conv_nth)
    from g'(4) k obtain a where "v = Var (a, maxidx env + 1) (Ts ! k)" by (auto dest: list_all2_nthD)
    with v k show ?thesis by auto
  qed
  have le: "maxidx env \<le> maxidx env'" using g' by (simp add: integer_arith)
  have "below (maxidx env') (lvars vs \<union> X \<union> evars env')"
    using below_mono[OF b _ le] g'(3) ev new by (fastforce simp: below_def)
  moreover have "vcons \<rho> (lvars vs \<union> X \<union> evars env')"
    unfolding vcons_def
  proof (intro allI impI)
    fix x U V assume U: "(x, U) \<in> lvars vs \<union> X \<union> evars env'" and V: "(x, V) \<in> lvars vs \<union> X \<union> evars env'"
    have old: "snd x \<le> maxidx env" if "(x, W) \<in> X \<union> evars env" for W
      using belowD[OF b that] .
    have clash: False if "(x, W) \<in> lvars vs" "(x, W') \<in> X \<union> evars env" for W W'
      using new[OF that(1)] old[OF that(2)] by (auto simp: integer_arith)
    have both: "U = V" if "(x, U) \<in> lvars vs" "(x, V) \<in> lvars vs"
    proof -
      from new[OF that(1)] new[OF that(2)] obtain k l where
        k: "k < length vs" "vs ! k = Var x U" and l: "l < length vs" "vs ! l = Var x V" by blast
      have "map var_of vs ! k = map var_of vs ! l" using k l by simp
      then have "k = l" using nth_eq_iff_index_eq[OF g'(5), of k l] k(1) l(1) by simp
      with k l show ?thesis by simp
    qed
    have U': "(x, U) \<in> lvars vs \<or> (x, U) \<in> X \<union> evars env" and V': "(x, V) \<in> lvars vs \<or> (x, V) \<in> X \<union> evars env"
      using U V ev by blast+
    show "tsubst \<rho> U = tsubst \<rho> V"
    proof (cases "(x, U) \<in> lvars vs")
      case True
      show ?thesis
      proof (cases "(x, V) \<in> lvars vs")
        case True
        with \<open>(x, U) \<in> lvars vs\<close> show ?thesis using both by simp
      next
        case False
        with V' have "(x, V) \<in> X \<union> evars env" by simp
        from clash[OF True this] show ?thesis ..
      qed
    next
      case False
      with U' have u: "(x, U) \<in> X \<union> evars env" by simp
      show ?thesis
      proof (cases "(x, V) \<in> lvars vs")
        case True
        from clash[OF True u] show ?thesis ..
      next
        case False
        with V' have "(x, V) \<in> X \<union> evars env" by simp
        from vconsD[OF c u this] show ?thesis .
      qed
    qed
  qed
  ultimately show ?thesis by (simp add: vinv_def ev)
qed

text \<open>The new arguments of a projection or an imitation:\<close>

lemma make_args_props:
  assumes "make_args name Ts env Us = (env', args)"
  obtains Gs where "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (lvars Gs \<union> X)"
proof (cases "Us = []")
  case True
  with assms have "env' = env" "args = []" by (simp_all add: make_args_def)
  with True show ?thesis by (intro that[of "[]"]) simp_all
next
  case False
  obtain env1 vs where g: "genvars name env (map (\<lambda>T. Ts \<Rrightarrow> T) Us) = (env1, vs)" by fastforce
  with assms False have e: "env' = env1" "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
    by (auto simp: make_args_def List.null_iff)
  note g' = genvars_props[OF g]
  show ?thesis
  proof (rule that[of vs])
    show "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) vs" by (simp add: e combound_bvs)
    show "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) vs Us"
      using g'(4) by (fastforce simp: list_all2_conv_all_nth)
    show "tenv env' = tenv env" "tyenv env' = tyenv env" using g' e by simp_all
    show "maxidx env \<le> maxidx env'" using g' e by (simp add: integer_arith)
    show "vinv \<rho> env' (lvars vs \<union> X)" if "vinv \<rho> env X" for \<rho> X
      using vinv_genvars[OF g that] e by simp
  qed
qed

lemma extends_tenv_eq: "tenv env' = tenv env \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow>
    extends env env'"
  by (simp add: extends_def)

lemma inst_bvs [simp]: "map (inst \<rho>) (bvs n) = bvs n"
  by simp

lemma vars_bvs [simp]: "lvars (bvs n) = {}"
  by auto

lemma loose_bvar_bvs_ilength: "length Ts = n \<Longrightarrow> \<forall>t\<in>set (bvs n). \<not> loose_bvar t (ilength Ts)"
  by (auto simp: ilength_eq integer_of_nat_eq_of_nat)

lemma cpy_new_arg: "closed G \<Longrightarrow> cpy ts (G \<degree>\<degree> bvs (length ts)) = G \<degree>\<degree> ts"
  by (simp only: cpy_apps cpy_closed map_cpy_bvs)


subsection \<open>Type computations\<close>

lemma mapM_fastype_sound:
  assumes "ok (mapM (fastype env rb) ts) Ts'"
  shows "length Ts' = length ts"
    and "tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<tturnstile> map (inst \<rho>) ts : Us \<Longrightarrow> map (tsubst \<rho>) Ts' = Us"
proof -
  from assms have l: "list_all2 (\<lambda>t T. ok (fastype env rb t) T) ts Ts'" by (simp add: ok_mapM)
  then show "length Ts' = length ts" by (simp add: list_all2_lengthD)
  assume tsol: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e rb" and ty: "e \<tturnstile> map (inst \<rho>) ts : Us"
  from l ty show "map (tsubst \<rho>) Ts' = Us"
  proof (induction ts Ts' arbitrary: Us rule: list_all2_induct)
    case (Cons t ts T Ts')
    from Cons.prems obtain U Us' where Us: "Us = U # Us'" and tt: "e \<turnstile> inst \<rho> t : U"
      and tts: "e \<tturnstile> map (inst \<rho>) ts : Us'"
      by (auto split: list.splits)
    from fastype_sound[OF Cons.hyps(1) tsol bs tt] Cons.IH[OF tts] Us show ?case by simp
  qed simp
qed

lemma body_type_TVar:
  assumes "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> B = TVar v S \<Longrightarrow> vt_lookup (tyenv env) v = None"
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where "Ts = [T1, U]" by auto
      with h Type True have "ok (bt env U) B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] show ?thesis .
    next
      case False
      with h Type have "B = T" by (auto split: list.splits if_splits)
      with Type "1.prems"(2) show ?thesis by simp
    qed
  next
    case (TVar v' S')
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v' S') lr"
      and rest: "ok (case lr of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B" by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr have "vt_lookup (tyenv env) v' = None"
        by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)
      with None rest TVar "1.prems"(2) show ?thesis by simp
    next
      case (Some T')
      with rest have "ok (bt env T') B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] show ?thesis .
    qed
  next
    case (TFree a S)
    with h "1.prems"(2) show ?thesis by simp
  qed
qed

lemma devar_nonTVar: "\<not> is_TVar U \<Longrightarrow> devar \<theta> U = return U"
  by (subst devar.simps) (cases U; simp)

lemma devar_unbound: "vt_lookup \<theta> v = None \<Longrightarrow> devar \<theta> (TVar v S) = return (TVar v S)"
  by (subst devar.simps) (simp add: type_lookup_def)

text \<open>Unifying an unbound type variable with another type binds it:\<close>

lemma cunify_types_TVar:
  assumes cu: "okW (cunify_types alg' (TVar v S) U env) env'" and nt: "\<not> is_TVar U"
    and unb: "vt_lookup (tyenv env) v = None" and tsol: "tsol (tyenv env') \<rho>"
  shows "\<rho> v S = tsubst \<rho> U"
proof -
  have nh: False if "ok (case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) (TVar v S) U)) | _ \<Rightarrow> raise e) y"
    for e and y :: env
    using that by (cases e) auto
  have ne: "TVar v S \<noteq> U" using nt by auto
  from cu[unfolded cunify_types_ok] ne obtain tye' n' where
    tu: "ok (type_unify alg' U (TVar v S) (tyenv env, maxidx env)) (tye', n')"
    and env': "env' = Envir n' (tenv env) tye'"
    by (auto simp: unify_types_def ok_handle split: prod.splits dest: nh)
  have uo: "ok (unify_aux alg' U (TVar v S) (tyenv env, maxidx env)) (tye', n')" using tu by (simp add: type_unify_def)
  obtain tye1 where u: "ok (update_new (v, (S, U)) (tyenv env)) tye1"
    and m: "ok (meet alg' U S (tye1, maxidx env)) (tye', n')"
    using uo nt by (subst (asm) unify_aux.simps) (cases U; auto simp: devar_nonTVar devar_unbound[OF unb] split: if_splits)
  have "textends tye1 tye'" using meet_textends[OF m refl] by simp
  from update_new_sound(2)[OF u this] tsol env' show ?thesis by simp
qed

lemma proj_unify_sound:
  assumes pu: "okW (proj_unify cfg base bary Cs env) env'"
    and tv: "Cs \<noteq> [] \<longrightarrow> is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env) v = None)"
  shows "tenv env' = tenv env" "extends env env'"
    and "tsol (tyenv env') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> base) \<Longrightarrow> wft ar (tsubst \<rho> bary) \<Longrightarrow>
      tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
proof -
  have "tenv env' = tenv env \<and> extends env env' \<and>
    (tsol (tyenv env') \<rho> \<longrightarrow> wft ar (tsubst \<rho> base) \<longrightarrow> wft ar (tsubst \<rho> bary) \<longrightarrow>
      tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base))"
  proof (cases "Cs = []")
    case True
    then have cu: "okW (cunify_types (cfg_alg cfg) base bary env) env'"
      using pu by (auto simp: proj_unify_def test_unify_types_ok split: if_splits)
    note c = cunify_types_sound[OF cu]
    show ?thesis using c(1,2) c(3)[of \<rho>] True by auto
  next
    case False
    then have cu: "okW (cunify_types (cfg_alg cfg) bary (Cs \<Rrightarrow> base) env) env'"
      using pu by (auto simp: proj_unify_def List.null_iff)
    note c = cunify_types_sound[OF cu]
    from tv False obtain v S where b: "bary = TVar v S" and unb: "vt_lookup (tyenv env) v = None"
      by (cases bary) auto
    from False obtain C Cs' where "Cs = C # Cs'" by (cases Cs) auto
    then have nt: "\<not> is_TVar (Cs \<Rrightarrow> base)" by simp
    show ?thesis using c(1,2) cunify_types_TVar[OF cu[unfolded b] nt unb] b by auto
  qed
  then show "tenv env' = tenv env" "extends env env'"
    and "tsol (tyenv env') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> base) \<Longrightarrow> wft ar (tsubst \<rho> bary) \<Longrightarrow>
      tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
    by blast+
qed

lemma gentvars_props:
  assumes "gentvars p env = (env', Cs)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'" "Cs = [] \<longleftrightarrow> p = 0"
  using assms by (auto simp: gentvars_def integer_arith split: if_splits env.splits)

lemma arity_guesses_TVar: "p \<in> set (arity_guesses cfg T) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> is_TVar T"
  by (auto simp: arity_guesses_def split: if_splits)

lemma cert_wft: "cert_typ alg ar T \<Longrightarrow> wft ar T"
  by (simp add: cert_typ_def)


subsection \<open>Projections and imitation\<close>

lemma nat_integer_of_nat [simp]: "nat_of_integer (integer_of_nat m) = m"
  by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq)

lemma integer_of_nat_less: "integer_of_nat a < integer_of_nat b \<longleftrightarrow> a < b"
  by (simp add: integer_less_iff integer_of_nat.rep_eq)

lemma body_type_tyenv:
  assumes "body_type env T = Some r"
  shows "tyenv env' = tyenv env \<Longrightarrow> body_type env' T = Some r"
  using assms
proof (induction env T r rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by auto
      with h Type have "bt env U = Some r" by simp
      from "1.IH"[OF this "1.prems"] Type Ts a show ?thesis by (subst body_type.simps) simp
    next
      case False
      with h Type show ?thesis by (subst body_type.simps) (auto split: list.splits if_splits)
    qed
  next
    case (TVar v' S')
    show ?thesis
    proof (cases "type_lookup (tyenv env) v' S'")
      case None
      with h TVar show ?thesis by (simp add: bindM_def)
    next
      case (Some lr)
      show ?thesis
      proof (cases lr)
        case (Err e)
        with h TVar Some "1.prems" show ?thesis by (subst body_type.simps) (simp add: bindM_def)
      next
        case (Ok lr')
        show ?thesis
        proof (cases lr')
          case None
          with h TVar Some Ok "1.prems" show ?thesis by (subst body_type.simps) (simp add: bindM_def)
        next
          case (Some T')
          with h TVar \<open>type_lookup (tyenv env) v' S' = Some lr\<close> Ok have "bt env T' = Some r"
            by (simp add: bindM_def)
          from "1.IH"[OF this "1.prems"] TVar \<open>type_lookup (tyenv env) v' S' = Some lr\<close> Ok Some "1.prems"
          show ?thesis by (subst body_type.simps) (simp add: bindM_def)
        qed
      qed
    qed
  next
    case (TFree a S)
    with h show ?thesis by (subst body_type.simps) simp
  qed
qed

subsection \<open>Binding the variable of a pair\<close>

lemma typings_unique: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<tturnstile> ts : Us \<Longrightarrow> Ts = Us"
  by (induction ts arbitrary: Ts Us) (auto split: list.splits dest: typing_unique)

lemma copy_bind_conv:
  assumes "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u')"
    "ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    "wt (ap \<rho> \<sigma> (Var v T \<degree>\<degree> targs))" "wt (ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs))"
  shows "ap \<rho> \<sigma> (Var v T \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
proof -
  have "ap \<rho> \<sigma> (Var v T \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs)"
    unfolding ap_apps
    by (rule conv_apps) (use assms in \<open>simp_all add: ap_apps list_all2_refl\<close>)
  from conv_trans[OF this assms(2)] show ?thesis .
qed

text \<open>
  Binding the variable \<open>?v\<close> of the pair \<open>?v targs =?= u\<close> to the abstraction of a term \<open>s\<close> over
  the types \<open>Ts\<close> of the arguments is a step to the pair \<open>s' =?= u\<close>, for a term \<open>s'\<close> that is
  equivalent to the application of the abstraction to the arguments. The environment \<open>env1\<close>
  holds the new variables of \<open>s\<close> (\<open>viN\<close>) and possibly further type bindings.
\<close>

lemma dstep_bind:
  assumes ext1: "extends env env1" and te1: "tenv env1 = tenv env"
    and upd: "ok (update (v, T) (types_abs Ts s) env1) env2"
    and viN: "\<And>\<rho> Y. vinv \<rho> env Y \<Longrightarrow> vinv \<rho> env1 (vars s \<union> Y)"
    and Tsok: "ok (mapM (fastype env rb) targs) Ts"
    and lbs: "\<not> loose_bvar s (ilength Ts)"
    and vs': "vars s' \<subseteq> vars s \<union> lvars targs"
    and ty: "\<And>\<rho> e U. tsol (tyenv env1) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow>
      e \<turnstile> inst \<rho> u : U \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> U \<Longrightarrow>
      \<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb) \<Longrightarrow> \<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> s : U) \<and> \<not> loose_bvar s' (ilength rb) \<and>
      e \<turnstile> inst \<rho> s' : U \<and> (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts s \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> s')"
  shows "dstep env ((rb, Var v T \<degree>\<degree> targs, u) # dps) env2 ((rb, s', u) # dps)"
proof (rule dstepI)
  show "extends env env2" by (rule extends_trans[OF ext1 extends_update[OF upd]])
  fix \<rho> env'' X assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env2 env''" and wte: "wt_env \<rho> env"
    and dt: "dtyped \<rho> ((rb, Var v T \<degree>\<degree> targs, u) # dps)"
    and vi: "vinv \<rho> env (X \<union> dvars ((rb, Var v T \<degree>\<degree> targs, u) # dps))"
  have ext2: "extends env1 env''" by (rule extends_trans[OF extends_update[OF upd] ext])
  have tsol1: "tsol (tyenv env1) \<rho>" by (rule extends_tsol[OF tsol ext2])
  have tsol0: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol1 ext1])
  from dt obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> (Var v T \<degree>\<degree> targs) : U"
    and tyu: "e \<turnstile> inst \<rho> u : U" and lbt: "\<not> loose_bvar (Var v T \<degree>\<degree> targs) (ilength rb)"
    and lbu: "\<not> loose_bvar u (ilength rb)" and dt1: "dtyped \<rho> dps"
    by auto
  have dec: "e' \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<and> tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> U'"
    if bse: "bs_env \<rho> e' rb" and tyt': "e' \<turnstile> inst \<rho> (Var v T \<degree>\<degree> targs) : U'" for e' U'
  proof -
    from tyt'[unfolded inst_apps] obtain Us where tyv: "e' \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U'"
      and tyas: "e' \<tturnstile> map (inst \<rho>) targs : Us"
      by (rule list_app_typeE)
    have Us: "map (tsubst \<rho>) Ts = Us" by (rule mapM_fastype_sound(2)[OF Tsok tsol0 bse tyas])
    with tyas tyv show ?thesis by auto
  qed
  have tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and TT: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> U"
    using dec[OF bs tyt] by blast+
  have lba: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" using lbt by (simp add: loose_bvar_apps)
  have lb: "\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)" using lba lbu by simp
  have cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tya lba])
  note R = ty[OF tsol1 bs tya tyu TT lb cert]
  have tys: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> s : U" for e' using R by blast
  have tyb: "e' \<turnstile> inst \<rho> (types_abs Ts s) : tsubst \<rho> T" for e'
    using typing_types_abs[OF tys] cert by (simp add: inst_types_abs TT)
  have cl: "closed (types_abs Ts s)" by (rule closed_types_abs[OF lbs])
  have wte1: "wt_env \<rho> env1" using wt_env_tenv[of env1 env \<rho>] te1 wte by simp
  show "wt_env \<rho> env2 \<and> dtyped \<rho> ((rb, s', u) # dps) \<and> vinv \<rho> env2 (X \<union> dvars ((rb, s', u) # dps)) \<and>
      deqv (binds \<rho> env2 \<union> dp_eqs \<rho> ((rb, s', u) # dps)) \<rho> ((rb, Var v T \<degree>\<degree> targs, u) # dps)"
  proof (intro conjI)
    show "wt_env \<rho> env2" by (rule wt_env_update[OF upd wte1 cl tyb])
    show "dtyped \<rho> ((rb, s', u) # dps)" using bs R tyu lbu dt1 by auto
    have "vinv \<rho> env1 (vars s \<union> (X \<union> dvars ((rb, Var v T \<degree>\<degree> targs, u) # dps)))" by (rule viN[OF vi])
    then have "vinv \<rho> env1 (X \<union> dvars ((rb, s', u) # dps) \<union> insert (v, T) (vars (types_abs Ts s)))"
      by (rule vinv_mono) (use vs' in \<open>auto simp: vars_apps\<close>)
    then show "vinv \<rho> env2 (X \<union> dvars ((rb, s', u) # dps))" by (rule vinv_update[OF upd])
    let ?E = "binds \<rho> env2 \<union> dp_eqs \<rho> ((rb, s', u) # dps)"
    have hd: "deqv ?E \<rho> [(rb, Var v T \<degree>\<degree> targs, u)]"
      unfolding deqv_single
    proof (intro allI impI)
      fix e' U' assume a: "bs_env \<rho> e' rb" "e' \<turnstile> inst \<rho> (Var v T \<degree>\<degree> targs) : U'" "e' \<turnstile> inst \<rho> u : U'"
      from dec[OF a(1,2)] have tya': "e' \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
        and TT': "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> U'" by blast+
      have cert': "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF a(1) tya' lba])
      note R' = ty[OF tsol1 a(1) tya' a(3) TT' lb cert']
      have tys': "pushes e'' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> s : U'" for e'' using R' by blast
      have tyb': "e'' \<turnstile> inst \<rho> (types_abs Ts s) : tsubst \<rho> T" for e''
        using typing_types_abs[OF tys'] cert' by (simp add: inst_types_abs TT')
      have "vt_lookup (tenv env2) v = Some (T, types_abs Ts s)" using ok_update(2)[OF upd] by simp
      then have "(Var v (tsubst \<rho> T), inst \<rho> (types_abs Ts s)) \<in> ?E" unfolding binds_def by blast
      from eqv_bind_closed[OF this _ tyb'] cl
      have b: "eqv ?E e' (Var v (tsubst \<rho> T)) (inst \<rho> (types_abs Ts s))" by (simp add: closed_def)
      have tyab: "e' \<turnstile> inst \<rho> (types_abs Ts s \<degree>\<degree> targs) : U'" by (rule typing_tabs_app[OF tys' tya' cert'])
      from eqv_apps_head[OF b, of "map (inst \<rho>) targs" U'] a(2) tyab
      have e1: "eqv ?E e' (inst \<rho> (Var v T \<degree>\<degree> targs)) (inst \<rho> (types_abs Ts s \<degree>\<degree> targs))"
        by (simp add: inst_apps)
      have "inst \<rho> (types_abs Ts s \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> inst \<rho> s'"
        using R'[THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format, OF wt_subst_Var]
        by (simp add: ap_Var)
      from eqv_conv[OF this tyab] R'
      have e2: "eqv ?E e' (inst \<rho> (types_abs Ts s \<degree>\<degree> targs)) (inst \<rho> s')" by blast
      have e3: "eqv ?E e' (inst \<rho> s') (inst \<rho> u)"
        by (rule dp_eqs_use[OF _ _ a(1) _ a(3) _ lbu]) (use R' in auto)
      from eqv.eqv_trans[OF eqv.eqv_trans[OF e1 e2] e3]
      show "eqv ?E e' (inst \<rho> (Var v T \<degree>\<degree> targs)) (inst \<rho> u)" .
    qed
    have tl: "deqv ?E \<rho> dps" by (rule deqv_self[OF dt1]) (auto simp: dp_eqs_Cons)
    from hd tl show "deqv ?E \<rho> ((rb, Var v T \<degree>\<degree> targs, u) # dps)"
      using deqv_Cons[of ?E \<rho> "(rb, Var v T \<degree>\<degree> targs, u)" dps] by blast
  qed
qed

text \<open>The application of the abstraction is the simultaneous substitution:\<close>

lemma bind_cpy:
  assumes tys: "\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> s : U"
    and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
  shows "e \<turnstile> inst \<rho> (cpy targs s) : U"
    and "\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts s \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy targs s)"
proof -
  have ty: "e \<turnstile> inst \<rho> (types_abs Ts s \<degree>\<degree> targs) : U" by (rule typing_tabs_app[OF _ tya cert]) (use tys in blast)
  have len: "length Ts = length targs" using typings_nth[OF tya] by simp
  show "e \<turnstile> inst \<rho> (cpy targs s) : U" by (rule subject_reduction_beta'[OF inst_reds[OF beta_cpy[OF len]] ty])
  show "\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts s \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy targs s)"
    using conv_cpy(1)[OF ty _ len] by blast
qed

text \<open>Imitation: the pair of two applications of the same closed head decomposes.\<close>

lemma dstep_decomp:
  assumes c: "closed h" and vh: "vars h = {}" and l: "length ss = length us"
  shows "dstep env ((rb, h \<degree>\<degree> ss, h \<degree>\<degree> us) # dps) env (map (\<lambda>(s, u). (rb, s, u)) (zip ss us) @ dps)"
proof (rule dstepI[OF extends_refl])
  fix \<rho> env'' X assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env env''" and wte: "wt_env \<rho> env"
    and dt: "dtyped \<rho> ((rb, h \<degree>\<degree> ss, h \<degree>\<degree> us) # dps)"
    and vi: "vinv \<rho> env (X \<union> dvars ((rb, h \<degree>\<degree> ss, h \<degree>\<degree> us) # dps))"
  from dt obtain e U where bs: "bs_env \<rho> e rb" and tys: "e \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : U"
    and tyu: "e \<turnstile> inst \<rho> (h \<degree>\<degree> us) : U" and lbs: "\<not> loose_bvar (h \<degree>\<degree> ss) (ilength rb)"
    and lbu: "\<not> loose_bvar (h \<degree>\<degree> us) (ilength rb)" and dt1: "dtyped \<rho> dps"
    by auto
  from tys[unfolded inst_apps] obtain Ss where th1: "e \<turnstile> inst \<rho> h : Ss \<Rrightarrow> U"
    and ts: "e \<tturnstile> map (inst \<rho>) ss : Ss"
    by (rule list_app_typeE)
  from tyu[unfolded inst_apps] obtain Us where th2: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> U"
    and tu: "e \<tturnstile> map (inst \<rho>) us : Us"
    by (rule list_app_typeE)
  have ls: "length Ss = length ss" and lu: "length Us = length us"
    using typings_nth[OF ts] typings_nth[OF tu] by simp_all
  have "Ss \<Rrightarrow> U = Us \<Rrightarrow> U" by (rule typing_unique[OF th1 th2])
  with funs_eq[of Ss Us U U] ls lu l have SU: "Ss = Us" by simp
  let ?ps = "map (\<lambda>(s, u). (rb, s, u)) (zip ss us)"
  have mem: "\<exists>i<length ss. s = ss ! i \<and> u = us ! i" if "(rb', s, u) \<in> set ?ps" for rb' s u
    using that l by (auto simp: set_zip)
  have rb: "rb' = rb" if "(rb', s, u) \<in> set ?ps" for rb' s u using that by auto
  show "wt_env \<rho> env \<and> dtyped \<rho> (?ps @ dps) \<and> vinv \<rho> env (X \<union> dvars (?ps @ dps)) \<and>
      deqv (binds \<rho> env \<union> dp_eqs \<rho> (?ps @ dps)) \<rho> ((rb, h \<degree>\<degree> ss, h \<degree>\<degree> us) # dps)"
  proof (intro conjI)
    show "wt_env \<rho> env" by (fact wte)
    have "dtyped \<rho> ?ps"
      unfolding dtyped_def
    proof (intro ballI, clarify)
      fix rb' s u assume m: "(rb', s, u) \<in> set ?ps"
      from mem[OF m] obtain i where i: "i < length ss" "s = ss ! i" "u = us ! i" by blast
      have "e \<turnstile> inst \<rho> s : Ss ! i" using typings_nth[OF ts] i by simp
      moreover have "e \<turnstile> inst \<rho> u : Ss ! i" using typings_nth[OF tu] i l SU by simp
      moreover have "\<not> loose_bvar s (ilength rb)" "\<not> loose_bvar u (ilength rb)"
        using lbs lbu i l by (auto simp: loose_bvar_apps)
      ultimately show "(\<exists>e T. bs_env \<rho> e rb' \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
          \<not> loose_bvar s (ilength rb') \<and> \<not> loose_bvar u (ilength rb')"
        using bs rb[OF m] by blast
    qed
    with dt1 show "dtyped \<rho> (?ps @ dps)" by simp
    have "dvars ?ps \<subseteq> lvars ss \<union> lvars us"
      by (auto simp: dvars_def set_zip dest!: mem)
    then show "vinv \<rho> env (X \<union> dvars (?ps @ dps))"
      by (intro vinv_mono[OF vi]) (auto simp: vars_apps vh)
    let ?E = "binds \<rho> env \<union> dp_eqs \<rho> (?ps @ dps)"
    have hd: "deqv ?E \<rho> [(rb, h \<degree>\<degree> ss, h \<degree>\<degree> us)]"
      unfolding deqv_single
    proof (intro allI impI)
      fix e' U' assume a: "bs_env \<rho> e' rb" "e' \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : U'" "e' \<turnstile> inst \<rho> (h \<degree>\<degree> us) : U'"
      from a(2)[unfolded inst_apps] obtain Ss' where th1': "e' \<turnstile> inst \<rho> h : Ss' \<Rrightarrow> U'"
        and ts': "e' \<tturnstile> map (inst \<rho>) ss : Ss'"
        by (rule list_app_typeE)
      from a(3)[unfolded inst_apps] obtain Us' where th2': "e' \<turnstile> inst \<rho> h : Us' \<Rrightarrow> U'"
        and tu': "e' \<tturnstile> map (inst \<rho>) us : Us'"
        by (rule list_app_typeE)
      have "length Ss' = length ss" "length Us' = length us"
        using typings_nth[OF ts'] typings_nth[OF tu'] by simp_all
      with typing_unique[OF th1' th2'] funs_eq[of Ss' Us' U' U'] l have SU': "Ss' = Us'" by simp
      have "list_all2 (eqv ?E e') (map (inst \<rho>) ss) (map (inst \<rho>) us)"
      proof (rule list_all2_all_nthI)
        show "length (map (inst \<rho>) ss) = length (map (inst \<rho>) us)" using l by simp
        fix i assume "i < length (map (inst \<rho>) ss)"
        then have i: "i < length ss" by simp
        have m: "(rb, ss ! i, us ! i) \<in> set (?ps @ dps)" using i l by (auto simp: set_zip)
        have "e' \<turnstile> inst \<rho> (ss ! i) : Ss' ! i" "e' \<turnstile> inst \<rho> (us ! i) : Ss' ! i"
          using typings_nth[OF ts'] typings_nth[OF tu'] i l SU' by simp_all
        moreover have "\<not> loose_bvar (ss ! i) (ilength rb)" "\<not> loose_bvar (us ! i) (ilength rb)"
          using lbs lbu i l by (auto simp: loose_bvar_apps)
        ultimately have "eqv ?E e' (inst \<rho> (ss ! i)) (inst \<rho> (us ! i))"
          by (intro dp_eqs_use[OF m _ a(1)]) auto
        then show "eqv ?E e' (map (inst \<rho>) ss ! i) (map (inst \<rho>) us ! i)" using i l by simp
      qed
      from eqv_apps[OF this eqv_refl[OF th1']] a(2)
      show "eqv ?E e' (inst \<rho> (h \<degree>\<degree> ss)) (inst \<rho> (h \<degree>\<degree> us))" by (simp add: inst_apps)
    qed
    have tl: "deqv ?E \<rho> dps" by (rule deqv_self[OF dt1]) auto
    from hd tl show "deqv ?E \<rho> ((rb, h \<degree>\<degree> ss, h \<degree>\<degree> us) # dps)"
      using deqv_Cons[of ?E \<rho> "(rb, h \<degree>\<degree> ss, h \<degree>\<degree> us)" dps] by blast
  qed
qed

text \<open>A pair of two abstractions over the same type is the pair of their bodies:\<close>

lemma dstep_abs: "dstep env ((rb, Abs a T s, Abs a T u) # dps) env (((a, T) # rb, s, u) # dps)"
proof (rule dstepI[OF extends_refl])
  fix \<rho> env'' X assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env env''" and wte: "wt_env \<rho> env"
    and dt: "dtyped \<rho> ((rb, Abs a T s, Abs a T u) # dps)"
    and vi: "vinv \<rho> env (X \<union> dvars ((rb, Abs a T s, Abs a T u) # dps))"
  from dt obtain e U where bs: "bs_env \<rho> e rb" and tys: "e \<turnstile> inst \<rho> (Abs a T s) : U"
    and tyu: "e \<turnstile> inst \<rho> (Abs a T u) : U" and lbs: "\<not> loose_bvar (Abs a T s) (ilength rb)"
    and lbu: "\<not> loose_bvar (Abs a T u) (ilength rb)" and dt1: "dtyped \<rho> dps"
    by (simp only: dtyped_simps) blast
  from tys obtain W where U: "U = tsubst \<rho> T \<rightarrow>\<^sub>T W" and cT: "cert_typ alg ar (tsubst \<rho> T)"
    and tyb: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> s : W"
    by auto
  from tyu U have tyc: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> u : W" by auto
  have bs1: "bs_env \<rho> (e\<langle>0:tsubst \<rho> T\<rangle>) ((a, T) # rb)" by (rule bs_env_Cons[OF bs cT])
  show "wt_env \<rho> env \<and> dtyped \<rho> (((a, T) # rb, s, u) # dps) \<and> vinv \<rho> env (X \<union> dvars (((a, T) # rb, s, u) # dps)) \<and>
      deqv (binds \<rho> env \<union> dp_eqs \<rho> (((a, T) # rb, s, u) # dps)) \<rho> ((rb, Abs a T s, Abs a T u) # dps)"
  proof (intro conjI)
    show "wt_env \<rho> env" by (fact wte)
    show "dtyped \<rho> (((a, T) # rb, s, u) # dps)" using bs1 tyb tyc lbs lbu dt1 by auto
    show "vinv \<rho> env (X \<union> dvars (((a, T) # rb, s, u) # dps))" using vi by simp
    let ?E = "binds \<rho> env \<union> dp_eqs \<rho> (((a, T) # rb, s, u) # dps)"
    have hd: "deqv ?E \<rho> [(rb, Abs a T s, Abs a T u)]"
      unfolding deqv_single
    proof (intro allI impI)
      fix e' U' assume a: "bs_env \<rho> e' rb" "e' \<turnstile> inst \<rho> (Abs a T s) : U'" "e' \<turnstile> inst \<rho> (Abs a T u) : U'"
      from a(2) obtain W' where U': "U' = tsubst \<rho> T \<rightarrow>\<^sub>T W'" and cT': "cert_typ alg ar (tsubst \<rho> T)"
        and tyb': "e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> s : W'"
        by auto
      from a(3) U' have tyc': "e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> u : W'" by auto
      have "eqv ?E (e'\<langle>0:tsubst \<rho> T\<rangle>) (inst \<rho> s) (inst \<rho> u)"
        by (rule dp_eqs_use[OF _ _ bs_env_Cons[OF a(1) cT'] tyb' tyc']) (use lbs lbu in \<open>auto simp: algebra_simps\<close>)
      from eqv.eqv_abs[OF this cT', of a a]
      show "eqv ?E e' (inst \<rho> (Abs a T s)) (inst \<rho> (Abs a T u))" by simp
    qed
    have tl: "deqv ?E \<rho> dps" by (rule deqv_self[OF dt1]) (auto simp: dp_eqs_Cons)
    from hd tl show "deqv ?E \<rho> ((rb, Abs a T s, Abs a T u) # dps)"
      using deqv_Cons[of ?E \<rho> "(rb, Abs a T s, Abs a T u)" dps] by blast
  qed
qed

text \<open>The copy of an abstraction: the application of the abstraction of an abstraction.\<close>

lemma conv_abs_bind:
  assumes ty0: "e \<turnstile> inst \<rho> (types_abs Ts (Abs a T b') \<degree>\<degree> targs) : tsubst \<rho> T \<rightarrow>\<^sub>T W"
    and cT: "cert_typ alg ar (tsubst \<rho> T)" and len: "length Ts = length targs"
    and lbb: "\<not> loose_bvar b' (ilength Ts + 1)"
    and ty2: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> (cpy targs1 b') : W"
    and \<sigma>: "wt_subst \<sigma>" and targs1_def: "targs1 = map (\<lambda>t. lift t 0) targs @ [Bound 0]"
  shows "ap \<rho> \<sigma> (types_abs Ts (Abs a T b') \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs a T (cpy targs1 b'))"
proof -
  define W0 where "W0 = types_abs Ts (Abs a T b') \<degree>\<degree> targs"
  have cl: "closed (types_abs Ts (Abs a T b'))" by (rule closed_types_abs) (use lbb in simp)
  have len1: "length (map (\<lambda>T. (STR '''', T)) Ts @ [(a, T)]) = length targs1" using len by (simp add: targs1_def)
  have "lift W0 0 $ Bound 0 = abs_list (map (\<lambda>T. (STR '''', T)) Ts @ [(a, T)]) b' \<degree>\<degree> targs1"
    using incr_bv_no_loose[OF closed_loose_bvar[OF cl order_refl]]
    by (simp add: W0_def incr_bv_apps targs1_def types_abs_abs_list)
  then have b1: "lift W0 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* cpy targs1 b'" using beta_cpy_abs_list[OF len1] by simp
  have tyl: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> (lift W0 0 $ Bound 0) : W"
    using typing.App[OF lift_type[OF ty0[folded W0_def], of 0 "tsubst \<rho> T"] typing.Bound[of 0]] by simp
  have c1: "ap \<rho> \<sigma> (lift W0 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy targs1 b')"
    by (rule conv_beta_eta[OF wt_ap[OF tyl \<sigma>] beta_reds_ap[OF b1 \<sigma>]])
  have apl: "ap \<rho> \<sigma> (lift W0 0 $ Bound 0) = lift (ap \<rho> \<sigma> W0) 0 $ Bound 0"
    using \<sigma> by (simp add: ap_lift)
  have "e \<turnstile> Abs a (tsubst \<rho> T) (lift (ap \<rho> \<sigma> W0) 0 $ Bound 0) : tsubst \<rho> T \<rightarrow>\<^sub>T W"
    using typing.Abs[OF cT typing_ap[OF tyl \<sigma>, unfolded apl]] .
  then have wa: "wt (Abs a (tsubst \<rho> T) (lift (ap \<rho> \<sigma> W0) 0 $ Bound 0))" by (auto simp: wt_def)
  have "e \<turnstile> Abs a (tsubst \<rho> T) (ap \<rho> \<sigma> (cpy targs1 b')) : tsubst \<rho> T \<rightarrow>\<^sub>T W"
    using typing.Abs[OF cT typing_ap[OF ty2 \<sigma>]] .
  then have wb: "wt (Abs a (tsubst \<rho> T) (ap \<rho> \<sigma> (cpy targs1 b')))" by (auto simp: wt_def)
  have "ap \<rho> \<sigma> W0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> T) (lift (ap \<rho> \<sigma> W0) 0 $ Bound 0)"
    by (rule conv_sym, rule conv_eta_lift[OF wa])
  also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> T) (ap \<rho> \<sigma> (cpy targs1 b'))"
    by (rule conv_Abs[OF wa wb]) (use c1 apl in simp)
  finally show ?thesis by (simp add: W0_def)
qed

text \<open>Normalizing in a smaller environment:\<close>

lemma tconv_refl: "tconv env bs t t"
  by (auto simp: tconv_def intro: eqv_refl)

lemma tconv_extends:
  assumes tc: "tconv env bs t t'" and ext: "extends env env'"
  shows "tconv env' bs t t'"
  unfolding tconv_def
proof (intro conjI allI impI)
  show "vars t' \<subseteq> vars t \<union> evars env'" using tc evars_extends[OF ext] by (auto simp: tconv_def)
  fix \<rho> e T assume tsol: "tsol (tyenv env') \<rho>" and wte: "wt_env \<rho> env'" and bs: "bs_env \<rho> e bs"
    and ty: "e \<turnstile> inst \<rho> t : T" and lb: "\<not> loose_bvar t (ilength bs)"
  have "e \<turnstile> inst \<rho> t' : T \<and> \<not> loose_bvar t' (ilength bs) \<and> eqv (binds \<rho> env) e (inst \<rho> t) (inst \<rho> t')"
    using tc extends_tsol[OF tsol ext] wt_env_extends[OF wte ext] bs ty lb unfolding tconv_def by blast
  then have r: "e \<turnstile> inst \<rho> t' : T" "\<not> loose_bvar t' (ilength bs)" "eqv (binds \<rho> env) e (inst \<rho> t) (inst \<rho> t')"
    by blast+
  show "e \<turnstile> inst \<rho> t' : T" by (fact r(1))
  show "\<not> loose_bvar t' (ilength bs)" by (fact r(2))
  show "eqv (binds \<rho> env') e (inst \<rho> t) (inst \<rho> t')" by (rule eqv_mono[OF r(3) binds_extends[OF ext]])
qed

text \<open>Types are computed in the type environment:\<close>

lemma env_fastype_tyenv: "tyenv env' = tyenv env \<Longrightarrow> env_fastype env' Ts t = env_fastype env Ts t"
  by (induction env Ts t rule: env_fastype.induct) simp_all

lemma fastype_tyenv: "tyenv env' = tyenv env \<Longrightarrow> fastype env' rb t = fastype env rb t"
  unfolding fastype_def by (rule env_fastype_tyenv)

lemma bs_env_Nil: "bs_env \<rho> e []"
  by (simp add: bs_env_def)


lemma typing_vars_cert: "e \<turnstile> inst \<rho> t : U \<Longrightarrow> (v, T) \<in> vars t \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  by (induction t arbitrary: e U) auto

lemma make_args_Gs:
  assumes "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us" "G \<in> set Gs"
  shows "\<exists>x U. G = Var x U" "head_of G = G" "closed G"
proof -
  from assms(2) obtain k where k: "k < length Gs" "G = Gs ! k" by (auto simp: in_set_conv_nth)
  from list_all2_nthD[OF assms(1) k(1)] k(2) show "\<exists>x U. G = Var x U" by blast
  then show "head_of G = G" "closed G" by (auto simp: closed_def)
qed

text \<open>A projection on the argument \<open>targ\<close>: the variable is bound to the bound variable of the
  argument applied to new arguments.\<close>

lemma proj_dstep:
  assumes pu0: "okW (proj_unify cfg base bary Cs env0) env'" and g: "gentvars p env = (env0, Cs)"
    and st: "ok (strip_type env T) (Us, bary)" and pg: "p \<in> set (arity_guesses cfg bary)"
    and hk: "k < length targs" "head = Bound (integer_of_nat (length targs - 1 - k))" "targ = targs ! k"
      "T = Ts ! k"
    and Tsok: "ok (mapM (fastype env rb) targs) Ts"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow>
      e \<turnstile> inst \<rho> (Var (fst X) (snd X) \<degree>\<degree> targs) : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow> U = tsubst \<rho> base"
    and ma0: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
    and up: "ok (update X (types_abs Ts (list_comb head args)) env1) env2"
  shows "dstep env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps) env2
    ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
proof -
  obtain v TX where X: "X = (v, TX)" by (cases X)
  note g' = gentvars_props[OF g]
  have tv: "Cs \<noteq> [] \<longrightarrow> is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env0) v = None)"
  proof
    assume "Cs \<noteq> []"
    then have "is_TVar bary" using arity_guesses_TVar[OF pg] g'(4) by simp
    moreover have "ok (body_type env T) bary" using st by (auto simp: strip_type_def)
    ultimately show "is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env0) v = None)"
      using body_type_TVar[of env T] g'(2) by auto
  qed
  note pu = proj_unify_sound[OF pu0 tv]
  have ext0: "extends env env0" by (rule extends_tenv_eq) (use g' in simp_all)
  have ext': "extends env env'" by (rule extends_trans[OF ext0 pu(2)])
  have tenv': "tenv env' = tenv env" using pu(1) g'(1) by simp
  have lTs: "length Ts = length targs" by (rule mapM_fastype_sound(1)[OF Tsok])
  define j where "j = integer_of_nat (length targs - 1 - k)"
  have hj: "head = Bound j" "0 \<le> j" "j < ilength targs" "targ = targs ! (length targs - 1 - nat_of_integer j)"
    using hk by (auto simp: j_def ilength_eq integer_of_nat_less integer_of_nat_nonneg)
  have targ_in: "targ \<in> set targs" using hk by simp
  define UCs where "UCs = Us @ Cs"
  have ma: "make_args vname Ts env' UCs = (env1, args)" using ma0 by (simp add: UCs_def)
  show ?thesis
  proof -
    obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
      and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs UCs"
      and ma': "tenv env1 = tenv env'" "tyenv env1 = tyenv env'" "maxidx env' \<le> maxidx env1"
      and viG: "\<And>\<rho> Y. vinv \<rho> env' Y \<Longrightarrow> vinv \<rho> env1 (lvars Gs \<union> Y)"
      by (rule make_args_props[OF ma]) blast
    note GG = make_args_Gs[OF Gs]
    have ext1: "extends env env1" by (rule extends_trans[OF ext' extends_tenv_eq[OF ma']])
    have hd: "map (\<lambda>arg. head_of arg \<degree>\<degree> targs) args = map (\<lambda>G. G \<degree>\<degree> targs) Gs"
      by (auto simp: args head_of_apps GG(2))
    have ma2: "map (cpy targs) args = map (\<lambda>G. G \<degree>\<degree> targs) Gs"
      using lTs by (auto simp: args cpy_new_arg[OF GG(3)])
    have cpa: "cpy targs (head \<degree>\<degree> args) = targ \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs"
      by (simp only: hj(1) cpy_apps ma2 cpy_Bound[OF hj(2,3)] hj(4))
    have cp: "cpy targs (list_comb head args) = list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args)"
      by (simp only: list_comb_apps cpa hd)
    have va: "vars (head \<degree>\<degree> args) = lvars Gs" by (auto simp: hj(1) args vars_apps)
    have lbs: "\<not> loose_bvar (list_comb head args) (ilength Ts)"
    proof -
      have "\<not> loose_bvar (Bound j) (ilength Ts)" using hj(3) lTs by (simp add: ilength_eq)
      moreover have "\<not> loose_bvar a (ilength Ts)" if "a \<in> set args" for a
        using that GG(3) loose_bvar_bvs_ilength[of Ts, OF refl]
        by (auto simp: args loose_bvar_apps closed_loose_bvar)
      ultimately show ?thesis by (simp add: list_comb_apps loose_bvar_apps hj(1))
    qed
    have "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env2 ((rb, cpy targs (list_comb head args), u) # dps)"
    proof (rule dstep_bind[OF ext1 _ up[unfolded X] _ Tsok lbs])
      show "tenv env1 = tenv env" using ma'(1) tenv' by simp
      show "vinv \<rho> env1 (vars (list_comb head args) \<union> Y)" if "vinv \<rho> env Y" for \<rho> Y
        using viG[OF vinv_tenv[OF tenv' ext' that]] by (simp add: va list_comb_apps)
      show "vars (cpy targs (list_comb head args)) \<subseteq> vars (list_comb head args) \<union> lvars targs"
        unfolding list_comb_apps cpa va using targ_in by (auto simp: vars_apps)
      fix \<rho> e U assume tsol1: "tsol (tyenv env1) \<rho>" and bs: "bs_env \<rho> e rb"
        and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and tyu: "e \<turnstile> inst \<rho> u : U"
        and TT: "tsubst \<rho> TX = map (tsubst \<rho>) Ts \<Rrightarrow> U" and lb: "\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)"
        and cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
      have tsol': "tsol (tyenv env') \<rho>" using tsol1 ma'(2) by simp
      have tsol0: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol' ext'])
      have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu]) (use lb in simp)
      have tyV: "e \<turnstile> inst \<rho> (Var v TX) : map (tsubst \<rho>) Ts \<Rrightarrow> U"
        using cert cU by (auto simp: TT cert_typ_funs)
      have tyX: "e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : U"
        using list_app_typeI[OF tyV tya] by (simp add: inst_apps)
      have U: "U = tsubst \<rho> base" using bse[OF tsol0 bs _ tyu] tyX by (simp add: X)
      have tyg: "e \<turnstile> inst \<rho> targ : tsubst \<rho> T"
        using typings_nth[OF tya] hk lTs by force
      have T: "tsubst \<rho> T = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> bary"
        using strip_type_sound[OF st tsol0] .
      have cT: "cert_typ alg ar (tsubst \<rho> T)" by (rule bs_env_cert[OF bs tyg]) (use lb targ_in in auto)
      have "tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
        using pu(3)[OF tsol'] cU cT by (simp add: U T cert_typ_funs cert_wft)
      with tyg T U have tyg': "e \<turnstile> inst \<rho> targ : map (tsubst \<rho>) UCs \<Rrightarrow> U"
        by (simp add: tsubst_funs UCs_def)
      have ltarg: "\<not> loose_bvar targ (ilength rb)" using lb targ_in by simp
      have cUs: "\<forall>U'\<in>set UCs. cert_typ alg ar (tsubst \<rho> U')"
        using bs_env_cert[OF bs tyg' ltarg] by (simp add: cert_typ_funs)
      have lGs: "length Gs = length UCs" by (rule list_all2_lengthD[OF Gs])
      have tyGk: "e' \<turnstile> inst \<rho> (Gs ! i) : map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> (UCs ! i)" if "i < length Gs" for e' i
      proof -
        from list_all2_nthD[OF Gs that] obtain x where "Gs ! i = Var x (Ts \<Rrightarrow> (UCs ! i))" by blast
        moreover have "cert_typ alg ar (tsubst \<rho> (UCs ! i))" using cUs that lGs by simp
        ultimately show ?thesis using cert by (auto simp: tsubst_funs cert_typ_funs)
      qed
      have jT: "pushes e' (map (tsubst \<rho>) Ts) j = map (tsubst \<rho>) UCs \<Rrightarrow> U" for e'
      proof -
        have jl: "nat_of_integer j < length targs" using hj(2,3) nat_of_integer_less_ilength by blast
        have "j < ilength (map (tsubst \<rho>) Ts)" using hj(3) lTs by (simp add: ilength_eq)
        then have "pushes e' (map (tsubst \<rho>) Ts) j = rev (map (tsubst \<rho>) Ts) ! nat_of_integer j"
          using hj(2) by (simp add: pushes_nth)
        also have "\<dots> = tsubst \<rho> (Ts ! (length targs - 1 - nat_of_integer j))" using jl lTs by (simp add: rev_nth)
        also have "\<dots> = map (tsubst \<rho>) UCs \<Rrightarrow> U"
        proof -
          have "e \<turnstile> inst \<rho> (targs ! (length targs - 1 - nat_of_integer j)) :
              tsubst \<rho> (Ts ! (length targs - 1 - nat_of_integer j))"
            using typings_nth[OF tya] jl lTs by force
          with tyg' hj(4) show ?thesis by (simp add: typing_unique)
        qed
        finally show ?thesis .
      qed
      have tyargs: "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) args : map (tsubst \<rho>) UCs" for e'
        unfolding typings_iff
      proof (rule list_all2_all_nthI)
        fix i assume "i < length (map (inst \<rho>) args)"
        then have i: "i < length Gs" by (simp add: args)
        have "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Gs ! i) \<degree>\<degree> bvs (length (map (tsubst \<rho>) Ts)) :
            tsubst \<rho> (UCs ! i)"
          by (rule list_app_typeI[OF tyGk[OF i] typings_bvs])
        then show "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> map (inst \<rho>) args ! i : map (tsubst \<rho>) UCs ! i"
          using i lGs by (simp add: args inst_apps comp_def)
      qed (simp add: args lGs)
      have tyc0: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb head args) : U" for e'
        using list_app_typeI[OF typing.Bound[where e="pushes e' (map (tsubst \<rho>) Ts)", OF hj(2) jT] tyargs[of e']]
        by (simp add: list_comb_apps inst_apps hj(1))
      have tyc: "\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb head args) : U" using tyc0 by blast
      note bc = bind_cpy[OF tyc tya cert]
      have "\<not> loose_bvar (cpy targs (list_comb head args)) (ilength rb)"
        using ltarg lb GG(3) by (auto simp: list_comb_apps cpa loose_bvar_apps closed_loose_bvar)
      with tyc bc show "(\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb head args) : U) \<and>
          \<not> loose_bvar (cpy targs (list_comb head args)) (ilength rb) \<and>
          e \<turnstile> inst \<rho> (cpy targs (list_comb head args)) : U \<and>
          (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts (list_comb head args) \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
            ap \<rho> \<sigma> (cpy targs (list_comb head args)))"
        by blast
    qed
    then show ?thesis by (simp only: cp X fst_conv snd_conv)
  qed
qed

lemma projenv_sinv:
  assumes pe: "okW (projenv cfg vname rb targs u env dps X base Ts head Usb targ p tail) s"
    and tl: "seqinv (GE env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)) tail"
    and st: "ok (strip_type env T) Usb" and pg: "p \<in> set (arity_guesses cfg (snd Usb))"
    and hk: "k < length targs" "head = Bound (integer_of_nat (length targs - 1 - k))" "targ = targs ! k"
      "T = Ts ! k"
    and Tsok: "ok (mapM (fastype env rb) targs) Ts"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow>
      e \<turnstile> inst \<rho> (Var (fst X) (snd X) \<degree>\<degree> targs) : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow> U = tsubst \<rho> base"
  shows "seqinv (GE env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)) s"
proof -
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by fastforce
  from okW_handle_CANTUNIFY[OF pe[unfolded projenv_def Usb g prod.case]]
  consider (ok) env' where "okW (proj_unify cfg base bary Cs env0) env'"
      "s = S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ X tail"
    | (cu) "s = tail"
    by auto
  then show ?thesis
  proof cases
    case (ok env')
    note pd = proj_dstep[OF ok(1) g st[unfolded Usb] pg[unfolded Usb snd_conv] hk Tsok bse]
    from tl ok(2) show ?thesis by (auto intro!: seqinv.Proj intro: pd)
  qed (use tl in simp)
qed

text \<open>The copies of the arguments into their new variables:\<close>

lemma copyargs_sinv:
  "dstep env0 dps0 env1 (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) gus @ dps) \<Longrightarrow> extends envM env1 \<Longrightarrow>
    \<forall>(G, uarg)\<in>set gus. \<exists>x U. G = Var x U \<Longrightarrow>
    seqinv (GE env0 dps0) (copyargs vname envM rb targs gus env1 dps)"
proof (induction gus arbitrary: env0 dps0)
  case Nil
  then show ?case by (auto intro: seqinv.Single)
next
  case (Cons gu gus)
  obtain G uarg where gu: "gu = (G, uarg)" by (cases gu)
  have "seqinv (GE env1 (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) gus @ dps)) (copyargs vname envM rb targs gus env1 dps)"
    by (rule Cons.IH[OF dstep_refl]) (use Cons.prems in auto)
  with Cons.prems show ?case by (auto simp: gu intro!: seqinv.Maps)
qed

text \<open>Imitation: the variable is bound to the head applied to new arguments, into which the
  arguments are copied.\<close>

lemma imit_dstep:
  assumes Us: "ok (mapM (fastype env rb) uargs) Us" and ma: "make_args vname Ts env Us = (env', args)"
    and up: "ok (update X (types_abs Ts (list_comb uhead args)) env') env''"
    and u: "u = uhead \<degree>\<degree> uargs" and c: "closed uhead" "vars uhead = {}"
    and Tsok: "ok (mapM (fastype env rb) targs) Ts"
  shows "dstep env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps) env''
    (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) (zip (map head_of args) uargs) @ dps)"
proof -
  obtain v TX where X: "X = (v, TX)" by (cases X)
  have up': "ok (update (v, TX) (types_abs Ts (list_comb uhead args)) env') env''" using up by (simp add: X)
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    and ma': "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    and viG: "\<And>\<rho> Y. vinv \<rho> env Y \<Longrightarrow> vinv \<rho> env' (lvars Gs \<union> Y)"
    by (rule make_args_props[OF ma]) blast
  note GG = make_args_Gs[OF Gs]
  have lTs: "length Ts = length targs" by (rule mapM_fastype_sound(1)[OF Tsok])
  have lUs: "length Us = length uargs" by (rule mapM_fastype_sound(1)[OF Us])
  have lGs: "length Gs = length Us" by (rule list_all2_lengthD[OF Gs])
  have ext1: "extends env env'" by (rule extends_tenv_eq[OF ma'])
  have hd: "map head_of args = Gs" by (auto simp: args head_of_apps GG(2) intro!: map_idI)
  have ma2: "map (cpy targs) args = map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    using lTs by (auto simp: args cpy_new_arg[OF GG(3)])
  have cp: "cpy targs (list_comb uhead args) = uhead \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    by (simp only: list_comb_apps cpy_apps ma2 cpy_closed[OF c(1)])
  have va: "vars (list_comb uhead args) = lvars Gs" by (auto simp: list_comb_apps args vars_apps c(2))
  have lbs: "\<not> loose_bvar (list_comb uhead args) (ilength Ts)"
    using GG(3) c(1) loose_bvar_bvs_ilength[of Ts, OF refl]
    by (auto simp: args list_comb_apps loose_bvar_apps closed_loose_bvar)
  have d1: "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      ((rb, cpy targs (list_comb uhead args), u) # dps)"
  proof (rule dstep_bind[OF ext1 ma'(1) up' _ Tsok lbs])
    show "vinv \<rho> env' (vars (list_comb uhead args) \<union> Y)" if "vinv \<rho> env Y" for \<rho> Y
      using viG[OF that] by (simp add: va)
    show "vars (cpy targs (list_comb uhead args)) \<subseteq> vars (list_comb uhead args) \<union> lvars targs"
      by (auto simp: cp va vars_apps c(2))
    fix \<rho> e U assume tsol1: "tsol (tyenv env') \<rho>" and bs: "bs_env \<rho> e rb"
      and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and tyu: "e \<turnstile> inst \<rho> u : U"
      and TT: "tsubst \<rho> TX = map (tsubst \<rho>) Ts \<Rrightarrow> U" and lb: "\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)"
      and cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
    have tsol0: "tsol (tyenv env) \<rho>" using tsol1 ma'(2) by simp
    from tyu[unfolded u inst_apps] obtain Vs where th: "e \<turnstile> inst \<rho> uhead : Vs \<Rrightarrow> U"
      and tus: "e \<tturnstile> map (inst \<rho>) uargs : Vs"
      by (rule list_app_typeE)
    have Vs: "map (tsubst \<rho>) Us = Vs" by (rule mapM_fastype_sound(2)[OF Us tsol0 bs tus])
    have luargs: "\<forall>t\<in>set uargs. \<not> loose_bvar t (ilength rb)" using lb by (auto simp: u loose_bvar_apps)
    have cVs: "\<forall>U'\<in>set Us. cert_typ alg ar (tsubst \<rho> U')"
    proof
      fix U' assume "U' \<in> set Us"
      then obtain i where i: "i < length Us" "U' = Us ! i" by (auto simp: in_set_conv_nth)
      have "e \<turnstile> inst \<rho> (uargs ! i) : Vs ! i" using typings_nth[OF tus] i lUs by simp
      then have "cert_typ alg ar (Vs ! i)" by (rule bs_env_cert[OF bs]) (use luargs i lUs in simp)
      then show "cert_typ alg ar (tsubst \<rho> U')" using i Vs[symmetric] by simp
    qed
    have tyGi: "e' \<turnstile> inst \<rho> (Gs ! i) : map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> (Us ! i)" if "i < length Gs" for e' i
    proof -
      from list_all2_nthD[OF Gs that] obtain x where "Gs ! i = Var x (Ts \<Rrightarrow> (Us ! i))" by blast
      moreover have "cert_typ alg ar (tsubst \<rho> (Us ! i))" using cVs that lGs by simp
      ultimately show ?thesis using cert by (auto simp: tsubst_funs cert_typ_funs)
    qed
    have tyargs: "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) args : Vs" for e'
      unfolding typings_iff
    proof (rule list_all2_all_nthI)
      fix i assume "i < length (map (inst \<rho>) args)"
      then have i: "i < length Gs" by (simp add: args)
      have "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Gs ! i) \<degree>\<degree> bvs (length (map (tsubst \<rho>) Ts)) : tsubst \<rho> (Us ! i)"
        by (rule list_app_typeI[OF tyGi[OF i] typings_bvs])
      then show "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> map (inst \<rho>) args ! i : Vs ! i"
        using i lGs Vs[symmetric] by (simp add: args inst_apps comp_def)
    qed (simp add: args lGs Vs[symmetric])
    have thc: "e' \<turnstile> inst \<rho> uhead : Vs \<Rrightarrow> U" for e' by (rule typing_closed[OF th closed_inst[OF c(1)]])
    have tyc: "\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb uhead args) : U"
      using list_app_typeI[OF thc tyargs] by (simp add: list_comb_apps inst_apps)
    note bc = bind_cpy[OF tyc tya cert]
    have "\<not> loose_bvar (cpy targs (list_comb uhead args)) (ilength rb)"
      using lb GG(3) c(1) by (auto simp: cp loose_bvar_apps closed_loose_bvar)
    with tyc bc show "(\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb uhead args) : U) \<and>
        \<not> loose_bvar (cpy targs (list_comb uhead args)) (ilength rb) \<and>
        e \<turnstile> inst \<rho> (cpy targs (list_comb uhead args)) : U \<and>
        (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts (list_comb uhead args) \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
          ap \<rho> \<sigma> (cpy targs (list_comb uhead args)))"
      by blast
  qed
  have l2: "length (map (\<lambda>G. G \<degree>\<degree> targs) Gs) = length uargs" using lGs lUs by simp
  have d2: "dstep env'' ((rb, uhead \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs, uhead \<degree>\<degree> uargs) # dps) env''
      (map (\<lambda>(s, u). (rb, s, u)) (zip (map (\<lambda>G. G \<degree>\<degree> targs) Gs) uargs) @ dps)"
    by (rule dstep_decomp[OF c l2])
  have zz: "map (\<lambda>(s, u). (rb, s, u)) (zip (map (\<lambda>G. G \<degree>\<degree> targs) Gs) uargs) =
      map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) (zip Gs uargs)"
    by (simp add: zip_map1 comp_def split_def)
  have ext2: "extends env env''" by (rule extends_trans[OF ext1 extends_update[OF up']])
  have d1': "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      ((rb, uhead \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs, uhead \<degree>\<degree> uargs) # dps)"
    using d1 by (simp only: cp u)
  show ?thesis using dstep_trans[OF d1' d2] by (simp only: zz hd X fst_conv snd_conv)
qed

lemma imitate_sinv:
  assumes im: "okW (imitate vname envM rb targs env dps X Ts uhead uargs) s"
    and u: "u = uhead \<degree>\<degree> uargs" and c: "closed uhead" "vars uhead = {}"
    and Tsok: "ok (mapM (fastype env rb) targs) Ts" and extM: "extends envM env"
  shows "seqinv (GE env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)) s"
proof -
  from im[unfolded imitate_def okW_bindW okW_liftM] obtain Us where Us: "ok (mapM (fastype env rb) uargs) Us"
    and r: "okW (case make_args vname Ts env Us of (env', args) \<Rightarrow> do {
        env'' \<leftarrow> liftM (update X (types_abs Ts (list_comb uhead args)) env');
        returnW (copyargs vname envM rb targs (zip (map head_of args) uargs) env'' dps)}) s"
    by blast
  obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by fastforce
  from r ma obtain env'' where up: "ok (update X (types_abs Ts (list_comb uhead args)) env') env''"
    and s: "s = copyargs vname envM rb targs (zip (map head_of args) uargs) env'' dps"
    by auto
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    and ma': "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    by (rule make_args_props[OF ma]) blast
  note GG = make_args_Gs[OF Gs]
  have hd: "map head_of args = Gs" by (auto simp: args head_of_apps GG(2) intro!: map_idI)
  obtain v TX where X: "X = (v, TX)" by (cases X)
  have ext2: "extends env env''" by (rule extends_trans[OF extends_tenv_eq[OF ma'] extends_update[OF up[unfolded X]]])
  show ?thesis unfolding s
  proof (rule copyargs_sinv)
    show "dstep env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps) env''
        (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) (zip (map head_of args) uargs) @ dps)"
      by (rule imit_dstep[OF Us ma up u c Tsok])
    show "extends envM env''" by (rule extends_trans[OF extM ext2])
    show "\<forall>(G, uarg)\<in>set (zip (map head_of args) uargs). \<exists>x U. G = Var x U"
      using GG(1) by (auto simp: hd dest: set_zip_leftD)
  qed
qed

lemma make_projs_props:
  "okW (make_projs u targs0 Ts targs) ps \<Longrightarrow> length Ts = length targs \<and>
    (\<forall>q\<in>set ps. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k))"
proof (induction u targs0 Ts targs arbitrary: ps rule: make_projs.induct)
  case (1 u targs0 T Ts targ targs)
  from "1.prems" obtain ps' where ps': "okW (make_projs u targs0 Ts targs) ps'"
    and ps: "ps = (Bound (ilength Ts), T, targ) # ps'" by auto
  note IH = "1.IH"[OF ps']
  have "\<exists>k<length (targ # targs). q = (Bound (integer_of_nat (length (targ # targs) - 1 - k)),
      (T # Ts) ! k, (targ # targs) ! k)" if "q \<in> set ps" for q
  proof -
    from that ps consider "q = (Bound (ilength Ts), T, targ)" | "q \<in> set ps'" by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using IH by (intro exI[of _ 0]) (simp add: ilength_eq)
    next
      case 2
      with IH obtain k where "k < length targs"
        "q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k)" by blast
      then show ?thesis by (intro exI[of _ "Suc k"]) simp
    qed
  qed
  with IH show ?case by simp
qed auto

lemma matchfun_sinv:
  assumes "okW (matchfun cfg vname envM rb targs u env dps X uhead uargs base Ts projs) s"
    and projs: "\<forall>q\<in>set projs. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k)"
    and u: "u = uhead \<degree>\<degree> uargs" and Tsok: "ok (mapM (fastype env rb) targs) Ts"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow>
      e \<turnstile> inst \<rho> (Var (fst X) (snd X) \<degree>\<degree> targs) : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow> U = tsubst \<rho> base"
    and extM: "extends envM env"
  shows "seqinv (GE env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)) s"
  using assms(1,2)
proof (induction projs arbitrary: s)
  case Nil
  then show ?case
    by (cases uhead)
      (auto simp: closed_def intro: imitate_sinv[OF _ u _ _ Tsok extM] seqinv.Empty)
next
  case (Cons q projs)
  obtain bvar T targ where q: "q = (bvar, T, targ)" by (cases q)
  from Cons.prems(2) q obtain k where hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    "T = Ts ! k" "targ = targs ! k" by auto
  from Cons.prems(1)[unfolded q matchfun.simps] obtain Usb tail where st: "ok (strip_type env T) Usb"
    and mt: "okW (matchfun cfg vname envM rb targs u env dps X uhead uargs base Ts projs) tail"
    and fo: "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts bvar Usb targ)
      (arity_guesses cfg (snd Usb)) tail) s"
    by auto
  let ?G = "GE env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)"
  have tl: "seqinv ?G tail" by (rule Cons.IH[OF mt]) (use Cons.prems(2) in auto)
  have "seqinv ?G tail \<longrightarrow> set ps \<subseteq> set (arity_guesses cfg (snd Usb)) \<longrightarrow> seqinv ?G s'"
    if "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts bvar Usb targ) ps tail) s'" for ps s'
    using that
  proof (induction rule: okW_foldrW_induct)
    case (Cons p ps b b1 b')
    show ?case
    proof (intro impI)
      assume b: "seqinv ?G b" and ss: "set (p # ps) \<subseteq> set (arity_guesses cfg (snd Usb))"
      with Cons.IH have b1: "seqinv ?G b1" by simp
      show "seqinv ?G b'"
        by (rule projenv_sinv[OF Cons.hyps(2) b1 st _ hk(1,2) hk(4,3) Tsok bse]) (use ss in auto)
    qed
  qed simp
  with fo tl show ?case by blast
qed


subsection \<open>Copies\<close>

text \<open>The successful runs of \<^const>\<open>mc\<close>:\<close>

lemma mc_okW_cases [consumes 1]:
  assumes "okW (mc cfg vname envM (v, TX) rb targs u env dps) s"
  obtains (asg) r where "ok (lookup env v TX) (Some r)"
      "s = S_Single (El_E env ((rb, list_comb (Var v TX) targs, u) # dps))"
  | (abs) a A body Ts B env' Y Y' env'' where "ok (lookup env v TX) None" "fst (strip_comb u) = Abs a A body"
      "ok (mapM (fastype env rb) targs) Ts" "ok (fastype env ((a, A) # rb) body) B"
      "genvar vname env (foldr fun_type (Ts @ [A]) B) = (env', Y)" "okW (dest_Var Y) Y'"
      "ok (update (v, TX) (types_abs Ts (Abs a A (combound Y 0 (Suc (length Ts))))) env') env''"
      "okW (mc cfg vname envM Y' ((a, A) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps) s"
  | (var) w W T0 base Ts env' newhd env'' where "ok (lookup env v TX) None" "fst (strip_comb u) = Var w W"
      "ok (fastype env rb (Var w W)) T0" "ok (body_type env T0) base" "ok (mapM (fastype env rb) targs) Ts"
      "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)"
      "ok (update (v, TX) (types_abs Ts (combound newhd 0 (length Ts))) env') env''"
      "s = S_Single (El_E env'' ((rb, list_comb newhd targs, u) # dps))"
  | (rigid) T0 base Ts projs where "ok (lookup env v TX) None" "\<not> is_Abs (fst (strip_comb u))"
      "\<not> is_Var (fst (strip_comb u))" "ok (fastype env rb (fst (strip_comb u))) T0" "ok (body_type env T0) base"
      "ok (mapM (fastype env rb) targs) Ts" "okW (make_projs u targs Ts targs) projs"
      "okW (matchfun cfg vname envM rb targs u env dps (v, TX) (fst (strip_comb u)) (snd (strip_comb u))
        base Ts (rev projs)) s"
proof -
  have rig: "(case h of Abs a T b \<Rightarrow> f a T b | Var w W \<Rightarrow> g w W | _ \<Rightarrow> R) = R"
    if "\<not> is_Abs h" "\<not> is_Var h" for h and f :: "name \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> seq W" and g R
    using that by (cases h) simp_all
  note m0 = assms[unfolded mc.simps[of cfg vname envM "(v, TX)" rb targs u env dps] Let_def case_prod_beta
    fst_conv snd_conv]
  show ?thesis
  proof (cases "\<exists>r'. ok (lookup env v TX) (Some r')")
    case True
    then obtain r' where lk: "ok (lookup env v TX) (Some r')" by blast
    from m0 lk have "s = S_Single (El_E env ((rb, list_comb (Var v TX) targs, u) # dps))" by auto
    with lk show ?thesis by (rule asg)
  next
    case False
    from m0 False have lk: "ok (lookup env v TX) None" by (auto split: if_splits)
    show ?thesis
    proof (cases "fst (strip_comb u)")
      case (Abs a A body)
      from m0 lk Abs obtain Ts B Y' env'' where Ts: "ok (mapM (fastype env rb) targs) Ts"
        and B: "ok (fastype env ((a, A) # rb) body) B"
        and r: "okW (dest_Var (snd (genvar vname env (foldr fun_type (Ts @ [A]) B)))) Y'"
        and up: "ok (update (v, TX) (types_abs Ts (Abs a A (combound (snd (genvar vname env (foldr fun_type (Ts @ [A]) B))) 0
          (Suc (length Ts))))) (fst (genvar vname env (foldr fun_type (Ts @ [A]) B)))) env''"
        and mc': "okW (mc cfg vname envM Y' ((a, A) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps) s"
        by (auto simp del: combound.simps foldr_append)
      show ?thesis
        by (rule abs[OF lk Abs Ts B prod.collapse[symmetric] r up mc'])
    next
      case (Var w W)
      from m0 lk Var obtain T0 base Ts env'' where T0: "ok (fastype env rb (Var w W)) T0"
        and base: "ok (body_type env T0) base" and Ts: "ok (mapM (fastype env rb) targs) Ts"
        and up: "ok (update (v, TX) (types_abs Ts (combound (snd (genvar (fst w) env (foldr fun_type Ts base))) 0 (length Ts)))
          (fst (genvar (fst w) env (foldr fun_type Ts base)))) env''"
        and s: "s = S_Single (El_E env'' ((rb, list_comb (snd (genvar (fst w) env (foldr fun_type Ts base))) targs, u) # dps))"
        by (auto simp del: combound.simps)
      show ?thesis
        by (rule var[OF lk Var T0 base Ts prod.collapse[symmetric] up s])
    next
      case (Const c C)
      then have na: "\<not> is_Abs (fst (strip_comb u))" "\<not> is_Var (fst (strip_comb u))" by simp_all
      from m0 lk na show ?thesis by (auto simp: rig intro: rigid)
    next
      case (Free c C)
      then have na: "\<not> is_Abs (fst (strip_comb u))" "\<not> is_Var (fst (strip_comb u))" by simp_all
      from m0 lk na show ?thesis by (auto simp: rig intro: rigid)
    next
      case (Bound i)
      then have na: "\<not> is_Abs (fst (strip_comb u))" "\<not> is_Var (fst (strip_comb u))" by simp_all
      from m0 lk na show ?thesis by (auto simp: rig intro: rigid)
    next
      case (App f x)
      then have na: "\<not> is_Abs (fst (strip_comb u))" "\<not> is_Var (fst (strip_comb u))" by simp_all
      from m0 lk na show ?thesis by (auto simp: rig intro: rigid)
    qed
  qed
qed

text \<open>
  The rigid side is saturated: its abstractions have no arguments, and otherwise its type is the
  body type of the type of its head, for every type instantiation.
\<close>

function satd :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "satd env rb u =
    (case fst (strip_comb u) of
      Abs a T b \<Rightarrow> snd (strip_comb u) = [] \<and> satd env ((a, T) # rb) b
    | _ \<Rightarrow> (\<forall>T0 B \<rho> e U. ok (fastype env rb (fst (strip_comb u))) T0 \<longrightarrow> ok (body_type env T0) B \<longrightarrow>
        tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow> U = tsubst \<rho> B))"
  by auto
termination
  by (relation "measure (\<lambda>(env, rb, u). size u)") (auto dest: strip_comb_Abs_size)

declare satd.simps[simp del]

lemma satd_Abs:
  "fst (strip_comb u) = Abs a T b \<Longrightarrow> satd env rb u \<Longrightarrow> snd (strip_comb u) = [] \<and> satd env ((a, T) # rb) b"
  by (subst (asm) satd.simps) simp

lemma satd_base:
  "\<not> is_Abs (fst (strip_comb u)) \<Longrightarrow> satd env rb u \<Longrightarrow> ok (fastype env rb (fst (strip_comb u))) T0 \<Longrightarrow>
    ok (body_type env T0) B \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
    U = tsubst \<rho> B"
  by (subst (asm) satd.simps) (auto split: pterm.splits)

text \<open>The saturation depends only on the type environment:\<close>

lemma satd_tyenv:
  assumes "satd env rb u" "tyenv env' = tyenv env"
  shows "satd env' rb u"
  using assms
proof (induction "size u" arbitrary: rb u rule: less_induct)
  case less
  show ?case
  proof (cases "is_Abs (fst (strip_comb u))")
    case True
    then obtain a T b where Abs: "fst (strip_comb u) = Abs a T b" by (cases "fst (strip_comb u)") auto
    from satd_Abs[OF Abs less.prems(1)] have n: "snd (strip_comb u) = []" and sb: "satd env ((a, T) # rb) b"
      by simp_all
    have "satd env' ((a, T) # rb) b" by (rule less.hyps[OF strip_comb_Abs_size[OF Abs] sb less.prems(2)])
    with n Abs show ?thesis by (subst satd.simps) simp
  next
    case na: False
    have "U = tsubst \<rho> B" if "ok (fastype env' rb (fst (strip_comb u))) T0" "ok (body_type env' T0) B"
      "tsol (tyenv env') \<rho>" "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> u : U" for T0 B \<rho> e U
    proof (rule satd_base[OF na less.prems(1)])
      show "ok (fastype env rb (fst (strip_comb u))) T0" using that(1) fastype_tyenv[OF less.prems(2)] by simp
      show "ok (body_type env T0) B" using body_type_tyenv[OF that(2)] less.prems(2) by simp
      show "tsol (tyenv env) \<rho>" using that(3) less.prems(2) by simp
    qed (use that in auto)
    then show ?thesis using na by (subst satd.simps) (auto split: pterm.splits)
  qed
qed

text \<open>
  The rigid side \<open>u\<close> of a pair with the flexible side \<open>t\<close> is saturated if its type is the body
  type of the type of its head whenever both sides are well-typed with the same type. (Unlike
  \<^const>\<open>satd\<close>, this restricts only the typings of \<open>u\<close> in which \<open>t\<close> has the same type.)
\<close>

definition rsat :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "rsat env rb t u \<longleftrightarrow> (\<forall>T0 B \<rho> e U. ok (fastype env rb (fst (strip_comb u))) T0 \<longrightarrow>
    ok (body_type env T0) B \<longrightarrow> tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow>
    e \<turnstile> inst \<rho> t : U \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow> U = tsubst \<rho> B)"

text \<open>The hypothesis of \<^const>\<open>mc\<close>, for the pair \<open>t =?= u\<close> (\<open>ot = Some t\<close>) or for all typings:\<close>

definition msat :: "pterm option \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "msat ot env rb u \<longleftrightarrow> (case ot of None \<Rightarrow> satd env rb u
    | Some t \<Rightarrow> \<not> is_Abs (fst (strip_comb u)) \<and> rsat env rb t u)"

lemma map_incr_boundvars_lift: "map (incr_boundvars 1) ts = map (\<lambda>t. lift t 0) ts"
  by (simp add: incr_boundvars_def)

lemma mc_abs_step:
  assumes abs: "ok (lookup env v TX) None" "fst (strip_comb u) = Abs a A body"
      "ok (mapM (fastype env rb) targs) Ts" "ok (fastype env ((a, A) # rb) body) B"
      "genvar vname env (foldr fun_type (Ts @ [A]) B) = (env', Y)" "okW (dest_Var Y) Y'"
      "ok (update (v, TX) (types_abs Ts (Abs a A (combound Y 0 (Suc (length Ts))))) env') env''"
    and sat: "satd env rb u"
  shows "u = Abs a A body" "Y = Var (fst Y') (snd Y')"
    "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      (((a, A) # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps)"
    "tyenv env'' = tyenv env" "extends env env''" "satd env'' ((a, A) # rb) body"
proof -
  from satd_Abs[OF abs(2) sat] have na: "snd (strip_comb u) = []" and sb: "satd env ((a, A) # rb) body"
    by simp_all
  have "strip_comb u = (Abs a A body, [])" using abs(2) na by (metis prod.collapse)
  then have u: "u = Abs a A body" using strip_comb_apps by fastforce
  note g = genvar_simps[OF abs(5)]
  have Y: "Y = Var (vname, maxidx env + 1) (foldr fun_type (Ts @ [A]) B)" by (rule g(4))
  with abs(6) have Y': "Y' = ((vname, maxidx env + 1), foldr fun_type (Ts @ [A]) B)" by simp
  have lTs: "length Ts = length targs" by (rule mapM_fastype_sound(1)[OF abs(3)])
  define targs1 where "targs1 = map (\<lambda>t. lift t 0) targs @ [Bound 0]"
  have lt1: "length targs1 = Suc (length Ts)" using lTs by (simp add: targs1_def)
  have cb: "combound Y 0 (Suc (length Ts)) = Y \<degree>\<degree> bvs (length targs1)" unfolding lt1 by (rule combound_bvs)
  have clY: "closed Y" by (simp add: Y closed_def)
  have cp: "cpy targs1 (Y \<degree>\<degree> bvs (length targs1)) = Y \<degree>\<degree> targs1" by (rule cpy_new_arg[OF clY])
  have ext1: "extends env env'" by (rule extends_genvar[OF abs(5)])
  have lbb: "\<not> loose_bvar (Y \<degree>\<degree> bvs (length targs1)) (ilength Ts + 1)"
  proof -
    have "ilength Ts + 1 = ilength (Ts @ [A])" by simp
    moreover have "\<forall>t\<in>set (bvs (length targs1)). \<not> loose_bvar t (ilength (Ts @ [A]))"
      using loose_bvar_bvs_ilength[of "Ts @ [A]" "length targs1"] lt1 by simp
    ultimately show ?thesis using clY by (simp add: loose_bvar_apps closed_loose_bvar)
  qed
  have d1: "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      ((rb, Abs a A (Y \<degree>\<degree> targs1), u) # dps)"
  proof (rule dstep_bind[OF ext1 g(1) abs(7) _ abs(3)])
    show "vinv \<rho> env' (vars (Abs a A (combound Y 0 (Suc (length Ts)))) \<union> Z)" if "vinv \<rho> env Z" for \<rho> Z
      using vinv_genvar[OF abs(5) that] unfolding cb by (simp add: vars_apps)
    show "\<not> loose_bvar (Abs a A (combound Y 0 (Suc (length Ts)))) (ilength Ts)"
      using lbb unfolding cb by simp
    show "vars (Abs a A (Y \<degree>\<degree> targs1)) \<subseteq> vars (Abs a A (combound Y 0 (Suc (length Ts)))) \<union> lvars targs"
      unfolding cb by (auto simp: vars_apps targs1_def)
    fix \<rho> e U assume tsol1: "tsol (tyenv env') \<rho>" and bs: "bs_env \<rho> e rb"
      and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and tyu: "e \<turnstile> inst \<rho> u : U"
      and TT: "tsubst \<rho> TX = map (tsubst \<rho>) Ts \<Rrightarrow> U" and lb: "\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)"
      and cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
    have tsol: "tsol (tyenv env) \<rho>" using tsol1 g(2) by simp
    from tyu obtain W where U: "U = tsubst \<rho> A \<rightarrow>\<^sub>T W" and cA: "cert_typ alg ar (tsubst \<rho> A)"
      and tyb: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> inst \<rho> body : W"
      by (auto simp: u)
    have bs1: "bs_env \<rho> (e\<langle>0:tsubst \<rho> A\<rangle>) ((a, A) # rb)" by (rule bs_env_Cons[OF bs cA])
    have BW: "tsubst \<rho> B = W" by (rule fastype_sound[OF abs(4) tsol bs1 tyb])
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu]) (use lb in simp)
    then have cAW: "cert_typ alg ar (tsubst \<rho> A \<rightarrow>\<^sub>T W)" by (simp add: U)
    then have cW: "cert_typ alg ar W" using cert_typ_funs[of alg ar "[tsubst \<rho> A]" W] by simp
    have cert1: "\<forall>T\<in>set (Ts @ [A]). cert_typ alg ar (tsubst \<rho> T)" using cert cA by simp
    have tyY: "e' \<turnstile> inst \<rho> Y : map (tsubst \<rho>) (Ts @ [A]) \<Rrightarrow> W" for e'
      using cert cAW by (auto simp: Y tsubst_funs BW cert_typ_funs)
    have lA: "length (map (tsubst \<rho>) (Ts @ [A])) = length targs1" using lt1 by simp
    have tys0: "pushes e' (map (tsubst \<rho>) (Ts @ [A])) \<turnstile> inst \<rho> Y \<degree>\<degree> bvs (length targs1) : W" for e'
      using list_app_typeI[OF tyY typings_bvs[of e' "map (tsubst \<rho>) (Ts @ [A])"]] by (simp only: lA)
    have tysA: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Abs a A (Y \<degree>\<degree> bvs (length targs1))) : U" for e'
    proof -
      have "(pushes e' (map (tsubst \<rho>) Ts))\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> inst \<rho> Y \<degree>\<degree> bvs (length targs1) : W"
        using tys0[of e'] by (simp add: pushes_append)
      from typing.Abs[OF cA this] show ?thesis by (simp add: U inst_apps comp_def)
    qed
    have tys: "\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Abs a A (combound Y 0 (Suc (length Ts)))) : U"
      unfolding cb using tysA by blast
    have tyt1: "e\<langle>0:tsubst \<rho> A\<rangle> \<tturnstile> map (inst \<rho>) targs1 : map (tsubst \<rho>) (Ts @ [A])"
    proof -
      have "list_all2 (typing (e\<langle>0:tsubst \<rho> A\<rangle>)) (map (\<lambda>t. lift t 0) (map (inst \<rho>) targs)) (map (tsubst \<rho>) Ts)"
        using lift_types[OF tya, of 0 "tsubst \<rho> A"] by (simp add: typings_iff)
      then show ?thesis by (auto simp: targs1_def typings_iff comp_def intro!: list_all2_appendI)
    qed
    have ty2: "e\<langle>0:tsubst \<rho> A\<rangle> \<turnstile> inst \<rho> (cpy targs1 (Y \<degree>\<degree> bvs (length targs1))) : W"
      unfolding cp inst_apps by (rule list_app_typeI[OF tyY tyt1])
    have ty0: "e \<turnstile> inst \<rho> (types_abs Ts (Abs a A (Y \<degree>\<degree> bvs (length targs1))) \<degree>\<degree> targs) : tsubst \<rho> A \<rightarrow>\<^sub>T W"
      using typing_tabs_app[OF tysA tya cert] unfolding U .
    have conv: "\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts (Abs a A (combound Y 0 (Suc (length Ts)))) \<degree>\<degree> targs)
        \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs a A (Y \<degree>\<degree> targs1))"
    proof (intro allI impI)
      fix \<sigma> :: vsubst assume \<sigma>: "wt_subst \<sigma>"
      from conv_abs_bind[OF ty0 cA lTs lbb ty2 \<sigma> targs1_def]
      show "ap \<rho> \<sigma> (types_abs Ts (Abs a A (combound Y 0 (Suc (length Ts)))) \<degree>\<degree> targs)
          \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs a A (Y \<degree>\<degree> targs1))"
        by (simp only: cb cp)
    qed
    have tys': "e \<turnstile> inst \<rho> (Abs a A (Y \<degree>\<degree> targs1)) : U"
      using typing.Abs[OF cA ty2[unfolded cp]] by (simp add: U)
    have nn: "0 \<le> ilength rb" by simp
    have "\<not> loose_bvar (lift t 0) (ilength rb + 1)" if "t \<in> set targs" for t
      using loose_bvar_lift[OF order_refl nn, of t] lb that by auto
    moreover have "\<not> ilength rb + 1 \<le> 0" using nn by (simp add: integer_arith)
    ultimately have "\<not> loose_bvar (Abs a A (Y \<degree>\<degree> targs1)) (ilength rb)"
      using clY by (auto simp: targs1_def loose_bvar_apps closed_loose_bvar)
    with tys tys' conv show "(\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Abs a A (combound Y 0 (Suc (length Ts)))) : U) \<and>
        \<not> loose_bvar (Abs a A (Y \<degree>\<degree> targs1)) (ilength rb) \<and> e \<turnstile> inst \<rho> (Abs a A (Y \<degree>\<degree> targs1)) : U \<and>
        (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts (Abs a A (combound Y 0 (Suc (length Ts)))) \<degree>\<degree> targs)
          \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs a A (Y \<degree>\<degree> targs1)))"
      by blast
  qed
  have d2: "dstep env'' ((rb, Abs a A (Y \<degree>\<degree> targs1), u) # dps) env'' (((a, A) # rb, Y \<degree>\<degree> targs1, body) # dps)"
    unfolding u by (rule dstep_abs)
  show "u = Abs a A body" by (fact u)
  show "Y = Var (fst Y') (snd Y')" by (simp add: Y Y')
  show "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      (((a, A) # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps)"
    using dstep_trans[OF d1 d2] by (simp add: targs1_def)
  show ty'': "tyenv env'' = tyenv env" using ok_update(3)[OF abs(7)] g(2) by simp
  show "extends env env''" by (rule extends_trans[OF ext1 extends_update[OF abs(7)]])
  show "satd env'' ((a, A) # rb) body" by (rule satd_tyenv[OF sb ty''])
qed

lemma mc_var_step:
  assumes var: "ok (lookup env v TX) None" "fst (strip_comb u) = Var w W"
      "ok (fastype env rb (Var w W)) T0" "ok (body_type env T0) base" "ok (mapM (fastype env rb) targs) Ts"
      "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)"
      "ok (update (v, TX) (types_abs Ts (combound newhd 0 (length Ts))) env') env''"
    and bse0: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow>
      e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow> U = tsubst \<rho> base"
  shows "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env'' ((rb, newhd \<degree>\<degree> targs, u) # dps)"
proof -
  note g = genvar_simps[OF var(6)]
  have lTs: "length Ts = length targs" by (rule mapM_fastype_sound(1)[OF var(5)])
  have cln: "closed newhd" by (simp add: g(4) closed_def)
  have cb: "combound newhd 0 (length Ts) = newhd \<degree>\<degree> bvs (length targs)" by (simp add: combound_bvs lTs)
  have cp: "cpy targs (combound newhd 0 (length Ts)) = newhd \<degree>\<degree> targs" by (simp only: cb cpy_new_arg[OF cln])
  have na: "\<not> is_Abs (fst (strip_comb u))" using var(2) by simp
  have "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env'' ((rb, cpy targs (combound newhd 0 (length Ts)), u) # dps)"
  proof (rule dstep_bind[OF extends_genvar[OF var(6)] g(1) var(7) _ var(5)])
    show "vinv \<rho> env' (vars (combound newhd 0 (length Ts)) \<union> Y)" if "vinv \<rho> env Y" for \<rho> Y
      using vinv_genvar[OF var(6) that] unfolding cb by (simp add: vars_apps)
    show "\<not> loose_bvar (combound newhd 0 (length Ts)) (ilength Ts)"
      unfolding combound_bvs using loose_bvar_bvs_ilength[of Ts, OF refl] cln
      by (auto simp: loose_bvar_apps closed_loose_bvar)
    show "vars (cpy targs (combound newhd 0 (length Ts))) \<subseteq> vars (combound newhd 0 (length Ts)) \<union> lvars targs"
      unfolding cp by (auto simp: cb vars_apps)
    fix \<rho> e U assume tsol1: "tsol (tyenv env') \<rho>" and bs: "bs_env \<rho> e rb"
      and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and tyu: "e \<turnstile> inst \<rho> u : U"
      and TT: "tsubst \<rho> TX = map (tsubst \<rho>) Ts \<Rrightarrow> U" and lb: "\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)"
      and cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
    have tsol: "tsol (tyenv env) \<rho>" using tsol1 g(2) by simp
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu]) (use lb in simp)
    have tyV: "e \<turnstile> inst \<rho> (Var v TX) : map (tsubst \<rho>) Ts \<Rrightarrow> U"
      using cert cU by (auto simp: TT cert_typ_funs)
    have tyX: "e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : U"
      using list_app_typeI[OF tyV tya] by (simp add: inst_apps)
    have U: "U = tsubst \<rho> base" by (rule bse0[OF tsol bs tyX tyu])
    have tyN: "e' \<turnstile> inst \<rho> newhd : map (tsubst \<rho>) Ts \<Rrightarrow> U" for e'
      using cert cU by (auto simp: g(4) tsubst_funs U cert_typ_funs)
    have tys: "\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (combound newhd 0 (length Ts)) : U"
      unfolding combound_bvs inst_apps inst_bvs
      using list_app_typeI[OF tyN typings_bvs[of _ "map (tsubst \<rho>) Ts", unfolded length_map]] by blast
    note bc = bind_cpy[OF tys tya cert]
    have "\<not> loose_bvar (cpy targs (combound newhd 0 (length Ts))) (ilength rb)"
      unfolding cp using lb cln by (auto simp: loose_bvar_apps closed_loose_bvar)
    with tys bc show "(\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (combound newhd 0 (length Ts)) : U) \<and>
        \<not> loose_bvar (cpy targs (combound newhd 0 (length Ts))) (ilength rb) \<and>
        e \<turnstile> inst \<rho> (cpy targs (combound newhd 0 (length Ts))) : U \<and>
        (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> (types_abs Ts (combound newhd 0 (length Ts)) \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
          ap \<rho> \<sigma> (cpy targs (combound newhd 0 (length Ts))))"
      by blast
  qed
  then show ?thesis by (simp only: cp)
qed

lemma mc_sinv:
  assumes "okW (mc cfg vname envM X rb targs u env dps) s" "extends envM env" "msat ot env rb u"
    "\<forall>t. ot = Some t \<longrightarrow> t = Var (fst X) (snd X) \<degree>\<degree> targs"
  shows "seqinv (GE env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)) s"
  using assms
proof (induction "size u" arbitrary: X rb targs u env s ot rule: less_induct)
  case less
  obtain v TX where X: "X = (v, TX)" by (cases X)
  note extM = less.prems(2)
  have bse: "U = tsubst \<rho> base"
    if na: "\<not> is_Abs (fst (strip_comb u))" and T0: "ok (fastype env rb (fst (strip_comb u))) T0"
      and base: "ok (body_type env T0) base" and tsol: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e rb"
      and tyt: "e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : U" and tyu: "e \<turnstile> inst \<rho> u : U" for \<rho> e U T0 base
  proof (cases ot)
    case None
    with less.prems(3) have sat: "satd env rb u" by (simp add: msat_def)
    show ?thesis by (rule satd_base[OF na sat T0 base tsol bs tyu])
  next
    case (Some t)
    with less.prems(3,4) X have "rsat env rb (Var v TX \<degree>\<degree> targs) u" by (simp add: msat_def)
    from this[unfolded rsat_def] T0 base tsol bs tyt tyu show ?thesis by blast
  qed
  show ?case
    using less.prems(1)[unfolded X]
  proof (cases rule: mc_okW_cases)
    case (asg r)
    then show ?thesis by (auto simp: X list_comb_apps intro!: seqinv.Single dstep_refl)
  next
    case (abs a A body Ts B env' Y Y' env'')
    have sat: "satd env rb u" using less.prems(3,4) abs(2) by (cases ot) (simp_all add: msat_def)
    note st = mc_abs_step[OF abs(1-7) sat]
    have "seqinv (GE env'' (((a, A) # rb, Var (fst Y') (snd Y') \<degree>\<degree> (map (incr_boundvars 1) targs @ [Bound 0]), body) # dps)) s"
    proof (rule less.hyps[OF _ abs(8) extends_trans[OF extM st(5)]])
      show "size body < size u" by (simp add: st(1))
      show "msat None env'' ((a, A) # rb) body" by (simp add: msat_def st(6))
    qed simp
    then have "seqinv (GE env'' (((a, A) # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps)) s"
      by (simp only: st(2) map_incr_boundvars_lift)
    from seqinv_GE_dstep[OF this refl st(3)] show ?thesis by (simp add: X)
  next
    case (var w W T0 base Ts env' newhd env'')
    have na: "\<not> is_Abs (fst (strip_comb u))" using var(2) by simp
    have "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env'' ((rb, newhd \<degree>\<degree> targs, u) # dps)"
      by (rule mc_var_step[OF var(1-7)]) (rule bse[OF na var(3)[folded var(2)] var(4)])
    then show ?thesis by (simp add: var(8) X list_comb_apps seqinv.Single)
  next
    case (rigid T0 base Ts projs)
    have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
    have bse': "U = tsubst \<rho> base" if "tsol (tyenv env) \<rho>" "bs_env \<rho> e rb"
      "e \<turnstile> inst \<rho> (Var (fst X) (snd X) \<degree>\<degree> targs) : U" "e \<turnstile> inst \<rho> u : U" for \<rho> e U
      by (rule bse[OF rigid(2,4,5) that[unfolded X fst_conv snd_conv]])
    show ?thesis
      by (rule matchfun_sinv[OF rigid(8)[folded X] _ u rigid(6) bse' extM])
        (use make_projs_props[OF rigid(7)] in simp)
  qed
qed

text \<open>
  The copies of an argument into its new variable: the argument is normalized in the environment
  \<open>envM\<close> of \<open>MATCH\<close>; a deferred argument remains as a pair, otherwise it is copied by \<^const>\<open>mc\<close>.
\<close>

lemma copycons_sinv:
  assumes cc: "okW (copycons cfg vname envM rb targs G uarg env dps) cs" and extM: "extends envM env"
    and sat: "\<And>u1 u2. ok (head_norm envM uarg) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> satd env rb u2"
  shows "seqinv (GE env ((rb, G \<degree>\<degree> targs, uarg) # dps)) cs"
proof -
  from cc[unfolded copycons_def okW_bindW okW_liftM] obtain X u1 u2 d where X: "okW (dest_Var G) X"
    and h: "ok (head_norm envM uarg) u1" and e: "ok (eta_norm env rb u1) u2"
    and s: "okW (if d then returnW (S_Single (El_E env ((rb, list_comb G targs, u2) # dps)))
      else mc cfg vname envM X rb targs u2 env dps) cs"
    by blast
  from X obtain x U where G: "G = Var x U" "X = (x, U)" by (cases G) auto
  have tc: "tconv env rb uarg u2"
    by (rule tconv_trans[OF tconv_extends[OF head_norm_tconv[OF h] extM] eta_norm_tconv[OF e]])
  have dc: "dstep env ((rb, G \<degree>\<degree> targs, uarg) # dps) env ((rb, G \<degree>\<degree> targs, u2) # dps)"
    using dstep_frame[OF tconv_dstep[OF tconv_refl tc], where fs = dps] by simp
  show ?thesis
  proof (cases d)
    case True
    with s have "cs = S_Single (El_E env ((rb, G \<degree>\<degree> targs, u2) # dps))" by (simp add: list_comb_apps)
    with dc show ?thesis by (simp add: seqinv.Single)
  next
    case False
    with s have "okW (mc cfg vname envM X rb targs u2 env dps) cs" by simp
    from mc_sinv[OF this extM, of None] sat[OF h e]
    have "seqinv (GE env ((rb, G \<degree>\<degree> targs, u2) # dps)) cs" by (simp add: msat_def G)
    from seqinv_GE_dstep[OF this refl dc] show ?thesis .
  qed
qed

subsection \<open>The \<open>\<eta>\<close>-expansion of a pair\<close>

lemma binder_types_sound:
  assumes "binder_types env T = Some r"
  shows "r = Ok Ts \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> \<exists>W. tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> W"
  using assms
proof (induction env T r arbitrary: Ts rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Us)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Us = [T1, U])")
      case True
      then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" using Type by auto
      from h T obtain Ts' where r: "ok (bt env U) Ts'" and Ts: "Ts = T1 # Ts'" by auto
      from "1.IH"[OF r refl "1.prems"(2)] Ts T show ?thesis by auto
    next
      case False
      with h Type have "Ts = []" by (auto split: list.splits if_splits)
      then show ?thesis by simp
    qed
  next
    case (TVar v S)
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v S) lr"
      and rest: "ok (case lr of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Ts"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some T')
      with rest have r: "ok (bt env T') Ts" by simp
      from "1.IH"[OF r refl "1.prems"(2)] ok_type_lookup_sound[OF lr[unfolded Some] "1.prems"(2)] TVar
      show ?thesis by simp
    qed (use rest in simp)
  next
    case (TFree a S)
    with h show ?thesis by simp
  qed
qed

lemma funs_prefix:
  "Us \<Rrightarrow> U = Vs \<Rrightarrow> W \<Longrightarrow> length Us \<le> length Vs \<Longrightarrow> U = drop (length Us) Vs \<Rrightarrow> W"
proof (induction Us arbitrary: Vs)
  case (Cons U' Us)
  then obtain V Vs' where "Vs = V # Vs'" by (cases Vs) auto
  with Cons show ?case by simp
qed simp

lemma bs_env_pushes:
  "bs_env \<rho> e rb \<Longrightarrow> \<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow>
    bs_env \<rho> (pushes e (map (tsubst \<rho>) Es)) (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb)"
proof (induction Es arbitrary: e rb)
  case (Cons E Es)
  have "bs_env \<rho> (e\<langle>0:tsubst \<rho> E\<rangle>) ((STR '''', E) # rb)" by (rule bs_env_Cons) (use Cons.prems in simp_all)
  from Cons.IH[OF this] Cons.prems(2) show ?case by simp
qed simp

lemma typing_incr_pushes: "e \<turnstile> s : S \<Longrightarrow> pushes e Us \<turnstile> incr_bv (ilength Us) 0 s : S"
proof (induction Us arbitrary: e s)
  case (Cons U Us)
  have "e\<langle>0:U\<rangle> \<turnstile> lift s 0 : S" using Cons.prems by (rule lift_type) simp
  from Cons.IH[OF this] show ?case by (simp add: incr_bv_incr_bv add.commute)
qed simp

lemma loose_bvar_incr_bv:
  "0 \<le> n \<Longrightarrow> 0 \<le> lev \<Longrightarrow> lev \<le> k \<Longrightarrow> loose_bvar (incr_bv n lev t) (k + n) = loose_bvar t k"
  by (induction n lev t arbitrary: k rule: incr_bv.induct) (auto simp: algebra_simps)

lemma conv_types_abs:
  "wt (types_abs Vs s) \<Longrightarrow> wt (types_abs Vs s') \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<Longrightarrow> types_abs Vs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Vs s'"
proof (induction Vs)
  case (Cons V Vs)
  from Cons.prems(1,2) have "wt (types_abs Vs s)" "wt (types_abs Vs s')" by (auto dest: wt_AbsD)
  from Cons.IH[OF this Cons.prems(3)] Cons.prems(1,2) show ?case by (simp add: conv_Abs)
qed simp

lemma bvs_Suc: "bvs (Suc n) = Bound (integer_of_nat n) # bvs n"
  by simp

text \<open>The abstraction of the application to new bound variables is \<open>\<eta>\<close>-equivalent:\<close>

lemma eta_bvs:
  "e \<turnstile> s : Vs \<Rrightarrow> W \<Longrightarrow> \<forall>V\<in>set Vs. cert_typ alg ar V \<Longrightarrow>
    e \<turnstile> types_abs Vs (incr_bv (ilength Vs) 0 s \<degree>\<degree> bvs (length Vs)) : Vs \<Rrightarrow> W \<and>
    types_abs Vs (incr_bv (ilength Vs) 0 s \<degree>\<degree> bvs (length Vs)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
proof (induction Vs arbitrary: e s)
  case (Cons V Vs)
  define s1 where "s1 = lift s 0 $ Bound 0"
  have ty1: "e\<langle>0:V\<rangle> \<turnstile> s1 : Vs \<Rrightarrow> W"
    using Cons.prems(1) by (auto simp: s1_def intro!: typing.App[OF lift_type])
  note IH = Cons.IH[OF ty1] Cons.prems(2)
  have eq: "incr_bv (ilength (V # Vs)) 0 s \<degree>\<degree> bvs (length (V # Vs)) =
      incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs)"
  proof -
    have i: "integer_of_nat (Suc (length Vs)) = integer_of_nat (length Vs) + 1"
      by (simp add: integer_of_nat_eq_of_nat)
    have "incr_bv (integer_of_nat (length Vs)) 0 (lift s 0) = incr_bv (integer_of_nat (length Vs) + 1) 0 s"
      by (rule incr_bv_incr_bv) (simp_all add: integer_of_nat_nonneg)
    then show ?thesis by (simp only: length_Cons bvs_Suc) (simp add: s1_def ilength_eq i del: upt_Suc)
  qed
  have cV: "cert_typ alg ar V" using Cons.prems(2) by simp
  have t1: "e \<turnstile> Abs STR '''' V (types_abs Vs (incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs))) : (V # Vs) \<Rrightarrow> W"
    using IH cV by auto
  have t2: "e \<turnstile> Abs STR '''' V s1 : (V # Vs) \<Rrightarrow> W" using ty1 cV by auto
  have "Abs STR '''' V (types_abs Vs (incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs STR '''' V s1"
    by (rule conv_Abs) (use t1 t2 IH in \<open>auto simp: wt_def\<close>)
  also have "Abs STR '''' V s1 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" unfolding s1_def by (rule conv_eta_lift) (use t2 in \<open>auto simp: wt_def s1_def\<close>)
  finally have c: "Abs STR '''' V (types_abs Vs (incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" .
  show ?case unfolding eq using t1 c by simp
qed simp

lemma strip_comb_expand:
  "strip_comb t = (Var v T, targs) \<Longrightarrow>
    strip_comb (incr_bv n 0 t \<degree>\<degree> ts) = (Var v T, map (incr_bv n 0) targs @ ts)"
  by (simp add: strip_comb_apps[of t] incr_bv_apps foldl_append[symmetric] strip_comb_atom_apps
      del: foldl_append)

lemma dstep_eta_expand:
  assumes st: "strip_comb t = (Var v T, targs)" and bt: "ok (binder_types env T) Ts"
    and len: "length targs \<le> length Ts"
  shows "dstep env [(rb, t, u)] env [eta_expand_dpair (drop (length targs) Ts) (rb, t, u)]"
proof -
  define Es where "Es = drop (length targs) Ts"
  define j where "j = length Es"
  have ij: "integer_of_nat j = ilength Es" by (simp add: j_def ilength_eq)
  have ed: "eta_expand_dpair Es (rb, t, u) =
      (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
       incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)"
    by (simp add: eta_expand_dpair_def Let_def j_def incr_boundvars_def list_comb_apps ij[unfolded j_def])
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  show ?thesis unfolding Es_def[symmetric] ed
  proof (rule dstepI[OF extends_refl])
    fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext: "extends env env''" and wte: "wt_env \<rho> env"
      and dt: "dtyped \<rho> [(rb, t, u)]" and vi: "vinv \<rho> env (X \<union> dvars [(rb, t, u)])"
    have tsol: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol'' ext])
    from dt obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : U" and tyu: "e \<turnstile> inst \<rho> u : U"
      and lbt: "\<not> loose_bvar t (ilength rb)" and lbu: "\<not> loose_bvar u (ilength rb)"
      by auto
    from binder_types_sound[OF bt refl tsol] obtain W where T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> W" by blast
    from tyt[unfolded t inst_apps] obtain Us where tyv: "e \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U"
      and tyas: "e \<tturnstile> map (inst \<rho>) targs : Us"
      by (rule list_app_typeE)
    have lUs: "length Us = length targs" using typings_nth[OF tyas] by simp
    from tyv T have "Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> W" by auto
    from funs_prefix[OF this] len lUs have U: "U = map (tsubst \<rho>) Es \<Rrightarrow> W" by (simp add: Es_def drop_map)
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu lbu])
    then have cEs: "\<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T)" by (simp add: U cert_typ_funs)
    define e' where "e' = pushes e (map (tsubst \<rho>) Es)"
    have bs': "bs_env \<rho> e' (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb)" unfolding e'_def by (rule bs_env_pushes[OF bs cEs])
    have tyb: "e' \<tturnstile> bvs j : map (tsubst \<rho>) Es" using typings_bvs[of e "map (tsubst \<rho>) Es"] by (simp add: e'_def j_def)
    have tyx: "e' \<turnstile> inst \<rho> (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j) : W" if "e \<turnstile> inst \<rho> x : U" for x
      using list_app_typeI[OF typing_incr_pushes[OF that[unfolded U], of "map (tsubst \<rho>) Es", unfolded ilength_map]
          typings_bvs[of e "map (tsubst \<rho>) Es", unfolded length_map]]
      by (simp add: e'_def j_def inst_apps comp_def)
    have lbx: "\<not> loose_bvar (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j) (ilength (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb))"
      if "\<not> loose_bvar x (ilength rb)" for x
    proof -
      have "\<not> loose_bvar (incr_bv (ilength Es) 0 x) (ilength rb + ilength Es)"
        using loose_bvar_incr_bv[of "ilength Es" 0 "ilength rb" x] that by simp
      moreover have "\<not> loose_bvar b (ilength rb + ilength Es)" if "b \<in> set (bvs j)" for b
      proof -
        from that obtain x where x: "x < length Es" "b = Bound (integer_of_nat x)" by (auto simp: j_def)
        have "integer_of_nat x < ilength Es" using x by (simp add: ilength_eq integer_of_nat_less)
        then have "integer_of_nat x < ilength rb + ilength Es"
          using ilength_nonneg[of rb] by (simp add: integer_less_iff integer_less_eq_iff plus_integer.rep_eq)
        then show ?thesis using x by simp
      qed
      ultimately show ?thesis by (auto simp: loose_bvar_apps add.commute)
    qed
    show "wt_env \<rho> env \<and> dtyped \<rho> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
        incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)] \<and>
      vinv \<rho> env (X \<union> dvars [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
        incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)]) \<and>
      deqv (binds \<rho> env \<union> dp_eqs \<rho> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb,
        incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j, incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)]) \<rho> [(rb, t, u)]"
    proof (intro conjI)
      show "wt_env \<rho> env" by (fact wte)
      show "dtyped \<rho> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
          incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)]"
        using bs' tyx[OF tyt] tyx[OF tyu] lbx[OF lbt] lbx[OF lbu] by auto
      show "vinv \<rho> env (X \<union> dvars [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
          incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)])"
        using vi by (simp add: vars_apps)
      let ?E = "binds \<rho> env \<union> dp_eqs \<rho> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb,
        incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j, incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)]"
      let ?Vs = "map (tsubst \<rho>) Es"
      have ix: "inst \<rho> (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j) = incr_bv (ilength ?Vs) 0 (inst \<rho> x) \<degree>\<degree> bvs (length ?Vs)"
        for x by (simp add: inst_apps j_def comp_def)
      show "deqv ?E \<rho> [(rb, t, u)]"
        unfolding deqv_single
      proof (intro allI impI)
        fix e1 U1 assume a: "bs_env \<rho> e1 rb" "e1 \<turnstile> inst \<rho> t : U1" "e1 \<turnstile> inst \<rho> u : U1"
        from a(2)[unfolded t inst_apps] obtain Us1 where tyv1: "e1 \<turnstile> inst \<rho> (Var v T) : Us1 \<Rrightarrow> U1"
          and tyas1: "e1 \<tturnstile> map (inst \<rho>) targs : Us1"
          by (rule list_app_typeE)
        have lUs1: "length Us1 = length targs" using typings_nth[OF tyas1] by simp
        from tyv1 T have "Us1 \<Rrightarrow> U1 = map (tsubst \<rho>) Ts \<Rrightarrow> W" by auto
        from funs_prefix[OF this] len lUs1 have U1: "U1 = ?Vs \<Rrightarrow> W" by (simp add: Es_def drop_map)
        have cV: "\<forall>V\<in>set ?Vs. cert_typ alg ar V" using cEs by simp
        note bt = eta_bvs[OF a(2)[unfolded U1] cV] and bu = eta_bvs[OF a(3)[unfolded U1] cV]
        have bs1: "bs_env \<rho> (pushes e1 ?Vs) (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb)"
          by (rule bs_env_pushes[OF a(1) cEs])
        have tyx1: "pushes e1 ?Vs \<turnstile> inst \<rho> (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j) : W"
          if "e1 \<turnstile> inst \<rho> x : U1" for x
          using list_app_typeI[OF typing_incr_pushes[OF that[unfolded U1], of ?Vs, unfolded ilength_map]
              typings_bvs[of e1 ?Vs, unfolded length_map]]
          by (simp add: j_def inst_apps comp_def)
        have "eqv ?E (pushes e1 ?Vs) (inst \<rho> (incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j))
            (inst \<rho> (incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j))"
          by (rule dp_eqs_use[OF _ _ bs1 tyx1[OF a(2)] tyx1[OF a(3)] lbx[OF lbt] lbx[OF lbu]]) auto
        then have "eqv ?E (pushes e1 (map snd (map (\<lambda>T. (STR '''', T)) ?Vs)))
            (incr_bv (ilength ?Vs) 0 (inst \<rho> t) \<degree>\<degree> bvs (length ?Vs)) (incr_bv (ilength ?Vs) 0 (inst \<rho> u) \<degree>\<degree> bvs (length ?Vs))"
          by (simp add: ix comp_def)
        from eqv_abs_list[OF this] cV
        have "eqv ?E e1 (types_abs ?Vs (incr_bv (ilength ?Vs) 0 (inst \<rho> t) \<degree>\<degree> bvs (length ?Vs)))
            (types_abs ?Vs (incr_bv (ilength ?Vs) 0 (inst \<rho> u) \<degree>\<degree> bvs (length ?Vs)))"
          by (simp add: types_abs_abs_list)
        moreover have "eqv ?E e1 (inst \<rho> t) (types_abs ?Vs (incr_bv (ilength ?Vs) 0 (inst \<rho> t) \<degree>\<degree> bvs (length ?Vs)))"
          using eqv_conv[OF conv_sym[OF conjunct2[OF bt]] a(2)[unfolded U1] conjunct1[OF bt]] .
        moreover have "eqv ?E e1 (types_abs ?Vs (incr_bv (ilength ?Vs) 0 (inst \<rho> u) \<degree>\<degree> bvs (length ?Vs))) (inst \<rho> u)"
          using eqv_conv[OF conjunct2[OF bu] conjunct1[OF bu] a(3)[unfolded U1]] .
        ultimately show "eqv ?E e1 (inst \<rho> t) (inst \<rho> u)" by (meson eqv.eqv_trans)
      qed
    qed
  qed
qed


subsection \<open>\<open>MATCH\<close>\<close>

lemma match_pair_sinv:
  assumes m: "okW (match_pair cfg env (rb, t, u) dps) s" and st: "strip_comb t = (Var v T, targs)"
    and sat: "rsat env rb t u" and nab: "\<not> is_Abs (fst (strip_comb u))"
  shows "seqinv (GE env ((rb, t, u) # dps)) s"
proof -
  from m st have "okW (mc cfg (fst v) env (v, T) rb targs u env dps) s" by (simp add: match_pair_def)
  from mc_sinv[OF this extends_refl, of "Some t"] sat nab show ?thesis
    by (simp add: msat_def strip_comb_apps[OF st])
qed

text \<open>
  The saturation of a pair: in the type environment of \<^const>\<open>match_sat\<close>, the variable of the
  flexible side has at least as many binder types as arguments, and after the \<open>\<eta>\<close>-expansion
  the rigid side is saturated (\<^const>\<open>rsat\<close>) and not an abstraction.
\<close>

definition msat_ok :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "msat_ok env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> \<forall>v T targs Ts. strip_comb t = (Var v T, targs) \<longrightarrow>
    ok (binder_types env T) Ts \<longrightarrow> length targs \<le> length Ts \<and>
    (case eta_expand_dpair (drop (length targs) Ts) dp of (rb', t', u') \<Rightarrow>
      rsat env rb' t' u' \<and> \<not> is_Abs (fst (strip_comb u'))))"

lemma eta_expand_dpair_eq:
  "eta_expand_dpair Es (rb, t, u) =
    (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs (length Es),
     incr_bv (ilength Es) 0 u \<degree>\<degree> bvs (length Es))"
  by (simp add: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq)

lemma match_sat_sinv:
  assumes m: "okW (match_sat cfg env dp dps) s" and ms: "msat_ok env dp"
  shows "seqinv (GE env (dp # dps)) s"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain h targs where st0: "strip_comb t = (h, targs)" by fastforce
  from m st0 obtain v T where h: "h = Var v T" by (cases h) (auto simp: match_sat_def dp)
  note st = st0[unfolded h]
  from m st obtain Ts where bt: "ok (binder_types env T) Ts"
    and mp: "okW (match_pair cfg env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u)) dps) s"
    by (auto simp: match_sat_def dp)
  from ms[unfolded msat_ok_def dp prod.case, rule_format, OF st bt]
  have len: "length targs \<le> length Ts"
    and sat: "case eta_expand_dpair (drop (length targs) Ts) (rb, t, u) of (rb', t', u') \<Rightarrow>
      rsat env rb' t' u' \<and> \<not> is_Abs (fst (strip_comb u'))"
    by (simp_all add: dp)
  define Es where "Es = drop (length targs) Ts"
  define targs' where "targs' = map (incr_bv (ilength Es) 0) targs @ bvs (length Es)"
  define rb' where "rb' = rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
  define t' where "t' = incr_bv (ilength Es) 0 t \<degree>\<degree> bvs (length Es)"
  define u' where "u' = incr_bv (ilength Es) 0 u \<degree>\<degree> bvs (length Es)"
  have ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
    by (simp add: eta_expand_dpair_eq rb'_def t'_def u'_def)
  have st': "strip_comb t' = (Var v T, targs')" by (simp add: t'_def targs'_def strip_comb_expand[OF st])
  have lt': "length targs' = length Ts" using len by (simp add: targs'_def Es_def)
  from sat ed have sat': "rsat env rb' t' u'" and nab: "\<not> is_Abs (fst (strip_comb u'))" by (simp_all add: Es_def)
  have "seqinv (GE env ((rb', t', u') # dps)) s"
    by (rule match_pair_sinv[OF mp[folded Es_def, unfolded ed] st' sat' nab])
  moreover have "dstep env (dp # dps) env ((rb', t', u') # dps)"
    using dstep_frame[OF dstep_eta_expand[OF st bt len, of rb u], of dps] ed by (simp add: dp Es_def)
  ultimately show ?thesis by (rule seqinv_GE_dstep[OF _ refl])
qed

lemma match_eta_sinv:
  assumes m: "okW (match_eta cfg env dp dps B j tail) s" and tl: "seqinv (GE env (dp # dps)) tail"
    and ms: "\<And>env'. extends env env' \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> msat_ok env' dp"
  shows "seqinv (GE env (dp # dps)) s"
proof (cases "j = 0")
  case True
  with m obtain s' where "okW (match_sat cfg env dp dps) s'" and s: "s = S_Append s' tail"
    by (auto simp: match_eta_def)
  from match_sat_sinv[OF this(1) ms[OF extends_refl refl]] tl show ?thesis by (simp add: s seqinv.Append)
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by fastforce
  note g' = gentvars_props[OF g]
  from okW_handle_CANTUNIFY[OF m[unfolded match_eta_def, simplified False if_False g prod.case]]
  consider (ok) env2 s' where "okW (cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1) env2"
      "okW (match_sat cfg env2 dp dps) s'" "s = S_Append s' tail"
    | (cu) "s = tail"
    by auto
  then show ?thesis
  proof cases
    case (ok env2 s')
    note c = cunify_types_sound[OF ok(1)]
    have ext1: "extends env env1" by (rule extends_tenv_eq) (use g' in simp_all)
    have ext: "extends env env2" by (rule extends_trans[OF ext1 c(2)])
    have te: "tenv env2 = tenv env" using c(1) g'(1) by simp
    have "seqinv (GE env2 (dp # dps)) s'" by (rule match_sat_sinv[OF ok(2) ms[OF ext te]])
    from seqinv_GE_dstep[OF this refl dstep_tenv[OF te ext]] tl show ?thesis by (simp add: ok(3) seqinv.Append)
  qed (use tl in simp)
qed

text \<open>
  The hypothesis of \<open>MATCH\<close>: in every extension of the type environment (by the guesses of
  \<^const>\<open>match_eta\<close>), the pair is saturated in the sense of \<^const>\<open>msat_ok\<close>.
\<close>

definition MATCH_ok :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "MATCH_ok env dp \<longleftrightarrow> (\<forall>env'. extends env env' \<longrightarrow> tenv env' = tenv env \<longrightarrow> msat_ok env' dp)"

theorem MATCH_sound:
  assumes m: "okW (MATCH cfg env dp dps) s" and mo: "MATCH_ok env dp"
  shows "seqinv (GE env (dp # dps)) s"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain h targs where st0: "strip_comb t = (h, targs)" by fastforce
  from m st0 obtain v T where h: "h = Var v T" by (cases h) (auto simp: MATCH_def dp)
  note st = st0[unfolded h]
  from m[unfolded dp] st obtain B where B: "ok (body_type env T) B"
    and r: "okW (if is_TVar B then foldrW (match_eta cfg env (rb, t, u) dps B) (arity_guesses cfg B) S_Empty
      else match_sat cfg env (rb, t, u) dps) s"
    by (auto simp: MATCH_def)
  note r = r[folded dp]
  have ms: "msat_ok env' dp" if "extends env env'" "tenv env' = tenv env" for env'
    using mo that unfolding MATCH_ok_def by blast
  show ?thesis
  proof (cases "is_TVar B")
    case True
    with r have f: "okW (foldrW (match_eta cfg env dp dps B) (arity_guesses cfg B) S_Empty) s" by simp
    have "seqinv (GE env (dp # dps)) b \<longrightarrow> seqinv (GE env (dp # dps)) s'"
      if "okW (foldrW (match_eta cfg env dp dps B) js b) s'" for js b s'
      using that
    proof (induction rule: okW_foldrW_induct)
      case (Cons j js b b1 b')
      show ?case
      proof
        assume "seqinv (GE env (dp # dps)) b"
        with Cons.IH have "seqinv (GE env (dp # dps)) b1" by simp
        from match_eta_sinv[OF Cons.hyps(2) this ms] show "seqinv (GE env (dp # dps)) b'" .
      qed
    qed simp
    with f show ?thesis by (blast intro: seqinv.Empty)
  next
    case False
    with r have "okW (match_sat cfg env dp dps) s" by simp
    from match_sat_sinv[OF this ms[OF extends_refl refl]] show ?thesis .
  qed
qed

end

end
