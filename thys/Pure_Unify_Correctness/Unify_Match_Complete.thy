section \<open>Completeness of \<open>MATCH\<close>\<close>

theory Unify_Match_Complete
  imports Unify_Search
begin

text \<open>
  Huet's lemma for \<open>unify.ML\<close>: for a flex-rigid pair solved by \<open>\<sigma>\<close>, the sequence of
  \<^const>\<open>MATCH\<close> has an element (\<^const>\<open>ev\<close>) whose environment and pairs are solved by an
  extension of \<open>\<sigma>\<close> to the new variables, and the sum of the sizes of the values of the unbound
  reachable variables decreases: the value of the flexible head is replaced by the values of
  the new variables, which are proper subterms of it.
\<close>

text \<open>A rigid head (a constant or a free variable) keeps its typing in every context.\<close>

lemma has_type_rigid_head:
  "has_type V Ts h T \<Longrightarrow> h = Const a T' \<or> h = Free a T' \<Longrightarrow> has_type V' Ts' h T"
  by (auto elim: has_type.cases intro: has_type.Const has_type.Free)

subsection \<open>Fresh variable names\<close>

text \<open>\<^const>\<open>genvars\<close> creates distinct names: \<^const>\<open>radixstring\<close> is injective.\<close>

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

text \<open>Extending a solution and the variable typing to fresh variables.\<close>

definition ext_subst :: "(nat \<Rightarrow> dB) \<Rightarrow> (indexname \<times> ptyp \<times> dB) list \<Rightarrow> nat \<Rightarrow> dB" where
  "ext_subst \<sigma> xs n = (case map_of (map (\<lambda>(x, T, w). (code (AVar x), w)) xs) n of Some w \<Rightarrow> w | None \<Rightarrow> \<sigma> n)"

definition ext_typ :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> (indexname \<times> ptyp \<times> dB) list \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "ext_typ V xs x = (case map_of (map (\<lambda>(x, T, w). (x, T)) xs) x of Some T \<Rightarrow> T | None \<Rightarrow> V x)"

lemma map_of_code_None: "(\<forall>x. n \<noteq> code (AVar x)) \<Longrightarrow> map_of (map (\<lambda>(x, T, w). (code (AVar x), w)) xs) n = None"
  by (induction xs) auto

lemma ext_subst_nonvar: "(\<forall>x. n \<noteq> code (AVar x)) \<Longrightarrow> ext_subst \<sigma> xs n = \<sigma> n"
  by (simp add: ext_subst_def map_of_code_None)

lemma map_of_code_AVar:
  "map_of (map (\<lambda>(x, T, w). (code (AVar x), w)) xs) (code (AVar y)) =
    map_option (\<lambda>(T, w). w) (map_of xs y)"
  by (induction xs) auto

lemma map_of_typ: "map_of (map (\<lambda>(x, T, w). (x, T)) xs) y = map_option fst (map_of xs y)"
  by (induction xs) auto

lemma ext_subst_AVar:
  "ext_subst \<sigma> xs (code (AVar y)) = (case map_of xs y of Some (T, w) \<Rightarrow> w | None \<Rightarrow> \<sigma> (code (AVar y)))"
  by (simp add: ext_subst_def map_of_code_AVar split: option.splits)

lemma ext_typ_simp: "ext_typ V xs y = (case map_of xs y of Some (T, w) \<Rightarrow> T | None \<Rightarrow> V y)"
  by (simp add: ext_typ_def map_of_typ split: option.splits)

lemma solution_extend:
  assumes sol: "solution V \<tau>' \<sigma> env" and fr: "fresh_env env"
    and xs: "\<And>x T w. (x, T, w) \<in> set xs \<Longrightarrow> maxidx env < snd x \<and> no_loose_bound w 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> w : trty T)"
  shows "solution (ext_typ V xs) \<tau>' (ext_subst \<sigma> xs) env" "agree (maxidx env) \<sigma> (ext_subst \<sigma> xs)"
    "agreeV (maxidx env) V (ext_typ V xs)"
proof -
  note \<sigma> = solutionD[OF sol]
  show ag: "agree (maxidx env) \<sigma> (ext_subst \<sigma> xs)"
    unfolding agree_def
  proof (intro allI impI)
    fix n assume ne: "ext_subst \<sigma> xs n \<noteq> \<sigma> n"
    then obtain y where n: "n = code (AVar y)" using ext_subst_nonvar[of n \<sigma> xs] by blast
    with ne obtain T w where "map_of xs y = Some (T, w)" by (auto simp: ext_subst_AVar split: option.splits)
    then have "(y, T, w) \<in> set xs" by (rule map_of_SomeD)
    with xs n show "\<exists>x. n = code (AVar x) \<and> maxidx env < snd x" by blast
  qed
  show "agreeV (maxidx env) V (ext_typ V xs)"
    unfolding agreeV_def
  proof (intro allI impI)
    fix x :: indexname assume x: "snd x \<le> maxidx env"
    have "map_of xs x = None"
    proof (rule ccontr)
      assume "map_of xs x \<noteq> None"
      then obtain T w where "map_of xs x = Some (T, w)" by auto
      then have "(x, T, w) \<in> set xs" by (rule map_of_SomeD)
      from xs[OF this] x show False by simp
    qed
    then show "ext_typ V xs x = V x" by (simp add: ext_typ_simp)
  qed
  have "closed_on UNIV (ext_subst \<sigma> xs)"
    unfolding closed_on_def
  proof
    fix n
    show "no_loose_bound (ext_subst \<sigma> xs n) 0"
    proof (cases "\<exists>y. n = code (AVar y)")
      case True
      then obtain y where n: "n = code (AVar y)" by blast
      show ?thesis
      proof (cases "map_of xs y")
        case None
        then show ?thesis using closed_onD[OF \<sigma>(1)] n by (simp add: ext_subst_AVar)
      next
        case (Some p)
        obtain T w where p: "p = (T, w)" by (cases p)
        with Some have "(y, T, w) \<in> set xs" by (auto dest: map_of_SomeD)
        from xs[OF this] Some p n show ?thesis by (simp add: ext_subst_AVar)
      qed
    qed (use closed_onD[OF \<sigma>(1)] ext_subst_nonvar in auto)
  qed
  moreover have "typed_on (range code) (tau (ext_typ V xs)) \<tau>' (ext_subst \<sigma> xs)"
    unfolding typed_on_def
  proof (intro ballI allI)
    fix n e assume "n \<in> range code"
    then obtain a where n: "n = code a" by blast
    show "(e, \<tau>') \<turnstile> ext_subst \<sigma> xs n : tau (ext_typ V xs) n"
    proof (cases a)
      case (AVar y)
      show ?thesis
      proof (cases "map_of xs y")
        case None
        with typed_onD[OF \<sigma>(2), of n e] n AVar show ?thesis by (simp add: ext_subst_AVar ext_typ_simp)
      next
        case (Some p)
        obtain T w where p: "p = (T, w)" by (cases p)
        with Some have "(y, T, w) \<in> set xs" by (auto dest: map_of_SomeD)
        with xs Some p n AVar show ?thesis by (simp add: ext_subst_AVar ext_typ_simp)
      qed
    qed (use typed_onD[OF \<sigma>(2), of n e] n ext_subst_nonvar in auto)
  qed
  moreover have "rigid_subst (ext_subst \<sigma> xs)"
    using \<sigma>(3) ext_subst_nonvar by (auto simp: rigid_subst_def rigid_code_def)
  moreover have "sat (ext_subst \<sigma> xs) env" by (rule sat_agree[OF \<sigma>(4) fr ag])
  ultimately show "solution (ext_typ V xs) \<tau>' (ext_subst \<sigma> xs) env" by (simp add: solution_def)
qed

subsection \<open>Extending solutions\<close>

lemma below_rlist_abs: "below m (rlist_abs rb t) \<longleftrightarrow> below m t"
  by (simp add: below_vps_iff vps_rlist_abs)

text \<open>The invariant of pairs carries over to an extension of the solution and the typing.\<close>

lemma cinv_extend:
  assumes "cinv ar V \<tau>' \<sigma> env dps" "env_inv ar V' env'" "solution V' \<tau>' \<sigma>' env'"
    "agree (maxidx env) \<sigma> \<sigma>'" "agreeV (maxidx env) V V'" "maxidx env \<le> maxidx env'"
  shows "cinv ar V' \<tau>' \<sigma>' env' dps"
proof -
  have "wf_dp ar dp \<and> dp_typed V' dp \<and> dp_below (maxidx env') dp \<and> dsolved \<sigma>' dp" if dp: "dp \<in> set dps" for dp
  proof -
  obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
  from cinvD(3)[OF assms(1) dp] dpe obtain T where w: "wf_dp ar (rb, t, u)"
    and ty: "has_type V (map snd rb) t T" "has_type V (map snd rb) u T"
    and bl: "below (maxidx env) t" "below (maxidx env) u" and ds: "dsolved \<sigma> (rb, t, u)"
    by auto
  have "dp_typed V' dp" using has_type_agreeV[OF ty(1) bl(1) assms(5)] has_type_agreeV[OF ty(2) bl(2) assms(5)] dpe
    by auto
  moreover have "dp_below (maxidx env') dp" using bl below_mono[OF _ assms(6)] dpe by simp
  moreover have "dsolved \<sigma>' dp"
    using dsolvedD[OF ds] mk_subst_agree[OF iffD2[OF below_rlist_abs bl(1)] assms(4), of rb]
      mk_subst_agree[OF iffD2[OF below_rlist_abs bl(2)] assms(4), of rb] dpe
    by (simp add: dsolved_def)
  ultimately show "wf_dp ar dp \<and> dp_typed V' dp \<and> dp_below (maxidx env') dp \<and> dsolved \<sigma>' dp"
    using w dpe by simp
  qed
  with assms(2,3) show ?thesis by (simp add: cinv_def)
qed

lemma env_inv_genvar:
  assumes "env_inv ar V env" "genvar a env T = (env1, G)" "env_typed V' env1" "fresh_env env1"
  shows "env_inv ar V' env1"
proof -
  note g = genvar_simps[OF assms(2)]
  have "acyc env1" using env_invD(1)[OF assms(1)] by (simp add: acyc_def dep_tenv[OF g(1)])
  moreover have "wf_env ar env1" using env_invD(2)[OF assms(1)] g(1,2) by (simp add: wf_env_def)
  ultimately show ?thesis using assms(3,4) by (simp add: env_inv_def)
qed

lemma genvar_extend:
  assumes inv: "cinv ar V \<tau>' \<sigma> env dps" and G: "genvar a env T = (env1, G)"
    and w: "no_loose_bound w 0" "\<And>e. (e, \<tau>') \<turnstile> w : trty T"
  defines "\<sigma>1 \<equiv> \<sigma>(code (AVar (a, maxidx env + 1)) := w)" and "V1 \<equiv> V((a, maxidx env + 1) := T)"
  shows "cinv ar V1 \<tau>' \<sigma>1 env1 dps" "agree (maxidx env) \<sigma> \<sigma>1" "agreeV (maxidx env) V V1"
    "maxidx env1 = maxidx env + 1" "G = Var (a, maxidx env + 1) T" "extends env1 env"
    "\<sigma>1 (code (AVar (a, maxidx env + 1))) = w" "V1 (a, maxidx env + 1) = T"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note nv = solution_new_var[OF cinvD(2)[OF inv] ei(4) ei(3) G w, folded \<sigma>1_def V1_def]
  have "env_inv ar V1 env1" by (rule env_inv_genvar[OF cinvD(1)[OF inv] G nv(4,5)])
  then show "cinv ar V1 \<tau>' \<sigma>1 env1 dps" using cinv_extend[OF inv _ nv(1,2,3)] nv(6) by simp
  show "agree (maxidx env) \<sigma> \<sigma>1" "agreeV (maxidx env) V V1" "maxidx env1 = maxidx env + 1"
    "G = Var (a, maxidx env + 1) T" "\<sigma>1 (code (AVar (a, maxidx env + 1))) = w" "V1 (a, maxidx env + 1) = T"
    by (rule nv)+
  show "extends env1 env" using genvar_simps(1)[OF G] by (simp add: extends_def)
qed

subsection \<open>The measure\<close>

text \<open>The size of the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal form of the value of a variable.\<close>

definition vsz :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> indexname \<times> ptyp \<Rightarrow> nat" where
  "vsz \<tau>' \<sigma> y = lsize (\<lambda>_. Atom 0) \<tau>' (SOME w. \<beta>\<eta>cl (\<sigma> (code (AVar (fst y)))) w \<and> normal w) (trty (snd y))"

lemma vsz_lsize:
  assumes ty: "\<And>e. (e, \<tau>') \<turnstile> \<sigma> (code (AVar x)) : trty T"
    and w: "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar x))" "no_redex w" "(\<lambda>_. Atom 0, \<tau>') \<turnstile> w : trty T"
  shows "vsz \<tau>' \<sigma> (x, T) = lsize (\<lambda>_. Atom 0) \<tau>' w (trty T)"
proof -
  let ?x = "\<sigma> (code (AVar x))"
  from normal_form_ex[OF ty] have "\<exists>w. \<beta>\<eta>cl ?x w \<and> normal w" .
  from someI_ex[OF this] have n: "\<beta>\<eta>cl ?x (SOME w. \<beta>\<eta>cl ?x w \<and> normal w)" "normal (SOME w. \<beta>\<eta>cl ?x w \<and> normal w)"
    by blast+
  show ?thesis unfolding vsz_def fst_conv snd_conv
  proof (rule lsize_equiv)
    show "(SOME w. \<beta>\<eta>cl ?x w \<and> normal w) \<equiv>\<^sub>\<beta>\<^sub>\<eta> w"
      using equiv_trans[OF equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF n(1)]] equiv_sym[OF w(1)]] .
    show "(\<lambda>_. Atom 0, \<tau>') \<turnstile> (SOME w. \<beta>\<eta>cl ?x w \<and> normal w) : trty T"
      by (rule subject_reduction_\<beta>\<eta>[OF n(1) ty])
  qed (use n w normal_no_redex in auto)
qed

text \<open>A value \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. s\<close> has the size of its body.\<close>

lemma vsz_Abs_m:
  assumes "\<sigma> (code (AVar x)) = Abs_m (length Ts) s" "(env_ext (\<lambda>_. Atom 0) (map trty Ts), \<tau>') \<turnstile> s : trty U"
    "no_redex s" "no_loose_bound s (length Ts)"
  shows "vsz \<tau>' \<sigma> (x, foldr fun_type Ts U) = lsize (env_ext (\<lambda>_. Atom 0) (map trty Ts)) \<tau>' s (trty U)"
proof -
  have ty0: "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m (length Ts) s : map trty Ts \<Rrightarrow> trty U"
    using typing_Abs_m[OF assms(2)] by simp
  have cl: "no_loose_bound (Abs_m (length Ts) s) 0" using assms(4) by (simp add: loose_bound_Abs_m)
  have ty: "(e, \<tau>') \<turnstile> \<sigma> (code (AVar x)) : trty (foldr fun_type Ts U)" for e
    using typing_closed[OF ty0 cl] assms(1) by (simp add: trty_foldr)
  have "vsz \<tau>' \<sigma> (x, foldr fun_type Ts U) =
      lsize (\<lambda>_. Atom 0) \<tau>' (Abs_m (length Ts) s) (trty (foldr fun_type Ts U))"
  proof (rule vsz_lsize)
    show "(e, \<tau>') \<turnstile> \<sigma> (code (AVar x)) : trty (foldr fun_type Ts U)" for e by (rule ty)
  qed (use assms(1,3) ty0 in \<open>simp_all add: trty_foldr\<close>)
  also have "\<dots> = lsize (env_ext (\<lambda>_. Atom 0) (map trty Ts)) \<tau>' s (trty U)"
    by (simp add: trty_foldr lsize_Abs_m)
  finally show ?thesis .
qed

text \<open>The measure of a state: the sum of the sizes of the values of the unbound reachable variables.\<close>

definition mu :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> nat" where
  "mu \<tau>' \<sigma> env dps = (\<Sum>y\<in>unb env (vps_dps dps). vsz \<tau>' \<sigma> y)"


subsection \<open>Extensions of states\<close>

text \<open>
  \<open>sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV\<close>: the state \<open>(env', dps')\<close> is in the invariant for the
  extensions \<open>V'\<close> and \<open>\<sigma>'\<close> of \<open>V\<close> and \<open>\<sigma>\<close>, and only the variables reachable from \<open>D\<close> and the new
  variables \<open>NV\<close> are reachable from it.
\<close>

definition sext :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow>
    (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV \<longleftrightarrow>
    cinv ar V' \<tau>' \<sigma>' env' dps' \<and> agreeV (maxidx env) V V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and>
    maxidx env \<le> maxidx env' \<and> extends env' env \<and> finite NV \<and>
    (\<forall>y\<in>NV. maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env') \<and>
    (\<forall>X. reach env' X \<subseteq> reach env (X \<union> D) \<union> NV) \<and> vps_dps dps' \<subseteq> reach env D \<union> NV"

lemma reach_new:
  assumes "fresh_env env" "\<forall>y\<in>NV. maxidx env < snd (fst y)"
  shows "reach env NV = NV"
proof
  show "reach env NV \<subseteq> NV"
  proof
    fix z assume "z \<in> reach env NV"
    then obtain y where y: "y \<in> NV" "(z, y) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
    have "reach env {y} = {y}"
      using reach_unbound[OF lk_fresh[OF assms(1)]] assms(2) y(1) by (cases y) auto
    with y show "z \<in> NV" by (auto simp: reach_def)
  qed
qed (rule reach_incl)

lemma sext_trans:
  assumes s1: "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env1 dps1 D1 NV1" and s2: "sext ar V1 \<tau>' \<sigma>1 env1 V2 \<sigma>2 env2 dps2 D2 NV2"
    and fr: "fresh_env env" and D: "D2 \<subseteq> reach env D1 \<union> NV1"
  shows "sext ar V \<tau>' \<sigma> env V2 \<sigma>2 env2 dps2 D1 (NV1 \<union> NV2)"
proof -
  from s1 have c1: "agreeV (maxidx env) V V1" "agree (maxidx env) \<sigma> \<sigma>1" "maxidx env \<le> maxidx env1"
    "extends env1 env" "finite NV1" "\<forall>y\<in>NV1. maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env1"
    "\<And>X. reach env1 X \<subseteq> reach env (X \<union> D1) \<union> NV1"
    by (auto simp: sext_def)
  from s2 have c2: "cinv ar V2 \<tau>' \<sigma>2 env2 dps2" "agreeV (maxidx env1) V1 V2" "agree (maxidx env1) \<sigma>1 \<sigma>2"
    "maxidx env1 \<le> maxidx env2" "extends env2 env1" "finite NV2"
    "\<forall>y\<in>NV2. maxidx env1 < snd (fst y) \<and> snd (fst y) \<le> maxidx env2"
    "\<And>X. reach env2 X \<subseteq> reach env1 (X \<union> D2) \<union> NV2" "vps_dps dps2 \<subseteq> reach env1 D2 \<union> NV2"
    by (auto simp: sext_def)
  have nv1: "reach env NV1 = NV1" using reach_new[OF fr] c1(6) by blast
  have rD2: "reach env D2 \<subseteq> reach env D1 \<union> NV1"
    using reach_mono[of D2 env "D1 \<union> NV1"] D reach_incl[of "D1 \<union> NV1" env] nv1
    by (auto simp: reach_Un)
  have r: "reach env2 X \<subseteq> reach env (X \<union> D1) \<union> (NV1 \<union> NV2)" for X
  proof -
    have "reach env2 X \<subseteq> reach env1 (X \<union> D2) \<union> NV2" by (rule c2(8))
    also have "\<dots> \<subseteq> reach env (X \<union> D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(7)[of "X \<union> D2"] by blast
    also have "\<dots> \<subseteq> reach env (X \<union> D1) \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: reach_Un)
    finally show ?thesis .
  qed
  have v: "vps_dps dps2 \<subseteq> reach env D1 \<union> (NV1 \<union> NV2)"
  proof -
    have "vps_dps dps2 \<subseteq> reach env1 D2 \<union> NV2" by (rule c2(9))
    also have "\<dots> \<subseteq> reach env (D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(7)[of D2] by blast
    also have "\<dots> \<subseteq> reach env D1 \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: reach_Un)
    finally show ?thesis .
  qed
  show ?thesis unfolding sext_def
  proof (intro conjI c2(1) r v allI)
    show "agreeV (maxidx env) V V2" using agreeV_trans[OF c1(1) c2(2) c1(3)] .
    show "agree (maxidx env) \<sigma> \<sigma>2" using agree_trans[OF c1(2) c2(3) c1(3)] .
    show "maxidx env \<le> maxidx env2" using c1(3) c2(4) by simp
    show "extends env2 env" using c2(5) c1(4) by (rule extends_trans)
    show "finite (NV1 \<union> NV2)" using c1(5) c2(6) by simp
    show "\<forall>y\<in>NV1 \<union> NV2. maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env2"
      using c1(3,6) c2(4,7) by force
  qed
qed

subsection \<open>New variables for arguments\<close>

lemma genvars_maxidx:
  assumes "genvars name env Ts = (env', vs)"
  shows "maxidx env' = maxidx env + 1" "vs = genvs name (maxidx env + 1) 0 Ts"
  using assms by (auto simp: genvars_def split: env.splits)

lemma genvs_index: "v \<in> set (genvs name i n Ts) \<Longrightarrow> snd (var_of v) = i"
  by (induction name i n Ts rule: genvs.induct) auto

lemma list_all2_Var: "list_all2 (\<lambda>v T. \<exists>x. v = Var x T) vs Ts \<Longrightarrow> vs = map2 Var (map var_of vs) Ts"
  by (induction rule: list_all2_induct) auto

text \<open>The new variables of \<^const>\<open>make_args\<close> extend a solution by given values.\<close>

lemma make_args_extend:
  assumes inv: "cinv ar V \<tau>' \<sigma> env dps" and ma: "make_args a Ts env Us = (env1, args)"
    and lw: "length ws = length Us"
    and ws: "\<And>i. i < length Us \<Longrightarrow>
      no_loose_bound (ws ! i) 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> ws ! i : trty (foldr fun_type Ts (Us ! i)))"
  obtains V1 \<sigma>1 xs where "cinv ar V1 \<tau>' \<sigma>1 env1 dps" "agree (maxidx env) \<sigma> \<sigma>1"
    "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env1" "extends env1 env"
    "length xs = length Us" "distinct xs" "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env1"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. \<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
proof (cases "Us = []")
  case True
  with ma have "env1 = env" "args = []" by (simp_all add: make_args_def)
  with True show ?thesis using that[of V \<sigma> "[]"] inv by (simp add: extends_def)
next
  case False
  define Gs where "Gs = map (\<lambda>T. foldr fun_type Ts T) Us"
  obtain env' vs where g: "genvars a env Gs = (env', vs)" by (cases "genvars a env Gs")
  with False ma have e: "env1 = env'" "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
    by (simp_all add: make_args_def Gs_def)
  note gm = genvars_maxidx[OF g] and gs = genvars_simps[OF g]
  define xs where "xs = map var_of vs"
  have lvs: "length vs = length Us" using list_all2_lengthD[OF gs(3)] by (simp add: Gs_def)
  have vs: "vs = map2 Var xs Gs" using list_all2_Var[OF gs(3)] by (simp add: xs_def)
  have dxs: "distinct xs" using genvs_distinct[of 0 a "maxidx env + 1" Gs] gm(2) by (simp add: xs_def)
  have ixs: "snd x = maxidx env + 1" if "x \<in> set xs" for x
    using that genvs_index gm(2) by (auto simp: xs_def)
  have lxs: "length xs = length Us" using lvs by (simp add: xs_def)
  define ys where "ys = zip xs (zip Gs ws)"
  note ei = env_invD[OF cinvD(1)[OF inv]]
  have yv: "maxidx env < snd x \<and> no_loose_bound w 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> w : trty T)"
    if "(x, T, w) \<in> set ys" for x T w
  proof -
    from that obtain i where i: "i < length Us" "x = xs ! i" "T = Gs ! i" "w = ws ! i"
      using lxs lw by (auto simp: ys_def in_set_conv_nth Gs_def)
    have "x \<in> set xs" using i(1,2) lxs by simp
    with ixs ws[OF i(1)] i show ?thesis by (simp add: Gs_def)
  qed
  note se = solution_extend[of V \<tau>' \<sigma> env ys, OF cinvD(2)[OF inv] ei(4) yv]
  define \<sigma>1 where "\<sigma>1 = ext_subst \<sigma> ys"
  define V1 where "V1 = ext_typ V ys"
  have m1: "maxidx env1 = maxidx env + 1" using gm(1) e(1) by simp
  have ext: "extends env1 env" using gs(1) e(1) by (simp add: extends_def)
  have sol1: "solution V1 \<tau>' \<sigma>1 env1"
    using se(1) gs(1) e(1) by (simp add: solution_def sat_def \<sigma>1_def V1_def)
  have fr1: "fresh_env env1"
    unfolding fresh_env_def e(1) gs(1) gm(1)
  proof (intro allI impI)
    fix x U u assume "vt_lookup (tenv env) x = Some (U, u)"
    from fresh_envD[OF ei(4) this] show "snd x \<le> maxidx env + 1 \<and> below (maxidx env + 1) u"
      by (auto intro: below_mono)
  qed
  have ety1: "env_typed V1 env1"
    using env_typed_agreeV[OF ei(3) ei(4) se(3)] gs(1) e(1) by (simp add: env_typed_def V1_def)
  have "env_inv ar V1 env1"
    using ei(1,2) ety1 fr1 gs(1,2) e(1)
    by (simp add: env_inv_def acyc_def dep_tenv[OF gs(1)] wf_env_def)
  then have "cinv ar V1 \<tau>' \<sigma>1 env1 dps"
    using cinv_extend[OF inv _ sol1 se(2,3)[folded \<sigma>1_def V1_def]] m1 by simp
  moreover have "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    using lxs by (simp add: e(2) vs Gs_def map_zip_map2 zip_map2 map_map comp_def split_def)
  moreover have "\<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    if i: "i < length Us" for i
  proof -
    have "map_of ys (xs ! i) = Some (Gs ! i, ws ! i)"
      using map_of_zip_nth[of xs "zip Gs ws" i] lxs lw dxs i by (simp add: ys_def Gs_def)
    then show ?thesis using i by (simp add: \<sigma>1_def V1_def ext_subst_AVar ext_typ_simp Gs_def)
  qed
  ultimately show ?thesis
    using that[of V1 \<sigma>1 xs] se(2,3) m1 ext lxs dxs ixs by (simp add: \<sigma>1_def V1_def)
qed

subsection \<open>Normal forms of copies\<close>

lemma no_redex_Abs_apps: "no_redex (dB.Abs u \<degree>\<degree> ts) \<Longrightarrow> ts = []"
  by (induction ts rule: rev_induct) auto

text \<open>A \<open>\<beta>\<close>-normal term that is not an abstraction is an atom applied to arguments.\<close>

lemma no_redex_atom_head:
  assumes "no_redex s" "\<not> Unif_Occurs.is_Abs s"
  obtains h ss where "is_atom h" "s = h \<degree>\<degree> ss"
proof -
  have "no_redex s \<longrightarrow> \<not> Unif_Occurs.is_Abs s \<longrightarrow> (\<exists>h ss. is_atom h \<and> s = h \<degree>\<degree> ss)"
  proof (induction s rule: Apps_dB_induct)
    case (1 n ts)
    then show ?case by (intro impI exI[of _ "BVar n"] exI[of _ ts]) simp
  next
    case (2 u ts)
    show ?case
    proof (intro impI)
      assume "no_redex (dB.Abs u \<degree>\<degree> ts)" "\<not> Unif_Occurs.is_Abs (dB.Abs u \<degree>\<degree> ts)"
      with no_redex_Abs_apps show "\<exists>h ss. is_atom h \<and> dB.Abs u \<degree>\<degree> ts = h \<degree>\<degree> ss" by fastforce
    qed
  next
    case (3 n ts)
    then show ?case by (intro impI exI[of _ "dB.Var n"] exI[of _ ts]) simp
  qed
  with assms that show ?thesis by blast
qed

lemma Abs_m_apps_downs:
  assumes "no_loose_bound s n"
  shows "Abs_m n s \<degree>\<degree> map BVar (downs n) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
proof -
  have "no_loose_bound (Abs_m n s) 0" using assms by (simp add: loose_bound_Abs_m)
  from eta_expand_equiv[OF this, of n] show ?thesis by (rule Abs_m_equiv_reflect)
qed

lemma Abs_m_Suc': "Abs_m (Suc n) t = Abs_m n (dB.Abs t)"
  by (induction n) auto

lemma env_ext_snoc: "env_ext e (Ts @ [T]) = (env_ext e Ts)\<langle>0:T\<rangle>"
  by (simp add: env_ext_def)


subsection \<open>Normalizing arguments\<close>

lemma copy_norm_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env dps" and bok: "binders_ok ar rb" and w: "wf_tm ar rb t"
    and ty: "has_type V (map snd rb) t T" and bl: "below (maxidx env) t"
  obtains u1 u2 where "ok (head_norm env t) u1" "ok (eta_norm env rb u1) u2"
    "wf_tm ar rb u2" "hnf u2" "hlong V (map snd rb) u2 T" "below (maxidx env) u2"
    "vps u2 \<subseteq> reach env (vps t)" "mk_subst \<sigma> (tr u2) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from head_norm_term[OF ei(1,2,3) ty] obtain u1 where h: "head_norm env t = Some (Ok u1)" by blast
  have ty1: "has_type V (map snd rb) u1 T" by (rule head_norm_typed[OF h refl ei(2,3) ty])
  from eta_norm_term[OF e ty1] obtain u2 where et: "eta_norm env rb u1 = Some (Ok u2)" by blast
  have h': "ok (head_norm env t) u1" and et': "ok (eta_norm env rb u1) u2" using h et by simp_all
  note hw = head_norm_wf_tm[OF h' ei(2) w]
  note ew = eta_norm_wf_tm[OF et' ei(2) bok hw[THEN conjunct1]]
  have hl: "hlong V (map snd rb) u2 T" by (rule eta_norm_hlong[OF e ty1 et'])
  have hn: "hnf u2" by (rule eta_norm_hnf[OF e et' head_norm_hnf[OF h refl]])
  have vs: "vps u2 = vps u1" using eta_norm_shape[OF et' e] by simp
  have rv: "vps u2 \<subseteq> reach env (vps t)" using hn_vps[OF head_norm_hn[OF h e refl]] vs by simp
  have b: "below (maxidx env) u2"
    using below_head_norm[OF h refl ei(2,4) bl] vs by (simp add: below_vps_iff)
  have "mk_subst \<sigma> (tr u2) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
    using equiv_trans[OF env_equivD[OF hw[THEN conjunct2] \<sigma>(1,4)] env_equivD[OF ew[THEN conjunct2] \<sigma>(1,4)]]
    by (rule equiv_sym)
  with that[OF h' et' ew[THEN conjunct1] hn hl b rv] show ?thesis .
qed

subsection \<open>Types\<close>

lemma trty_inj: "trty T = trty U \<Longrightarrow> T = U"
proof (induction T arbitrary: U rule: trty.induct)
  case (1 a T1 T2)
  then show ?case by (cases U rule: trty.cases) (auto split: if_splits)
qed (case_tac U rule: trty.cases; auto split: if_splits)+

lemma trty_base: "\<not> is_funT B \<Longrightarrow> \<exists>a. trty B = Atom a"
  by (cases B rule: trty.cases) auto

lemma arrows_Atom_inj: "Ws \<Rrightarrow> Atom a = Ws' \<Rrightarrow> Atom b \<Longrightarrow> Ws = Ws' \<and> a = b"
proof (induction Ws arbitrary: Ws')
  case Nil
  then show ?case by (cases Ws') auto
next
  case (Cons W Ws)
  then show ?case by (cases Ws') auto
qed

lemma arrows_base_inj:
  assumes "Ws \<Rrightarrow> trty B = Ws' \<Rrightarrow> trty B'" "\<not> is_funT B" "\<not> is_funT B'"
  shows "Ws = Ws' \<and> B = B'"
  using assms trty_base[OF assms(2)] trty_base[OF assms(3)] arrows_Atom_inj trty_inj by metis

lemma has_type_combound:
  assumes "has_type V Bs G (foldr fun_type Ts U)" "n + length Ts \<le> length Bs"
    "\<And>i. i < length Ts \<Longrightarrow> Bs ! (n + i) = Ts ! (length Ts - Suc i)"
  shows "has_type V Bs (combound G (integer_of_nat n) (length Ts)) U"
  using assms
proof (induction Ts arbitrary: n U rule: rev_induct)
  case (snoc A Ts)
  have IH: "has_type V Bs (combound G (integer_of_nat (Suc n)) (length Ts)) (A \<rightarrow>\<^sub>T U)"
  proof (rule snoc.IH)
    show "has_type V Bs G (foldr fun_type Ts (A \<rightarrow>\<^sub>T U))" using snoc.prems(1) by simp
    show "Suc n + length Ts \<le> length Bs" using snoc.prems(2) by simp
    show "Bs ! (Suc n + i) = Ts ! (length Ts - Suc i)" if "i < length Ts" for i
      using snoc.prems(3)[of "Suc i"] that by (auto simp: nth_append)
  qed
  have "Bs ! n = A" using snoc.prems(3)[of 0] by simp
  then have "has_type V Bs (Bound (integer_of_nat n)) A"
    using snoc.prems(2) by (simp add: has_type_Bound_iff integer_reps)
  moreover have "integer_of_nat n + 1 = integer_of_nat (Suc n)" by (simp add: integer_eq_iff)
  ultimately show ?case using has_type.App[OF IH] by simp
qed simp

lemma has_type_combound0:
  "has_type V (rev Ts @ Rs) G (foldr fun_type Ts U) \<Longrightarrow> has_type V (rev Ts @ Rs) (combound G 0 (length Ts)) U"
  using has_type_combound[of V "rev Ts @ Rs" G Ts U 0] by (simp add: nth_append rev_nth)

text \<open>A solution fixes the rigid atoms, so they have their own types in \<open>\<tau>'\<close>.\<close>

lemma solution_rigid_type:
  assumes "solution V \<tau>' \<sigma> env" "h = Const a T \<or> h = Free a T"
  shows "(e, \<tau>') \<turnstile> tr h : trty T"
proof -
  note \<sigma> = solutionD[OF assms(1)]
  define c where "c = (if h = Const a T then code (AConst a T) else code (AFree a T))"
  have tr: "tr h = dB.Var c" and rc: "rigid_code c" and tc: "tau V c = trty T"
    using assms(2) by (auto simp: c_def)
  have "(e, \<tau>') \<turnstile> \<sigma> c : tau V c" by (rule typed_onD[OF \<sigma>(2)]) (simp add: c_def)
  with rigid_substD[OF \<sigma>(3) rc] tr tc show ?thesis by simp
qed

subsection \<open>Projections\<close>

lemma body_type_res: "vt_is_empty (tyenv env) \<Longrightarrow> body_type env T = return (res_type T)"
  using body_type_base[OF _ res_type_base, of env "arg_types T" T] by (simp add: arg_res_type)

lemma binder_types_arg: "vt_is_empty (tyenv env) \<Longrightarrow> binder_types env T = return (arg_types T)"
  using binder_types_base[OF _ res_type_base, of env "arg_types T" T] by (simp add: arg_res_type)

lemma strip_type_arg_res:
  "vt_is_empty (tyenv env) \<Longrightarrow> strip_type env T = return (arg_types T, res_type T)"
  by (simp add: strip_type_def body_type_res binder_types_arg)

lemma make_projs_exact:
  "length Ts = length targs \<Longrightarrow> \<exists>ps. make_projs u targs0 Ts targs = returnW ps \<and>
    (\<forall>j<length targs. (Bound (integer_of_nat j), Ts ! (length targs - Suc j), targs ! (length targs - Suc j)) \<in> set ps)"
proof (induction u targs0 Ts targs rule: make_projs.induct)
  case (1 u targs0 T Ts targ targs)
  then obtain ps where ps: "make_projs u targs0 Ts targs = returnW ps"
    and m: "\<forall>j<length targs. (Bound (integer_of_nat j), Ts ! (length targs - Suc j), targs ! (length targs - Suc j)) \<in> set ps"
    by auto
  have l: "length Ts = length targs" using "1.prems" by simp
  show ?case
  proof (intro exI conjI allI impI)
    show "make_projs u targs0 (T # Ts) (targ # targs) = returnW ((Bound (ilength Ts), T, targ) # ps)"
      by (simp add: ps)
  next
    fix j assume j: "j < length (targ # targs)"
    show "(Bound (integer_of_nat j), (T # Ts) ! (length (targ # targs) - Suc j),
        (targ # targs) ! (length (targ # targs) - Suc j)) \<in> set ((Bound (ilength Ts), T, targ) # ps)"
    proof (cases "j = length targs")
      case True
      then show ?thesis using l by (simp add: ilength_eq)
    next
      case False
      with j have "j < length targs" by simp
      with m have "(Bound (integer_of_nat j), Ts ! (length targs - Suc j), targs ! (length targs - Suc j)) \<in> set ps"
        by blast
      moreover have "length targs - j = Suc (length targs - Suc j)" using \<open>j < length targs\<close> by simp
      ultimately show ?thesis by simp
    qed
  qed
qed auto

lemma cunify_types_ground_neq:
  "ground ar T \<Longrightarrow> ground ar U \<Longrightarrow> T \<noteq> U \<Longrightarrow> \<exists>evs. cunify_types alg T U env = Some (evs, UErr CANTUNIFY)"
  by (simp add: cunify_types_def unify_types_ground raise_def emit_def bindW_def raiseW_def)

lemma projenv_result:
  assumes "ground ar base" "ground ar bary"
  shows "okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ 0 tail)
    (if base = bary then S_Proj vname env Ts Us targs rb u dps head targ tail else tail)"
proof -
  let ?m = "(if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base bary env
    else cunify_types (cfg_alg cfg) base bary env)"
  let ?r = "do {env' \<leftarrow> ?m; returnW (S_Proj vname env' Ts Us targs rb u dps head targ tail)}"
  show ?thesis
  proof (cases "base = bary")
    case True
    then have "okW ?m env"
      by (auto simp: test_unify_types_def cunify_types_same okW_whenW)
    then have "okW ?r (S_Proj vname env Ts Us targs rb u dps head targ tail)" by auto
    then have "okW (handleW ?r (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e))
        (S_Proj vname env Ts Us targs rb u dps head targ tail)"
      by (rule okW_handleW[THEN iffD2, OF disjI1])
    then show ?thesis unfolding projenv_0 prod.case if_P[OF True] .
  next
    case False
    from cunify_types_ground_neq[OF assms False] obtain evs
      where c: "cunify_types (cfg_alg cfg) base bary env = Some (evs, UErr CANTUNIFY)" by blast
    then have "\<exists>evs. ?m = Some (evs, UErr CANTUNIFY)"
      by (auto simp: test_unify_types_def bindW_def)
    then have "\<exists>evs. ?r = Some (evs, UErr CANTUNIFY)" by (auto simp: bindW_def)
    with False show ?thesis by (auto simp: projenv_0 okW_handleW)
  qed
qed

lemma ev_proj_tail_if: "ev cfg tail x \<Longrightarrow> ev cfg (if b then S_Proj vname env Ts Us targs rb u dps head targ tail else tail) x"
  by (auto intro: ev.proj_tail)

text \<open>The sequence of \<^const>\<open>matchfun\<close> contains the elements of all type-correct projections and of the imitation.\<close>

lemma matchfun_result:
  assumes "vt_is_empty (tyenv env)" "ground ar base" "\<forall>(bv, T, targ)\<in>set projs. ground ar T"
  shows "\<exists>sq. okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) sq \<and>
    (\<forall>x. ev cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg sq x) \<and>
    (\<forall>bv T targ env' args env2 fr ff. (bv, T, targ) \<in> set projs \<longrightarrow> res_type T = base \<longrightarrow>
      make_args vname Ts env (arg_types T) = (env', args) \<longrightarrow>
      okW (SIMPL (cfg_alg cfg) env'
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<longrightarrow>
      ev cfg sq (El_C (list_comb bv args) env2 (fr @ ff)))"
  using assms(3)
proof (induction projs)
  case Nil
  show ?case by (intro exI[of _ "case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty"]) simp
next
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  from Cons obtain tail where tl: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) tail"
    and imit: "\<forall>x. ev cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg tail x"
    and prj: "\<forall>bv T targ env' args env2 fr ff. (bv, T, targ) \<in> set projs \<longrightarrow> res_type T = base \<longrightarrow>
      make_args vname Ts env (arg_types T) = (env', args) \<longrightarrow>
      okW (SIMPL (cfg_alg cfg) env'
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<longrightarrow>
      ev cfg tail (El_C (list_comb bv args) env2 (fr @ ff))"
    by auto
  have gT: "ground ar T" using Cons.prems p by simp
  have gb: "ground ar (res_type T)"
    using strip_type_ground(2)[OF assms(1) gT, of "arg_types T" "res_type T"]
    by (simp add: strip_type_arg_res[OF assms(1)])
  let ?r = "if base = res_type T then S_Proj vname env Ts (arg_types T) targs rb u dps bv targ tail else tail"
  have pe: "okW (projenv cfg vname rb targs u env dps base Ts bv (arg_types T, res_type T) targ 0 tail) ?r"
    by (rule projenv_result[OF assms(2) gb])
  have "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (p # projs)) ?r"
    using tl pe by (auto simp: p strip_type_arg_res[OF assms(1)] foldrW_arity_guesses_ground[OF gb])
  moreover have "ev cfg ?r x" if "ev cfg tail x" for x using that by (rule ev_proj_tail_if)
  moreover have "ev cfg ?r (El_C (list_comb bv' args) env2 (fr @ ff))"
    if "(bv', T', targ') \<in> set (p # projs)" "res_type T' = base"
      "make_args vname Ts env (arg_types T') = (env', args)"
      "okW (SIMPL (cfg_alg cfg) env'
        ((rb, list_comb targ' (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff)"
    for bv' T' targ' env' args env2 fr ff
  proof (cases "(bv', T', targ') = p")
    case True
    with that(3,4) p have "ev cfg (S_Proj vname env Ts (arg_types T) targs rb u dps bv targ tail)
        (El_C (list_comb bv args) env2 (fr @ ff))"
      by (auto intro: ev.proj)
    with True that(2) p show ?thesis by simp
  next
    case False
    with that have "(bv', T', targ') \<in> set projs" by simp
    with that(2-4) prj have "ev cfg tail (El_C (list_comb bv' args) env2 (fr @ ff))" by blast
    then show ?thesis by (rule ev_proj_tail_if)
  qed
  ultimately show ?case using imit by blast
qed

subsection \<open>Copies\<close>

lemma vsz_agree: "agree m \<sigma> \<sigma>' \<Longrightarrow> snd (fst y) \<le> m \<Longrightarrow> vsz \<tau>' \<sigma>' y = vsz \<tau>' \<sigma> y"
  by (simp add: vsz_def agree_Var)

lemma sum_vsz_agree: "agree m \<sigma> \<sigma>' \<Longrightarrow> \<forall>y\<in>NV. snd (fst y) \<le> m \<Longrightarrow> sum (vsz \<tau>' \<sigma>') NV = sum (vsz \<tau>' \<sigma>) NV"
  by (rule sum.cong) (auto simp: vsz_agree)

lemma sum_Un_le: "finite A \<Longrightarrow> finite B \<Longrightarrow> sum (f :: _ \<Rightarrow> nat) (A \<union> B) \<le> sum f A + sum f B"
  using sum.union_inter[of A B f] by linarith

lemma sext_refl: "cinv ar V \<tau>' \<sigma> env dps \<Longrightarrow> vps_dps dps \<subseteq> D \<Longrightarrow> sext ar V \<tau>' \<sigma> env V \<sigma> env dps D {}"
  using reach_incl[of D env] by (auto simp: sext_def reach_Un)

lemma sext_mono:
  assumes s: "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV" and D: "D \<subseteq> D'"
  shows "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D' NV"
proof -
  have r: "reach env (X \<union> D) \<subseteq> reach env (X \<union> D')" for X using D by (intro reach_subset) blast
  have "reach env D \<subseteq> reach env D'" using D by (rule reach_subset)
  then have "vps_dps dps' \<subseteq> reach env D' \<union> NV" using s by (auto simp: sext_def)
  moreover have "reach env' X \<subseteq> reach env (X \<union> D') \<union> NV" for X using s r[of X] by (auto simp: sext_def)
  ultimately show ?thesis using s by (simp add: sext_def)
qed

lemma sextD:
  assumes "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV"
  shows "cinv ar V' \<tau>' \<sigma>' env' dps'" "agreeV (maxidx env) V V'" "agree (maxidx env) \<sigma> \<sigma>'"
    "maxidx env \<le> maxidx env'" "extends env' env" "finite NV"
    "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'"
    "\<And>X. reach env' X \<subseteq> reach env (X \<union> D) \<union> NV" "vps_dps dps' \<subseteq> reach env D \<union> NV"
  using assms by (auto simp: sext_def)

abbreviation bctx :: "ptyp list \<Rightarrow> nat \<Rightarrow> type" where
  "bctx Ts \<equiv> env_ext (\<lambda>_. Atom 0) (map trty Ts)"

text \<open>
  \<open>mc_pre\<close>: the assumptions on a call \<open>mc cfg vname rb targs u env dps\<close> of \<open>matchcopy\<close> with a target
  \<open>s\<close>: the abstraction \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. s\<close> applied to the arguments \<open>targs\<close> is the instance of \<open>u\<close>.
  \<open>copy_res\<close>: a copy \<open>u'\<close> with the extensions of the solution and the typing: its instance is
  the target, and the values of the new variables are smaller than the target, strictly by \<open>k\<close>.
\<close>

definition mc_pre :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> dB \<Rightarrow> bool" where
  "mc_pre ar V \<tau>' \<sigma> env dps rb targs Ts u U s \<longleftrightarrow>
    cinv ar V \<tau>' \<sigma> env dps \<and> binders_ok ar rb \<and>
    (\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t) \<and> list_all2 (has_type V (map snd rb)) targs Ts \<and>
    wf_tm ar rb u \<and> hnf u \<and> hlong V (map snd rb) u U \<and> below (maxidx env) u \<and>
    (bctx Ts, \<tau>') \<turnstile> s : trty U \<and> no_redex s \<and> no_loose_bound s (length Ts) \<and>
    Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"

definition copy_res :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> dB \<Rightarrow> nat \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow>
    (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "copy_res ar V \<tau>' \<sigma> env D Ts U s k u' env' dps' V' \<sigma>' NV \<longleftrightarrow>
    sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV \<and> has_type V' (rev Ts) u' U \<and> wf_cp ar (length Ts) u' \<and>
    below (maxidx env') u' \<and> vps u' \<subseteq> NV \<and> mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s \<and>
    (\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + k \<le> lsize (bctx Ts) \<tau>' s (trty U)"

definition mc_post :: "(name \<Rightarrow> nat) \<Rightarrow> cfg \<Rightarrow> name \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow>
    (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> dB \<Rightarrow> bool" where
  "mc_post ar cfg vname V \<tau>' \<sigma> env dps rb targs Ts u U s \<longleftrightarrow>
    (\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
      (\<exists>u' env' dps' V' \<sigma>' NV. ev cfg sq (El_C u' env' dps') \<and>
        copy_res ar V \<tau>' \<sigma> env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U s
          (if is_Var (head_of (strip_abs_body u)) then 0 else 1) u' env' dps' V' \<sigma>' NV))"

lemma mk_subst_list_agree:
  "\<forall>t\<in>set ts. below m t \<Longrightarrow> agree m \<sigma> \<sigma>' \<Longrightarrow>
    map (\<lambda>t. mk_subst \<sigma>' (tr t)) ts = map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
  by (auto simp: mk_subst_agree)

lemma list_all2_has_type_agreeV:
  "list_all2 (has_type V Bs) ts Ts \<Longrightarrow> \<forall>t\<in>set ts. below m t \<Longrightarrow> agreeV m V V' \<Longrightarrow>
    list_all2 (has_type V' Bs) ts Ts"
  by (induction rule: list_all2_induct) (auto intro: has_type_agreeV)

lemma defer_arg_typed:
  assumes "vt_is_empty (tyenv env)" "binders_ok ar rb" "typs_ok ar u" "has_type V (map snd rb) u A"
  shows "ok (defer_arg env rb u) False"
proof -
  have f: "fastype env rb u = return A" by (rule fastype_typed[OF assms(1,4)])
  then have gA: "ground ar A" using fastype_ground[OF assms(1-3), of A] by (simp add: return_def)
  from body_type_ground_ex[OF assms(1) gA] obtain B where b: "body_type env A = return B" by blast
  then have "ground ar B" using body_type_ground[OF assms(1) gA, of B] by (simp add: return_def)
  then show ?thesis by (simp add: defer_arg_def f b ground_not_TVar return_def)
qed

lemma copycons_ok:
  "ok (head_norm env uarg) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> ok (defer_arg env rb u2) False \<Longrightarrow>
    okW (mc cfg vname rb targs u2 env dps) sq \<Longrightarrow>
    okW (copycons cfg vname rb targs uarg uargs env dps) (S_MapCons uargs sq)"
  by (auto simp: copycons_def)

text \<open>Copying the arguments of an imitation, given copies of each argument.\<close>

lemma copyargs_complete:
  assumes MC: "\<And>V0 \<sigma>0 env0 dps0 u0 A s0. (A, s0) \<in> set (zip As ss) \<Longrightarrow>
      mc_pre ar V0 \<tau>' \<sigma>0 env0 dps0 rb targs Ts u0 A s0 \<Longrightarrow> mc_post ar cfg vname V0 \<tau>' \<sigma>0 env0 dps0 rb targs Ts u0 A s0"
    and inv: "cinv ar V \<tau>' \<sigma> env dps" and bok: "binders_ok ar rb"
    and tg: "\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t" "list_all2 (has_type V (map snd rb)) targs Ts"
    and ua: "\<forall>t\<in>set uargs. wf_tm ar rb t \<and> below (maxidx env) t" "list_all2 (has_type V (map snd rb)) uargs As"
    and ss: "list_all2 (\<lambda>s A. (bctx Ts, \<tau>') \<turnstile> s : trty A \<and> no_redex s \<and> no_loose_bound s (length Ts)) ss As"
    and eq: "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)) ss uargs"
  shows "\<exists>uargs' env' dps' V' \<sigma>' NV. ev cfg (copyargs vname rb targs env dps uargs) (El_D uargs' env' dps') \<and>
    sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) NV \<and>
    list_all2 (has_type V' (rev Ts)) uargs' As \<and>
    (\<forall>u'\<in>set uargs'. wf_cp ar (length Ts) u' \<and> below (maxidx env') u' \<and> vps u' \<subseteq> NV) \<and>
    list_all2 (\<lambda>u' s. mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs' ss \<and>
    (\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) \<le> sum_list (map2 (\<lambda>s A. lsize (bctx Ts) \<tau>' s (trty A)) ss As)"
  using MC ua ss eq
proof (induction uargs arbitrary: As ss)
  case Nil
  then have "As = []" "ss = []" by (simp_all add: list_all2_Nil list_all2_Nil2)
  with Nil show ?case using sext_refl[OF inv, of "\<Union> (vps ` set []) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"]
    by (intro exI[of _ "[]"] exI[of _ env] exI[of _ dps] exI[of _ V] exI[of _ \<sigma>] exI[of _ "{}"])
      (auto intro: ev.single)
next
  case (Cons uarg uargs)
  from Cons.prems(3) obtain A As' where As: "As = A # As'" "has_type V (map snd rb) uarg A"
    "list_all2 (has_type V (map snd rb)) uargs As'"
    by (auto simp: list_all2_Cons1)
  from Cons.prems(4) As obtain s0 ss' where ss: "ss = s0 # ss'"
    "(bctx Ts, \<tau>') \<turnstile> s0 : trty A" "no_redex s0" "no_loose_bound s0 (length Ts)"
    "list_all2 (\<lambda>s A. (bctx Ts, \<tau>') \<turnstile> s : trty A \<and> no_redex s \<and> no_loose_bound s (length Ts)) ss' As'"
    by (auto simp: list_all2_Cons2)
  from Cons.prems(5) ss(1) have "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs
      \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)) (s0 # ss') (uarg # uargs)" by (simp only:)
  then have eq0: "Abs_m (length Ts) s0 \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr uarg)"
    and eqs: "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)) ss' uargs"
    unfolding list_all2_Cons by blast+
  have MC': "mc_post ar cfg vname V0 \<tau>' \<sigma>0 env0 dps0 rb targs Ts u0 A0 s1"
    if "(A0, s1) \<in> set (zip As' ss')" "mc_pre ar V0 \<tau>' \<sigma>0 env0 dps0 rb targs Ts u0 A0 s1"
    for V0 \<sigma>0 env0 dps0 u0 A0 s1
    using Cons.prems(1)[OF _ that(2)] that(1) As ss by simp
  have ua': "\<forall>t\<in>set uargs. wf_tm ar rb t \<and> below (maxidx env) t" using Cons.prems(2) by simp
  from Cons.IH[OF MC' ua' As(3) ss(5) eqs] obtain uargs1 env1 dps1 V1 \<sigma>1 NV1 where
    ev1: "ev cfg (copyargs vname rb targs env dps uargs) (El_D uargs1 env1 dps1)"
    and s1: "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env1 dps1 (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) NV1"
    and ty1: "list_all2 (has_type V1 (rev Ts)) uargs1 As'"
    and w1: "\<forall>u'\<in>set uargs1. wf_cp ar (length Ts) u' \<and> below (maxidx env1) u' \<and> vps u' \<subseteq> NV1"
    and e1: "list_all2 (\<lambda>u' s. mk_subst \<sigma>1 (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs1 ss'"
    and sz1: "(\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>1 y) \<le> sum_list (map2 (\<lambda>s A. lsize (bctx Ts) \<tau>' s (trty A)) ss' As')"
    by blast
  define D where "D = \<Union> (vps ` set (uarg # uargs)) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
  have s1': "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env1 dps1 D NV1" by (rule sext_mono[OF s1]) (auto simp: D_def)
  note sd1 = sextD[OF s1']
  have wu: "wf_tm ar rb uarg" "below (maxidx env) uarg" using Cons.prems(2) by auto
  have bu1: "below (maxidx env1) uarg" using below_mono[OF wu(2) sd1(4)] .
  have tyu1: "has_type V1 (map snd rb) uarg A" using has_type_agreeV[OF As(2) wu(2) sd1(2)] .
  obtain u1 u2 where cn: "ok (head_norm env1 uarg) u1" "ok (eta_norm env1 rb u1) u2" "wf_tm ar rb u2"
    "hnf u2" "hlong V1 (map snd rb) u2 A" "below (maxidx env1) u2" "vps u2 \<subseteq> reach env1 (vps uarg)"
    "mk_subst \<sigma>1 (tr u2) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>1 (tr uarg)"
    by (rule copy_norm_complete[OF sd1(1) bok wu(1) tyu1 bu1])
  have tg1: "\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env1) t" using tg(1) below_mono sd1(4) by blast
  have tgty1: "list_all2 (has_type V1 (map snd rb)) targs Ts"
    using list_all2_has_type_agreeV[OF tg(2) _ sd1(2)] tg(1) by blast
  have ta: "map (\<lambda>t. mk_subst \<sigma>1 (tr t)) targs = map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
    using mk_subst_list_agree[OF _ sd1(3)] tg(1) by blast
  have "mk_subst \<sigma>1 (tr uarg) = mk_subst \<sigma> (tr uarg)" using mk_subst_agree[OF wu(2) sd1(3)] .
  with cn(8) have e12: "mk_subst \<sigma>1 (tr u2) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr uarg)" by simp
  have eq1: "Abs_m (length Ts) s0 \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma>1 (tr t)) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>1 (tr u2)"
    using equiv_trans[OF eq0 equiv_sym[OF e12]] ta by (simp only:)
  have pre: "mc_pre ar V1 \<tau>' \<sigma>1 env1 dps1 rb targs Ts u2 A s0"
    unfolding mc_pre_def using sd1(1) bok tg1 tgty1 cn(3-6) ss(2-4) eq1 by simp
  from Cons.prems(1)[OF _ pre] As ss have "mc_post ar cfg vname V1 \<tau>' \<sigma>1 env1 dps1 rb targs Ts u2 A s0" by simp
  then obtain sq u' env2 dps2 V2 \<sigma>2 NV2 where mc: "okW (mc cfg vname rb targs u2 env1 dps1) sq"
    and ev2: "ev cfg sq (El_C u' env2 dps2)"
    and cr: "copy_res ar V1 \<tau>' \<sigma>1 env1 (vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps1) Ts A s0
      (if is_Var (head_of (strip_abs_body u2)) then 0 else 1) u' env2 dps2 V2 \<sigma>2 NV2"
    unfolding mc_post_def by blast
  from cr have s2: "sext ar V1 \<tau>' \<sigma>1 env1 V2 \<sigma>2 env2 dps2 (vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps1) NV2"
    and ty2: "has_type V2 (rev Ts) u' A" and w2: "wf_cp ar (length Ts) u'" "below (maxidx env2) u'" "vps u' \<subseteq> NV2"
    and e2: "mk_subst \<sigma>2 (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s0" and sz2: "(\<Sum>y\<in>NV2. vsz \<tau>' \<sigma>2 y) \<le> lsize (bctx Ts) \<tau>' s0 (trty A)"
    unfolding copy_res_def by auto
  note sd2 = sextD[OF s2]
  have fr: "fresh_env env" using env_invD(4)[OF cinvD(1)[OF inv]] .
  have DD: "vps u2 \<union> \<Union> (vps ` set targs) \<union> vps_dps dps1 \<subseteq> reach env D \<union> NV1"
  proof -
    have "vps u2 \<subseteq> reach env (vps uarg \<union> D) \<union> NV1" using cn(7) sd1(8)[of "vps uarg"] by blast
    moreover have "vps uarg \<union> D = D" by (auto simp: D_def)
    moreover have "\<Union> (vps ` set targs) \<subseteq> reach env D" using reach_incl[of D env] by (auto simp: D_def)
    ultimately show ?thesis using sd1(9) by auto
  qed
  have s12: "sext ar V \<tau>' \<sigma> env V2 \<sigma>2 env2 dps2 D (NV1 \<union> NV2)" by (rule sext_trans[OF s1' s2 fr DD])
  have ev: "ev cfg (copyargs vname rb targs env dps (uarg # uargs)) (El_D (u' # uargs1) env2 dps2)"
  proof -
    have "ok (defer_arg env1 rb u2) False"
      using defer_arg_typed[OF wf_envD(1)[OF env_invD(2)[OF cinvD(1)[OF sd1(1)]]] bok _ hlong_typed[OF cn(5)]]
        cn(3) by (simp add: wf_tm_def)
    from ev.maps[OF ev1 copycons_ok[OF cn(1,2) this mc] ev.map_cons[OF ev2]] show ?thesis by simp
  qed
  have b1: "\<forall>t\<in>set uargs1. below (maxidx env1) t" using w1 by blast
  have ty: "list_all2 (has_type V2 (rev Ts)) (u' # uargs1) As"
    using ty2 list_all2_has_type_agreeV[OF ty1 b1 sd2(2)] As(1) by simp
  have w: "\<forall>u''\<in>set (u' # uargs1). wf_cp ar (length Ts) u'' \<and> below (maxidx env2) u'' \<and> vps u'' \<subseteq> NV1 \<union> NV2"
    using w1 w2 below_mono[OF _ sd2(4)] by auto
  have "list_all2 (\<lambda>u' s. mk_subst \<sigma>2 (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs1 ss'"
    using e1 b1 by (induction rule: list_all2_induct) (auto simp: mk_subst_agree[OF _ sd2(3)])
  with e2 have e: "list_all2 (\<lambda>u' s. mk_subst \<sigma>2 (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) (u' # uargs1) ss" using ss(1) by simp
  have "(\<Sum>y\<in>NV1 \<union> NV2. vsz \<tau>' \<sigma>2 y) \<le> (\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>2 y) + (\<Sum>y\<in>NV2. vsz \<tau>' \<sigma>2 y)"
    by (rule sum_Un_le[OF sd1(6) sd2(6)])
  also have "(\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>2 y) = (\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>1 y)"
    using sum_vsz_agree[OF sd2(3)] sd1(7) by blast
  finally have "(\<Sum>y\<in>NV1 \<union> NV2. vsz \<tau>' \<sigma>2 y) \<le> sum_list (map2 (\<lambda>s A. lsize (bctx Ts) \<tau>' s (trty A)) ss As)"
    using sz1 sz2 ss(1) As(1) by simp
  then show ?case using ev s12[unfolded D_def] ty w e by blast
qed

lemma mapM_fastype:
  assumes "vt_is_empty (tyenv env)"
  shows "list_all2 (has_type V (map snd rb)) ts Ts \<Longrightarrow> mapM (fastype env rb) ts = return Ts"
  by (induction rule: list_all2_induct) (simp_all add: fastype_typed[OF assms] return_def)

lemma mc_unfold:
  assumes "vt_is_empty (tyenv env)" "fastype env rb (head_of u) = return T0"
    "mapM (fastype env rb) targs = return Ts"
  shows "mc cfg vname rb targs u env dps =
    (case head_of u of
        Abs a T body \<Rightarrow> do {
          s \<leftarrow> mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps;
          returnW (S_MapAbs a T s)}
      | Var w _ \<Rightarrow>
          (let (env', newhd) = genvar (fst w) env (foldr fun_type Ts (res_type T0)) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u) # dps))))
      | _ \<Rightarrow> do {
          projs \<leftarrow> make_projs u targs Ts targs;
          matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) (res_type T0) Ts (rev projs)})"
  by (subst mc.simps) (simp add: assms body_type_res fst_strip_comb liftM_return Let_def)

lemma sum_list_map2_nth:
  "length xs = length ys \<Longrightarrow> sum_list (map2 f xs ys) = (\<Sum>i<length xs. f (xs ! i) (ys ! i))"
proof (induction xs ys rule: list_induct2)
  case (Cons x xs y ys)
  then show ?case by (simp add: sum.lessThan_Suc_shift del: sum.lessThan_Suc)
qed simp

lemma cinv_Cons:
  "cinv ar V \<tau>' \<sigma> env dps \<Longrightarrow> wf_dp ar dp \<Longrightarrow> dp_typed V dp \<Longrightarrow> dp_below (maxidx env) dp \<Longrightarrow>
    dsolved \<sigma> dp \<Longrightarrow> cinv ar V \<tau>' \<sigma> env (dp # dps)"
  by (simp add: cinv_def)

lemma vps_combound[simp]: "vps (combound t n k) = vps t"
  by (induction k arbitrary: n) auto

lemma below_list_comb: "below m (list_comb h ts) \<longleftrightarrow> below m h \<and> (\<forall>t\<in>set ts. below m t)"
  by (auto simp: below_vps_iff vps_list_comb)

lemma head_of_nonAbs: "\<not> is_Abs (head_of u) \<Longrightarrow> \<not> is_Abs u"
  by (cases u) auto

lemma strip_abs_body_nonAbs: "\<not> is_Abs u \<Longrightarrow> strip_abs_body u = u"
  by (cases u) auto

lemma res_type_head:
  assumes "has_type V Bs u U" "\<not> is_funT U" "has_type V Bs (head_of u) T0"
  shows "res_type T0 = U" "\<exists>As. T0 = foldr fun_type As U \<and> list_all2 (has_type V Bs) (snd (strip_comb u)) As"
proof -
  from assms(1) head_of_list_comb[of u] obtain As where
    As: "has_type V Bs (head_of u) (foldr fun_type As U)" "list_all2 (has_type V Bs) (snd (strip_comb u)) As"
    by (metis has_type_list_comb)
  with has_type_unique[OF assms(3) As(1)] arg_res_type_fun[OF assms(2)]
  show "res_type T0 = U" "\<exists>As. T0 = foldr fun_type As U \<and> list_all2 (has_type V Bs) (snd (strip_comb u)) As"
    by auto
qed

lemma ground_has_type:
  "vt_is_empty (tyenv env) \<Longrightarrow> binders_ok ar rb \<Longrightarrow> wf_tm ar rb t \<Longrightarrow> has_type V (map snd rb) t T \<Longrightarrow>
    ground ar T"
  using fastype_ground[of env ar rb t T] fastype_typed[of env V rb t T] by (simp add: wf_tm_def return_def)

lemma lift_is_Abs: "Unif_Occurs.is_Abs (lift t k) = Unif_Occurs.is_Abs t"
  by (cases t) auto

lemma no_redex_lift: "no_redex (lift t k) = no_redex t"
  by (induction t arbitrary: k) (auto simp: lift_is_Abs)

text \<open>The body of the \<open>\<eta>\<close>-expansion of a \<open>\<beta>\<close>-normal term of a function type.\<close>

lemma eta_body:
  assumes "(e, \<tau>) \<turnstile> s : A \<Rightarrow> B" "no_redex s" "no_loose_bound s n"
  obtains s' where "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> s' : B" "no_redex s'" "no_loose_bound s' (Suc n)"
    "dB.Abs s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" "lsize (e\<langle>0:A\<rangle>) \<tau> s' B = lsize e \<tau> s (A \<Rightarrow> B)"
proof (cases "\<exists>s1. s = dB.Abs s1")
  case True
  then obtain s1 where s: "s = dB.Abs s1" by blast
  from assms(1) s have "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> s1 : B" by auto
  moreover have "no_redex s1" "no_loose_bound s1 (Suc n)" using assms(2,3) s by simp_all
  ultimately show ?thesis using that[of s1] s by simp
next
  case False
  let ?s' = "lift s 0 \<degree> BVar 0"
  have nA: "\<not> Unif_Occurs.is_Abs s" using False by (cases s) auto
  have "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> lift s 0 : A \<Rightarrow> B" by (rule lift_type[OF assms(1)])
  then have ty: "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> ?s' : B" by (rule typing.App) (simp add: typing.BVar)
  have nr: "no_redex ?s'" using nA assms(2) by (simp add: lift_is_Abs no_redex_lift)
  have nl: "no_loose_bound ?s' (Suc n)" using no_loose_bound_lift[OF assms(3)] by simp
  have tyA: "(e, \<tau>) \<turnstile> dB.Abs ?s' : A \<Rightarrow> B" using ty by (rule typing.Abs)
  have "lsize e \<tau> s (A \<Rightarrow> B) = lsize e \<tau> (dB.Abs ?s') (A \<Rightarrow> B)"
    using lsize_eta[OF eta_Abs_lift tyA] nr by simp
  then have "lsize (e\<langle>0:A\<rangle>) \<tau> ?s' B = lsize e \<tau> s (A \<Rightarrow> B)" by simp
  with that[OF ty nr nl eta_lift_equiv] show ?thesis .
qed

lemma vps_incr_boundvars[simp]: "vps (incr_boundvars i t) = vps t"
  by (simp add: incr_boundvars_def vps_incr_bv)

lemma mc_complete_step:
  assumes IH: "\<And>V \<sigma> env dps rb targs Ts u U s. lsize (bctx Ts) \<tau>' s (trty U) < N \<Longrightarrow>
      mc_pre ar V \<tau>' \<sigma> env dps rb targs Ts u U s \<Longrightarrow> mc_post ar cfg vname V \<tau>' \<sigma> env dps rb targs Ts u U s"
  shows "mc_pre ar V \<tau>' \<sigma> env dps rb targs Ts u U s \<Longrightarrow> lsize (bctx Ts) \<tau>' s (trty U) = N \<Longrightarrow>
    mc_post ar cfg vname V \<tau>' \<sigma> env dps rb targs Ts u U s"
proof (induction "size u" arbitrary: rb targs Ts u U s rule: less_induct)
  case less
  from less.prems(1) have inv: "cinv ar V \<tau>' \<sigma> env dps" and bok: "binders_ok ar rb"
    and tg: "\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t"
    and tgty: "list_all2 (has_type V (map snd rb)) targs Ts"
    and wu: "wf_tm ar rb u" and hu: "hnf u" and hl: "hlong V (map snd rb) u U" and bu: "below (maxidx env) u"
    and tys: "(bctx Ts, \<tau>') \<turnstile> s : trty U" and nrs: "no_redex s" and nls: "no_loose_bound s (length Ts)"
    and eqs: "Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    unfolding mc_pre_def by blast+
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  have tyu: "has_type V (map snd rb) u U" by (rule hlong_typed[OF hl])
  from has_type_head_of[OF tyu] obtain T0 where tyh: "has_type V (map snd rb) (head_of u) T0" ..
  have mcu: "mc cfg vname rb targs u env dps =
    (case head_of u of
        Abs a T body \<Rightarrow> do {
          s \<leftarrow> mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps;
          returnW (S_MapAbs a T s)}
      | Var w _ \<Rightarrow>
          (let (env', newhd) = genvar (fst w) env (foldr fun_type Ts (res_type T0)) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u) # dps))))
      | _ \<Rightarrow> do {
          projs \<leftarrow> make_projs u targs Ts targs;
          matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) (res_type T0) Ts (rev projs)})"
    by (rule mc_unfold[OF e fastype_typed[OF e tyh] mapM_fastype[OF e tgty]])
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF tgty] by simp
  have gTs: "ground ar T" if "T \<in> set Ts" for T
  proof -
    from that obtain i where i: "i < length Ts" "T = Ts ! i" by (auto simp: in_set_conv_nth)
    with tgty have "has_type V (map snd rb) (targs ! i) T" by (simp add: list_all2_conv_all_nth)
    moreover have "wf_tm ar rb (targs ! i)" using tg i lTs by simp
    ultimately show ?thesis using ground_has_type[OF e bok] by blast
  qed
  have gU: "ground ar U" by (rule ground_has_type[OF e bok wu tyu])
  have rigid: "mc_post ar cfg vname V \<tau>' \<sigma> env dps rb targs Ts u U s"
    if hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
  proof -
    have nA: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
    have nfU: "\<not> is_funT U" using hl nA by (cases rule: hlong.cases) auto
    have rT0: "res_type T0 = U" using res_type_head(1)[OF tyu nfU tyh] .
    define uargs where "uargs = snd (strip_comb u)"
    from res_type_head(2)[OF tyu nfU tyh] obtain As where T0: "T0 = foldr fun_type As U"
      and tyargs: "list_all2 (has_type V (map snd rb)) uargs As" by (auto simp: uargs_def)
    have u_eq: "u = list_comb (head_of u) uargs" unfolding uargs_def by (rule head_of_list_comb)
    have kk: "(if is_Var (head_of (strip_abs_body u)) then 0 else 1) = (1::nat)"
      using hV nA by (simp add: strip_abs_body_nonAbs)
    from make_projs_exact[OF lTs, of u targs] obtain projs where pr: "make_projs u targs Ts targs = returnW projs"
      and prs: "\<forall>j<length targs. (Bound (integer_of_nat j), Ts ! (length targs - Suc j),
        targs ! (length targs - Suc j)) \<in> set projs"
      by blast
    have gp: "\<forall>(bv, T, targ)\<in>set (rev projs). ground ar T"
      using make_projs_ok[of u targs Ts targs projs] pr gTs by fastforce
    have gb: "ground ar (res_type T0)" using rT0 gU by simp
    from matchfun_result[OF e gb gp, where cfg = cfg and vname = vname and rb = rb and targs = targs and u = u
        and dps = dps and uhead = "head_of u" and uargs = uargs and Ts = Ts] obtain sq where
      mf: "okW (matchfun cfg vname rb targs u env dps (head_of u) uargs (res_type T0) Ts (rev projs)) sq"
      and imit: "\<And>x. ev cfg (case head_of u of
          Const _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs)
        | Free _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs)
        | _ \<Rightarrow> S_Empty) x \<Longrightarrow> ev cfg sq x"
      and prj: "\<And>bv T targ env' args env2 fr ff. (bv, T, targ) \<in> set (rev projs) \<Longrightarrow> res_type T = res_type T0 \<Longrightarrow>
        make_args vname Ts env (arg_types T) = (env', args) \<Longrightarrow>
        okW (SIMPL (cfg_alg cfg) env'
          ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<Longrightarrow>
        ev cfg sq (El_C (list_comb bv args) env2 (fr @ ff))"
      by blast
    have mc: "okW (mc cfg vname rb targs u env dps) sq"
      using mcu pr mf hA hV by (cases "head_of u") (simp_all add: uargs_def)
    have sA: "\<not> Unif_Occurs.is_Abs s"
    proof
      assume "Unif_Occurs.is_Abs s"
      then obtain s1 where "s = dB.Abs s1" by (cases s) auto
      with tys have "\<exists>A B. trty U = A \<Rightarrow> B" by auto
      with trty_base[OF nfU] show False by auto
    qed
    obtain h ss where h: "is_atom h" "s = h \<degree>\<degree> ss" by (rule no_redex_atom_head[OF nrs sA])
    from tys h(2) obtain Ws where tyh': "(bctx Ts, \<tau>') \<turnstile> h : Ws \<Rrightarrow> trty U"
      and tyss: "(bctx Ts, \<tau>') \<tturnstile> ss : Ws"
      by (auto elim: list_app_typeE)
    have nrss: "\<forall>w\<in>set ss. no_redex w" using nrs h no_redex_atom_apps by simp
    have nlh: "no_loose_bound h (length Ts)" and nlss: "\<forall>w\<in>set ss. no_loose_bound w (length Ts)"
      using nls h(2) by (simp_all add: no_loose_bound_list_app)
    have lWs: "length Ws = length ss" by (rule typings_length[OF tyss])
    have lsz_s: "lsize (bctx Ts) \<tau>' s (trty U) =
        Suc (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (Ws ! i)) + (tsize (trty U) - 1)"
      using lsize_atom_apps[OF h(1) tyh' tyss nrss] h(2) by simp
    define D where "D = vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
    show ?thesis
    proof (cases "\<exists>j. h = BVar j")
      case True
      then obtain j where hj: "h = BVar j" by blast
      have jn: "j < length Ts" using nlh hj by simp
      define T where "T = Ts ! (length targs - Suc j)"
      define targ where "targ = targs ! (length targs - Suc j)"
      have tgtj: "length targs - Suc j < length targs" using jn lTs by simp
      have inp: "(Bound (integer_of_nat j), T, targ) \<in> set (rev projs)"
        using prs jn lTs by (simp add: T_def targ_def)
      have gT: "ground ar T" using gTs jn lTs by (simp add: T_def)
      have bT: "bctx Ts j = trty T" using jn lTs by (simp add: env_ext_map T_def)
      from tyh' hj bT have tT: "trty T = Ws \<Rrightarrow> trty U" by auto
      have "trty T = map trty (arg_types T) \<Rrightarrow> trty (res_type T)" by (metis arg_res_type trty_foldr)
      with tT arrows_base_inj[OF _ res_type_base nfU, of "map trty (arg_types T)" T Ws]
      have Ws: "Ws = map trty (arg_types T)" and rT: "res_type T = U" by auto
      define Us where "Us = arg_types T"
      have lUs: "length Us = length ss" using lWs Ws by (simp add: Us_def)
      have T_eq: "T = foldr fun_type Us U" using arg_res_type[of T] rT by (simp add: Us_def)
      have gUs: "\<forall>A\<in>set Us. ground ar A"
        using strip_type_ground(1)[OF e gT, of Us "res_type T"] by (simp add: strip_type_arg_res[OF e] Us_def)
      obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by (cases "make_args vname Ts env Us")
      define ws where "ws = map (Abs_m (length Ts)) ss"
      have lw: "length ws = length Us" using lUs by (simp add: ws_def)
      have tyssi: "(bctx Ts, \<tau>') \<turnstile> ss ! i : trty (Us ! i)" if "i < length Us" for i
        using typings_nth[OF tyss, of i] that lUs Ws by (simp add: Us_def)
      have wsi: "no_loose_bound (ws ! i) 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> ws ! i : trty (foldr fun_type Ts (Us ! i)))"
        if i: "i < length Us" for i
      proof -
        have nl: "no_loose_bound (ws ! i) 0" using nlss i lUs by (simp add: ws_def loose_bound_Abs_m)
        have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> ws ! i : map trty Ts \<Rrightarrow> trty (Us ! i)"
          using typing_Abs_m[OF tyssi[OF i]] i lUs by (simp add: ws_def)
        then have "(e, \<tau>') \<turnstile> ws ! i : trty (foldr fun_type Ts (Us ! i))" for e
          using typing_closed[OF _ nl] by (simp add: trty_foldr)
        with nl show ?thesis by blast
      qed
      obtain V1 \<sigma>1 xs where me: "cinv ar V1 \<tau>' \<sigma>1 env' dps" "agree (maxidx env) \<sigma> \<sigma>1"
        "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env'" "extends env' env" "length xs = length Us"
        "distinct xs" "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env'"
        "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
        "\<forall>i<length Us. \<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
        by (rule make_args_extend[OF inv ma lw wsi])
      have me10: "\<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
        if "i < length Us" for i using me(10) that by blast
      have la: "length args = length Us" using me(6,9) by simp
      have ai: "args ! i = combound (Var (xs ! i) (foldr fun_type Ts (Us ! i))) 0 (length Ts)"
        if "i < length Us" for i
        using me(6,9) that by simp
      have hai: "head_of (args ! i) = Var (xs ! i) (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
        using ai[OF that] by (simp add: head_of_combound)
      define Ls where "Ls = map (\<lambda>arg. list_comb (head_of arg) targs) args"
      define dp where "dp = (rb, list_comb targ Ls, u)"
      have tyt: "has_type V (map snd rb) targ T"
        using tgty tgtj lTs by (simp add: list_all2_conv_all_nth targ_def T_def)
      have wtg: "wf_tm ar rb targ" "below (maxidx env) targ" using tg tgtj by (simp_all add: targ_def)
      have tg1: "list_all2 (has_type V1 (map snd rb)) targs Ts"
        using list_all2_has_type_agreeV[OF tgty _ me(3)] tg by blast
      have tyt1: "has_type V1 (map snd rb) targ T" using has_type_agreeV[OF tyt wtg(2) me(3)] .
      have tyGi: "has_type V1 Bs (Var (xs ! i) (foldr fun_type Ts (Us ! i))) (foldr fun_type Ts (Us ! i))"
        if "i < length Us" for i Bs
        using me10[OF that] by (simp add: has_type.Var)
      have tyli: "list_all2 (has_type V1 (map snd rb)) Ls Us"
        unfolding list_all2_conv_all_nth Ls_def using la tyGi tg1 hai by (auto simp: has_type_list_comb)
      have tylhs: "has_type V1 (map snd rb) (list_comb targ Ls) U"
        using tyt1 tyli T_eq by (auto simp: has_type_list_comb)
      have tyu1: "has_type V1 (map snd rb) u U" using has_type_agreeV[OF tyu bu me(3)] .
      let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
      have ta1: "mk_subst \<sigma>1 (tr t) = mk_subst \<sigma> (tr t)" if "t \<in> set targs" for t
        using mk_subst_agree[OF _ me(2)] tg that by blast
      have Lsem: "map (\<lambda>t. mk_subst \<sigma>1 (tr t)) Ls = map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
      proof (rule nth_equalityI)
        show "length (map (\<lambda>t. mk_subst \<sigma>1 (tr t)) Ls) = length (map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss)"
          using la lUs by (simp add: Ls_def)
        fix i assume "i < length (map (\<lambda>t. mk_subst \<sigma>1 (tr t)) Ls)"
        then have i: "i < length Us" using la by (simp add: Ls_def)
        have "map (\<lambda>t. mk_subst \<sigma>1 (tr t)) targs = ?st" using ta1 by simp
        then show "map (\<lambda>t. mk_subst \<sigma>1 (tr t)) Ls ! i = map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss ! i"
          using hai[OF i] me10[OF i] i la lUs
          by (simp add: Ls_def tr_list_comb ws_def comp_def del: map_eq_conv)
      qed
      have stj: "rev ?st ! j = mk_subst \<sigma> (tr targ)" using jn lTs by (simp add: rev_nth targ_def)
      have e1: "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr targ) \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
        using Abs_m_apps_BVar_head[of ?st "length Ts" j ss] lTs jn stj h(2) hj by simp
      have "mk_subst \<sigma>1 (tr (list_comb targ Ls)) = mk_subst \<sigma> (tr targ) \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
        using Lsem mk_subst_agree[OF wtg(2) me(2)] by (simp add: tr_list_comb comp_def del: map_eq_conv)
      moreover have "mk_subst \<sigma>1 (tr u) = mk_subst \<sigma> (tr u)" by (rule mk_subst_agree[OF bu me(2)])
      ultimately have dsol: "dsolved \<sigma>1 dp"
        unfolding dp_def dsolved_dsolvedB dsolvedB_unabs using equiv_trans[OF equiv_sym[OF e1] eqs] by simp
      have gGi: "ground ar (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
        using ground_foldr_fun_type[of Ts ar "Us ! i"] gTs gUs that by auto
      have bGi: "maxidx env < snd (xs ! i)" "snd (xs ! i) \<le> maxidx env'" if "i < length Us" for i
        using me(8) me(6) that by (auto dest: nth_mem)
      have Lsi: "Ls ! i = list_comb (Var (xs ! i) (foldr fun_type Ts (Us ! i))) targs" if "i < length Us" for i
        using hai[OF that] la that by (simp add: Ls_def)
      have lLs: "length Ls = length Us" using la by (simp add: Ls_def)
      have inv1: "cinv ar V1 \<tau>' \<sigma>1 env' (dp # dps)"
      proof (rule cinv_Cons[OF me(1)])
        have "wf_tm ar rb t \<and> below (maxidx env') t" if "t \<in> set Ls" for t
        proof -
          from that obtain i where i: "i < length Us" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
          then show ?thesis using Lsi[OF i(1)] gGi[OF i(1)] bGi(2)[OF i(1)] tg below_mono[OF _ me(4)]
            by (auto simp: wf_tm_def proper_list_comb typs_ok_list_comb tr_list_comb no_loose_bound_list_app
                below_list_comb)
        qed
        then show "wf_dp ar dp" "dp_below (maxidx env') dp"
          using bok wtg wu bu below_mono[OF _ me(4)]
          by (auto simp: dp_def wf_tm_list_comb below_list_comb dp_below_def)
        show "dp_typed V1 dp" using tylhs tyu1 by (auto simp: dp_def dp_typed_def)
      qed (rule dsol)
      from SIMPL_complete[OF inv1, of "cfg_alg cfg"] obtain st' where
        sp0: "okW (SIMPL (cfg_alg cfg) env' (dp # dps)) st'" and sr0: "simpl_res ar V1 \<tau>' \<sigma>1 (dp # dps) env' st'"
        by blast
      obtain env2 fr ff where st': "st' = (env2, fr, ff)" by (cases st')
      have sr: "cinv ar V1 \<tau>' \<sigma>1 env2 (fr @ ff)" "extends env2 env'" "maxidx env2 = maxidx env'"
        "\<And>X. reach env2 X \<subseteq> reach env' (X \<union> vps_dps (dp # dps))"
        "vps_dps (fr @ ff) \<subseteq> reach env' (vps_dps (dp # dps))"
        using sr0 unfolding st' simpl_res_def by auto
      have evp: "ev cfg sq (El_C (list_comb (Bound (integer_of_nat j)) args) env2 (fr @ ff))"
        using prj[OF inp _ _ sp0[unfolded st' dp_def Ls_def]] rT rT0 ma by (simp add: Us_def)
      define NV where "NV = set (map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us)"
      have "map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us =
          map (\<lambda>i. (xs ! i, foldr fun_type Ts (Us ! i))) [0..<length Us]"
        using me(6) by (intro nth_equalityI) auto
      then have NVi: "y \<in> NV \<longleftrightarrow> (\<exists>i<length Us. y = (xs ! i, foldr fun_type Ts (Us ! i)))" for y
        by (auto simp: NV_def)
      have NVb: "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'" if "y \<in> NV" for y
        using that NVi bGi by auto
      have vai: "vps (args ! i) = {(xs ! i, foldr fun_type Ts (Us ! i))}" if "i < length Us" for i
        using ai[OF that] by simp
      have vargs: "\<Union> (vps ` set args) = NV"
      proof
        show "\<Union> (vps ` set args) \<subseteq> NV" using vai la NVi by (force simp: in_set_conv_nth)
        show "NV \<subseteq> \<Union> (vps ` set args)"
        proof
          fix y assume "y \<in> NV"
          then obtain i where i: "i < length Us" "y = (xs ! i, foldr fun_type Ts (Us ! i))" using NVi by blast
          then have "y \<in> vps (args ! i)" using vai by simp
          with i(1) la show "y \<in> \<Union> (vps ` set args)" by (auto dest: nth_mem[of i args])
        qed
      qed
      have vLs: "\<Union> (vps ` set Ls) \<subseteq> NV \<union> \<Union> (vps ` set targs)"
      proof
        fix y assume "y \<in> \<Union> (vps ` set Ls)"
        then obtain i where i: "i < length Us" "y \<in> vps (Ls ! i)" using lLs by (auto simp: in_set_conv_nth)
        then show "y \<in> NV \<union> \<Union> (vps ` set targs)" using Lsi[OF i(1)] NVi by (auto simp: vps_list_comb)
      qed
      have tgD: "vps targ \<subseteq> D" using tgtj by (auto simp: D_def targ_def dest: nth_mem)
      have vdp: "vps_dps (dp # dps) \<subseteq> D \<union> NV"
        using vLs tgD by (auto simp: dp_def vps_dp_def vps_list_comb D_def)
      have rr: "reach env' = reach env" by (rule reach_tenv[OF make_args_props(1)[OF ma]])
      have nvr: "reach env NV = NV" using reach_new[OF ei(4)] NVb by blast
      have rDNV: "reach env (X \<union> D \<union> NV) = reach env (X \<union> D) \<union> NV" for X using nvr by (simp add: reach_Un)
      have sx: "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env2 (fr @ ff) D NV"
        unfolding sext_def
      proof (intro conjI allI ballI sr(1) me(2,3))
        show "maxidx env \<le> maxidx env2" using me(4) sr(3) by simp
        show "extends env2 env" using sr(2) me(5) by (rule extends_trans)
        show "finite NV" by (simp add: NV_def)
        show "maxidx env < snd (fst y)" if "y \<in> NV" for y using NVb that by blast
        show "snd (fst y) \<le> maxidx env2" if "y \<in> NV" for y using NVb that sr(3) by simp
        show "reach env2 X \<subseteq> reach env (X \<union> D) \<union> NV" for X
        proof -
          have "reach env2 X \<subseteq> reach env (X \<union> vps_dps (dp # dps))" using sr(4)[of X] rr by simp
          also have "\<dots> \<subseteq> reach env (X \<union> D \<union> NV)" using vdp by (intro reach_subset) blast
          finally show ?thesis using rDNV by simp
        qed
        show "vps_dps (fr @ ff) \<subseteq> reach env D \<union> NV"
        proof -
          have "vps_dps (fr @ ff) \<subseteq> reach env (vps_dps (dp # dps))" using sr(5) rr by simp
          also have "\<dots> \<subseteq> reach env ({} \<union> D \<union> NV)" using vdp by (intro reach_subset) blast
          finally show ?thesis using rDNV[of "{}"] by simp
        qed
      qed
      define u' where "u' = list_comb (Bound (integer_of_nat j)) args"
      have tyBj: "has_type V1 (rev Ts) (Bound (integer_of_nat j)) (foldr fun_type Us U)"
        using jn lTs T_eq by (simp add: has_type_Bound_iff rev_nth T_def integer_reps)
      have "has_type V1 (rev Ts) (args ! i) (Us ! i)" if "i < length Us" for i
        using has_type_combound0[of V1 Ts "[]" "Var (xs ! i) (foldr fun_type Ts (Us ! i))" "Us ! i"]
          tyGi[OF that] ai[OF that] by simp
      then have tyai: "list_all2 (has_type V1 (rev Ts)) args Us" using la by (simp add: list_all2_conv_all_nth)
      have tyu': "has_type V1 (rev Ts) u' U" using tyBj tyai by (auto simp: u'_def has_type_list_comb)
      have vu': "vps u' = NV" using vargs by (simp add: u'_def vps_list_comb)
      have nri: "no_redex (ss ! i)" "no_loose_bound (ss ! i) (length Ts)" if "i < length ss" for i
        using nrss nlss that by auto
      have cr: "copy_res ar V \<tau>' \<sigma> env D Ts U s 1 u' env2 (fr @ ff) V1 \<sigma>1 NV"
        unfolding copy_res_def
      proof (intro conjI sx tyu')
        have "typs_ok ar a" if "a \<in> set args" for a
          using that la ai gGi by (auto simp: in_set_conv_nth typs_ok_combound)
        then show "wf_cp ar (length Ts) u'"
          unfolding wf_cp_def using has_type_proper[OF tyu'] has_type_closed[OF tyu']
          by (auto simp: u'_def typs_ok_list_comb)
        show "below (maxidx env2) u'" using vu' NVb sr(3) by (auto simp: below_vps_iff)
        show "vps u' \<subseteq> NV" using vu' by simp
        have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args) ss"
          unfolding list_all2_conv_all_nth
        proof (intro conjI allI impI)
          show "length (map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args) = length ss" using la lUs by simp
          fix i assume "i < length (map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args)"
          then have i: "i < length Us" using la by simp
          have "mk_subst \<sigma>1 (tr (args ! i)) = Abs_m (length Ts) (ss ! i) \<degree>\<degree> map BVar (downs (length Ts))"
            using ai[OF i] me10[OF i] i lUs by (simp add: tr_combound0 ws_def)
          then show "map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args ! i \<equiv>\<^sub>\<beta>\<^sub>\<eta> ss ! i"
            using Abs_m_apps_downs[OF nri(2)] i lUs la by simp
        qed
        then have "BVar j \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar j \<degree>\<degree> ss"
          by (rule equiv_list_app[OF equiv_refl])
        then show "mk_subst \<sigma>1 (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" using h(2) hj by (simp add: u'_def tr_list_comb comp_def integer_reps)
        let ?L = "map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us"
        have "map fst ?L = xs" using me(6) by (simp add: map_zip_map2 zip_map2 map_map comp_def split_def)
        then have dL: "distinct ?L" using me(7) by (metis distinct_map)
        have "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) = sum_list (map (vsz \<tau>' \<sigma>1) ?L)"
          using sum.distinct_set_conv_list[OF dL] by (simp add: NV_def)
        also have "\<dots> = (\<Sum>i<length Us. vsz \<tau>' \<sigma>1 (xs ! i, foldr fun_type Ts (Us ! i)))"
          using me(6) by (simp add: sum_list_sum_nth atLeast0LessThan)
        also have "\<dots> = (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (Ws ! i))"
        proof (rule sum.cong)
          show "{..<length Us} = {..<length ss}" using lUs by simp
          fix i assume "i \<in> {..<length ss}"
          then have i: "i < length Us" using lUs by simp
          have "\<sigma>1 (code (AVar (xs ! i))) = Abs_m (length Ts) (ss ! i)" using me10[OF i] i lUs by (simp add: ws_def)
          from vsz_Abs_m[where Ts = Ts and \<sigma> = \<sigma>1 and x = "xs ! i", OF this tyssi[OF i] nri[OF i[unfolded lUs]]]
          show "vsz \<tau>' \<sigma>1 (xs ! i, foldr fun_type Ts (Us ! i)) = lsize (bctx Ts) \<tau>' (ss ! i) (Ws ! i)"
            using Ws i lUs by (simp add: Us_def)
        qed
        finally show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) + 1 \<le> lsize (bctx Ts) \<tau>' s (trty U)" using lsz_s by simp
      qed
      with kk have "copy_res ar V \<tau>' \<sigma> env D Ts U s (if is_Var (head_of (strip_abs_body u)) then 0 else 1)
          u' env2 (fr @ ff) V1 \<sigma>1 NV" by simp
      then show ?thesis unfolding mc_post_def D_def u'_def using mc evp by blast
    next
      case False
      with h(1) obtain c where hc: "h = dB.Var c" by (auto simp: is_atom_def)
      have hd: "(\<exists>a T. head_of u = Const a T) \<or> (\<exists>a T. head_of u = Free a T) \<or> (\<exists>i. head_of u = Bound i)"
        using hA hV head_of_not_App[of u] by (cases "head_of u") auto
      have trh: "mk_subst \<sigma> (tr (head_of u)) = tr (head_of u)" and ath: "is_atom (tr (head_of u))"
        using hd rigid_substD[OF \<sigma>(3)] by auto
      have equ: "mk_subst \<sigma> (tr u) = tr (head_of u) \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) uargs"
        using arg_cong[OF u_eq, of "\<lambda>t. mk_subst \<sigma> (tr t)"] trh by (simp add: tr_list_comb comp_def)
      let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
      have e2: "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
        using Abs_m_apps_closed_head[of h ?st "length Ts" ss] hc h(2) lTs by simp
      have "h \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          tr (head_of u) \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) uargs"
        using equiv_trans[OF equiv_sym[OF e2] eqs] equ by simp
      from atom_apps_equiv[OF h(1) ath this] have hh: "h = tr (head_of u)"
        and la2: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss)
          (map (\<lambda>t. mk_subst \<sigma> (tr t)) uargs)"
        by auto
      from hd hh hc obtain a Tc where hu': "head_of u = Const a Tc \<or> head_of u = Free a Tc" by auto
      have Tc: "Tc = T0" using tyh hu' by (auto elim: has_type_elims)
      have tyhc: "(bctx Ts, \<tau>') \<turnstile> h : trty T0"
        using solution_rigid_type[OF cinvD(2)[OF inv] hu'] hh Tc by simp
      from tyhc tyh' hc have "Ws \<Rrightarrow> trty U = map trty As \<Rrightarrow> trty U" by (auto simp: T0 trty_foldr)
      with arrows_base_inj[OF _ nfU nfU] have Ws: "Ws = map trty As" by blast
      have lAs: "length As = length uargs" using list_all2_lengthD[OF tyargs] by simp
      have lss: "length ss = length uargs" using lWs Ws lAs by simp
      have MC: "mc_post ar cfg vname V0 \<tau>' \<sigma>0 env0 dps0 rb targs Ts u0 A s0"
        if "(A, s0) \<in> set (zip As ss)" "mc_pre ar V0 \<tau>' \<sigma>0 env0 dps0 rb targs Ts u0 A s0"
        for V0 \<sigma>0 env0 dps0 u0 A s0
      proof (rule IH[OF _ that(2)])
        from that(1) obtain i where i: "i < length ss" "A = As ! i" "s0 = ss ! i"
          using lAs lss by (auto simp: in_set_zip)
        have "lsize (bctx Ts) \<tau>' (ss ! i) (Ws ! i) \<le> (\<Sum>k<length ss. lsize (bctx Ts) \<tau>' (ss ! k) (Ws ! k))"
          by (rule member_le_sum) (use i in auto)
        then show "lsize (bctx Ts) \<tau>' s0 (trty A) < N" using lsz_s less.prems(2) i Ws lAs lss by simp
      qed
      have whd: "wf_tm ar rb (head_of u)" and ua: "\<forall>t\<in>set uargs. wf_tm ar rb t \<and> below (maxidx env) t"
        using wu bu u_eq by (metis wf_tm_list_comb below_list_comb)+
      have ssc: "list_all2 (\<lambda>s A. (bctx Ts, \<tau>') \<turnstile> s : trty A \<and> no_redex s \<and> no_loose_bound s (length Ts)) ss As"
        unfolding list_all2_conv_all_nth using lss lAs typings_nth[OF tyss] Ws nrss nlss by auto
      have eqa: "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)) ss uargs"
        using la2 by (simp add: list_all2_map1 list_all2_map2)
      from copyargs_complete[OF MC inv bok tg tgty ua tyargs ssc eqa] obtain uargs' env' dps' V' \<sigma>' NV where
        evc: "ev cfg (copyargs vname rb targs env dps uargs) (El_D uargs' env' dps')"
        and sxc: "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' (\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) NV"
        and tyc: "list_all2 (has_type V' (rev Ts)) uargs' As"
        and wc: "\<forall>u'\<in>set uargs'. wf_cp ar (length Ts) u' \<and> below (maxidx env') u' \<and> vps u' \<subseteq> NV"
        and ec: "list_all2 (\<lambda>u' s. mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs' ss"
        and szc: "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) \<le> sum_list (map2 (\<lambda>s A. lsize (bctx Ts) \<tau>' s (trty A)) ss As)"
        by blast
      have "ev cfg (S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs))
          (El_C (list_comb (head_of u) uargs') env' dps')" by (rule ev.map_join[OF evc])
      then have evj: "ev cfg sq (El_C (list_comb (head_of u) uargs') env' dps')"
        using hu' imit by (elim disjE) auto
      have sx: "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV"
      proof (rule sext_mono[OF sxc])
        have "vps u = vps (head_of u) \<union> \<Union> (vps ` set uargs)" by (subst u_eq) (simp add: vps_list_comb)
        then show "\<Union> (vps ` set uargs) \<union> \<Union> (vps ` set targs) \<union> vps_dps dps \<subseteq> D" by (auto simp: D_def)
      qed
      define u' where "u' = list_comb (head_of u) uargs'"
      have tyhu: "has_type V' (rev Ts) (head_of u) (foldr fun_type As U)"
        using has_type_rigid_head[OF tyh hu'] T0 by simp
      have rs': "rigid_subst \<sigma>'" using solutionD(3)[OF cinvD(2)[OF sextD(1)[OF sx]]] .
      have trh': "mk_subst \<sigma>' (tr (head_of u)) = tr (head_of u)" using hu' rigid_substD[OF rs'] by auto
      have cr: "copy_res ar V \<tau>' \<sigma> env D Ts U s 1 u' env' dps' V' \<sigma>' NV"
        unfolding copy_res_def
      proof (intro conjI sx)
        show "has_type V' (rev Ts) u' U" using tyhu tyc by (auto simp: u'_def has_type_list_comb)
        show "wf_cp ar (length Ts) u'"
          using whd wc hu' by (auto simp: u'_def wf_cp_def wf_tm_def proper_list_comb typs_ok_list_comb tr_list_comb
              no_loose_bound_list_app)
        show "below (maxidx env') u'" using wc hu' by (auto simp: u'_def below_list_comb)
        show "vps u' \<subseteq> NV" using wc hu' by (auto simp: u'_def vps_list_comb)
        have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma>' (tr a)) uargs') ss"
          using ec by (simp add: list_all2_map1)
        from equiv_list_app[OF equiv_refl this]
        show "mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" using trh' hh h(2) by (simp add: u'_def tr_list_comb comp_def)
        have "sum_list (map2 (\<lambda>s A. lsize (bctx Ts) \<tau>' s (trty A)) ss As) =
            (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (Ws ! i))"
          using sum_list_map2_nth[of ss As "\<lambda>s A. lsize (bctx Ts) \<tau>' s (trty A)"] lss lAs Ws by simp
        with szc show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + 1 \<le> lsize (bctx Ts) \<tau>' s (trty U)" using lsz_s by simp
      qed
      with kk have "copy_res ar V \<tau>' \<sigma> env D Ts U s (if is_Var (head_of (strip_abs_body u)) then 0 else 1)
          u' env' dps' V' \<sigma>' NV" by simp
      then show ?thesis unfolding mc_post_def D_def u'_def using mc evj by blast
    qed
  qed
  show ?case
  proof (cases "head_of u")
    case (Abs a T body)
    have u: "u = Abs a T body" using hnf_Abs_head[OF hu] Abs by (simp add: fst_strip_comb)
    from hl u obtain U' where U: "U = T \<rightarrow>\<^sub>T U'" and hlb: "hlong V (T # map snd rb) body U'"
      by (auto elim: hlong.cases)
    have wb: "wf_tm ar ((a, T) # rb) body" and gT: "ground ar T" using wu u by (simp_all add: wf_tm_def)
    have bok': "binders_ok ar ((a, T) # rb)" using bok gT by (simp add: binders_ok_def)
    have hb: "hnf body" using hu u by simp
    have bb: "below (maxidx env) body" using bu u by simp
    define targs' where "targs' = map (incr_boundvars 1) targs @ [Bound 0]"
    have tg': "\<forall>t\<in>set targs'. wf_tm ar ((a, T) # rb) t \<and> below (maxidx env) t"
      using tg by (auto simp: targs'_def below_vps_iff intro: wf_tm_incr wf_tm_Bound0)
    have tgty': "list_all2 (has_type V (map snd ((a, T) # rb))) targs' (Ts @ [T])"
      unfolding targs'_def
    proof (rule list_all2_appendI)
      show "list_all2 (has_type V (map snd ((a, T) # rb))) (map (incr_boundvars 1) targs) Ts"
        using tgty by (simp add: list_all2_map1) (erule list_all2_mono, simp add: has_type_incr_boundvars1)
    qed (simp add: has_type_Bound_iff)
    have tys0: "(bctx Ts, \<tau>') \<turnstile> s : trty T \<Rightarrow> trty U'" using tys U by simp
    obtain s' where s': "((bctx Ts)\<langle>0:trty T\<rangle>, \<tau>') \<turnstile> s' : trty U'" "no_redex s'"
      "no_loose_bound s' (Suc (length Ts))" "dB.Abs s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
      "lsize ((bctx Ts)\<langle>0:trty T\<rangle>) \<tau>' s' (trty U') = lsize (bctx Ts) \<tau>' s (trty T \<Rightarrow> trty U')"
      by (rule eta_body[OF tys0 nrs nls])
    have bctx': "bctx (Ts @ [T]) = (bctx Ts)\<langle>0:trty T\<rangle>" by (simp add: env_ext_snoc)
    let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
    have st': "map (\<lambda>t. mk_subst \<sigma> (tr t)) targs' = map (\<lambda>t. lift t 0) ?st @ [BVar 0]"
    proof -
      have "mk_subst \<sigma> (tr (incr_boundvars 1 t)) = lift (mk_subst \<sigma> (tr t)) 0" if "t \<in> set targs" for t
      proof -
        have "proper t" using tg that by (simp add: wf_tm_def)
        then have "tr (incr_boundvars 1 t) = lift (tr t) 0" by (rule tr_incr_boundvars1)
        moreover have "closed_on (FV (tr t)) \<sigma>" using \<sigma>(1) by (simp add: closed_on_def)
        ultimately show ?thesis by (simp add: mk_subst_lift_on)
      qed
      then show ?thesis by (simp add: targs'_def)
    qed
    define F where "F = Abs_m (Suc (length Ts)) s'"
    have F0: "no_loose_bound F 0" using s'(3) by (simp add: F_def loose_bound_Abs_m)
    have "F \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length Ts) s" unfolding F_def Abs_m_Suc' by (rule equiv_Abs_m[OF s'(4)])
    then have "F \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
      using equiv_trans[OF equiv_list_app[OF _ list_all2_refl] eqs] by (simp add: equiv_refl)
    then have Fe: "F \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr body))" using u by simp
    have "dB.Abs ((F \<degree>\<degree> map (\<lambda>t. lift t 0) ?st) \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr body))"
      by (rule equiv_trans[OF Abs_apps_lift_eta[OF F0] Fe])
    then have eqb: "Abs_m (length (Ts @ [T])) s' \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs' \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr body)"
      using equiv_Abs_reflect st' by (simp add: F_def)
    have pre: "mc_pre ar V \<tau>' \<sigma> env dps ((a, T) # rb) targs' (Ts @ [T]) body U' s'"
      unfolding mc_pre_def bctx' using inv bok' tg' tgty' wb hb hlb bb s'(1-3) eqb by simp
    have lsz: "lsize (bctx (Ts @ [T])) \<tau>' s' (trty U') = N" unfolding bctx' using s'(5) less.prems(2) U by simp
    have "size body < size u" using u by simp
    from less.hyps[OF this pre lsz] obtain sq u' env' dps' V' \<sigma>' NV where
      mcb: "okW (mc cfg vname ((a, T) # rb) targs' body env dps) sq" and evb: "ev cfg sq (El_C u' env' dps')"
      and cr: "copy_res ar V \<tau>' \<sigma> env (vps body \<union> \<Union> (vps ` set targs') \<union> vps_dps dps) (Ts @ [T]) U' s'
          (if is_Var (head_of (strip_abs_body body)) then 0 else 1) u' env' dps' V' \<sigma>' NV"
      unfolding mc_post_def by blast
    have D: "vps body \<union> \<Union> (vps ` set targs') \<union> vps_dps dps = vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
      using u by (auto simp: targs'_def)
    have mc: "okW (mc cfg vname rb targs u env dps) (S_MapAbs a T sq)"
      using mcu Abs mcb by (simp add: targs'_def)
    have ev: "ev cfg (S_MapAbs a T sq) (El_C (Abs a T u') env' dps')" by (rule ev.map_abs[OF evb])
    from cr have cr': "copy_res ar V \<tau>' \<sigma> env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U s
        (if is_Var (head_of (strip_abs_body u)) then 0 else 1) (Abs a T u') env' dps' V' \<sigma>' NV"
      unfolding copy_res_def D
    proof (elim conjE, intro conjI)
      assume ty': "has_type V' (rev (Ts @ [T])) u' U'" and w': "wf_cp ar (length (Ts @ [T])) u'"
        and e': "mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s'"
        and sz: "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + (if is_Var (head_of (strip_abs_body body)) then 0 else 1)
          \<le> lsize (bctx (Ts @ [T])) \<tau>' s' (trty U')"
      show "has_type V' (rev Ts) (Abs a T u') U" using ty' U by (simp add: has_type.Abs)
      show "wf_cp ar (length Ts) (Abs a T u')" using w' gT by (simp add: wf_cp_def)
      show "mk_subst \<sigma>' (tr (Abs a T u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" using equiv_trans[OF equiv_Abs[OF e'] s'(4)] by simp
      show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + (if is_Var (head_of (strip_abs_body u)) then 0 else 1)
          \<le> lsize (bctx Ts) \<tau>' s (trty U)"
        using sz s'(5) U u unfolding bctx' by simp
    qed simp_all
    show ?thesis unfolding mc_post_def using mc ev cr' by blast
  next
    case (Var w W)
    have nA: "\<not> is_Abs u" using Var by (cases u) auto
    have nfU: "\<not> is_funT U" using hl nA by (cases rule: hlong.cases) auto
    have rT0: "res_type T0 = U" using res_type_head(1)[OF tyu nfU tyh] .
    define GT where "GT = foldr fun_type Ts U"
    have gGT: "ground ar GT" unfolding GT_def by (rule ground_foldr_fun_type) (use gTs gU in auto)
    obtain env1 newhd where g: "genvar (fst w) env GT = (env1, newhd)" by (cases "genvar (fst w) env GT")
    define G where "G = (fst w, maxidx env + 1)"
    define \<sigma>1 where "\<sigma>1 = \<sigma>(code (AVar G) := Abs_m (length Ts) s)"
    define V1 where "V1 = V(G := GT)"
    have w0: "no_loose_bound (Abs_m (length Ts) s) 0" using nls by (simp add: loose_bound_Abs_m)
    have wty: "(e, \<tau>') \<turnstile> Abs_m (length Ts) s : trty GT" for e
    proof -
      have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m (length Ts) s : map trty Ts \<Rrightarrow> trty U" using typing_Abs_m[OF tys] by simp
      from typing_closed[OF this w0] show ?thesis by (simp add: GT_def trty_foldr)
    qed
    note ge = genvar_extend[OF inv g w0 wty, folded G_def \<sigma>1_def V1_def]
    define dp where "dp = (rb, list_comb newhd targs, u)"
    have tg1: "list_all2 (has_type V1 (map snd rb)) targs Ts"
      using list_all2_has_type_agreeV[OF tgty _ ge(3)] tg by blast
    have tyu1: "has_type V1 (map snd rb) u U" using has_type_agreeV[OF tyu bu ge(3)] .
    have tyG: "has_type V1 Bs newhd GT" for Bs using ge(5,8) by (simp add: has_type.Var)
    have tyl: "has_type V1 (map snd rb) (list_comb newhd targs) U"
      using tyG tg1 by (auto simp: has_type_list_comb GT_def)
    have wG: "wf_tm ar rb newhd" using ge(5) gGT by (simp add: wf_tm_def)
    have bG: "below (maxidx env1) newhd" using ge(4,5) by (simp add: G_def)
    have ta1: "map (\<lambda>t. mk_subst \<sigma>1 (tr t)) targs = map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
      using mk_subst_list_agree[OF _ ge(2)] tg by blast
    have u1: "mk_subst \<sigma>1 (tr u) = mk_subst \<sigma> (tr u)" by (rule mk_subst_agree[OF bu ge(2)])
    have ds: "dsolved \<sigma>1 dp"
    proof -
      have "mk_subst \<sigma>1 (tr (list_comb newhd targs)) = Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
        using ge(5,7) ta1 by (simp add: tr_list_comb comp_def del: map_eq_conv)
      then show ?thesis unfolding dp_def dsolved_dsolvedB dsolvedB_unabs using eqs u1 by simp
    qed
    have inv1: "cinv ar V1 \<tau>' \<sigma>1 env1 (dp # dps)"
    proof (rule cinv_Cons[OF ge(1)])
      show "wf_dp ar dp" using bok wG tg wu by (simp add: dp_def wf_tm_list_comb)
      show "dp_typed V1 dp" using tyl tyu1 by (auto simp: dp_def dp_typed_def)
      show "dp_below (maxidx env1) dp"
        using bG tg bu below_mono[OF _ ge(4)[THEN eq_refl]] ge(4)
        by (auto simp: dp_def dp_below_def below_list_comb intro: below_mono)
    qed (rule ds)
    have mc: "okW (mc cfg vname rb targs u env dps) (S_Single (El_C (combound newhd 0 (length Ts)) env1 (dp # dps)))"
      using mcu Var g rT0 by (simp add: dp_def GT_def)
    define NV where "NV = {(G, GT)}"
    define D where "D = vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
    have rr: "reach env1 = reach env" by (rule reach_tenv[OF genvar_simps(1)[OF g]])
    have sx: "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env1 (dp # dps) D NV"
      unfolding sext_def
    proof (intro conjI allI ballI inv1 ge(2,3,6))
      show "maxidx env \<le> maxidx env1" using ge(4) by simp
      show "finite NV" by (simp add: NV_def)
      show "maxidx env < snd (fst y)" if "y \<in> NV" for y using that by (simp add: NV_def G_def)
      show "snd (fst y) \<le> maxidx env1" if "y \<in> NV" for y using that ge(4) by (simp add: NV_def G_def)
      show "reach env1 X \<subseteq> reach env (X \<union> D) \<union> NV" for X using reach_subset[of X "X \<union> D" env] rr by auto
      have "vps_dps (dp # dps) \<subseteq> D \<union> NV" using ge(5) by (auto simp: dp_def vps_dp_def vps_list_comb D_def NV_def)
      then show "vps_dps (dp # dps) \<subseteq> reach env D \<union> NV" using reach_incl[of D env] by blast
    qed
    have cr: "copy_res ar V \<tau>' \<sigma> env D Ts U s 0 (combound newhd 0 (length Ts)) env1 (dp # dps) V1 \<sigma>1 NV"
      unfolding copy_res_def
    proof (intro conjI sx)
      show "has_type V1 (rev Ts) (combound newhd 0 (length Ts)) U"
        using has_type_combound0[of V1 Ts "[]" newhd U] tyG by (simp add: GT_def)
      show "wf_cp ar (length Ts) (combound newhd 0 (length Ts))"
        by (rule wf_cp_combound) (use ge(5) gGT in simp_all)
      show "below (maxidx env1) (combound newhd 0 (length Ts))" using bG by (simp add: below_vps_iff)
      show "vps (combound newhd 0 (length Ts)) \<subseteq> NV" using ge(5) by (simp add: NV_def)
      show "mk_subst \<sigma>1 (tr (combound newhd 0 (length Ts))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
        using Abs_m_apps_downs[OF nls] ge(5,7) by (simp add: tr_combound0)
      show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) + 0 \<le> lsize (bctx Ts) \<tau>' s (trty U)"
        using vsz_Abs_m[where Ts = Ts and \<sigma> = \<sigma>1 and x = G, OF ge(7) tys nrs nls] by (simp add: NV_def GT_def)
    qed
    have k: "is_Var (head_of (strip_abs_body u))" using Var nA by (simp add: strip_abs_body_nonAbs)
    with cr have "copy_res ar V \<tau>' \<sigma> env D Ts U s (if is_Var (head_of (strip_abs_body u)) then 0 else 1)
        (combound newhd 0 (length Ts)) env1 (dp # dps) V1 \<sigma>1 NV" by simp
    then show ?thesis unfolding mc_post_def D_def using mc by (blast intro: ev.single)
  next
    case (Const c Tc)
    then show ?thesis using rigid by simp
  next
    case (Free c Tc)
    then show ?thesis using rigid by simp
  next
    case (Bound i)
    then show ?thesis using rigid by simp
  next
    case (App f x)
    then show ?thesis by (simp add: head_of_not_App)
  qed
qed

theorem mc_complete:
  "mc_pre ar V \<tau>' \<sigma> env dps rb targs Ts u U s \<Longrightarrow> mc_post ar cfg vname V \<tau>' \<sigma> env dps rb targs Ts u U s"
proof (induction "lsize (bctx Ts) \<tau>' s (trty U)" arbitrary: V \<sigma> env dps rb targs Ts u U s rule: less_induct)
  case less
  show ?case by (rule mc_complete_step[OF less.hyps less.prems refl])
qed


subsection \<open>The measure decreases\<close>

lemma mu_decrease:
  assumes fr: "fresh_env env" and Zb: "\<forall>y\<in>Z. snd (fst y) \<le> maxidx env" and fZ: "finite Z"
    and vZ: "(v, T) \<in> unb env Z" and ext: "extends env'' env" and vb: "lk env'' v T \<noteq> None"
    and rY: "reach env'' Y \<subseteq> reach env Z \<union> NV" and fNV: "finite NV"
    and ag: "agree (maxidx env) \<sigma> \<sigma>''" and sNV: "sum (vsz \<tau>' \<sigma>'') NV < vsz \<tau>' \<sigma> (v, T)"
  shows "sum (vsz \<tau>' \<sigma>'') (unb env'' Y) < sum (vsz \<tau>' \<sigma>) (unb env Z)"
proof -
  have sub: "unb env'' Y \<subseteq> (unb env Z - {(v, T)}) \<union> NV"
  proof
    fix y assume y: "y \<in> unb env'' Y"
    then have r: "y \<in> reach env Z \<union> NV" and l: "lk env'' (fst y) (snd y) = None"
      using rY by (auto simp: unb_def)
    have "lk env (fst y) (snd y) = None"
    proof (rule ccontr)
      assume "lk env (fst y) (snd y) \<noteq> None"
      then obtain u where "lk env (fst y) (snd y) = Some u" by blast
      from extends_lk[OF ext this] l show False by simp
    qed
    moreover have "y \<noteq> (v, T)" using l vb by auto
    ultimately show "y \<in> (unb env Z - {(v, T)}) \<union> NV" using r by (auto simp: unb_def)
  qed
  have fU: "finite (unb env Z)" by (rule finite_unb[OF fZ])
  have old: "snd (fst y) \<le> maxidx env" if "y \<in> unb env Z" for y
    using reach_old[OF fr Zb] that by (auto simp: unb_def)
  have "sum (vsz \<tau>' \<sigma>'') (unb env'' Y) \<le> sum (vsz \<tau>' \<sigma>'') ((unb env Z - {(v, T)}) \<union> NV)"
    by (rule sum_mono2[OF _ sub]) (use fU fNV in auto)
  also have "\<dots> \<le> sum (vsz \<tau>' \<sigma>'') (unb env Z - {(v, T)}) + sum (vsz \<tau>' \<sigma>'') NV"
    by (rule sum_Un_le) (use fU fNV in auto)
  also have "sum (vsz \<tau>' \<sigma>'') (unb env Z - {(v, T)}) = sum (vsz \<tau>' \<sigma>) (unb env Z - {(v, T)})"
    using sum_vsz_agree[OF ag] old by blast
  also have "sum (vsz \<tau>' \<sigma>) (unb env Z - {(v, T)}) + sum (vsz \<tau>' \<sigma>'') NV <
      sum (vsz \<tau>' \<sigma>) (unb env Z - {(v, T)}) + vsz \<tau>' \<sigma> (v, T)"
    using sNV by simp
  also have "\<dots> = sum (vsz \<tau>' \<sigma>) (unb env Z)"
    using sum.remove[OF fU vZ, of "vsz \<tau>' \<sigma>"] by simp
  finally show ?thesis .
qed

subsection \<open>Binding the variable of the pair\<close>

lemma has_type_types_abs: "has_type V (rev Ts @ Bs) u U \<Longrightarrow> has_type V Bs (types_abs Ts u) (foldr fun_type Ts U)"
  by (induction Ts arbitrary: Bs) (auto intro: has_type.Abs)

lemma vps_types_abs[simp]: "vps (types_abs Ts u) = vps u"
  by (induction Ts) simp_all

lemma below_types_abs[simp]: "below m (types_abs Ts u) \<longleftrightarrow> below m u"
  by (induction Ts) simp_all

text \<open>
  \<^const>\<open>new_dset\<close> on a copy \<open>u'\<close> of the body \<open>s\<close> of the value of \<open>v\<close>: the measure decreases if
  the new variables are smaller than the value of \<open>v\<close>.
\<close>

lemma new_dset_complete:
  assumes sx: "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV" and fr: "fresh_env env"
    and tyu': "has_type V' (rev Ts) u' U" and wc: "wf_cp ar (length Ts) u'"
    and bu': "below (maxidx env') u'" and vu': "vps u' \<subseteq> NV"
    and eq': "mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" and vs: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length Ts) s"
    and T: "T = foldr fun_type Ts U" and Vv: "V v = T" and gT: "ground ar T" and gTs: "\<forall>A\<in>set Ts. ground ar A"
    and vZ: "(v, T) \<in> unb env Z" and DZ: "D \<subseteq> Z" and Zb: "\<forall>y\<in>Z. snd (fst y) \<le> maxidx env"
    and fZ: "finite Z" and ac: "(v, T) \<notin> reach env' (vps u')"
    and sz: "sum (vsz \<tau>' \<sigma>') NV < vsz \<tau>' \<sigma> (v, T)"
  shows "\<exists>y. okW (new_dset (v, T) Ts u' env' dps') y \<and> (\<exists>env'' dps''. y = El_E env'' dps'' \<and>
    cinv ar V' \<tau>' \<sigma>' env'' dps'' \<and> extends env'' env' \<and> maxidx env'' = maxidx env' \<and>
    sum (vsz \<tau>' \<sigma>') (unb env'' (vps_dps dps'')) < sum (vsz \<tau>' \<sigma>) (unb env Z))"
proof -
  note sd = sextD[OF sx]
  note ei = env_invD[OF cinvD(1)[OF sd(1)]]
  note \<sigma>' = solutionD[OF cinvD(2)[OF sd(1)]]
  have e: "vt_is_empty (tyenv env')" by (rule wf_envD(1)[OF ei(2)])
  have vm: "snd v \<le> maxidx env" using reach_old[OF fr Zb, of "(v, T)"] vZ by (simp add: unb_def)
  have Vv': "V' v = T" using sd(2) vm Vv unfolding agreeV_def by blast
  have \<sigma>v: "\<sigma>' (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (types_abs Ts u'))"
    using agree_Var[OF sd(3) vm] vs equiv_Abs_m[OF equiv_sym[OF eq'], of "length Ts"]
    by (auto simp: tr_types_abs intro: equiv_trans)
  have tya: "has_type V' [] (types_abs Ts u') T" using has_type_types_abs[of V' Ts "[]" u' U] tyu' T by simp
  have wa: "wf_tm ar [] (types_abs Ts u')" by (rule wf_tm_types_abs[OF gTs wc])
  have NVr: "reach env NV = NV" using reach_new[OF fr] sd(7) by blast
  have vZr: "(v, T) \<in> reach env Z" using vZ by (simp add: unb_def)
  have RZ: "reach env' X \<subseteq> reach env Z \<union> NV" if "X \<subseteq> reach env Z \<union> NV" for X
  proof -
    have "X \<union> D \<subseteq> reach env Z \<union> NV" using that reach_subset[OF DZ, of env] reach_incl[of D env] by blast
    then have "reach env (X \<union> D) \<subseteq> reach env (reach env Z \<union> NV)" by (rule reach_subset)
    also have "\<dots> = reach env Z \<union> NV"
      using reach_mono[of "reach env Z" env Z] reach_incl[of "reach env Z" env] NVr by (auto simp: reach_Un)
    finally show ?thesis using sd(8)[of X] by blast
  qed
  have Yr: "vps_dps dps' \<subseteq> reach env Z \<union> NV" using sd(9) reach_subset[OF DZ, of env] by blast
  have fNV: "finite NV" by (rule sd(6))
  from lookup_typed[OF e ei(3) Vv'] obtain r where lr: "lookup env' v T = return r" by blast
  then have lk: "ok (lookup env' v T) r" by (simp add: return_def)
  from ok_lookup[OF e lk] show ?thesis
  proof (elim disjE exE conjE)
    assume r: "r = None" and vn: "vt_lookup (tenv env') v = None"
    from update_unbound_ok[OF vn, of T "types_abs Ts u'"] obtain env'' where
      upd: "update (v, T) (types_abs Ts u') env' = Some (Ok env'')" by blast
    have upd': "ok (update (v, T) (types_abs Ts u') env') env''" using upd by simp
    have ok: "okW (new_dset (v, T) Ts u' env' dps') (El_E env'' dps')"
      using lr r upd by (simp add: new_dset_def return_def)
    have vm': "snd v \<le> maxidx env'" using vm sd(4) by simp
    have ba: "below (maxidx env') (types_abs Ts u')" using bu' by simp
    note su = solution_update[OF cinvD(2)[OF sd(1)] ei(4) ei(3) upd' \<sigma>v Vv' tya vm' ba]
    have ac'': "acyc env''"
      unfolding acyc_def
      by (rule acyclic_update[OF dep_update[OF ok_update(2,1)[OF upd']]])
        (use ac ei(1) in \<open>simp_all add: acyc_def\<close>)
    have wf'': "wf_env ar env''"
      using ok_update_wf_env[OF upd' ei(2) _ _ gT] wa by (simp add: wf_tm_def)
    have inv'': "cinv ar V' \<tau>' \<sigma>' env'' dps'"
      using sd(1) su(1-3) ac'' wf'' by (simp add: cinv_def env_inv_def su(4))
    have ext: "extends env'' env'" by (rule ok_update_extends[OF upd'])
    have "sum (vsz \<tau>' \<sigma>') (unb env'' (vps_dps dps')) < sum (vsz \<tau>' \<sigma>) (unb env Z)"
    proof (rule mu_decrease[OF fr Zb fZ vZ extends_trans[OF ext sd(5)] _ _ fNV _ sz])
      show "lk env'' v T \<noteq> None" using ok_update_lookup[OF upd'] by (simp add: lk_def)
      have "reach env'' (vps_dps dps') \<subseteq> reach env' (vps_dps dps' \<union> vps u')"
        using Unify_Simpl_Complete.reach_update[OF upd'] by simp
      also have "\<dots> \<subseteq> reach env Z \<union> NV" by (rule RZ) (use Yr vu' in blast)
      finally show "reach env'' (vps_dps dps') \<subseteq> reach env Z \<union> NV" .
      show "agree (maxidx env) \<sigma> \<sigma>'" by (rule sd(3))
    qed
    then show ?thesis using ok inv'' ext su(4) by blast
  next
    fix s0 assume r: "r = Some s0" and vs0: "vt_lookup (tenv env') v = Some (T, s0)"
    let ?dp = "([], s0, types_abs Ts u')"
    have ok: "okW (new_dset (v, T) Ts u' env' dps') (El_E env' (?dp # dps'))"
      using lr r by (simp add: new_dset_def return_def)
    have ws0: "wf_tm ar [] s0" using wf_envD[OF ei(2)] vs0 by (auto simp: wf_env_def wf_tm_def)
    have ty0: "has_type V' [] s0 T" using env_typedD[OF ei(3) vs0] by simp
    have b0: "below (maxidx env') s0" using fresh_envD[OF ei(4) vs0] by simp
    have ds: "dsolved \<sigma>' ?dp"
      using equiv_trans[OF equiv_sym[OF satD[OF \<sigma>'(4) vs0]] \<sigma>v] by (simp add: dsolved_def)
    have inv'': "cinv ar V' \<tau>' \<sigma>' env' (?dp # dps')"
      using sd(1) ws0 wa ty0 tya b0 bu' ds by (auto simp: cinv_def binders_ok_def)
    have "sum (vsz \<tau>' \<sigma>') (unb env' (vps_dps (?dp # dps'))) < sum (vsz \<tau>' \<sigma>) (unb env Z)"
    proof (rule mu_decrease[OF fr Zb fZ vZ sd(5) _ _ fNV sd(3) sz])
      show "lk env' v T \<noteq> None" using vs0 by (simp add: lk_def)
      have "vps s0 \<subseteq> reach env' {(v, T)}" using reach_lk[of env' v T s0] reach_incl[of "vps s0" env'] vs0
        by (auto simp: lk_def)
      moreover have "reach env' {(v, T)} \<subseteq> reach env Z \<union> NV" using RZ vZr by blast
      ultimately have "vps_dps (?dp # dps') \<subseteq> reach env Z \<union> NV" using Yr vu' by auto
      then show "reach env' (vps_dps (?dp # dps')) \<subseteq> reach env Z \<union> NV" by (rule RZ)
    qed
    then show ?thesis using ok inv'' extends_refl by blast
  qed
qed

subsection \<open>Single steps of matching\<close>

text \<open>
  The term \<open>hd ?G\<^sub>1(\<dots>) \<dots> ?G\<^sub>m(\<dots>)\<close> built with \<^const>\<open>make_args\<close> is a copy of \<open>h ss\<close> if the new
  variables \<open>?G\<^sub>i\<close> are assigned the abstractions of \<open>ss\<close>.
\<close>

lemma make_args_copy:
  assumes inv: "cinv ar V \<tau>' \<sigma> env dps" and ma: "make_args vname Ts env Us = (env', args)"
    and gTs: "\<forall>A\<in>set Ts. ground ar A" and gUs: "\<forall>A\<in>set Us. ground ar A"
    and tyss: "(bctx Ts, \<tau>') \<tturnstile> ss : map trty Us"
    and nrss: "\<forall>w\<in>set ss. no_redex w" and nlss: "\<forall>w\<in>set ss. no_loose_bound w (length Ts)"
    and tyhd: "\<And>V'. has_type V' (rev Ts) hd0 (foldr fun_type Us U)" and vhd: "vps hd0 = {}"
    and thd: "typs_ok ar hd0" and htr: "\<And>\<sigma>'. rigid_subst \<sigma>' \<Longrightarrow> mk_subst \<sigma>' (tr hd0) = h"
    and dD: "vps_dps dps \<subseteq> D"
  obtains V1 \<sigma>1 NV where "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env' dps D NV"
    "has_type V1 (rev Ts) (list_comb hd0 args) U" "wf_cp ar (length Ts) (list_comb hd0 args)"
    "below (maxidx env') (list_comb hd0 args)" "vps (list_comb hd0 args) = NV"
    "mk_subst \<sigma>1 (tr (list_comb hd0 args)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
    "sum (vsz \<tau>' \<sigma>1) NV = (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (trty (Us ! i)))"
proof -
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  note ei = env_invD[OF cinvD(1)[OF inv]]
  have lUs: "length Us = length ss" using typings_length[OF tyss] by simp
  define ws where "ws = map (Abs_m (length Ts)) ss"
  have lw: "length ws = length Us" using lUs by (simp add: ws_def)
  have tyssi: "(bctx Ts, \<tau>') \<turnstile> ss ! i : trty (Us ! i)" if "i < length Us" for i
    using typings_nth[OF tyss, of i] that lUs by simp
  have nri: "no_redex (ss ! i)" "no_loose_bound (ss ! i) (length Ts)" if "i < length ss" for i
    using nrss nlss that by auto
  have wsi: "no_loose_bound (ws ! i) 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> ws ! i : trty (foldr fun_type Ts (Us ! i)))"
    if i: "i < length Us" for i
  proof -
    have nl: "no_loose_bound (ws ! i) 0" using nlss i lUs by (simp add: ws_def loose_bound_Abs_m)
    have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> ws ! i : map trty Ts \<Rrightarrow> trty (Us ! i)"
      using typing_Abs_m[OF tyssi[OF i]] i lUs by (simp add: ws_def)
    then have "(e, \<tau>') \<turnstile> ws ! i : trty (foldr fun_type Ts (Us ! i))" for e
      using typing_closed[OF _ nl] by (simp add: trty_foldr)
    with nl show ?thesis by blast
  qed
  obtain V1 \<sigma>1 xs where me: "cinv ar V1 \<tau>' \<sigma>1 env' dps" "agree (maxidx env) \<sigma> \<sigma>1"
    "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env'" "extends env' env" "length xs = length Us"
    "distinct xs" "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env'"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. \<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    by (rule make_args_extend[OF inv ma lw wsi])
  have me10: "\<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    if "i < length Us" for i using me(10) that by blast
  note \<sigma>1 = solutionD[OF cinvD(2)[OF me(1)]]
  have la: "length args = length Us" using me(6,9) by simp
  have ai: "args ! i = combound (Var (xs ! i) (foldr fun_type Ts (Us ! i))) 0 (length Ts)"
    if "i < length Us" for i
    using me(6,9) that by simp
  have gGi: "ground ar (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
    using ground_foldr_fun_type[of Ts ar "Us ! i"] gTs gUs that by auto
  have bGi: "maxidx env < snd (xs ! i)" "snd (xs ! i) \<le> maxidx env'" if "i < length Us" for i
    using me(8) me(6) that by (auto dest: nth_mem)
  have tyGi: "has_type V1 Bs (Var (xs ! i) (foldr fun_type Ts (Us ! i))) (foldr fun_type Ts (Us ! i))"
    if "i < length Us" for i Bs
    using me10[OF that] by (simp add: has_type.Var)
  define NV where "NV = set (map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us)"
  have "map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us =
      map (\<lambda>i. (xs ! i, foldr fun_type Ts (Us ! i))) [0..<length Us]"
    using me(6) by (intro nth_equalityI) auto
  then have NVi: "y \<in> NV \<longleftrightarrow> (\<exists>i<length Us. y = (xs ! i, foldr fun_type Ts (Us ! i)))" for y
    by (auto simp: NV_def)
  have NVb: "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'" if "y \<in> NV" for y
    using that NVi bGi by auto
  have vai: "vps (args ! i) = {(xs ! i, foldr fun_type Ts (Us ! i))}" if "i < length Us" for i
    using ai[OF that] by simp
  have vargs: "\<Union> (vps ` set args) = NV"
  proof
    show "\<Union> (vps ` set args) \<subseteq> NV" using vai la NVi by (force simp: in_set_conv_nth)
    show "NV \<subseteq> \<Union> (vps ` set args)"
    proof
      fix y assume "y \<in> NV"
      then obtain i where i: "i < length Us" "y = (xs ! i, foldr fun_type Ts (Us ! i))" using NVi by blast
      then have "y \<in> vps (args ! i)" using vai by simp
      with i(1) la show "y \<in> \<Union> (vps ` set args)" by (auto dest: nth_mem[of i args])
    qed
  qed
  define u' where "u' = list_comb hd0 args"
  have "has_type V1 (rev Ts) (args ! i) (Us ! i)" if "i < length Us" for i
    using has_type_combound0[of V1 Ts "[]" "Var (xs ! i) (foldr fun_type Ts (Us ! i))" "Us ! i"]
      tyGi[OF that] ai[OF that] by simp
  then have tyai: "list_all2 (has_type V1 (rev Ts)) args Us" using la by (simp add: list_all2_conv_all_nth)
  have tyu': "has_type V1 (rev Ts) u' U" using tyhd[of V1] tyai by (auto simp: u'_def has_type_list_comb)
  have vu': "vps u' = NV" using vargs vhd by (simp add: u'_def vps_list_comb)
  have rr: "reach env' = reach env" by (rule reach_tenv[OF make_args_props(1)[OF ma]])
  have sx: "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env' dps D NV"
    unfolding sext_def
  proof (intro conjI allI ballI me(1-5))
    show "finite NV" by (simp add: NV_def)
    show "maxidx env < snd (fst y)" "snd (fst y) \<le> maxidx env'" if "y \<in> NV" for y using NVb that by blast+
    show "reach env' X \<subseteq> reach env (X \<union> D) \<union> NV" for X
      using rr reach_subset[of X "X \<union> D" env] by auto
    show "vps_dps dps \<subseteq> reach env D \<union> NV" using dD reach_incl[of D env] by blast
  qed
  have wc: "wf_cp ar (length Ts) u'"
  proof -
    have "typs_ok ar a" if "a \<in> set args" for a
      using that la ai gGi by (auto simp: in_set_conv_nth typs_ok_combound)
    then show ?thesis
      unfolding wf_cp_def using has_type_proper[OF tyu'] has_type_closed[OF tyu'] thd
      by (auto simp: u'_def typs_ok_list_comb)
  qed
  have bu': "below (maxidx env') u'" using vu' NVb by (auto simp: below_vps_iff)
  have eq: "mk_subst \<sigma>1 (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
  proof -
    have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args) ss"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args) = length ss" using la lUs by simp
      fix i assume "i < length (map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args)"
      then have i: "i < length Us" using la by simp
      have "mk_subst \<sigma>1 (tr (args ! i)) = Abs_m (length Ts) (ss ! i) \<degree>\<degree> map BVar (downs (length Ts))"
        using ai[OF i] me10[OF i] i lUs by (simp add: tr_combound0 ws_def)
      then show "map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args ! i \<equiv>\<^sub>\<beta>\<^sub>\<eta> ss ! i"
        using Abs_m_apps_downs[OF nri(2)] i lUs la by simp
    qed
    then have "h \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma>1 (tr a)) args \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
      by (rule equiv_list_app[OF equiv_refl])
    then show ?thesis using htr[OF \<sigma>1(3)] by (simp add: u'_def tr_list_comb comp_def)
  qed
  have sz: "sum (vsz \<tau>' \<sigma>1) NV = (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (trty (Us ! i)))"
  proof -
    let ?L = "map2 (\<lambda>x A. (x, foldr fun_type Ts A)) xs Us"
    have "map fst ?L = xs" using me(6) by (simp add: map_zip_map2 zip_map2 map_map comp_def split_def)
    then have dL: "distinct ?L" using me(7) by (metis distinct_map)
    have "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) = sum_list (map (vsz \<tau>' \<sigma>1) ?L)"
      using sum.distinct_set_conv_list[OF dL] by (simp add: NV_def)
    also have "\<dots> = (\<Sum>i<length Us. vsz \<tau>' \<sigma>1 (xs ! i, foldr fun_type Ts (Us ! i)))"
      using me(6) by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (trty (Us ! i)))"
    proof (rule sum.cong)
      show "{..<length Us} = {..<length ss}" using lUs by simp
      fix i assume "i \<in> {..<length ss}"
      then have i: "i < length Us" using lUs by simp
      have "\<sigma>1 (code (AVar (xs ! i))) = Abs_m (length Ts) (ss ! i)" using me10[OF i] i lUs by (simp add: ws_def)
      from vsz_Abs_m[where Ts = Ts and \<sigma> = \<sigma>1 and x = "xs ! i", OF this tyssi[OF i] nri[OF i[unfolded lUs]]]
      show "vsz \<tau>' \<sigma>1 (xs ! i, foldr fun_type Ts (Us ! i)) = lsize (bctx Ts) \<tau>' (ss ! i) (trty (Us ! i))" .
    qed
    finally show ?thesis .
  qed
  show ?thesis by (rule that[OF sx tyu'[unfolded u'_def] wc[unfolded u'_def] bu'[unfolded u'_def]
    vu'[unfolded u'_def] eq[unfolded u'_def] sz])
qed

text \<open>The sequence of \<^const>\<open>match1_projs\<close> contains the elements of all type-correct projections.\<close>

lemma match1_projs_result:
  assumes "vt_is_empty (tyenv env)" "ground ar base" "\<forall>(bv, T, targ)\<in>set projs. ground ar T"
  shows "\<exists>sq. okW (match1_projs cfg vname env dps base Ts projs tail) sq \<and> (\<forall>x. ev cfg tail x \<longrightarrow> ev cfg sq x) \<and>
    (\<forall>bv T targ env' args. (bv, T, targ) \<in> set projs \<longrightarrow> res_type T = base \<longrightarrow>
      make_args vname Ts env (arg_types T) = (env', args) \<longrightarrow> ev cfg sq (El_C (list_comb bv args) env' dps))"
  using assms(3)
proof (induction projs)
  case Nil
  show ?case by (intro exI[of _ tail]) simp
next
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  from Cons obtain tl where tl: "okW (match1_projs cfg vname env dps base Ts projs tail) tl"
    and tail: "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg tl x"
    and prj: "\<forall>bv T targ env' args. (bv, T, targ) \<in> set projs \<longrightarrow> res_type T = base \<longrightarrow>
      make_args vname Ts env (arg_types T) = (env', args) \<longrightarrow> ev cfg tl (El_C (list_comb bv args) env' dps)"
    by auto
  have gT: "ground ar T" using Cons.prems p by simp
  have gb: "ground ar (res_type T)"
    using strip_type_ground(2)[OF assms(1) gT, of "arg_types T" "res_type T"]
    by (simp add: strip_type_arg_res[OF assms(1)])
  obtain env1 args1 where ma: "make_args vname Ts env (arg_types T) = (env1, args1)"
    by (cases "make_args vname Ts env (arg_types T)")
  let ?r = "if base = res_type T then S_Append (S_Single (El_C (list_comb bv args1) env1 dps)) tl else tl"
  let ?m = "(if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base (res_type T) env
    else cunify_types (cfg_alg cfg) base (res_type T) env)"
  let ?b = "do {env' \<leftarrow> ?m; (case make_args vname Ts env' (arg_types T) of (env'', args) \<Rightarrow>
    returnW (S_Append (S_Single (El_C (list_comb bv args) env'' dps)) tl))}"
  have h: "okW (handleW ?b (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tl | _ \<Rightarrow> raiseW e)) ?r"
  proof (cases "base = res_type T")
    case True
    then have "okW ?m env"
      by (auto simp: test_unify_types_def cunify_types_same okW_whenW)
    then have "okW ?b (S_Append (S_Single (El_C (list_comb bv args1) env1 dps)) tl)" using ma by auto
    then show ?thesis using True by (simp add: okW_handleW)
  next
    case False
    from cunify_types_ground_neq[OF assms(2) gb False] obtain evs
      where c: "cunify_types (cfg_alg cfg) base (res_type T) env = Some (evs, UErr CANTUNIFY)" by blast
    then have "\<exists>evs. ?m = Some (evs, UErr CANTUNIFY)"
      by (auto simp: test_unify_types_def bindW_def)
    then have "\<exists>evs. ?b = Some (evs, UErr CANTUNIFY)" by (auto simp: bindW_def)
    with False show ?thesis by (auto simp: okW_handleW)
  qed
  have "okW (match1_projs cfg vname env dps base Ts (p # projs) tail) ?r"
    using tl h by (auto simp: p strip_type_arg_res[OF assms(1)] foldrW_arity_guesses_ground[OF gb] match1_proj_0)
  moreover have "ev cfg ?r x" if "ev cfg tail x" for x using tail that by (auto intro: ev.append_r)
  moreover have "ev cfg ?r (El_C (list_comb bv' args) env' dps)"
    if "(bv', T', targ') \<in> set (p # projs)" "res_type T' = base"
      "make_args vname Ts env (arg_types T') = (env', args)"
    for bv' T' targ' env' args
  proof (cases "(bv', T', targ') = p")
    case True
    with that(2,3) p ma show ?thesis by (auto intro: ev.append_l ev.single)
  next
    case False
    with that have "(bv', T', targ') \<in> set projs" by simp
    with that(2,3) prj have "ev cfg tl (El_C (list_comb bv' args) env' dps)" by blast
    then show ?thesis by (auto intro: ev.append_r)
  qed
  ultimately show ?case by blast
qed

lemma match1_unfold:
  assumes "vt_is_empty (tyenv env)" "fastype env rb (head_of u) = return T0"
    "mapM (fastype env rb) targs = return Ts"
  shows "match1 cfg vname rb targs u env dps = do {
      projs \<leftarrow> make_projs u targs Ts targs;
      imit \<leftarrow>
        (case head_of u of
          Const _ _ \<Rightarrow>
            (case make_args vname Ts env (arg_types T0) of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb (head_of u) args) env' dps)))
        | Free _ _ \<Rightarrow>
            (case make_args vname Ts env (arg_types T0) of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb (head_of u) args) env' dps)))
        | _ \<Rightarrow> returnW S_Empty);
      match1_projs cfg vname env dps (res_type T0) Ts (rev projs) imit}"
  unfolding match1_def
  by (simp add: assms body_type_res binder_types_arg fst_strip_comb liftM_return Let_def
      split: pterm.split)

text \<open>
  Completeness of \<^const>\<open>match1\<close>: for a target \<open>s\<close> with a rigid head, the step that copies the
  head of \<open>s\<close> is among the elements; the pairs and the bindings are unchanged.
\<close>

lemma match1_complete:
  assumes pre: "mc_pre ar V \<tau>' \<sigma> env dps rb targs Ts u U s"
    and hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
  shows "\<exists>sq. okW (match1 cfg vname rb targs u env dps) sq \<and>
    (\<exists>u' env' V' \<sigma>' NV. ev cfg sq (El_C u' env' dps) \<and> tenv env' = tenv env \<and>
      copy_res ar V \<tau>' \<sigma> env (vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps) Ts U s 1 u' env' dps V' \<sigma>' NV)"
proof -
  from pre have inv: "cinv ar V \<tau>' \<sigma> env dps" and bok: "binders_ok ar rb"
    and tg: "\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t"
    and tgty: "list_all2 (has_type V (map snd rb)) targs Ts"
    and wu: "wf_tm ar rb u" and hl: "hlong V (map snd rb) u U" and bu: "below (maxidx env) u"
    and tys: "(bctx Ts, \<tau>') \<turnstile> s : trty U" and nrs: "no_redex s" and nls: "no_loose_bound s (length Ts)"
    and eqs: "Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    unfolding mc_pre_def by blast+
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  have tyu: "has_type V (map snd rb) u U" by (rule hlong_typed[OF hl])
  from has_type_head_of[OF tyu] obtain T0 where tyh: "has_type V (map snd rb) (head_of u) T0" ..
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF tgty] by simp
  have gTs: "\<forall>A\<in>set Ts. ground ar A"
  proof
    fix T assume "T \<in> set Ts"
    then obtain i where i: "i < length Ts" "T = Ts ! i" by (auto simp: in_set_conv_nth)
    with tgty have "has_type V (map snd rb) (targs ! i) T" by (simp add: list_all2_conv_all_nth)
    moreover have "wf_tm ar rb (targs ! i)" using tg i lTs by simp
    ultimately show "ground ar T" using ground_has_type[OF e bok] by blast
  qed
  have gU: "ground ar U" by (rule ground_has_type[OF e bok wu tyu])
  have nA: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
  have nfU: "\<not> is_funT U" using hl nA by (cases rule: hlong.cases) auto
  have rT0: "res_type T0 = U" using res_type_head(1)[OF tyu nfU tyh] .
  define uargs where "uargs = snd (strip_comb u)"
  from res_type_head(2)[OF tyu nfU tyh] obtain As where T0: "T0 = foldr fun_type As U"
    and tyargs: "list_all2 (has_type V (map snd rb)) uargs As" by (auto simp: uargs_def)
  have u_eq: "u = list_comb (head_of u) uargs" unfolding uargs_def by (rule head_of_list_comb)
  have aT0: "arg_types T0 = As" using arg_res_type_fun[OF nfU, of As] T0 by simp
  from make_projs_exact[OF lTs, of u targs] obtain projs where pr: "make_projs u targs Ts targs = returnW projs"
    and prs: "\<forall>j<length targs. (Bound (integer_of_nat j), Ts ! (length targs - Suc j),
      targs ! (length targs - Suc j)) \<in> set projs"
    by blast
  have gp: "\<forall>(bv, T, targ)\<in>set (rev projs). ground ar T"
    using make_projs_ok[of u targs Ts targs projs] pr gTs by fastforce
  have gb: "ground ar (res_type T0)" using rT0 gU by simp
  obtain env0 args0 where ma0: "make_args vname Ts env As = (env0, args0)"
    by (cases "make_args vname Ts env As")
  define imit where "imit = (case head_of u of
      Const _ _ \<Rightarrow> S_Single (El_C (list_comb (head_of u) args0) env0 dps)
    | Free _ _ \<Rightarrow> S_Single (El_C (list_comb (head_of u) args0) env0 dps)
    | _ \<Rightarrow> S_Empty)"
  have m1: "match1 cfg vname rb targs u env dps = match1_projs cfg vname env dps (res_type T0) Ts (rev projs) imit"
    using match1_unfold[OF e fastype_typed[OF e tyh] mapM_fastype[OF e tgty], of cfg vname dps] pr aT0 ma0
    by (cases "head_of u") (simp_all add: imit_def)
  from match1_projs_result[OF e gb gp, of cfg vname dps Ts imit] obtain sq where
    mp: "okW (match1_projs cfg vname env dps (res_type T0) Ts (rev projs) imit) sq"
    and imv: "\<And>x. ev cfg imit x \<Longrightarrow> ev cfg sq x"
    and prj: "\<And>bv T targ env' args. (bv, T, targ) \<in> set (rev projs) \<Longrightarrow> res_type T = res_type T0 \<Longrightarrow>
      make_args vname Ts env (arg_types T) = (env', args) \<Longrightarrow> ev cfg sq (El_C (list_comb bv args) env' dps)"
    by blast
  have sA: "\<not> Unif_Occurs.is_Abs s"
  proof
    assume "Unif_Occurs.is_Abs s"
    then obtain s1 where "s = dB.Abs s1" by (cases s) auto
    with tys have "\<exists>A B. trty U = A \<Rightarrow> B" by auto
    with trty_base[OF nfU] show False by auto
  qed
  obtain h ss where h: "is_atom h" "s = h \<degree>\<degree> ss" by (rule no_redex_atom_head[OF nrs sA])
  from tys h(2) obtain Ws where tyh': "(bctx Ts, \<tau>') \<turnstile> h : Ws \<Rrightarrow> trty U"
    and tyss: "(bctx Ts, \<tau>') \<tturnstile> ss : Ws"
    by (auto elim: list_app_typeE)
  have nrss: "\<forall>w\<in>set ss. no_redex w" using nrs h no_redex_atom_apps by simp
  have nlh: "no_loose_bound h (length Ts)" and nlss: "\<forall>w\<in>set ss. no_loose_bound w (length Ts)"
    using nls h(2) by (simp_all add: no_loose_bound_list_app)
  have lWs: "length Ws = length ss" by (rule typings_length[OF tyss])
  have lsz_s: "lsize (bctx Ts) \<tau>' s (trty U) =
      Suc (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (Ws ! i)) + (tsize (trty U) - 1)"
    using lsize_atom_apps[OF h(1) tyh' tyss nrss] h(2) by simp
  define D where "D = vps u \<union> \<Union> (vps ` set targs) \<union> vps_dps dps"
  text \<open>The head of the copy: a projection or the imitation.\<close>
  have "\<exists>hd0 Us env' args. make_args vname Ts env Us = (env', args) \<and>
      ev cfg sq (El_C (list_comb hd0 args) env' dps) \<and> Ws = map trty Us \<and> (\<forall>A\<in>set Us. ground ar A) \<and>
      (\<forall>V'. has_type V' (rev Ts) hd0 (foldr fun_type Us U)) \<and> vps hd0 = {} \<and> typs_ok ar hd0 \<and>
      (\<forall>\<sigma>'. rigid_subst \<sigma>' \<longrightarrow> mk_subst \<sigma>' (tr hd0) = h)"
  proof (cases "\<exists>j. h = BVar j")
    case True
    then obtain j where hj: "h = BVar j" by blast
    have jn: "j < length Ts" using nlh hj by simp
    define T where "T = Ts ! (length targs - Suc j)"
    define targ where "targ = targs ! (length targs - Suc j)"
    have inp: "(Bound (integer_of_nat j), T, targ) \<in> set (rev projs)"
      using prs jn lTs by (simp add: T_def targ_def)
    have gT: "ground ar T" using gTs jn lTs by (simp add: T_def)
    have bT: "bctx Ts j = trty T" using jn lTs by (simp add: env_ext_map T_def)
    from tyh' hj bT have tT: "trty T = Ws \<Rrightarrow> trty U" by auto
    have "trty T = map trty (arg_types T) \<Rrightarrow> trty (res_type T)" by (metis arg_res_type trty_foldr)
    with tT arrows_base_inj[OF _ res_type_base nfU, of "map trty (arg_types T)" T Ws]
    have Ws: "Ws = map trty (arg_types T)" and rT: "res_type T = U" by auto
    define Us where "Us = arg_types T"
    have T_eq: "T = foldr fun_type Us U" using arg_res_type[of T] rT by (simp add: Us_def)
    have gUs: "\<forall>A\<in>set Us. ground ar A"
      using strip_type_ground(1)[OF e gT, of Us "res_type T"] by (simp add: strip_type_arg_res[OF e] Us_def)
    obtain env' args where ma: "make_args vname Ts env Us = (env', args)"
      by (cases "make_args vname Ts env Us")
    have evp: "ev cfg sq (El_C (list_comb (Bound (integer_of_nat j)) args) env' dps)"
      using prj[OF inp _ ma[unfolded Us_def]] rT rT0 by simp
    have tyBj: "has_type V' (rev Ts) (Bound (integer_of_nat j)) (foldr fun_type Us U)" for V'
      using jn lTs T_eq by (simp add: has_type_Bound_iff rev_nth T_def integer_reps)
    have "mk_subst \<sigma>' (tr (Bound (integer_of_nat j))) = h" for \<sigma>' using hj by (simp add: integer_reps)
    then show ?thesis using ma evp Ws gUs tyBj unfolding Us_def[symmetric]
      by (intro exI[of _ "Bound (integer_of_nat j)"] exI[of _ Us] exI[of _ env'] exI[of _ args]) (simp add: hj)
  next
    case False
    with h(1) obtain c where hc: "h = dB.Var c" by (auto simp: is_atom_def)
    have hd: "(\<exists>a T. head_of u = Const a T) \<or> (\<exists>a T. head_of u = Free a T) \<or> (\<exists>i. head_of u = Bound i)"
      using hA hV head_of_not_App[of u] by (cases "head_of u") auto
    have trh: "mk_subst \<sigma> (tr (head_of u)) = tr (head_of u)" and ath: "is_atom (tr (head_of u))"
      using hd rigid_substD[OF \<sigma>(3)] by auto
    have equ: "mk_subst \<sigma> (tr u) = tr (head_of u) \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) uargs"
      using arg_cong[OF u_eq, of "\<lambda>t. mk_subst \<sigma> (tr t)"] trh by (simp add: tr_list_comb comp_def)
    let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
    have e2: "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
      using Abs_m_apps_closed_head[of h ?st "length Ts" ss] hc h(2) lTs by simp
    have "h \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr (head_of u) \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) uargs"
      using equiv_trans[OF equiv_sym[OF e2] eqs] equ by simp
    from atom_apps_equiv[OF h(1) ath this] have hh: "h = tr (head_of u)" by auto
    from hd hh hc obtain a Tc where hu': "head_of u = Const a Tc \<or> head_of u = Free a Tc" by auto
    have Tc: "Tc = T0" using tyh hu' by (auto elim: has_type_elims)
    have tyhc: "(bctx Ts, \<tau>') \<turnstile> h : trty T0"
      using solution_rigid_type[OF cinvD(2)[OF inv] hu'] hh Tc by simp
    from tyhc tyh' hc have "Ws \<Rrightarrow> trty U = map trty As \<Rrightarrow> trty U" by (auto simp: T0 trty_foldr)
    with arrows_base_inj[OF _ nfU nfU] have Ws: "Ws = map trty As" by blast
    have whd: "wf_tm ar rb (head_of u)" using wu u_eq by (metis wf_tm_list_comb)
    have gT0: "ground ar T0" by (rule ground_has_type[OF e bok whd tyh])
    then have gAs: "\<forall>A\<in>set As. ground ar A" unfolding T0 by (induction As) simp_all
    have tyhd: "has_type V' (rev Ts) (head_of u) (foldr fun_type As U)" for V'
      using has_type_rigid_head[OF tyh hu'] T0 by simp
    have "ev cfg imit (El_C (list_comb (head_of u) args0) env0 dps)"
      using hu' by (auto simp: imit_def intro: ev.single)
    then have evi: "ev cfg sq (El_C (list_comb (head_of u) args0) env0 dps)" by (rule imv)
    have "mk_subst \<sigma>' (tr (head_of u)) = h" if "rigid_subst \<sigma>'" for \<sigma>'
      using hu' rigid_substD[OF that] hh by auto
    moreover have "vps (head_of u) = {}" "typs_ok ar (head_of u)"
      using hu' whd by (auto simp: wf_tm_def)
    ultimately show ?thesis using ma0 evi Ws gAs tyhd
      by (intro exI[of _ "head_of u"] exI[of _ As] exI[of _ env0] exI[of _ args0]) simp
  qed
  then obtain hd0 Us env' args where ma: "make_args vname Ts env Us = (env', args)"
    and evx: "ev cfg sq (El_C (list_comb hd0 args) env' dps)" and Ws: "Ws = map trty Us"
    and gUs: "\<forall>A\<in>set Us. ground ar A" and tyhd: "\<And>V'. has_type V' (rev Ts) hd0 (foldr fun_type Us U)"
    and vhd: "vps hd0 = {}" and thd: "typs_ok ar hd0" and htr: "\<And>\<sigma>'. rigid_subst \<sigma>' \<Longrightarrow> mk_subst \<sigma>' (tr hd0) = h"
    by blast
  have dD: "vps_dps dps \<subseteq> D" by (auto simp: D_def)
  obtain V1 \<sigma>1 NV where c: "sext ar V \<tau>' \<sigma> env V1 \<sigma>1 env' dps D NV"
    "has_type V1 (rev Ts) (list_comb hd0 args) U" "wf_cp ar (length Ts) (list_comb hd0 args)"
    "below (maxidx env') (list_comb hd0 args)" "vps (list_comb hd0 args) = NV"
    "mk_subst \<sigma>1 (tr (list_comb hd0 args)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
    "sum (vsz \<tau>' \<sigma>1) NV = (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (trty (Us ! i)))"
    by (rule make_args_copy[OF inv ma gTs gUs tyss[unfolded Ws] nrss nlss tyhd vhd thd htr dD])
  have "(\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (trty (Us ! i))) =
      (\<Sum>i<length ss. lsize (bctx Ts) \<tau>' (ss ! i) (Ws ! i))"
    using lWs Ws by simp
  then have "copy_res ar V \<tau>' \<sigma> env D Ts U s 1 (list_comb hd0 args) env' dps V1 \<sigma>1 NV"
    using c h(2) lsz_s by (simp add: copy_res_def)
  moreover have "okW (match1 cfg vname rb targs u env dps) sq" using mp m1 by simp
  ultimately show ?thesis using evx make_args_props(1)[OF ma] unfolding D_def by blast
qed

subsection \<open>Completeness of \<open>MATCH\<close>\<close>

text \<open>
  The target of the variable \<open>v\<close> of a flex-rigid pair: the value \<open>\<sigma> v\<close> is \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. s\<close>
  modulo \<open>\<beta>\<eta>\<close> for a \<open>\<beta>\<close>-normal body \<open>s\<close> of the base type, whose size is the size of \<open>v\<close>.
\<close>

lemma value_target:
  assumes \<sigma>: "solution V \<tau>' \<sigma> env" and Vv: "V v = foldr fun_type Ts B"
  obtains s where "(bctx Ts, \<tau>') \<turnstile> s : trty B" "no_redex s" "no_loose_bound s (length Ts)"
    "Abs_m (length Ts) s \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))"
    "vsz \<tau>' \<sigma> (v, foldr fun_type Ts B) = lsize (bctx Ts) \<tau>' s (trty B)"
proof -
  note sd = solutionD[OF \<sigma>]
  let ?w = "\<sigma> (code (AVar v))"
  let ?n = "length Ts"
  have tyw: "(e, \<tau>') \<turnstile> ?w : map trty Ts \<Rrightarrow> trty B" for e
    using typed_onD[OF sd(2), of "code (AVar v)" e] Vv by (simp add: trty_foldr)
  have nlw: "no_loose_bound ?w 0" using closed_onD[OF sd(1)] by simp
  let ?r = "?w \<degree>\<degree> map BVar (downs ?n)"
  have "(bctx Ts, \<tau>') \<tturnstile> map BVar (downs ?n) : map trty Ts"
    using env_ext_downs[of "\<lambda>_. Atom 0" "map trty Ts"] by (simp add: typings_map_BVar)
  then have tyr: "(bctx Ts, \<tau>') \<turnstile> ?r : trty B" by (rule list_app_typeI[OF tyw])
  have nlr: "no_loose_bound ?r ?n"
    using no_loose_bound_mono[OF nlw] by (auto simp: no_loose_bound_list_app)
  from normal_form_ex[OF tyr] obtain s where s: "\<beta>\<eta>cl ?r s" "normal s" by blast
  have tys: "(bctx Ts, \<tau>') \<turnstile> s : trty B" by (rule subject_reduction_\<beta>\<eta>[OF s(1) tyr])
  have nrs: "no_redex s" by (rule normal_no_redex[OF s(2)])
  have nls: "no_loose_bound s ?n" by (rule \<beta>\<eta>cl_no_loose_bound[OF s(1) nlr])
  have eq: "Abs_m ?n s \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?w"
    using equiv_trans[OF equiv_Abs_m[OF equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF s(1)]]] eta_expand_equiv[OF nlw]] .
  have "vsz \<tau>' \<sigma> (v, foldr fun_type Ts B) = lsize (\<lambda>_. Atom 0) \<tau>' (Abs_m ?n s) (trty (foldr fun_type Ts B))"
  proof (rule vsz_lsize)
    show "(e, \<tau>') \<turnstile> ?w : trty (foldr fun_type Ts B)" for e using tyw by (simp add: trty_foldr)
    show "Abs_m ?n s \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?w" by (rule eq)
    show "no_redex (Abs_m ?n s)" using nrs by (induction ?n) simp_all
    show "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m ?n s : trty (foldr fun_type Ts B)"
      using typing_Abs_m[OF tys] by (simp add: trty_foldr)
  qed
  also have "\<dots> = lsize (bctx Ts) \<tau>' s (trty B)" by (simp add: trty_foldr lsize_Abs_m)
  finally show ?thesis using that tys nrs nls eq by blast
qed

lemma occurs_terms_term:
  assumes e: "vt_is_empty (tyenv env)" and ety: "env_typed V env" and ty: "\<forall>t\<in>set ts. vtyped V t"
  shows "\<exists>b. occurs_terms env v ts = return b"
proof -
  have "\<exists>b s. occurs_list env v seen ts = Some (Ok (b, s))" for seen
    using ty
  proof (induction ts arbitrary: seen)
    case (Cons t ts)
    from occur_term[OF e ety order_refl, where t = t and seen = seen and v = v] Cons.prems obtain b s
      where o: "occur t env v seen = Some (Ok (b, s))" by auto
    from Cons.IH[of s] Cons.prems obtain b' s' where "occurs_list env v s ts = Some (Ok (b', s'))" by auto
    with o show ?case by (cases b) (auto simp: return_def)
  qed (auto simp: return_def)
  then obtain b s where "occurs_list env v [] ts = Some (Ok (b, s))" by blast
  then show ?thesis by (auto simp: occurs_terms_def return_def)
qed

lemma vps_list_dpairs: "vps_list (concat (map (\<lambda>(_, t, u). [t, u]) dps)) = vps_dps dps"
  by (induction dps) auto

text \<open>
  Completeness of \<^const>\<open>MATCH\<close> on a flex-rigid pair: some element of the sequence is in the
  invariant for extensions of the solution and the typing, and the measure decreases.
\<close>

theorem MATCH_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env (dp # dps)" and frs: "fr_shape V dp" and hun: "heads_unb env dp"
  shows "\<exists>ms. okW (MATCH cfg env dp dps) ms \<and> (\<exists>env'' dps'' V'' \<sigma>''. ev cfg ms (El_E env'' dps'') \<and>
    cinv ar V'' \<tau>' \<sigma>'' env'' dps'' \<and> agree (maxidx env) \<sigma> \<sigma>'' \<and> agreeV (maxidx env) V V'' \<and>
    maxidx env \<le> maxidx env'' \<and> extends env'' env \<and> mu \<tau>' \<sigma>'' env'' dps'' < mu \<tau>' \<sigma> env (dp # dps))"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from frs obtain B where nfB: "\<not> is_funT B" and tyt: "has_type V (map snd rb) t B"
    and tyu: "has_type V (map snd rb) u B" and hvt: "is_Var (head_of t)" and hru: "is_rigid (head_of u)"
    by (auto simp: fr_shape_def dp)
  from hvt obtain v T where ht: "head_of t = Var v T" by (cases "head_of t") auto
  have vn: "vt_lookup (tenv env) v = None" using hun ht by (cases v) (auto simp: heads_unb_def dp)
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note sol = cinvD(2)[OF inv]
  note \<sigma> = solutionD[OF sol]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from cinvD(3)[OF inv, of dp] have wfd: "wf_dp ar (rb, t, u)" and bt: "below (maxidx env) t"
    and bu: "below (maxidx env) u" and ds: "dsolved \<sigma> (rb, t, u)"
    by (auto simp: dp)
  define targs where "targs = snd (strip_comb t)"
  have sc: "strip_comb t = (Var v T, targs)" using fst_strip_comb[of t] ht by (simp add: targs_def prod_eq_iff)
  have t_eq: "t = list_comb (Var v T) targs" using head_of_list_comb[of t] ht by (simp add: targs_def)
  have tyh: "has_type V (map snd rb) (Var v T) T" and Vv: "V v = T"
    using has_type_head_of[OF tyt] ht by (auto elim: has_type_elims intro: has_type.Var)
  from res_type_head(2)[OF tyt nfB tyh[folded ht]] obtain Ts where T: "T = foldr fun_type Ts B"
    and tgty: "list_all2 (has_type V (map snd rb)) targs Ts" by (auto simp: targs_def)
  have aT: "arg_types T = Ts" using arg_res_type_fun[OF nfB, of Ts] T by simp
  have bT: "binder_types env T = return Ts" using binder_types_arg[OF e] aT by simp
  have bok: "binders_ok ar rb" and wu: "wf_tm ar rb u" using wfd by simp_all
  have wt: "wf_tm ar rb (list_comb (Var v T) targs)" using wfd t_eq by simp
  have whd: "wf_tm ar rb (Var v T)" and tgw: "\<forall>t\<in>set targs. wf_tm ar rb t \<and> below (maxidx env) t"
    using wt bt t_eq by (auto simp: wf_tm_list_comb below_list_comb)
  have gT: "ground ar T" by (rule ground_has_type[OF e bok whd tyh])
  have gTs: "\<forall>A\<in>set Ts. ground ar A" using gT unfolding T by (induction Ts) simp_all
  have hA: "\<not> is_Abs (head_of u)" "\<not> is_Var (head_of u)" using hru by (auto simp: is_rigid_def)
  have nAu: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA(1)])
  have hnu: "hnf u" using hA(1) by (cases u) auto
  have hlu: "hlong V (map snd rb) u B" by (rule hlong.base[OF tyu nAu nfB])
  obtain s where tys: "(bctx Ts, \<tau>') \<turnstile> s : trty B"
    and nrs: "no_redex s" and nls: "no_loose_bound s (length Ts)"
    and eqv: "Abs_m (length Ts) s \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))"
    and vszv0: "vsz \<tau>' \<sigma> (v, foldr fun_type Ts B) = lsize (bctx Ts) \<tau>' s (trty B)"
    by (rule value_target[OF sol Vv[unfolded T]])
  have vszv: "vsz \<tau>' \<sigma> (v, T) = lsize (bctx Ts) \<tau>' s (trty B)" using vszv0 T by simp
  let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr t)) targs"
  have "mk_subst \<sigma> (tr t) = \<sigma> (code (AVar v)) \<degree>\<degree> ?st" by (simp add: t_eq tr_list_comb comp_def)
  moreover have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" using ds by (simp add: dsolved_dsolvedB dsolvedB_unabs)
  moreover have "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v)) \<degree>\<degree> ?st"
    by (rule equiv_list_app[OF eqv]) (simp add: list_all2_conv_all_nth equiv_refl)
  ultimately have eqs: "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" by (metis equiv_trans)
  have pre: "mc_pre ar V \<tau>' \<sigma> env dps' rb targs Ts u B s" if "cinv ar V \<tau>' \<sigma> env dps'" for dps'
    unfolding mc_pre_def by (intro conjI that bok tgw tgty wu hnu hlu bu tys nrs nls eqs)
  define Z where "Z = vps_dps (dp # dps)"
  have vZ0: "(v, T) \<in> Z" using vps_head_of[OF ht] by (auto simp: Z_def dp)
  have Zb: "\<forall>y\<in>Z. snd (fst y) \<le> maxidx env"
  proof
    fix y assume "y \<in> Z"
    then obtain dq where dq: "dq \<in> set (dp # dps)" "y \<in> vps_dp dq" unfolding Z_def by blast
    obtain rb' t' u' where "dq = (rb', t', u')" by (cases dq)
    with cinvD(3)[OF inv dq(1)] dq(2) show "snd (fst y) \<le> maxidx env" by (auto dest: below_vps)
  qed
  have fZ: "finite Z"
  proof -
    have "finite (vps_dp dq)" for dq by (cases dq) simp
    then show ?thesis by (simp add: Z_def)
  qed
  have vm: "snd v \<le> maxidx env" using Zb vZ0 by auto
  have vZ: "(v, T) \<in> unb env Z" using vZ0 reach_incl[of Z env] vn by (auto simp: unb_def lk_def)
  have muZ: "mu \<tau>' \<sigma> env (dp # dps) = sum (vsz \<tau>' \<sigma>) (unb env Z)" by (simp add: mu_def Z_def)
  let ?ts = "u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)"
  have vty: "\<forall>t\<in>set ?ts. vtyped V t"
  proof -
    have "vtyped V t'" if "t' \<in> set targs" for t'
      using that tgty by (metis has_type_vtyped in_set_conv_nth list_all2_conv_all_nth)
    moreover have "vtyped V t' \<and> vtyped V u'" if "(rb', t', u') \<in> set dps" for rb' t' u'
      using cinvD(3)[OF inv, of "(rb', t', u')"] that by (auto intro: has_type_vtyped)
    ultimately show ?thesis using has_type_vtyped[OF tyu] by auto
  qed
  from occurs_terms_term[OF e ei(3) vty] obtain occ where oc: "occurs_terms env v ?ts = return occ" by blast
  have okc: "ok (occurs_terms env v ?ts) occ" using oc by (simp add: return_def)
  have vl: "vps_list ?ts = vps u \<union> vps_list targs \<union> vps_dps dps"
    unfolding vps_list_dpairs[symmetric] by auto
  have occ: "occ \<longleftrightarrow> occ_in env v (vps u \<union> vps_list targs \<union> vps_dps dps)"
    using occurs_terms_correct[OF e ei(1) okc] unfolding vl .
  have M: "MATCH cfg env dp dps = do {
      s \<leftarrow> (if occ then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps) else mc cfg (fst v) rb targs u env dps);
      returnW (S_MapNewDset (v, T) Ts s)}"
  proof -
    have "MATCH cfg env (rb, t, u) dps = match_pair cfg env (rb, t, u) dps"
    proof (rule MATCH_ground[OF e wfd])
      fix rb' t' u' v' T' targs' Ts'
      assume "(rb, t, u) = (rb', t', u')" "strip_comb t' = (Var v' T', targs')"
        "binder_types env T' = return Ts'"
      with sc bT list_all2_lengthD[OF tgty] show "length Ts' = length targs'" by (auto simp: return_def)
    qed
    then show ?thesis by (simp add: dp match_pair_def sc bT oc liftM_return)
  qed
  text \<open>The element of the copy is mapped to an element of the sequence of \<^const>\<open>MATCH\<close>.\<close>
  have step: "?thesis"
    if sq: "okW (if occ then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps) else mc cfg (fst v) rb targs u env dps) sq"
      and evc: "ev cfg sq (El_C u' env' dps')"
      and cr: "copy_res ar V \<tau>' \<sigma> env D Ts B s 1 u' env' dps' V' \<sigma>' NV"
      and DZ: "D \<subseteq> Z" and ac: "(v, T) \<notin> reach env' (vps u')"
    for sq u' env' dps' V' \<sigma>' NV D
  proof -
    from cr have sx: "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV" and tyu': "has_type V' (rev Ts) u' B"
      and wc: "wf_cp ar (length Ts) u'" and bu': "below (maxidx env') u'" and vu': "vps u' \<subseteq> NV"
      and eq': "mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" and szc: "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + 1 \<le> lsize (bctx Ts) \<tau>' s (trty B)"
      unfolding copy_res_def by blast+
    have sz: "sum (vsz \<tau>' \<sigma>') NV < vsz \<tau>' \<sigma> (v, T)" using szc vszv by simp
    from new_dset_complete[OF sx ei(4) tyu' wc bu' vu' eq' equiv_sym[OF eqv] T Vv gT gTs vZ DZ Zb fZ ac sz]
    obtain y env'' dps'' where nd: "okW (new_dset (v, T) Ts u' env' dps') y" "y = El_E env'' dps''"
      "cinv ar V' \<tau>' \<sigma>' env'' dps''" "extends env'' env'" "maxidx env'' = maxidx env'"
      "sum (vsz \<tau>' \<sigma>') (unb env'' (vps_dps dps'')) < sum (vsz \<tau>' \<sigma>) (unb env Z)"
      by blast
    note sd = sextD[OF sx]
    have "okW (MATCH cfg env dp dps) (S_MapNewDset (v, T) Ts sq)" using M sq by simp
    moreover have "ev cfg (S_MapNewDset (v, T) Ts sq) (El_E env'' dps'')" using ev.new_dset[OF evc nd(1)] nd(2) by simp
    moreover have "mu \<tau>' \<sigma>' env'' dps'' < mu \<tau>' \<sigma> env (dp # dps)" using nd(6) muZ by (simp add: mu_def)
    ultimately show ?thesis using nd(3-5) sd(2-5) extends_trans[OF nd(4) sd(5)] by fastforce
  qed
  have vtl: "vps_list targs \<subseteq> vps t" using vps_list_comb[of "Var v T" targs] t_eq by auto
  have nNV: "(v, T) \<notin> NV" if "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV" for V' \<sigma>' env' dps' D NV
    using sextD(7)[OF that, of "(v, T)"] vm by auto
  have rNV: "reach env NV = NV" if "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV" for V' \<sigma>' env' dps' D NV
    using reach_new[OF ei(4)] sextD(7)[OF that] by blast
  show ?thesis
  proof (cases occ)
    case True
    have inv1: "cinv ar V \<tau>' \<sigma> env ((rb, t, u) # dps)" using inv by (simp add: dp)
    from match1_complete[OF pre[OF inv1] hA, of cfg "fst v"] obtain sq u' env' V' \<sigma>' NV where
      m: "okW (match1 cfg (fst v) rb targs u env ((rb, t, u) # dps)) sq"
      "ev cfg sq (El_C u' env' ((rb, t, u) # dps))" "tenv env' = tenv env"
      "copy_res ar V \<tau>' \<sigma> env (vps u \<union> vps_list targs \<union> vps_dps ((rb, t, u) # dps)) Ts B s 1 u' env'
        ((rb, t, u) # dps) V' \<sigma>' NV"
      by blast
    from m(4) have sx: "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' ((rb, t, u) # dps)
        (vps u \<union> vps_list targs \<union> vps_dps ((rb, t, u) # dps)) NV" and vu': "vps u' \<subseteq> NV"
      unfolding copy_res_def by blast+
    have DZ: "vps u \<union> vps_list targs \<union> vps_dps ((rb, t, u) # dps) \<subseteq> Z" using vtl by (auto simp: Z_def dp)
    have "reach env' (vps u') \<subseteq> NV"
      using reach_tenv[OF m(3)] reach_subset[OF vu', of env] rNV[OF sx] by simp
    then have ac: "(v, T) \<notin> reach env' (vps u')" using nNV[OF sx] by blast
    from True m(1) have "okW (if occ then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps)
      else mc cfg (fst v) rb targs u env dps) sq" by simp
    from step[OF this m(2,4) DZ ac] show ?thesis .
  next
    case False
    have inv0: "cinv ar V \<tau>' \<sigma> env dps" using inv by (simp add: cinv_def)
    have kk: "(if is_Var (head_of (strip_abs_body u)) then 0 else 1) = (1::nat)"
      using hA nAu by (simp add: strip_abs_body_nonAbs)
    define D where "D = vps u \<union> vps_list targs \<union> vps_dps dps"
    from mc_complete[OF pre[OF inv0], of cfg "fst v"] kk obtain sq u' env' dps' V' \<sigma>' NV where
      m: "okW (mc cfg (fst v) rb targs u env dps) sq" "ev cfg sq (El_C u' env' dps')"
      "copy_res ar V \<tau>' \<sigma> env D Ts B s 1 u' env' dps' V' \<sigma>' NV"
      unfolding mc_post_def D_def by auto
    from m(3) have sx: "sext ar V \<tau>' \<sigma> env V' \<sigma>' env' dps' D NV" and vu': "vps u' \<subseteq> NV"
      unfolding copy_res_def by blast+
    have DZ: "D \<subseteq> Z" using vtl by (auto simp: Z_def dp D_def)
    have nD: "(v, T) \<notin> reach env D" using False occ by (auto simp: occ_in_def D_def)
    have "reach env' (vps u') \<subseteq> reach env (vps u' \<union> D) \<union> NV" by (rule sextD(8)[OF sx])
    also have "\<dots> \<subseteq> reach env D \<union> NV"
      using reach_subset[OF vu', of env] rNV[OF sx] by (auto simp: reach_Un)
    finally have ac: "(v, T) \<notin> reach env' (vps u')" using nD nNV[OF sx] by blast
    from False m(1) have "okW (if occ then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps)
      else mc cfg (fst v) rb targs u env dps) sq" by simp
    from step[OF this m(2,3) DZ ac] show ?thesis .
  qed
qed

end
