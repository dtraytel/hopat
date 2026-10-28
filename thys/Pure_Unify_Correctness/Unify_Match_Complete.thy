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
    "\<And>i. i < length Us \<Longrightarrow> \<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> V1 (xs ! i) = foldr fun_type Ts (Us ! i)"
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
  shows "okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ tail)
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
    then show ?thesis unfolding projenv_def prod.case if_P[OF True] .
  next
    case False
    from cunify_types_ground_neq[OF assms False] obtain evs
      where c: "cunify_types (cfg_alg cfg) base bary env = Some (evs, UErr CANTUNIFY)" by blast
    then have "\<exists>evs. ?m = Some (evs, UErr CANTUNIFY)"
      by (auto simp: test_unify_types_def bindW_def)
    then have "\<exists>evs. ?r = Some (evs, UErr CANTUNIFY)" by (auto simp: bindW_def)
    with False show ?thesis by (auto simp: projenv_def okW_handleW)
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
  have pe: "okW (projenv cfg vname rb targs u env dps base Ts bv (arg_types T, res_type T) targ tail) ?r"
    by (rule projenv_result[OF assms(2) gb])
  have "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (p # projs)) ?r"
    using tl pe by (auto simp: p strip_type_arg_res[OF assms(1)])
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

end
