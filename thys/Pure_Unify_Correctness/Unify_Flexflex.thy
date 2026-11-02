section \<open>Soundness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex
  imports Unify_Match
begin

context csig
begin

text \<open>
  At the end of the search, \<open>add_ffpair\<close> simplifies the remaining flex-flex pairs: it deletes
  bound variables that do not occur in both terms (\<open>clean_term\<close>), does the assignments it
  can, and returns the other pairs. We show that the result is a unifier: every substitution
  that satisfies the final environment and solves the returned pairs solves the input pairs.
\<close>


subsection \<open>Normalization\<close>

lemma ok_lookup1:
  "ok (lookup1 te xi T) r \<Longrightarrow>
    r = None \<and> vt_lookup te xi = None \<or> (\<exists>u. r = Some u \<and> vt_lookup te xi = Some (T, u))"
  by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)

subsection \<open>Deleting bound variables\<close>

text \<open>
  \<open>change_bnos banned\<close> deletes the banned loose bound variables: the others are renamed by
  \<open>squash B\<close>, which maps \<open>i\<close> to the number of non-banned indices below \<open>i\<close>. The renaming is
  injective on the non-banned indices, so it can be undone on terms without banned loose bound
  variables.
\<close>

definition squash :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "squash B i = card ({..<i} - B)"

definition shift_at :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "shift_at k f i = (if i < k then i else k + f (i - k))"

lemma shift_at_Suc: "case_nat 0 (\<lambda>a. Suc (shift_at k f a)) = shift_at (Suc k) f"
  by (auto simp: fun_eq_iff shift_at_def split: nat.split)

lemma squash_less:
  assumes "i < i'" "i \<notin> B"
  shows "squash B i < squash B i'"
  unfolding squash_def by (rule psubset_card_mono) (use assms in auto)

lemma inj_on_squash: "inj_on (squash B) (- B)"
proof (rule inj_onI)
  fix i i' assume "i \<in> - B" "i' \<in> - B" "squash B i = squash B i'"
  then show "i = i'" using squash_less[of i i' B] squash_less[of i' i B]
    by (cases i i' rule: linorder_cases) auto
qed

lemma squash_bound:
  assumes "B \<subseteq> {..<n}" "i < n" "i \<notin> B"
  shows "squash B i < n - card B"
proof -
  have "squash B i < card ({..<n} - B)" unfolding squash_def
    by (rule psubset_card_mono) (use assms in auto)
  also have "card ({..<n} - B) = n - card B" using assms(1) by (simp add: card_Diff_subset finite_subset)
  finally show ?thesis .
qed

definition unsquash :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "unsquash B = inv_into (- B) (squash B)"

lemma unsquash_squash: "i \<notin> B \<Longrightarrow> unsquash B (squash B i) = i"
  unfolding unsquash_def by (rule inv_into_f_f[OF inj_on_squash]) simp

definition bset :: "integer list \<Rightarrow> nat set" where
  "bset banned = nat_of_integer ` set banned"

lemma nat_of_integer_inj: "inj_on nat_of_integer {i. 0 \<le> i}"
  by (rule inj_onI) (simp add: nat_of_integer_eq_iff)

lemma squash_count:
  assumes "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "0 \<le> k"
  shows "nat_of_integer (k - ilength (filter (\<lambda>j. j < k) banned)) = squash (bset banned) (nat_of_integer k)"
    and "ilength (filter (\<lambda>j. j < k) banned) \<le> k"
proof -
  let ?m = "nat_of_integer k"
  have "length (filter (\<lambda>j. j < k) banned) = card ({j. j < k} \<inter> set banned)"
    using assms(1) by (rule distinct_length_filter)
  also have "{j. j < k} \<inter> set banned = {j\<in>set banned. j < k}" by auto
  also have "card {j\<in>set banned. j < k} = card (nat_of_integer ` {j\<in>set banned. j < k})"
    by (rule card_image[symmetric], rule inj_on_subset[OF nat_of_integer_inj]) (use assms(2) in auto)
  also have "nat_of_integer ` {j\<in>set banned. j < k} = {..<?m} \<inter> bset banned"
    using assms(2,3) by (auto simp: bset_def nat_of_integer_less_iff image_iff)
  finally have c: "length (filter (\<lambda>j. j < k) banned) = card ({..<?m} \<inter> bset banned)" .
  have le: "card ({..<?m} \<inter> bset banned) \<le> ?m"
    using card_mono[of "{..<?m}" "{..<?m} \<inter> bset banned"] by auto
  have "squash (bset banned) ?m = ?m - card ({..<?m} \<inter> bset banned)"
    unfolding squash_def by (simp add: card_Diff_subset_Int)
  moreover have "nat_of_integer (k - integer_of_nat (card ({..<?m} \<inter> bset banned))) =
      ?m - card ({..<?m} \<inter> bset banned)"
    using le assms(3) by (simp add: integer_reps)
  ultimately show "nat_of_integer (k - ilength (filter (\<lambda>j. j < k) banned)) =
      squash (bset banned) (nat_of_integer k)" using c by (simp add: ilength_eq)
  show "ilength (filter (\<lambda>j. j < k) banned) \<le> k"
    using c le assms(3) by (simp add: ilength_eq integer_reps)
qed

lemma change_bnos_sound:
  assumes "okW (change_bnos banned lev x) x'" "proper x" "0 \<le> lev" "distinct banned"
    "\<forall>j\<in>set banned. 0 \<le> j"
  shows "proper x' \<and> (typs_ok ar x' \<longleftrightarrow> typs_ok ar x) \<and>
    tr x' = map_BVars (shift_at (nat_of_integer lev) (squash (bset banned))) (tr x) \<and>
    (\<forall>i\<in>loose_BVars (tr x). nat_of_integer lev \<le> i \<longrightarrow> i - nat_of_integer lev \<notin> bset banned)"
  using assms
proof (induction banned lev x arbitrary: x' rule: change_bnos.induct)
  case (1 banned lev i)
  show ?case
  proof (cases "i < lev")
    case True
    with "1.prems" show ?thesis by (auto simp: shift_at_def integer_reps)
  next
    case False
    with "1.prems"(1) have nb: "i - lev \<notin> set banned"
      and x': "x' = Bound (i - ilength (filter (\<lambda>j. j < i - lev) banned))"
      by (auto split: if_splits)
    have k: "0 \<le> i - lev" using False by simp
    have sq: "nat_of_integer (i - lev - ilength (filter (\<lambda>j. j < i - lev) banned)) =
        squash (bset banned) (nat_of_integer (i - lev))"
      by (rule squash_count(1)[OF "1.prems"(4,5) k])
    have cle: "ilength (filter (\<lambda>j. j < i - lev) banned) \<le> i - lev"
      by (rule squash_count(2)[OF "1.prems"(4,5) k])
    have nl: "nat_of_integer (i - lev) = nat_of_integer i - nat_of_integer lev"
      using False "1.prems"(3) by (simp add: integer_reps nat_diff_distrib)
    have "nat_of_integer (i - ilength (filter (\<lambda>j. j < i - lev) banned)) =
        nat_of_integer lev + nat_of_integer (i - lev - ilength (filter (\<lambda>j. j < i - lev) banned))"
      using cle "1.prems"(3) by (simp add: integer_reps nat_add_distrib[symmetric])
    moreover have "nat_of_integer (i - lev) \<notin> bset banned"
      using nb k "1.prems"(5) by (auto simp: bset_def nat_of_integer_eq_iff)
    moreover have "0 \<le> i - ilength (filter (\<lambda>j. j < i - lev) banned)"
      using cle "1.prems"(3) by (simp add: integer_reps)
    ultimately show ?thesis using x' sq nl False "1.prems"(3)
      by (auto simp: shift_at_def nat_of_integer_less_iff)
  qed
next
  case (2 banned lev a T t)
  from "2.prems"(1) obtain t' where t': "okW (change_bnos banned (lev + 1) t) t'"
    and x': "x' = Abs a T t'" by auto
  have l: "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)"
    using "2.prems"(3) by (simp add: integer_reps)
  from "2.IH"[OF t'] "2.prems" l show ?case
    by (auto simp: x' shift_at_Suc)
next
  case (3 banned lev t u)
  from "3.prems"(1) obtain t' u' where t': "okW (change_bnos banned lev t) t'"
    and u': "okW (change_bnos banned lev u) u'" and x': "x' = t' $ u'" by auto
  from "3.IH"(1)[OF t'] "3.IH"(2)[OF t' u'] "3.prems" show ?case by (auto simp: x')
qed auto


lemma change_bnos_unsquash:
  assumes "okW (change_bnos banned 0 x) x'" "proper x" "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j"
  shows "map_BVars (unsquash (bset banned)) (tr x') = tr x"
proof -
  from change_bnos_sound[OF assms(1,2) _ assms(3,4)]
  have x': "tr x' = map_BVars (squash (bset banned)) (tr x)"
    and nb: "\<forall>i\<in>loose_BVars (tr x). i \<notin> bset banned"
    by (simp_all add: shift_at_def[abs_def])
  have "map_BVars (unsquash (bset banned)) (tr x') = map_BVars (unsquash (bset banned) \<circ> squash (bset banned)) (tr x)"
    by (simp add: x' map_BVars_comp)
  also have "\<dots> = map_BVars id (tr x)"
    by (rule map_BVars_cong) (use nb unsquash_squash in auto)
  finally show ?thesis by (simp add: map_BVars_id)
qed

lemma change_bnos_bound:
  assumes "okW (change_bnos banned 0 x) x'" "proper x" "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j"
    "bset banned \<subseteq> {..<n}" "no_loose_bound (tr x) n"
  shows "no_loose_bound (tr x') (n - card (bset banned))"
proof -
  from change_bnos_sound[OF assms(1,2) _ assms(3,4)]
  have x': "tr x' = map_BVars (squash (bset banned)) (tr x)"
    and nb: "\<forall>i\<in>loose_BVars (tr x). i \<notin> bset banned"
    by (simp_all add: shift_at_def[abs_def])
  have "loose_BVars (tr x) \<subseteq> {0..<n}" by (rule no_loose_bound_BVars[OF assms(6)])
  then have "loose_BVars (tr x') \<subseteq> {..<n - card (bset banned)}"
    using nb squash_bound[OF assms(5)] by (auto simp: x' loose_BVars_map_BVars)
  then show ?thesis by (rule loose_BVars_no_loose_bound)
qed

lemma mk_subst_map_BVars:
  "closed_on UNIV \<sigma> \<Longrightarrow> mk_subst \<sigma> (map_BVars f t) = map_BVars f (mk_subst \<sigma> t)"
  by (induction t arbitrary: f) (auto intro: map_BVars_no_loose[symmetric] closed_onD)

lemma map_BVars_equiv: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> map_BVars f s \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f t"
  by (rule map_BVars_preserves_closure)


subsection \<open>Flexible arguments\<close>

lemma flexargs_ok:
  "okW (flexargs js ts Ts) fas \<Longrightarrow>
    length js = length ts \<and> length Ts = length ts \<and>
    (\<forall>a\<in>set fas. \<exists>k<length ts. a = Flarg (js ! k) (ts ! k) (Ts ! k))"
proof (induction js ts Ts arbitrary: fas rule: flexargs.induct)
  case (2 j js t ts T Ts)
  then obtain args where "okW (flexargs js ts Ts) args" "fas = Flarg j t T # args" by auto
  with "2.IH"[OF this(1)] show ?case by (fastforce simp: nth_Cons')
qed auto

lemma foldrW_change_arg:
  "okW (foldrW (change_arg del banned) fas acc) cas \<Longrightarrow>
    \<forall>a'\<in>set cas. a' \<in> set acc \<or> (\<exists>a\<in>set fas. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and>
      okW (change_bnos banned 0 (fl_t a)) (fl_t a'))"
proof (induction fas arbitrary: cas)
  case (Cons a fas)
  then obtain cas1 where c1: "okW (foldrW (change_arg del banned) fas acc) cas1"
    and c: "okW (change_arg del banned a cas1) cas" by auto
  obtain j t T where a: "a = Flarg j t T" by (cases a)
  from c a have "cas = cas1 \<or> (\<exists>t'. okW (change_bnos banned 0 t) t' \<and> cas = Flarg j t' T # cas1)"
    by (auto simp: change_arg_def split: if_splits)
  with "Cons.IH"[OF c1] a show ?case by fastforce
qed simp

lemma set_ins_arg: "set (ins_arg x xs) = insert x (set xs)"
  by (induction xs) auto

lemma set_sort_args: "set (sort_args xs) = set xs"
  by (induction xs) (auto simp: set_ins_arg)

lemma not_decreasing_neg: "k < 0 \<Longrightarrow> \<not> decreasing k args"
  by (induction k args rule: decreasing.induct) auto

lemma decreasing_downs:
  "decreasing (integer_of_nat m) args \<Longrightarrow> map (nat_of_integer \<circ> fl_j) args = downs m"
proof (induction args arbitrary: m)
  case Nil
  then show ?case by (simp add: integer_eq_iff)
next
  case (Cons a args)
  show ?case
  proof (cases m)
    case 0
    with Cons.prems not_decreasing_neg[of "-1" args] show ?thesis by simp
  next
    case (Suc m')
    have m1: "integer_of_nat m - 1 = integer_of_nat m'" using Suc by (simp add: integer_eq_iff)
    with Cons.prems have "fl_j a = integer_of_nat m'" "decreasing (integer_of_nat m') args" by simp_all
    with Cons.IH[of m'] Suc show ?thesis by simp
  qed
qed

text \<open>The new variable applied to the kept arguments, for a binding that selects them.\<close>

lemma Abs_m_select_map_BVars:
  assumes "no_loose_bound G 0" "length ts = n" "\<forall>k\<in>set ks. k < n"
    "list_all2 (\<lambda>k a. map_BVars f a = rev ts ! k) ks as"
  shows "Abs_m n (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (G \<degree>\<degree> as)"
proof -
  have "map (map_BVars f) as = map (\<lambda>k. rev ts ! k) ks"
    using assms(4) by (induction rule: list_all2_induct) auto
  then have "map_BVars f (G \<degree>\<degree> as) = G \<degree>\<degree> map (\<lambda>k. rev ts ! k) ks"
    using map_BVars_no_loose[OF assms(1)] by simp
  with Abs_m_apps_select[OF assms(1-3)] show ?thesis by simp
qed


lemma clean_binding_equiv:
  assumes "length ts = n" "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m n (G \<degree>\<degree> map BVar ks)"
    "closed_on UNIV \<sigma>" "no_loose_bound G 0"
    "list_all2 (\<lambda>k a. k < n \<and> map_BVars f (tr a) = rev (map tr ts) ! k) ks as"
  shows "mk_subst \<sigma> (tr (list_comb (Var v T) ts)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (G \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) as)"
proof -
  let ?ts = "map (mk_subst \<sigma> \<circ> tr) ts"
  have e: "mk_subst \<sigma> (tr (list_comb (Var v T) ts)) = \<sigma> (code (AVar v)) \<degree>\<degree> ?ts"
    by (simp add: tr_list_comb)
  have 1: "\<sigma> (code (AVar v)) \<degree>\<degree> ?ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m n (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ?ts"
    by (rule equiv_list_app[OF assms(2)]) (simp add: list_all2_refl)
  have 2: "Abs_m n (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ?ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (G \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) as)"
  proof (rule Abs_m_select_map_BVars[OF assms(4)])
    show "length ?ts = n" using assms(1) by simp
    show "\<forall>k\<in>set ks. k < n" using assms(5) by (induction rule: list_all2_induct) auto
    show "list_all2 (\<lambda>k a. map_BVars f a = rev ?ts ! k) ks (map (mk_subst \<sigma> \<circ> tr) as)"
      unfolding list_all2_map2
    proof (rule list_all2_mono[OF assms(5)])
      fix k a assume "k < n \<and> map_BVars f (tr a) = rev (map tr ts) ! k"
      with assms(1,3) show "map_BVars f ((mk_subst \<sigma> \<circ> tr) a) = rev ?ts ! k"
        by (simp add: mk_subst_map_BVars[symmetric] rev_map)
    qed
  qed
  show ?thesis unfolding e by (rule equiv_trans[OF 1 2])
qed

lemma downto0_list_nth: "k < n \<Longrightarrow> downto0_list n ! k = integer_of_nat (n - 1 - k)"
  by (simp add: downto0_list_def rev_nth)

subsection \<open>Remaining pairs\<close>

text \<open>The remaining flex-flex pairs are closed terms; a substitution solves them if it makes both
  sides \<open>\<beta>\<eta>\<close>-equal.\<close>

definition tsolved :: "(nat \<Rightarrow> dB) \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "tsolved \<sigma> tps \<longleftrightarrow> (\<forall>(t, u)\<in>set tps. mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u))"

lemma tsolved_Cons: "tsolved \<sigma> ((t, u) # tps) \<longleftrightarrow>
    mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u) \<and> tsolved \<sigma> tps"
  by (simp add: tsolved_def)

lemma aconv_term_tr: "aconv_term t u \<Longrightarrow> tr t = tr u"
  by (induction t u rule: aconv_term.induct) auto

lemma add_tpair_sound:
  "tsolved \<sigma> (add_tpair rb t u tps) \<Longrightarrow> dsolved \<sigma> (rb, t, u) \<and> tsolved \<sigma> tps"
proof (cases "aconv_term t u")
  case True
  assume "tsolved \<sigma> (add_tpair rb t u tps)"
  with True show ?thesis by (simp add: add_tpair_def dsolved_dsolvedB aconv_term_tr)
next
  case False
  assume s: "tsolved \<sigma> (add_tpair rb t u tps)"
  show ?thesis
  proof (cases "\<exists>(t', u')\<in>set tps. aconv_term (rlist_abs rb t) t' \<and> aconv_term (rlist_abs rb u) u'")
    case True
    then obtain t' u' where "(t', u') \<in> set tps" "aconv_term (rlist_abs rb t) t'"
      "aconv_term (rlist_abs rb u) u'" by blast
    moreover from s False True have "tsolved \<sigma> tps" by (simp add: add_tpair_def Let_def)
    ultimately show ?thesis by (auto simp: tsolved_def dsolved_def aconv_term_tr)
  next
    case nex: False
    with s False have "tsolved \<sigma> ((rlist_abs rb t, rlist_abs rb u) # tps)"
      by (simp add: add_tpair_def Let_def)
    then show ?thesis by (simp add: tsolved_Cons dsolved_def)
  qed
qed

lemma add_index_fold:
  assumes "distinct (map fst xs)" "foldr (add_index lt lu) xs ([], []) = (bn, rb')"
  shows "set bn \<subseteq> fst ` set xs \<and> distinct bn \<and> length bn + length rb' = length xs \<and>
    set rb' \<subseteq> snd ` set xs"
  using assms
proof (induction xs arbitrary: bn rb')
  case (Cons x xs)
  obtain bn1 rb1 where f: "foldr (add_index lt lu) xs ([], []) = (bn1, rb1)"
    by (cases "foldr (add_index lt lu) xs ([], [])")
  obtain j xT where x: "x = (j, xT)" by (cases x)
  from Cons.IH[OF _ f] Cons.prems(1) have IH: "set bn1 \<subseteq> fst ` set xs" "distinct bn1"
    "length bn1 + length rb1 = length xs" "set rb1 \<subseteq> snd ` set xs" by simp_all
  from Cons.prems(1) x have "j \<notin> fst ` set xs" by auto
  moreover from Cons.prems(2) f x have "add_index lt lu (j, xT) (bn1, rb1) = (bn, rb')" by simp
  ultimately show ?case using IH x by (auto simp: add_index_def split: if_splits)
qed simp

lemma clean_binder:
  assumes "foldr (add_index lt lu) (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
  shows "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "bset banned \<subseteq> {..<length rb}"
    "length rb' = length rb - card (bset banned)" "set rb' \<subseteq> set rb"
proof -
  have d: "distinct (map fst (zip (upto_list (length rb)) rb))"
    by (simp add: upto_list_def distinct_map inj_on_def integer_eq_iff)
  note f = add_index_fold[OF d assms]
  have "fst ` set (zip (upto_list (length rb)) rb) \<subseteq> set (upto_list (length rb))"
    by (auto dest: set_zip_leftD)
  with f have s: "set banned \<subseteq> integer_of_nat ` {..<length rb}"
    by (auto simp: upto_list_def atLeast0LessThan)
  show db: "distinct banned" using f by simp
  show nn: "\<forall>j\<in>set banned. 0 \<le> j" using s by (auto simp: integer_reps)
  show "bset banned \<subseteq> {..<length rb}" using s by (auto simp: bset_def integer_reps)
  have "card (bset banned) = length banned"
    unfolding bset_def using nn
    by (subst card_image) (auto intro: inj_on_subset[OF nat_of_integer_inj] simp: distinct_card[OF db])
  then show "length rb' = length rb - card (bset banned)" using f by (auto simp: upto_list_def)
  have "snd ` set (zip (upto_list (length rb)) rb) \<subseteq> set rb" by (auto dest: set_zip_rightD)
  with f show "set rb' \<subseteq> set rb" by blast
qed

lemma ff_handler:
  assumes "okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
    (\<lambda>e. case e of
      ASSIGN \<Rightarrow>
        handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
          (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
    | _ \<Rightarrow> raiseW e)) r"
  shows "(\<exists>env3. okW (ff_assign alg env2 rb' t' u') env3 \<and> r = (env3, tps)) \<or>
    (\<exists>env3. okW (ff_assign alg env2 rb' u' t') env3 \<and> r = (env3, tps)) \<or>
    r = (env2, add_tpair rb' t' u' tps)"
proof -
  have h1: "okW (case e of ASSIGN \<Rightarrow> handleW m h | _ \<Rightarrow> raiseW e) y \<Longrightarrow>
      okW m y \<or> (\<exists>evs e. m = Some (evs, UErr e) \<and> okW (h e) y)" for e m h y
    by (cases e) (auto simp: okW_handleW)
  have h2: "bindW m f = Some (evs, UOk y) \<Longrightarrow> \<exists>x. okW m x \<and> okW (f x) y" for m f evs y
    using okW_bindW[of m f y] by blast
  from assms show ?thesis
    by (auto simp: okW_handleW returnW_def dest!: h1 h2 okW_ASSIGN_handler)
qed


lemma okW_CHANGE_FAIL_handler:
  "okW (case e of CHANGE_FAIL \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

text \<open>A solution of the cleaned pair solves the original pair: the renamings undo the deletion
  of the banned bound variables.\<close>

lemma dsolved_rename:
  assumes "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (mk_subst \<sigma> (tr t'))"
    "mk_subst \<sigma> (tr u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (mk_subst \<sigma> (tr u'))" "dsolved \<sigma> (rb', t', u')"
  shows "dsolved \<sigma> (rb, t, u)"
proof -
  from assms(3) have "mk_subst \<sigma> (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u')"
    by (simp add: dsolved_dsolvedB dsolvedB_unabs)
  then have "map_BVars f (mk_subst \<sigma> (tr t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (mk_subst \<sigma> (tr u'))"
    by (rule map_BVars_equiv)
  from equiv_trans[OF equiv_trans[OF assms(1) this] equiv_sym[OF assms(2)]]
  show ?thesis by (simp add: dsolved_dsolvedB dsolvedB_unabs)
qed

lemma dsolved_swap: "dsolved \<sigma> (rb, u, t) \<Longrightarrow> dsolved \<sigma> (rb, t, u)"
  by (simp add: dsolved_def equiv_sym)

end

end
