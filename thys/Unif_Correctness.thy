section \<open>Correctness of the Unification Algorithm\<close>

theory Unif_Correctness
  imports Unif_Termination Unif_Normal
begin

text \<open>
  We follow Grobauer's correctness proof (Section 2.2). The terms are simply typed: as shown in
  Angehrn's thesis, the algorithm does not compute most general unifiers for untyped terms.
  Unifiers are only required to be closed (and typed) on the relevant variables.
\<close>

declare upt_Suc[simp del]

lemma mk_subst_Var_fun[simp]: "mk_subst Var = id"
  by (simp add: fun_eq_iff)

subsection \<open>Substitutions and reduction\<close>

lemma mk_subst_free_on: "\<not> free t i \<Longrightarrow> closed_on (FV t) \<sigma> \<Longrightarrow> \<not> free (mk_subst \<sigma> t) i"
  by (induction t arbitrary: i) (auto simp: closed_on_def loose_bound_free)

lemma mk_subst_beta_on: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> closed_on (FV s) \<sigma> \<Longrightarrow> mk_subst \<sigma> s \<rightarrow>\<^sub>\<beta> mk_subst \<sigma> t"
proof (induction rule: beta.induct)
  case (beta s t)
  then have "mk_subst \<sigma> (s[t/0]) = (mk_subst \<sigma> s)[mk_subst \<sigma> t/0]"
    by (intro mk_subst_subst_on) simp
  then show ?case by simp
qed (auto intro: closed_on_mono)

lemma mk_subst_eta_on: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> closed_on (FV s) \<sigma> \<Longrightarrow> mk_subst \<sigma> s \<rightarrow>\<^sub>\<eta> mk_subst \<sigma> t"
proof (induction rule: eta.induct)
  case (eta s dummy)
  have "s[dummy/0] = s[BVar 0/0]" by (rule subst_not_free[OF eta.hyps])
  moreover have "mk_subst \<sigma> (s[BVar 0/0]) = (mk_subst \<sigma> s)[BVar 0/0]"
    using mk_subst_subst_on[of s "BVar 0" \<sigma> 0] eta.prems by simp
  moreover have "\<not> free (mk_subst \<sigma> s) 0"
    using eta by (intro mk_subst_free_on) simp_all
  ultimately show ?case
    by (metis Eta.eta mk_subst.simps(2,3,4))
qed (auto intro: closed_on_mono)

lemma mk_subst_\<beta>\<eta>cl_on: "\<beta>\<eta>cl s t \<Longrightarrow> closed_on (FV s) \<sigma> \<Longrightarrow> \<beta>\<eta>cl (mk_subst \<sigma> s) (mk_subst \<sigma> t)"
proof (induction rule: rtranclp_induct)
  case (step t u)
  have "FV t \<subseteq> FV s"
    using step.hyps(1) by (induction rule: rtranclp_induct) (auto dest: FV_beta FV_eta)
  then have "closed_on (FV t) \<sigma>" using step.prems closed_on_mono by blast
  with step.hyps(2) have "\<beta>\<eta> (mk_subst \<sigma> t) (mk_subst \<sigma> u)"
    by (auto intro: mk_subst_beta_on mk_subst_eta_on)
  with step show ?case by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed simp

lemma mk_subst_beta_rtrancl_on: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> closed_on (FV s) \<sigma> \<Longrightarrow> mk_subst \<sigma> s \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst \<sigma> t"
proof (induction rule: rtranclp_induct)
  case (step t u)
  have "closed_on (FV t) \<sigma>" using closed_on_mono[OF step.prems FV_beta_rtrancl[OF step.hyps(1)]] .
  with step have "mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta> mk_subst \<sigma> u" by (intro mk_subst_beta_on)
  with step show ?case by (simp add: rtranclp.rtrancl_into_rtrancl)
qed simp

lemma FV_\<beta>\<eta>cl: "\<beta>\<eta>cl s t \<Longrightarrow> FV t \<subseteq> FV s"
  by (induction rule: rtranclp_induct) (auto dest: FV_beta FV_eta)

lemma mk_subst_equiv_on:
  assumes "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t" "closed_on (FV s \<union> FV t) \<sigma>"
  shows "mk_subst \<sigma> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t"
proof -
  from closure_confluent[OF assms(1)] obtain c where "\<beta>\<eta>cl s c" "\<beta>\<eta>cl t c" by blast
  with assms(2) have "\<beta>\<eta>cl (mk_subst \<sigma> s) (mk_subst \<sigma> c)" "\<beta>\<eta>cl (mk_subst \<sigma> t) (mk_subst \<sigma> c)"
    by (auto intro!: mk_subst_\<beta>\<eta>cl_on intro: closed_on_mono)
  then show ?thesis
    by (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
qed


subsection \<open>Unifiers\<close>

definition unifies :: "(nat \<Rightarrow> dB) \<Rightarrow> dB \<Rightarrow> dB \<Rightarrow> bool" where
  "unifies \<sigma> s t \<longleftrightarrow> mk_subst \<sigma> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t"

definition unifies_all :: "(nat \<Rightarrow> dB) \<Rightarrow> unif_problem list \<Rightarrow> bool" where
  "unifies_all \<sigma> us \<longleftrightarrow> (\<forall>(s, t)\<in>set (probs us). unifies \<sigma> s t)"

lemma unifies_sym: "unifies \<sigma> s t \<longleftrightarrow> unifies \<sigma> t s"
  by (auto simp: unifies_def intro: equiv_sym)

lemma unifies_all_simps[simp]:
  "unifies_all \<sigma> []"
  "unifies_all \<sigma> (Marker # us) \<longleftrightarrow> unifies_all \<sigma> us"
  "unifies_all \<sigma> (Problem s t # us) \<longleftrightarrow> unifies \<sigma> s t \<and> unifies_all \<sigma> us"
  "unifies_all \<sigma> (xs @ ys) \<longleftrightarrow> unifies_all \<sigma> xs \<and> unifies_all \<sigma> ys"
  by (auto simp: unifies_all_def)

lemma unifies_comp: "unifies (\<sigma> \<circ>\<^sub>s \<mu>) s t \<longleftrightarrow> unifies \<sigma> (mk_subst \<mu> s) (mk_subst \<mu> t)"
  by (simp add: unifies_def)

text \<open>Equivalent substitutions have the same unifiers.\<close>

lemma unifies_cong:
  assumes "\<And>F. F \<in> FV s \<union> FV t \<Longrightarrow> \<sigma> F \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma>' F"
  shows "unifies \<sigma> s t \<longleftrightarrow> unifies \<sigma>' s t"
proof -
  have "mk_subst \<sigma> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' s" "mk_subst \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' t"
    using assms by (auto intro!: mk_subst_equiv_cong)
  then show ?thesis unfolding unifies_def by (meson equiv_sym equiv_trans)
qed

text \<open>Grobauer's Fact 2: \<open>\<beta>\<close>-normalization does not change the unifiers.\<close>

lemma unifies_\<beta>_nf:
  assumes "closed_on (FV s \<union> FV t) \<sigma>"
  shows "unifies \<sigma> (\<beta>_nf s) (\<beta>_nf t) \<longleftrightarrow> unifies \<sigma> s t"
proof -
  have "mk_subst \<sigma> (\<beta>_nf s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> s" "mk_subst \<sigma> (\<beta>_nf t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t"
    using assms \<beta>_nf_FV
    by (auto intro!: mk_subst_equiv_on \<beta>_nf_equiv intro: closed_on_mono)
  then show ?thesis unfolding unifies_def by (meson equiv_sym equiv_trans)
qed


subsection \<open>Proposition 1: on-the-fly \<open>\<eta>\<close>-conversion\<close>

proposition otf\<eta>_unifies:
  assumes "otf\<eta> (s, t) = (s', t')" "closed_on (FV s \<union> FV t) \<sigma>"
  shows "unifies \<sigma> s' t' \<longleftrightarrow> unifies \<sigma> s t"
proof -
  have "unifies \<sigma> (fst (otf\<eta> (s, t))) (snd (otf\<eta> (s, t))) \<longleftrightarrow> unifies \<sigma> s t"
    using assms(2)
  proof (induction s t rule: otf\<eta>_induct)
    case (AbsAbs s t)
    then show ?case using fact5 by (simp add: unifies_def)
  next
    case (AbsL s t)
    have "mk_subst \<sigma> (lift t 0) = lift (mk_subst \<sigma> t) 0"
      using AbsL.prems by (intro mk_subst_lift_on) (auto intro: closed_on_mono)
    with AbsL show ?case by (simp add: unifies_def fact6)
  next
    case (AbsR s t)
    have "mk_subst \<sigma> (lift s 0) = lift (mk_subst \<sigma> s) 0"
      using AbsR.prems by (intro mk_subst_lift_on) (auto intro: closed_on_mono)
    moreover have "mk_subst \<sigma> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs (mk_subst \<sigma> t) \<longleftrightarrow>
      lift (mk_subst \<sigma> s) 0 \<degree> BVar 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t"
      using fact6[of "mk_subst \<sigma> t" "mk_subst \<sigma> s"] equiv_sym by blast
    ultimately show ?case using AbsR by (simp add: unifies_def Un_commute)
  qed simp
  with assms(1) show ?thesis by simp
qed

lemma prep_unifies:
  assumes "prep (s, t) = ((h1, as1), (h2, as2))" "closed_on (FV s \<union> FV t) \<sigma>"
  shows "unifies \<sigma> (h1 \<degree>\<degree> as1) (h2 \<degree>\<degree> as2) \<longleftrightarrow> unifies \<sigma> s t"
proof -
  from prep_eq[OF assms(1)] obtain s' t' where
    "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" "s' = h1 \<degree>\<degree> as1" "t' = h2 \<degree>\<degree> as2"
    by blast
  with otf\<eta>_unifies[OF _ assms(2)] show ?thesis
    by (auto simp: unifies_sym)
qed


subsection \<open>Instantiating bindings\<close>

text \<open>Applying the bindings computed by \<open>cases\<close> to bound variables (Grobauer's Lemmas 18 and 19).\<close>

lemma appb_flex_binding:
  assumes "length xs = m" "\<forall>z\<in>set zs. z < m"
  shows "appb (Abs_m m (Var H \<degree>\<degree> map BVar zs)) xs = Var H \<degree>\<degree> map BVar (map (\<lambda>z. xs ! (m - Suc z)) zs)"
  using assms by (simp add: appb_Abs_m comp_def)

lemma appb_fr_binding:
  assumes "length xs = m" "j < m" "set Hs \<subseteq> range Var"
  shows "appb (Abs_m m (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs)) xs =
    BVar (xs ! (m - Suc j)) \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar xs) Hs"
proof -
  have "map_BVars g (H \<degree>\<degree> map BVar (downs m)) = H \<degree>\<degree> map BVar xs"
    if "H \<in> set Hs" "g = (\<lambda>i. if i < m then xs ! (m - Suc i) else i - m)" for H g
  proof -
    from that assms(3) obtain G where "H = Var G" by auto
    moreover have "map g (downs m) = map (\<lambda>i. xs ! (m - Suc i)) (downs m)"
      using that(2) by (intro map_cong) auto
    then have "map g (downs m) = xs"
      using map_downs[OF assms(1)] by simp
    ultimately show ?thesis by (simp del: map_map)
  qed
  then show ?thesis
    using assms by (simp add: appb_Abs_m comp_def cong: map_cong)
qed

lemma unifies_equiv:
  assumes "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> s'" "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> t'" "closed_on (FV s \<union> FV s' \<union> FV t \<union> FV t') \<sigma>"
  shows "unifies \<sigma> s t \<longleftrightarrow> unifies \<sigma> s' t'"
proof -
  have "mk_subst \<sigma> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> s'" "mk_subst \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t'"
    using assms by (auto intro!: mk_subst_equiv_on intro: closed_on_mono)
  then show ?thesis unfolding unifies_def by (meson equiv_sym equiv_trans)
qed

lemma unifies_BVar_apps:
  "unifies \<sigma> (BVar p \<degree>\<degree> as) (BVar q \<degree>\<degree> bs) \<longleftrightarrow> p = q \<and> list_all2 (unifies \<sigma>) as bs"
proof
  assume "unifies \<sigma> (BVar p \<degree>\<degree> as) (BVar q \<degree>\<degree> bs)"
  then have "BVar p \<degree>\<degree> map (mk_subst \<sigma>) as \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar q \<degree>\<degree> map (mk_subst \<sigma>) bs"
    by (simp add: unifies_def)
  from atom_apps_equiv[OF _ _ this] show "p = q \<and> list_all2 (unifies \<sigma>) as bs"
    by (simp add: unifies_def[abs_def] list_all2_map1 list_all2_map2)
next
  assume "p = q \<and> list_all2 (unifies \<sigma>) as bs"
  then show "unifies \<sigma> (BVar p \<degree>\<degree> as) (BVar q \<degree>\<degree> bs)"
    by (auto simp: unifies_def[abs_def] list_all2_map1 list_all2_map2 intro!: equiv_list_app)
qed


lemma unifies_all_map2:
  "length as = length bs \<Longrightarrow> unifies_all \<sigma> (map2 Problem as bs) \<longleftrightarrow> list_all2 (unifies \<sigma>) as bs"
  by (induction as bs rule: list_induct2) auto

lemma unifies_all_map2':
  "length Hs = length bs \<Longrightarrow>
    unifies_all \<sigma> (map2 (\<lambda>H s. Problem (f H) s) Hs bs) \<longleftrightarrow> list_all2 (unifies \<sigma>) (map f Hs) bs"
  by (induction Hs bs rule: list_induct2) auto

lemma ff1_args_eq:
  assumes "length xs = length ys"
  shows "map (\<lambda>z. xs ! (length xs - Suc z)) (ff1_args xs ys) = map (\<lambda>z. ys ! (length xs - Suc z)) (ff1_args xs ys)"
proof -
  have "xs ! (length xs - Suc (length xs - 1 - i)) = ys ! (length xs - Suc (length xs - 1 - i))"
    if "i < length xs" "xs ! i = ys ! i" for i
    using that by (simp add: Suc_diff_Suc)
  then show ?thesis by (auto simp: ff1_args_def)
qed

lemma ff2_args_eq:
  assumes "ff2_args xs ys = (zs1, zs2)"
  shows "map (\<lambda>z. xs ! (length xs - Suc z)) zs1 = map (\<lambda>z. ys ! (length ys - Suc z)) zs2"
proof -
  have "xs ! (length xs - Suc (the (idx xs (ys ! i)))) = ys ! (length ys - Suc (length ys - 1 - i))"
    if "i < length ys" "ys ! i \<in> set xs" for i
  proof -
    from that(2) obtain j where "idx xs (ys ! i) = Some j"
      using idx_None_iff by fastforce
    with idx_SomeD[OF this] that(1) show ?thesis by (simp add: Suc_diff_Suc)
  qed
  with assms show ?thesis by (auto simp: ff2_args_def Let_def)
qed

lemma closed_on_upd: "closed_on (V - {F}) \<sigma> \<Longrightarrow> no_loose_bound v 0 \<Longrightarrow> closed_on V (\<sigma>(F := v))"
  by (auto simp: closed_on_def)


subsection \<open>Analysis of \<open>cases\<close>\<close>

text \<open>
  The following lemma summarizes the properties of a successful step that are needed for the
  correctness proofs: the shape of the substitution, the new variables, and the fact that the
  substitution maps the (prepared) problem to terms that are \<open>\<beta>\<close>-equivalent to the new problems
  (for the flexible cases: to identical terms).
\<close>

lemma cases_closed:
  assumes "cases k (prep (s, t)) = Some (k', us', \<mu>)" "pat s" "pat t"
  shows "pat_subst UNIV \<mu>" "k \<le> k'"
proof -
  obtain h1 as1 h2 as2 where prep: "prep (s, t) = ((h1, as1), (h2, as2))"
    by (metis prod.exhaust)
  from prep_eq[OF prep] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2"
    by blast
  have pats': "pat s'" "pat t'" using otf otf\<eta>_props[of s t] assms(2,3) by auto
  from assms(1)[unfolded prep] have "pat_subst UNIV \<mu> \<and> k \<le> k'"
  proof (cases rule: cases_SomeE)
    case (flex_rigid F xs p j)
    let ?Hs = "map Var [Suc k..<Suc k + length as2]"
    have "j < length as1" using idx_SomeD[OF flex_rigid(5)] by simp
    then have "pat (Abs_m (length as1) (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs (length as1))) ?Hs))"
      "no_loose_bound (Abs_m (length as1) (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs (length as1))) ?Hs)) 0"
      by (auto simp: no_loose_bound_list_app)
    with flex_rigid show ?thesis by (auto simp: pat_subst_def)
  next
    case (flex_flex1 F xs ys)
    then show ?thesis
      by (auto simp: pat_subst_def ff1_args_distinct no_loose_bound_list_app dest: ff1_args_less)
  next
    case (flex_flex2 F G xs ys zs1 zs2)
    have "distinct ys" using pats' t' flex_flex2(2,5) by simp
    with flex_flex2 show ?thesis
      by (auto simp: pat_subst_def no_loose_bound_list_app ff2_args_distinct2
        dest: ff2_args_distinct1 ff2_args_less)
  qed (auto simp: pat_subst_def)
  then show "pat_subst UNIV \<mu>" "k \<le> k'" by auto
qed


subsection \<open>Proposition 3: the new problems have the same unifiers\<close>

proposition cases_same_unifiers:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)"
    and pats: "pat s" "pat t"
    and cl: "closed_on (\<Union> (FV ` \<mu> ` (FV s \<union> FV t)) \<union> FVs us') \<sigma>"
  shows "unifies \<sigma> (mk_subst \<mu> s) (mk_subst \<mu> t) \<longleftrightarrow> unifies_all \<sigma> us'"
proof -
  obtain h1 as1 h2 as2 where prep: "prep (s, t) = ((h1, as1), (h2, as2))"
    by (metis prod.exhaust)
  from prep_eq[OF prep] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2"
    by blast
  have pats': "pat s'" "pat t'" and FV': "FV s' \<union> FV t' = FV s \<union> FV t"
    using otf otf\<eta>_props[of s t] pats by auto
  note ps = cases_closed(1)[OF cs pats]
  have cl_comp: "closed_on (FV s \<union> FV t) (\<sigma> \<circ>\<^sub>s \<mu>)"
  proof (rule closed_on_comp)
    show "closed_on (FV s \<union> FV t) \<mu>" using pat_subst_closed_on[OF ps] closed_on_mono by blast
    show "closed_on (\<Union> (FV ` \<mu> ` (FV s \<union> FV t))) \<sigma>" using cl closed_on_mono by blast
  qed
  have "unifies \<sigma> (mk_subst \<mu> s) (mk_subst \<mu> t) \<longleftrightarrow> unifies \<sigma> (mk_subst \<mu> s') (mk_subst \<mu> t')"
    using prep_unifies[OF prep cl_comp] s' t' by (simp add: unifies_comp)
  also have "\<dots> \<longleftrightarrow> unifies_all \<sigma> us'"
    using cs[unfolded prep]
  proof (cases rule: cases_SomeE)
    case (rigid_rigid p)
    then show ?thesis by (simp add: s' t' unifies_BVar_apps unifies_all_map2)
  next
    case (flex_rigid F xs p j)
    define m where "m = length as1"
    define Hs where "Hs = map Var [Suc k..<Suc k + length as2]"
    define v where "v = Abs_m m (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs)"
    have \<mu>: "\<mu> = Var(F := v)" using flex_rigid by (simp add: v_def Hs_def m_def)
    have "j < m" using idx_SomeD[OF flex_rigid(5)] by (simp add: m_def)
    have p: "xs ! (m - Suc j) = p"
    proof -
      have "j < length xs" "map BVar xs ! (length xs - Suc j) = BVar p"
        using idx_SomeD[OF flex_rigid(5)] flex_rigid(2) by auto
      then show ?thesis by (simp add: m_def flex_rigid(2))
    qed
    have setHs: "set Hs \<subseteq> range Var" by (auto simp: Hs_def)
    have "mk_subst \<mu> s' = v \<degree>\<degree> map BVar xs" using flex_rigid(1,2) by (simp add: s' \<mu>)
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> appb v xs" by (rule beta_into_equiv[OF appb_reduces])
    also have "appb v xs = BVar p \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> as1) Hs"
      unfolding v_def using \<open>j < m\<close> setHs p flex_rigid(2)
      by (subst appb_fr_binding) (simp_all add: m_def)
    finally have s'': "mk_subst \<mu> s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar p \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> as1) Hs" .
    have t'': "mk_subst \<mu> t' = BVar p \<degree>\<degree> as2"
      using flex_rigid by (auto simp: t' \<mu> intro!: mk_subst_cong[where \<sigma>' = Var, simplified] map_idI)
    have lenHs: "length Hs = length as2" by (simp add: Hs_def)
    have us': "us' = map2 (\<lambda>H s. Problem (H \<degree>\<degree> as1) s) Hs as2 @ [Marker]"
      using flex_rigid(7) by (simp add: Hs_def)
    have FVHs: "\<Union> (FV ` set (map (\<lambda>H. H \<degree>\<degree> as1) Hs)) = {Suc k..<Suc k + length as2}"
      using flex_rigid(2) by (auto simp: Hs_def)
    have FVus': "FVs us' = {Suc k..<Suc k + length as2} \<union> \<Union> (FV ` set as2)"
    proof -
      have "FVs us' = (\<Union>(a, b)\<in>set (zip (map (\<lambda>H. H \<degree>\<degree> as1) Hs) as2). FV a \<union> FV b)"
        by (simp add: us' FVs_def)
      also have "\<dots> = \<Union> (FV ` set (map (\<lambda>H. H \<degree>\<degree> as1) Hs)) \<union> \<Union> (FV ` set as2)"
        using lenHs by (simp add: UN_zip)
      finally show ?thesis using FVHs by simp
    qed
    have cl': "closed_on (FVs us') \<sigma>" using cl closed_on_mono by blast
    have "unifies \<sigma> (mk_subst \<mu> s') (mk_subst \<mu> t') \<longleftrightarrow>
      unifies \<sigma> (BVar p \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> as1) Hs) (BVar p \<degree>\<degree> as2)"
    proof (rule unifies_equiv[OF s''])
      show "mk_subst \<mu> t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar p \<degree>\<degree> as2" by (simp add: t'')
      have "FV (mk_subst \<mu> s') \<subseteq> FVs us'"
        using flex_rigid(1,2) FVus' by (auto simp: s' \<mu> v_def Hs_def)
      moreover have "FV (BVar p \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> as1) Hs) \<subseteq> FVs us'"
        using FVHs FVus' by (simp only: FV_list_app) auto
      moreover have "FV (BVar p \<degree>\<degree> as2) \<subseteq> FVs us'" using FVus' by auto
      ultimately show "closed_on (FV (mk_subst \<mu> s') \<union> FV (BVar p \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> as1) Hs) \<union>
          FV (mk_subst \<mu> t') \<union> FV (BVar p \<degree>\<degree> as2)) \<sigma>"
        using t'' by (intro closed_on_mono[OF cl']) (simp only: FV_list_app; auto)
    qed
    also have "\<dots> \<longleftrightarrow> unifies_all \<sigma> us'"
      using lenHs by (simp add: us' unifies_BVar_apps unifies_all_map2')
    finally show ?thesis .
  next
    case (flex_flex1 F xs ys)
    let ?zs = "ff1_args xs ys"
    let ?v = "Abs_m (length xs) (Var (Suc k) \<degree>\<degree> map BVar ?zs)"
    have \<mu>: "\<mu> = Var(F := ?v)" using flex_flex1 by simp
    have zs: "\<forall>z\<in>set ?zs. z < length xs" using ff1_args_less by blast
    have "mk_subst \<mu> s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> appb ?v xs" "mk_subst \<mu> t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> appb ?v ys"
      using flex_flex1 by (auto simp: s' t' \<mu> intro: beta_into_equiv[OF appb_reduces])
    moreover have "appb ?v xs = appb ?v ys"
      using flex_flex1(5) zs ff1_args_eq[OF flex_flex1(5)]
      by (simp add: appb_flex_binding)
    moreover have "closed_on (FV (mk_subst \<mu> s') \<union> FV (appb ?v xs) \<union> FV (mk_subst \<mu> t') \<union> FV (appb ?v ys)) \<sigma>"
    proof -
      have "F \<in> FV s \<union> FV t" using FV' flex_flex1 by (auto simp: s')
      then have "Suc k \<in> \<Union> (FV ` \<mu> ` (FV s \<union> FV t))" by (force simp: \<mu>)
      then show ?thesis using cl flex_flex1 by (auto simp: s' t' \<mu> intro: closed_on_mono)
    qed
    ultimately have "unifies \<sigma> (mk_subst \<mu> s') (mk_subst \<mu> t')"
      using unifies_equiv[of "mk_subst \<mu> s'" "appb ?v xs" "mk_subst \<mu> t'" "appb ?v ys" \<sigma>]
      by (simp add: unifies_def)
    then show ?thesis using flex_flex1 by simp
  next
    case (flex_flex2 F G xs ys zs1 zs2)
    let ?v1 = "Abs_m (length xs) (Var (Suc k) \<degree>\<degree> map BVar zs1)"
    let ?v2 = "Abs_m (length ys) (Var (Suc k) \<degree>\<degree> map BVar zs2)"
    have \<mu>: "\<mu> = Var(F := ?v1, G := ?v2)" using flex_flex2 by simp
    have "mk_subst \<mu> s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> appb ?v1 xs" "mk_subst \<mu> t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> appb ?v2 ys"
      using flex_flex2 by (auto simp: s' t' \<mu> intro: beta_into_equiv[OF appb_reduces])
    moreover have "appb ?v1 xs = appb ?v2 ys"
      using ff2_args_less[OF flex_flex2(6)] ff2_args_eq[OF flex_flex2(6)]
      by (simp add: appb_flex_binding)
    moreover have "closed_on (FV (mk_subst \<mu> s') \<union> FV (appb ?v1 xs) \<union> FV (mk_subst \<mu> t') \<union> FV (appb ?v2 ys)) \<sigma>"
    proof -
      have "F \<in> FV s \<union> FV t" using FV' flex_flex2 by (auto simp: s')
      then have "Suc k \<in> \<Union> (FV ` \<mu> ` (FV s \<union> FV t))" by (force simp: \<mu>)
      then show ?thesis using cl flex_flex2 by (auto simp: s' t' \<mu> intro: closed_on_mono)
    qed
    ultimately have "unifies \<sigma> (mk_subst \<mu> s') (mk_subst \<mu> t')"
      using unifies_equiv[of "mk_subst \<mu> s'" "appb ?v1 xs" "mk_subst \<mu> t'" "appb ?v2 ys" \<sigma>]
      by (simp add: unifies_def)
    then show ?thesis using flex_flex2 by simp
  qed
  finally show ?thesis .
qed


subsection \<open>Typing of a step\<close>

definition typed_prob :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> dB \<Rightarrow> bool" where
  "typed_prob \<tau> s t \<longleftrightarrow> (\<exists>e T. (e, \<tau>) \<turnstile> s : T \<and> (e, \<tau>) \<turnstile> t : T)"

definition typed_list :: "(nat \<Rightarrow> type) \<Rightarrow> unif_problem list \<Rightarrow> bool" where
  "typed_list \<tau> us \<longleftrightarrow> (\<forall>(s, t)\<in>set (probs us). typed_prob \<tau> s t)"

lemma typed_list_simps[simp]:
  "typed_list \<tau> []"
  "typed_list \<tau> (Marker # us) \<longleftrightarrow> typed_list \<tau> us"
  "typed_list \<tau> (Problem s t # us) \<longleftrightarrow> typed_prob \<tau> s t \<and> typed_list \<tau> us"
  "typed_list \<tau> (xs @ ys) \<longleftrightarrow> typed_list \<tau> xs \<and> typed_list \<tau> ys"
  by (auto simp: typed_list_def)

lemma prep_typing:
  assumes "prep (s, t) = ((h1, as1), (h2, as2))" "typed_prob \<tau> s t"
  shows "typed_prob \<tau> (h1 \<degree>\<degree> as1) (h2 \<degree>\<degree> as2)"
proof -
  from prep_eq[OF assms(1)] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2"
    by blast
  from assms(2) obtain e T where "(e, \<tau>) \<turnstile> s : T" "(e, \<tau>) \<turnstile> t : T"
    by (auto simp: typed_prob_def)
  with otf otf\<eta>_typing[of s t] show ?thesis
    unfolding typed_prob_def s'[symmetric] t'[symmetric] by blast
qed

lemma typing_Var_app_BVars:
  "(e, \<tau>) \<turnstile> Var F \<degree>\<degree> map BVar xs : T \<longleftrightarrow> \<tau> F = map e xs \<Rrightarrow> T"
  by (auto simp: list_app_typing_iff typings_map_BVar)

lemma typing_BVar_app:
  "(e, \<tau>) \<turnstile> BVar p \<degree>\<degree> as : T \<longleftrightarrow> (\<exists>Us. e p = Us \<Rrightarrow> T \<and> (e, \<tau>) \<tturnstile> as : Us)"
  by (auto simp: list_app_typing_iff)

lemma env_ext_less: "z < length Ts \<Longrightarrow> env_ext e Ts z = Ts ! (length Ts - Suc z)"
  by (simp add: env_ext_nth)

lemma env_ext_downs: "map (env_ext e Ts) (downs (length Ts)) = Ts"
proof -
  have "map (env_ext e Ts) (downs (length Ts)) = map (\<lambda>i. Ts ! (length Ts - Suc i)) (downs (length Ts))"
    by (intro map_cong) (auto simp: env_ext_less)
  also have "\<dots> = Ts" by (rule map_downs) simp
  finally show ?thesis .
qed

lemma env_ext_map: "z < length xs \<Longrightarrow> env_ext e (map E xs) z = E (xs ! (length xs - Suc z))"
  by (simp add: env_ext_less)

lemma typings_map2:
  assumes "length Hs = length Us" "\<And>i. i < length Hs \<Longrightarrow> e \<turnstile> Hs ! i : Us ! i"
  shows "e \<tturnstile> Hs : Us"
  using assms
proof (induction Hs Us rule: list_induct2)
  case (Cons H Hs U Us)
  have "e \<turnstile> H : U" using Cons.prems[of 0] by simp
  moreover have "e \<tturnstile> Hs : Us"
  proof (rule Cons.IH)
    fix i assume "i < length Hs"
    then show "e \<turnstile> Hs ! i : Us ! i" using Cons.prems[of "Suc i"] by simp
  qed
  ultimately show ?case by simp
qed simp

lemma cases_typing:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)"
    and pats: "pat s" "pat t" and typed: "typed_prob \<tau> s t" and FV: "FV s \<union> FV t \<subseteq> {..k}"
  obtains \<tau>' where "\<And>F. F \<le> k \<Longrightarrow> \<tau>' F = \<tau> F" "typed_list \<tau>' us'" "typed_on {..k} \<tau> \<tau>' \<mu>"
proof -
  obtain h1 as1 h2 as2 where prep: "prep (s, t) = ((h1, as1), (h2, as2))"
    by (metis prod.exhaust)
  from prep_eq[OF prep] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2"
    by blast
  have FV': "FV s' \<union> FV t' = FV s \<union> FV t"
    using otf otf\<eta>_props[of s t] pats by auto
  from prep_typing[OF prep typed] obtain E T where
    ty: "(E, \<tau>) \<turnstile> h1 \<degree>\<degree> as1 : T" "(E, \<tau>) \<turnstile> h2 \<degree>\<degree> as2 : T"
    by (auto simp: typed_prob_def)
  have tyV: "typed_on V \<tau> \<tau>' Var" if "\<And>F. F \<in> V \<Longrightarrow> \<tau>' F = \<tau> F" for V \<tau>'
    using that by (auto simp: typed_on_def)
  have typed_on_upd: "typed_on {..k} \<tau> \<tau>' (Var(F := v))"
    if "\<And>G. G \<le> k \<Longrightarrow> \<tau>' G = \<tau> G" "\<And>e. (e, \<tau>') \<turnstile> v : \<tau> F" for F v \<tau>'
    using that by (auto simp: typed_on_def)
  from cs[unfolded prep] show ?thesis
  proof (cases rule: cases_SomeE)
    case (rigid_rigid p)
    from ty obtain Us1 Us2 where "E p = Us1 \<Rrightarrow> T" "(E, \<tau>) \<tturnstile> as1 : Us1" "E p = Us2 \<Rrightarrow> T" "(E, \<tau>) \<tturnstile> as2 : Us2"
      by (auto simp: rigid_rigid typing_BVar_app)
    moreover from this have "length Us1 = length Us2"
      using rigid_rigid(3) typings_length by metis
    ultimately have "Us1 = Us2" by (auto simp: funs_eq_iff)
    with \<open>(E, \<tau>) \<tturnstile> as1 : Us1\<close> \<open>(E, \<tau>) \<tturnstile> as2 : Us2\<close> have "typed_list \<tau> us'"
      using rigid_rigid(3,5) by (auto simp: typed_list_def typed_prob_def set_zip
        dest!: typings_nth[of "(E, \<tau>)" as1] typings_nth[of "(E, \<tau>)" as2])
    then show ?thesis using that[of \<tau>] rigid_rigid(6) tyV[of "{..k}" \<tau>] by simp
  next
    case (flex_rigid F xs p j)
    define m where "m = length xs"
    define n where "n = length as2"
    define Ts where "Ts = map E xs"
    have \<tau>F: "\<tau> F = Ts \<Rrightarrow> T" using ty(1) flex_rigid by (simp add: typing_Var_app_BVars Ts_def)
    from ty(2) flex_rigid obtain Us where Us: "E p = Us \<Rrightarrow> T" "(E, \<tau>) \<tturnstile> as2 : Us"
      by (auto simp: typing_BVar_app)
    have lenUs: "length Us = n" using typings_length[OF Us(2)] by (simp add: n_def)
    define \<tau>' where "\<tau>' = (\<lambda>G. if Suc k \<le> G \<and> G < Suc k + n then Ts \<Rrightarrow> (Us ! (G - Suc k)) else \<tau> G)"
    have \<tau>'k: "\<tau>' G = \<tau> G" if "G \<le> k" for G using that by (simp add: \<tau>'_def)
    have FVas2: "\<Union> (FV ` set as2) \<subseteq> {..k}" using FV FV' t' flex_rigid(3) by auto
    have "typed_list \<tau>' us'"
    proof -
      have "(E, \<tau>') \<turnstile> Var (Suc k + i) \<degree>\<degree> as1 : Us ! i" if "i < n" for i
        using that flex_rigid(2) by (simp add: typing_Var_app_BVars \<tau>'_def Ts_def)
      moreover have "(E, \<tau>') \<turnstile> as2 ! i : Us ! i" if "i < n" for i
      proof (rule typing_free_cong)
        show "(E, \<tau>) \<turnstile> as2 ! i : Us ! i" using typings_nth[OF Us(2)] that by (simp add: n_def)
        show "\<tau> G = \<tau>' G" if "G \<in> FV (as2 ! i)" for G
          using that \<open>i < n\<close> FVas2 \<tau>'k by (force simp: n_def)
      qed
      ultimately have "typed_prob \<tau>' (Var (Suc k + i) \<degree>\<degree> as1) (as2 ! i)" if "i < n" for i
        using that unfolding typed_prob_def by blast
      then show ?thesis
        using flex_rigid(7) by (auto simp: typed_list_def set_zip n_def)
    qed
    moreover have "typed_on {..k} \<tau> \<tau>' \<mu>"
    proof -
      have "j < m" using idx_SomeD[OF flex_rigid(5)] flex_rigid(2) by (simp add: m_def)
      have pj: "xs ! (m - Suc j) = p"
      proof -
        have "j < length xs" "map BVar xs ! (length xs - Suc j) = BVar p"
          using idx_SomeD[OF flex_rigid(5)] flex_rigid(2) by auto
        moreover have "length xs - Suc j < length xs" using calculation(1) by arith
        ultimately show ?thesis by (simp add: m_def)
      qed
      have "(e, \<tau>') \<turnstile> Abs_m m (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m))
          (map Var [Suc k..<Suc k + n])) : \<tau> F" for e
      proof -
        have "(env_ext e Ts, \<tau>') \<turnstile> BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m))
            (map Var [Suc k..<Suc k + n]) : T"
          unfolding typing_BVar_app
        proof (intro exI conjI)
          show "env_ext e Ts j = Us \<Rrightarrow> T"
            using \<open>j < m\<close> pj Us(1) by (simp add: env_ext_less Ts_def m_def)
          show "(env_ext e Ts, \<tau>') \<tturnstile> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) (map Var [Suc k..<Suc k + n]) : Us"
          proof (rule typings_map2)
            fix i assume "i < length (map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) (map Var [Suc k..<Suc k + n]))"
            then have "i < n" by simp
            then show "(env_ext e Ts, \<tau>') \<turnstile> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) (map Var [Suc k..<Suc k + n]) ! i : Us ! i"
              using env_ext_downs[of e Ts] by (simp add: typing_Var_app_BVars \<tau>'_def m_def Ts_def)
          qed (simp add: lenUs)
        qed
        then show ?thesis using typing_Abs_m[of e Ts \<tau>'] \<tau>F by (simp add: Ts_def m_def)
      qed
      then show ?thesis
        unfolding flex_rigid(8) by (intro typed_on_upd[OF \<tau>'k]) (simp_all add: m_def n_def flex_rigid(2))
    qed
    ultimately show ?thesis using that \<tau>'k by blast
  next
    case (flex_flex1 F xs ys)
    define m where "m = length xs"
    define Ts where "Ts = map E xs"
    define zs where "zs = ff1_args xs ys"
    have \<tau>F: "\<tau> F = Ts \<Rrightarrow> T" using ty(1) flex_flex1 by (simp add: typing_Var_app_BVars Ts_def)
    define \<tau>' where "\<tau>' = \<tau>(Suc k := map (env_ext E Ts) zs \<Rrightarrow> T)"
    have \<tau>'k: "\<tau>' G = \<tau> G" if "G \<le> k" for G using that by (simp add: \<tau>'_def)
    have "(e, \<tau>') \<turnstile> Abs_m m (Var (Suc k) \<degree>\<degree> map BVar zs) : \<tau> F" for e
    proof -
      have eqm: "map (env_ext e Ts) zs = map (env_ext E Ts) zs"
        using ff1_args_less[of _ xs ys] by (auto simp: zs_def env_ext_less Ts_def intro!: map_cong)
      have "(env_ext e Ts, \<tau>') \<turnstile> Var (Suc k) \<degree>\<degree> map BVar zs : T"
        by (simp add: typing_Var_app_BVars \<tau>'_def eqm)
      then show ?thesis using typing_Abs_m[of e Ts \<tau>'] \<tau>F by (simp add: Ts_def m_def)
    qed
    then have "typed_on {..k} \<tau> \<tau>' \<mu>"
      unfolding flex_flex1(8) by (intro typed_on_upd[OF \<tau>'k]) (simp_all add: m_def zs_def)
    then show ?thesis using flex_flex1(7) by (intro that[of \<tau>']) (simp_all add: \<tau>'k)
  next
    case (flex_flex2 F G xs ys zs1 zs2)
    define m where "m = length xs"
    define n where "n = length ys"
    define Ts where "Ts = map E xs"
    define Ss where "Ss = map E ys"
    have \<tau>F: "\<tau> F = Ts \<Rrightarrow> T" using ty(1) flex_flex2 by (simp add: typing_Var_app_BVars Ts_def)
    have \<tau>G: "\<tau> G = Ss \<Rrightarrow> T" using ty(2) flex_flex2 by (simp add: typing_Var_app_BVars Ss_def)
    define \<tau>' where "\<tau>' = \<tau>(Suc k := map (env_ext E Ts) zs1 \<Rrightarrow> T)"
    have \<tau>'k: "\<tau>' H = \<tau> H" if "H \<le> k" for H using that by (simp add: \<tau>'_def)
    have eq: "map (env_ext E Ts) zs1 = map (env_ext E Ss) zs2"
    proof -
      have "map (env_ext E Ts) zs1 = map E (map (\<lambda>z. xs ! (m - Suc z)) zs1)"
        using ff2_args_less(1)[OF flex_flex2(6)]
        by (auto simp: env_ext_map Ts_def m_def intro!: map_cong)
      also have "\<dots> = map E (map (\<lambda>z. ys ! (n - Suc z)) zs2)"
        using ff2_args_eq[OF flex_flex2(6)] by (simp add: m_def n_def)
      also have "\<dots> = map (env_ext E Ss) zs2"
        using ff2_args_less(2)[OF flex_flex2(6)]
        by (auto simp: env_ext_map Ss_def n_def intro!: map_cong)
      finally show ?thesis .
    qed
    have "(e, \<tau>') \<turnstile> Abs_m m (Var (Suc k) \<degree>\<degree> map BVar zs1) : \<tau> F" for e
    proof -
      have eqm: "map (env_ext e Ts) zs1 = map (env_ext E Ts) zs1"
        using ff2_args_less(1)[OF flex_flex2(6)] by (auto simp: env_ext_less Ts_def m_def intro!: map_cong)
      have "(env_ext e Ts, \<tau>') \<turnstile> Var (Suc k) \<degree>\<degree> map BVar zs1 : T"
        by (simp add: typing_Var_app_BVars \<tau>'_def eqm)
      then show ?thesis using typing_Abs_m[of e Ts \<tau>'] \<tau>F by (simp add: Ts_def m_def)
    qed
    moreover have "(e, \<tau>') \<turnstile> Abs_m n (Var (Suc k) \<degree>\<degree> map BVar zs2) : \<tau> G" for e
    proof -
      have eqm: "map (env_ext e Ss) zs2 = map (env_ext E Ss) zs2"
        using ff2_args_less(2)[OF flex_flex2(6)] by (auto simp: env_ext_less Ss_def n_def intro!: map_cong)
      have "(env_ext e Ss, \<tau>') \<turnstile> Var (Suc k) \<degree>\<degree> map BVar zs2 : T"
        by (simp add: typing_Var_app_BVars \<tau>'_def eqm eq)
      then show ?thesis using typing_Abs_m[of e Ss \<tau>'] \<tau>G by (simp add: Ss_def n_def)
    qed
    ultimately have "typed_on {..k} \<tau> \<tau>' \<mu>"
      using flex_flex2(3,9) \<tau>'k by (auto simp: typed_on_def m_def n_def)
    then show ?thesis using flex_flex2(8) by (intro that[of \<tau>']) (simp_all add: \<tau>'k)
  qed
qed


subsection \<open>Variables of a step\<close>

lemma zip_memD: "(a, b) \<in> set (zip A B) \<Longrightarrow> a \<in> set A \<and> b \<in> set B"
  by (meson set_zip_leftD set_zip_rightD)

lemma cases_vars:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)" and pats: "pat s" "pat t"
  shows "FVs us' \<subseteq> FV s \<union> FV t \<union> {k<..k'}"
    and "\<And>F. FV (\<mu> F) \<subseteq> insert F {k<..k'}"
    and "\<And>F. \<mu> F \<noteq> Var F \<Longrightarrow> F \<in> FV s \<union> FV t"
proof -
  obtain h1 as1 h2 as2 where prep: "prep (s, t) = ((h1, as1), (h2, as2))"
    by (metis prod.exhaust)
  from prep_eq[OF prep] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2"
    by blast
  have FV': "FV s' \<union> FV t' = FV s \<union> FV t"
    using otf otf\<eta>_props[of s t] pats by auto
  from cs[unfolded prep]
  have "FVs us' \<subseteq> FV s \<union> FV t \<union> {k<..k'} \<and> (\<forall>F. FV (\<mu> F) \<subseteq> insert F {k<..k'}) \<and>
    (\<forall>F. \<mu> F \<noteq> Var F \<longrightarrow> F \<in> FV s \<union> FV t)"
  proof (cases rule: cases_SomeE)
    case (rigid_rigid p)
    then show ?thesis using FV' s' t' by (auto simp: FVs_map2)
  next
    case (flex_rigid F xs p j)
    have "FVs us' \<subseteq> {k<..k'} \<union> \<Union> (FV ` set as2)"
      using flex_rigid(2,6,7) by (auto simp: FVs_def dest!: zip_memD)
    then show ?thesis using flex_rigid FV' s' t' by auto
  next
    case (flex_flex1 F xs ys)
    then show ?thesis using FV' s' by auto
  next
    case (flex_flex2 F G xs ys zs1 zs2)
    then show ?thesis using FV' s' t' by auto
  qed
  then show "FVs us' \<subseteq> FV s \<union> FV t \<union> {k<..k'}" "\<And>F. FV (\<mu> F) \<subseteq> insert F {k<..k'}"
    "\<And>F. \<mu> F \<noteq> Var F \<Longrightarrow> F \<in> FV s \<union> FV t"
    by blast+
qed

lemma more_general_unifies:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)" and pats: "pat s" "pat t"
    and W: "FV s \<union> FV t \<subseteq> W"
    and \<sigma>: "unifies \<sigma> s t"
    and \<rho>: "closed_on (W \<union> {k<..k'}) \<rho>" "\<And>F. F \<in> W \<Longrightarrow> mk_subst \<rho> (\<mu> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
  shows "unifies_all \<rho> us'"
proof -
  have "unifies (\<rho> \<circ>\<^sub>s \<mu>) s t" using \<sigma> \<rho>(2) W by (subst unifies_cong) auto
  then have "unifies \<rho> (mk_subst \<mu> s) (mk_subst \<mu> t)" by (simp add: unifies_comp)
  moreover have "closed_on (\<Union> (FV ` \<mu> ` (FV s \<union> FV t)) \<union> FVs us') \<rho>"
    using cases_vars[OF cs pats] W by (intro closed_on_mono[OF \<rho>(1)]) blast
  ultimately show ?thesis using cases_same_unifiers[OF cs pats] by blast
qed

end
