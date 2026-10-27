section \<open>Correctness of the Unification Algorithm\<close>

theory Unif_Correctness
  imports Unif_Termination Unif_Occurs
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


subsection \<open>Abstracting normal forms\<close>

text \<open>
  To show that the computed substitutions are most general, we instantiate the new variables
  with abstractions of \<open>\<beta>\<eta>\<close>-normal forms of the given unifier. The following function abstracts a
  term over the bound variables \<open>zs\<close> (the last element of \<open>zs\<close> becomes the innermost binder).
\<close>

definition abst :: "nat list \<Rightarrow> dB \<Rightarrow> dB" where
  "abst zs r = Abs_m (length zs) (map_BVars (\<lambda>v. the (idx zs v)) r)"

lemma idx_mem:
  assumes "v \<in> set zs"
  shows "idx zs v = Some (the (idx zs v))" "the (idx zs v) < length zs"
    "zs ! (length zs - Suc (the (idx zs v))) = v"
  using assms idx_None_iff[of zs v] idx_SomeD[of zs v] by auto

lemma loose_BVars_abst:
  assumes "loose_BVars r \<subseteq> set zs"
  shows "no_loose_bound (abst zs r) 0"
proof -
  have "loose_BVars (map_BVars (\<lambda>v. the (idx zs v)) r) \<subseteq> {..<length zs}"
    using assms by (auto simp: loose_BVars_map_BVars intro!: idx_mem(2))
  then show ?thesis
    by (simp add: abst_def loose_BVars_no_loose_bound)
qed

lemma appb_abst:
  assumes "loose_BVars r \<subseteq> set zs" "length ys = length zs"
  shows "appb (abst zs r) ys = map_BVars (\<lambda>v. ys ! (length zs - Suc (the (idx zs v)))) r"
proof -
  have idx: "idx zs v = Some (the (idx zs v))" "the (idx zs v) < length zs" if "v \<in> loose_BVars r" for v
    using that assms(1) idx_None_iff[of zs v] idx_SomeD[of zs v] by auto
  show ?thesis
    unfolding abst_def using assms(2) idx
    by (auto simp: appb_Abs_m map_BVars_comp intro!: map_BVars_cong)
qed

lemma appb_abst_self:
  assumes "loose_BVars r \<subseteq> set zs"
  shows "appb (abst zs r) zs = r"
proof -
  have "zs ! (length zs - Suc (the (idx zs v))) = v" if "v \<in> loose_BVars r" for v
    using that assms idx_None_iff[of zs v] idx_SomeD[of zs v] by fastforce
  then have "map_BVars (\<lambda>v. zs ! (length zs - Suc (the (idx zs v)))) r = map_BVars id r"
    by (intro map_BVars_cong) simp
  then show ?thesis using appb_abst[OF assms refl] by (simp add: map_BVars_id)
qed

lemma typing_abst:
  assumes "(env_ext e Ts, \<tau>) \<turnstile> r : T" "loose_BVars r \<subseteq> set zs"
  shows "(e, \<tau>) \<turnstile> abst zs r : map (env_ext e Ts) zs \<Rrightarrow> T"
proof -
  let ?Us = "map (env_ext e Ts) zs"
  have "(env_ext e ?Us, \<tau>) \<turnstile> map_BVars (\<lambda>v. the (idx zs v)) r : T"
  proof (rule typing_map_BVars[OF assms(1)])
    fix v assume "v \<in> loose_BVars r"
    with assms(2) obtain j where "idx zs v = Some j"
      using idx_None_iff[of zs v] by auto
    moreover from idx_SomeD[OF this] have "length zs - Suc j < length zs" "zs ! (length zs - Suc j) = v"
      by auto
    ultimately show "env_ext e ?Us (the (idx zs v)) = env_ext e Ts v"
      using idx_SomeD[OF \<open>idx zs v = Some j\<close>] by (simp add: env_ext_less)
  qed
  from typing_Abs_m[OF this] show ?thesis by (simp add: abst_def)
qed

lemma map_BVars_eq_on:
  "map_BVars f r = map_BVars g r \<Longrightarrow> v \<in> loose_BVars r \<Longrightarrow> f v = g v"
proof (induction r arbitrary: f g v)
  case (Abs r)
  from Abs.prems have "Suc v \<in> loose_BVars r" by auto
  with Abs.prems Abs.IH[of "case_nat 0 (\<lambda>a. Suc (f a))" "case_nat 0 (\<lambda>a. Suc (g a))" "Suc v"]
  show ?case by simp
qed auto

lemma map_BVars_inj_eq:
  assumes "map_BVars f a = map_BVars f b" "inj_on f (loose_BVars a \<union> loose_BVars b)"
  shows "a = b"
proof -
  let ?g = "inv_into (loose_BVars a \<union> loose_BVars b) f"
  have "map_BVars ?g (map_BVars f c) = c" if "c \<in> {a, b}" for c
  proof -
    have "map_BVars ?g (map_BVars f c) = map_BVars (?g \<circ> f) c" by (simp add: map_BVars_comp)
    also have "\<dots> = map_BVars id c"
      using assms(2) that by (intro map_BVars_cong) auto
    finally show ?thesis by (simp add: map_BVars_id)
  qed
  then have "a = map_BVars ?g (map_BVars f a)" "b = map_BVars ?g (map_BVars f b)" by auto
  with assms(1) show ?thesis by simp
qed

lemma Abs_binding_equiv:
  assumes "no_loose_bound (\<sigma> F) 0" "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar (downs m)) r" "mk_subst \<rho> b \<equiv>\<^sub>\<beta>\<^sub>\<eta> r"
  shows "mk_subst \<rho> (Abs_m m b) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
proof -
  have "mk_subst \<rho> (Abs_m m b) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m r"
    using assms(3) by (simp add: equiv_Abs_m)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m (\<sigma> F \<degree>\<degree> map BVar (downs m))"
    using assms(2) by (intro equiv_Abs_m equiv_sym[OF \<beta>\<eta>cl_into_equiv])
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F" using assms(1) by (rule eta_expand_equiv)
  finally show ?thesis .
qed

lemma flex_binding_equiv:
  assumes "no_loose_bound (\<sigma> F) 0" "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar (downs m)) r" "appb (\<rho> H) zs = r"
  shows "mk_subst \<rho> (Abs_m m (Var H \<degree>\<degree> map BVar zs)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
proof (rule Abs_binding_equiv[where \<sigma> = \<sigma> and F = F, OF assms(1,2)])
  show "mk_subst \<rho> (Var H \<degree>\<degree> map BVar zs) \<equiv>\<^sub>\<beta>\<^sub>\<eta> r"
    using appb_reduces[of "\<rho> H" zs] assms(3) by (simp add: beta_into_equiv)
qed

lemma idx_map_inj: "inj f \<Longrightarrow> idx (map f xs) (f y) = idx xs y"
  by (induction xs) (auto simp: inj_eq)

text \<open>Extending a unifier by bindings for the new variables.\<close>

lemma extend_subst:
  assumes "W \<subseteq> {..k}" "closed_on W \<sigma>" "typed_on W \<tau> \<tau>\<sigma> \<sigma>" "\<And>F. F \<le> k \<Longrightarrow> \<tau>' F = \<tau> F"
    and "\<And>G. G \<in> {k<..k'} \<Longrightarrow> no_loose_bound (\<nu> G) 0 \<and> (\<exists>e. (e, \<tau>\<sigma>) \<turnstile> \<nu> G : \<tau>' G)"
  shows "closed_on (W \<union> {k<..k'}) (\<lambda>G. if G \<in> {k<..k'} then \<nu> G else \<sigma> G)"
    "typed_on (W \<union> {k<..k'}) \<tau>' \<tau>\<sigma> (\<lambda>G. if G \<in> {k<..k'} then \<nu> G else \<sigma> G)"
    "\<And>F. F \<in> W \<Longrightarrow> (\<lambda>G. if G \<in> {k<..k'} then \<nu> G else \<sigma> G) F = \<sigma> F"
proof -
  have notin: "F \<notin> {k<..k'}" if "F \<in> W" for F using that assms(1) by auto
  show "closed_on (W \<union> {k<..k'}) (\<lambda>G. if G \<in> {k<..k'} then \<nu> G else \<sigma> G)"
    using assms(2,5) notin by (auto simp: closed_on_def)
  have "typed_on W \<tau>' \<tau>\<sigma> \<sigma>"
    using assms(1,3,4) by (auto simp: typed_on_def subset_iff)
  then show "typed_on (W \<union> {k<..k'}) \<tau>' \<tau>\<sigma> (\<lambda>G. if G \<in> {k<..k'} then \<nu> G else \<sigma> G)"
    using assms(5) notin by (intro typed_onI_closed) (auto simp: typed_on_def closed_on_def
      intro: closed_onD[OF assms(2)])
  show "\<And>F. F \<in> W \<Longrightarrow> (\<lambda>G. if G \<in> {k<..k'} then \<nu> G else \<sigma> G) F = \<sigma> F"
    using notin by auto
qed


subsection \<open>Proposition 2: the computed substitution is more general\<close>

text \<open>
  Every closed, well-typed unifier \<open>\<sigma>\<close> of \<open>s\<close> and \<open>t\<close> factors through the substitution \<open>\<mu>\<close>
  computed by a step, up to \<open>\<beta>\<eta>\<close>-equivalence: \<open>\<sigma> F \<equiv> \<rho>(\<mu> F)\<close> for all relevant \<open>F\<close>, where \<open>\<rho>\<close> is a
  closed, well-typed unifier of the new problems. Grobauer constructs \<open>\<rho>\<close> via renamings of the
  bound variables; we use \<open>\<beta>\<eta>\<close>-normal forms of \<open>\<sigma> F\<close> applied to its bound variables instead.
\<close>

proposition cases_more_general:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)" and pats: "pat s" "pat t"
    and W: "FV s \<union> FV t \<subseteq> W" "W \<subseteq> {..k}"
    and \<sigma>: "closed_on W \<sigma>" "typed_on W \<tau> \<tau>\<sigma> \<sigma>" "unifies \<sigma> s t"
    and \<tau>': "\<And>F. F \<le> k \<Longrightarrow> \<tau>' F = \<tau> F" "typed_on {..k} \<tau> \<tau>' \<mu>"
  obtains \<rho> where "\<And>F. F \<in> W \<Longrightarrow> mk_subst \<rho> (\<mu> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
    "closed_on (W \<union> {k<..k'}) \<rho>" "typed_on (W \<union> {k<..k'}) \<tau>' \<tau>\<sigma> \<rho>" "unifies_all \<rho> us'"
proof -
  obtain h1 as1 h2 as2 where prep: "prep (s, t) = ((h1, as1), (h2, as2))"
    by (metis prod.exhaust)
  from prep_eq[OF prep] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2"
    by blast
  have pats': "pat s'" "pat t'" and FV': "FV s' \<union> FV t' = FV s \<union> FV t"
    using otf otf\<eta>_props[of s t] pats by auto
  have cl: "closed_on (FV s \<union> FV t) \<sigma>" using \<sigma>(1) W(1) closed_on_mono by blast
  have u': "mk_subst \<sigma> s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t'"
    using prep_unifies[OF prep cl] \<sigma>(3) s' t' by (simp add: unifies_def)
  have \<sigma>F: "no_loose_bound (\<sigma> F) 0" "(e, \<tau>\<sigma>) \<turnstile> \<sigma> F : \<tau> F" if "F \<in> FV s' \<union> FV t'" for F e
    using that FV' W(1) closed_onD[OF \<sigma>(1)] typed_onD[OF \<sigma>(2)] by auto
  have \<mu>F: "(e, \<tau>') \<turnstile> \<mu> F : \<tau> F" if "F \<in> FV s' \<union> FV t'" for F e
    using that FV' W typed_onD[OF \<tau>'(2)] by auto
  obtain e0 :: "nat \<Rightarrow> type" where True by simp
  have "\<exists>\<rho>. (\<forall>F\<in>W. mk_subst \<rho> (\<mu> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F) \<and> closed_on (W \<union> {k<..k'}) \<rho> \<and>
    typed_on (W \<union> {k<..k'}) \<tau>' \<tau>\<sigma> \<rho>"
    using cs[unfolded prep]
  proof (cases rule: cases_SomeE)
    case (rigid_rigid p)
    have "typed_on W \<tau>' \<tau>\<sigma> \<sigma>"
      using \<sigma>(2) W(2) \<tau>'(1) by (auto simp: typed_on_def subset_iff)
    then show ?thesis using rigid_rigid \<sigma>(1) by (intro exI[of _ \<sigma>]) simp
  next
    case (flex_rigid F xs p j)
    define m where "m = length xs"
    define n where "n = length as2"
    define Hs where "Hs = map Var [Suc k..<Suc k + n]"
    define g where "g = (\<lambda>i. xs ! (m - Suc i))"
    define g' where "g' = (\<lambda>v. the (idx xs v))"
    have F: "F \<in> FV s' \<union> FV t'" using flex_rigid by (simp add: s')
    have dxs: "distinct xs" using pats' flex_rigid by (simp add: s')
    have "(e0, \<tau>') \<turnstile> Abs_m m (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs) : \<tau> F"
      using \<mu>F[OF F, of e0] by (simp add: flex_rigid(2,8) m_def n_def Hs_def)
    then obtain Ts U where Ts: "length Ts = m" "\<tau> F = Ts \<Rrightarrow> U"
      and "(env_ext e0 Ts, \<tau>') \<turnstile> BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs : U"
      by (blast dest: typing_Abs_m_D)
    then obtain Us where Us: "env_ext e0 Ts j = Us \<Rrightarrow> U"
      "(env_ext e0 Ts, \<tau>') \<tturnstile> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs : Us"
      by (auto simp: typing_BVar_app)
    have lenUs: "length Us = n" using typings_length[OF Us(2)] by (simp add: Hs_def)
    have \<tau>'H: "\<tau>' (Suc k + i) = Ts \<Rrightarrow> (Us ! i)" if "i < n" for i
    proof -
      have "(env_ext e0 Ts, \<tau>') \<turnstile> Var (Suc k + i) \<degree>\<degree> map BVar (downs m) : Us ! i"
        using typings_nth[OF Us(2), of i] that by (simp add: Hs_def)
      then show ?thesis using env_ext_downs[of e0 Ts] Ts(1) by (simp add: typing_Var_app_BVars)
    qed
    obtain r where r: "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar (downs m)) r" "normal r" "(env_ext e0 Ts, \<tau>\<sigma>) \<turnstile> r : U"
      "loose_BVars r \<subseteq> {..<m}"
      using typed_nf_args[OF \<sigma>F(1)[OF F] \<sigma>F(2)[OF F, of e0, unfolded Ts(2)] Ts(1)] .
    note ren = nf_rename_args[OF \<sigma>F(1)[OF F] r(1,2) m_def[symmetric] dxs, folded g_def]
    have "\<sigma> F \<degree>\<degree> map BVar xs \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar p \<degree>\<degree> map (mk_subst \<sigma>) as2"
      using u' flex_rigid by (simp add: s' t')
    then have "BVar p \<degree>\<degree> map (mk_subst \<sigma>) as2 \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars g r"
      using ren(1) by (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
    from atom_apps_\<beta>\<eta>cl[OF _ equiv_\<beta>\<eta>cl_normal[OF this ren(2)]] obtain cs where
      cs: "map_BVars g r = BVar p \<degree>\<degree> cs" "list_all2 \<beta>\<eta>cl (map (mk_subst \<sigma>) as2) cs"
      by auto
    have "map_BVars g' (map_BVars g r) = map_BVars id r"
      unfolding map_BVars_comp
    proof (rule map_BVars_cong)
      fix v assume "v \<in> loose_BVars r"
      then have "v < m" using r(4) by auto
      then have "m - Suc v < length xs" by (simp add: m_def)
      from idx_distinct[OF dxs this] \<open>v < m\<close> show "(g' \<circ> g) v = id v"
        by (simp add: g_def g'_def m_def)
    qed
    moreover have "g' p = j"
    proof -
      have "idx (map BVar xs) (BVar p) = idx xs p" by (rule idx_map_inj) (simp add: inj_def)
      then show ?thesis using flex_rigid(2,5) by (simp add: g'_def)
    qed
    ultimately have r_eq: "r = BVar j \<degree>\<degree> map (map_BVars g') cs"
      using cs(1) by (simp add: map_BVars_id)
    define ws where "ws = map (map_BVars g') cs"
    have lenws: "length ws = n" using list_all2_lengthD[OF cs(2)] by (simp add: ws_def n_def)
    from r(3) obtain Us' where "env_ext e0 Ts j = Us' \<Rrightarrow> U" "(env_ext e0 Ts, \<tau>\<sigma>) \<tturnstile> ws : Us'"
      by (auto simp: r_eq typing_BVar_app ws_def)
    moreover from this have "Us' = Us"
      using Us(1) lenUs lenws typings_length funs_eq_iff by metis
    ultimately have ws_ty: "(env_ext e0 Ts, \<tau>\<sigma>) \<turnstile> ws ! i : Us ! i" if "i < n" for i
      using typings_nth that lenws by metis
    have ws_loose: "loose_BVars (ws ! i) \<subseteq> set (downs m)" if "i < n" for i
    proof -
      have "ws ! i \<in> set ws" using that lenws by simp
      then show ?thesis using r(4) by (auto simp: r_eq ws_def[symmetric])
    qed
    define \<rho> where "\<rho> = (\<lambda>H. if H \<in> {k<..k'} then abst (downs m) (ws ! (H - Suc k)) else \<sigma> H)"
    have new: "no_loose_bound (abst (downs m) (ws ! (H - Suc k))) 0 \<and>
      (\<exists>e. (e, \<tau>\<sigma>) \<turnstile> abst (downs m) (ws ! (H - Suc k)) : \<tau>' H)" if "H \<in> {k<..k'}" for H
    proof -
      define i where "i = H - Suc k"
      have i: "i < n" "H = Suc k + i" using that flex_rigid(6) by (auto simp: i_def n_def)
      show ?thesis
        using loose_BVars_abst[OF ws_loose[OF i(1)]] typing_abst[OF ws_ty[OF i(1)] ws_loose[OF i(1)]]
          env_ext_downs[of e0 Ts] Ts(1) \<tau>'H[OF i(1)] by (auto simp: i(2) i_def[symmetric])
    qed
    note ext = extend_subst[where k' = k' and \<nu> = "\<lambda>H. abst (downs m) (ws ! (H - Suc k))",
      OF W(2) \<sigma>(1,2) \<tau>'(1) new, folded \<rho>_def]
    have "mk_subst \<rho> (\<mu> F') \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F'" if "F' \<in> W" for F'
    proof (cases "F' = F")
      case True
      have "mk_subst \<rho> (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs) \<equiv>\<^sub>\<beta>\<^sub>\<eta> r"
        unfolding r_eq ws_def[symmetric] mk_subst_list_app
      proof (rule equiv_list_app)
        show "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (mk_subst \<rho>) (map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs)) ws"
        proof (rule list_all2_all_nthI)
          fix i assume "i < length (map (mk_subst \<rho>) (map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs))"
          then have i: "i < n" by (simp add: Hs_def)
          then have "\<rho> (Suc k + i) = abst (downs m) (ws ! i)"
            using flex_rigid(6) by (simp add: \<rho>_def n_def)
          then have "map (mk_subst \<rho>) (map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs) ! i =
            abst (downs m) (ws ! i) \<degree>\<degree> map BVar (downs m)"
            using i by (simp add: Hs_def)
          also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> appb (abst (downs m) (ws ! i)) (downs m)"
            by (rule beta_into_equiv[OF appb_reduces])
          also have "\<dots> = ws ! i" by (rule appb_abst_self[OF ws_loose[OF i]])
          finally show "map (mk_subst \<rho>) (map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs) ! i \<equiv>\<^sub>\<beta>\<^sub>\<eta> ws ! i" .
        qed (simp add: Hs_def lenws)
      qed simp
      from Abs_binding_equiv[where \<sigma> = \<sigma> and F = F, OF \<sigma>F(1)[OF F] r(1) this] show ?thesis
        using True flex_rigid(2,8) by (simp add: m_def n_def Hs_def)
    next
      case False
      have "\<rho> F' = \<sigma> F'" using that W(2) by (auto simp: \<rho>_def)
      then show ?thesis using False flex_rigid(8) by simp
    qed
    then show ?thesis using ext(1,2) by blast
  next
    case (flex_flex1 F xs ys)
    define m where "m = length xs"
    define zs where "zs = ff1_args xs ys"
    have F: "F \<in> FV s' \<union> FV t'" using flex_flex1 by (simp add: s')
    have dxs: "distinct xs" "distinct ys" using pats' flex_flex1 by (simp_all add: s' t')
    have "(e0, \<tau>') \<turnstile> Abs_m m (Var (Suc k) \<degree>\<degree> map BVar zs) : \<tau> F"
      using \<mu>F[OF F, of e0] by (simp add: flex_flex1 m_def zs_def)
    then obtain Ts U where Ts: "length Ts = m" "\<tau> F = Ts \<Rrightarrow> U"
      and "(env_ext e0 Ts, \<tau>') \<turnstile> Var (Suc k) \<degree>\<degree> map BVar zs : U"
      by (blast dest: typing_Abs_m_D)
    then have \<tau>'k: "\<tau>' (Suc k) = map (env_ext e0 Ts) zs \<Rrightarrow> U" by (simp add: typing_Var_app_BVars)
    obtain r where r: "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar (downs m)) r" "normal r" "(env_ext e0 Ts, \<tau>\<sigma>) \<turnstile> r : U"
      "loose_BVars r \<subseteq> {..<m}"
      using typed_nf_args[OF \<sigma>F(1)[OF F] \<sigma>F(2)[OF F, of e0, unfolded Ts(2)] Ts(1)] .
    have "map_BVars (\<lambda>i. xs ! (m - Suc i)) r = map_BVars (\<lambda>i. ys ! (m - Suc i)) r"
    proof (rule normal_form_unique)
      show "\<sigma> F \<degree>\<degree> map BVar xs \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F \<degree>\<degree> map BVar ys" using u' flex_flex1 by (simp add: s' t')
      show "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar xs) (map_BVars (\<lambda>i. xs ! (m - Suc i)) r)"
        "normal (map_BVars (\<lambda>i. xs ! (m - Suc i)) r)"
        using nf_rename_args[OF \<sigma>F(1)[OF F] r(1,2)] dxs by (simp_all add: m_def)
      show "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar ys) (map_BVars (\<lambda>i. ys ! (m - Suc i)) r)"
        "normal (map_BVars (\<lambda>i. ys ! (m - Suc i)) r)"
        using nf_rename_args[OF \<sigma>F(1)[OF F] r(1,2)] dxs flex_flex1(5) by (simp_all add: m_def)
    qed
    then have loose: "loose_BVars r \<subseteq> set zs"
    proof (intro subsetI)
      fix v assume v: "v \<in> loose_BVars r"
      have "xs ! (m - Suc v) = ys ! (m - Suc v)"
        using map_BVars_eq_on[OF \<open>map_BVars _ r = _\<close> v] .
      moreover have "v < m" using v r(4) by auto
      ultimately have "m - Suc v \<in> set (filter (\<lambda>i. xs ! i = ys ! i) [0..<m])" by auto
      moreover have "v = m - 1 - (m - Suc v)" using \<open>v < m\<close> by simp
      ultimately have "v \<in> (\<lambda>i. m - 1 - i) ` set (filter (\<lambda>i. xs ! i = ys ! i) [0..<m])"
        by (rule rev_image_eqI)
      then show "v \<in> set zs" by (simp add: zs_def ff1_args_def m_def)
    qed
    define \<rho> where "\<rho> = (\<lambda>G. if G \<in> {k<..k'} then abst zs r else \<sigma> G)"
    have new: "no_loose_bound (abst zs r) 0 \<and> (\<exists>e. (e, \<tau>\<sigma>) \<turnstile> abst zs r : \<tau>' G)" if "G \<in> {k<..k'}" for G
    proof -
      have "G = Suc k" using that flex_flex1(6) by auto
      then show ?thesis using loose_BVars_abst[OF loose] typing_abst[OF r(3) loose] \<tau>'k by auto
    qed
    note ext = extend_subst[where k' = k' and \<nu> = "\<lambda>_. abst zs r", OF W(2) \<sigma>(1,2) \<tau>'(1) new,
      folded \<rho>_def]
    have "mk_subst \<rho> (\<mu> F') \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F'" if "F' \<in> W" for F'
    proof (cases "F' = F")
      case True
      have "appb (\<rho> (Suc k)) zs = r"
        using appb_abst_self[OF loose] flex_flex1(6) by (simp add: \<rho>_def)
      from flex_binding_equiv[where \<sigma> = \<sigma> and F = F and \<rho> = \<rho> and H = "Suc k",
        OF \<sigma>F(1)[OF F] r(1) this] show ?thesis
        using True flex_flex1(8) by (simp add: m_def zs_def)
    next
      case False
      have "\<rho> F' = \<sigma> F'" using that W(2) by (auto simp: \<rho>_def)
      then show ?thesis using False flex_flex1(8) by simp
    qed
    then show ?thesis using ext(1,2) by blast
  next
    case (flex_flex2 F G xs ys zs1 zs2)
    define m where "m = length xs"
    define n where "n = length ys"
    define gx where "gx = (\<lambda>i. xs ! (m - Suc i))"
    define gy where "gy = (\<lambda>i. ys ! (n - Suc i))"
    have F: "F \<in> FV s' \<union> FV t'" and G: "G \<in> FV s' \<union> FV t'" using flex_flex2 by (simp_all add: s' t')
    have dxs: "distinct xs" "distinct ys" using pats' flex_flex2 by (simp_all add: s' t')
    have "(e0, \<tau>') \<turnstile> Abs_m m (Var (Suc k) \<degree>\<degree> map BVar zs1) : \<tau> F"
      using \<mu>F[OF F, of e0] flex_flex2(3) by (simp add: flex_flex2(9) m_def)
    then obtain Ts U where Ts: "length Ts = m" "\<tau> F = Ts \<Rrightarrow> U"
      and "(env_ext e0 Ts, \<tau>') \<turnstile> Var (Suc k) \<degree>\<degree> map BVar zs1 : U"
      by (blast dest: typing_Abs_m_D)
    then have \<tau>'k: "\<tau>' (Suc k) = map (env_ext e0 Ts) zs1 \<Rrightarrow> U" by (simp add: typing_Var_app_BVars)
    have "(e0, \<tau>') \<turnstile> Abs_m n (Var (Suc k) \<degree>\<degree> map BVar zs2) : \<tau> G"
      using \<mu>F[OF G, of e0] by (simp add: flex_flex2(9) n_def)
    then obtain Ss U' where Ss: "length Ss = n" "\<tau> G = Ss \<Rrightarrow> U'"
      by (blast dest: typing_Abs_m_D)
    obtain rF where rF: "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar (downs m)) rF" "normal rF" "(env_ext e0 Ts, \<tau>\<sigma>) \<turnstile> rF : U"
      "loose_BVars rF \<subseteq> {..<m}"
      using typed_nf_args[OF \<sigma>F(1)[OF F] \<sigma>F(2)[OF F, of e0, unfolded Ts(2)] Ts(1)] .
    obtain rG where rG: "\<beta>\<eta>cl (\<sigma> G \<degree>\<degree> map BVar (downs n)) rG" "normal rG"
      "(env_ext e0 Ss, \<tau>\<sigma>) \<turnstile> rG : U'" "loose_BVars rG \<subseteq> {..<n}"
      using typed_nf_args[OF \<sigma>F(1)[OF G] \<sigma>F(2)[OF G, of e0, unfolded Ss(2)] Ss(1)] .
    have eq: "map_BVars gx rF = map_BVars gy rG"
    proof (rule normal_form_unique)
      show "\<sigma> F \<degree>\<degree> map BVar xs \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> G \<degree>\<degree> map BVar ys" using u' flex_flex2 by (simp add: s' t')
      show "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar xs) (map_BVars gx rF)" "normal (map_BVars gx rF)"
        using nf_rename_args[OF \<sigma>F(1)[OF F] rF(1,2)] dxs by (simp_all add: m_def gx_def)
      show "\<beta>\<eta>cl (\<sigma> G \<degree>\<degree> map BVar ys) (map_BVars gy rG)" "normal (map_BVars gy rG)"
        using nf_rename_args[OF \<sigma>F(1)[OF G] rG(1,2)] dxs by (simp_all add: n_def gy_def)
    qed
    have loose: "loose_BVars rF \<subseteq> set zs1"
    proof
      fix v assume v: "v \<in> loose_BVars rF"
      then have "gx v \<in> loose_BVars (map_BVars gy rG)"
        unfolding eq[symmetric] loose_BVars_map_BVars by blast
      then obtain w where w: "w \<in> loose_BVars rG" "xs ! (m - Suc v) = ys ! (n - Suc w)"
        by (auto simp: loose_BVars_map_BVars gx_def gy_def)
      have "v < m" "w < n" using v w(1) rF(4) rG(4) by auto
      then have "n - Suc w < n" "m - Suc v < m" by arith+
      then have mem: "n - Suc w \<in> set (filter (\<lambda>i. ys ! i \<in> set xs) [0..<n])"
        using w(2) by (auto simp flip: w(2) simp: m_def)
      have "idx xs (ys ! (n - Suc w)) = Some v"
        using idx_distinct[OF dxs(1) \<open>m - Suc v < m\<close>[unfolded m_def]] \<open>v < m\<close> w(2)
        by (simp add: m_def)
      then have "v = the (idx xs (ys ! (n - Suc w)))" by simp
      with mem have "v \<in> (\<lambda>i. the (idx xs (ys ! i))) ` set (filter (\<lambda>i. ys ! i \<in> set xs) [0..<n])"
        by (rule rev_image_eqI)
      moreover have "zs1 = map (\<lambda>i. the (idx xs (ys ! i))) (filter (\<lambda>i. ys ! i \<in> set xs) [0..<n])"
        using flex_flex2(6) by (simp add: ff2_args_def Let_def n_def)
      ultimately show "v \<in> set zs1" by (simp only: set_map)
    qed
    define \<rho> where "\<rho> = (\<lambda>H. if H \<in> {k<..k'} then abst zs1 rF else \<sigma> H)"
    have new: "no_loose_bound (abst zs1 rF) 0 \<and> (\<exists>e. (e, \<tau>\<sigma>) \<turnstile> abst zs1 rF : \<tau>' H)" if "H \<in> {k<..k'}" for H
    proof -
      have "H = Suc k" using that flex_flex2(7) by auto
      then show ?thesis using loose_BVars_abst[OF loose] typing_abst[OF rF(3) loose] \<tau>'k by auto
    qed
    note ext = extend_subst[where k' = k' and \<nu> = "\<lambda>_. abst zs1 rF", OF W(2) \<sigma>(1,2) \<tau>'(1) new,
      folded \<rho>_def]
    have \<rho>k: "\<rho> (Suc k) = abst zs1 rF" using flex_flex2(7) by (simp add: \<rho>_def)
    have appbG: "appb (\<rho> (Suc k)) zs2 = rG"
    proof (rule map_BVars_inj_eq)
      define L where "L = length zs1"
      have lens: "length zs2 = L" using ff2_args_length[OF flex_flex2(6)] by (simp add: L_def)
      have appb: "appb (\<rho> (Suc k)) zs2 = map_BVars (\<lambda>v. zs2 ! (L - Suc (the (idx zs1 v)))) rF"
        unfolding \<rho>k L_def using appb_abst[OF loose] lens by (simp add: L_def)
      have "gy (zs2 ! (L - Suc (the (idx zs1 v)))) = gx v" if "v \<in> loose_BVars rF" for v
      proof -
        have v: "v \<in> set zs1" using that loose by blast
        let ?q = "L - Suc (the (idx zs1 v))"
        have q: "?q < L" "zs1 ! ?q = v" using idx_mem[OF v] by (auto simp: L_def)
        have "map (\<lambda>z. xs ! (m - Suc z)) zs1 ! ?q = map (\<lambda>z. ys ! (n - Suc z)) zs2 ! ?q"
          using ff2_args_eq[OF flex_flex2(6)] by (simp add: m_def n_def)
        then show ?thesis using q lens by (simp add: gx_def gy_def L_def)
      qed
      then have "map_BVars gy (appb (\<rho> (Suc k)) zs2) = map_BVars gx rF"
        unfolding appb map_BVars_comp by (intro map_BVars_cong) simp
      then show "map_BVars gy (appb (\<rho> (Suc k)) zs2) = map_BVars gy rG" using eq by simp
      have "zs2 ! (L - Suc (the (idx zs1 v))) \<in> set zs2" if "v \<in> loose_BVars rF" for v
        using idx_mem(2)[of v zs1] that loose lens by (intro nth_mem) (auto simp: L_def)
      then have "loose_BVars (appb (\<rho> (Suc k)) zs2) \<subseteq> set zs2"
        unfolding appb loose_BVars_map_BVars by blast
      then have "loose_BVars (appb (\<rho> (Suc k)) zs2) \<union> loose_BVars rG \<subseteq> {..<n}"
        using ff2_args_less(2)[OF flex_flex2(6)] rG(4) by (auto simp: n_def)
      moreover have "inj_on gy {..<n}"
        using dxs(2) by (auto simp: inj_on_def gy_def n_def nth_eq_iff_index_eq)
      ultimately show "inj_on gy (loose_BVars (appb (\<rho> (Suc k)) zs2) \<union> loose_BVars rG)"
        by (rule inj_on_subset[rotated])
    qed
    have "mk_subst \<rho> (\<mu> F') \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F'" if "F' \<in> W" for F'
    proof -
      consider "F' = F" | "F' = G" | "F' \<noteq> F" "F' \<noteq> G" by blast
      then show ?thesis
      proof cases
        case 1
        have "appb (\<rho> (Suc k)) zs1 = rF" using appb_abst_self[OF loose] by (simp add: \<rho>k)
        from flex_binding_equiv[where \<sigma> = \<sigma> and F = F and \<rho> = \<rho> and H = "Suc k",
            OF \<sigma>F(1)[OF F] rF(1) this]
        show ?thesis using 1 flex_flex2(3,9) by (simp add: m_def)
      next
        case 2
        from flex_binding_equiv[where \<sigma> = \<sigma> and F = G and \<rho> = \<rho> and H = "Suc k",
            OF \<sigma>F(1)[OF G] rG(1) appbG]
        show ?thesis using 2 flex_flex2(9) by (simp add: n_def)
      next
        case 3
        have "\<rho> F' = \<sigma> F'" using that W(2) by (auto simp: \<rho>_def)
        then show ?thesis using 3 flex_flex2(9) by simp
      qed
    qed
    then show ?thesis using ext(1,2) by blast
  qed
  then obtain \<rho> where \<rho>: "\<And>F. F \<in> W \<Longrightarrow> mk_subst \<rho> (\<mu> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
    "closed_on (W \<union> {k<..k'}) \<rho>" "typed_on (W \<union> {k<..k'}) \<tau>' \<tau>\<sigma> \<rho>"
    by blast
  moreover have "unifies_all \<rho> us'"
    using more_general_unifies[OF cs pats W(1) \<sigma>(3) \<rho>(2,1)] .
  ultimately show ?thesis using that by blast
qed


subsection \<open>Proposition 4: failure means there is no unifier\<close>

lemma otf\<eta>_not_Abs: "otf\<eta> (s, t) = (s', t') \<Longrightarrow> s' \<noteq> Abs u \<and> t' \<noteq> Abs u"
proof -
  have "fst (otf\<eta> (s, t)) \<noteq> Abs u \<and> snd (otf\<eta> (s, t)) \<noteq> Abs u"
    by (induction s t rule: otf\<eta>_induct) auto
  then show "otf\<eta> (s, t) = (s', t') \<Longrightarrow> s' \<noteq> Abs u \<and> t' \<noteq> Abs u" by simp
qed

lemma prep_rigid_left:
  assumes "prep (s, t) = ((h1, as1), (h2, as2))" "\<And>F. h1 \<noteq> Var F"
  shows "h2 \<noteq> Var G"
proof -
  obtain a b where ab: "otf\<eta> (s, t) = (a, b)" by fastforce
  obtain ha aa where a: "dest_comb a = (ha, aa)" by fastforce
  show ?thesis
  proof (cases "\<exists>F. ha = Var F")
    case True
    then have "h1 = ha" using assms(1) ab a by (auto simp: prep_def)
    with True assms(2) show ?thesis by blast
  next
    case False
    then have "tw (a, b) = (b, a)" using a by (cases ha) auto
    then have "h2 = ha" using assms(1) ab a by (auto simp: prep_def)
    with False show ?thesis by blast
  qed
qed

lemma pat_dest_comb:
  assumes "pat s" "s = h \<degree>\<degree> as" "\<And>u1 u2. h \<noteq> u1 \<degree> u2" "\<And>u. s \<noteq> Abs u"
  obtains (rigid) p where "h = BVar p" "\<forall>a\<in>set as. pat a"
  | (flex) F xs where "h = Var F" "as = map BVar xs" "distinct xs"
proof -
  have dc: "dest_comb s = (h, as)" using assms(2,3) by (simp add: dest_comb_eq_iff)
  from assms(1) show ?thesis
  proof (cases rule: pat_cases)
    case (BVar x ts)
    then show ?thesis using dc by (intro rigid[of x]) auto
  next
    case (Var F xs)
    then show ?thesis using dc by (intro flex[of F xs]) auto
  qed (use assms(4) in blast)
qed

proposition cases_None:
  assumes cs: "cases k (prep (s, t)) = None" and pats: "pat s" "pat t" and typed: "typed_prob \<tau> s t"
    and \<sigma>: "closed_on (FV s \<union> FV t) \<sigma>" "typed_on (FV s \<union> FV t) \<tau> \<tau>\<sigma> \<sigma>"
  shows "\<not> unifies \<sigma> s t"
proof
  assume u: "unifies \<sigma> s t"
  obtain h1 as1 h2 as2 where prep: "prep (s, t) = ((h1, as1), (h2, as2))"
    by (metis prod.exhaust)
  from prep_eq[OF prep] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2" and
    h: "\<And>u1 u2. h1 \<noteq> u1 \<degree> u2" "\<And>u1 u2. h2 \<noteq> u1 \<degree> u2"
    by blast
  have pats': "pat s'" "pat t'" and FV': "FV s' \<union> FV t' = FV s \<union> FV t"
    using otf otf\<eta>_props[of s t] pats by auto
  have notAbs: "s' \<noteq> Abs u" "t' \<noteq> Abs u" for u using otf otf\<eta>_not_Abs by blast+
  have u': "mk_subst \<sigma> s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t'"
    using prep_unifies[OF prep \<sigma>(1)] u s' t' by (simp add: unifies_def)
  from prep_typing[OF prep typed] obtain E T where
    ty: "(E, \<tau>) \<turnstile> s' : T" "(E, \<tau>) \<turnstile> t' : T"
    by (auto simp: typed_prob_def s' t')
  have cs': "cases k ((h1, as1), (h2, as2)) = None" using cs prep by simp
  from pats'(1) s' h(1) notAbs(1) show False
  proof (cases rule: pat_dest_comb)
    case (rigid p)
    have "\<forall>G. h2 \<noteq> Var G" using prep_rigid_left[OF prep] rigid(1) by blast
    with pats'(2) t' h(2) notAbs(2) obtain q where q: "h2 = BVar q"
      by (cases rule: pat_dest_comb) auto
    have "unifies \<sigma> (BVar p \<degree>\<degree> as1) (BVar q \<degree>\<degree> as2)"
      using u' by (simp add: unifies_def s' t' rigid q)
    then have "p = q \<and> length as1 = length as2"
      by (auto simp: unifies_BVar_apps dest: list_all2_lengthD)
    with cs' show False by (simp add: rigid q)
  next
    case (flex F xs)
    from pats'(2) t' h(2) notAbs(2) show False
    proof (cases rule: pat_dest_comb)
      case (rigid p)
      have "F \<in> \<Union> (FV ` set as2) \<or> p \<notin> set xs"
        using cs' by (auto simp: flex rigid Let_def idx_None_iff split: option.splits)
      then show False
      proof
        assume F: "F \<in> \<Union> (FV ` set as2)"
        have FVt': "\<Union> (FV ` set as2) \<subseteq> FV s \<union> FV t" using FV' t' by auto
        have "\<not> mk_subst \<sigma> (Var F \<degree>\<degree> map BVar xs) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (BVar p \<degree>\<degree> as2)"
          using occurs_check[OF flex(3) rigid(2) F] ty closed_on_mono[OF \<sigma>(1) FVt']
            typed_on_mono[OF \<sigma>(2) FVt'] by (simp add: s' t' flex rigid)
        with u' show False by (simp add: s' t' flex rigid)
      next
        assume p: "p \<notin> set xs"
        define m where "m = length xs"
        define g where "g = (\<lambda>i. xs ! (m - Suc i))"
        have F: "F \<in> FV s \<union> FV t" using FV' s' flex by auto
        have \<tau>F: "\<tau> F = map E xs \<Rrightarrow> T" using ty(1) by (simp add: s' flex typing_Var_app_BVars)
        have \<sigma>F: "no_loose_bound (\<sigma> F) 0" "(E, \<tau>\<sigma>) \<turnstile> \<sigma> F : map E xs \<Rrightarrow> T"
          using closed_onD[OF \<sigma>(1) F] typed_onD[OF \<sigma>(2) F] \<tau>F by auto
        have lenm: "length (map E xs) = m" by (simp add: m_def)
        obtain r where r: "\<beta>\<eta>cl (\<sigma> F \<degree>\<degree> map BVar (downs m)) r" "normal r"
          "(env_ext E (map E xs), \<tau>\<sigma>) \<turnstile> r : T" "loose_BVars r \<subseteq> {..<m}"
          using typed_nf_args[OF \<sigma>F lenm] .
        note ren = nf_rename_args[OF \<sigma>F(1) r(1,2) m_def[symmetric] flex(3), folded g_def]
        have "BVar p \<degree>\<degree> map (mk_subst \<sigma>) as2 \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars g r"
          using u' ren(1) by (simp add: s' t' flex rigid) (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
        from atom_apps_\<beta>\<eta>cl[OF _ equiv_\<beta>\<eta>cl_normal[OF this ren(2)]] obtain cs where
          "map_BVars g r = BVar p \<degree>\<degree> cs" by auto
        then have "p \<in> loose_BVars (map_BVars g r)" by simp
        then obtain i where "i \<in> loose_BVars r" "p = g i" by (auto simp: loose_BVars_map_BVars)
        moreover from this have "i < m" using r(4) by auto
        ultimately have "p \<in> set xs" by (simp add: g_def m_def)
        with p show False by simp
      qed
    next
      case (flex G ys)
      have "length xs \<noteq> length ys" and FG: "F = G"
        using cs' by (auto simp: \<open>h1 = Var F\<close> \<open>as1 = map BVar xs\<close> flex Let_def split: if_splits prod.splits)
      moreover have "map E xs \<Rrightarrow> T = map E ys \<Rrightarrow> T"
        using ty \<open>h1 = Var F\<close> \<open>as1 = map BVar xs\<close> flex FG by (simp add: s' t' typing_Var_app_BVars)
      ultimately show False using funs_eq_length by fastforce
    qed
  qed
qed


subsection \<open>Propositions 5--7: correctness of \<open>unif\<close>\<close>

text \<open>
  A closed, well-typed unifier of a problem list, defined on a set \<open>W\<close> of variables that covers
  the free variables of the problems and consists of variables in use (bounded by \<open>k\<close>).
\<close>

definition solves :: "nat \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> unif_problem list \<Rightarrow> nat set \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow>
    (nat \<Rightarrow> type) \<Rightarrow> bool" where
  "solves k \<tau> us W \<sigma> \<tau>\<sigma> \<longleftrightarrow>
    FVs us \<subseteq> W \<and> W \<subseteq> {..k} \<and> closed_on W \<sigma> \<and> typed_on W \<tau> \<tau>\<sigma> \<sigma> \<and> unifies_all \<sigma> us"

lemma solves_Marker[simp]: "solves k \<tau> (Marker # us) W \<sigma> \<tau>\<sigma> = solves k \<tau> us W \<sigma> \<tau>\<sigma>"
  by (simp add: solves_def)

abbreviation map_subst :: "(nat \<Rightarrow> dB) \<Rightarrow> unif_problem list \<Rightarrow> unif_problem list" where
  "map_subst \<mu> \<equiv> map (map_unif_problem (\<lambda>u. \<beta>_nf (mk_subst \<mu> u)))"

lemma typed_list_map_subst:
  assumes "typed_list \<tau> us" "FVs us \<subseteq> V" "typed_on V \<tau> \<tau>' \<mu>"
  shows "typed_list \<tau>' (map_subst \<mu> us)"
proof -
  have "typed_prob \<tau>' (\<beta>_nf (mk_subst \<mu> a)) (\<beta>_nf (mk_subst \<mu> b))" if "(a, b) \<in> set (probs us)" for a b
  proof -
    from assms(1) that obtain e T where "(e, \<tau>) \<turnstile> a : T" "(e, \<tau>) \<turnstile> b : T"
      by (auto simp: typed_list_def typed_prob_def)
    moreover have "typed_on (FV a) \<tau> \<tau>' \<mu>" "typed_on (FV b) \<tau> \<tau>' \<mu>"
      using that assms(2,3) by (auto simp: FVs_def intro: typed_on_mono)
    ultimately show ?thesis
      unfolding typed_prob_def by (blast intro: \<beta>_nf_typing typing_mk_subst)
  qed
  then show ?thesis by (auto simp: typed_list_def)
qed

lemma unifies_all_map_subst:
  assumes "closed_on (\<Union> (FV ` \<mu> ` FVs us)) \<rho>"
  shows "unifies_all \<rho> (map_subst \<mu> us) \<longleftrightarrow> unifies_all (\<rho> \<circ>\<^sub>s \<mu>) us"
proof -
  have "unifies \<rho> (\<beta>_nf (mk_subst \<mu> a)) (\<beta>_nf (mk_subst \<mu> b)) \<longleftrightarrow> unifies (\<rho> \<circ>\<^sub>s \<mu>) a b"
    if "(a, b) \<in> set (probs us)" for a b
  proof -
    have "closed_on (FV (mk_subst \<mu> a) \<union> FV (mk_subst \<mu> b)) \<rho>"
      using that assms by (auto simp: FV_mk_subst FVs_def intro: closed_on_mono)
    then show ?thesis by (simp add: unifies_\<beta>_nf unifies_comp)
  qed
  then show ?thesis by (fastforce simp: unifies_all_def)
qed

text \<open>A successful step preserves typing and the free variables are as expected.\<close>

lemma step_vars:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)" and pats: "pat s" "pat t"
    and W: "FVs (Problem s t # us) \<subseteq> W"
  shows "FVs (us' @ map_subst \<mu> us) \<subseteq> W \<union> {k<..k'}"
proof -
  have "FVs (map_subst \<mu> us) \<subseteq> \<Union> (FV ` \<mu> ` FVs us)" by (rule map_subst_FVs)
  also have "\<dots> \<subseteq> W \<union> {k<..k'}" using cases_vars(2)[OF cs pats] W by fastforce
  finally have "FVs (map_subst \<mu> us) \<subseteq> W \<union> {k<..k'}" .
  moreover have "FVs us' \<subseteq> W \<union> {k<..k'}" using cases_vars(1)[OF cs pats] W by auto
  ultimately show ?thesis by simp
qed

lemma step_solves:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)" and pats: "pat s" "pat t"
    and \<tau>': "\<forall>F\<le>k. \<tau>' F = \<tau> F" "typed_on {..k} \<tau> \<tau>' \<mu>"
    and sol: "solves k \<tau> (Problem s t # us) W \<sigma> \<tau>\<sigma>"
  obtains \<rho> where "solves k' \<tau>' (us' @ map_subst \<mu> us) (W \<union> {k<..k'}) \<rho> \<tau>\<sigma>"
    "\<And>F. F \<in> W \<Longrightarrow> mk_subst \<rho> (\<mu> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
proof -
  from sol have W: "FV s \<union> FV t \<union> FVs us \<subseteq> W" "W \<subseteq> {..k}" and \<sigma>: "closed_on W \<sigma>"
    "typed_on W \<tau> \<tau>\<sigma> \<sigma>" "unifies \<sigma> s t" "unifies_all \<sigma> us"
    by (auto simp: solves_def)
  obtain \<rho> where \<rho>: "\<And>F. F \<in> W \<Longrightarrow> mk_subst \<rho> (\<mu> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
    "closed_on (W \<union> {k<..k'}) \<rho>" "typed_on (W \<union> {k<..k'}) \<tau>' \<tau>\<sigma> \<rho>" "unifies_all \<rho> us'"
    using cases_more_general[OF cs pats _ W(2) \<sigma>(1,2,3) \<tau>'(1)[rule_format] \<tau>'(2)] W(1) by blast
  have FV\<mu>: "\<Union> (FV ` \<mu> ` FVs us) \<subseteq> W \<union> {k<..k'}" using cases_vars(2)[OF cs pats] W(1) by fastforce
  have "unifies_all (\<rho> \<circ>\<^sub>s \<mu>) us"
    unfolding unifies_all_def
  proof safe
    fix a b assume ab: "(a, b) \<in> set (probs us)"
    then have "FV a \<union> FV b \<subseteq> W" using W(1) by (auto simp: FVs_def)
    then have "unifies (\<rho> \<circ>\<^sub>s \<mu>) a b \<longleftrightarrow> unifies \<sigma> a b"
      using \<rho>(1) by (intro unifies_cong) auto
    with \<sigma>(4) ab show "unifies (\<rho> \<circ>\<^sub>s \<mu>) a b" by (auto simp: unifies_all_def)
  qed
  then have "unifies_all \<rho> (map_subst \<mu> us)"
    using unifies_all_map_subst closed_on_mono[OF \<rho>(2) FV\<mu>] by blast
  moreover have "k \<le> k'" using cases_closed(2)[OF cs pats] .
  moreover have "FVs (us' @ map_subst \<mu> us) \<subseteq> W \<union> {k<..k'}"
    by (rule step_vars[OF cs pats]) (use W(1) in simp)
  ultimately have "solves k' \<tau>' (us' @ map_subst \<mu> us) (W \<union> {k<..k'}) \<rho> \<tau>\<sigma>"
    using \<rho>(2,3,4) W(2) by (auto simp: solves_def)
  with \<rho>(1) show ?thesis using that by blast
qed

lemma step_unifies:
  assumes cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)" and pats: "pat s" "pat t"
    and \<psi>: "closed_on UNIV \<psi>" "unifies_all \<psi> (us' @ map_subst \<mu> us)"
  shows "unifies_all (\<psi> \<circ>\<^sub>s \<mu>) (Problem s t # us)"
proof -
  have "unifies \<psi> (mk_subst \<mu> s) (mk_subst \<mu> t)"
    using cases_same_unifiers[OF cs pats closed_on_mono[OF \<psi>(1)]] \<psi>(2) by simp
  moreover have "unifies_all (\<psi> \<circ>\<^sub>s \<mu>) us"
    using unifies_all_map_subst[OF closed_on_mono[OF \<psi>(1)]] \<psi>(2) by simp
  ultimately show ?thesis by (simp add: unifies_comp)
qed

theorem unif_correct:
  assumes "unif_dom (k, us, \<phi>)" "inv k fr us" "typed_list \<tau> us"
  shows "case unif k us \<phi> of
      None \<Rightarrow> (\<forall>W \<sigma> \<tau>\<sigma>. \<not> solves k \<tau> us W \<sigma> \<tau>\<sigma>)
    | Some \<phi>' \<Rightarrow> (\<exists>\<psi>. \<phi>' = \<psi> \<circ>\<^sub>s \<phi> \<and> closed_on UNIV \<psi> \<and> unifies_all \<psi> us \<and>
        (\<forall>W \<sigma> \<tau>\<sigma>. solves k \<tau> us W \<sigma> \<tau>\<sigma> \<longrightarrow> (\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> (\<psi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F)))"
  using assms
proof (induction k us \<phi> arbitrary: fr \<tau> rule: unif.pinduct)
  case (1 k \<phi>)
  have "\<exists>\<psi>. \<phi> = \<psi> \<circ>\<^sub>s \<phi> \<and> closed_on UNIV \<psi> \<and> unifies_all \<psi> [] \<and>
    (\<forall>W \<sigma> \<tau>\<sigma>. solves k \<tau> [] W \<sigma> \<tau>\<sigma> \<longrightarrow> (\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> (\<psi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F))"
  proof (rule exI[of _ Var], intro conjI allI impI)
    show "closed_on UNIV Var" by (simp add: closed_on_def)
    show "\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> (Var F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F" for W \<sigma> by (rule exI[of _ \<sigma>]) simp
  qed simp_all
  then show ?case using 1(1) by (simp add: unif.psimps)
next
  case (2 k us \<phi>)
  have "inv k fr us" using unif_step_Marker(1)[OF 2(3)] .
  moreover have "typed_list \<tau> us" using 2(4) by simp
  ultimately have "case unif k us \<phi> of
      None \<Rightarrow> (\<forall>W \<sigma> \<tau>\<sigma>. \<not> solves k \<tau> us W \<sigma> \<tau>\<sigma>)
    | Some \<phi>' \<Rightarrow> (\<exists>\<psi>. \<phi>' = \<psi> \<circ>\<^sub>s \<phi> \<and> closed_on UNIV \<psi> \<and> unifies_all \<psi> us \<and>
        (\<forall>W \<sigma> \<tau>\<sigma>. solves k \<tau> us W \<sigma> \<tau>\<sigma> \<longrightarrow> (\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> (\<psi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F)))"
    by (rule 2(2))
  moreover have "unif k (Marker # us) \<phi> = unif k us \<phi>" by (simp add: unif.psimps 2(1))
  ultimately show ?case unfolding solves_Marker unifies_all_simps by simp
next
  case (3 k s t us \<phi>)
  note D = inv_ProblemD[OF 3(3)]
  have tyst: "typed_prob \<tau> s t" "typed_list \<tau> us" using 3(4) by simp_all
  show ?case
  proof (cases "cases k (prep (s, t))")
    case None
    have "\<not> solves k \<tau> (Problem s t # us) W \<sigma> \<tau>\<sigma>" for W \<sigma> \<tau>\<sigma>
    proof
      assume "solves k \<tau> (Problem s t # us) W \<sigma> \<tau>\<sigma>"
      then have "closed_on (FV s \<union> FV t) \<sigma>" "typed_on (FV s \<union> FV t) \<tau> \<tau>\<sigma> \<sigma>" "unifies \<sigma> s t"
        by (auto simp: solves_def intro: closed_on_mono typed_on_mono)
      with cases_None[OF None D(1,2) tyst(1)] show False by blast
    qed
    then show ?thesis using None by (simp add: unif.psimps 3(1))
  next
    case (Some r)
    then obtain k' us' \<mu> where cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)"
      by (metis prod.exhaust)
    define L' where "L' = us' @ map_subst \<mu> us"
    have unif_eq: "unif k (Problem s t # us) \<phi> = unif k' L' (\<mu> \<circ>\<^sub>s \<phi>)"
      using cs by (simp add: unif.psimps 3(1) L'_def)
    obtain fr' where inv': "inv k' fr' L'"
      using unif_step_Problem[OF 3(3) cs] by (auto simp: L'_def)
    obtain \<tau>' where \<tau>': "\<And>F. F \<le> k \<Longrightarrow> \<tau>' F = \<tau> F" "typed_list \<tau>' us'" "typed_on {..k} \<tau> \<tau>' \<mu>"
      using cases_typing[OF cs D(1,2) tyst(1)] D(4) by blast
    have "typed_list \<tau>' L'"
      using \<tau>'(2) typed_list_map_subst[OF tyst(2) _ \<tau>'(3)] D(4) by (simp add: L'_def)
    from 3(2)[OF cs refl refl, folded L'_def, OF inv' this]
    have IH: "case unif k' L' (\<mu> \<circ>\<^sub>s \<phi>) of
      None \<Rightarrow> (\<forall>W \<sigma> \<tau>\<sigma>. \<not> solves k' \<tau>' L' W \<sigma> \<tau>\<sigma>)
    | Some \<phi>' \<Rightarrow> (\<exists>\<psi>. \<phi>' = \<psi> \<circ>\<^sub>s (\<mu> \<circ>\<^sub>s \<phi>) \<and> closed_on UNIV \<psi> \<and> unifies_all \<psi> L' \<and>
        (\<forall>W \<sigma> \<tau>\<sigma>. solves k' \<tau>' L' W \<sigma> \<tau>\<sigma> \<longrightarrow> (\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> (\<psi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F)))" .
    have \<tau>'1: "\<forall>F\<le>k. \<tau>' F = \<tau> F" using \<tau>'(1) by simp
    note step = step_solves[where us = us, OF cs D(1,2) \<tau>'1 \<tau>'(3), folded L'_def]
    show ?thesis
    proof (cases "unif k' L' (\<mu> \<circ>\<^sub>s \<phi>)")
      case None
      have "\<not> solves k \<tau> (Problem s t # us) W \<sigma> \<tau>\<sigma>" for W \<sigma> \<tau>\<sigma>
      proof
        assume "solves k \<tau> (Problem s t # us) W \<sigma> \<tau>\<sigma>"
        from step[OF this] obtain \<rho> where "solves k' \<tau>' L' (W \<union> {k<..k'}) \<rho> \<tau>\<sigma>" by blast
        with IH None show False by simp
      qed
      then show ?thesis using None unif_eq by simp
    next
      case (Some \<phi>')
      with IH obtain \<psi> where \<psi>: "\<phi>' = \<psi> \<circ>\<^sub>s (\<mu> \<circ>\<^sub>s \<phi>)" "closed_on UNIV \<psi>" "unifies_all \<psi> L'"
        "\<forall>W \<sigma> \<tau>\<sigma>. solves k' \<tau>' L' W \<sigma> \<tau>\<sigma> \<longrightarrow> (\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> (\<psi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F)"
        by auto
      have \<mu>cl: "closed_on UNIV \<mu>" using pat_subst_closed_on[OF cases_closed(1)[OF cs D(1,2)]] .
      have "\<phi>' = (\<psi> \<circ>\<^sub>s \<mu>) \<circ>\<^sub>s \<phi>" using \<psi>(1) by (simp add: subst_comp_assoc)
      moreover have "closed_on UNIV (\<psi> \<circ>\<^sub>s \<mu>)" using closed_on_comp[OF \<mu>cl closed_on_mono[OF \<psi>(2)]] by simp
      moreover have "unifies_all (\<psi> \<circ>\<^sub>s \<mu>) (Problem s t # us)"
        using step_unifies[OF cs D(1,2) \<psi>(2) \<psi>(3)[unfolded L'_def]] .
      moreover have "\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> ((\<psi> \<circ>\<^sub>s \<mu>) F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
        if sol: "solves k \<tau> (Problem s t # us) W \<sigma> \<tau>\<sigma>" for W \<sigma> \<tau>\<sigma>
      proof -
        from step[OF sol] obtain \<rho> where \<rho>: "solves k' \<tau>' L' (W \<union> {k<..k'}) \<rho> \<tau>\<sigma>"
          "\<And>F. F \<in> W \<Longrightarrow> mk_subst \<rho> (\<mu> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F" by blast
        from \<psi>(4)[rule_format, OF \<rho>(1)] obtain \<gamma> where
          \<gamma>: "\<And>F. F \<in> W \<union> {k<..k'} \<Longrightarrow> mk_subst \<gamma> (\<psi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<rho> F" by blast
        have "mk_subst \<gamma> ((\<psi> \<circ>\<^sub>s \<mu>) F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F" if "F \<in> W" for F
        proof -
          have "mk_subst \<gamma> ((\<psi> \<circ>\<^sub>s \<mu>) F) = mk_subst (\<gamma> \<circ>\<^sub>s \<psi>) (\<mu> F)" by simp
          also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<rho> (\<mu> F)"
          proof (rule mk_subst_equiv_cong)
            fix G assume "G \<in> FV (\<mu> F)"
            then have "G \<in> W \<union> {k<..k'}" using cases_vars(2)[OF cs D(1,2), of F] that by auto
            then show "(\<gamma> \<circ>\<^sub>s \<psi>) G \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<rho> G" using \<gamma> by simp
          qed
          also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F" using \<rho>(2)[OF that] .
          finally show ?thesis .
        qed
        then show ?thesis by blast
      qed
      ultimately show ?thesis using Some unif_eq by auto
    qed
  qed
qed


subsection \<open>Main theorem\<close>

text \<open>
  For two well-typed patterns \<open>s\<close> and \<open>t\<close> (of the same type), \<open>unify\<close> terminates and either
  fails, in which case there is no closed, well-typed unifier, or it returns a closed unifier that
  is most general (up to \<open>\<beta>\<eta>\<close>-equivalence) among all closed, well-typed unifiers.
\<close>

lemma unify_correct:
  assumes "pat s" "pat t" "(e, \<tau>) \<turnstile> s : T" "(e, \<tau>) \<turnstile> t : T"
  shows "case unify s t of
      None \<Rightarrow> (\<forall>W \<sigma> \<tau>\<sigma>. \<not> solves (max_var s t) \<tau> [Problem s t] W \<sigma> \<tau>\<sigma>)
    | Some \<phi>' \<Rightarrow> (closed_on UNIV \<phi>' \<and> unifies \<phi>' s t \<and>
        (\<forall>W \<sigma> \<tau>\<sigma>. solves (max_var s t) \<tau> [Problem s t] W \<sigma> \<tau>\<sigma> \<longrightarrow>
          (\<exists>\<gamma>. \<forall>F\<in>W. mk_subst \<gamma> (\<phi>' F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F)))"
proof -
  have "typed_list \<tau> [Problem s t]" using assms(3,4) by (auto simp: typed_prob_def)
  from unif_correct[OF unify_terminates[OF assms(1,2)] inv_init[OF assms(1,2) FV_le_max_var] this]
  show ?thesis unfolding unify_def by (auto split: option.splits)
qed

theorem unify_None:
  assumes "pat s" "pat t" "(e, \<tau>) \<turnstile> s : T" "(e, \<tau>) \<turnstile> t : T" "unify s t = None"
    and "closed_on (FV s \<union> FV t) \<sigma>" "typed_on (FV s \<union> FV t) \<tau> \<tau>\<sigma> \<sigma>"
  shows "\<not> unifies \<sigma> s t"
proof
  assume "unifies \<sigma> s t"
  with assms(6,7) have "solves (max_var s t) \<tau> [Problem s t] (FV s \<union> FV t) \<sigma> \<tau>\<sigma>"
    using FV_le_max_var by (simp add: solves_def)
  with unify_correct[OF assms(1-4)] assms(5) show False by simp
qed

theorem unify_Some:
  assumes "pat s" "pat t" "(e, \<tau>) \<turnstile> s : T" "(e, \<tau>) \<turnstile> t : T" "unify s t = Some \<phi>"
  shows "closed_on UNIV \<phi>" "unifies \<phi> s t"
    and "closed_on (FV s \<union> FV t) \<sigma> \<Longrightarrow> typed_on (FV s \<union> FV t) \<tau> \<tau>\<sigma> \<sigma> \<Longrightarrow> unifies \<sigma> s t \<Longrightarrow>
      \<exists>\<gamma>. \<forall>F\<in>FV s \<union> FV t. mk_subst \<gamma> (\<phi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F"
proof -
  note c = unify_correct[OF assms(1-4), unfolded assms(5) option.case]
  show "closed_on UNIV \<phi>" "unifies \<phi> s t" using c by simp_all
  assume "closed_on (FV s \<union> FV t) \<sigma>" "typed_on (FV s \<union> FV t) \<tau> \<tau>\<sigma> \<sigma>" "unifies \<sigma> s t"
  then have "solves (max_var s t) \<tau> [Problem s t] (FV s \<union> FV t) \<sigma> \<tau>\<sigma>"
    using FV_le_max_var by (simp add: solves_def)
  with c show "\<exists>\<gamma>. \<forall>F\<in>FV s \<union> FV t. mk_subst \<gamma> (\<phi> F) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F" by blast
qed

end
