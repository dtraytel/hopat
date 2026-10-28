section \<open>Applying Abstractions to Arguments\<close>

theory Unify_Beta
  imports
    Unify_Occurs
    "Pure_Pattern_Correctness.Pattern_Size"
begin

text \<open>
  \<open>MATCH\<close> of \<open>unify.ML\<close> solves a flex-rigid pair \<open>?F t\<^sub>1 \<dots> t\<^sub>k =?= u\<close> by assigning to \<open>?F\<close> an
  abstraction \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>k. u'\<close> over a \<^emph>\<open>copy\<close> \<open>u'\<close> of \<open>u\<close>, built from bound variables (projection)
  and the head of \<open>u\<close> (imitation), with new variables for the arguments. Its correctness rests
  on how \<open>(\<lambda>x\<^sub>1 \<dots> x\<^sub>k. u') t\<^sub>1 \<dots> t\<^sub>k\<close> \<open>\<beta>\<close>-reduces. This theory provides the reductions on de Bruijn
  terms: the arguments are substituted for the bound variables \<open>BVar (k - 1), \<dots>, BVar 0\<close>.
\<close>


subsection \<open>Closed terms\<close>

lemma lift_closed: "no_loose_bound t k \<Longrightarrow> lift t k = t"
  by (simp add: lift_map_BVars map_BVars_no_loose)

lemma liftn_closed: "no_loose_bound t k \<Longrightarrow> liftn n t k = t"
  by (induction n) (simp_all add: lift_closed)

lemma liftn_Suc_subst: "(liftn (Suc n) t k)[s/k + n] = liftn n t k"
proof (induction t arbitrary: k s)
  case (Abs t)
  from Abs.IH[of "Suc k" "lift s 0"] show ?case by (simp del: liftn_lift)
qed (auto simp del: liftn_lift)


subsection \<open>\<open>\<beta>\<close>-reduction of applied abstractions\<close>

lemma Abs_m_beta_step:
  "dB.Abs (Abs_m m X) \<degree> t \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta> Abs_m m (X[liftn m t 0/m]) \<degree>\<degree> ts"
proof -
  have "dB.Abs (Abs_m m X) \<degree> t \<rightarrow>\<^sub>\<beta> (Abs_m m X)[t/0]" by (rule beta.beta)
  also have "(Abs_m m X)[t/0] = Abs_m m (X[liftn m t 0/m])" by (simp add: Abs_m_subst_gen)
  finally show ?thesis by (rule apps_preserves_beta)
qed

lemma Abs_m_beta_equiv:
  "dB.Abs (Abs_m m X) \<degree> t \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m (X[liftn m t 0/m]) \<degree>\<degree> ts"
  by (rule beta_into_equiv) (use Abs_m_beta_step in blast)

lemma equiv_apps_args:
  "(\<And>a. a \<in> set A \<Longrightarrow> f a \<equiv>\<^sub>\<beta>\<^sub>\<eta> g a) \<Longrightarrow> H \<degree>\<degree> map f A \<equiv>\<^sub>\<beta>\<^sub>\<eta> H \<degree>\<degree> map g A"
  by (rule equiv_list_app) (auto simp: list_all2_conv_all_nth)

text \<open>A head that does not depend on the abstracted variables stays the head.\<close>

lemma Abs_m_apps_lifted_head:
  "length ts = m \<Longrightarrow>
    Abs_m m (liftn m H 0 \<degree>\<degree> A) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> H \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A"
proof (induction ts arbitrary: m A)
  case (Cons t ts)
  then obtain m' where m: "m = Suc m'" "length ts = m'" by auto
  let ?s = "liftn m' t 0"
  have "(liftn (Suc m') H 0 \<degree>\<degree> A)[?s/m'] = liftn m' H 0 \<degree>\<degree> map (\<lambda>a. a[?s/m']) A"
    using liftn_Suc_subst[of m' H 0 ?s] by (simp del: liftn_lift)
  then have "Abs_m m (liftn m H 0 \<degree>\<degree> A) \<degree>\<degree> (t # ts) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      Abs_m m' (liftn m' H 0 \<degree>\<degree> map (\<lambda>a. a[?s/m']) A) \<degree>\<degree> ts"
    using Abs_m_beta_equiv[of m' "liftn (Suc m') H 0 \<degree>\<degree> A" t ts] m(1)
    by (simp del: liftn_lift subst_map)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> H \<degree>\<degree> map (\<lambda>a. Abs_m m' (a[?s/m']) \<degree>\<degree> ts) A"
    using Cons.IH[OF m(2), of "map (\<lambda>a. a[?s/m']) A"] unfolding map_map comp_def .
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> H \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> (t # ts)) A"
    by (rule equiv_apps_args) (simp add: m(1) equiv_sym[OF Abs_m_beta_equiv])
  finally show ?case .
qed simp

lemma Abs_m_apps_closed_head:
  "no_loose_bound H 0 \<Longrightarrow> length ts = m \<Longrightarrow>
    Abs_m m (H \<degree>\<degree> A) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> H \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A"
  using Abs_m_apps_lifted_head[of ts m H A] by (simp add: liftn_closed)

text \<open>A bound variable at the head is replaced by its argument.\<close>

lemma Abs_m_apps_BVar_head:
  "length ts = m \<Longrightarrow> k < m \<Longrightarrow>
    Abs_m m (BVar k \<degree>\<degree> A) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> (rev ts ! k) \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A"
proof (induction ts arbitrary: m A)
  case (Cons t ts)
  then obtain m' where m: "m = Suc m'" "length ts = m'" by auto
  let ?s = "liftn m' t 0"
  have "Abs_m m (BVar k \<degree>\<degree> A) \<degree>\<degree> (t # ts) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      Abs_m m' ((BVar k \<degree>\<degree> A)[?s/m']) \<degree>\<degree> ts"
    using Abs_m_beta_equiv[of m' "BVar k \<degree>\<degree> A" t ts] m(1)
    by (simp del: liftn_lift subst_map)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> (rev (t # ts) ! k) \<degree>\<degree> map (\<lambda>a. Abs_m m' (a[?s/m']) \<degree>\<degree> ts) A"
  proof (cases "k = m'")
    case True
    then have e1: "(BVar k \<degree>\<degree> A)[?s/m'] = liftn m' t 0 \<degree>\<degree> map (\<lambda>a. a[?s/m']) A" by simp
    have e2: "rev (t # ts) ! k = t" using True m by (simp add: nth_append)
    show ?thesis unfolding e1 e2
      using Abs_m_apps_lifted_head[OF m(2), of t "map (\<lambda>a. a[?s/m']) A"] unfolding map_map comp_def .
  next
    case False
    with Cons.prems(2) m have k: "k < m'" by simp
    then have e1: "(BVar k \<degree>\<degree> A)[?s/m'] = BVar k \<degree>\<degree> map (\<lambda>a. a[?s/m']) A" by simp
    have e2: "rev (t # ts) ! k = rev ts ! k" using k m by (simp add: nth_append)
    show ?thesis unfolding e1 e2
      using Cons.IH[OF m(2) k, of "map (\<lambda>a. a[?s/m']) A"] unfolding map_map comp_def .
  qed
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> (rev (t # ts) ! k) \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> (t # ts)) A"
    by (rule equiv_apps_args) (simp add: m(1) equiv_sym[OF Abs_m_beta_equiv])
  finally show ?case .
qed simp

text \<open>A closed head applied to bound variables picks the corresponding arguments.\<close>

lemma Abs_m_apps_select:
  assumes "no_loose_bound G 0" "length ts = m" "\<forall>k\<in>set ks. k < m"
  shows "Abs_m m (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> G \<degree>\<degree> map (\<lambda>k. rev ts ! k) ks"
proof -
  have 1: "Abs_m m (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> G \<degree>\<degree> map (\<lambda>k. Abs_m m (BVar k) \<degree>\<degree> ts) ks"
    using Abs_m_apps_closed_head[OF assms(1,2), of "map BVar ks"] unfolding map_map comp_def .
  have 2: "G \<degree>\<degree> map (\<lambda>k. Abs_m m (BVar k) \<degree>\<degree> ts) ks \<equiv>\<^sub>\<beta>\<^sub>\<eta> G \<degree>\<degree> map (\<lambda>k. rev ts ! k) ks"
  proof (rule equiv_apps_args)
    fix k assume "k \<in> set ks"
    with assms(3) have "k < m" by blast
    from Abs_m_apps_BVar_head[OF assms(2) this, of "[]"]
    show "Abs_m m (BVar k) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> rev ts ! k" by simp
  qed
  from equiv_trans[OF 1 2] show ?thesis .
qed

lemma map_rev_nth_downs: "length ts = m \<Longrightarrow> map (\<lambda>k. rev ts ! k) (downs m) = ts"
proof -
  assume "length ts = m"
  then have "map (\<lambda>k. rev ts ! k) [0..<m] = rev ts"
    using map_nth[of "rev ts"] by simp
  then show ?thesis by (simp add: rev_map[symmetric])
qed

lemma Abs_m_apps_eta:
  assumes "no_loose_bound G 0" "length ts = m"
  shows "Abs_m m (G \<degree>\<degree> map BVar (downs m)) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> G \<degree>\<degree> ts"
proof -
  have "Abs_m m (G \<degree>\<degree> map BVar (downs m)) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> G \<degree>\<degree> map (\<lambda>k. rev ts ! k) (downs m)"
    by (rule Abs_m_apps_select[OF assms]) simp
  then show ?thesis unfolding map_rev_nth_downs[OF assms(2)] .
qed

text \<open>Copying under an abstraction: \<open>\<lambda>x. F t\<^sub>1\<up> \<dots> t\<^sub>k\<up> x\<close> is \<open>\<eta>\<close>-equivalent to \<open>F t\<^sub>1 \<dots> t\<^sub>k\<close> for closed \<open>F\<close>.\<close>

lemma Abs_apps_lift_eta:
  assumes "no_loose_bound F 0"
  shows "dB.Abs ((F \<degree>\<degree> map (\<lambda>t. lift t 0) ts) \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> F \<degree>\<degree> ts"
proof -
  have l: "lift (F \<degree>\<degree> ts) 0 = F \<degree>\<degree> map (\<lambda>t. lift t 0) ts" using assms by (simp add: lift_closed)
  have "dB.Abs (lift (F \<degree>\<degree> ts) 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> F \<degree>\<degree> ts"
    by (rule eta_into_equiv[OF eta_Abs_lift])
  then show ?thesis unfolding l .
qed


subsection \<open>Translations\<close>

lemma tr_types_abs: "tr (types_abs Ts u) = Abs_m (length Ts) (tr u)"
  by (induction Ts) simp_all

lemma tr_combound:
  "0 \<le> n \<Longrightarrow> tr (combound t n k) = tr t \<degree>\<degree> map (\<lambda>i. BVar (nat_of_integer n + i)) (downs k)"
proof (induction k arbitrary: n)
  case (Suc k)
  have n1: "nat_of_integer (n + 1) = Suc (nat_of_integer n)" using Suc.prems by (simp add: integer_reps)
  have "tr (combound t (n + 1) k) = tr t \<degree>\<degree> map (\<lambda>i. BVar (Suc (nat_of_integer n) + i)) (downs k)"
    using Suc.IH[of "n + 1"] Suc.prems n1 by simp
  then have "tr (combound t n (Suc k)) =
      (tr t \<degree>\<degree> map (\<lambda>i. BVar (Suc (nat_of_integer n) + i)) (downs k)) \<degree> BVar (nat_of_integer n)"
    by simp
  also have "\<dots> = tr t \<degree>\<degree> (map (\<lambda>i. BVar (Suc (nat_of_integer n) + i)) (downs k) @ [BVar (nat_of_integer n)])"
    by (rule app_last)
  also have "\<dots> = tr t \<degree>\<degree> map (\<lambda>i. BVar (nat_of_integer n + i)) (downs (Suc k))"
    unfolding downs_Suc by (simp add: comp_def)
  finally show ?case .
qed simp

lemma tr_combound0: "tr (combound t 0 k) = tr t \<degree>\<degree> map BVar (downs k)"
  using tr_combound[of 0 t k] by (simp add: comp_def)


subsection \<open>Solving pairs of de Bruijn terms\<close>

text \<open>\<open>dsolvedB \<sigma> rb A B\<close>: \<open>\<sigma>\<close> makes the abstractions of \<open>A\<close> and \<open>B\<close> over the binder \<open>rb\<close> \<open>\<beta>\<eta>\<close>-equal.\<close>

definition dsolvedB :: "(nat \<Rightarrow> dB) \<Rightarrow> binders \<Rightarrow> dB \<Rightarrow> dB \<Rightarrow> bool" where
  "dsolvedB \<sigma> rb A B \<longleftrightarrow> mk_subst \<sigma> (Abs_m (length rb) A) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (Abs_m (length rb) B)"

lemma dsolved_dsolvedB: "dsolved \<sigma> (rb, s, t) \<longleftrightarrow> dsolvedB \<sigma> rb (tr s) (tr t)"
  by (simp add: dsolved_def dsolvedB_def tr_rlist_abs)

lemma dsolvedB_refl[simp]: "dsolvedB \<sigma> rb A A"
  by (simp add: dsolvedB_def)

lemma dsolvedB_sym: "dsolvedB \<sigma> rb A B \<Longrightarrow> dsolvedB \<sigma> rb B A"
  by (simp add: dsolvedB_def equiv_sym)

lemma dsolvedB_trans: "dsolvedB \<sigma> rb A B \<Longrightarrow> dsolvedB \<sigma> rb B C \<Longrightarrow> dsolvedB \<sigma> rb A C"
  by (auto simp: dsolvedB_def intro: equiv_trans)

lemma dsolvedB_equiv:
  "closed_on UNIV \<sigma> \<Longrightarrow> A \<equiv>\<^sub>\<beta>\<^sub>\<eta> B \<Longrightarrow> dsolvedB \<sigma> rb A B"
  by (simp add: dsolvedB_def mk_subst_equiv equiv_Abs_m)

lemma dsolvedB_unabs:
  "dsolvedB \<sigma> rb A B \<longleftrightarrow> mk_subst \<sigma> A \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> B"
  by (auto simp: dsolvedB_def mk_subst_Abs_m equiv_Abs_m dest: Abs_m_equiv_reflect)

lemma dsolvedB_App:
  "dsolvedB \<sigma> rb A B \<Longrightarrow> dsolvedB \<sigma> rb C D \<Longrightarrow> dsolvedB \<sigma> rb (A \<degree> C) (B \<degree> D)"
  by (simp add: dsolvedB_unabs equiv_App)

lemma dsolvedB_apps:
  "list_all2 (dsolvedB \<sigma> rb) As Bs \<Longrightarrow> dsolvedB \<sigma> rb H H' \<Longrightarrow>
    dsolvedB \<sigma> rb (H \<degree>\<degree> As) (H' \<degree>\<degree> Bs)"
proof (induction As Bs arbitrary: H H' rule: list_all2_induct)
  case (Cons a As b Bs)
  from Cons.IH[OF dsolvedB_App[OF Cons.prems Cons.hyps(1)]] show ?case by simp
qed simp

lemma dsolvedB_Abs: "dsolvedB \<sigma> ((a, T) # rb) A B \<longleftrightarrow> dsolvedB \<sigma> rb (dB.Abs A) (dB.Abs B)"
  by (simp add: dsolvedB_unabs equiv_Abs) (meson equiv_Abs equiv_Abs_reflect)


subsection \<open>Copies\<close>

text \<open>
  The meaning of a copy \<open>u'\<close> relative to the arguments \<open>targs\<close>: the abstraction of \<open>u'\<close> over
  as many bound variables as there are arguments, applied to the arguments.
\<close>

definition cpy :: "pterm list \<Rightarrow> pterm \<Rightarrow> dB" where
  "cpy targs u' = Abs_m (length targs) (tr u') \<degree>\<degree> map tr targs"

lemma cpy_fun: "cpy targs = (\<lambda>u'. Abs_m (length targs) (tr u') \<degree>\<degree> map tr targs)"
  by (rule ext) (simp add: cpy_def)

lemma tr_list_comb_types_abs:
  "length Ts = length targs \<Longrightarrow> tr (list_comb (types_abs Ts u') targs) = cpy targs u'"
  by (simp add: cpy_def tr_list_comb tr_types_abs)

text \<open>Copy by a new variable applied to all abstracted variables (the flexible case).\<close>

lemma cpy_combound:
  assumes "no_loose_bound (tr G) 0"
  shows "cpy targs (combound G 0 (length targs)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (list_comb G targs)"
  unfolding cpy_def tr_combound0 tr_list_comb
  by (rule Abs_m_apps_eta[OF assms length_map])

text \<open>Imitation: the head is kept, the arguments are copies.\<close>

lemma cpy_imitate:
  assumes "no_loose_bound (tr h) 0"
  shows "cpy targs (list_comb h us) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> map (cpy targs) us"
  using Abs_m_apps_closed_head[where A = "map tr us", OF assms length_map[where f = tr and xs = targs]]
  unfolding cpy_fun tr_list_comb map_map comp_def .

text \<open>Projection: the head \<open>Bound j\<close> becomes the argument it refers to.\<close>

lemma cpy_project:
  assumes "0 \<le> j" "nat_of_integer j < length targs"
  shows "cpy targs (list_comb (Bound j) us) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
    tr (targs ! (length targs - 1 - nat_of_integer j)) \<degree>\<degree> map (cpy targs) us"
proof -
  have "cpy targs (list_comb (Bound j) us) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      (rev (map tr targs) ! nat_of_integer j) \<degree>\<degree> map (cpy targs) us"
    using Abs_m_apps_BVar_head[where ts = "map tr targs" and m = "length targs"
        and k = "nat_of_integer j" and A = "map tr us", OF length_map assms(2)]
    unfolding cpy_fun tr_list_comb map_map comp_def tr.simps .
  moreover have "rev (map tr targs) ! nat_of_integer j = tr (targs ! (length targs - 1 - nat_of_integer j))"
    using assms(2) by (simp add: rev_nth)
  ultimately show ?thesis by (simp only:)
qed

text \<open>Copying under an abstraction.\<close>

lemma cpy_Abs:
  assumes "no_loose_bound (tr body') (Suc (length targs))" "\<forall>t\<in>set targs. proper t"
  shows "dB.Abs (cpy (map (incr_boundvars 1) targs @ [Bound 0]) body') \<equiv>\<^sub>\<beta>\<^sub>\<eta>
    cpy targs (Abs a T body')"
proof -
  let ?F = "Abs_m (Suc (length targs)) (tr body')"
  have F: "no_loose_bound ?F 0" using assms(1) by (simp add: loose_bound_Abs_m)
  have "map tr (map (incr_boundvars 1) targs @ [Bound 0]) = map (\<lambda>t. lift t 0) (map tr targs) @ [BVar 0]"
    using assms(2) by (simp add: tr_incr_boundvars1)
  then have "cpy (map (incr_boundvars 1) targs @ [Bound 0]) body' =
      ?F \<degree>\<degree> (map (\<lambda>t. lift t 0) (map tr targs) @ [BVar 0])"
    by (simp add: cpy_def)
  also have "\<dots> = (?F \<degree>\<degree> map (\<lambda>t. lift t 0) (map tr targs)) \<degree> BVar 0"
    by (rule app_last[symmetric])
  finally have "cpy (map (incr_boundvars 1) targs @ [Bound 0]) body' =
      (?F \<degree>\<degree> map (\<lambda>t. lift t 0) (map tr targs)) \<degree> BVar 0" .
  moreover have "cpy targs (Abs a T body') = ?F \<degree>\<degree> map tr targs"
    by (simp add: cpy_def Abs_m)
  ultimately show ?thesis using Abs_apps_lift_eta[OF F, of "map tr targs"] by (simp only:)
qed

end
