section \<open>Normal Forms, Renamings, and Typing\<close>

theory Unif_Normal
  imports Unif_Prelims
begin

text \<open>
  Auxiliary results about \<open>\<beta>\<eta>\<close>-normal forms, renamings of loose bound variables, and typing,
  which are needed to construct the substitutions in Grobauer's Proposition 2.
\<close>

declare upt_Suc[simp del]

subsection \<open>Renamings preserve reduction\<close>

lemma replace_BVar_list_preserves_beta:
  "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> replace_BVar_list s xs ys \<rightarrow>\<^sub>\<beta> replace_BVar_list t xs ys"
  by (induction xs ys arbitrary: s t rule: list_induct2') (auto intro: replace_BVar_preserves_beta)

lemma replace_BVar_list_preserves_eta:
  "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> replace_BVar_list s xs ys \<rightarrow>\<^sub>\<eta> replace_BVar_list t xs ys"
  by (induction xs ys arbitrary: s t rule: list_induct2') (auto intro: replace_BVar_preserves_eta)

lemma map_BVars_preserves_\<beta>\<eta>: "\<beta>\<eta> s t \<Longrightarrow> \<beta>\<eta> (map_BVars f s) (map_BVars f t)"
proof -
  from map_BVars_replace[of f "s \<degree> t"] obtain xs ys where
    "map_BVars f (s \<degree> t) = replace_BVar_list (s \<degree> t) xs ys" by blast
  with replace_BVar_list_App[of s t xs ys] have
    "map_BVars f s = replace_BVar_list s xs ys" "map_BVars f t = replace_BVar_list t xs ys"
    by simp_all
  moreover assume "\<beta>\<eta> s t"
  ultimately show ?thesis
    using replace_BVar_list_preserves_beta replace_BVar_list_preserves_eta by auto
qed

lemma map_BVars_preserves_\<beta>\<eta>cl: "\<beta>\<eta>cl s t \<Longrightarrow> \<beta>\<eta>cl (map_BVars f s) (map_BVars f t)"
proof (induction rule: rtranclp_induct)
  case (step y z)
  from step.hyps(2) have "\<beta>\<eta> (map_BVars f y) (map_BVars f z)" by (rule map_BVars_preserves_\<beta>\<eta>)
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed simp

lemma map_BVars_inverse:
  assumes "inj_on f (loose_BVars t)"
  obtains g where "map_BVars g (map_BVars f t) = t"
proof
  let ?g = "inv_into (loose_BVars t) f"
  have "map_BVars ?g (map_BVars f t) = map_BVars (?g \<circ> f) t" by (simp add: map_BVars_comp)
  also have "\<dots> = map_BVars id t"
    using assms by (intro map_BVars_cong) simp
  also have "\<dots> = t" by (simp add: map_BVars_id)
  finally show "map_BVars ?g (map_BVars f t) = t" .
qed

lemma normal_map_BVars:
  assumes "normal t" "inj_on f (loose_BVars t)"
  shows "normal (map_BVars f t)"
proof
  assume "\<exists>u. \<beta>\<eta> (map_BVars f t) u"
  then obtain u where "\<beta>\<eta> (map_BVars f t) u" by blast
  moreover from assms(2) obtain g where "map_BVars g (map_BVars f t) = t"
    by (rule map_BVars_inverse)
  ultimately have "\<beta>\<eta> t (map_BVars g u)"
    using map_BVars_preserves_\<beta>\<eta> by metis
  with assms(1) show False by blast
qed

lemma loose_BVars_free: "i \<in> loose_BVars t \<longleftrightarrow> free t i"
  by (induction t arbitrary: i) auto

lemma loose_BVars_\<beta>\<eta>cl: "\<beta>\<eta>cl s t \<Longrightarrow> loose_BVars t \<subseteq> loose_BVars s"
  by (meson \<beta>\<eta>cl_not_free loose_BVars_free subsetI)


subsection \<open>Normality of \<open>appb\<close>\<close>

lemma normal_subst_BVar: "normal t \<Longrightarrow> normal (t[BVar x/i])"
  using subst_BVar_betaetaD by blast

lemma normal_Abs: "normal (Abs t) \<Longrightarrow> normal t"
  by blast

lemma normal_apps_BVars:
  assumes "normal r" "\<And>u. r \<noteq> Abs u"
  shows "normal (r \<degree>\<degree> map BVar xs)"
proof (induction xs rule: rev_induct)
  case (snoc x xs)
  have nAbs: "r \<degree>\<degree> map BVar xs \<noteq> Abs v" for v
    using assms(2) by (cases xs rule: rev_cases) auto
  show ?case
  proof
    assume "\<exists>u. \<beta>\<eta> (r \<degree>\<degree> map BVar (xs @ [x])) u"
    then obtain u where "\<beta>\<eta> (r \<degree>\<degree> map BVar (xs @ [x])) u" ..
    then have "(r \<degree>\<degree> map BVar xs) \<degree> BVar x \<rightarrow>\<^sub>\<beta> u \<or> (r \<degree>\<degree> map BVar xs) \<degree> BVar x \<rightarrow>\<^sub>\<eta> u"
      by simp
    then show False
    proof
      assume "(r \<degree>\<degree> map BVar xs) \<degree> BVar x \<rightarrow>\<^sub>\<beta> u"
      then show False
        by (cases rule: beta.cases) (use nAbs snoc.IH in auto)
    next
      assume "(r \<degree>\<degree> map BVar xs) \<degree> BVar x \<rightarrow>\<^sub>\<eta> u"
      then show False
        by (cases rule: eta.cases) (use snoc.IH in auto)
    qed
  qed
qed (use assms in simp)

lemma normal_appb: "normal r \<Longrightarrow> normal (appb r xs)"
proof (induction r xs rule: appb.induct)
  case (1 r x xs)
  then show ?case using normal_subst_BVar[OF normal_Abs] by simp
next
  case (3 y xs)
  then show ?case by (simp only: appb.simps) (rule normal_apps_BVars; simp)
next
  case (4 F xs)
  then show ?case by (simp only: appb.simps) (rule normal_apps_BVars; simp)
next
  case (5 s t xs)
  then show ?case by (simp only: appb.simps) (rule normal_apps_BVars; simp)
qed simp

lemma appb_Abs_m:
  "length xs = m \<Longrightarrow> appb (Abs_m m r) xs = map_BVars (\<lambda>i. if i < m then xs ! (m - Suc i) else i - m) r"
proof (induction xs arbitrary: m r)
  case Nil
  then show ?case by (simp add: map_BVars_id)
next
  case (Cons x xs)
  then obtain m' where m: "m = Suc m'" "length xs = m'" by auto
  let ?h = "\<lambda>j. if m' < j then j - 1 else if j = m' then x + m' else j"
  have "appb (Abs_m m r) (x # xs) = appb (Abs_m m' (r[BVar (x + m')/m'])) xs"
    by (simp add: m Abs_m_subst)
  also have "\<dots> = map_BVars (\<lambda>i. if i < m' then xs ! (m' - Suc i) else i - m') (map_BVars ?h r)"
    by (simp add: Cons.IH m subst_BVar_map_BVars)
  also have "\<dots> = map_BVars (\<lambda>i. if i < m then (x # xs) ! (m - Suc i) else i - m) r"
    unfolding map_BVars_comp
  proof (rule map_BVars_cong)
    fix j
    show "((\<lambda>i. if i < m' then xs ! (m' - Suc i) else i - m') \<circ> ?h) j =
      (if j < m then (x # xs) ! (m - Suc j) else j - m)"
      by (cases "j < m'"; cases "j = m'") (auto simp: m nth_Cons' Suc_diff_Suc)
  qed
  finally show ?case .
qed

lemma map_downs: "length xs = m \<Longrightarrow> map (\<lambda>i. xs ! (m - Suc i)) (downs m) = xs"
  by (rule nth_equalityI) (auto simp: rev_nth)

lemma downs_nth': "i < m \<Longrightarrow> downs m ! (m - Suc i) = i"
  by (simp add: rev_nth)

text \<open>Grobauer's Lemma 21.\<close>

lemma appb_downs:
  assumes "no_loose_bound r m"
  shows "appb (Abs_m m r) (downs m) = r"
proof -
  have "appb (Abs_m m r) (downs m) = map_BVars (\<lambda>i. if i < m then downs m ! (m - Suc i) else i - m) r"
    by (simp add: appb_Abs_m)
  also have "\<dots> = map_BVars id r"
    using assms no_loose_bound_BVars[OF assms] by (intro map_BVars_cong) (auto simp: downs_nth')
  finally show ?thesis by (simp add: map_BVars_id)
qed

lemma downt_downs: "downt m 0 = downs (Suc m)"
  by (induction m) (simp_all add: upt_Suc)

lemma eta_m_equiv: "eta_m m s t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
proof (induction rule: eta_m.induct)
  case (2 r s m t)
  from eta_into_equiv[OF 2(1)] 2(3) show ?case by (rule equiv_trans)
qed simp

lemma Abs_m_Suc[simp]: "Abs_m (Suc m) t = Abs (Abs_m m t)"
  by simp

text \<open>Grobauer's Lemma 20: \<open>\<eta>\<close>-expansion of a closed term.\<close>

lemma eta_expand_equiv:
  assumes "no_loose_bound t 0"
  shows "Abs_m m (t \<degree>\<degree> map BVar (downs m)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
proof (cases m)
  case (Suc m')
  then show ?thesis using lemma20[OF assms, of m'] by (simp add: downt_downs eta_m_equiv del: Abs_m_Suc)
qed simp


subsection \<open>Typing\<close>

definition env_ext :: "(nat \<Rightarrow> type) \<Rightarrow> type list \<Rightarrow> nat \<Rightarrow> type" where
  "env_ext e Ts = foldl (\<lambda>e T. e\<langle>0:T\<rangle>) e Ts"

lemma env_ext_simps[simp]: "env_ext e [] = e" "env_ext e (T # Ts) = env_ext (e\<langle>0:T\<rangle>) Ts"
  by (simp_all add: env_ext_def)

lemma env_ext_nth:
  "env_ext e Ts i = (if i < length Ts then Ts ! (length Ts - Suc i) else e (i - length Ts))"
proof (induction Ts arbitrary: e i)
  case (Cons T Ts)
  then show ?case
    by (auto simp: shift_def nth_Cons' Suc_diff_Suc split: if_splits)
qed simp

lemma typing_Abs_m:
  "(env_ext e1 Ts, e2) \<turnstile> t : T \<Longrightarrow> (e1, e2) \<turnstile> Abs_m (length Ts) t : Ts \<Rrightarrow> T"
proof (induction Ts arbitrary: e1)
  case (Cons U Ts)
  then have "(e1\<langle>0:U\<rangle>, e2) \<turnstile> Abs_m (length Ts) t : Ts \<Rrightarrow> T" by simp
  then show ?case by (simp add: typing.Abs)
qed simp

lemma typing_Abs_m_D:
  "(e1, e2) \<turnstile> Abs_m m t : T \<Longrightarrow> \<exists>Ts U. length Ts = m \<and> T = Ts \<Rrightarrow> U \<and> (env_ext e1 Ts, e2) \<turnstile> t : U"
proof (induction m arbitrary: e1 T)
  case (Suc m)
  from Suc.prems obtain A B where "T = A \<Rightarrow> B" "(e1\<langle>0:A\<rangle>, e2) \<turnstile> Abs_m m t : B"
    by auto
  with Suc.IH obtain Ts U where "length Ts = m" "B = Ts \<Rrightarrow> U" "(env_ext (e1\<langle>0:A\<rangle>) Ts, e2) \<turnstile> t : U"
    by blast
  with \<open>T = A \<Rightarrow> B\<close> show ?case by (intro exI[of _ "A # Ts"]) auto
qed auto

lemma typing_map_BVars:
  "(e, e2) \<turnstile> t : T \<Longrightarrow> (\<And>v. v \<in> loose_BVars t \<Longrightarrow> e' (f v) = e v) \<Longrightarrow> (e', e2) \<turnstile> map_BVars f t : T"
proof (induction e e2 t T arbitrary: e' f rule: typing.induct[split_format(complete)])
  case (Abs env1 T env2 t U)
  have "(e'\<langle>0:T\<rangle>, env2) \<turnstile> map_BVars (case_nat 0 (\<lambda>a. Suc (f a))) t : U"
  proof (rule Abs.IH)
    fix v assume "v \<in> loose_BVars t"
    with Abs.prems show "(e'\<langle>0:T\<rangle>) (case v of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (f a)) = (env1\<langle>0:T\<rangle>) v"
      by (cases v) (auto simp: shift_def)
  qed
  then show ?case by auto
next
  case (App env1 env2 s T U t)
  then show ?case by (metis UnCI loose_BVars.simps(3) map_BVars.simps(3) typing.App)
qed auto

lemma size_funs: "size (Ts \<Rrightarrow> T) = sum_list (map size Ts) + length Ts + size T"
  by (induction Ts) auto

lemma funs_append_eq:
  "length Ts = length Us1 \<Longrightarrow> Ts \<Rrightarrow> T = (Us1 @ Us2) \<Rrightarrow> U \<Longrightarrow> T = Us2 \<Rrightarrow> U"
  by (induction Ts Us1 rule: list_induct2) auto

lemma funs_eq_length:
  assumes "Ts \<Rrightarrow> T = Us \<Rrightarrow> T"
  shows "length Ts = length Us"
proof -
  have False if "length Ts < length Us" "Ts \<Rrightarrow> T = Us \<Rrightarrow> T" for Ts Us
  proof -
    define Us1 where "Us1 = take (length Ts) Us"
    define Us2 where "Us2 = drop (length Ts) Us"
    have "Us = Us1 @ Us2" "length Us1 = length Ts" "Us2 \<noteq> []"
      using that(1) by (simp_all add: Us1_def Us2_def)
    with that(2) have "Ts \<Rrightarrow> T = (Us1 @ Us2) \<Rrightarrow> T" by simp
    with \<open>length Us1 = length Ts\<close> have "T = Us2 \<Rrightarrow> T" using funs_append_eq by metis
    then have "size T = size (Us2 \<Rrightarrow> T)" by simp
    with \<open>Us2 \<noteq> []\<close> show False by (simp add: size_funs)
  qed
  with assms show ?thesis by (metis linorder_neqE_nat)
qed

lemma funs_eq_iff:
  "length Ts = length Us \<Longrightarrow> Ts \<Rrightarrow> T = Us \<Rrightarrow> U \<longleftrightarrow> Ts = Us \<and> T = U"
  by (induction Ts Us rule: list_induct2) auto

lemma typings_map_BVar: "(e1, e2) \<tturnstile> map BVar xs : Ts \<longleftrightarrow> Ts = map e1 xs"
  by (induction xs arbitrary: Ts) (auto split: list.splits)

lemma typings_length: "e \<tturnstile> ts : Ts \<Longrightarrow> length Ts = length ts"
  by (induction ts arbitrary: Ts) (auto split: list.splits)

lemma typings_nth: "e \<tturnstile> ts : Ts \<Longrightarrow> i < length ts \<Longrightarrow> e \<turnstile> ts ! i : Ts ! i"
  by (induction ts arbitrary: Ts i) (auto split: list.splits simp: nth_Cons')


subsection \<open>Normal forms\<close>

lemma normal_form_unique:
  assumes "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> s'" "\<beta>\<eta>cl s r" "normal r" "\<beta>\<eta>cl s' r'" "normal r'"
  shows "r = r'"
proof -
  have "r \<equiv>\<^sub>\<beta>\<^sub>\<eta> r'"
    using assms by (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
  with assms(3,5) show ?thesis
    using equiv_\<beta>\<eta>cl_normal by (metis converse_rtranclpE)
qed

lemma normal_form_rename:
  assumes "\<beta>\<eta>cl s r" "normal r" "inj_on f (loose_BVars s)"
  shows "\<beta>\<eta>cl (map_BVars f s) (map_BVars f r)" "normal (map_BVars f r)"
proof -
  show "\<beta>\<eta>cl (map_BVars f s) (map_BVars f r)" using assms(1) by (rule map_BVars_preserves_\<beta>\<eta>cl)
  have "loose_BVars r \<subseteq> loose_BVars s" using assms(1) by (rule loose_BVars_\<beta>\<eta>cl)
  with assms(3) have "inj_on f (loose_BVars r)" by (rule inj_on_subset)
  with assms(2) show "normal (map_BVars f r)" by (rule normal_map_BVars)
qed

lemma map_BVars_closed_app:
  "no_loose_bound t 0 \<Longrightarrow> map_BVars f (t \<degree>\<degree> map BVar zs) = t \<degree>\<degree> map BVar (map f zs)"
  by (simp add: map_BVars_no_loose del: map_map)

text \<open>
  If a closed term applied to bound variables \<open>zs\<close> is equivalent to the same term applied to a
  renaming of \<open>zs\<close>, then the variables moved outside of \<open>zs\<close> do not occur in the normal form.
\<close>

lemma normal_form_independent:
  assumes closed: "no_loose_bound t 0"
    and nf: "\<beta>\<eta>cl (t \<degree>\<degree> map BVar zs) r" "normal r"
    and eq: "t \<degree>\<degree> map BVar zs \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<degree>\<degree> map BVar (map f zs)"
    and inj: "inj_on f (set zs)"
    and v: "v \<in> set zs" "f v \<notin> set zs"
  shows "v \<notin> loose_BVars r"
proof
  assume vr: "v \<in> loose_BVars r"
  have loose: "loose_BVars (t \<degree>\<degree> map BVar zs) = set zs"
    using no_loose_bound_loose_BVars[OF closed] by simp
  with inj have "inj_on f (loose_BVars (t \<degree>\<degree> map BVar zs))" by simp
  from normal_form_rename[OF nf this] closed have
    "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (map f zs)) (map_BVars f r)" "normal (map_BVars f r)"
    by (simp_all add: map_BVars_closed_app)
  with normal_form_unique[OF eq nf] have "map_BVars f r = r" by simp
  moreover have "f v \<in> loose_BVars (map_BVars f r)"
    using vr by (simp add: loose_BVars_map_BVars)
  moreover have "loose_BVars r \<subseteq> set zs" using loose_BVars_\<beta>\<eta>cl[OF nf(1)] loose by simp
  ultimately show False using v(2) by auto
qed

lemma typed_normal_form:
  assumes "e \<turnstile> t : T"
  obtains r where "\<beta>\<eta>cl t r" "normal r" "e \<turnstile> r : T"
  using normal_form_ex[OF assms] subject_reduction_\<beta>\<eta>[OF _ assms] by blast

end
