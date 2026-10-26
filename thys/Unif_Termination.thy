section \<open>Termination of the Unification Algorithm\<close>

theory Unif_Termination
  imports Unification
begin

text \<open>
  We follow Grobauer's termination argument (Section 2.2.1). With every list of unification
  problems we associate a tuple of natural numbers, ordered lexicographically:
  \<^item> \<open>N\<close>: the number of free variables, not counting those introduced in (flex-rigid) steps;
  \<^item> \<open>C\<^sub>m\<close>: the complexity of the right-hand sides in front of the last marker;
  \<^item> the number of occurrences of free variables not introduced in (flex-rigid) steps;
  \<^item> \<open>C\<close>: the size of the problems after the last marker;
  \<^item> the length of the list.

  Grobauer's triple \<open>\<langle>N, C\<^sub>m, C\<rangle>\<close> needs two adjustments: the size measure \<open>C\<close> must account for the
  \<open>\<eta>\<close>-expansions performed by \<open>otf\<eta>\<close> (we count abstractions), and the (flex-flex-1) case does
  not decrease \<open>C\<close> when the substituted variable occurs partially applied. That case
  decreases the number of occurrences of free variables instead. The length of the list
  takes care of markers being discarded.

  The variables introduced in (flex-rigid) steps are tracked by a ghost set \<open>fr\<close>.
  Grobauer's observations (a)--(c) are generalized to an invariant that is preserved by every step.
\<close>

subsection \<open>Measures on terms\<close>

fun flex_head :: "dB \<Rightarrow> bool" where
  "flex_head (Var _) = True"
| "flex_head (s \<degree> t) = flex_head s"
| "flex_head _ = False"

text \<open>Grobauer's complexity: the number of functors in a term, where the arguments of free
  variables (bound variables in a pattern) are not counted.\<close>

fun cpx :: "dB \<Rightarrow> nat" where
  "cpx (Abs t) = cpx t"
| "cpx (BVar _) = 1"
| "cpx (Var _) = 1"
| "cpx (s \<degree> t) = (if flex_head s then cpx s else cpx s + cpx t)"

text \<open>The size of a term, ignoring applications.\<close>

fun csz :: "dB \<Rightarrow> nat" where
  "csz (Abs t) = Suc (csz t)"
| "csz (BVar _) = 1"
| "csz (Var _) = 1"
| "csz (s \<degree> t) = csz s + csz t"

text \<open>The number of occurrences of free variables outside \<open>fr\<close>.\<close>

fun nocc :: "nat set \<Rightarrow> dB \<Rightarrow> nat" where
  "nocc fr (Var x) = (if x \<in> fr then 0 else 1)"
| "nocc fr (Abs t) = nocc fr t"
| "nocc fr (s \<degree> t) = nocc fr s + nocc fr t"
| "nocc _ (BVar _) = 0"

lemma flex_head_list_app[simp]: "flex_head (t \<degree>\<degree> ts) = flex_head t"
  by (induction ts arbitrary: t) auto

lemma cpx_Var_app[simp]: "cpx (Var F \<degree>\<degree> ts) = 1"
  by (induction ts rule: rev_induct) auto

lemma cpx_BVar_app[simp]: "cpx (BVar x \<degree>\<degree> ts) = Suc (sum_list (map cpx ts))"
  by (induction ts rule: rev_induct) auto

lemma cpx_Abs_m[simp]: "cpx (Abs_m m t) = cpx t"
  by (induction m) auto

lemma csz_list_app[simp]: "csz (t \<degree>\<degree> ts) = csz t + sum_list (map csz ts)"
  by (induction ts rule: rev_induct) auto

lemma nocc_list_app[simp]: "nocc fr (t \<degree>\<degree> ts) = nocc fr t + sum_list (map (nocc fr) ts)"
  by (induction ts rule: rev_induct) auto

lemma nocc_map_BVar[simp]: "sum_list (map (nocc fr) (map BVar xs)) = 0"
  by (induction xs) auto

lemma csz_map_BVars[simp]: "csz (map_BVars f t) = csz t"
  by (induction t arbitrary: f) auto

lemma nocc_map_BVars[simp]: "nocc fr (map_BVars f t) = nocc fr t"
  by (induction t arbitrary: f) auto

lemma flex_head_map_BVars[simp]: "flex_head (map_BVars f t) = flex_head t"
  by (induction t arbitrary: f rule: flex_head.induct) auto

lemma cpx_map_BVars[simp]: "cpx (map_BVars f t) = cpx t"
  by (induction t arbitrary: f) auto

lemma csz_lift[simp]: "csz (lift t i) = csz t"
  by (simp add: lift_map_BVars)

lemma nocc_lift[simp]: "nocc fr (lift t i) = nocc fr t"
  by (simp add: lift_map_BVars)

lemma cpx_lift[simp]: "cpx (lift t i) = cpx t"
  by (simp add: lift_map_BVars)

lemma nocc_pos: "F \<in> FV t \<Longrightarrow> F \<notin> fr \<Longrightarrow> 0 < nocc fr t"
  by (induction t) auto

lemma nocc_Abs_m[simp]: "nocc fr (Abs_m m t) = nocc fr t"
  by (induction m) auto


subsection \<open>Measures under substitution\<close>

text \<open>Values of substitutions in the flexible cases: \<open>\<lambda>\<^sup>a H([zs])\<close>.\<close>

definition flexval :: "dB \<Rightarrow> bool" where
  "flexval r \<longleftrightarrow> (\<exists>a H zs. r = Abs_m a (Var H \<degree>\<degree> map BVar zs))"

lemma flexval_Var[simp]: "flexval (Var G)"
  unfolding flexval_def by (rule exI[of _ 0]) auto

lemma flexval_Abs_m[simp]: "flexval (Abs_m a (Var H \<degree>\<degree> map BVar zs))"
  unfolding flexval_def by blast

lemma Var_app_subst_BVar:
  "(Var H \<degree>\<degree> map BVar zs)[BVar x/i] = Var H \<degree>\<degree> map BVar (map (\<lambda>j. if i < j then j - 1 else if j = i then x else j) zs)"
  by (induction zs rule: rev_induct) (auto simp: subst_BVar)

lemma appb_flexval:
  "\<exists>a' zs'. appb (Abs_m a (Var H \<degree>\<degree> map BVar zs)) xs = Abs_m a' (Var H \<degree>\<degree> map BVar zs')"
proof (induction xs arbitrary: a zs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases a)
    case 0
    then show ?thesis
      by (intro exI[of _ 0] exI[of _ "zs @ x # xs"]) (simp add: appb_not_Abs)
  next
    case (Suc a')
    then have "appb (Abs_m a (Var H \<degree>\<degree> map BVar zs)) (x # xs) =
      appb ((Abs_m a' (Var H \<degree>\<degree> map BVar zs))[BVar x/0]) xs"
      by simp
    also have "(Abs_m a' (Var H \<degree>\<degree> map BVar zs))[BVar x/0] =
      Abs_m a' (Var H \<degree>\<degree> map BVar (map (\<lambda>j. if a' < j then j - 1 else if j = a' then x + a' else j) zs))"
      apply (simp add: Abs_m_subst comp_def subst_BVar)
      apply (intro arg_cong[where f = "\<lambda>ts. Abs_m a' (Var H \<degree>\<degree> ts)"] map_cong refl)
      apply auto
      done
    finally have eq: "appb (Abs_m a (Var H \<degree>\<degree> map BVar zs)) (x # xs) =
      appb (Abs_m a' (Var H \<degree>\<degree> map BVar (map (\<lambda>j. if a' < j then j - 1 else if j = a' then x + a' else j) zs))) xs" .
    from Cons.IH obtain a'' zs'' where
      "appb (Abs_m a' (Var H \<degree>\<degree> map BVar (map (\<lambda>j. if a' < j then j - 1 else if j = a' then x + a' else j) zs))) xs =
       Abs_m a'' (Var H \<degree>\<degree> map BVar zs'')"
      by blast
    with eq show ?thesis by auto
  qed
qed

lemma flexval_appb: "flexval r \<Longrightarrow> flexval (appb r xs)"
  unfolding flexval_def using appb_flexval by blast

lemma cpx_flexval: "flexval r \<Longrightarrow> cpx r = 1"
  unfolding flexval_def by auto

lemma nocc_appb[simp]: "nocc fr (appb r xs) = nocc fr r"
  by (induction r xs rule: appb.induct) (auto simp: subst_BVar_map_BVars)

lemma nocc_\<beta>_nf_mk_subst:
  assumes "pat t" "pat_subst (FV t) \<sigma>" "\<forall>F\<in>FV t. nocc fr (\<sigma> F) = nocc fr (Var F)"
  shows "nocc fr (\<beta>_nf (mk_subst \<sigma> t)) = nocc fr t"
  using assms
proof (induction rule: pat.induct)
  case (pat_Abs t)
  then show ?case by (simp add: \<beta>_nf_mk_subst_Abs)
next
  case (pat_BVar ts x)
  have "pat_subst (\<Union> (FV ` set ts)) \<sigma>" using pat_BVar.prems by simp
  then have "\<beta>_nf (BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts) = BVar x \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<sigma> t)) ts"
    using pat_BVar.hyps by (intro \<beta>_nf_mk_subst_BVar) auto
  moreover have "(\<Sum>t\<leftarrow>ts. nocc fr (\<beta>_nf (mk_subst \<sigma> t))) = (\<Sum>t\<leftarrow>ts. nocc fr t)"
    using pat_BVar.IH pat_BVar.prems by (intro arg_cong[where f = sum_list] map_cong) (auto intro: pat_subst_mono)
  ultimately show ?case by (simp add: comp_def)
next
  case (pat_Var xs F)
  then show ?case
    by (simp add: \<beta>_nf_mk_subst_Var pat_subst_mono)
qed

lemma cpx_\<beta>_nf_mk_subst:
  assumes "pat t" "pat_subst (FV t) \<sigma>" "\<forall>F\<in>FV t. flexval (\<sigma> F)"
  shows "cpx (\<beta>_nf (mk_subst \<sigma> t)) = cpx t"
  using assms
proof (induction rule: pat.induct)
  case (pat_Abs t)
  then show ?case by (simp add: \<beta>_nf_mk_subst_Abs)
next
  case (pat_BVar ts x)
  have "pat_subst (\<Union> (FV ` set ts)) \<sigma>" using pat_BVar.prems by simp
  then have "\<beta>_nf (BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts) = BVar x \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<sigma> t)) ts"
    using pat_BVar.hyps by (intro \<beta>_nf_mk_subst_BVar) auto
  moreover have "(\<Sum>t\<leftarrow>ts. cpx (\<beta>_nf (mk_subst \<sigma> t))) = (\<Sum>t\<leftarrow>ts. cpx t)"
    using pat_BVar.IH pat_BVar.prems by (intro arg_cong[where f = sum_list] map_cong) (auto intro: pat_subst_mono)
  ultimately show ?case by (simp add: comp_def)
next
  case (pat_Var xs F)
  then show ?case
    by (simp add: \<beta>_nf_mk_subst_Var pat_subst_mono cpx_flexval flexval_appb)
qed

lemma \<beta>_nf_mk_subst_id:
  "pat t \<Longrightarrow> (\<And>F. F \<in> FV t \<Longrightarrow> \<sigma> F = Var F) \<Longrightarrow> \<beta>_nf (mk_subst \<sigma> t) = t"
  by (metis mk_subst_Var_id mk_subst_cong pat_\<beta>_nf)

lemma FV_\<beta>_nf_mk_subst: "FV (\<beta>_nf (mk_subst \<sigma> t)) \<subseteq> \<Union> (FV ` \<sigma> ` FV t)"
  using \<beta>_nf_FV[of "mk_subst \<sigma> t"] by (simp add: FV_mk_subst)


subsection \<open>Lists of unification problems\<close>

fun probs :: "unif_problem list \<Rightarrow> (dB \<times> dB) list" where
  "probs [] = []"
| "probs (Marker # us) = probs us"
| "probs (Problem s t # us) = (s, t) # probs us"

text \<open>The problems in front of the last marker, and the problems after it (all problems if
  there is no marker).\<close>

fun blm :: "unif_problem list \<Rightarrow> (dB \<times> dB) list" where
  "blm [] = []"
| "blm (Marker # us) = (if Marker \<in> set us then blm us else [])"
| "blm (Problem s t # us) = (if Marker \<in> set us then (s, t) # blm us else [])"

fun alm :: "unif_problem list \<Rightarrow> (dB \<times> dB) list" where
  "alm [] = []"
| "alm (Marker # us) = (if Marker \<in> set us then alm us else probs us)"
| "alm (Problem s t # us) = (if Marker \<in> set us then alm us else (s, t) # probs us)"

definition FVs :: "unif_problem list \<Rightarrow> nat set" where
  "FVs us = (\<Union>(s, t)\<in>set (probs us). FV s \<union> FV t)"

lemma probs_append[simp]: "probs (xs @ ys) = probs xs @ probs ys"
  by (induction xs rule: probs.induct) auto

lemma blm_no_marker: "Marker \<notin> set us \<Longrightarrow> blm us = []"
  by (induction us rule: blm.induct) auto

lemma alm_no_marker: "Marker \<notin> set us \<Longrightarrow> alm us = probs us"
  by (induction us rule: alm.induct) auto

lemma blm_append: "blm (xs @ ys) = (if Marker \<in> set ys then probs xs @ blm ys else blm xs)"
proof (induction xs)
  case (Cons a xs)
  then show ?case by (cases a) (auto simp: blm_no_marker)
qed (simp add: blm_no_marker)

lemma alm_append: "alm (xs @ ys) = (if Marker \<in> set ys then alm ys else alm xs @ probs ys)"
proof (induction xs)
  case (Cons a xs)
  then show ?case by (cases a) (auto simp: alm_no_marker)
qed (simp add: alm_no_marker)

lemma map_unif_problem_eq_Marker[simp]: "map_unif_problem f a = Marker \<longleftrightarrow> a = Marker"
  "Marker = map_unif_problem f a \<longleftrightarrow> a = Marker"
  by (cases a; auto)+

lemma Marker_in_map[simp]: "Marker \<in> set (map (map_unif_problem f) us) \<longleftrightarrow> Marker \<in> set us"
  by (induction us) auto

lemma probs_map[simp]: "probs (map (map_unif_problem f) us) = map (\<lambda>(s, t). (f s, f t)) (probs us)"
  by (induction us rule: probs.induct) auto

lemma blm_map[simp]: "blm (map (map_unif_problem f) us) = map (\<lambda>(s, t). (f s, f t)) (blm us)"
proof (induction us)
  case (Cons a us)
  then show ?case by (cases a) auto
qed simp

lemma alm_map[simp]: "alm (map (map_unif_problem f) us) = map (\<lambda>(s, t). (f s, f t)) (alm us)"
proof (induction us)
  case (Cons a us)
  then show ?case by (cases a) (auto simp: alm_no_marker)
qed simp

lemma set_blm: "set (blm us) \<subseteq> set (probs us)"
  by (induction us rule: blm.induct) auto

lemma probs_map2[simp]: "probs (map2 Problem ss ts) = zip ss ts"
  by (induction ss ts rule: list_induct2') auto

lemma probs_map2'[simp]: "probs (map2 (\<lambda>H s. Problem (f H) s) Hs ss) = zip (map f Hs) ss"
  by (induction Hs ss rule: list_induct2') auto

lemma Marker_notin_map2[simp]:
  "Marker \<notin> set (map2 Problem ss ts)" "Marker \<notin> set (map2 (\<lambda>H s. Problem (f H) s) Hs ss)"
  by (auto simp: set_zip)

lemma FVs_simps[simp]:
  "FVs [] = {}" "FVs (Marker # us) = FVs us" "FVs (Problem s t # us) = FV s \<union> FV t \<union> FVs us"
  "FVs (xs @ ys) = FVs xs \<union> FVs ys"
  by (auto simp: FVs_def)

lemma finite_FVs[simp]: "finite (FVs us)"
  by (induction us rule: probs.induct) auto

lemma FVs_map: "FVs (map (map_unif_problem f) us) = (\<Union>(s, t)\<in>set (probs us). FV (f s) \<union> FV (f t))"
  by (auto simp: FVs_def)


subsection \<open>On-the-fly \<open>\<eta>\<close>-conversion and orientation\<close>

lemma otf\<eta>_measures:
  assumes "otf\<eta> (s, t) = (s', t')"
  shows "csz s' + csz t' \<le> csz s + csz t" "nocc fr s' + nocc fr t' = nocc fr s + nocc fr t"
    "(\<And>u. s' \<noteq> Abs u)" "(\<And>u. t' \<noteq> Abs u)"
proof -
  have "csz (fst (otf\<eta> (s, t))) + csz (snd (otf\<eta> (s, t))) \<le> csz s + csz t \<and>
    nocc fr (fst (otf\<eta> (s, t))) + nocc fr (snd (otf\<eta> (s, t))) = nocc fr s + nocc fr t \<and>
    (\<forall>u. fst (otf\<eta> (s, t)) \<noteq> Abs u) \<and> (\<forall>u. snd (otf\<eta> (s, t)) \<noteq> Abs u)"
    by (induction s t rule: otf\<eta>_induct) auto
  with assms show "csz s' + csz t' \<le> csz s + csz t" "nocc fr s' + nocc fr t' = nocc fr s + nocc fr t"
    "(\<And>u. s' \<noteq> Abs u)" "(\<And>u. t' \<noteq> Abs u)"
    by auto
qed

lemma tw_cases: "tw p = p \<or> tw p = prod.swap p"
  by (cases p) (auto split: prod.splits dB.splits)

lemma prep_eq:
  assumes "prep (s, t) = ((h1, as1), (h2, as2))"
  obtains s' t' where "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')"
    "s' = h1 \<degree>\<degree> as1" "t' = h2 \<degree>\<degree> as2"
    "\<And>u1 u2. h1 \<noteq> u1 \<degree> u2" "\<And>u1 u2. h2 \<noteq> u1 \<degree> u2"
proof -
  obtain s' t' where tw: "tw (otf\<eta> (s, t)) = (s', t')" by fastforce
  with assms have "dest_comb s' = (h1, as1)" "dest_comb t' = (h2, as2)"
    by (auto simp: prep_def)
  then have "s' = h1 \<degree>\<degree> as1" "t' = h2 \<degree>\<degree> as2" "\<And>u1 u2. h1 \<noteq> u1 \<degree> u2" "\<And>u1 u2. h2 \<noteq> u1 \<degree> u2"
    by (auto simp: dest_comb_eq_iff)
  moreover from tw tw_cases[of "otf\<eta> (s, t)"] have "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')"
    by (auto simp: prod.swap_def)
  ultimately show ?thesis using that by blast
qed

lemma prep_flex:
  assumes "distinct xs"
  obtains xs' t' b where "prep (Var H \<degree>\<degree> map BVar xs, t) = ((Var H, map BVar xs'), dest_comb t')"
    "distinct xs'" "t = Abs_m b t'" "otf\<eta> (Var H \<degree>\<degree> map BVar xs, t) = (Var H \<degree>\<degree> map BVar xs', t')"
proof -
  from otf\<eta>_flex[OF assms, of H t] obtain xs' b where
    "otf\<eta> (Var H \<degree>\<degree> map BVar xs, t) = (Var H \<degree>\<degree> map BVar xs', snd (otf\<eta> (Var H \<degree>\<degree> map BVar xs, t)))"
    "distinct xs'" "t = Abs_m b (snd (otf\<eta> (Var H \<degree>\<degree> map BVar xs, t)))"
    by blast
  with that show ?thesis
    by (auto simp: prep_def)
qed


subsection \<open>The invariant\<close>

text \<open>
  The invariant generalizes Grobauer's observations to nested markers:
  \<^item> all problems are patterns and all variables are bounded by \<open>k\<close>;
  \<^item> (c) the left-hand sides in front of the last marker are of the form \<open>H(x\<^sub>m)\<close> for pairwise
    distinct variables \<open>H\<close> introduced in (flex-rigid) steps;
  \<^item> (a) the right-hand sides in front of the last marker contain no such variable;
  \<^item> (b) every variable introduced in a (flex-rigid) step that still occurs is the head of a
    left-hand side in front of the last marker.
\<close>

definition inv :: "nat \<Rightarrow> nat set \<Rightarrow> unif_problem list \<Rightarrow> bool" where
  "inv k fr us \<longleftrightarrow>
    (\<forall>(s, t)\<in>set (probs us). pat s \<and> pat t) \<and> FVs us \<subseteq> {..k} \<and> fr \<subseteq> {..k} \<and>
    (\<forall>(s, t)\<in>set (blm us). (\<exists>H xs. s = Var H \<degree>\<degree> map BVar xs \<and> H \<in> fr) \<and> FV t \<inter> fr = {}) \<and>
    distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm us)) \<and>
    FVs us \<inter> fr \<subseteq> (\<Union>(s, t)\<in>set (blm us). FV s)"

definition Cm :: "unif_problem list \<Rightarrow> nat" where
  "Cm us = sum_list (map (\<lambda>(s, t). cpx t) (blm us))"

definition Nocc :: "nat set \<Rightarrow> unif_problem list \<Rightarrow> nat" where
  "Nocc fr us = sum_list (map (\<lambda>(s, t). nocc fr s + nocc fr t) (probs us))"

definition Csz :: "unif_problem list \<Rightarrow> nat" where
  "Csz us = sum_list (map (\<lambda>(s, t). csz s + csz t) (alm us))"

definition umeasure :: "nat set \<Rightarrow> unif_problem list \<Rightarrow> nat \<times> nat \<times> nat \<times> nat \<times> nat" where
  "umeasure fr us = (card (FVs us - fr), Cm us, Nocc fr us, Csz us, length us)"

abbreviation lex5 :: "((nat \<times> nat \<times> nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat \<times> nat \<times> nat)) set" where
  "lex5 \<equiv> less_than <*lex*> less_than <*lex*> less_than <*lex*> less_than <*lex*> less_than"

lemma wf_lex5: "wf lex5"
  by auto

lemma unif_step_Marker:
  assumes "inv k fr (Marker # us)"
  shows "inv k fr us" "(umeasure fr us, umeasure fr (Marker # us)) \<in> lex5"
proof -
  have b: "blm (Marker # us) = blm us" and a: "alm (Marker # us) = alm us"
    by (auto simp: blm_no_marker alm_no_marker)
  show "inv k fr us" using assms unfolding inv_def b by simp
  show "(umeasure fr us, umeasure fr (Marker # us)) \<in> lex5"
    unfolding umeasure_def Cm_def Nocc_def Csz_def a b by simp
qed


subsection \<open>One step of \<open>unif\<close>\<close>

lemma inv_ProblemD:
  assumes "inv k fr (Problem s t # us)"
  shows "pat s" "pat t" "\<forall>(a, b)\<in>set (probs us). pat a \<and> pat b"
    "FV s \<union> FV t \<union> FVs us \<subseteq> {..k}" "fr \<subseteq> {..k}"
  using assms unfolding inv_def by auto

lemma inv_Problem_no_marker:
  assumes "inv k fr (Problem s t # us)" "Marker \<notin> set us"
  shows "(FV s \<union> FV t \<union> FVs us) \<inter> fr = {}"
  using assms unfolding inv_def by (auto simp: blm_no_marker)

lemma inv_Problem_marker:
  assumes "inv k fr (Problem s t # us)" "Marker \<in> set us"
  obtains H xs where "s = Var H \<degree>\<degree> map BVar xs" "H \<in> fr" "FV t \<inter> fr = {}"
    "\<forall>(a, b)\<in>set (blm us). (\<exists>H' ys. a = Var H' \<degree>\<degree> map BVar ys \<and> H' \<in> fr \<and> H' \<noteq> H) \<and> FV b \<inter> fr = {}"
    "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm us))"
    "(FV s \<union> FV t \<union> FVs us) \<inter> fr \<subseteq> insert H (\<Union>(a, b)\<in>set (blm us). FV a)"
proof -
  from assms obtain H xs where H: "s = Var H \<degree>\<degree> map BVar xs" "H \<in> fr" "FV t \<inter> fr = {}"
    unfolding inv_def by auto
  moreover have "\<forall>(a, b)\<in>set (blm us). (\<exists>H' ys. a = Var H' \<degree>\<degree> map BVar ys \<and> H' \<in> fr \<and> H' \<noteq> H) \<and> FV b \<inter> fr = {}"
  proof (intro ballI, clarify)
    fix a b assume ab: "(a, b) \<in> set (blm us)"
    with assms obtain H' ys where "a = Var H' \<degree>\<degree> map BVar ys" "H' \<in> fr" "FV b \<inter> fr = {}"
      unfolding inv_def by fastforce
    moreover have "H' \<noteq> H"
    proof
      assume "H' = H"
      with assms ab H(1) \<open>a = Var H' \<degree>\<degree> map BVar ys\<close> show False
        unfolding inv_def by (auto simp: image_iff dest!: bspec[of _ _ "(a, b)"])
    qed
    ultimately show "(\<exists>H' ys. a = Var H' \<degree>\<degree> map BVar ys \<and> H' \<in> fr \<and> H' \<noteq> H) \<and> FV b \<inter> fr = {}"
      by blast
  qed
  moreover from assms have "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm us))"
    unfolding inv_def by simp
  moreover from assms H(1) have "(FV s \<union> FV t \<union> FVs us) \<inter> fr \<subseteq> insert H (\<Union>(a, b)\<in>set (blm us). FV a)"
    unfolding inv_def by auto
  ultimately show ?thesis using that by blast
qed

lemma map_subst_pats:
  assumes "\<forall>(a, b)\<in>set (probs us). pat a \<and> pat b" "pat_subst (FVs us) \<mu>"
  shows "\<forall>(a, b)\<in>set (probs (map (map_unif_problem (\<lambda>u. \<beta>_nf (mk_subst \<mu> u))) us)). pat a \<and> pat b"
  using assms by (auto simp: FVs_def intro!: pat_mk_subst intro: pat_subst_mono)

lemma map_subst_FVs:
  "FVs (map (map_unif_problem (\<lambda>u. \<beta>_nf (mk_subst \<mu> u))) us) \<subseteq> \<Union> (FV ` \<mu> ` FVs us)"
  unfolding FVs_map using FV_\<beta>_nf_mk_subst by (fastforce simp: FVs_def)

lemma FV_upd_subst:
  "\<Union> (FV ` Var(F := v) ` V) \<subseteq> (V - {F}) \<union> FV v"
  by auto

lemma FV_upd2_subst:
  "\<Union> (FV ` Var(F := v1, G := v2) ` V) \<subseteq> (V - {F, G}) \<union> FV v1 \<union> FV v2"
  by auto

lemma sum_list_zip:
  "length xs = length ys \<Longrightarrow>
    (\<Sum>(a, b)\<leftarrow>zip xs ys. f a + g b) = sum_list (map f xs) + (sum_list (map g ys) :: nat)"
  by (induction xs ys rule: list_induct2) auto

lemma card_Diff_insert_le:
  assumes "finite A" "x \<in> A" "y \<notin> A"
  shows "card (insert y (A - {x})) \<le> card A"
  using assms by (simp add: card_Diff1_less_iff card.insert_remove)
    (metis Suc_pred card_gt_0_iff empty_iff le_refl)


lemma map_subst_Var_pats:
  "\<forall>(a, b)\<in>set (probs us). pat a \<and> pat b \<Longrightarrow> map (map_unif_problem \<beta>_nf) us = us"
proof (induction us)
  case (Cons a us)
  then show ?case by (cases a) auto
qed simp

lemma blm_map2[simp]: "blm (map2 Problem ss ts) = []"
  by (rule blm_no_marker) (auto simp: set_zip)

lemma alm_map2[simp]: "alm (map2 Problem ss ts) = zip ss ts"
  by (subst alm_no_marker) (auto simp: set_zip)

lemma FVs_map2:
  "length ss = length ts \<Longrightarrow> FVs (map2 Problem ss ts) = \<Union> (FV ` set ss) \<union> \<Union> (FV ` set ts)"
  by (induction ss ts rule: list_induct2) auto

lemma UN_zip:
  "length A = length B \<Longrightarrow> (\<Union>(a, b)\<in>set (zip A B). g a \<union> h b) = \<Union> (g ` set A) \<union> \<Union> (h ` set B)"
  by (induction A B rule: list_induct2) auto

lemma UN_zip_fst: "length A = length B \<Longrightarrow> (\<Union>(a, b)\<in>set (zip A B). g a) = \<Union> (g ` set A)"
  by (induction A B rule: list_induct2) auto

lemma Marker_in_image[simp]: "Marker \<in> map_unif_problem f ` A \<longleftrightarrow> Marker \<in> A"
  by (auto simp: image_iff)

lemma Cm_no_marker: "Marker \<notin> set us \<Longrightarrow> Cm us = 0"
  by (simp add: Cm_def blm_no_marker)

lemma unif_step_Problem:
  assumes inv: "inv k fr (Problem s t # us)"
    and cs: "cases k (prep (s, t)) = Some (k', us', \<mu>)"
  shows "\<exists>fr'. inv k' fr' (us' @ map (map_unif_problem (\<lambda>u. \<beta>_nf (mk_subst \<mu> u))) us) \<and>
    (umeasure fr' (us' @ map (map_unif_problem (\<lambda>u. \<beta>_nf (mk_subst \<mu> u))) us),
     umeasure fr (Problem s t # us)) \<in> lex5"
proof -
  define f where "f = (\<lambda>u. \<beta>_nf (mk_subst \<mu> u))"
  define L where "L = Problem s t # us"
  define L' where "L' = us' @ map (map_unif_problem f) us"
  note D = inv_ProblemD[OF inv]
  obtain h1 as1 h2 as2 where prep: "prep (s, t) = ((h1, as1), (h2, as2))"
    by (metis prod.exhaust)
  from prep_eq[OF prep] obtain s' t' where
    otf: "otf\<eta> (s, t) = (s', t') \<or> otf\<eta> (s, t) = (t', s')" and
    s': "s' = h1 \<degree>\<degree> as1" and t': "t' = h2 \<degree>\<degree> as2"
    by blast
  have pats': "pat s'" "pat t'" and FV': "FV s' \<union> FV t' = FV s \<union> FV t"
    using otf otf\<eta>_props[of s t] D(1,2) by auto
  have csz': "csz s' + csz t' \<le> csz s + csz t"
    and nocc': "\<And>fr. nocc fr s' + nocc fr t' = nocc fr s + nocc fr t"
  proof -
    from otf have "csz s' + csz t' \<le> csz s + csz t \<and> (\<forall>fr. nocc fr s' + nocc fr t' = nocc fr s + nocc fr t)"
    proof
      assume "otf\<eta> (s, t) = (s', t')"
      from otf\<eta>_measures[OF this] show ?thesis by simp
    next
      assume "otf\<eta> (s, t) = (t', s')"
      from otf\<eta>_measures[OF this] show ?thesis by (simp add: add.commute)
    qed
    then show "csz s' + csz t' \<le> csz s + csz t" "\<And>fr. nocc fr s' + nocc fr t' = nocc fr s + nocc fr t"
      by auto
  qed
  have FVL: "FVs L = FV s' \<union> FV t' \<union> FVs us" using FV' by (auto simp: L_def)
  have finL: "finite (FVs L - fr)" by simp
  have marker_flex: "\<exists>H xs'. h1 = Var H \<and> as1 = map BVar xs' \<and> H \<in> fr \<and> FV t' = FV t \<and>
      (\<exists>b. t = Abs_m b t')" if M: "Marker \<in> set us"
  proof -
    from inv_Problem_marker[OF inv M] obtain H xs where
      s: "s = Var H \<degree>\<degree> map BVar xs" "H \<in> fr" by blast
    with D(1) have "distinct xs" by simp
    from prep_flex[OF this, of H t] obtain xs' t'' b where
      "prep (Var H \<degree>\<degree> map BVar xs, t) = ((Var H, map BVar xs'), dest_comb t'')"
      "t = Abs_m b t''"
      by blast
    with prep s have "h1 = Var H" "as1 = map BVar xs'" "dest_comb t'' = (h2, as2)" "t = Abs_m b t''"
      by auto
    then show ?thesis using s(2) t' by (auto simp: dest_comb_eq_iff)
  qed
  from cs[unfolded prep] show ?thesis
  proof (cases rule: cases_SomeE)
    case (rigid_rigid p)
    have nM: "Marker \<notin> set us"
      using marker_flex rigid_rigid(1) by blast
    have L': "L' = map2 Problem as1 as2 @ us"
      using rigid_rigid D(3) by (simp add: L'_def f_def map_subst_Var_pats)
    have FVL': "FVs L' = FVs L"
      unfolding L' FVL s' t' rigid_rigid using rigid_rigid(3) by (simp add: FVs_map2)
    have "inv k fr L'"
    proof -
      have "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b"
        using pats' D(3) unfolding L' s' t' rigid_rigid by (auto dest: set_zip_leftD set_zip_rightD)
      moreover have "blm L' = []" using nM by (simp add: L' blm_append blm_no_marker)
      moreover have "FVs L' \<inter> fr = {}"
        using inv_Problem_no_marker[OF inv nM] FVL' by (simp add: L_def)
      ultimately show ?thesis
        using D(4,5) FVL' by (simp add: inv_def L_def)
    qed
    moreover have "(umeasure fr L', umeasure fr L) \<in> lex5"
    proof -
      have "Cm L' = 0" "Cm L = 0" using nM unfolding L' L_def by (auto intro!: Cm_no_marker simp: set_zip)
      moreover have "Nocc fr L' = Nocc fr L"
        using nocc'[of fr] rigid_rigid(3)
        by (simp add: Nocc_def L' L_def s' t' rigid_rigid sum_list_zip)
      moreover have "Csz L' < Csz L"
        using csz' rigid_rigid(3) nM
        by (simp add: Csz_def L' L_def s' t' rigid_rigid sum_list_zip alm_append alm_no_marker)
      ultimately show ?thesis using FVL' by (simp add: umeasure_def)
    qed
    ultimately show ?thesis using rigid_rigid(4) by (auto simp: L'_def L_def f_def)
  next
    case (flex_rigid F xs p j)
    define n where "n = length as2"
    define m where "m = length as1"
    define N where "N = {Suc k..<Suc k + n}"
    define Hs where "Hs = map Var [Suc k..<Suc k + n]"
    define v where "v = Abs_m m (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs)"
    define new where "new = map2 (\<lambda>H s. Problem (H \<degree>\<degree> as1) s) Hs as2"
    have \<mu>: "\<mu> = Var(F := v)" and us': "us' = new @ [Marker]" and k': "k' = k + n"
      using flex_rigid by (simp_all add: v_def Hs_def m_def n_def new_def)
    have L': "L' = new @ Marker # map (map_unif_problem f) us"
      by (simp add: L'_def us')
    have dxs: "distinct xs" using pats' s' flex_rigid(1,2) by simp
    have "j < m" using idx_SomeD[OF flex_rigid(5)] by (simp add: m_def)
    have lenHs: "length Hs = n" by (simp add: Hs_def)
    have setHs: "set Hs = Var ` N" by (simp add: Hs_def N_def del: upt_Suc)
    have distHs: "distinct Hs" by (simp add: Hs_def distinct_map inj_on_def del: upt_Suc)
    have pv: "pat v" using setHs by (auto simp: v_def)
    have cv: "no_loose_bound v 0"
      using \<open>j < m\<close> setHs by (auto simp: v_def no_loose_bound_list_app)
    have FVv: "FV v = N" using setHs by (auto simp: v_def)
    have ps: "pat_subst V \<mu>" for V using pv cv by (auto simp: pat_subst_def \<mu>)
    have probs_new: "probs new = zip (map (\<lambda>H. H \<degree>\<degree> as1) Hs) as2"
      by (simp add: new_def)
    have FVnew: "FVs new = N \<union> \<Union> (FV ` set as2)"
    proof -
      have "FVs new = (\<Union>(a, b)\<in>set (zip (map (\<lambda>H. H \<degree>\<degree> as1) Hs) as2). FV a \<union> FV b)"
        by (simp add: FVs_def probs_new)
      also have "\<dots> = \<Union> (FV ` set (map (\<lambda>H. H \<degree>\<degree> as1) Hs)) \<union> \<Union> (FV ` set as2)"
        using lenHs by (simp add: UN_zip n_def)
      also have "\<Union> (FV ` set (map (\<lambda>H. H \<degree>\<degree> as1) Hs)) = N"
        using setHs flex_rigid(2) by auto
      finally show ?thesis .
    qed
    have F_as2: "F \<notin> \<Union> (FV ` set as2)" using flex_rigid(4) .
    have FVt': "\<Union> (FV ` set as2) = FV t'" using t' flex_rigid(3) by simp
    have FL: "F \<in> FVs L" using FVL s' flex_rigid(1) by simp
    have NL: "N \<inter> {..k} = {}" by (auto simp: N_def)
    have FVL'_sub: "FVs L' \<subseteq> (FVs L - {F}) \<union> N"
    proof -
      have "FVs (map (map_unif_problem f) us) \<subseteq> (FVs us - {F}) \<union> N"
        using map_subst_FVs[of \<mu> us] FV_upd_subst[of F v "FVs us"] FVv by (auto simp: f_def \<mu>)
      moreover have "\<Union> (FV ` set as2) \<subseteq> FVs L - {F}" using FVt' F_as2 FVL by auto
      ultimately show ?thesis using FVnew by (auto simp: L' FVL)
    qed
    have zipD: "(\<exists>H\<in>N. a = Var H \<degree>\<degree> map BVar xs) \<and> b \<in> set as2" if "(a, b) \<in> set (probs new)" for a b
    proof -
      from that have "a \<in> set (map (\<lambda>H. H \<degree>\<degree> as1) Hs)" "b \<in> set as2"
        by (auto simp: probs_new dest: set_zip_leftD set_zip_rightD)
      with setHs flex_rigid(2) show ?thesis by auto
    qed
    have pats_new: "\<forall>(a, b)\<in>set (probs new). pat a \<and> pat b"
      using pats' dxs t' flex_rigid(3) zipD by fastforce
    have heads_new: "map (\<lambda>(s, t). fst (dest_comb s)) (probs new) = Hs"
    proof -
      have "map (\<lambda>(s, t). fst (dest_comb s)) (probs new) =
        map (\<lambda>s. fst (dest_comb s)) (map fst (zip (map (\<lambda>H. H \<degree>\<degree> as1) Hs) as2))"
        by (simp add: probs_new split_def)
      also have "\<dots> = map (\<lambda>H. fst (dest_comb (H \<degree>\<degree> as1))) Hs"
        using lenHs by (simp add: n_def)
      also have "\<dots> = Hs"
        using setHs by (intro map_idI) auto
      finally show ?thesis .
    qed
    have FV_new_rhs: "\<forall>(a, b)\<in>set (probs new). FV b \<subseteq> FV t' \<and> (\<exists>H\<in>N. a = Var H \<degree>\<degree> map BVar xs)"
      using FVt' zipD by fastforce
    have lhs_new: "(\<Union>(s, t)\<in>set (probs new). FV s) = N"
    proof -
      have "(\<Union>(s, t)\<in>set (probs new). FV s) = \<Union> (FV ` set (map (\<lambda>H. H \<degree>\<degree> as1) Hs))"
        using lenHs by (simp add: probs_new UN_zip_fst n_def)
      also have "\<dots> = N" using setHs flex_rigid(2) by auto
      finally show ?thesis .
    qed
    have pats'': "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b"
      using pats_new map_subst_pats[OF D(3) ps[of "FVs us"]] by (auto simp: L' f_def)
    show ?thesis
    proof (cases "Marker \<in> set us")
      case False
      have Ffr: "F \<notin> fr" and Lfr: "FVs L \<inter> fr = {}"
        using inv_Problem_no_marker[OF inv False] FL by (auto simp: L_def)
      have blmL': "blm L' = probs new"
        using False by (simp add: L' blm_append blm_no_marker)
      have "inv k' (fr \<union> N) L'"
        unfolding inv_def
      proof (intro conjI)
        show "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b" by (rule pats'')
        show "FVs L' \<subseteq> {..k'}" using FVL'_sub D(4) by (fastforce simp: k' N_def L_def)
        show "fr \<union> N \<subseteq> {..k'}" using D(5) by (auto simp: k' N_def)
        show "\<forall>(a, b)\<in>set (blm L'). (\<exists>H xs. a = Var H \<degree>\<degree> map BVar xs \<and> H \<in> fr \<union> N) \<and> FV b \<inter> (fr \<union> N) = {}"
          using FV_new_rhs Lfr NL D(4) FVL by (fastforce simp: blmL' L_def)
        show "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm L'))"
          by (simp add: blmL' heads_new distHs)
        show "FVs L' \<inter> (fr \<union> N) \<subseteq> (\<Union>(s, t)\<in>set (blm L'). FV s)"
        proof -
          have "(\<Union>(s, t)\<in>set (blm L'). FV s) = N"
            using lhs_new by (simp add: blmL')
          moreover have "FVs L' \<inter> (fr \<union> N) \<subseteq> N"
            using FVL'_sub Lfr by auto
          ultimately show ?thesis by simp
        qed
      qed
      moreover have "card (FVs L' - (fr \<union> N)) < card (FVs L - fr)"
      proof (rule psubset_card_mono)
        show "FVs L' - (fr \<union> N) \<subset> FVs L - fr"
          using FVL'_sub FL Ffr by auto
      qed simp
      ultimately show ?thesis
        by (intro exI[of _ "fr \<union> N"]) (simp add: umeasure_def L'_def L_def f_def)
    next
      case True
      from marker_flex[OF True] flex_rigid(1) have Ffr: "F \<in> fr" and FVtt: "FV t' = FV t"
        and tb: "\<exists>b. t = Abs_m b t'"
        by auto
      from inv_Problem_marker[OF inv True] obtain H0 xs0 where
        s: "s = Var H0 \<degree>\<degree> map BVar xs0" and "H0 \<in> fr" and tfr: "FV t \<inter> fr = {}" and
        blm_us: "\<forall>(a, b)\<in>set (blm us). (\<exists>H' ys. a = Var H' \<degree>\<degree> map BVar ys \<and> H' \<in> fr \<and> H' \<noteq> H0) \<and> FV b \<inter> fr = {}"
        and dist_us: "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm us))"
        and III: "(FV s \<union> FV t \<union> FVs us) \<inter> fr \<subseteq> insert H0 (\<Union>(a, b)\<in>set (blm us). FV a)"
        by blast
      have "F = H0"
      proof -
        from D(1) s have "distinct xs0" by simp
        from prep_flex[OF this, of H0 t] obtain xs' t'' where
          "prep (Var H0 \<degree>\<degree> map BVar xs0, t) = ((Var H0, map BVar xs'), dest_comb t'')"
          by blast
        with prep s flex_rigid(1) show ?thesis by simp
      qed
      have fixed: "map (\<lambda>(a, b). (f a, f b)) (blm us) = blm us"
      proof (rule map_idI)
        fix x assume x_in: "x \<in> set (blm us)"
        obtain a b where x: "x = (a, b)" by fastforce
        with x_in have ab: "(a, b) \<in> set (blm us)" by simp
        with blm_us obtain H' ys where a: "a = Var H' \<degree>\<degree> map BVar ys" "H' \<noteq> F" and "FV b \<inter> fr = {}"
          using \<open>F = H0\<close> by blast
        with Ffr have "F \<notin> FV b" by auto
        moreover have "pat a" "pat b" using ab set_blm D(3) by fastforce+
        ultimately show "(\<lambda>(a, b). (f a, f b)) x = x"
          using a x by (auto simp: f_def \<mu> intro!: \<beta>_nf_mk_subst_id)
      qed
      have blmL': "blm L' = probs new @ blm us"
        using True fixed by (simp add: L' blm_append)
      have "inv k' (fr \<union> N) L'"
        unfolding inv_def
      proof (intro conjI)
        show "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b" by (rule pats'')
        show "FVs L' \<subseteq> {..k'}" using FVL'_sub D(4) by (fastforce simp: k' N_def L_def)
        show "fr \<union> N \<subseteq> {..k'}" using D(5) by (auto simp: k' N_def)
        show "\<forall>(a, b)\<in>set (blm L'). (\<exists>H xs. a = Var H \<degree>\<degree> map BVar xs \<and> H \<in> fr \<union> N) \<and> FV b \<inter> (fr \<union> N) = {}"
        proof -
          have "FV b \<inter> N = {}" if "(a, b) \<in> set (blm us)" for a b
            using that set_blm D(4) NL by (fastforce simp: FVs_def)
          moreover have "FV t' \<inter> (fr \<union> N) = {}" using FVtt tfr D(4) NL by auto
          ultimately show ?thesis using FV_new_rhs blm_us by (fastforce simp: blmL')
        qed
        show "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm L'))"
        proof -
          have "fst (dest_comb a) \<in> Var ` fr" if "(a, b) \<in> set (blm us)" for a b
            using that blm_us by fastforce
          then have "set (map (\<lambda>(s, t). fst (dest_comb s)) (blm us)) \<inter> set Hs = {}"
            using D(5) setHs NL by fastforce
          then show ?thesis using dist_us distHs by (simp add: blmL' heads_new Int_commute)
        qed
        show "FVs L' \<inter> (fr \<union> N) \<subseteq> (\<Union>(s, t)\<in>set (blm L'). FV s)"
        proof -
          have "N \<subseteq> (\<Union>(s, t)\<in>set (probs new). FV s)"
            using lhs_new by simp
          moreover have "(FVs L - {F}) \<inter> fr \<subseteq> (\<Union>(a, b)\<in>set (blm us). FV a)"
            using III \<open>F = H0\<close> by (auto simp: L_def)
          ultimately show ?thesis using FVL'_sub by (auto simp: blmL')
        qed
      qed
      moreover have "card (FVs L' - (fr \<union> N)) \<le> card (FVs L - fr)"
        by (rule card_mono) (use FVL'_sub in auto)
      moreover have "Cm L' < Cm L"
      proof -
        have "Cm L = cpx t + Cm us" using True by (simp add: Cm_def L_def)
        moreover have "cpx t = Suc (sum_list (map cpx as2))"
          using tb t' flex_rigid(3) by auto
        moreover have "Cm L' = sum_list (map cpx as2) + Cm us"
        proof -
          have "map (\<lambda>(s, t). cpx t) (zip (map (\<lambda>H. H \<degree>\<degree> as1) Hs) as2) =
            map cpx (map snd (zip (map (\<lambda>H. H \<degree>\<degree> as1) Hs) as2))"
            by (simp add: split_def)
          also have "map snd (zip (map (\<lambda>H. H \<degree>\<degree> as1) Hs) as2) = as2"
            using lenHs by (simp add: n_def)
          finally show ?thesis by (simp add: Cm_def blmL' probs_new)
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis
        by (intro exI[of _ "fr \<union> N"]) (auto simp: umeasure_def L'_def L_def f_def le_less)
    qed
  next
    case (flex_flex1 F xs ys)
    define v where "v = Abs_m (length xs) (Var (Suc k) \<degree>\<degree> map BVar (ff1_args xs ys))"
    have \<mu>: "\<mu> = Var(F := v)" using flex_flex1 by (simp add: v_def)
    have L': "L' = map (map_unif_problem f) us" using flex_flex1 by (simp add: L'_def)
    have pv: "pat v" by (simp add: v_def ff1_args_distinct)
    have cv: "no_loose_bound v 0"
      by (auto simp: v_def no_loose_bound_list_app dest: ff1_args_less)
    have ps: "pat_subst V \<mu>" for V using pv cv by (auto simp: pat_subst_def \<mu>)
    have FL: "F \<in> FV s'" "F \<in> FV t'" using s' t' flex_flex1 by auto
    have nM: "Marker \<notin> set us"
    proof
      assume M: "Marker \<in> set us"
      from marker_flex[OF M] flex_flex1(1) have "F \<in> fr" "FV t' = FV t" by auto
      moreover from inv_Problem_marker[OF inv M] have "FV t \<inter> fr = {}" by blast
      ultimately show False using FL by auto
    qed
    have Lfr: "FVs L \<inter> fr = {}" using inv_Problem_no_marker[OF inv nM] by (simp add: L_def)
    have kL: "Suc k \<notin> FVs L" "Suc k \<notin> fr" using D(4,5) by (auto simp: L_def)
    have FVL'_sub: "FVs L' \<subseteq> insert (Suc k) (FVs L - {F})"
      using map_subst_FVs[of \<mu> us] FV_upd_subst[of F v "FVs us"]
      by (auto simp: L' f_def \<mu> v_def FVL)
    have "inv k' fr L'"
      unfolding inv_def
    proof (intro conjI)
      show "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b"
        using map_subst_pats[OF D(3) ps[of "FVs us"]] by (simp add: L' f_def)
      show "FVs L' \<subseteq> {..k'}" using FVL'_sub D(4) flex_flex1(6) by (fastforce simp: L_def)
      show "fr \<subseteq> {..k'}" using D(5) flex_flex1(6) by auto
      have "blm L' = []" using nM by (simp add: L' blm_no_marker)
      then show "\<forall>(a, b)\<in>set (blm L'). (\<exists>H xs. a = Var H \<degree>\<degree> map BVar xs \<and> H \<in> fr) \<and> FV b \<inter> fr = {}"
        "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm L'))"
        by simp_all
      show "FVs L' \<inter> fr \<subseteq> (\<Union>(s, t)\<in>set (blm L'). FV s)"
        using FVL'_sub Lfr kL by auto
    qed
    moreover have "card (FVs L' - fr) \<le> card (FVs L - fr)"
    proof -
      have "FVs L' - fr \<subseteq> insert (Suc k) ((FVs L - fr) - {F})" using FVL'_sub by auto
      moreover have "card (insert (Suc k) ((FVs L - fr) - {F})) \<le> card (FVs L - fr)"
        using FL Lfr kL by (intro card_Diff_insert_le) (auto simp: FVL)
      ultimately show ?thesis by (meson card_mono finite_insert finite_Diff finite_FVs le_trans)
    qed
    moreover have "Cm L' = Cm L" using nM by (simp add: Cm_no_marker L' L_def)
    moreover have "Nocc fr L' < Nocc fr L"
    proof -
      have "Nocc fr L' = Nocc fr us"
      proof -
        have "nocc fr (f a) = nocc fr a" if "pat a" "FV a \<subseteq> FVs us" for a
        proof -
          have "\<forall>G\<in>FV a. nocc fr (\<mu> G) = nocc fr (Var G)"
            using that Lfr kL by (auto simp: \<mu> v_def L_def)
          with that ps show ?thesis by (simp add: f_def nocc_\<beta>_nf_mk_subst)
        qed
        moreover have "pat a \<and> pat b \<and> FV a \<subseteq> FVs us \<and> FV b \<subseteq> FVs us" if "(a, b) \<in> set (probs us)" for a b
          using that D(3) by (auto simp: FVs_def)
        ultimately have "nocc fr (f a) + nocc fr (f b) = nocc fr a + nocc fr b" if "(a, b) \<in> set (probs us)" for a b
          using that by presburger
        then show ?thesis
          unfolding Nocc_def L' by (auto intro!: arg_cong[where f = sum_list] map_cong)
      qed
      moreover have "Nocc fr L = nocc fr s' + nocc fr t' + Nocc fr us"
        using nocc'[of fr] by (simp add: Nocc_def L_def)
      moreover have "0 < nocc fr s'" "0 < nocc fr t'"
        using FL Lfr by (auto intro!: nocc_pos simp: FVL)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis
      by (intro exI[of _ fr]) (auto simp: umeasure_def L'_def L_def f_def flex_flex1(6))
  next
    case (flex_flex2 F G xs ys zs1 zs2)
    define v1 where "v1 = Abs_m (length xs) (Var (Suc k) \<degree>\<degree> map BVar zs1)"
    define v2 where "v2 = Abs_m (length ys) (Var (Suc k) \<degree>\<degree> map BVar zs2)"
    have \<mu>: "\<mu> = Var(F := v1, G := v2)" using flex_flex2 by (simp add: v1_def v2_def)
    have L': "L' = map (map_unif_problem f) us" using flex_flex2 by (simp add: L'_def)
    have "distinct ys" using pats' t' flex_flex2 by simp
    then have pv: "pat v1" "pat v2"
      using flex_flex2(6) ff2_args_distinct1 ff2_args_distinct2 by (auto simp: v1_def v2_def)
    have cv: "no_loose_bound v1 0" "no_loose_bound v2 0"
      using ff2_args_less[OF flex_flex2(6)]
      by (auto simp: v1_def v2_def no_loose_bound_list_app)
    have ps: "pat_subst V \<mu>" for V using pv cv by (auto simp: pat_subst_def \<mu>)
    have fv: "flexval (\<mu> H)" for H by (auto simp: \<mu> v1_def v2_def)
    have FL: "F \<in> FV s'" "G \<in> FV t'" using s' t' flex_flex2 by auto
    have kL: "Suc k \<notin> FVs L" "Suc k \<notin> fr" using D(4,5) by (auto simp: L_def)
    have FVL'_sub: "FVs L' \<subseteq> insert (Suc k) (FVs L - {F, G})"
      using map_subst_FVs[of \<mu> us] FV_upd2_subst[of F v1 G v2 "FVs us"]
      by (auto simp: L' f_def \<mu> v1_def v2_def FVL)
    have pats'': "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b"
      using map_subst_pats[OF D(3) ps[of "FVs us"]] by (simp add: L' f_def)
    have FVs': "FVs L' \<subseteq> {..k'}" using FVL'_sub D(4) flex_flex2(7) by (fastforce simp: L_def)
    show ?thesis
    proof (cases "Marker \<in> set us")
      case False
      have Lfr: "FVs L \<inter> fr = {}" using inv_Problem_no_marker[OF inv False] by (simp add: L_def)
      have "inv k' fr L'"
        unfolding inv_def
      proof (intro conjI)
        show "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b" by (rule pats'')
        show "FVs L' \<subseteq> {..k'}" by (rule FVs')
        show "fr \<subseteq> {..k'}" using D(5) flex_flex2(7) by auto
        have "blm L' = []" using False by (simp add: L' blm_no_marker)
        then show "\<forall>(a, b)\<in>set (blm L'). (\<exists>H xs. a = Var H \<degree>\<degree> map BVar xs \<and> H \<in> fr) \<and> FV b \<inter> fr = {}"
          "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm L'))"
          by simp_all
        show "FVs L' \<inter> fr \<subseteq> (\<Union>(s, t)\<in>set (blm L'). FV s)"
          using FVL'_sub Lfr kL by auto
      qed
      moreover have "card (FVs L' - fr) < card (FVs L - fr)"
      proof -
        have "FVs L' - fr \<subseteq> insert (Suc k) ((FVs L - fr) - {F} - {G})" using FVL'_sub by auto
        moreover have "card (insert (Suc k) ((FVs L - fr) - {F} - {G})) < card (FVs L - fr)"
        proof -
          have "F \<in> FVs L - fr" "G \<in> FVs L - fr - {F}"
            using FL Lfr flex_flex2(3) by (auto simp: FVL)
          then have "card ((FVs L - fr) - {F} - {G}) + 2 = card (FVs L - fr)"
          proof -
            assume F: "F \<in> FVs L - fr" and G: "G \<in> FVs L - fr - {F}"
            have "card (FVs L - fr - {F}) = card (FVs L - fr) - 1"
              using F by (simp add: card_Diff_singleton)
            moreover have "card (FVs L - fr - {F} - {G}) = card (FVs L - fr - {F}) - 1"
              using G by (simp add: card_Diff_singleton)
            moreover have "0 < card (FVs L - fr - {F})"
              using G by (auto simp: card_gt_0_iff)
            ultimately show ?thesis by linarith
          qed
          then show ?thesis using kL by simp
        qed
        ultimately show ?thesis by (meson card_mono finite_insert finite_Diff finite_FVs le_less_trans)
      qed
      ultimately show ?thesis
        by (intro exI[of _ fr]) (auto simp: umeasure_def L'_def L_def f_def flex_flex2(7))
    next
      case True
      from marker_flex[OF True] flex_flex2(1) have Ffr: "F \<in> fr" and FVtt: "FV t' = FV t"
        and tb: "\<exists>b. t = Abs_m b t'"
        by auto
      from inv_Problem_marker[OF inv True] obtain H0 xs0 where
        s: "s = Var H0 \<degree>\<degree> map BVar xs0" and "H0 \<in> fr" and tfr: "FV t \<inter> fr = {}" and
        blm_us: "\<forall>(a, b)\<in>set (blm us). (\<exists>H' ys. a = Var H' \<degree>\<degree> map BVar ys \<and> H' \<in> fr \<and> H' \<noteq> H0) \<and> FV b \<inter> fr = {}"
        and dist_us: "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm us))"
        and III: "(FV s \<union> FV t \<union> FVs us) \<inter> fr \<subseteq> insert H0 (\<Union>(a, b)\<in>set (blm us). FV a)"
        by blast
      have "F = H0"
      proof -
        from D(1) s have "distinct xs0" by simp
        from prep_flex[OF this, of H0 t] obtain xs' t'' where
          "prep (Var H0 \<degree>\<degree> map BVar xs0, t) = ((Var H0, map BVar xs'), dest_comb t'')"
          by blast
        with prep s flex_flex2(1) show ?thesis by simp
      qed
      have Gfr: "G \<notin> fr" using FL FVtt tfr by auto
      have lhs_fixed: "f a = a" if "(a, b) \<in> set (blm us)" for a b
      proof -
        from that blm_us obtain H' ys' where a: "a = Var H' \<degree>\<degree> map BVar ys'" "H' \<in> fr" "H' \<noteq> F"
          using \<open>F = H0\<close> by blast
        with Gfr have "H' \<noteq> G" by auto
        moreover have "pat a" using that set_blm D(3) by fastforce
        ultimately show ?thesis
          using a by (auto simp: f_def \<mu> intro!: \<beta>_nf_mk_subst_id)
      qed
      have blmL': "blm L' = map (\<lambda>(a, b). (a, f b)) (blm us)"
        using True lhs_fixed by (auto simp: L' intro!: map_cong)
      have FV_fb: "FV (f b) \<subseteq> insert (Suc k) (FV b - {F, G})" for b
        using FV_\<beta>_nf_mk_subst[of \<mu> b] FV_upd2_subst[of F v1 G v2 "FV b"]
        by (auto simp: f_def \<mu> v1_def v2_def)
      have "inv k' fr L'"
        unfolding inv_def
      proof (intro conjI)
        show "\<forall>(a, b)\<in>set (probs L'). pat a \<and> pat b" by (rule pats'')
        show "FVs L' \<subseteq> {..k'}" by (rule FVs')
        show "fr \<subseteq> {..k'}" using D(5) flex_flex2(7) by auto
        show "\<forall>(a, b)\<in>set (blm L'). (\<exists>H xs. a = Var H \<degree>\<degree> map BVar xs \<and> H \<in> fr) \<and> FV b \<inter> fr = {}"
          using blm_us FV_fb kL by (fastforce simp: blmL')
        show "distinct (map (\<lambda>(s, t). fst (dest_comb s)) (blm L'))"
          using dist_us by (simp add: blmL' comp_def split_def)
        show "FVs L' \<inter> fr \<subseteq> (\<Union>(s, t)\<in>set (blm L'). FV s)"
        proof -
          have "(\<Union>(s, t)\<in>set (blm L'). FV s) = (\<Union>(a, b)\<in>set (blm us). FV a)"
            by (force simp: blmL')
          moreover have "FVs L' \<inter> fr \<subseteq> (FVs L - {F}) \<inter> fr" using FVL'_sub kL by auto
          ultimately show ?thesis using III \<open>F = H0\<close> by (auto simp: L_def)
        qed
      qed
      moreover have "card (FVs L' - fr) \<le> card (FVs L - fr)"
      proof -
        have "FVs L' - fr \<subseteq> insert (Suc k) ((FVs L - fr) - {G})" using FVL'_sub by auto
        moreover have "card (insert (Suc k) ((FVs L - fr) - {G})) \<le> card (FVs L - fr)"
          using FL Gfr kL by (intro card_Diff_insert_le) (auto simp: FVL)
        ultimately show ?thesis by (meson card_mono finite_insert finite_Diff finite_FVs le_trans)
      qed
      moreover have "Cm L' < Cm L"
      proof -
        have "Cm L = cpx t + Cm us" using True by (simp add: Cm_def L_def)
        moreover have "cpx t = 1" using tb t' flex_flex2(2) by auto
        moreover have "Cm L' = Cm us"
        proof -
          have "cpx (f b) = cpx b" if "(a, b) \<in> set (blm us)" for a b
          proof -
            have "pat b" "FV b \<subseteq> FVs us" using that set_blm D(3) by (fastforce simp: FVs_def)+
            then show ?thesis using ps fv by (simp add: f_def cpx_\<beta>_nf_mk_subst)
          qed
          then show ?thesis
            unfolding Cm_def blmL' by (auto intro!: arg_cong[where f = sum_list] map_cong)
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis
        by (intro exI[of _ fr]) (auto simp: umeasure_def L'_def L_def f_def flex_flex2(7))
    qed
  qed
qed



subsection \<open>Termination\<close>

theorem unif_dom_inv: "inv k fr us \<Longrightarrow> unif_dom (k, us, \<phi>)"
proof -
  have "\<forall>k fr us \<phi>. umeasure fr us = m \<longrightarrow> inv k fr us \<longrightarrow> unif_dom (k, us, \<phi>)" for m
  proof (induction m rule: wf_induct[OF wf_lex5])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix k fr us \<phi> assume m: "umeasure fr us = m" and inv: "inv k fr us"
      show "unif_dom (k, us, \<phi>)"
      proof (cases us)
        case Nil
        then show ?thesis by (simp add: unif.domintros(1))
      next
        case (Cons u us0)
        show ?thesis
        proof (cases u)
          case Marker
          with Cons inv have "inv k fr us0" "(umeasure fr us0, m) \<in> lex5"
            using unif_step_Marker m by auto
          with "1.IH" have "unif_dom (k, us0, \<phi>)" by blast
          then show ?thesis using Cons Marker by (simp add: unif.domintros(2))
        next
          case (Problem s t)
          show ?thesis
            unfolding Cons Problem
          proof (rule unif.domintros(3))
            fix k' us' \<mu> assume "cases k (prep (s, t)) = Some (k', us', \<mu>)"
            from unif_step_Problem[OF _ this] inv Cons Problem m obtain fr' where
              "inv k' fr' (us' @ map (map_unif_problem (\<lambda>u. \<beta>_nf (mk_subst \<mu> u))) us0)"
              "(umeasure fr' (us' @ map (map_unif_problem (\<lambda>u. \<beta>_nf (mk_subst \<mu> u))) us0), m) \<in> lex5"
              by blast
            with "1.IH" show "unif_dom (k', us' @ map (map_unif_problem (\<lambda>t. \<beta>_nf (mk_subst \<mu> t))) us0, \<mu> \<circ>\<^sub>s \<phi>)"
              by blast
          qed
        qed
      qed
    qed
  qed
  then show "inv k fr us \<Longrightarrow> unif_dom (k, us, \<phi>)" by blast
qed

text \<open>In particular, \<open>unif\<close> terminates when started on a single pattern problem.\<close>

lemma inv_init:
  assumes "pat s" "pat t" "FV s \<union> FV t \<subseteq> {..k}"
  shows "inv k {} [Problem s t]"
  using assms by (simp add: inv_def)

theorem unif_terminates:
  assumes "pat s" "pat t" "FV s \<union> FV t \<subseteq> {..k}"
  shows "unif_dom (k, [Problem s t], \<phi>)"
  using unif_dom_inv[OF inv_init[OF assms]] .

lemma FV_le_max_var: "FV s \<union> FV t \<subseteq> {..max_var s t}"
  by (auto simp: max_var_def)

theorem unify_terminates: "pat s \<Longrightarrow> pat t \<Longrightarrow> unif_dom (max_var s t, [Problem s t], Var)"
  using unif_terminates FV_le_max_var by blast

end
