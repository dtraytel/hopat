section \<open>The Unification Algorithm\<close>

theory Unification
  imports Unif_Prelims
begin

text \<open>
  This theory defines the first version of the unification algorithm for higher-order
  patterns from Grobauer's thesis (Chapter 2.1), including the marker symbol that Grobauer
  introduces for the termination proof (Section 2.2.1). Substitutions are represented as
  functions from free variables to terms. The parameter \<open>k\<close> is Grobauer's ``hidden
  parameter'' for the choice of new variables: all variables in use are at most \<open>k\<close>, and new
  variables are taken from \<open>k + 1, k + 2, \<dots>\<close>.
\<close>

subsection \<open>Auxiliary functions\<close>

fun dest_comb :: "dB \<Rightarrow> (dB \<times> dB list)" where
  "dest_comb (t1 \<degree> t2) = (let (s, xs) = dest_comb t1 in (s, xs @ [t2]))"
| "dest_comb t = (t, [])"

lemma dest_comb_eq_iff:
  "dest_comb t = (u, xs) \<longleftrightarrow> (t = u \<degree>\<degree> xs \<and> \<not>(\<exists>u1 u2. u = u1 \<degree> u2))"
  apply (induct t arbitrary: u xs rule: dest_comb.induct)
  apply (auto simp: App_eq_foldl_conv split: prod.splits if_splits)
  apply (smt prod.inject)
  apply (smt prod.inject)
  apply (smt prod.inject)
  apply (smt prod.inject)
  done

lemma dest_comb_atom[simp]: "is_atom h \<Longrightarrow> dest_comb (h \<degree>\<degree> ts) = (h, ts)"
  by (auto simp: dest_comb_eq_iff is_atom_def)

lemma dest_comb_Abs[simp]: "dest_comb (Abs t) = (Abs t, [])"
  by simp

text \<open>Grobauer's function \<open>idx\<close> (Section 1.3.2): lists are indexed from the end.\<close>

fun idx :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "idx [] _ = None"
| "idx (x # xs) y = (if x = y then Some (length xs) else idx xs y)"

fun is_BVar :: "dB \<Rightarrow> bool" where
  "is_BVar (BVar _) = True"
| "is_BVar _ = False"

fun unBVar :: "dB \<Rightarrow> nat" where
  "unBVar (BVar x) = x"
| "unBVar _ = 0"

text \<open>
  The arguments of the new variable in the (flex-flex-1) case:
  \<open>[k | 0 \<le> k \<le> m - 1, x\<^sub>k = y\<^sub>k]\<close> in Grobauer's reverse indexing.
\<close>

definition ff1_args :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "ff1_args xs ys = map (\<lambda>i. length xs - 1 - i) (filter (\<lambda>i. xs ! i = ys ! i) [0..<length xs])"

text \<open>
  The arguments of the new variable in the (flex-flex-2) case, as computed by \<open>cases\<^sub>3\<close>
  (Grobauer, Section 4.1): for every argument \<open>y\<^sub>k\<close> that also occurs in \<open>x\<^sub>m\<close>, say as \<open>x\<^sub>j\<close>,
  we obtain \<open>j\<close> in the first and \<open>k\<close> in the second list.
\<close>

definition ff2_args :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list" where
  "ff2_args xs ys = (let is = filter (\<lambda>i. ys ! i \<in> set xs) [0..<length ys] in
    (map (\<lambda>i. the (idx xs (ys ! i))) is, map (\<lambda>i. length ys - 1 - i) is))"


subsection \<open>Reducing a single unification problem\<close>

datatype unif_problem = Problem dB dB | Marker

fun map_unif_problem :: "(dB \<Rightarrow> dB) \<Rightarrow> unif_problem \<Rightarrow> unif_problem" where
  "map_unif_problem _ Marker = Marker"
| "map_unif_problem f (Problem u1 u2) = Problem (f u1) (f u2)"

text \<open>
  The function \<open>cases\<close> corresponds to Grobauer's \<open>cases\<^sub>1\<close> (with the marker of Section 2.2.1).
  The new variables are \<open>Var (k + 1), \<dots>\<close>; the returned number is the new upper bound on the
  variables in use. The two flex-flex cases compute their argument lists like \<open>cases\<^sub>3\<close>, since
  \<open>cases\<^sub>1\<close> leaves them underspecified. A problem \<open>F(x\<^sub>m) = F(y\<^sub>n)\<close> with \<open>m \<noteq> n\<close> is ill-typed and
  therefore rejected.
\<close>

fun cases :: "nat \<Rightarrow> (dB \<times> dB list) \<times> (dB \<times> dB list) \<Rightarrow>
    (nat \<times> unif_problem list \<times> (nat \<Rightarrow> dB)) option" where
  rigid_rigid: "cases k ((BVar p, ss), (BVar q, ts)) =
    (if p = q \<and> length ss = length ts then Some (k, map2 Problem ss ts, Var) else None)"
| flex_rigid: "cases k ((Var F, xs), (BVar p, ss)) =
    (if (\<forall>x\<in>set xs. is_BVar x) \<and> F \<notin> \<Union> (FV ` set ss) then
      (case idx xs (BVar p) of
        None \<Rightarrow> None
      | Some j \<Rightarrow>
          let m = length xs; n = length ss; Hs = map Var [Suc k..<Suc k + n] in
          Some (k + n, map2 (\<lambda>H s. Problem (H \<degree>\<degree> xs) s) Hs ss @ [Marker],
            Var(F := Abs_m m (BVar j \<degree>\<degree> map (\<lambda>H. H \<degree>\<degree> map BVar (downs m)) Hs))))
    else None)"
| flex_flex: "cases k ((Var F, xs), (Var G, ys)) =
    (if (\<forall>x\<in>set xs. is_BVar x) \<and> (\<forall>y\<in>set ys. is_BVar y) then
      (let m = length xs; n = length ys; H = Var (Suc k) in
      if F = G then
        (if m = n then
          Some (Suc k, [], Var(F := Abs_m m (H \<degree>\<degree> map BVar (ff1_args (map unBVar xs) (map unBVar ys)))))
        else None)
      else
        (case ff2_args (map unBVar xs) (map unBVar ys) of (zs1, zs2) \<Rightarrow>
          Some (Suc k, [], Var(F := Abs_m m (H \<degree>\<degree> map BVar zs1), G := Abs_m n (H \<degree>\<degree> map BVar zs2)))))
    else None)"
| other: "cases _ _ = None"


subsection \<open>On-the-fly \<open>\<eta>\<close>-conversion and orientation\<close>

fun count_Abs :: "dB \<Rightarrow> nat" where
  "count_Abs (Abs t) = 1 + count_Abs t"
| "count_Abs (t1 \<degree> t2) = count_Abs t1 + count_Abs t2"
| "count_Abs t = 0"

lemma count_Abs_lift: "count_Abs (lift t i) = count_Abs t"
  by (induction t arbitrary: i rule: count_Abs.induct) auto

function (sequential) otf\<eta> :: "(dB \<times> dB) \<Rightarrow> (dB \<times> dB)" where
  "otf\<eta> (Abs s', Abs t') = otf\<eta> (s', t')"
| "otf\<eta> (Abs s', t) = otf\<eta> (s', lift t 0 \<degree> BVar 0)"
| "otf\<eta> (s, Abs t') = otf\<eta> (lift s 0 \<degree> BVar 0, t')"
| "otf\<eta> t = t"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, t). count_Abs s + count_Abs t)") (auto simp add: count_Abs_lift)

fun tw :: "(dB \<times> dB) \<Rightarrow> (dB \<times> dB)" where
  "tw (s, t) = (case dest_comb s of (Var F, _) \<Rightarrow> (s, t) | _ \<Rightarrow> (t, s))"

definition prep :: "dB \<times> dB \<Rightarrow> (dB \<times> dB list) \<times> (dB \<times> dB list)" where
  "prep u = (case tw (otf\<eta> u) of (s, t) \<Rightarrow> (dest_comb s, dest_comb t))"


subsection \<open>Solving a list of unification problems\<close>

text \<open>
  Grobauer's \<open>unif\<^sub>1\<close>: the first problem is reduced by \<open>cases \<circ> tw \<circ> otf\<eta>\<close>, and the resulting
  substitution is applied to the remaining problems, which are then \<open>\<beta>\<close>-normalized.
\<close>

function (domintros) unif :: "nat \<Rightarrow> unif_problem list \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> (nat \<Rightarrow> dB) option" where
  "unif k [] \<phi> = Some \<phi>"
| "unif k (Marker # us) \<phi> = unif k us \<phi>"
| "unif k (Problem s t # us) \<phi> = (case cases k (prep (s, t)) of
      None \<Rightarrow> None
    | Some (k', us', \<mu>) \<Rightarrow>
        unif k' (us' @ map (map_unif_problem (\<lambda>t. \<beta>_nf (mk_subst \<mu> t))) us) (\<mu> \<circ>\<^sub>s \<phi>))"
  by pat_completeness auto

text \<open>Unification of two terms: all variables in use are bounded by the largest variable.\<close>

definition max_var :: "dB \<Rightarrow> dB \<Rightarrow> nat" where
  "max_var s t = Max (insert 0 (FV s \<union> FV t))"

definition unify :: "dB \<Rightarrow> dB \<Rightarrow> (nat \<Rightarrow> dB) option" where
  "unify s t = unif (max_var s t) [Problem s t] Var"



subsection \<open>Basic properties\<close>

subsubsection \<open>Function \<open>idx\<close> and argument lists\<close>

text \<open>Grobauer's Lemmas 3 and 4.\<close>

lemma idx_None_iff: "idx xs y = None \<longleftrightarrow> y \<notin> set xs"
  by (induction xs) auto

lemma idx_SomeD: "idx xs y = Some j \<Longrightarrow> j < length xs \<and> xs ! (length xs - Suc j) = y"
  by (induction xs) (auto split: if_splits simp: nth_Cons')

lemma idx_distinct: "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> idx xs (xs ! i) = Some (length xs - Suc i)"
proof (induction xs arbitrary: i)
  case (Cons x xs)
  then show ?case by (cases i) auto
qed simp

lemma idx_Some_iff_distinct:
  "distinct xs \<Longrightarrow> idx xs y = Some j \<longleftrightarrow> j < length xs \<and> xs ! (length xs - Suc j) = y"
  using idx_distinct[of xs "length xs - Suc j"] idx_SomeD[of xs y j] by auto

lemma all_is_BVar_iff: "(\<forall>x\<in>set xs. is_BVar x) \<longleftrightarrow> (\<exists>ys. xs = map BVar ys)"
proof
  assume "\<forall>x\<in>set xs. is_BVar x"
  then have "xs = map BVar (map unBVar xs)"
    by (induction xs) (auto elim: is_BVar.elims)
  then show "\<exists>ys. xs = map BVar ys" ..
qed auto

lemma map_unBVar_map_BVar[simp]: "map unBVar (map BVar xs) = xs"
  by (induction xs) auto

lemma unBVar_comp_BVar[simp]: "unBVar \<circ> BVar = id"
  by auto

lemma no_loose_bound_list_app:
  "no_loose_bound (t \<degree>\<degree> ts) i \<longleftrightarrow> no_loose_bound t i \<and> (\<forall>s\<in>set ts. no_loose_bound s i)"
  by (induction ts arbitrary: t) auto

lemma no_loose_bound_Abs_m[simp]: "no_loose_bound (Abs_m m t) i \<longleftrightarrow> no_loose_bound t (i + m)"
  using loose_bound_Abs_m by simp

lemma ff1_args_distinct: "distinct (ff1_args xs ys)"
  unfolding ff1_args_def by (auto simp: distinct_map inj_on_def)

lemma ff1_args_less: "z \<in> set (ff1_args xs ys) \<Longrightarrow> z < length xs"
  unfolding ff1_args_def by auto

lemma ff2_args_length: "ff2_args xs ys = (zs1, zs2) \<Longrightarrow> length zs1 = length zs2"
  unfolding ff2_args_def by (auto simp: Let_def)

lemma ff2_args_less:
  "ff2_args xs ys = (zs1, zs2) \<Longrightarrow> z \<in> set zs1 \<Longrightarrow> z < length xs"
  "ff2_args xs ys = (zs1, zs2) \<Longrightarrow> z \<in> set zs2 \<Longrightarrow> z < length ys"
  unfolding ff2_args_def
  by (auto simp: Let_def dest!: idx_SomeD split: option.splits)
    (metis idx_None_iff idx_SomeD option.exhaust_sel)

lemma ff2_args_distinct2: "ff2_args xs ys = (zs1, zs2) \<Longrightarrow> distinct zs2"
  unfolding ff2_args_def by (auto simp: Let_def distinct_map inj_on_def)

lemma ff2_args_distinct1:
  assumes "ff2_args xs ys = (zs1, zs2)" "distinct ys"
  shows "distinct zs1"
proof -
  let ?is = "filter (\<lambda>i. ys ! i \<in> set xs) [0..<length ys]"
  have "inj_on (\<lambda>i. the (idx xs (ys ! i))) (set ?is)"
  proof (rule inj_onI)
    fix i i' assume ii': "i \<in> set ?is" "i' \<in> set ?is"
      and eq: "the (idx xs (ys ! i)) = the (idx xs (ys ! i'))"
    have some: "idx xs y = Some (the (idx xs y))" if "y \<in> set xs" for y
      using that idx_None_iff[of xs y] by auto
    from ii' have "idx xs (ys ! i) = Some (the (idx xs (ys ! i)))"
      "idx xs (ys ! i') = Some (the (idx xs (ys ! i')))"
      by (auto intro: some)
    with eq have "ys ! i = ys ! i'"
      by (metis idx_SomeD)
    with \<open>i \<in> set ?is\<close> \<open>i' \<in> set ?is\<close> assms(2) show "i = i'"
      by (auto simp: nth_eq_iff_index_eq)
  qed
  with assms(1) show ?thesis
    unfolding ff2_args_def by (auto simp: Let_def distinct_map)
qed


subsubsection \<open>On-the-fly \<open>\<eta>\<close>-conversion\<close>

lemma not_Abs_lift: "(\<And>u. t \<noteq> Abs u) \<Longrightarrow> (\<And>u. lift t i \<noteq> Abs u)"
  by (cases t) auto

lemma otf\<eta>_simps[simp]:
  "otf\<eta> (Abs s, Abs t) = otf\<eta> (s, t)"
  "(\<And>u. t \<noteq> Abs u) \<Longrightarrow> otf\<eta> (Abs s, t) = otf\<eta> (s, lift t 0 \<degree> BVar 0)"
  "(\<And>u. s \<noteq> Abs u) \<Longrightarrow> otf\<eta> (s, Abs t) = otf\<eta> (lift s 0 \<degree> BVar 0, t)"
  "(\<And>u. s \<noteq> Abs u) \<Longrightarrow> (\<And>u. t \<noteq> Abs u) \<Longrightarrow> otf\<eta> (s, t) = (s, t)"
    apply simp
   apply (cases t; auto)
  apply (cases s; auto)
  apply (cases s; cases t; auto)
  done

declare otf\<eta>.simps[simp del]

lemma otf\<eta>_induct[case_names AbsAbs AbsL AbsR other]:
  assumes "\<And>s t. P s t \<Longrightarrow> P (Abs s) (Abs t)"
    "\<And>s t. (\<And>u. t \<noteq> Abs u) \<Longrightarrow> P s (lift t 0 \<degree> BVar 0) \<Longrightarrow> P (Abs s) t"
    "\<And>s t. (\<And>u. s \<noteq> Abs u) \<Longrightarrow> P (lift s 0 \<degree> BVar 0) t \<Longrightarrow> P s (Abs t)"
    "\<And>s t. (\<And>u. s \<noteq> Abs u) \<Longrightarrow> (\<And>u. t \<noteq> Abs u) \<Longrightarrow> P s t"
  shows "P s t"
proof (induction "count_Abs s + count_Abs t" arbitrary: s t rule: less_induct)
  case less
  show ?case
  proof (cases "\<exists>u. s = Abs u")
    case True
    then obtain s' where s: "s = Abs s'" by blast
    show ?thesis
    proof (cases "\<exists>u. t = Abs u")
      case True
      then obtain t' where "t = Abs t'" by blast
      with s show ?thesis using assms(1) less by simp
    next
      case False
      with s show ?thesis using assms(2) less by (auto simp: count_Abs_lift)
    qed
  next
    case False
    show ?thesis
    proof (cases "\<exists>u. t = Abs u")
      case True
      then obtain t' where "t = Abs t'" by blast
      with False show ?thesis using assms(3) less by (auto simp: count_Abs_lift)
    next
      case False': False
      with False show ?thesis using assms(4) by auto
    qed
  qed
qed

lemma pat_lift_app_BVar0:
  assumes "pat t" "\<And>u. t \<noteq> Abs u"
  shows "pat (lift t 0 \<degree> BVar 0)"
  using assms(1)
proof (cases rule: pat_cases)
  case (BVar x ts)
  then show ?thesis
    using pat_lift[of _ 0] by simp
next
  case (Var F xs)
  then have "lift t 0 \<degree> BVar 0 = Var F \<degree>\<degree> map BVar (map Suc xs @ [0])"
    by (simp add: comp_def)
  moreover have "distinct (map Suc xs @ [0])"
    using Var by (auto simp: distinct_map)
  ultimately show ?thesis by (simp del: map_append)
qed (use assms in simp)

lemma otf\<eta>_props:
  assumes "otf\<eta> (s, t) = (s', t')" "pat s" "pat t"
  shows "pat s'" "pat t'" "FV s' \<union> FV t' = FV s \<union> FV t"
proof -
  have "pat (fst (otf\<eta> (s, t))) \<and> pat (snd (otf\<eta> (s, t))) \<and>
    FV (fst (otf\<eta> (s, t))) \<union> FV (snd (otf\<eta> (s, t))) = FV s \<union> FV t"
    using assms(2,3)
  proof (induction s t rule: otf\<eta>_induct)
    case (AbsL s t)
    then show ?case using pat_lift_app_BVar0[of t] by simp
  next
    case (AbsR s t)
    then show ?case using pat_lift_app_BVar0[of s] by (simp add: Un_commute)
  qed auto
  with assms(1) show "pat s'" "pat t'" "FV s' \<union> FV t' = FV s \<union> FV t" by auto
qed

lemma otf\<eta>_typing:
  assumes "otf\<eta> (s, t) = (s', t')" "(e1, \<tau>) \<turnstile> s : T" "(e1, \<tau>) \<turnstile> t : T"
  shows "\<exists>e1' T'. (e1', \<tau>) \<turnstile> s' : T' \<and> (e1', \<tau>) \<turnstile> t' : T'"
proof -
  have "\<exists>e1' T'. (e1', \<tau>) \<turnstile> fst (otf\<eta> (s, t)) : T' \<and> (e1', \<tau>) \<turnstile> snd (otf\<eta> (s, t)) : T'"
    using assms(2,3)
  proof (induction s t arbitrary: e1 T rule: otf\<eta>_induct)
    case (AbsAbs s t)
    from AbsAbs.prems obtain A B where "(e1\<langle>0:A\<rangle>, \<tau>) \<turnstile> s : B" "(e1\<langle>0:A\<rangle>, \<tau>) \<turnstile> t : B"
      by auto
    with AbsAbs.IH show ?case by simp
  next
    case (AbsL s t)
    from AbsL.prems obtain A B where "T = A \<Rightarrow> B" "(e1\<langle>0:A\<rangle>, \<tau>) \<turnstile> s : B"
      by auto
    moreover from AbsL.prems \<open>T = A \<Rightarrow> B\<close> have "(e1\<langle>0:A\<rangle>, \<tau>) \<turnstile> lift t 0 \<degree> BVar 0 : B"
      by auto
    ultimately show ?case using AbsL by simp
  next
    case (AbsR s t)
    from AbsR.prems obtain A B where "T = A \<Rightarrow> B" "(e1\<langle>0:A\<rangle>, \<tau>) \<turnstile> t : B"
      by auto
    moreover from AbsR.prems \<open>T = A \<Rightarrow> B\<close> have "(e1\<langle>0:A\<rangle>, \<tau>) \<turnstile> lift s 0 \<degree> BVar 0 : B"
      by auto
    ultimately show ?case using AbsR by simp
  qed auto
  with assms(1) show ?thesis by simp
qed

text \<open>If the left-hand side is a flexible term without leading abstraction, \<open>otf\<eta>\<close> keeps it
  flexible with the same head and strips the abstractions of the right-hand side.\<close>

lemma otf\<eta>_flex:
  assumes "distinct xs"
  shows "\<exists>xs' b. otf\<eta> (Var H \<degree>\<degree> map BVar xs, t) = (Var H \<degree>\<degree> map BVar xs', snd (otf\<eta> (Var H \<degree>\<degree> map BVar xs, t)))
    \<and> distinct xs' \<and> t = Abs_m b (snd (otf\<eta> (Var H \<degree>\<degree> map BVar xs, t)))"
  using assms
proof (induction t arbitrary: xs)
  case (Abs t)
  have eq: "otf\<eta> (Var H \<degree>\<degree> map BVar xs, Abs t) =
    otf\<eta> (Var H \<degree>\<degree> map BVar (map Suc xs @ [0]), t)"
    by (simp add: comp_def)
  have "distinct (map Suc xs @ [0])" using Abs.prems by (auto simp: distinct_map)
  from Abs.IH[OF this] obtain xs' b where
    "otf\<eta> (Var H \<degree>\<degree> map BVar (map Suc xs @ [0]), t) =
      (Var H \<degree>\<degree> map BVar xs', snd (otf\<eta> (Var H \<degree>\<degree> map BVar (map Suc xs @ [0]), t)))"
    "distinct xs'" "t = Abs_m b (snd (otf\<eta> (Var H \<degree>\<degree> map BVar (map Suc xs @ [0]), t)))"
    by blast
  then show ?case
    by (intro exI[of _ xs'] exI[of _ "Suc b"]) (simp add: eq Abs_m)
next
  case (BVar x)
  then show ?case
    by (intro exI[of _ xs] exI[of _ 0]) (cases xs rule: rev_cases; simp)
next
  case (Var x)
  then show ?case
    by (intro exI[of _ xs] exI[of _ 0]) (cases xs rule: rev_cases; simp)
next
  case (App t1 t2)
  then show ?case
    by (intro exI[of _ xs] exI[of _ 0]) (cases xs rule: rev_cases; simp)
qed


subsubsection \<open>Analysis of \<open>cases\<close>\<close>

lemma cases_SomeE:
  assumes "cases k ((h1, as1), (h2, as2)) = Some (k', us', \<mu>)"
  obtains
    (rigid_rigid) p where "h1 = BVar p" "h2 = BVar p" "length as1 = length as2"
      "k' = k" "us' = map2 Problem as1 as2" "\<mu> = Var"
  | (flex_rigid) F xs p j where "h1 = Var F" "as1 = map BVar xs" "h2 = BVar p"
      "F \<notin> \<Union> (FV ` set as2)" "idx as1 (BVar p) = Some j" "k' = k + length as2"
      "us' = map2 (\<lambda>H s. Problem (H \<degree>\<degree> as1) s) (map Var [Suc k..<Suc k + length as2]) as2 @ [Marker]"
      "\<mu> = Var(F := Abs_m (length as1) (BVar j \<degree>\<degree>
          map (\<lambda>H. H \<degree>\<degree> map BVar (downs (length as1))) (map Var [Suc k..<Suc k + length as2])))"
  | (flex_flex1) F xs ys where "h1 = Var F" "h2 = Var F" "as1 = map BVar xs" "as2 = map BVar ys"
      "length xs = length ys" "k' = Suc k" "us' = []"
      "\<mu> = Var(F := Abs_m (length xs) (Var (Suc k) \<degree>\<degree> map BVar (ff1_args xs ys)))"
  | (flex_flex2) F G xs ys zs1 zs2 where "h1 = Var F" "h2 = Var G" "F \<noteq> G"
      "as1 = map BVar xs" "as2 = map BVar ys" "ff2_args xs ys = (zs1, zs2)" "k' = Suc k" "us' = []"
      "\<mu> = Var(F := Abs_m (length xs) (Var (Suc k) \<degree>\<degree> map BVar zs1),
               G := Abs_m (length ys) (Var (Suc k) \<degree>\<degree> map BVar zs2))"
  using assms
  by (cases h1; cases h2)
    (auto simp: Let_def all_is_BVar_iff split: if_splits option.splits prod.splits)

end
