section \<open>Preliminaries for the Unification Algorithm\<close>

theory Unif_Prelims
  imports Lemmas
begin

text \<open>
  This theory collects the notions needed to state and verify the unification
  algorithm of Grobauer's thesis (Chapter 2): free variables, composition of
  substitutions, \<open>\<beta>\<close>-normal forms, higher-order patterns, and some typing lemmas.
\<close>

subsection \<open>Free variables\<close>

fun FV :: "dB \<Rightarrow> nat set" where
  "FV (Var x) = {x}"
| "FV (t1 \<degree> t2) = FV t1 \<union> FV t2"
| "FV (Abs t) = FV t"
| "FV (BVar _) = {}"

lemma finite_FV[simp]: "finite (FV t)"
  by (induction t) auto

lemma FV_list_app[simp]: "FV (t \<degree>\<degree> ts) = FV t \<union> \<Union> (FV ` set ts)"
  by (induction ts arbitrary: t) auto

lemma FV_Abs_m[simp]: "FV (Abs_m m t) = FV t"
  by (induction m) auto

lemma FV_lift[simp]: "FV (lift t i) = FV t"
  by (induction t arbitrary: i) auto

lemma FV_subst_subset: "FV (t[s/i]) \<subseteq> FV t \<union> FV s"
proof (induction t arbitrary: s i)
  case (App t1 t2)
  have "FV (t1[s/i]) \<subseteq> FV t1 \<union> FV s" "FV (t2[s/i]) \<subseteq> FV t2 \<union> FV s"
    by (rule App.IH)+
  then show ?case by auto
next
  case (Abs t)
  then show ?case using Abs.IH[of "lift s 0" "Suc i"] by auto
qed (auto simp: subst_BVar)

lemma FV_subst_BVar[simp]: "FV (t[BVar x/i]) = FV t"
  by (induction t arbitrary: x i) (auto simp: subst_BVar)

lemma FV_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> FV t \<subseteq> FV s"
  by (induction rule: beta.induct) (use FV_subst_subset in auto)

lemma FV_beta_rtrancl: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> FV t \<subseteq> FV s"
  by (induction rule: rtranclp_induct) (auto dest: FV_beta)

lemma FV_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> FV t \<subseteq> FV s"
proof (induction rule: eta.induct)
  case (eta s dummy)
  then have "s[dummy/0] = s[BVar 0/0]" by (rule subst_not_free)
  then show ?case by simp
qed auto


subsection \<open>Substitutions\<close>

text \<open>
  Substitutions are functions from free variables to terms, applied with
  \<^const>\<open>mk_subst\<close>. Composition is the usual functional composition.
\<close>

definition subst_comp :: "(nat \<Rightarrow> dB) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> nat \<Rightarrow> dB" (infixl "\<circ>\<^sub>s" 55) where
  "\<sigma> \<circ>\<^sub>s \<rho> = (\<lambda>F. mk_subst \<sigma> (\<rho> F))"

lemma subst_comp_apply[simp]: "(\<sigma> \<circ>\<^sub>s \<rho>) F = mk_subst \<sigma> (\<rho> F)"
  by (simp add: subst_comp_def)

lemma mk_subst_comp[simp]: "mk_subst \<sigma> (mk_subst \<rho> t) = mk_subst (\<sigma> \<circ>\<^sub>s \<rho>) t"
  by (induction t) auto

lemma subst_comp_assoc: "(\<sigma> \<circ>\<^sub>s \<rho>) \<circ>\<^sub>s \<gamma> = \<sigma> \<circ>\<^sub>s (\<rho> \<circ>\<^sub>s \<gamma>)"
  by (simp add: subst_comp_def fun_eq_iff)

lemma mk_subst_Var_id[simp]: "mk_subst Var t = t"
  by (induction t) auto

lemma subst_comp_Var[simp]: "\<sigma> \<circ>\<^sub>s Var = \<sigma>" "Var \<circ>\<^sub>s \<sigma> = \<sigma>"
  by (simp_all add: subst_comp_def fun_eq_iff)

lemma mk_subst_cong: "(\<And>F. F \<in> FV t \<Longrightarrow> \<sigma> F = \<sigma>' F) \<Longrightarrow> mk_subst \<sigma> t = mk_subst \<sigma>' t"
  by (induction t) auto

lemma mk_subst_list_app[simp]: "mk_subst \<sigma> (t \<degree>\<degree> ts) = mk_subst \<sigma> t \<degree>\<degree> map (mk_subst \<sigma>) ts"
  by (induction ts arbitrary: t) auto

lemma mk_subst_Abs_m[simp]: "mk_subst \<sigma> (Abs_m m t) = Abs_m m (mk_subst \<sigma> t)"
  by (induction m) auto

lemma mk_subst_map_BVar[simp]: "map (mk_subst \<sigma>) (map BVar xs) = map BVar xs"
  by simp

lemma FV_mk_subst: "FV (mk_subst \<sigma> t) = \<Union> (FV ` \<sigma> ` FV t)"
  by (induction t) auto

lemma no_loose_bound_mono: "no_loose_bound t i \<Longrightarrow> i \<le> j \<Longrightarrow> no_loose_bound t j"
  by (induction t arbitrary: i j) auto

text \<open>A substitution is \<^emph>\<open>closed\<close> on a set of variables if it maps them to terms
  without loose bound variables.\<close>

definition closed_on :: "nat set \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "closed_on V \<sigma> \<longleftrightarrow> (\<forall>F\<in>V. no_loose_bound (\<sigma> F) 0)"

lemma closed_onD: "closed_on V \<sigma> \<Longrightarrow> F \<in> V \<Longrightarrow> no_loose_bound (\<sigma> F) 0"
  by (simp add: closed_on_def)

lemma closed_on_mono: "closed_on V \<sigma> \<Longrightarrow> W \<subseteq> V \<Longrightarrow> closed_on W \<sigma>"
  by (auto simp: closed_on_def)

lemma mk_subst_no_loose_bound:
  "no_loose_bound t i \<Longrightarrow> closed_on (FV t) \<sigma> \<Longrightarrow> no_loose_bound (mk_subst \<sigma> t) i"
  by (induction t arbitrary: i) (auto simp: closed_on_def intro: no_loose_bound_mono)

lemma closed_on_comp:
  "closed_on V \<rho> \<Longrightarrow> closed_on (\<Union> (FV ` \<rho> ` V)) \<sigma> \<Longrightarrow> closed_on V (\<sigma> \<circ>\<^sub>s \<rho>)"
  unfolding closed_on_def by (auto intro!: mk_subst_no_loose_bound simp: closed_on_def)

text \<open>The facts about substitutions from @{theory HOPAT_Base.Lemmas} assume closedness everywhere.
  We need versions that only assume closedness on the free variables of the terms involved.\<close>

lemma mk_subst_lift_on:
  "closed_on (FV t) \<sigma> \<Longrightarrow> mk_subst \<sigma> (lift t i) = lift (mk_subst \<sigma> t) i"
proof (induction t arbitrary: i)
  case (Var x)
  then have "no_loose_bound (\<sigma> x) 0" by (simp add: closed_on_def)
  then have "\<not> free (\<sigma> x) i" by (simp add: loose_bound_free)
  then show ?case
    by (metis lift.simps(4) lift_subst_dummy loose_bound_subst \<open>no_loose_bound (\<sigma> x) 0\<close>
      mk_subst.simps(1) zero_le)
qed (auto simp: closed_on_def)

lemma mk_subst_subst_on:
  "closed_on (FV t \<union> FV s) \<sigma> \<Longrightarrow> mk_subst \<sigma> (t[s/i]) = (mk_subst \<sigma> t)[mk_subst \<sigma> s/i]"
proof (induction t arbitrary: s i)
  case (BVar x)
  then show ?case by (simp add: subst_BVar)
next
  case (Var x)
  then have "no_loose_bound (\<sigma> x) 0" by (simp add: closed_on_def)
  then show ?case by (simp add: loose_bound_subst)
next
  case (App t1 t2)
  then have "closed_on (FV t1 \<union> FV s) \<sigma>" "closed_on (FV t2 \<union> FV s) \<sigma>"
    by (auto simp: closed_on_def)
  with App.IH show ?case by simp
next
  case (Abs t)
  have "closed_on (FV t \<union> FV (lift s 0)) \<sigma>" using Abs.prems by simp
  with Abs.IH[of "lift s 0" "Suc i"] show ?case
    using Abs.prems by (simp add: mk_subst_lift_on closed_on_def)
qed


subsection \<open>Equivalence modulo \<open>\<beta>\<eta>\<close>\<close>

lemma symcl_iff: "symcl r x y \<longleftrightarrow> r x y \<or> r y x"
  by simp

declare symcl.simps[simp del]

abbreviation equiv :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infix "\<equiv>\<^sub>\<beta>\<^sub>\<eta>" 50) where
  "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<equiv> closure \<beta>\<eta> s t"

lemma equiv_refl[simp, intro]: "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by simp

lemma equiv_sym: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
  by (rule closure_symmetric)

lemma equiv_trans[trans]: "r \<equiv>\<^sub>\<beta>\<^sub>\<eta> s \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> r \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by (rule rtranclp_trans)

lemma \<beta>\<eta>cl_into_equiv: "\<beta>\<eta>cl s t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl simp: symcl_iff)

lemma beta_into_\<beta>\<eta>cl: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> \<beta>\<eta>cl s t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_into_equiv: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by (rule \<beta>\<eta>cl_into_equiv[OF beta_into_\<beta>\<eta>cl])

lemma eta_into_equiv: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by (auto intro: \<beta>\<eta>cl_into_equiv)

lemma equiv_AppL: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> s' \<Longrightarrow> s \<degree> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> s' \<degree> t"
  by (rule closure_\<beta>\<eta>_App)

lemma equiv_AppR: "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> t' \<Longrightarrow> s \<degree> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> s \<degree> t'"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl simp: symcl_iff)

lemma equiv_App: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> s' \<Longrightarrow> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> t' \<Longrightarrow> s \<degree> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> s' \<degree> t'"
  using equiv_AppL equiv_AppR equiv_trans by blast

lemma equiv_Abs: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs t"
  using fact5 by blast

lemma equiv_Abs_m: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> Abs_m m s \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m t"
  by (induction m) (simp_all add: equiv_Abs)

lemma equiv_list_app:
  assumes "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> s'" "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) ts ts'"
  shows "s \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> s' \<degree>\<degree> ts'"
  using assms(2,1)
proof (induction ts ts' arbitrary: s s' rule: list_all2_induct)
  case (Cons t ts t' ts')
  show ?case using Cons.IH[OF equiv_App[OF Cons.prems Cons.hyps(1)]] by simp
qed simp

lemma mk_subst_equiv_cong:
  "(\<And>F. F \<in> FV t \<Longrightarrow> \<sigma> F \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma>' F) \<Longrightarrow> mk_subst \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' t"
  by (induction t) (simp_all add: equiv_App equiv_Abs)

lemma mk_subst_equiv:
  "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> mk_subst \<sigma> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> t"
  by (rule fact8_3) (simp_all add: closed_on_def)


subsection \<open>\<open>\<beta>\<close>-normal forms\<close>

abbreviation \<beta>_normal :: "dB \<Rightarrow> bool" where
  "\<beta>_normal t \<equiv> \<nexists>u. t \<rightarrow>\<^sub>\<beta> u"

lemma beta_normal_reduct_unique:
  assumes "t \<rightarrow>\<^sub>\<beta>\<^sup>* u" "t \<rightarrow>\<^sub>\<beta>\<^sup>* u'" "\<beta>_normal u" "\<beta>_normal u'"
  shows "u = u'"
proof -
  from beta_confluent assms(1,2) obtain v where "u \<rightarrow>\<^sub>\<beta>\<^sup>* v" "u' \<rightarrow>\<^sub>\<beta>\<^sup>* v"
    unfolding diamond_def commute_def square_def by blast
  with assms(3,4) show ?thesis
    by (metis converse_rtranclpE)
qed

text \<open>The \<open>\<beta>\<close>-normal form of a term, if it exists (we only use it for terms where it does).\<close>

definition \<beta>_nf :: "dB \<Rightarrow> dB" where
  "\<beta>_nf t = (if \<exists>u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> \<beta>_normal u then THE u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> \<beta>_normal u else t)"

lemma \<beta>_nf_eq: "t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<Longrightarrow> \<beta>_normal u \<Longrightarrow> \<beta>_nf t = u"
  unfolding \<beta>_nf_def using beta_normal_reduct_unique by auto

lemma \<beta>_nf_normal_id: "\<beta>_normal t \<Longrightarrow> \<beta>_nf t = t"
  by (rule \<beta>_nf_eq) simp_all

lemma \<beta>_nf_reduces: "t \<rightarrow>\<^sub>\<beta>\<^sup>* \<beta>_nf t"
proof (cases "\<exists>u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> \<beta>_normal u")
  case True
  then obtain u where "t \<rightarrow>\<^sub>\<beta>\<^sup>* u" "\<beta>_normal u" by blast
  then show ?thesis using \<beta>_nf_eq by simp
qed (simp add: \<beta>_nf_def)

lemma \<beta>_nf_equiv: "\<beta>_nf t \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by (rule equiv_sym[OF beta_into_equiv[OF \<beta>_nf_reduces]])

lemma \<beta>_nf_FV: "FV (\<beta>_nf t) \<subseteq> FV t"
  by (rule FV_beta_rtrancl[OF \<beta>_nf_reduces])

lemma \<beta>_nf_typing: "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> \<beta>_nf t : T"
  by (rule subject_reduction'[OF \<beta>_nf_reduces])


subsection \<open>Renaming of loose bound variables\<close>

lemma loose_BVars_list_app[simp]:
  "loose_BVars (t \<degree>\<degree> ts) = loose_BVars t \<union> \<Union> (loose_BVars ` set ts)"
  by (induction ts arbitrary: t) auto

lemma loose_BVars_map_BVar[simp]: "loose_BVars (Var F \<degree>\<degree> map BVar xs) = set xs"
  by simp

lemma map_BVars_list_app[simp]: "map_BVars f (t \<degree>\<degree> ts) = map_BVars f t \<degree>\<degree> map (map_BVars f) ts"
  by (induction ts arbitrary: t) auto

lemma map_BVars_map_BVar[simp]: "map (map_BVars f) (map BVar xs) = map BVar (map f xs)"
  by (induction xs) auto

lemma map_BVar_eq_iff[simp]: "map BVar xs = map BVar ys \<longleftrightarrow> xs = ys"
  by (simp add: inj_def)

lemma loose_BVars_map_BVars: "loose_BVars (map_BVars f t) = f ` loose_BVars t"
proof (induction t arbitrary: f)
  case (Abs t)
  have "Suc -` (case_nat 0 (\<lambda>a. Suc (f a)) ` L) = f ` (Suc -` L)" for L
    by (auto simp: image_iff split: nat.splits) (metis vimageI2)
  with Abs show ?case by simp
qed auto

lemma FV_map_BVars[simp]: "FV (map_BVars f t) = FV t"
  by (induction t arbitrary: f) auto

lemma size_map_BVars[simp]: "size (map_BVars f t) = size t"
  by (induction t arbitrary: f) auto

lemma subst_BVar_map_BVars:
  "t[BVar x/i] = map_BVars (\<lambda>j. if i < j then j - 1 else if j = i then x else j) t"
proof (induction t arbitrary: x i)
  case (Abs t)
  have "(\<lambda>j. if Suc i < j then j - 1 else if j = Suc i then Suc x else j) =
    case_nat 0 (\<lambda>a. Suc (if i < a then a - 1 else if a = i then x else a))"
    by (auto simp: fun_eq_iff split: nat.splits)
  with Abs show ?case by simp
qed (simp_all add: subst_BVar)

lemma size_subst_BVar[simp]: "size (t[BVar x/i]) = size t"
  by (simp add: subst_BVar_map_BVars)

lemma map_BVars_cong: "(\<And>j. j \<in> loose_BVars t \<Longrightarrow> f j = g j) \<Longrightarrow> map_BVars f t = map_BVars g t"
proof (induction t arbitrary: f g)
  case (App t1 t2)
  have "map_BVars f t1 = map_BVars g t1" "map_BVars f t2 = map_BVars g t2"
    by (rule App.IH; simp add: App.prems)+
  then show ?case by simp
next
  case (Abs t)
  have "map_BVars (case_nat 0 (\<lambda>a. Suc (f a))) t = map_BVars (case_nat 0 (\<lambda>a. Suc (g a))) t"
  proof (rule Abs.IH)
    fix j assume "j \<in> loose_BVars t"
    with Abs.prems show "case_nat 0 (\<lambda>a. Suc (f a)) j = case_nat 0 (\<lambda>a. Suc (g a)) j"
      by (cases j) auto
  qed
  then show ?case by simp
qed simp_all

lemma lift_map_BVars: "lift t i = map_BVars (\<lambda>j. if j < i then j else Suc j) t"
proof (induction t arbitrary: i)
  case (Abs t)
  have "(\<lambda>j. if j < Suc i then j else Suc j) = case_nat 0 (\<lambda>a. Suc (if a < i then a else Suc a))"
    by (auto simp: fun_eq_iff split: nat.splits)
  with Abs show ?case by simp
qed auto


subsection \<open>Higher-order patterns\<close>

text \<open>
  Following Grobauer (Section 1.1.5), a pattern is a term in \<open>\<beta>\<close>-normal form in which every
  free variable is applied to a list of distinct bound variables. Grobauer only requires the
  arguments to be \<open>\<eta>\<close>-equivalent to distinct bound variables but then assumes, for simplicity,
  that they are bound variables. We adopt this simplification. Since the head of any
  application is a variable, patterns are automatically in \<open>\<beta>\<close>-normal form.
\<close>

inductive pat :: "dB \<Rightarrow> bool" where
  pat_Abs: "pat t \<Longrightarrow> pat (Abs t)"
| pat_BVar: "(\<And>t. t \<in> set ts \<Longrightarrow> pat t) \<Longrightarrow> pat (BVar x \<degree>\<degree> ts)"
| pat_Var: "distinct xs \<Longrightarrow> pat (Var F \<degree>\<degree> map BVar xs)"

lemma pat_Abs_iff[simp]: "pat (Abs t) \<longleftrightarrow> pat t"
  by (auto elim: pat.cases intro: pat.intros)

lemma pat_Abs_m_iff[simp]: "pat (Abs_m m t) \<longleftrightarrow> pat t"
  by (induction m) auto

lemma pat_BVar_iff[simp]: "pat (BVar x \<degree>\<degree> ts) \<longleftrightarrow> (\<forall>t\<in>set ts. pat t)"
  by (auto elim: pat.cases intro: pat.intros)

lemma pat_BVar_iff'[simp]: "pat (BVar x) \<longleftrightarrow> True"
  using pat_BVar_iff[of x "[]"] by simp

lemma pat_Var_iff: "pat (Var F \<degree>\<degree> ts) \<longleftrightarrow> (\<exists>xs. ts = map BVar xs \<and> distinct xs)"
  by (auto elim: pat.cases intro: pat.intros)

lemma pat_Var_map_BVar_iff[simp]: "pat (Var F \<degree>\<degree> map BVar xs) \<longleftrightarrow> distinct xs"
  by (auto simp: pat_Var_iff)

lemma pat_Var_iff'[simp]: "pat (Var F) \<longleftrightarrow> True"
  using pat_Var_map_BVar_iff[of F "[]"] by simp

lemma pat_BVar_snoc[simp]: "pat ((BVar x \<degree>\<degree> ts) \<degree> u) \<longleftrightarrow> (\<forall>t\<in>set ts. pat t) \<and> pat u"
  using pat_BVar_iff[of x "ts @ [u]"] by auto

lemma pat_Var_snoc[simp]:
  "pat ((Var F \<degree>\<degree> map BVar xs) \<degree> u) \<longleftrightarrow> (\<exists>y. u = BVar y \<and> distinct xs \<and> y \<notin> set xs)"
  using pat_Var_iff[of F "map BVar xs @ [u]"] by (auto simp: append_eq_map_conv)

lemma not_pat_Abs_app: "ts \<noteq> [] \<Longrightarrow> \<not> pat (Abs u \<degree>\<degree> ts)"
  by (auto elim!: pat.cases)

lemma pat_cases[consumes 1, case_names Abs BVar Var]:
  assumes "pat t"
  obtains (Abs) u where "t = Abs u" "pat u"
  | (BVar) x ts where "t = BVar x \<degree>\<degree> ts" "\<forall>s\<in>set ts. pat s"
  | (Var) F xs where "t = Var F \<degree>\<degree> map BVar xs" "distinct xs"
  using assms by (cases rule: pat.cases) auto

lemma pat_beta_normal: "pat t \<Longrightarrow> \<beta>_normal t"
proof (induction rule: pat.induct)
  case (pat_BVar ts x)
  show ?case
  proof
    assume "\<exists>u. BVar x \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta> u"
    then obtain ss where "ts => ss" using head_BVar_reduction by blast
    then obtain us z z' vs where "ts = us @ z' # vs" "z' \<rightarrow>\<^sub>\<beta> z"
      unfolding step1_def by blast
    with pat_BVar.IH show False by auto
  qed
next
  case (pat_Var xs F)
  show ?case
  proof
    assume "\<exists>u. Var F \<degree>\<degree> map BVar xs \<rightarrow>\<^sub>\<beta> u"
    then obtain ss where "map BVar xs => ss" using head_Var_reduction by blast
    then obtain us z z' vs where "map BVar xs = us @ z' # vs" "z' \<rightarrow>\<^sub>\<beta> z"
      unfolding step1_def by blast
    then show False by (metis beta_cases(1) ex_map_conv in_set_conv_decomp)
  qed
qed blast

lemma pat_\<beta>_nf[simp]: "pat t \<Longrightarrow> \<beta>_nf t = t"
  by (simp add: \<beta>_nf_normal_id pat_beta_normal)

lemma pat_map_BVars: "pat t \<Longrightarrow> inj_on f (loose_BVars t) \<Longrightarrow> pat (map_BVars f t)"
proof (induction t arbitrary: f rule: pat.induct)
  case (pat_Abs t)
  let ?f = "case_nat 0 (\<lambda>a. Suc (f a))"
  have "inj_on ?f (loose_BVars t)"
  proof (rule inj_onI)
    fix a b assume "a \<in> loose_BVars t" "b \<in> loose_BVars t" "?f a = ?f b"
    with pat_Abs.prems show "a = b"
      by (cases a; cases b) (auto dest: inj_onD)
  qed
  with pat_Abs.IH show ?case by simp
next
  case (pat_BVar ts x)
  then have "inj_on f (loose_BVars s)" if "s \<in> set ts" for s
    using that by (auto intro: inj_on_subset)
  with pat_BVar.IH show ?case by auto
next
  case (pat_Var xs F)
  then show ?case by (simp del: map_map add: distinct_map)
qed

lemma pat_lift: "pat t \<Longrightarrow> pat (lift t i)"
  by (auto simp: lift_map_BVars intro!: pat_map_BVars inj_onI split: if_splits)



lemma apps_rtrancl_beta:
  assumes "list_all2 (\<lambda>t u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u) ts us" "h \<rightarrow>\<^sub>\<beta>\<^sup>* h'"
  shows "h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* h' \<degree>\<degree> us"
  using assms
proof (induction ts us arbitrary: h h' rule: list_all2_induct)
  case (Cons t ts u us)
  then show ?case by (simp add: rtrancl_beta_App)
qed simp

lemma mk_subst_comp_BVar[simp]: "mk_subst \<sigma> \<circ> BVar = BVar"
  by (simp add: fun_eq_iff)

subsection \<open>Applying a pattern to bound variables\<close>

text \<open>
  \<open>appb r xs\<close> is the \<open>\<beta>\<close>-normal form of \<open>r \<degree>\<degree> map BVar xs\<close> for a pattern \<open>r\<close>: the leading
  abstractions of \<open>r\<close> are consumed by the bound variables. Since only bound variables are
  substituted, no new redexes arise (cf.\ Grobauer, Lemmas 15, 18, 19).
\<close>

function appb :: "dB \<Rightarrow> nat list \<Rightarrow> dB" where
  "appb (Abs r) (x # xs) = appb (r[BVar x/0]) xs"
| "appb (Abs r) [] = Abs r"
| "appb (BVar y) xs = BVar y \<degree>\<degree> map BVar xs"
| "appb (Var F) xs = Var F \<degree>\<degree> map BVar xs"
| "appb (s \<degree> t) xs = (s \<degree> t) \<degree>\<degree> map BVar xs"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(r, xs). size r)") auto

lemma appb_Nil[simp]: "appb r [] = r"
  by (cases r) auto

lemma appb_not_Abs: "(\<And>u. r \<noteq> Abs u) \<Longrightarrow> appb r xs = r \<degree>\<degree> map BVar xs"
  by (cases r) auto

lemma appb_reduces: "r \<degree>\<degree> map BVar xs \<rightarrow>\<^sub>\<beta>\<^sup>* appb r xs"
proof (induction r xs rule: appb.induct)
  case (1 r x xs)
  have "Abs r \<degree>\<degree> map BVar (x # xs) \<rightarrow>\<^sub>\<beta> r[BVar x/0] \<degree>\<degree> map BVar xs"
    by simp
  with 1 show ?case by (simp only: appb.simps(1))
qed simp_all

lemma FV_appb[simp]: "FV (appb r xs) = FV r"
  by (induction r xs rule: appb.induct) auto

lemma appb_typing: "e \<turnstile> r \<degree>\<degree> map BVar xs : T \<Longrightarrow> e \<turnstile> appb r xs : T"
  by (rule subject_reduction'[OF appb_reduces])

lemma loose_BVars_subst_BVar0: "loose_BVars (r[BVar x/0]) \<subseteq> insert x (loose_BVars (Abs r))"
  by (auto simp: subst_BVar_map_BVars loose_BVars_map_BVars split: if_splits)

lemma pat_appb:
  assumes "pat r" "distinct xs" "set xs \<inter> loose_BVars r = {}"
  shows "pat (appb r xs)"
  using assms
proof (induction r xs rule: appb.induct)
  case (1 r x xs)
  let ?g = "\<lambda>j. if 0 < j then j - 1 else if j = 0 then x else j"
  have "inj_on ?g (loose_BVars r)"
  proof (rule inj_onI)
    fix a b assume ab: "a \<in> loose_BVars r" "b \<in> loose_BVars r" "?g a = ?g b"
    have "x \<notin> loose_BVars (Abs r)" using "1.prems"(3) by auto
    then have "c - 1 \<noteq> x" if "c \<in> loose_BVars r" "0 < c" for c
      using that by (auto intro!: vimageI2[of Suc] simp del: vimage_eq)
    with ab show "a = b" by (auto split: if_splits)
  qed
  then have "pat (r[BVar x/0])"
    using "1.prems"(1) by (simp add: subst_BVar_map_BVars pat_map_BVars)
  moreover have "set xs \<inter> loose_BVars (r[BVar x/0]) = {}"
    using "1.prems"(2,3) loose_BVars_subst_BVar0[of r x] by auto
  ultimately show ?case using "1.IH" "1.prems"(2) by simp
next
  case (5 s t xs)
  have "pat ((s \<degree> t) \<degree>\<degree> map BVar xs)"
    using \<open>pat (s \<degree> t)\<close>
  proof (cases rule: pat_cases)
    case (BVar y ts)
    with 5 show ?thesis by (auto simp flip: foldl_append)
  next
    case (Var F zs)
    with "5.prems"(3) have "set xs \<inter> set zs = {}" by auto
    with Var "5.prems"(2) have "pat (Var F \<degree>\<degree> map BVar (zs @ xs))"
      by (simp only: pat_Var_map_BVar_iff distinct_append) blast
    with Var show ?thesis by (metis foldl_append map_append)
  qed simp
  then show ?case by simp
qed (simp_all flip: foldl_append)


subsection \<open>Substituting patterns into patterns\<close>

text \<open>
  If a pattern \<open>t\<close> is instantiated with closed patterns, the \<open>\<beta>\<close>-normal form of the result is
  obtained by replacing every occurrence of \<open>F \<degree>\<degree> map BVar xs\<close> by \<open>appb (\<sigma> F) xs\<close>.
  This is the basis for Grobauer's Fact 3 and for the termination argument.
\<close>

definition pat_subst :: "nat set \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "pat_subst V \<sigma> \<longleftrightarrow> (\<forall>F\<in>V. pat (\<sigma> F) \<and> no_loose_bound (\<sigma> F) 0)"

lemma pat_substD: "pat_subst V \<sigma> \<Longrightarrow> F \<in> V \<Longrightarrow> pat (\<sigma> F)"
  "pat_subst V \<sigma> \<Longrightarrow> F \<in> V \<Longrightarrow> no_loose_bound (\<sigma> F) 0"
  by (simp_all add: pat_subst_def)

lemma pat_subst_mono: "pat_subst V \<sigma> \<Longrightarrow> W \<subseteq> V \<Longrightarrow> pat_subst W \<sigma>"
  by (auto simp: pat_subst_def)

lemma pat_subst_closed_on: "pat_subst V \<sigma> \<Longrightarrow> closed_on V \<sigma>"
  by (simp add: pat_subst_def closed_on_def)

lemma no_loose_bound_loose_BVars: "no_loose_bound t 0 \<Longrightarrow> loose_BVars t = {}"
  using no_loose_bound_BVars by fastforce

lemma pat_mk_subst_reduces:
  assumes "pat t" "pat_subst (FV t) \<sigma>"
  shows "mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* \<beta>_nf (mk_subst \<sigma> t) \<and> pat (\<beta>_nf (mk_subst \<sigma> t))"
proof -
  have "\<exists>u. mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> pat u"
    using assms
  proof (induction t rule: pat.induct)
    case (pat_Abs t)
    then obtain u where "mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* u" "pat u" by auto
    then show ?case by (auto intro!: exI[of _ "Abs u"])
  next
    case (pat_BVar ts x)
    have "\<exists>u. mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> pat u" if "t \<in> set ts" for t
      using pat_BVar.IH[OF that] pat_BVar.prems that by (auto intro: pat_subst_mono)
    then have "\<exists>us. list_all2 (\<lambda>t u. mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> pat u) ts us"
      by (induction ts) auto
    then obtain us where us: "list_all2 (\<lambda>t u. mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> pat u) ts us" ..
    then have "BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts \<rightarrow>\<^sub>\<beta>\<^sup>* BVar x \<degree>\<degree> us"
      by (auto intro!: apps_rtrancl_beta simp: list_all2_map1 elim: list_all2_mono)
    moreover have "pat (BVar x \<degree>\<degree> us)"
      using us by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
    ultimately show ?case by auto
  next
    case (pat_Var xs F)
    have "pat (\<sigma> F)" "no_loose_bound (\<sigma> F) 0"
      using pat_Var.prems by (simp_all add: pat_subst_def)
    then have "pat (appb (\<sigma> F) xs)"
      using pat_Var.hyps by (auto intro!: pat_appb dest: no_loose_bound_loose_BVars)
    then show ?case using appb_reduces[of "\<sigma> F" xs] by auto
  qed
  then obtain u where "mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* u" "pat u" by blast
  with pat_beta_normal show ?thesis by (simp add: \<beta>_nf_eq)
qed

lemma pat_mk_subst: "pat t \<Longrightarrow> pat_subst (FV t) \<sigma> \<Longrightarrow> pat (\<beta>_nf (mk_subst \<sigma> t))"
  using pat_mk_subst_reduces by blast

text \<open>The \<open>\<beta>\<close>-normal form of an instantiated pattern can be computed structurally.\<close>

lemma \<beta>_nf_mk_subst_Abs:
  "pat t \<Longrightarrow> pat_subst (FV t) \<sigma> \<Longrightarrow>
    \<beta>_nf (Abs (mk_subst \<sigma> t)) = Abs (\<beta>_nf (mk_subst \<sigma> t))"
  using pat_mk_subst_reduces[of t \<sigma>] by (auto intro!: \<beta>_nf_eq pat_beta_normal)

lemma \<beta>_nf_mk_subst_BVar:
  assumes "\<forall>t\<in>set ts. pat t" "pat_subst (\<Union> (FV ` set ts)) \<sigma>"
  shows "\<beta>_nf (BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts) = BVar x \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<sigma> t)) ts"
proof (rule \<beta>_nf_eq)
  have red: "mk_subst \<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* \<beta>_nf (mk_subst \<sigma> t)" "pat (\<beta>_nf (mk_subst \<sigma> t))"
    if "t \<in> set ts" for t
    using pat_mk_subst_reduces[of t \<sigma>] assms that by (auto intro: pat_subst_mono)
  have "BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts \<rightarrow>\<^sub>\<beta>\<^sup>* BVar x \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<sigma> t)) ts"
    using red(1) by (auto intro!: apps_rtrancl_beta simp: list_all2_map1 list_all2_map2 list_all2_same)
  then show "BVar x \<degree>\<degree> map (mk_subst \<sigma>) ts \<rightarrow>\<^sub>\<beta>\<^sup>* BVar x \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<sigma> t)) ts"
    by simp
  show "\<beta>_normal (BVar x \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<sigma> t)) ts)"
    by (rule pat_beta_normal) (use red(2) in auto)
qed

lemma \<beta>_nf_mk_subst_Var:
  "distinct xs \<Longrightarrow> pat_subst {F} \<sigma> \<Longrightarrow>
    \<beta>_nf (\<sigma> F \<degree>\<degree> map BVar xs) = appb (\<sigma> F) xs"
  by (auto intro!: \<beta>_nf_eq pat_beta_normal pat_appb appb_reduces
    simp: pat_subst_def dest: no_loose_bound_loose_BVars)



subsection \<open>Typing\<close>

lemma typing_bound_cong:
  "(e1, e2) \<turnstile> t : T \<Longrightarrow> no_loose_bound t n \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> e1 i = e1' i) \<Longrightarrow>
    (e1', e2) \<turnstile> t : T"
proof (induction e1 e2 t T arbitrary: n e1' rule: typing.induct[split_format(complete)])
  case (Abs env1 T env2 t U)
  have "(e1'\<langle>0:T\<rangle>, env2) \<turnstile> t : U"
  proof (rule Abs.IH)
    show "no_loose_bound t (Suc n)" using Abs.prems(1) by simp
    fix i assume "i < Suc n"
    with Abs.prems(2) show "(env1\<langle>0:T\<rangle>) i = (e1'\<langle>0:T\<rangle>) i"
      by (cases i) (auto simp: shift_def)
  qed
  then show ?case by auto
next
  case (App env s T U t)
  then show ?case by auto
qed auto

lemma typing_closed: "(e1, e2) \<turnstile> t : T \<Longrightarrow> no_loose_bound t 0 \<Longrightarrow> (e1', e2) \<turnstile> t : T"
  using typing_bound_cong[of e1 e2 t T 0 e1'] by auto

lemma typing_free_cong:
  "(e1, e2) \<turnstile> t : T \<Longrightarrow> (\<And>F. F \<in> FV t \<Longrightarrow> e2 F = e2' F) \<Longrightarrow> (e1, e2') \<turnstile> t : T"
proof (induction e1 e2 t T rule: typing.induct[split_format(complete)])
  case (App env1 env2 s T U t)
  then show ?case by auto
qed auto

text \<open>A substitution \<open>\<sigma>\<close> is well-typed on \<open>V\<close> if it maps every variable \<open>F \<in> V\<close> of type \<open>\<tau> F\<close>
  to a term of the same type (with free variables typed by \<open>\<tau>'\<close>), in any bound environment.\<close>

definition typed_on :: "nat set \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "typed_on V \<tau> \<tau>' \<sigma> \<longleftrightarrow> (\<forall>F\<in>V. \<forall>e. (e, \<tau>') \<turnstile> \<sigma> F : \<tau> F)"

lemma typed_onD: "typed_on V \<tau> \<tau>' \<sigma> \<Longrightarrow> F \<in> V \<Longrightarrow> (e, \<tau>') \<turnstile> \<sigma> F : \<tau> F"
  by (simp add: typed_on_def)

lemma typed_on_mono: "typed_on V \<tau> \<tau>' \<sigma> \<Longrightarrow> W \<subseteq> V \<Longrightarrow> typed_on W \<tau> \<tau>' \<sigma>"
  by (auto simp: typed_on_def)

lemma typed_onI_closed:
  "(\<And>F. F \<in> V \<Longrightarrow> no_loose_bound (\<sigma> F) 0 \<and> (\<exists>e. (e, \<tau>') \<turnstile> \<sigma> F : \<tau> F)) \<Longrightarrow> typed_on V \<tau> \<tau>' \<sigma>"
  unfolding typed_on_def by (metis typing_closed)

lemma typing_mk_subst:
  "(e1, \<tau>) \<turnstile> t : T \<Longrightarrow> typed_on (FV t) \<tau> \<tau>' \<sigma> \<Longrightarrow> (e1, \<tau>') \<turnstile> mk_subst \<sigma> t : T"
proof (induction e1 \<tau> t T rule: typing.induct[split_format(complete)])
  case (App env1 env2 s T U t)
  then show ?case by (auto intro: typed_on_mono)
qed (auto simp: typed_on_def)

lemma typed_on_comp:
  "typed_on V \<tau> \<tau>' \<rho> \<Longrightarrow> typed_on (\<Union> (FV ` \<rho> ` V)) \<tau>' \<tau>'' \<sigma> \<Longrightarrow> typed_on V \<tau> \<tau>'' (\<sigma> \<circ>\<^sub>s \<rho>)"
  unfolding typed_on_def
  by (auto intro!: typing_mk_subst simp: typed_on_def)

lemma typed_on_Var: "typed_on V \<tau> \<tau> Var"
  by (auto simp: typed_on_def)

lemma list_app_typing_iff: "e \<turnstile> t \<degree>\<degree> ts : T \<longleftrightarrow> (\<exists>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<and> e \<tturnstile> ts : Ts)"
  by (auto intro: list_app_typeI dest: list_app_typeD)


subsection \<open>Terms with an atomic head\<close>

definition is_atom :: "dB \<Rightarrow> bool" where
  "is_atom h \<longleftrightarrow> (\<exists>x. h = BVar x) \<or> (\<exists>F. h = Var F)"

lemma is_atom_simps[simp]: "is_atom (BVar x)" "is_atom (Var F)"
  "\<not> is_atom (Abs t)" "\<not> is_atom (s \<degree> t)"
  by (auto simp: is_atom_def)

lemma atom_apps_eq_iff:
  "is_atom h \<Longrightarrow> is_atom h' \<Longrightarrow> h \<degree>\<degree> as = h' \<degree>\<degree> bs \<longleftrightarrow> h = h' \<and> as = bs"
  by (auto simp: is_atom_def)

lemma atom_apps_beta: "is_atom h \<Longrightarrow> h \<degree>\<degree> as \<rightarrow>\<^sub>\<beta> u \<Longrightarrow> \<exists>bs. u = h \<degree>\<degree> bs \<and> step1 beta as bs"
  by (auto simp: is_atom_def dest: head_BVar_reduction head_Var_reduction)

lemma step1_snoc1: "step1 r xs ys \<Longrightarrow> step1 r (xs @ [a]) (ys @ [a])"
  unfolding step1_def by force

lemma step1_snoc2: "r a b \<Longrightarrow> step1 r (xs @ [a]) (xs @ [b])"
  unfolding step1_def by force

lemma atom_apps_eta: "is_atom h \<Longrightarrow> h \<degree>\<degree> as \<rightarrow>\<^sub>\<eta> u \<Longrightarrow> \<exists>bs. u = h \<degree>\<degree> bs \<and> step1 eta as bs"
proof (induction as arbitrary: u rule: rev_induct)
  case Nil
  then show ?case by (auto simp: is_atom_def)
next
  case (snoc a as)
  from snoc.prems(2) have "(h \<degree>\<degree> as) \<degree> a \<rightarrow>\<^sub>\<eta> u" by simp
  then show ?case
  proof (rule eta_cases(2))
    fix t assume "h \<degree>\<degree> as \<rightarrow>\<^sub>\<eta> t" "u = t \<degree> a"
    with snoc.IH[OF snoc.prems(1)] obtain bs where "t = h \<degree>\<degree> bs" "step1 eta as bs" by blast
    with \<open>u = t \<degree> a\<close> show ?thesis
      by (intro exI[of _ "bs @ [a]"]) (simp add: step1_snoc1)
  next
    fix t assume "a \<rightarrow>\<^sub>\<eta> t" "u = (h \<degree>\<degree> as) \<degree> t"
    then show ?thesis
      by (intro exI[of _ "as @ [t]"]) (simp add: step1_snoc2)
  qed
qed

lemma step1_list_all2_rtranclp:
  assumes "step1 r bs bs'" "\<And>x y. r x y \<Longrightarrow> R x y" "list_all2 R\<^sup>*\<^sup>* as bs"
  shows "list_all2 R\<^sup>*\<^sup>* as bs'"
proof -
  from assms(1) obtain us z z' vs where "bs' = us @ z # vs" "r z' z" "bs = us @ z' # vs"
    unfolding step1_def by blast
  with assms(3) obtain as1 a as2 where "as = as1 @ a # as2" "list_all2 R\<^sup>*\<^sup>* as1 us"
    "R\<^sup>*\<^sup>* a z'" "list_all2 R\<^sup>*\<^sup>* as2 vs"
    by (auto simp: list_all2_append2 list_all2_Cons2)
  with \<open>bs' = us @ z # vs\<close> \<open>r z' z\<close> assms(2) show ?thesis
    by (auto intro!: list_all2_appendI intro: rtranclp.rtrancl_into_rtrancl)
qed

lemma atom_apps_\<beta>\<eta>cl:
  assumes "is_atom h" "\<beta>\<eta>cl (h \<degree>\<degree> as) u"
  shows "\<exists>bs. u = h \<degree>\<degree> bs \<and> list_all2 \<beta>\<eta>cl as bs"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by (auto simp: list_all2_refl)
next
  case (step u u')
  then obtain bs where bs: "u = h \<degree>\<degree> bs" "list_all2 \<beta>\<eta>cl as bs" by blast
  from step.hyps(2) have "h \<degree>\<degree> bs \<rightarrow>\<^sub>\<beta> u' \<or> h \<degree>\<degree> bs \<rightarrow>\<^sub>\<eta> u'" by (simp add: bs(1))
  with assms(1) obtain bs' where "u' = h \<degree>\<degree> bs'"
    "step1 beta bs bs' \<or> step1 eta bs bs'"
    by (meson atom_apps_beta atom_apps_eta)
  moreover have "list_all2 \<beta>\<eta>cl as bs'"
    using calculation(2)
  proof
    assume "step1 beta bs bs'"
    then show ?thesis by (rule step1_list_all2_rtranclp) (simp_all add: bs(2))
  next
    assume "step1 eta bs bs'"
    then show ?thesis by (rule step1_list_all2_rtranclp) (simp_all add: bs(2))
  qed
  ultimately show ?case by blast
qed

lemma equiv_\<beta>\<eta>cl_normal: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> normal t \<Longrightarrow> \<beta>\<eta>cl s t"
  using closure_confluent by (metis converse_rtranclpE)

lemma atom_apps_equiv:
  assumes "is_atom h" "is_atom h'" "h \<degree>\<degree> as \<equiv>\<^sub>\<beta>\<^sub>\<eta> h' \<degree>\<degree> bs"
  shows "h = h' \<and> list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as bs"
proof -
  from closure_confluent[OF assms(3)] obtain c where
    "\<beta>\<eta>cl (h \<degree>\<degree> as) c" "\<beta>\<eta>cl (h' \<degree>\<degree> bs) c" by blast
  with assms(1,2) obtain as' bs' where
    "c = h \<degree>\<degree> as'" "list_all2 \<beta>\<eta>cl as as'" "c = h' \<degree>\<degree> bs'" "list_all2 \<beta>\<eta>cl bs bs'"
    by (blast dest: atom_apps_\<beta>\<eta>cl)
  with assms(1,2) have "h = h'" "as' = bs'" by (auto simp: atom_apps_eq_iff)
  with \<open>list_all2 \<beta>\<eta>cl as as'\<close> \<open>list_all2 \<beta>\<eta>cl bs bs'\<close> show ?thesis
    by (auto simp: list_all2_conv_all_nth) (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
qed

end
