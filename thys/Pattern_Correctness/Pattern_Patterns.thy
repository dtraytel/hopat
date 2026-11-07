section \<open>\<open>\<beta>\<close>-Normal Patterns\<close>

theory Pattern_Patterns
  imports Pattern_Vars
begin

text \<open>
  \<open>\<beta>\<close>-normal higher-order patterns: below abstractions, a rigid head applied to patterns, or a
  schematic variable applied to distinct bound variables. An environment of patterns binds
  patterns only.
\<close>

inductive ppat :: "pterm \<Rightarrow> bool" where
  ppat_Abs: "ppat t \<Longrightarrow> ppat (Abs a T t)"
| ppat_rigid: "rigid h \<Longrightarrow> \<forall>t\<in>set ts. ppat t \<Longrightarrow> ppat (h \<degree>\<degree> ts)"
| ppat_flex: "distinct is \<Longrightarrow> ppat (app (Var x T) is)"

definition env_ppat :: "env \<Rightarrow> bool" where
  "env_ppat env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> ppat u)"

lemma ppat_atom: "rigid h \<Longrightarrow> ppat h"
  using ppat_rigid[of h "[]"] by simp

lemma apps_eq_Abs: "h \<degree>\<degree> ts = Abs a T t \<longleftrightarrow> ts = [] \<and> h = Abs a T t"
  by (cases ts rule: rev_cases) (simp_all add: app_last[symmetric])

lemma ppat_AbsD: "ppat (Abs a T t) \<Longrightarrow> ppat t"
  by (cases rule: ppat.cases) (auto simp: app_apps apps_eq_Abs)

lemma ppat_nonAbsE:
  assumes "ppat t" "\<not> is_Abs t"
  obtains (rigid) h ts where "rigid h" "t = h \<degree>\<degree> ts" "\<forall>u\<in>set ts. ppat u"
  | (flex) x T "is" where "t = app (Var x T) is" "distinct is"
  using assms by (cases rule: ppat.cases) auto

lemma ppat_AppE:
  assumes "ppat (f $ u)"
  obtains (rigid) h ts where "rigid h" "f $ u = h \<degree>\<degree> ts" "\<forall>u\<in>set ts. ppat u"
  | (flex) x T iss i where "f = app (Var x T) iss" "u = Bound i" "distinct (iss @ [i])"
  using assms
proof (cases rule: ppat.cases)
  case (ppat_flex "is" x T)
  then obtain iss i where "is = iss @ [i]" by (cases "is" rule: rev_cases) (auto simp: app_apps)
  with ppat_flex show ?thesis using that(2) by (auto simp: app_apps)
qed (use that(1) in auto)

lemma ppat_abs_list: "ppat t \<Longrightarrow> ppat (abs_list bs t)"
proof (induction bs)
  case (Cons b bs)
  then show ?case by (cases b) (auto intro: ppat_Abs)
qed simp

lemma ppat_lift: "ppat t \<Longrightarrow> ppat (lift t d)"
proof (induction arbitrary: d rule: ppat.induct)
  case (ppat_Abs t a T)
  then show ?case by (auto intro: ppat.ppat_Abs)
next
  case (ppat_rigid h ts)
  have "rigid (lift h d)" using ppat_rigid.hyps(1) by (cases h) auto
  with ppat_rigid show ?case by (auto simp: incr_bv_apps intro!: ppat.ppat_rigid)
next
  case (ppat_flex "is" x T)
  have "inj_on (\<lambda>i. if d \<le> i then i + 1 else i) (set is)" by (auto simp: inj_on_def split: if_splits)
  with ppat_flex show ?case by (auto simp: lift_app distinct_map intro!: ppat.ppat_flex)
qed

lemma ppat_lift_Bound0:
  assumes "ppat t" "\<not> is_Abs t"
  shows "ppat (lift t 0 $ Bound 0)"
  using assms
proof (cases rule: ppat_nonAbsE)
  case (rigid h ts)
  have "rigid (lift h 0)" using rigid(1) by (cases h) auto
  then have "ppat (lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0]))"
    using rigid(3) ppat_lift ppat_atom[of "Bound 0"] by (intro ppat.ppat_rigid) auto
  moreover have "lift t 0 $ Bound 0 = lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0])"
    by (simp add: rigid(2) incr_bv_apps)
  ultimately show ?thesis by simp
next
  case (flex x T "is")
  let ?g = "\<lambda>i::integer. if 0 \<le> i then i + 1 else i"
  have "inj_on ?g (set is)" by (auto simp: inj_on_def split: if_splits)
  moreover have "0 \<notin> ?g ` set is" by auto
  ultimately have "distinct (map ?g is @ [0])" using flex(2) by (auto simp: distinct_map)
  then have "ppat (app (Var x T) (map ?g is @ [0]))" by (rule ppat_flex)
  moreover have "lift t 0 $ Bound 0 = app (Var x T) (map ?g is @ [0])"
    by (simp only: flex(1) lift_app) (simp add: app_def)
  ultimately show ?thesis by simp
qed

lemma ppat_subst:
  "ppat t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> 0 \<le> y \<Longrightarrow> \<not> loose_bvar1 t (y + lev + 1) \<Longrightarrow> ppat (t[Bound (y + lev)/lev])"
proof (induction arbitrary: lev rule: ppat.induct)
  case (ppat_Abs t a T)
  have "ppat (t[Bound (y + (lev + 1))/lev + 1])"
    using ppat_Abs.prems by (intro ppat_Abs.IH) (simp_all add: algebra_simps)
  with ppat_Abs.prems show ?case by (auto simp: algebra_simps intro: ppat.ppat_Abs)
next
  case (ppat_rigid h ts)
  have "rigid (h[Bound (y + lev)/lev])" using ppat_rigid.hyps(1) by (cases h) (auto simp: subst_Bound)
  moreover have "ppat (t[Bound (y + lev)/lev])" if "t \<in> set ts" for t
    using ppat_rigid.IH that ppat_rigid.prems by (auto simp: loose_bvar1_apps)
  ultimately show ?case by (auto simp: subst_apps intro!: ppat.ppat_rigid)
next
  case (ppat_flex "is" x T)
  let ?g = "\<lambda>i. if lev < i then i - 1 else if i = lev then y + lev else i"
  have nin: "y + lev + 1 \<notin> set is" using ppat_flex.prems(3) by (simp add: loose_bvar1_app)
  have "inj_on ?g (set is)"
  proof (rule inj_onI)
    fix i j assume "i \<in> set is" "j \<in> set is" "?g i = ?g j"
    moreover have "\<forall>k\<in>set is. k \<noteq> y + lev + 1" using nin by blast
    ultimately show "i = j" using ppat_flex.prems(1,2) by (auto split: if_splits simp: integer_arith)
  qed
  with ppat_flex.hyps have "ppat (app (Var x T) (map ?g is))" by (intro ppat.ppat_flex) (simp add: distinct_map)
  then show ?case by (simp add: subst_app)
qed


end
