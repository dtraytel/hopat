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

lemma env_ppatD: "env_ppat env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ppat u"
  unfolding env_ppat_def by blast

lemma ppat_atom: "rigid h \<Longrightarrow> ppat h"
  using ppat_rigid[of h "[]"] by simp

lemma apps_eq_Abs: "h \<degree>\<degree> ts = Abs a T t \<longleftrightarrow> ts = [] \<and> h = Abs a T t"
  by (cases ts rule: rev_cases) (simp_all add: app_last[symmetric])

lemma ppat_AbsD: "ppat (Abs a T t) \<Longrightarrow> ppat t"
  by (cases rule: ppat.cases) (auto simp: app_apps apps_eq_Abs)

end
