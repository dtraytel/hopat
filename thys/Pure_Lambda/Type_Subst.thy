section \<open>Type Substitutions\<close>

theory Type_Subst
  imports "Pure_Pattern.Pure_Term"
begin

text \<open>
  A type instantiation maps schematic type variables, with their sorts, to types. It is shared by
  the typed \<open>\<lambda>\<close>-calculus (session Pure_Lambda) and type unification (session
  Pure_Pattern_Correctness).
\<close>

type_synonym tinst = "indexname \<Rightarrow> psort \<Rightarrow> ptyp"

fun tvars :: "ptyp \<Rightarrow> (indexname \<times> psort) set" where
  "tvars (Type _ Ts) = \<Union> (tvars ` set Ts)"
| "tvars (TFree _ _) = {}"
| "tvars (TVar v S) = {(v, S)}"

lemma finite_tvars[simp]: "finite (tvars T)"
  by (induction T) auto

fun tsubst :: "tinst \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "tsubst \<rho> (Type a Ts) = Type a (map (tsubst \<rho>) Ts)"
| "tsubst \<rho> (TFree a S) = TFree a S"
| "tsubst \<rho> (TVar v S) = \<rho> v S"

lemma tsubst_cong: "(\<And>v S. (v, S) \<in> tvars T \<Longrightarrow> \<rho> v S = \<rho>' v S) \<Longrightarrow> tsubst \<rho> T = tsubst \<rho>' T"
proof (induction T)
  case (Type a Ts)
  have "tsubst \<rho> T = tsubst \<rho>' T" if "T \<in> set Ts" for T
    by (rule Type.IH[OF that], rule Type.prems) (use that in auto)
  then show ?case by simp
qed auto

lemma tsubst_tsubst: "tsubst \<rho> (tsubst \<rho>' T) = tsubst (\<lambda>v S. tsubst \<rho> (\<rho>' v S)) T"
  by (induction T) auto

lemma tsubst_TVar[simp]: "tsubst TVar T = T"
  by (induction T) (auto simp: map_idI)

lemma tvars_tsubst: "tvars (tsubst \<rho> T) = (\<Union>(v, S)\<in>tvars T. tvars (\<rho> v S))"
  by (induction T) auto

end
