section \<open>Closed Environments\<close>

text \<open>
  Environments with closed bindings, the substitution that unfolds the bindings of an acyclic
  environment (\<open>usubst\<close>), and extensions of well-typed environments. The soundness of the
  unifiers uses them; the size measures are in theory \<open>Pattern_Size\<close>.
\<close>

theory Pattern_Closed_Env
  imports Pattern_Renaming Pattern_Acyclic
begin

subsection \<open>The arity of a type\<close>

context pure_sig_gen
begin

fun arity :: "ptyp \<Rightarrow> nat" where
  "arity (Type a [T, U]) = (if a = STR ''fun'' then Suc (arity U) else 0)"
| "arity _ = 0"

subsection \<open>Unfolding closed and well-typed bindings\<close>

definition closed_env :: "env \<Rightarrow> bool" where
  "closed_env env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> closed u)"

lemma wt_env_closed_env: "wt_env \<rho> env \<Longrightarrow> closed_env env"
  unfolding closed_env_def using wt_env_closed by blast

lemma loose_bvar_vsubst_on:
  "(\<And>x T. (x, T) \<in> vars t \<Longrightarrow> closed (\<sigma> x T)) \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar (vsubst \<sigma> t) k \<longleftrightarrow> loose_bvar t k"
proof (induction t arbitrary: k)
  case (Var x T)
  then show ?case using closed_loose_bvar by auto
next
  case (Abs a T t)
  then show ?case by (simp add: integer_arith)
qed auto

abbreviation usubst :: "env \<Rightarrow> vsubst" where
  "usubst env \<equiv> \<lambda>x T. case uval env x of Some v \<Rightarrow> v | None \<Rightarrow> Var x T"

lemma closed_usubst:
  assumes ac: "acyc env" and cl: "closed_env env"
  shows "closed_subst (usubst env)"
proof -
  have "closed (unf env u)" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using that
  proof (induction x arbitrary: U u rule: dep_induct[OF ac])
    case (1 x)
    have "closed (usubst env y T)" if "(y, T) \<in> vars u" for y T
    proof (cases "vt_lookup (tenv env) y")
      case (Some b)
      obtain U' u' where b: "b = (U', u')" by force
      have "(y, x) \<in> dep env" by (rule depI[OF "1.prems" that])
      from "1.IH"[OF this Some[unfolded b]] Some b show ?thesis by (simp add: uval_eq[OF ac])
    qed (simp add: uval_eq[OF ac] closed_def)
    moreover have "closed u" using cl "1.prems" unfolding closed_env_def by blast
    ultimately show ?case
      unfolding unf_def closed_def by (subst loose_bvar_vsubst_on) (simp_all add: closed_def)
  qed
  then show ?thesis
    by (auto simp: closed_subst_def uval_eq[OF ac] closed_def split: option.splits)
qed

lemma unf_subst:
  "acyc env \<Longrightarrow> closed_env env \<Longrightarrow> 0 \<le> k \<Longrightarrow> unf env (t[s/k]) = (unf env t)[unf env s/k]"
  unfolding unf_def using closed_usubst by simp

lemma inst_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> inst \<rho> s \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl beta_inst)

subsection \<open>Substitutions and extensions\<close>

lemma vsubst_vsubst: "vsubst \<sigma> (vsubst \<tau> t) = vsubst (\<lambda>x T. vsubst \<sigma> (\<tau> x T)) t"
  by (induction t) simp_all

lemma beta_reds_vsubst: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> closed_subst \<sigma> \<Longrightarrow> vsubst \<sigma> s \<rightarrow>\<^sub>\<beta>\<^sup>* vsubst \<sigma> t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl beta_vsubst)

text \<open>Environments and their extensions:\<close>

lemma wt_env_extends: "wt_env \<rho> env' \<Longrightarrow> extends env env' \<Longrightarrow> wt_env \<rho> env"
  unfolding wt_env_def extends_def by blast

lemma evars_extends: "extends env env' \<Longrightarrow> evars env \<subseteq> evars env'"
  unfolding evars_def bnds_def extends_def by blast

end

end
