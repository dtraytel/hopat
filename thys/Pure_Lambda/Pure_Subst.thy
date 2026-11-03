section \<open>Substitution of Schematic Variables\<close>

theory Pure_Subst
  imports Pure_Typing
begin

text \<open>
  A substitution for the schematic variables of Pure terms. As in Isabelle, a variable is
  identified by its name and its type. The values are closed terms, so substitution does not
  need to lift them under abstractions.
\<close>

type_synonym vsubst = "indexname \<Rightarrow> ptyp \<Rightarrow> pterm"

fun vsubst :: "vsubst \<Rightarrow> pterm \<Rightarrow> pterm" where
  "vsubst \<sigma> (Var x T) = \<sigma> x T"
| "vsubst \<sigma> (Abs a T t) = Abs a T (vsubst \<sigma> t)"
| "vsubst \<sigma> (s $ t) = vsubst \<sigma> s $ vsubst \<sigma> t"
| "vsubst \<sigma> t = t"

definition closed :: "pterm \<Rightarrow> bool" where
  "closed t \<longleftrightarrow> \<not> loose_bvar t 0"

definition closed_subst :: "vsubst \<Rightarrow> bool" where
  "closed_subst \<sigma> \<longleftrightarrow> (\<forall>x T. closed (\<sigma> x T))"

lemma closed_substD: "closed_subst \<sigma> \<Longrightarrow> closed (\<sigma> x T)"
  unfolding closed_subst_def by blast

lemma loose_bvar_mono: "loose_bvar t k' \<Longrightarrow> k \<le> k' \<Longrightarrow> loose_bvar t k"
  by (induction t k' arbitrary: k rule: loose_bvar.induct) (auto simp: integer_arith)

lemma closed_loose_bvar: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar t k"
  unfolding closed_def using loose_bvar_mono by blast

lemma closed_loose_bvar1: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar1 t k"
proof -
  have "loose_bvar1 t k \<Longrightarrow> loose_bvar t k" for t k
    by (induction t k rule: loose_bvar1.induct) auto
  then show "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar1 t k" using closed_loose_bvar by blast
qed

lemma incr_bv_no_loose: "\<not> loose_bvar t k \<Longrightarrow> incr_bv n k t = t"
  by (induction n k t rule: incr_bv.induct) auto

lemma subst_no_loose: "\<not> loose_bvar t k \<Longrightarrow> t[s/k] = t"
proof (induction t arbitrary: s k)
  case (Abs a T t)
  then show ?case using Abs.IH[of "k + 1"] by simp
qed (auto simp: subst_Bound)

lemma vsubst_lift [simp]:
  "closed_subst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> vsubst \<sigma> (incr_bv n k t) = incr_bv n k (vsubst \<sigma> t)"
  by (induction n k t rule: incr_bv.induct)
    (simp_all add: closed_substD closed_loose_bvar incr_bv_no_loose)

lemma vsubst_subst [simp]:
  "closed_subst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> vsubst \<sigma> (t[s/k]) = (vsubst \<sigma> t)[vsubst \<sigma> s/k]"
proof (induction t arbitrary: s k)
  case (Var x T)
  then show ?case by (simp add: closed_substD closed_loose_bvar subst_no_loose)
next
  case (Abs a T t)
  then show ?case using Abs.IH[of "k + 1" "lift s 0"] by simp
qed (auto simp: subst_Bound)

lemma loose_bvar1_vsubst [simp]:
  "closed_subst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar1 (vsubst \<sigma> t) k = loose_bvar1 t k"
proof (induction t arbitrary: k)
  case (Var x T)
  then show ?case by (simp add: closed_substD closed_loose_bvar1)
next
  case (Abs a T t)
  then show ?case using Abs.IH[of "k + 1"] by simp
qed auto

lemma beta_vsubst: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> closed_subst \<sigma> \<Longrightarrow> vsubst \<sigma> s \<rightarrow>\<^sub>\<beta> vsubst \<sigma> t"
  by (induction set: beta) auto

lemma eta_vsubst: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> closed_subst \<sigma> \<Longrightarrow> vsubst \<sigma> s \<rightarrow>\<^sub>\<eta> vsubst \<sigma> t"
proof (induction set: eta)
  case (eta s a T d)
  then show ?case using eta.eta[of "vsubst \<sigma> s" a T "vsubst \<sigma> d"] by simp
qed auto

lemma alpha_vsubst: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> vsubst \<sigma> s \<rightarrow>\<^sub>\<alpha> vsubst \<sigma> t"
  by (induction set: alpha) auto


context signature
begin

subsection \<open>Well-typed substitutions\<close>

text \<open>A closed term has its type in every environment of bound variables.\<close>

lemma typing_env_cong:
  "e \<turnstile> t : T \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> loose_bvar1 t i \<Longrightarrow> e' i = e i) \<Longrightarrow> e' \<turnstile> t : T"
proof (induction arbitrary: e' rule: typing.induct)
  case (Abs T e t U a)
  have "(e'\<langle>0:T\<rangle>) i = (e\<langle>0:T\<rangle>) i" if "0 \<le> i" "loose_bvar1 t i" for i
  proof (cases "i = 0")
    case False
    with that have "0 \<le> i - 1" "loose_bvar1 (Abs a T t) (i - 1)" by (simp_all add: integer_arith)
    with Abs.prems False that show ?thesis by (simp add: shift_def integer_arith)
  qed simp
  with Abs.IH have "e'\<langle>0:T\<rangle> \<turnstile> t : U" by blast
  with Abs.hyps(1) show ?case by blast
qed auto

lemma typing_closed: "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> e' \<turnstile> t : T"
  by (erule typing_env_cong) (simp add: closed_loose_bvar1)

text \<open>A substitution is well-typed if it maps variables of certified types to closed terms of
  their types (only certified types have closed terms).\<close>

definition wt_subst :: "vsubst \<Rightarrow> bool" where
  "wt_subst \<sigma> \<longleftrightarrow> closed_subst \<sigma> \<and> (\<forall>x T. ty_ok T \<longrightarrow> (\<exists>e. e \<turnstile> \<sigma> x T : T))"

lemma wt_subst_typing: "wt_subst \<sigma> \<Longrightarrow> ty_ok T \<Longrightarrow> e \<turnstile> \<sigma> x T : T"
  unfolding wt_subst_def closed_subst_def by (meson typing_closed)

lemma typing_vsubst: "e \<turnstile> t : T \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> e \<turnstile> vsubst \<sigma> t : T"
  by (induction rule: typing.induct) (auto intro: wt_subst_typing)

lemma conv_vsubst: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> vsubst \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> t"
proof -
  assume \<sigma>: "wt_subst \<sigma>"
  then have closed: "closed_subst \<sigma>" by (simp add: wt_subst_def)
  have step: "conv_step s t \<Longrightarrow> conv_step (vsubst \<sigma> s) (vsubst \<sigma> t)" for s t
    unfolding conv_step_def wt_def
    using alpha_vsubst beta_vsubst[OF _ closed] eta_vsubst[OF _ closed] typing_vsubst[OF _ \<sigma>]
    by meson
  show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> vsubst \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> t"
    unfolding conv_def by (induction rule: equivclp_induct) (auto intro: equivclp_into_equivclp step)
qed

end

end
