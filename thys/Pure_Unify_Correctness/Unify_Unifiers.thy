section \<open>Correctness of \<open>unifiers\<close>\<close>

theory Unify_Unifiers
  imports Unify_Flexflex_Complete Unify_Dfs Unify_Occurs Unify_Pull
begin

context csig
begin

text \<open>
  \<^const>\<open>unifiers\<close> first tries pattern unification (\<^const>\<open>Pure_Pattern.unify\<close>) on the pairs in
  turn, and falls back to \<^const>\<open>hounifiers\<close> if a term is not a pattern. On well-typed problems
  with ground types and an acyclic environment, pattern unification is proved terminating,
  sound and complete in session \<open>Pure_Pattern_Correctness\<close> (in the setting of empty type
  environments used here, @{thm [source] unif_term}, @{thm [source] unify_sound_Ok} and
  @{thm [source] unif_complete}), and raises only \<open>Pattern\<close> and \<open>Unif\<close>
  (@{thm [source] unif_exn}). Hence \<^const>\<open>unifiers\<close> is sound and complete as
  \<^const>\<open>hounifiers\<close>.
\<close>

subsection \<open>Well-typed problems\<close>

text \<open>The invariant \<^const>\<open>cinv\<close> without a solution:\<close>

definition tyinv :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "tyinv ar V env dps \<longleftrightarrow> env_inv ar V env \<and>
    (\<forall>dp\<in>set dps. wf_dp ar dp \<and> dp_typed V dp \<and> dp_below (maxidx env) dp)"

lemma tyinvD:
  assumes "tyinv ar V env dps"
  shows "env_inv ar V env" "dp \<in> set dps \<Longrightarrow> wf_dp ar dp \<and> dp_typed V dp \<and> dp_below (maxidx env) dp"
  using assms by (simp_all add: tyinv_def)

lemma tyinv_transfer:
  assumes "env_inv ar V' env'" "\<forall>dp\<in>set dps. wf_dp ar dp \<and> dp_typed V dp \<and> dp_below m dp"
    "agreeV m V V'" "m \<le> maxidx env'"
  shows "tyinv ar V' env' dps"
proof -
  have "wf_dp ar dp \<and> dp_typed V' dp \<and> dp_below (maxidx env') dp" if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb a b where dp': "dp = (rb, a, b)" by (cases dp)
    have h: "wf_dp ar dp \<and> dp_typed V dp \<and> dp_below m dp" using assms(2) dp by blast
    then obtain U where "wf_dp ar dp" "has_type V (map snd rb) a U" "has_type V (map snd rb) b U"
      "below m a" "below m b" using dp' by auto
    with assms(3,4) dp' show ?thesis by (auto intro: has_type_agreeV below_mono)
  qed
  with assms(1) show ?thesis by (simp add: tyinv_def)
qed

abbreviation dps_of :: "(pterm \<times> pterm) list \<Rightarrow> dpair list" where
  "dps_of tus \<equiv> map (\<lambda>(t, u). ([], t, u)) tus"

lemma dsolved_Nil: "dsolved \<sigma> ([], t, u) \<longleftrightarrow> unifies \<sigma> (tr t) (tr u)"
  by (simp add: dsolved_def unifies_def)


subsection \<open>The results of \<^const>\<open>unifiers\<close>\<close>

lemma pull_Empty: "pull cfg S_Empty = returnW None"
  by (subst pull.simps) simp

lemma pull_Single: "pull cfg (S_Single x) = returnW (Some (x, S_Empty))"
  by (subst pull.simps) simp

lemma evals_Empty: "evals cfg S_Empty xs \<Longrightarrow> xs = []"
  by (auto elim: evals.cases simp: pull_Empty returnW_def)

lemma evals_Single: "evals cfg (S_Single x) xs \<Longrightarrow> xs = [x]"
  by (erule evals.cases) (auto simp: pull_Single returnW_def dest: evals_Empty)

end

end
