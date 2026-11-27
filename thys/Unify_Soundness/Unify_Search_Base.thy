section \<open>Variables of Pairs in the Invariant\<close>

text \<open>
  The variables of pairs in the invariant, the type variables of the terms that \<open>MATCH\<close>
  builds, and the hypothesis of \<open>MATCH\<close> for flex-rigid pairs in the invariant.
\<close>

theory Unify_Search_Base
  imports Unify_Match_Base Unify_Flexflex_Base Unify_Shape
begin

subsection \<open>Variables of the pairs\<close>

context pure_sig_gen
begin

lemma sinv_dvars: "sinv A K X env dps \<Longrightarrow> dvars dps \<subseteq> X \<union> evars env"
  unfolding sinv_def dvars_def by (fastforce dest: upokD(1,2))

lemma ttvars_combound: "ttvars (combound t m k) = ttvars t"
  by (simp add: combound_apps ttvars_apps)

declare ttvars_types_abs [simp]

lemma finite_dvars [simp]: "finite (dvars dps)"
  by (auto simp: dvars_def)

end

context pure_sig_gen
begin

text \<open>
  The hypothesis of \<^const>\<open>MATCH\<close> holds for flex-rigid pairs in the invariant: the types of the
  two sides are equal modulo the type environment.
\<close>

lemma sinv_MATCH_ok:
  assumes sh: "frs_shape (rb, t, u)" and si: "sinv A K X env ((rb, t, u) # dps)"
  shows "MATCH_ok env (rb, t, u)"
proof -
  have ei: "einv A K env" and p: "upok A env rb X t u" using si by (auto simp: sinv_def)
  note e = einvD[OF ei]
  from fastype_pair_term[OF ei p] obtain T1 U1 where
    ty: "fastype env rb t = return T1" "fastype env rb u = return U1"
      "tvars T1 \<subseteq> tvars_env (tyenv env) \<union> A" "tvars U1 \<subseteq> tvars_env (tyenv env) \<union> A"
      "tnorm (tyenv env) T1 = tnorm (tyenv env) U1"
    by blast
  have "tspine (tyenv env) T1 U1"
    by (rule tspine_tnorm[OF e(6,7) tinv_tcons[OF e(2) ty(3)] tinv_tcons[OF e(2) ty(4)] ty(5)])
  with ty(1,2) show ?thesis by (intro frs_shape_MATCH_ok[OF sh]) (simp_all add: return_def)
qed

end

end
