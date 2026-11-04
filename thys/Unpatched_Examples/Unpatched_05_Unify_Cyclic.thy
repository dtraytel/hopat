section \<open>Patch 05: cyclic environments, a proof of \<open>False\<close> (soundness)\<close>

theory Unpatched_05_Unify_Cyclic
  imports Unpatched_Base
begin

text \<open>
  \<open>MATCH\<close> copies the rigid side of a flex-rigid pair \<open>?v =?= \<lambda>x. x (\<not> ?F ?v)\<close> into \<open>?v\<close>. The
  projection on \<open>x\<close> assigns its new variable \<open>?G := \<lambda>x. \<not> ?F ?v\<close> before \<open>?v\<close> is updated to
  \<open>\<lambda>x. x (?G x)\<close>, which closes a cycle in the environment. The cyclic environment is not a
  solution: it only stands for one if \<open>?F\<close> discards its argument, but \<open>?F\<close> stays open. Since
  neither \<open>?v\<close> nor \<open>?G\<close> occurs in the remaining proof state, normalization terminates, and a
  later step can instantiate \<open>?F\<close> such that the equation has no solution.

  The first component \<open>?G True =?= False\<close> is not a pattern, so that \<open>Unify.unifiers\<close> uses
  Huet's procedure instead of \<open>Pattern.unify\<close>, whose occurs check would reject the problem.
\<close>

lemma False_aux: "(G True, \<lambda>x::bool \<Rightarrow> bool. x (\<not> F v)) = (False, v) \<Longrightarrow> F = (\<lambda>w. w id) \<Longrightarrow> False"
  by (metis (no_types) id_apply prod.inject)

lemma bad: False
  apply (rule False_aux)
   apply (rule refl)  \<comment> \<open>the cyclic ``unifier'' of \<open>?v = \<lambda>x. x (\<not> ?F ?v)\<close>\<close>
  apply (rule refl)  \<comment> \<open>\<open>?F := \<lambda>w. w id\<close>\<close>
  done

end
