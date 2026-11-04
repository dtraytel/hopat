section \<open>Patch 03: flex-flex pairs (completeness)\<close>

theory Unpatched_03_Unify_Flexflex
  imports Unpatched_Base
begin

text \<open>
  For \<open>\<lambda>j. ?F (\<lambda>z. z j) =?= \<lambda>j. ?G\<close>, \<open>clean_term\<close> deletes the argument of \<open>?F\<close>, which contains
  the banned bound variable \<open>j\<close> rigidly. The only unifier is \<open>?F := \<lambda>x. ?G\<close>; it does not cover
  \<open>?F := \<lambda>x. x (\<lambda>w. c)\<close>, \<open>?G := c\<close>, which the rest of the goal needs: the remaining subgoal
  \<open>?G = True \<and> ?G = False\<close> is unprovable. With the patch, the second unifier of \<open>rule refl\<close>
  lets the next steps succeed.
\<close>

lemma "\<exists>F G. (\<forall>j::bool. F (\<lambda>z. z j) = (G::bool)) \<and> F (\<lambda>z. True) = True \<and> F (\<lambda>z. False) = False"
  apply (rule exI, rule exI, rule conjI, rule allI)
  apply (fails \<open>rule refl, rule conjI, rule refl, rule refl\<close>)
  oops

lemma "\<exists>F G. (\<forall>j::bool. F (\<lambda>z. z j) = (G::bool)) \<and> F (\<lambda>z. True) = True \<and> F (\<lambda>z. False) = False"
  by (rule exI[where x = "\<lambda>x. x (\<lambda>w. True)"], rule exI[where x = True]) simp

end
