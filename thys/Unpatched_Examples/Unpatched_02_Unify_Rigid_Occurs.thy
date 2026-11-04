section \<open>Patch 02: the rigid occurs check of \<open>Unify\<close> (completeness)\<close>

theory Unpatched_02_Unify_Rigid_Occurs
  imports Unpatched_Base
begin

text \<open>
  \<open>rigid_occurs_term\<close> rejects \<open>?v := \<lambda>y. y (?v (\<lambda>z. d))\<close> because \<open>?v\<close> occurs on a rigid path,
  although its argument lets an instance discard the occurrence: \<open>?v := \<lambda>y. y d\<close> is a unifier.
\<close>

lemma "\<exists>v. \<forall>y. v y = y (v (\<lambda>z::'b. d::'b))"
  apply (rule exI, rule allI)
  apply (fails \<open>rule refl\<close>)
  oops

lemma "\<exists>v. \<forall>y. v y = y (v (\<lambda>z::'b. d::'b))"
  by (rule exI[where x = "\<lambda>y. y d"]) simp

end
