section \<open>Patch 01: the occurs check of \<open>Pattern.unify\<close> (completeness)\<close>

theory Unpatched_01_Pattern_Rigid_Occurs
  imports Unpatched_Base
begin

text \<open>
  \<open>Pattern.unify\<close> raises \<open>Unif\<close> for \<open>?p =?= \<not> ?f ?p\<close> because \<open>?p\<close> occurs in the rigid side,
  although only under the flexible head \<open>?f\<close>. \<open>Unify.unifiers\<close> takes this as ``no unifier'',
  but \<open>?p := \<not> False\<close>, \<open>?f := \<lambda>_. False\<close> is one.
\<close>

lemma "\<exists>p f. p = (\<not> f p)"
  apply (intro exI)
  apply (fails \<open>rule refl\<close>)
  oops

lemma "\<exists>p f. p = (\<not> f p)"
  by (intro exI[where x = "\<not> False"] exI[where x = "\<lambda>_. False"]) simp

end
