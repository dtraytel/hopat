section \<open>Patch 06: renaming and the flex-flex pairs of the rule, a proof of \<open>False\<close> (soundness)\<close>

theory Unpatched_06_Thm_Rename_Flexflex
  imports Unpatched_Base
begin

text \<open>
  \<^bold>\<open>Not checked.\<close> The installed Isabelle already contains this patch, so this theory is not
  part of session \<open>Unpatched_Examples\<close>; with the patch, the step marked below leaves an
  unprovable subgoal and the theory fails. The expected behaviour of Isabelle2026 is derived
  from its code.

  \<open>Thm.bicompose_aux\<close> renames a schematic variable \<open>?x\<close> of the new premises of a lifted rule to
  \<open>?y\<close> if a bound variable \<open>x\<close> of the rule's conclusion corresponds to a bound variable \<open>y\<close> of the
  subgoal (as \<open>exI\<close> on \<open>\<exists>y. Q y\<close> gives \<open>Q ?y\<close>). It must keep every variable that occurs
  elsewhere in the result, but it only checks the conclusion of the rule and the flex-flex pairs
  that the unifier returns, not the flex-flex pairs of the rule. A variable of the rule's
  flex-flex pairs that the unifier assigns is in neither, so it is renamed in the new premises
  and escapes its assignment.

  The rule \<open>R\<close> below is \<open>?x a \<Longrightarrow> app (\<lambda>x. x) (?z b)\<close> with the flex-flex pair \<open>?x a \<equiv> ?z b\<close>
  (from \<open>L\<close> by \<open>refl\<close>; neither side is a pattern, so the pair stays). Resolution with the subgoal
  \<open>app (\<lambda>y. y) False\<close>:
  \<^item> the conclusions give \<open>?z := \<lambda>w. False\<close>, the flex-flex pair then \<open>?x := \<lambda>w. False\<close>, and no
    flex-flex pairs remain;
  \<^item> \<open>?x\<close> is not in the conclusion of the rule and not among the remaining flex-flex pairs, so
    the premise \<open>?x a\<close> becomes \<open>?y a\<close>, which the assignment does not reach.

  The new subgoal \<open>?y a\<close> is proved by \<open>?y := \<lambda>w. True\<close>, which proves \<open>app (\<lambda>y. y) False\<close>, i.e.
  \<open>False\<close>. With the patch, \<open>?x\<close> is kept and the new subgoal is \<open>(\<lambda>w. False) a\<close>.
\<close>

typedecl i
axiomatization a b :: i

definition app :: "(bool \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool" where "app f v = f v"

lemma L: "x a = z b \<Longrightarrow> x a \<Longrightarrow> app (\<lambda>x. x) (z b)"
  by (simp add: app_def)

ML \<open>val R = @{thm refl} RS @{thm L}\<close>  \<comment> \<open>\<open>?x a \<Longrightarrow> app (\<lambda>x. x) (?z b)\<close> with the pair \<open>?x a \<equiv> ?z b\<close>\<close>

lemma bad: "app (\<lambda>y. y) False"
  apply (tactic \<open>resolve_tac \<^context> [R] 1\<close>)  \<comment> \<open>new subgoal \<open>?y a\<close>\<close>
  apply (rule TrueI)
  done

lemma False
  using bad by (simp add: app_def)

end
