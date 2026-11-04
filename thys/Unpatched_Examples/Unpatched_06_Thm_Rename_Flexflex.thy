section \<open>Patch 06: renaming and the flex-flex pairs of the rule, proofs of \<open>False\<close> (soundness)\<close>

theory Unpatched_06_Thm_Rename_Flexflex
  imports Main
begin

text \<open>
  \<^bold>\<open>Not checked here.\<close> The installed Isabelle already contains this patch, so this theory is not
  part of session \<open>Unpatched_Examples\<close>; with the patch, the final steps fail. The examples are
  those of Kevin Kappelmann and Fabian Huch, ``Soundness-critical issues in thm.ML'',
  isabelle-users, 27 October 2026 (tested on Isabelle dev, hg 410b271f3ac4).

  \<open>Thm.bicompose_aux\<close> renames a schematic variable \<open>?x\<close> of the new premises of a lifted rule to
  \<open>?y\<close> if a bound variable \<open>x\<close> of the rule's conclusion corresponds to a bound variable \<open>y\<close> of the
  subgoal. It must keep every variable that occurs elsewhere in the result, but it only checks
  the conclusion of the rule and the flex-flex pairs that the unifier returns, not those of the
  rule. A variable of the rule's flex-flex pairs that the unifier assigns is in neither, so it is
  renamed in the new premises and escapes its assignment.

  \<open>flex_rule1[THEN flex_rule2]\<close> is \<open>?x True \<Longrightarrow> \<forall>x. ?P True\<close> with the flex-flex pair
  \<open>?x True \<equiv> ?P True\<close>. Resolution with \<open>\<forall>y. False\<close> assigns \<open>?P\<close> and then \<open>?x\<close>, and renames \<open>?x\<close>
  to \<open>?y\<close> in the premise: the new subgoal is \<open>?y True\<close> instead of \<open>False\<close>. The same happens in
  elim-resolution.
\<close>

lemma flex_rule1: "x True \<Longrightarrow> x True" .

lemma flex_rule2: "P True \<Longrightarrow> \<forall>x::bool. P True"
  by simp

subsection \<open>Resolution\<close>

lemma "\<forall>y::bool. False"
  apply (rule flex_rule1[THEN flex_rule2])  \<comment> \<open>new subgoal \<open>?y True\<close>, should be \<open>False\<close>\<close>
  by (rule TrueI)

subsection \<open>Elim-resolution\<close>

lemma eres_rule: "P True \<Longrightarrow> (\<forall>x::bool. \<not> P True) \<Longrightarrow> False"
  by simp

lemma "\<forall>y::bool. \<not> False \<Longrightarrow> False"
  apply (erule flex_rule1[THEN eres_rule, rotated])  \<comment> \<open>new subgoal \<open>?y True\<close>\<close>
  by (rule TrueI)

end
