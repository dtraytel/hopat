section \<open>Patch 07: renaming and the lifting over the subgoal, a proof of \<open>False\<close> (soundness)\<close>

theory Unpatched_07_Thm_Rename_Lifting
  imports Main
begin

text \<open>
  \<^bold>\<open>Not checked here.\<close> The installed Isabelle already contains this patch, so this theory is not
  part of session \<open>Unpatched_Examples\<close>; with the patch, the proof of \<open>split_bad\<close> fails. The
  example is that of Kevin Kappelmann and Fabian Huch, ``Soundness-critical issues in thm.ML'',
  isabelle-users, 27 October 2026 (tested on Isabelle dev, hg 410b271f3ac4).

  To find the variables of a new premise of a lifted rule and to rename them,
  \<open>Thm.bicompose_aux\<close> strips the lifting off the premise (\<open>strip_lifted\<close>, \<open>strip_apply\<close>), but
  with the prefix of the rule's conclusion \<open>B\<close> rather than of the subgoal \<open>Bi\<close>. If \<open>B\<close> itself
  begins with \<open>\<And>w. A w \<Longrightarrow> \<dots>\<close>, a premise of the same shape loses its own parameter and assumption
  as well, and only the rest of it is renamed.

  The rule \<open>split_rule[unfolded X_def]\<close> keeps the conclusion \<open>\<And>w. True \<Longrightarrow> False\<close> (the definition
  hides it from the flattening of the statement). Resolution with \<open>?G (\<lambda>v. v)\<close> matches the bound
  variables \<open>w\<close> and \<open>v\<close>; the premise \<open>\<And>z. z = ?w \<Longrightarrow> z \<noteq> ?w\<close>, which no \<open>?w\<close> satisfies, becomes
  \<open>\<And>z. z = ?w \<Longrightarrow> z \<noteq> ?v\<close>, which \<open>split_aux\<close> proves.
\<close>

definition X :: "prop" where "X \<equiv> (\<And>w::bool. True \<Longrightarrow> False)"

lemma split_rule: "(\<And>z::bool. z = w \<Longrightarrow> z \<noteq> w) \<Longrightarrow> PROP X"
  unfolding X_def by auto

lemma split_aux: "z = True \<Longrightarrow> z \<noteq> False"
  by simp

schematic_goal split_bad: "PROP ?G (\<lambda>v::nat. v)"
  apply (rule split_rule[unfolded X_def])  \<comment> \<open>new subgoal \<open>\<And>z. z = ?w \<Longrightarrow> z \<noteq> ?v\<close>\<close>
  apply (rule split_aux)
  apply assumption
  done

lemma False
  by (rule split_bad) (rule TrueI)

end
