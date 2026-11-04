section \<open>Patch 07: renaming and the lifting over the subgoal, a proof of \<open>False\<close> (soundness)\<close>

theory Unpatched_07_Thm_Rename_Lifting
  imports Unpatched_Base
begin

text \<open>
  \<^bold>\<open>Not checked.\<close> The installed Isabelle already contains this patch, so this theory is not
  part of session \<open>Unpatched_Examples\<close>; with the patch, the step marked below leaves an
  unprovable subgoal and the theory fails. The expected behaviour of Isabelle2026 is derived
  from its code.

  \<open>Thm.bicompose_aux\<close> renames a schematic variable \<open>?x\<close> of the new premises of a lifted rule to
  \<open>?y\<close> if a bound variable \<open>x\<close> of the rule's conclusion corresponds to a bound variable \<open>y\<close> of the
  subgoal. To find the variables of a premise and to rename them, it strips the lifting off the
  premise (\<open>strip_lifted\<close>, \<open>strip_apply\<close>), but with the prefix of the rule's conclusion \<open>B\<close>
  rather than of the subgoal \<open>Bi\<close>. If \<open>B\<close> itself begins with \<open>\<And>x. A x \<Longrightarrow> \<dots>\<close>, a premise of the same
  shape loses its own parameter and assumption as well: their variables are not looked at,
  and only the rest of the premise is renamed.

  The rule \<open>R\<close> has the premise \<open>\<And>z. z = ?x \<Longrightarrow> z \<noteq> ?x\<close>, which no \<open>?x\<close> satisfies, and the
  conclusion \<open>\<And>x::unit. True \<Longrightarrow> False\<close>. Resolution with the subgoal \<open>?Q (\<lambda>y. ?R y)\<close> (no lifting)
  matches the bound variables \<open>x\<close> and \<open>y\<close>, and \<open>?x\<close> does not occur in the conclusion. The
  premise is stripped like the conclusion, by \<open>\<And>z\<close> and \<open>z = ?x\<close>, and only \<open>z \<noteq> ?x\<close> is renamed:
  the new subgoal is \<open>\<And>z. z = ?x \<Longrightarrow> z \<noteq> ?y\<close>, which \<open>?x := True\<close>, \<open>?y := False\<close> satisfy. With the
  patch, the whole premise is renamed to \<open>\<And>z. z = ?y \<Longrightarrow> z \<noteq> ?y\<close>, which is unprovable.
\<close>

context
  fixes x :: bool
begin

lemma L: "(\<And>z::bool. z = x \<Longrightarrow> z \<noteq> x) \<Longrightarrow> True \<Longrightarrow> False"
  by blast

text \<open>
  The rule with the conclusion \<open>\<And>x::unit. True \<Longrightarrow> False\<close>, which Isar would flatten, and
  \<open>x\<close> generalized to \<open>?x\<close>:
\<close>

ML \<open>
  val A = Thm.cprem_of @{thm L} 1;
  val R =
    Thm.implies_intr A (Thm.forall_intr (Thm.cterm_of \<^context> (Free ("x", \<^typ>\<open>unit\<close>)))
      (Thm.implies_elim @{thm L} (Thm.assume A)))
    |> Thm.generalize (Names.empty, Names.make1_set "x") 0;
\<close>

end

schematic_goal bad: "PROP ?Q (\<lambda>y::unit. PROP ?R y)"
  apply (tactic \<open>resolve_tac \<^context> [R] 1\<close>)  \<comment> \<open>new subgoal \<open>\<And>z. z = ?x \<Longrightarrow> z \<noteq> ?y\<close>\<close>
  apply simp  \<comment> \<open>\<open>?x \<noteq> ?y\<close>\<close>
  apply (rule True_not_False)
  done

lemma False
  using bad by simp

end
