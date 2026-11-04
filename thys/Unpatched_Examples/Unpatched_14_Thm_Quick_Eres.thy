section \<open>Patch 14: the quick test of elim-resolution (completeness)\<close>

theory Unpatched_14_Thm_Quick_Eres
  imports Unpatched_Base
begin

text \<open>
  Elim-resolution of the rule \<open>PROP qR \<Longrightarrow> PROP qC\<close> with the subgoal
  \<open>\<And>x. (\<And>z. PROP qS \<Longrightarrow> PROP qR) \<Longrightarrow> (\<And>y. PROP qS \<Longrightarrow> PROP qC)\<close> succeeds: it strips the
  parameter \<open>x\<close> and the first assumption from the lifted first premise of the rule and unifies
  the rest \<open>\<And>y. PROP qS \<Longrightarrow> PROP qR\<close> with the assumption \<open>\<And>z. PROP qS \<Longrightarrow> PROP qR\<close>. The quick test of
  \<open>Thm.biresolution\<close> compares the premise \<open>PROP qR\<close> itself with the assumptions of the subgoal,
  \<open>\<And>z. PROP qS \<Longrightarrow> PROP qR\<close> and \<open>PROP qS\<close>, and skips the rule: \<open>erule\<close> fails unless the tracing of
  unification failures disables the test.
\<close>

typedecl qi
axiomatization qR :: "prop" and qS :: "prop" and qC :: "prop" where qrule: "PROP qR \<Longrightarrow> PROP qC"

lemma "\<And>x::qi. (\<And>z::qi. PROP qS \<Longrightarrow> PROP qR) \<Longrightarrow> (\<And>y::qi. PROP qS \<Longrightarrow> PROP qC)"
  apply (fails \<open>erule qrule\<close>)
  supply [[unify_trace_failure]]
  apply (erule qrule)
  done

end
