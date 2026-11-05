section \<open>The Pattern Test\<close>

theory Match_Pattern
  imports Match_Complete
begin

text \<open>
  \<^const>\<open>pattern\<close> (\<open>Pattern.pattern\<close>) decides whether a term is a higher-order pattern: it agrees
  with the inductive characterization \<^const>\<open>ppat\<close> on terms without \<open>\<beta>\<close>-redexes; on terms with
  \<open>\<beta>\<close>-redexes it does not inspect the heads of redexes. The two directions are theorems
  \<open>ppat_pattern\<close> and \<open>pattern_ppat\<close> of theory
  \<^theory>\<open>Pattern_Correctness.Pattern_Norm_Term\<close>, where the occurs check needs them.
\<close>

context pure_sig
begin

corollary pattern_iff_ppat: "no_redex t \<Longrightarrow> pattern t \<longleftrightarrow> ppat t"
  using pattern_ppat ppat_pattern by blast

end

end
