section \<open>Patch 12: tight proofs by assumption\<close>

theory Unpatched_12_ZTerm_Asm
  imports Unpatched_Base
begin

text \<open>
  Elim-resolution proves the first premise \<open>A\<close> of the rule by one of its assumptions; the tight
  proof abstracts over the assumptions of the normalised premise, up to the number of assumptions
  of the subgoal, while the unifier only considered the assumptions of \<open>A\<close> before normalisation.
  Here (\<open>Thm.bicompose\<close> with an unlifted rule) the premise \<open>(ZEA \<Longrightarrow> ZEB) \<Longrightarrow> ?Q\<close> has one
  assumption, the subgoal two, and the unifier instantiates \<open>?Q := ZEA \<Longrightarrow> ZEB\<close>: the tight proof
  of the premise abstracts over \<open>ZEA\<close> as well and proves
  \<open>(ZEA \<Longrightarrow> ZEB) \<Longrightarrow> ZEA \<Longrightarrow> (ZEA \<Longrightarrow> ZEB)\<close>, so the composed proof is ill-typed.
\<close>

consts ZEA :: "prop" ZEB :: "prop" ZEH1 :: "prop" ZEH2 :: "prop" ZEK :: "prop"

ML \<open>Proofterm.proofs := 4\<close>
axiomatization where zeres: "((PROP ZEA \<Longrightarrow> PROP ZEB) \<Longrightarrow> PROP Q) \<Longrightarrow> PROP R"
ML \<open>Proofterm.proofs := 0\<close>

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val st = Goal.init \<^cterm>\<open>PROP ZEH1 \<Longrightarrow> PROP ZEH2 \<Longrightarrow> PROP ZEK\<close>;
  val st' = Seq.hd (Thm.bicompose (SOME ctxt) {flatten = false, match = false, incremented = false}
    (true, @{thm zeres}, 1) 1 st);
  val _ = Proofterm.proofs := proofs;
  val ZAppp (_, ZAppp (p, asm)) = Thm.zproof_of st';
  val _ = \<^assert> (zprop thy [] p aconv
    \<^prop>\<open>((PROP ZEA \<Longrightarrow> PROP ZEB) \<Longrightarrow> PROP ZEA \<Longrightarrow> PROP ZEB) \<Longrightarrow> PROP ZEH1 \<Longrightarrow> PROP ZEH2 \<Longrightarrow> PROP ZEK\<close>);
  val _ = \<^assert> (zprop thy [] asm aconv
    \<^prop>\<open>(PROP ZEA \<Longrightarrow> PROP ZEB) \<Longrightarrow> PROP ZEA \<Longrightarrow> (PROP ZEA \<Longrightarrow> PROP ZEB)\<close>);
  val _ = \<^assert> (not (can (zprop thy []) (Thm.zproof_of st')));
\<close>

end
