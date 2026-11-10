section \<open>Patch 19: the tight proof by assumption with an instantiated conclusion\<close>

theory Unpatched_19_ZTerm_Assumption
  imports Unpatched_Base
begin

text \<open>
  The tight proof of \<open>Thm.assumption\<close> (\<open>ZTerm.assumption_proof\<close>) proves the normalised
  subgoal by \<open>mk_asm_prf\<close> with all assumptions of the normalised subgoal, while the unifier
  considers those before normalisation (\<open>Logic.assum_problems (~1, Bi)\<close>), as the classic proof
  did before patch 10. If the unifier instantiates the conclusion by an implication, the proof
  abstracts over its premises as well and is ill-typed. Here the subgoal \<open>(TA \<Longrightarrow> TB) \<Longrightarrow> ?P\<close> is
  solved by its assumption with \<open>?P := TA \<Longrightarrow> TB\<close>, and the tight proof proves the premise by
  \<open>\<lambda>H:TA \<Longrightarrow> TB. \<lambda>H':TA. H\<close>.
\<close>

consts TA :: "prop" TB :: "prop"

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val st = Goal.init (Thm.cterm_of ctxt
    (Logic.mk_implies (\<^prop>\<open>PROP TA \<Longrightarrow> PROP TB\<close>, Var (("P", 0), propT))));
  fun assume st = Seq.hd (Thm.assumption (SOME ctxt) 1 st);
  val prop = Logic.protect \<^prop>\<open>(PROP TA \<Longrightarrow> PROP TB) \<Longrightarrow> PROP TA \<Longrightarrow> PROP TB\<close>;

  (*the tight proof is ill-typed*)
  val zth = with_zproofs assume st;
  val _ = \<^assert> (Thm.prop_of zth aconv prop);
  val ZAppp (_, asm) = Thm.zproof_of zth;
  val _ = \<^assert> (zprop thy [] asm aconv
    \<^prop>\<open>(PROP TA \<Longrightarrow> PROP TB) \<Longrightarrow> PROP TA \<Longrightarrow> (PROP TA \<Longrightarrow> PROP TB)\<close>);
  val _ = \<^assert> (not (can (zprop thy []) (Thm.zproof_of zth)));
\<close>

end
