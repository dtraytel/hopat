section \<open>Patch 18: proofs by assumption with an instantiated conclusion\<close>

theory Unpatched_18_Thm_Assumption
  imports Unpatched_Base
begin

text \<open>
  \<open>Thm.assumption\<close> unifies an assumption of the subgoal with its conclusion, both taken
  before normalisation (\<open>Logic.assum_problems (~1, Bi)\<close>), but the classic and the tight proofs
  prove the normalised subgoal by \<open>mk_asm_prf\<close>, which abstracts over all assumptions of the
  normalised subgoal. If the unifier instantiates the conclusion by an implication, the proofs
  abstract over its premises as well and are ill-typed. Here the subgoal
  \<open>(TA \<Longrightarrow> TB) \<Longrightarrow> ?P\<close> is solved by its assumption with \<open>?P := TA \<Longrightarrow> TB\<close>, and both proofs prove
  the premise by \<open>\<lambda>H:TA \<Longrightarrow> TB. \<lambda>H':TA. H\<close>.
\<close>

consts TA :: "prop" TB :: "prop"

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val st = Goal.init (Thm.cterm_of ctxt
    (Logic.mk_implies (\<^prop>\<open>PROP TA \<Longrightarrow> PROP TB\<close>, Var (("P", 0), propT))));
  fun assume st = Seq.hd (Thm.assumption (SOME ctxt) 1 st);
  val prop = Logic.protect \<^prop>\<open>(PROP TA \<Longrightarrow> PROP TB) \<Longrightarrow> PROP TA \<Longrightarrow> PROP TB\<close>;

  (*the classic proof does not check*)
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 2;
  val th = Exn.result assume st;
  val _ = Proofterm.proofs := proofs;
  val th = Exn.release th;
  val _ = \<^assert> (Thm.prop_of th aconv prop);
  fun checks th =
    can (Proof_Checker.thm_of_proof thy o Proofterm.reconstruct_proof thy (Thm.prop_of th))
      (Thm.proof_of th);
  val _ = \<^assert> (not (checks th));

  (*it checks if the conclusion is not instantiated by an implication*)
  val _ = Proofterm.proofs := 2;
  val th0 = Exn.result assume
    (Goal.init (Thm.cterm_of ctxt (Logic.mk_implies (\<^prop>\<open>PROP TB\<close>, Var (("P", 0), propT)))));
  val _ = Proofterm.proofs := proofs;
  val _ = \<^assert> (checks (Exn.release th0));

  (*the tight proof is ill-typed*)
  val zth = with_zproofs assume st;
  val _ = \<^assert> (Thm.prop_of zth aconv prop);
  val ZAppp (_, asm) = Thm.zproof_of zth;
  val _ = \<^assert> (zprop thy [] asm aconv
    \<^prop>\<open>(PROP TA \<Longrightarrow> PROP TB) \<Longrightarrow> PROP TA \<Longrightarrow> (PROP TA \<Longrightarrow> PROP TB)\<close>);
  val _ = \<^assert> (not (can (zprop thy []) (Thm.zproof_of zth)));
\<close>

end
