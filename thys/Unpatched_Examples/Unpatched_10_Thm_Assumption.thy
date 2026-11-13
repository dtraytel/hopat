section \<open>Patch 10: the classic proof by assumption with an instantiated conclusion\<close>

theory Unpatched_10_Thm_Assumption
  imports Unpatched_Base
begin

text \<open>
  \<open>Thm.assumption\<close> unifies an assumption of the subgoal with its conclusion, both taken
  before normalisation (\<open>Logic.assum_problems (~1, Bi)\<close>), but the classic proof proves the
  normalised subgoal by \<open>mk_asm_prf\<close>, which abstracts over all assumptions of the normalised
  subgoal. If the unifier instantiates the conclusion by an implication, the proof abstracts over
  its premises as well and does not check. Here the subgoal \<open>(TA \<Longrightarrow> TB) \<Longrightarrow> ?P\<close> is solved by its
  assumption with \<open>?P := TA \<Longrightarrow> TB\<close>, and the proof proves the premise by
  \<open>\<lambda>H:TA \<Longrightarrow> TB. \<lambda>H':TA. H\<close>. The tight proof is affected likewise (patch 19).
\<close>

consts TA :: "prop" TB :: "prop"

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  fun init A = Goal.init (Thm.cterm_of ctxt (Logic.mk_implies (A, Var (("P", 0), propT))));
  fun assume st = Seq.hd (Thm.assumption (SOME ctxt) 1 st);
  val prop = Logic.protect \<^prop>\<open>(PROP TA \<Longrightarrow> PROP TB) \<Longrightarrow> PROP TA \<Longrightarrow> PROP TB\<close>;
  fun checks th =
    can (Proof_Checker.thm_of_proof thy o Proofterm.reconstruct_proof thy (Thm.prop_of th))
      (Thm.proof_of th);

  (*the proof state and the result, both with classic proofs recorded (the default level of
    proofs records none, and a proof without the proof of the state never checks)*)
  fun with_proofs f x =
    let
      val proofs = ! Proofterm.proofs;
      val _ = Proofterm.proofs := 2;
      val r = Exn.result f x;
      val _ = Proofterm.proofs := proofs;
    in Exn.release r end;
  fun solve A = with_proofs (fn () => let val st = init A in (st, assume st) end) ();

  (*the classic proof does not check, although the proof of the proof state does*)
  val (st, th) = solve \<^prop>\<open>PROP TA \<Longrightarrow> PROP TB\<close>;
  val _ = \<^assert> (Thm.prop_of th aconv prop);
  val _ = \<^assert> (checks st);
  val _ = \<^assert> (not (checks th));

  (*it checks if the conclusion is not instantiated by an implication*)
  val (st0, th0) = solve \<^prop>\<open>PROP TB\<close>;
  val _ = \<^assert> (checks st0 andalso checks th0);
\<close>

end
