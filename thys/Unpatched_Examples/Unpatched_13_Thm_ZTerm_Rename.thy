section \<open>Patch 13: tight proofs of renamed premises\<close>

theory Unpatched_13_Thm_ZTerm_Rename
  imports Unpatched_Base
begin

text \<open>
  \<open>Thm.bicompose_aux\<close> renames variables of the new premises of a lifted rule after the bound
  variables of the subgoal, and the variables of the classic proof of the rule likewise, but not
  those of its tight proof. Resolution with \<open>ZG ?x \<Longrightarrow> ZF (\<lambda>x. x)\<close> on \<open>ZF (\<lambda>y. y)\<close> gives the
  subgoal \<open>ZG ?y\<close>, while the tight proof of the rule still proves \<open>ZG ?x \<Longrightarrow> ZF (\<lambda>x. x)\<close>.
\<close>

consts ZF :: "(zi \<Rightarrow> zi) \<Rightarrow> prop" ZG :: "zi \<Rightarrow> prop"

ML \<open>Proofterm.proofs := 4\<close>
axiomatization where zren: "PROP ZG x \<Longrightarrow> PROP ZF (\<lambda>x. x)"
ML \<open>Proofterm.proofs := 0\<close>

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val goal = \<^prop>\<open>PROP ZF (\<lambda>y. y)\<close>;
  val st = Seq.hd (resolve_tac ctxt @{thms zren} 1 (Goal.init (Thm.cterm_of ctxt goal)));
  val _ = Proofterm.proofs := proofs;
  val N = hd (Thm.prems_of st);
  val _ = \<^assert> (fst (fst (Term.dest_Var (snd (Term.dest_comb N)))) = "y");
  (*the tight proof of the theorem is ill-typed*)
  val _ = \<^assert> (not (can (zprop thy []) (Thm.zproof_of st)));
\<close>

end
