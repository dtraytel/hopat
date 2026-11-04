section \<open>Patch 12: tight proofs of flattened premises\<close>

theory Unpatched_12_ZTerm_Flatten
  imports Unpatched_Base
begin

text \<open>
  The new subgoals of a resolution step are the flattened premises of the rule, normalised
  afterwards. \<open>ZTerm.bicompose_proof\<close> builds the proofs of the premises from the new subgoals
  by flattening the normalised premises. Here the premise \<open>\<And>x. ZH x \<Longrightarrow> ?P x\<close> becomes the
  subgoal \<open>\<And>x. ZH x \<Longrightarrow> (\<And>y. ZK x y)\<close>, but its tight proof applies the subgoal to \<open>x\<close>,
  \<open>y\<close> and then to the assumption, which is ill-typed.
\<close>

consts ZC :: "(zi \<Rightarrow> prop) \<Rightarrow> prop" ZH :: "zi \<Rightarrow> prop" ZK :: "zi \<Rightarrow> zi \<Rightarrow> prop"
axiomatization where zflat: "(\<And>x. PROP ZH x \<Longrightarrow> PROP P x) \<Longrightarrow> PROP ZC P"

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val goal = \<^prop>\<open>PROP ZC (\<lambda>x. (\<And>y. PROP ZK x y))\<close>;
  val st = Seq.hd (resolve_tac ctxt @{thms zflat} 1 (Goal.init (Thm.cterm_of ctxt goal)));
  val _ = Proofterm.proofs := proofs;
  val N = hd (Thm.prems_of st);
  val _ = \<^assert> (N aconv \<^prop>\<open>\<And>x. PROP ZH x \<Longrightarrow> (\<And>y. PROP ZK x y)\<close>);
  (*the proof of the premise of the rule from the new subgoal*)
  val ZAbsp (_, _, ZAppp (_, ZAppp (_, p))) = Thm.zproof_of st;
  val _ = \<^assert> (not (can (zprop thy [N]) p));
\<close>

end
