section \<open>Patch 14: class memberships in composed tight proofs\<close>

theory Unpatched_14_ZTerm_Norm_Ofclass
  imports Unpatched_Base
begin

text \<open>
  \<open>ZTerm.norm_term\<close> does not normalise the types of class memberships. Resolution with
  \<open>OFCLASS(?'a, zd_class) \<Longrightarrow> ZP ?x\<close> on \<open>ZP y\<close> for \<open>y :: zi\<close> gives the subgoal
  \<open>OFCLASS(zi, zd_class)\<close>, but its tight proof assumes \<open>OFCLASS(?'a, zd_class)\<close>.
\<close>

class zd
consts ZP :: "'a \<Rightarrow> prop" zy :: zi
axiomatization where zofc: "OFCLASS('a, zd_class) \<Longrightarrow> PROP ZP (x::'a)"

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val goal = \<^prop>\<open>PROP ZP zy\<close>;
  val st = Seq.hd (resolve_tac ctxt @{thms zofc} 1 (Goal.init (Thm.cterm_of ctxt goal)));
  val _ = Proofterm.proofs := proofs;
  val N = hd (Thm.prems_of st);
  val _ = \<^assert> (N aconv Logic.mk_of_class (\<^typ>\<open>zi\<close>, \<^class>\<open>zd\<close>));
  (*the annotation of the new subgoal in the tight proof*)
  val ZAbsp (_, A, _) = Thm.zproof_of st;
  val _ = \<^assert> (not (ZTerm.term_of thy A aconv N));
  val _ = \<^assert> (Term.is_TVar (#1 (Logic.dest_of_class (ZTerm.term_of thy A))));
\<close>

end
