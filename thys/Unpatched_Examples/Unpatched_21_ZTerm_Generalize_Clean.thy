section \<open>Patch 21: names of the generalized variables in tight proofs\<close>

theory Unpatched_21_ZTerm_Generalize_Clean
  imports Unpatched_Base
begin

text \<open>
  Generalizing the skolem constant \<open>x__\<close> of \<open>x__ \<equiv> x__\<close> gives \<open>?x3 \<equiv> ?x3\<close>: \<open>Thm.generalize\<close>
  cleans the internal name (\<open>Name.clean_index\<close>), which raises the index. \<open>ZTerm.generalize_proof\<close>
  keeps the name: the tight proof instantiates the reflexivity axiom with \<open>?x__1\<close> and proves
  \<open>?x__1 \<equiv> ?x__1\<close>. Skolem constants are generalized whenever a result is exported from a
  context with fixed variables.
\<close>

ML_val \<open>
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val ctxt = \<^context>;
  val th = Thm.reflexive (Thm.cterm_of ctxt (Free (Name.skolem "x", \<^typ>\<open>nat\<close>)));
  val th' = Thm.generalize (Names.empty, Names.make_set [Name.skolem "x"]) 1 th;
  val prf = Thm.zproof_of th';
  val _ = Proofterm.proofs := proofs;
  (*the theorem has ?x3 ...*)
  val _ = \<^assert> (Term.add_vars (Thm.prop_of th') [] = [(("x", 3), \<^typ>\<open>nat\<close>)]);
  (*... but its tight proof has ?x__1*)
  val _ =
    \<^assert> (case prf of
      ZConstp (_, (_, inst)) =>
        ZVars.exists (fn (_, t) => t = ZVar (("x__", 1), ZTerm.ztyp_of \<^typ>\<open>nat\<close>)) inst
    | _ => false);
\<close>

end
