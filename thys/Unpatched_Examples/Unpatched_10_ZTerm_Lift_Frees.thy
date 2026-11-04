section \<open>Patch 10: free variables of lifted tight proofs\<close>

theory Unpatched_10_ZTerm_Lift_Frees
  imports Unpatched_Base
begin

text \<open>
  Lifting the rule \<open>Q x \<Longrightarrow> Q x\<close> with a free variable \<open>x :: ?'a\<close> over a subgoal \<open>Q ?z\<close>
  increments \<open>?'a\<close> in the lifted rule, but \<open>ZTerm.lift_proof\<close> keeps the type of \<open>x\<close> in the
  tight proof, where \<open>Q\<close> is instantiated with the incremented type.
\<close>

consts ZR :: "'a \<Rightarrow> prop"

ML_val \<open>
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val ctxt = \<^context>;
  val aT = TVar (("'a", 0), []);
  val bT = TVar (("'b", 0), []);
  val r = Thm.trivial (Thm.cterm_of ctxt (Const (\<^const_name>\<open>ZR\<close>, aT --> propT) $ Free ("x", aT)));
  val st = Thm.trivial (Thm.cterm_of ctxt (Const (\<^const_name>\<open>ZR\<close>, bT --> propT) $ Var (("z", 0), bT)));
  val lr = Thm.lift_rule (Thm.cprem_of st 1) r;
  val prf = Thm.zproof_of lr;
  val _ = Proofterm.proofs := proofs;
  (*the lifted rule has x :: ?'a1 ...*)
  val _ = \<^assert> (member (op =) (Term.add_frees (Thm.prop_of lr) []) ("x", TVar (("'a", 1), [])));
  (*... but its tight proof still has x :: ?'a*)
  fun frees (ZAbsp (_, t, p)) = ZTerm.fold_vars (fn v => fn vs => v :: vs) t [] @ frees p
    | frees (ZAppp (p, q)) = frees p @ frees q
    | frees _ = [];
  val _ = \<^assert> (member (op =) (frees prf) (("x", ~1), ZTerm.ztyp_of aT));
\<close>

end
