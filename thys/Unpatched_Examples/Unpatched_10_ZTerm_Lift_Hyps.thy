section \<open>Patch 10: the assumptions of a lifted subgoal in tight proofs\<close>

theory Unpatched_10_ZTerm_Lift_Hyps
  imports Unpatched_Base
begin

text \<open>
  Lifting a rule over a subgoal \<open>PA ?x \<Longrightarrow> PB c\<close> keeps the assumption \<open>PA ?x\<close> of the subgoal as it
  is: resolving it with \<open>PD ?x \<Longrightarrow> PB c\<close> (here a trivial theorem with that conclusion) yields a
  theorem with the premise \<open>PA ?x \<Longrightarrow> PD ?x1\<close>. \<open>ZTerm.lift_proof\<close> annotates the abstraction over
  that assumption in the tight proof with \<open>PA ?x1\<close>, the assumption with the indices of its
  variables incremented like those of the rule: the variable of the rule, not the one of the
  assumption. The classic proof (\<open>Proofterm.lift_proof\<close>) has no annotation there.
\<close>

consts PA :: "zi \<Rightarrow> prop" PB :: "zi \<Rightarrow> prop" PD :: "zi \<Rightarrow> prop" zc :: zi

ML_val \<open>
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val ctxt = \<^context>;
  val iT = \<^typ>\<open>zi\<close>;
  fun P n t = Const (n, iT --> propT) $ t;
  val c = Const (\<^const_name>\<open>zc\<close>, iT);
  fun x i = Var (("x", i), iT);
  fun triv t = Thm.trivial (Thm.cterm_of ctxt t);
  val st = triv (Logic.mk_implies (P \<^const_name>\<open>PA\<close> (x 0), P \<^const_name>\<open>PB\<close> c));
  val r = triv (Logic.mk_implies (P \<^const_name>\<open>PD\<close> (x 0), P \<^const_name>\<open>PB\<close> c));
  val res = Thm.biresolution NONE false [(false, r)] 1 st |> Seq.hd;
  val prf = Thm.zproof_of res;
  val _ = Proofterm.proofs := proofs;
  fun annots (ZAbsp (_, t, p)) = t :: annots p
    | annots (ZAbst (_, _, p)) = annots p
    | annots (ZAppt (p, _)) = annots p
    | annots (ZAppp (p, q)) = annots p @ annots q
    | annots _ = [];
  fun zP n i = ZApp (ZConst0 n, ZVar (("x", i), ZTerm.ztyp_of iT));
  (*the premise of the theorem has the assumption PA ?x, ...*)
  val _ = \<^assert> (member (op aconv) (Logic.strip_imp_prems (Thm.prop_of res))
    (Logic.mk_implies (P \<^const_name>\<open>PA\<close> (x 0), P \<^const_name>\<open>PD\<close> (x 1))));
  (*... but the tight proof assumes PA ?x1*)
  val _ = \<^assert> (member (op =) (annots prf) (zP \<^const_name>\<open>PA\<close> 1));
\<close>

end
