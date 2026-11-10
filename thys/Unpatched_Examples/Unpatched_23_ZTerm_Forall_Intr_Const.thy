section \<open>Patch 23: tight proofs of forall_intr over instances of proof constants\<close>

theory Unpatched_23_ZTerm_Forall_Intr_Const
  imports Unpatched_Base
begin

text \<open>
  \<open>ZTerm.forall_intr_proof\<close> abstracts the variable in the terms of the proof, but not in the
  instances of proof constants. The tight proof of \<open>x \<equiv> x\<close> is the reflexivity axiom with
  instance \<open>x\<close>; \<open>Thm.forall_intr\<close> gives \<open>\<And>x. x \<equiv> x\<close>, but its tight proof keeps the free
  \<open>x\<close> in the instance and proves \<open>\<And>y. x \<equiv> x\<close>. The same happens for \<open>Thm.abstract_rule\<close>
  (as in \<open>Conv.abs_conv\<close>): from \<open>Suc x \<equiv> Suc x\<close> it derives \<open>(\<lambda>x. Suc x) \<equiv> (\<lambda>x. Suc x)\<close>,
  and its tight proof applies the axiom \<open>abstract_rule\<close>, whose premise is
  \<open>\<And>x. Suc x \<equiv> Suc x\<close>, to a proof of \<open>\<And>y. Suc x \<equiv> Suc x\<close>. Proof constants of theorems
  list the free variables of their propositions in their instances too.
\<close>

ML_val \<open>
  val proofs = ! Proofterm.proofs;
  val _ = Proofterm.proofs := 4;
  val ctxt = \<^context>;
  val x = Free ("x", \<^typ>\<open>nat\<close>);
  val x' = ZVar (("x", ~1), ZTerm.ztyp_of \<^typ>\<open>nat\<close>);
  val th1 = Thm.forall_intr (Thm.cterm_of ctxt x) (Thm.reflexive (Thm.cterm_of ctxt x));
  val prf1 = Thm.zproof_of th1;
  val th2 =
    Thm.abstract_rule "x" (Thm.cterm_of ctxt x) (Thm.reflexive (Thm.cterm_of ctxt \<^term>\<open>Suc x\<close>));
  val prf2 = Thm.zproof_of th2;
  val _ = Proofterm.proofs := proofs;
  fun has_inst t (ZConstp (_, (_, inst))) = ZVars.exists (fn (_, u) => u = t) inst
    | has_inst _ _ = false;
  (*the theorem is \<And>x. x \<equiv> x, but the instance of the axiom in its tight proof is the free x*)
  val _ = \<^assert> (Thm.prop_of th1 aconv \<^prop>\<open>\<And>x::nat. x \<equiv> x\<close>);
  val _ = \<^assert> (case prf1 of ZAbst (_, _, c) => has_inst x' c | _ => false);
  (*the same for the premise of abstract_rule*)
  val _ = \<^assert> (Thm.prop_of th2 aconv \<^prop>\<open>(\<lambda>x. Suc x) \<equiv> (\<lambda>x. Suc x)\<close>);
  val _ =
    \<^assert> (case prf2 of
      ZAppp (_, ZAbst (_, _, c)) => has_inst (ZApp (ZConst0 \<^const_name>\<open>Suc\<close>, x')) c
    | _ => false);
\<close>

end
