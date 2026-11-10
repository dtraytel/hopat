section \<open>Patch 24: the tight proof of unconstrainT\<close>

theory Unpatched_24_ZTerm_Unconstrain
  imports Unpatched_Base
begin

text \<open>
  \<open>Thm.unconstrainT\<close> replaces the type variables of a theorem by type variables without sort
  constraints and adds the premises \<open>OFCLASS\<close> for the sort hypotheses; its classic proof is a
  proof box of this proposition. Its tight proof (\<open>ZTerm.add_box_proof {unconstrain = true}\<close>)
  is a box whose premises are the classes of the present type variables only, and it applies
  this box to proofs \<open>OFCLASSp\<close> of the classes for the unconstrained type variables: from
  \<open>?x \<equiv> ?x\<close> with \<open>?x :: ?'a :: order\<close>, it derives \<open>OFCLASS(?'a, order_class) \<Longrightarrow> ?x \<equiv> ?x\<close> with a
  tight proof of \<open>?x \<equiv> ?x\<close> that relies on \<open>OFCLASS(?'a, order_class)\<close> for an
  unconstrained \<open>?'a\<close>. For a sort hypothesis without type variable, the premise is missing
  from the box: the theorem is \<open>OFCLASS(?'a, zbar_class) \<Longrightarrow> True\<close>, its tight proof proves
  \<open>True\<close>.
\<close>

class zbar = fixes zb :: 'a assumes zbar_neq: "zb \<noteq> zb"

ML \<open>
  (*zprop with class proofs*)
  fun zprop' thy Hs prf =
    (case prf of
      ZAppp (p, OFCLASSp (T, c)) =>
        (case zprop' thy Hs p of
          Const ("Pure.imp", _) $ A $ B =>
            if A aconv Logic.mk_of_class (ZTerm.typ_of T, c) then B else raise Fail "ZAppp"
        | _ => raise Fail "ZAppp")
    | _ => zprop thy Hs prf);
\<close>

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val x = Thm.cterm_of ctxt (Var (("x", 0), TVar (("'a", 0), \<^sort>\<open>order\<close>)));
  val th = with_zproofs (Thm.unconstrainT o Thm.reflexive) x;
  val prf = Thm.zproof_of th;
  val A = Thm.prop_of th;
  val _ = \<^assert> (length (Logic.strip_imp_prems A) = 1);
  (*the tight proof proves the conclusion, using a class proof for an unconstrained type variable*)
  val _ = \<^assert> (zprop' thy [] prf aconv Logic.strip_imp_concl A);
  val _ = \<^assert> (case prf of ZAppp (_, OFCLASSp (ZTVar (_, []), _)) => true | _ => false);

  val y = Thm.cterm_of ctxt (Var (("y", 0), TVar (("'a", 0), \<^sort>\<open>zbar\<close>)));
  val th' =
    with_zproofs (fn () =>
      Thm.unconstrainT (Thm.forall_elim y (Thm.forall_intr y (Thm.trivial \<^cprop>\<open>True\<close>)))) ();
  val A' = Thm.prop_of th';
  (*the premise of the sort hypothesis is missing from the box*)
  val _ = \<^assert> (length (Logic.strip_imp_prems A') = 2);
  val _ = \<^assert> (zprop' thy [] (Thm.zproof_of th') aconv \<^prop>\<open>True \<Longrightarrow> True\<close>);
\<close>

end
