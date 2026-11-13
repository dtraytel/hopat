section \<open>Patch 26: instantiation of a variable of index -1\<close>

theory Unpatched_26_Thm_Instantiate_Index
  imports Unpatched_Base
begin

text \<open>
  \<open>Thm.instantiate\<close> takes any variable as the key of an instantiation. A variable of index
  \<open>-1\<close> does not occur in a theorem, so the theorem stays as it is. Tight terms write the free
  variable \<open>x\<close> as the variable \<open>x\<close> of index \<open>-1\<close>, and tight types likewise: the tight proof
  instantiates the free variable. The tight proof of \<open>x \<equiv> x\<close> is the reflexivity axiom with
  instance \<open>x\<close>; after the instantiation of \<open>?x\<close> of index \<open>-1\<close> by \<open>0\<close> the theorem is still
  \<open>x \<equiv> x\<close> and its tight proof proves \<open>0 \<equiv> 0\<close>. The same happens for the free type variable
  \<open>'a\<close> of \<open>y \<equiv> y\<close>. With the patch, \<open>Thm.instantiate\<close> raises \<open>THM\<close> for such a key.
\<close>

ML_val \<open>
  val ctxt = \<^context>;
  fun has_inst t (ZConstp (_, (_, inst))) = ZVars.exists (fn (_, u) => u = t) inst
    | has_inst _ _ = false;
  fun has_instT T (ZConstp (_, (instT, _))) = ZTVars.exists (fn (_, U) => U = T) instT
    | has_instT _ _ = false;

  (*a free variable*)
  val th0 = with_zproofs Thm.reflexive (Thm.cterm_of ctxt (Free ("x", \<^typ>\<open>nat\<close>)));
  val th =
    with_zproofs (Thm.instantiate
      (TVars.empty, Vars.make1 ((("x", ~1), \<^typ>\<open>nat\<close>), \<^cterm>\<open>0::nat\<close>))) th0;
  val _ = \<^assert> (Thm.prop_of th aconv Thm.prop_of th0);
  val _ = \<^assert> (has_inst (ZTerm.zterm_of \<^theory> \<^term>\<open>0::nat\<close>) (Thm.zproof_of th));

  (*a free type variable*)
  val th0' = with_zproofs Thm.reflexive (Thm.cterm_of ctxt (Free ("y", TFree ("'a", \<^sort>\<open>type\<close>))));
  val th' =
    with_zproofs (Thm.instantiate
      (TVars.make1 ((("'a", ~1), \<^sort>\<open>type\<close>), \<^ctyp>\<open>nat\<close>), Vars.empty)) th0';
  val _ = \<^assert> (Thm.prop_of th' aconv Thm.prop_of th0');
  val _ = \<^assert> (has_instT (ZTerm.ztyp_of \<^typ>\<open>nat\<close>) (Thm.zproof_of th'));
\<close>

end
