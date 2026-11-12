section \<open>Instances of tight proof boxes with variables of the same name\<close>

theory Unpatched_Box_Instances
  imports Unpatched_Base
begin

text \<open>
  A tight proof box (\<open>ZConstp\<close>) records the instances of the variables of its proposition in a
  table keyed by name and type. A type instantiation of the proof (\<open>ZTerm.map_insts_same\<close>)
  retypes the keys. If the proposition has two variables of the same name and different types,
  such as \<open>?x :: ?'a\<close> and \<open>?x :: ?'b\<close> (which the rules that combine theorems produce, and
  which Isabelle does not reject), a type instantiation that identifies their types merges two
  keys; if their instances differ, \<open>ZTerm.make_inst\<close> raises \<open>ZTerm.BAD_INST\<close>. So with tight
  proofs, \<open>Thm.instantiate\<close> fails on such a theorem, while it succeeds with classic proofs. This
  affects named boxes (\<open>Thm.close_derivation\<close>) and the box of \<open>Thm.unconstrainT\<close> alike. It is
  a failure, not an unsound proof: the instances cannot be represented, so none is built. The
  model of \<open>unconstrainT\<close> (\<open>Thm_Unconstrain.thy\<close>, \<open>vars_consistent\<close>) excludes such theorems,
  since the invariant of the tight proofs (\<open>zconsts_ok\<close>) requires the variables of each box to
  have distinct names. None of the patches changes this.
\<close>

ML \<open>
  fun inconsistent_thm ctxt box =
    let
      val xa = Thm.cterm_of ctxt (Var (("x", 0), TVar (("'a", 0), [])));
      val xb = Thm.cterm_of ctxt (Var (("x", 0), TVar (("'b", 0), [])));
    in box (Thm.implies_intr (Thm.cprop_of (Thm.reflexive xb)) (Thm.reflexive xa)) end;

  (*instantiate ?x :: ?'a and ?x :: ?'b by different variables, then ?'a := ?'b*)
  fun inst_then_merge ctxt th =
    let
      val aT = TVar (("'a", 0), []) and bT = TVar (("'b", 0), []);
      val u = Thm.cterm_of ctxt (Var (("u", 0), aT)) and w = Thm.cterm_of ctxt (Var (("w", 0), bT));
    in
      th
      |> Thm.instantiate (TVars.empty, Vars.make [((("x", 0), aT), u), ((("x", 0), bT), w)])
      |> Thm.instantiate (TVars.make [((("'a", 0), []), Thm.ctyp_of ctxt bT)], Vars.empty)
    end;

  fun is_bad_inst f x = (f x; false) handle ZTerm.BAD_INST _ => true;
\<close>

ML_val \<open>
  val ctxt = \<^context>;
  val boxes = [Thm.unconstrainT, Thm.close_derivation \<^here>];

  (*with tight proofs, the type instantiation fails*)
  val _ = boxes |> List.app (fn box =>
    \<^assert> (with_zproofs (is_bad_inst (fn () => inst_then_merge ctxt (inconsistent_thm ctxt box))) ()));

  (*with classic proofs, it succeeds: the variables of the result are ?u, ?w :: ?'b*)
  val _ = boxes |> List.app (fn box =>
    let
      val th = inst_then_merge ctxt (inconsistent_thm ctxt box);
      val bT = TVar (("'b", 0), []);
    in
      \<^assert> (sort_by (#1 o #1) (Term.add_vars (Thm.prop_of th) []) =
        [(("u", 0), bT), (("w", 0), bT)])
    end);
\<close>

end
