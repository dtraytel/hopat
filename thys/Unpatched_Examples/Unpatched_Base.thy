section \<open>Tools for the examples\<close>

theory Unpatched_Base
  imports Main
begin

text \<open>
  The examples run in the unpatched Isabelle2026. A proof step that the patches make
  succeed fails there; it is stated with the method \<open>fails m\<close>, which succeeds (without
  changing the goal) exactly if the method \<open>m\<close> has no result.
\<close>

method_setup fails = \<open>
  Method.text_closure >> (fn text => fn ctxt => fn facts => fn st =>
    if is_none (Seq.pull (Seq.filter_results (Method.evaluate_runtime text ctxt facts st)))
    then Seq.single (Seq.Result st)
    else Seq.single (Seq.Error (fn () => "fails: the method has a result")))
\<close> "succeed iff the method fails"

text \<open>
  \<open>results tac st\<close> lists the results of a tactic; \<open>zprop thy Hs prf\<close> is the proposition that a
  tight proof proves, given the propositions \<open>Hs\<close> of its free proof variables, and fails if the
  proof is ill-typed.
\<close>

ML \<open>
  fun results tac st = Seq.list_of (tac st);
  fun zprop thy Hs prf =
    (case prf of
      ZBoundp i => nth Hs i
    | ZAbsp (_, t, p) =>
        let val A = ZTerm.term_of thy t in Logic.mk_implies (A, zprop thy (A :: Hs) p) end
    | ZAbst (a, T, p) =>
        let val T' = ZTerm.typ_of T
        in Logic.all_const T' $ Abs (a, T', zprop thy (map (Term.incr_boundvars 1) Hs) p) end
    | ZAppt (p, t) =>
        (case zprop thy Hs p of
          Const ("Pure.all", _) $ Abs (_, _, b) =>
            Envir.beta_norm (Term.subst_bound (ZTerm.term_of thy t, b))
        | _ => raise Fail "ZAppt")
    | ZAppp (p, q) =>
        (case zprop thy Hs p of
          Const ("Pure.imp", _) $ A $ B => if A aconv zprop thy Hs q then B else raise Fail "ZAppp"
        | _ => raise Fail "ZAppp")
    | ZConstp ((_, A), (instT, inst)) =>
        Term_Subst.instantiate
          (ZTVars.fold (fn (v, T) => TVars.add (v, ZTerm.typ_of T)) instT TVars.empty,
           ZVars.fold (fn ((x, T), t) => Vars.add ((x, ZTerm.typ_of T), ZTerm.term_of thy t)) inst
            Vars.empty)
          (ZTerm.term_of thy A)
    | _ => raise Fail "zprop");

  (*the theorem and its tight proof, with tight proofs recorded*)
  fun with_zproofs f x =
    let
      val proofs = ! Proofterm.proofs;
      val _ = Proofterm.proofs := 4;
      val r = Exn.result f x;
      val _ = Proofterm.proofs := proofs;
    in Exn.release r end;
\<close>

typedecl zi

end
