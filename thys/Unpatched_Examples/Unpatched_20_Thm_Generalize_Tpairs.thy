section \<open>Patch 20: the classic proof of \<open>generalize\<close> and the flex-flex pairs\<close>

theory Unpatched_20_Thm_Generalize_Tpairs
  imports Unpatched_Base
begin

text \<open>
  \<open>Thm.generalize\<close> generalizes the free variables in the flex-flex pairs as well, but its classic
  proof (\<open>Proofterm.generalize_proof\<close>) generalizes only those of the proposition. A free variable
  \<open>a\<close> that occurs only in a pair becomes \<open>?a\<close> in the pair but stays fixed in the proof, and an
  instance of the theorem has a proof that does not reconstruct (counterexample by Kevin).
  Abstracting the variable in the proof would not help either, since the pairs constrain it; the
  proof with the variable substituted reconstructs.
\<close>

lemma gtr1: "x True \<Longrightarrow> x True" .

ML_val \<open>
  val ctxt = \<^context>;
  val thy = \<^theory>;
  val insts = [(("x", 1), \<^cterm>\<open>\<lambda>_::bool. True\<close>), (("P", 0), \<^cterm>\<open>\<lambda>x::bool. x\<close>)];
  val (th0, th) = Unsynchronized.setmp Proofterm.proofs 2 (fn () =>
    let
      val th0 = @{thm gtr1} RS Drule.infer_instantiate ctxt [(("x", 0), \<^cterm>\<open>a::bool\<close>)] @{thm exI};
      val th = th0
        |> Thm.generalize (Names.empty, Names.make_set ["a"]) 2
        |> Drule.infer_instantiate ctxt insts;
    in (th0, th) end) ();
  val _ = \<^assert> (Thm.tpairs_of th0 <> [] andalso
    not (member (op =) (Term.add_free_names (Thm.prop_of th0) []) "a"));
  val _ = \<^assert> (Thm.tpairs_of th = [] andalso Thm.prop_of th aconv \<^prop>\<open>True \<Longrightarrow> \<exists>x. x\<close>);
  val _ = \<^assert> (member (op =) (Proofterm.fold_proof_terms Term.add_free_names (Thm.proof_of th) []) "a");
  val _ = \<^assert> (not (can Thm.reconstruct_proof_of th));

  (*the proof with the variable of the pairs substituted instead of abstracted reconstructs for the
    instance (in which the pair True \<equiv> ?a2 is solved by ?a2 := True)*)
  val th1 = Thm.generalize (Names.empty, Names.make_set ["a"]) 2 th0;
  val prf =
    Thm.proof_of th0 |> Proofterm.map_proof_terms (Term_Subst.generalize (Names.empty, Names.make_set ["a"]) 2) I;
  val inst = Vars.make
    [((("x", 1), \<^typ>\<open>bool \<Rightarrow> bool\<close>), \<^term>\<open>\<lambda>_::bool. True\<close>),
     ((("P", 0), \<^typ>\<open>bool \<Rightarrow> bool\<close>), \<^term>\<open>\<lambda>x::bool. x\<close>),
     ((("a", 2), \<^typ>\<open>bool\<close>), \<^term>\<open>True\<close>)];
  val P' = Envir.beta_norm (Term_Subst.instantiate (TVars.empty, inst) (Thm.prop_of th1));
  val _ = \<^assert> (P' aconv Thm.prop_of th);
  val _ = \<^assert> (can (Proof_Checker.thm_of_proof thy o Proofterm.reconstruct_proof thy P')
    (Proofterm.instantiate (TVars.empty, inst) prf));
  val _ = \<^assert> (not (can (Proof_Checker.thm_of_proof thy o Proofterm.reconstruct_proof thy P')
    (Proofterm.instantiate (TVars.empty, inst) (Thm.proof_of th1))));
\<close>

end
