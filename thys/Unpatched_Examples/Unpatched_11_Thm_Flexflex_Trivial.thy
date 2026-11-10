section \<open>Patch 11: trivial flex-flex pairs after \<open>flexflex_rule\<close>\<close>

theory Unpatched_11_Thm_Flexflex_Trivial
  imports Unpatched_Base
begin

text \<open>
  \<open>Thm.flexflex_rule\<close> removes the trivial flex-flex pairs (\<open>t \<equiv> t\<close>) of the instance of a
  theorem by a unifier, but returns the theorem unchanged if the unifier is empty. A theorem whose
  pairs are already trivial then keeps them, and \<open>Thm.plain_prop_of\<close> rejects the result
  (counterexample by Kevin Kappelmann and Fabian Huch, from \<open>Thm.instantiate_beta\<close>, which does
  not remove trivial pairs).
\<close>

lemma ffr1: "x True \<Longrightarrow> x True" .
lemma ffr2: "P True \<Longrightarrow> \<forall>x::bool. P True" by simp

ML_val \<open>
  val th = @{thm ffr1[THEN ffr2]}
    |> Thm.instantiate_beta (TVars.empty, Vars.make
      [((("x", 1), \<^typ>\<open>bool \<Rightarrow> bool\<close>), \<^cterm>\<open>\<lambda>_::bool. True\<close>),
       ((("P", 0), \<^typ>\<open>bool \<Rightarrow> bool\<close>), \<^cterm>\<open>\<lambda>_::bool. True\<close>)]);
  val _ = \<^assert> (Thm.tpairs_of th = [(\<^term>\<open>True\<close>, \<^term>\<open>True\<close>)]);
  val th' = Seq.hd (Thm.flexflex_rule NONE th);
  val _ = \<^assert> (Thm.tpairs_of th' = [(\<^term>\<open>True\<close>, \<^term>\<open>True\<close>)]);
  val _ = \<^assert> (not (can Thm.plain_prop_of th'));
\<close>

end
