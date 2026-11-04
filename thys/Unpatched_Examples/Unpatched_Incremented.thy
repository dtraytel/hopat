section \<open>Shared variables of different types with \<open>incremented = true\<close>\<close>

theory Unpatched_Incremented
  imports Unpatched_Base
begin

text \<open>
  With \<open>incremented = true\<close>, \<open>Thm.bicompose\<close> identifies the schematic variables of the proof
  state and the rule by their names. If a variable occurs with different types in both and gets
  bound, normalization raises an exception (\<open>Envir.lookup\<close>); if the types are unified, the
  variables are identified, which yields an instance of both theorems.
\<close>

ML_val \<open>
  val st = @{lemma "(z::bool) = True \<Longrightarrow> (x::nat) = x" by simp};
  val rl = @{lemma "(x::bool) = x" by simp};
  val r = Exn.result (fn () =>
    Thm.bicompose (SOME \<^context>) {flatten = true, match = false, incremented = true}
      (false, rl, 0) 1 st |> Seq.list_of) ();
  val _ = \<^assert>
    (case r of Exn.Exn (TYPE ("Variable has two distinct types", _, _)) => true | _ => false);
\<close>

end
