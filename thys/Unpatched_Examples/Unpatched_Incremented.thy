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

text \<open>
  A variable that occurs with two types in the proof state alone is a third case. The pattern
  unifier compares the heads of a flex-flex pair by their names (\<open>if F = G\<close> in \<open>Pattern.cases\<close>),
  so it takes \<open>?x :: 'a \<Rightarrow> 'b \<Rightarrow> 'r\<close> and \<open>?x :: 'b \<Rightarrow> 'a \<Rightarrow> 'r\<close> for one variable and binds it, at
  the first type, to a function that ignores both arguments. If the occurrence at the other
  type is in the solved subgoal only, no lookup meets it again, and the resolution has a
  result. The result is a consequence of the state and the rule: the solved subgoal holds if
  the variable at the other type is the same constant function, and that variable occurs
  nowhere else. But the environment alone does not unify the subgoal with the rule, and the
  state is outside the theorems of the correctness proofs, which assume one type for each name.
  If the variable at the other type occurs in the conclusion as well, normalization raises
  \<open>TYPE\<close>. If the two occurrences have different numbers of arguments, \<open>Pattern.mk_ff_list\<close>
  raises \<open>Fail\<close>, an exception that leaves the kernel.
\<close>

ML_val \<open>
  val thy = \<^theory>;
  val ct = Thm.global_cterm_of thy;
  val (A, B, R) = (TFree ("'a", \<^sort>\<open>type\<close>), TFree ("'b", \<^sort>\<open>type\<close>), TFree ("'r", \<^sort>\<open>type\<close>));
  fun lam b = Abs ("u", A, Abs ("v", B, b));
  (*the theorem "s == t ==> concl" with the two free variables turned into ?x at two types*)
  fun state (T, s) (U, t) concl =
    let
      val hyp = ct (Logic.mk_equals (s (Free ("x1", T)), t (Free ("x2", U))));
      val th = Thm.implies_intr hyp (concl hyp)
        |> Thm.generalize (Names.empty, Names.make_set ["x1", "x2"]) 0;
    in Thm.instantiate (TVars.empty, Vars.make1 ((("x2", 0), U), ct (Var (("x1", 0), U)))) th end;
  fun resolve st = Exn.result (fn () =>
    Seq.list_of (Thm.biresolution NONE false [(false, Drule.reflexive_thm)] 1 st)) ();
  val T = A --> B --> R and U = B --> A --> R;
  val s = (fn x => lam (x $ Bound 1 $ Bound 0)) and t = (fn x => lam (x $ Bound 0 $ Bound 1));
  fun refl_s _ = Thm.reflexive (ct (s (Free ("x1", T))));

  (*the variable at the other type in the solved subgoal only: a result*)
  val st1 = state (T, s) (U, t) refl_s;
  val _ = \<^assert> (length (Term.add_vars (Thm.prop_of st1) []) = 2);
  val _ = \<^assert>
    (case resolve st1 of
      Exn.Res [th] =>
        (case Term.add_vars (Thm.full_prop_of th) [] of [(_, R')] => R' = R | _ => false)
    | _ => false);

  (*also in the conclusion: TYPE*)
  val st2 = state (T, s) (U, t) Thm.assume;
  val _ = \<^assert>
    (case resolve st2 of Exn.Exn (TYPE ("Variable has two distinct types", _, _)) => true | _ => false);

  (*different numbers of arguments: Fail*)
  val T3 = A --> R and U3 = A --> B --> R;
  val s3 = (fn x => lam (x $ Bound 1)) and t3 = (fn x => lam (x $ Bound 1 $ Bound 0));
  val st3 = state (T3, s3) (U3, t3) (fn _ => Thm.reflexive (ct (s3 (Free ("x1", T3)))));
  val _ = \<^assert> (case resolve st3 of Exn.Exn (Fail "mk_ff_list") => true | _ => false);
\<close>

end
