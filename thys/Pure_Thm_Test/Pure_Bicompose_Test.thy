section \<open>Testing the Generated Code against \<open>Thm.bicompose_aux\<close>\<close>

theory Pure_Bicompose_Test
  imports Pure_Bicompose_Test_Base
begin

text \<open>The comparison on the problems of the infrastructure of
  \<^theory_text>\<open>Pure_Bicompose_Test_Base\<close>.\<close>

ML \<open>
local
  val thy = \<^theory>;
  val ctxt = \<^context> |> Context_Position.set_visible false;
  val rules = Bicompose_Test.theorems thy 3000;
  val facts = Global_Theory.all_thms_of thy true |> map (Thm.transfer thy o snd) |> take 6000;
  val tab = Bicompose_Test.rule_table (rules @ facts);
  val states = take 1500 rules;
  val goals = map (Bicompose_Test.goal_state thy) (take 1500 rules);
  val res = Bicompose_Test.res_problems tab 3 (states @ goals);
  val eres = Bicompose_Test.eres_problems rules 2 (states @ goals);
  val comps = Bicompose_Test.comp_problems tab 3 states;
  (*the reference: Thm.biresolution with the fix thm-quick-eres, which compares the first
    premise of a rule for elim-resolution with the assumptions of the subgoal only if no
    parameters follow them; otherwise, the rules that pass the fixed quick test are composed
    with tracing, which disables the quick test of Isabelle2026*)
  fun test_hyps Bi = not (Logic.is_all (Logic.strip_imp_concl (Term.strip_all_body Bi)));
  fun quick_ok Bi (eres_flg, r) =
    Term.could_unify (Thm.concl_of r, Logic.strip_assums_concl Bi) andalso
      (not eres_flg orelse
        (case Thm.prems_of r of
          A1 :: _ => exists (fn H => Term.could_unify (A1, H)) (Logic.strip_assums_hyp Bi)
        | [] => false) orelse (Thm.nprems_of r > 0 andalso not (test_hyps Bi)));
  val ctxt_trace = Config.put Pattern.unify_trace_failure true ctxt;
  fun biresolution match brules i st =
    (case try Logic.nth_prem (i, Thm.prop_of st) of
      SOME Bi =>
        if test_hyps Bi then Thm.biresolution (SOME ctxt) match brules i st
        else Thm.biresolution (SOME ctxt_trace) match (filter (quick_ok Bi) brules) i st
    | NONE => Thm.biresolution (SOME ctxt) match brules i st);
  fun bires match eres_flg (r, i, st) = biresolution match [(eres_flg, r)] i st;
  fun bires' match eres_flg (r, i, st) = Bicompose_Test.biresolution ctxt match [(eres_flg, r)] i st;
  fun comp flags (r, i, st) = Thm.bicompose (SOME ctxt) flags (false, r, 0) i st;
  fun comp' flags (r, i, st) = Bicompose_Test.bicompose ctxt flags (false, r, 0) i st;
  val flags1 = {flatten = true, match = false, incremented = false};
  val flags2 = {flatten = false, match = true, incremented = false};
  val show = Bicompose_Test.show_problem;
  val r1 = Bicompose_Test.compare "resolution" 3 show (bires false false) (bires' false false) res;
  val r2 = Bicompose_Test.compare "resolution (match)" 3 show (bires true false) (bires' true false) res;
  val r3 = Bicompose_Test.compare "elim-resolution" 3 show (bires false true) (bires' false true) eres;
  val r4 = Bicompose_Test.compare "composition" 3 show (comp flags1) (comp' flags1) comps;
  val r5 = Bicompose_Test.compare "composition (match, no flattening)" 3 show
    (comp flags2) (comp' flags2) comps;
  (*exceptions: too few premises of the rule, elim-resolution with a rule without premises,
    and elim-resolution without lifting, where the other premises of the rule may have too
    few assumptions to delete*)
  fun gen arg flags (r, i, st) = Thm.bicompose (SOME ctxt) flags (arg r) i st;
  fun gen' arg flags (r, i, st) = Bicompose_Test.bicompose ctxt flags (arg r) i st;
  val flags3 = {flatten = true, match = false, incremented = false};
  fun too_many r = (false, r, Thm.nprems_of r + 1);
  fun no_prems r = (true, r, 0);
  fun all_prems r = (true, r, Thm.nprems_of r);
  val r6 = Bicompose_Test.compare "too many subgoals" 3 show
    (gen too_many flags3) (gen' too_many flags3) (take 300 comps);
  val r7 = Bicompose_Test.compare "elim-resolution without premises" 3 show
    (gen no_prems flags3) (gen' no_prems flags3) (take 300 comps);
  val r8 = Bicompose_Test.compare "elim-resolution without lifting" 3 show
    (gen all_prems flags3) (gen' all_prems flags3) (take 3000 eres);
  (*lifting, lists of rules, and subgoals out of range*)
  fun lift (r, i, st) = Seq.single (Thm.lift_rule (Thm.cprem_of st i) r);
  val r9 = Bicompose_Test.compare "lift_rule" 1 show lift Bicompose_Test.lift_rule res;
  val multi = Bicompose_Test.multi_problems rules res;
  fun mbires match (brules, i, st) = biresolution match brules i st;
  fun mbires' match (brules, i, st) = Bicompose_Test.biresolution ctxt match brules i st;
  val r10 = Bicompose_Test.compare "biresolution with lists of rules" 5 Bicompose_Test.show_multi
    (mbires false) (mbires' false) multi;
  val r11 = Bicompose_Test.compare "biresolution with lists of rules (match)" 5
    Bicompose_Test.show_multi (mbires true) (mbires' true) multi;
  fun out_of_range k (r, i, st) = (r, if k = 0 then 0 else Thm.nprems_of st + k, st);
  val r12 = Bicompose_Test.compare "subgoal out of range" 3 show
    (bires false false o out_of_range 1) (bires' false false o out_of_range 1) (take 300 res);
  val r13 = Bicompose_Test.compare "subgoal 0" 3 show
    (bires false false o out_of_range 0) (bires' false false o out_of_range 0) (take 300 res);
  (*elim-resolution on subgoals with a parameter after the first assumption, and on subgoals
    (\<And>u. A1) \<Longrightarrow> (\<And>u. C) with the rules A1 \<Longrightarrow> \<dots> \<Longrightarrow> C, where the assumption is the rest of the
    lifted premise (Isabelle2026 skips the rule)*)
  fun all_u t = Logic.all_const \<^typ>\<open>bool\<close> $ Abs ("u", \<^typ>\<open>bool\<close>, t);
  fun quantified r =
    (case Thm.prems_of r of
      A1 :: _ =>
        try (Goal.init o Thm.global_cterm_of thy o Bicompose_Test.freeze)
          (Logic.mk_implies (all_u A1, all_u (Thm.concl_of r)))
        |> Option.map (fn st => (r, 1, st))
    | [] => NONE);
  fun interleave th =
    (case Thm.prems_of th of
      H1 :: H2 :: Hs =>
        try (Goal.init o Thm.global_cterm_of thy o Bicompose_Test.freeze)
          (Logic.mk_implies (H1, all_u (Logic.list_implies (H2 :: Hs, Thm.concl_of th))))
    | _ => NONE);
  val ieres = Bicompose_Test.eres_problems rules 2 (map_filter interleave (take 1500 rules)) @
    map_filter quantified (take 1500 rules);
  val r14 = Bicompose_Test.compare "elim-resolution, parameters after assumptions" 3 show
    (bires false true) (bires' false true) ieres;
  val rs = [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14];
  (*the problems where Thm.biresolution of Isabelle2026 skips a rule with results*)
  fun nres f =
    (case Exn.result (Timeout.apply (seconds 5.0) (fn () => length (Seq.list_of (Seq.take 3 (f ()))))) () of
      Exn.Res n => n
    | Exn.Exn _ => 0);
  val skipped = ieres |> filter (fn (r, i, st) =>
    nres (fn () => Thm.biresolution (SOME ctxt) false [(true, r)] i st) <
    nres (fn () => bires' false true (r, i, st)));
in
  val _ = writeln (cat_lines (map Bicompose_Test.report rs));
  val _ = writeln ("Elim-resolution, parameters after assumptions: Isabelle2026 skips rules with results on " ^
    string_of_int (length skipped) ^ " of " ^ string_of_int (length ieres) ^ " problems");
  val _ = Bicompose_Test.check rs;
end
\<close>

end
