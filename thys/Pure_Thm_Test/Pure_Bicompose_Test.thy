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
  val comps = Bicompose_Test.comp_problems tab 3 states @
    Bicompose_Test.match_problems thy (take 300 (filter (fn r => Thm.nprems_of r = 0) (rules @ facts)));
  (*the reference: Thm.biresolution. Without the patches, the fix thm-quick-eres is emulated: it
    compares the first premise of a rule for elim-resolution with the assumptions of the subgoal
    only if no parameters follow them; otherwise, the rules that pass the fixed quick test are
    composed with tracing, which disables the quick test of Isabelle2026*)
  fun test_hyps Bi = not (Logic.is_all (Logic.strip_imp_concl (Term.strip_all_body Bi)));
  fun quick_ok Bi (eres_flg, r) =
    Term.could_unify (Thm.concl_of r, Logic.strip_assums_concl Bi) andalso
      (not eres_flg orelse
        (case Thm.prems_of r of
          A1 :: _ => exists (fn H => Term.could_unify (A1, H)) (Logic.strip_assums_hyp Bi)
        | [] => false) orelse (Thm.nprems_of r > 0 andalso not (test_hyps Bi)));
  val ctxt_trace = Config.put Pattern.unify_trace_failure true ctxt;
  fun biresolution match brules i st =
    if Test_System.patched then Thm.biresolution (SOME ctxt) match brules i st
    else
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
  (*Further inputs. (1) A schematic variable at two types: Isabelle admits such theorems, the
    build of HOL applies resolution and composition to them, and the theorems on the models
    exclude them. A variable is instantiated by the name of another one.*)
  fun clash th =
    let val vs = Term.add_vars (Thm.prop_of th) [] in
      vs |> get_first (fn (x, T) =>
        vs |> get_first (fn (y, U) =>
          if x <> y andalso T <> U
          then try (Thm.instantiate (TVars.empty, Vars.make1 ((y, U), Thm.global_cterm_of thy (Var (x, U))))) th
          else NONE))
    end;
  val clashing = map_filter clash (take 2000 rules);
  val clash_tab = Bicompose_Test.rule_table clashing;
  val clash_res = Bicompose_Test.res_problems tab 2 (take 600 clashing) @
    Bicompose_Test.res_problems clash_tab 2 (take 600 states @ take 300 clashing);
  val r15 = Bicompose_Test.compare "resolution, a variable at two types" 3 show
    (bires false false) (bires' false false) clash_res;
  val r16 = Bicompose_Test.compare "elim-resolution, a variable at two types" 3 show
    (bires false true) (bires' false true) (Bicompose_Test.eres_problems clashing 2 (take 400 states @ take 400 clashing));
  (*(2) composition where the names of the variables of the rule and the state are identified
    (as Metis does), also at different types*)
  val flags_inc = {flatten = true, match = false, incremented = true};
  val r17 = Bicompose_Test.compare "composition (incremented)" 3 show (comp flags_inc) (comp' flags_inc)
    (comps @ Bicompose_Test.comp_problems clash_tab 2 (take 600 states));
  (*(3) terms with \<beta>-redexes: a variable of function type is instantiated by an abstraction*)
  fun redex th =
    Term.add_vars (Thm.prop_of th) [] |> get_first (fn (v as ((x, i), T)) =>
      (case T of
        Type ("fun", [T1, _]) =>
          try (Thm.instantiate (TVars.empty, Vars.make1 (v,
            Thm.global_cterm_of thy (Abs ("r", T1, Var ((x ^ "r", i), T) $ Bound 0))))) th
      | _ => NONE));
  val redexes = map_filter redex (take 2000 rules);
  val r18 = Bicompose_Test.compare "resolution, terms with redexes" 3 show
    (bires false false) (bires' false false)
    (Bicompose_Test.res_problems tab 2 (take 400 redexes) @
      Bicompose_Test.res_problems (Bicompose_Test.rule_table redexes) 2 (take 600 states));
  (*(4) proof states with flex-flex pairs and with hypotheses*)
  val ff_states = res |> take 3000 |> maps (fn (r, i, st) =>
    (case Exn.result (Timeout.apply (seconds 2.0) (fn () =>
        Seq.list_of (Seq.take 2 (Thm.biresolution (SOME ctxt) false [(false, r)] i st)))) () of
      Exn.Res ths => filter (fn th => not (null (Thm.tpairs_of th)) andalso Thm.nprems_of th > 0) ths
    | Exn.Exn _ => [])) |> take 300;
  val hyp_states = take 300 goals |> map_filter (fn st =>
    try (fn () => Thm.implies_elim st (Thm.assume (Thm.cprem_of st 1))) ()) |> filter (fn th => Thm.nprems_of th > 0);
  val assumed = take 300 rules |> map_filter (fn th =>
    try (Thm.assume o Thm.global_cterm_of thy o Bicompose_Test.freeze o Thm.prop_of) th)
    |> filter (fn th => Thm.nprems_of th > 0);
  val r19 = Bicompose_Test.compare "resolution, states with flex-flex pairs" 3 show
    (bires false false) (bires' false false) (Bicompose_Test.res_problems tab 3 ff_states);
  val r20 = Bicompose_Test.compare "resolution, states with hypotheses" 3 show
    (bires false false) (bires' false false) (Bicompose_Test.res_problems tab 3 (hyp_states @ assumed));
  (*(5) names with bytes above 127 (the names of the models are ASCII strings in HOL; the generated
    code works on ML strings): variables and bound variables are renamed*)
  val nonascii = String.implode [Char.chr 206, Char.chr 177];
  fun rename_vars th =
    let val vs = take 3 (Term.add_vars (Thm.prop_of th) []) in
      try (Thm.instantiate (TVars.empty, Vars.make (map (fn v as ((x, i), T) =>
        (v, Thm.global_cterm_of thy (Var ((x ^ nonascii, i), T)))) vs))) th
    end;
  fun rename_bounds (Abs (a, T, b)) = Abs (a ^ nonascii, T, rename_bounds b)
    | rename_bounds (t $ u) = rename_bounds t $ rename_bounds u
    | rename_bounds t = t;
  val na_rules = map_filter rename_vars (take 1000 rules);
  val na_states = map_filter (fn th => try (Thm.renamed_prop (rename_bounds (Thm.prop_of th))) th)
    (take 500 states @ take 500 goals);
  val r21 = Bicompose_Test.compare "resolution, names with bytes above 127" 3 show
    (bires false false) (bires' false false)
    (Bicompose_Test.res_problems (Bicompose_Test.rule_table na_rules) 2 (na_states @ take 300 states) @
      Bicompose_Test.res_problems tab 2 (take 300 na_states));
  val r22 = Bicompose_Test.compare "elim-resolution, names with bytes above 127" 3 show
    (bires false true) (bires' false true) (Bicompose_Test.eres_problems na_rules 2 (take 500 na_states));
  (*(6) whole sequences, where they are short*)
  val r23 = Bicompose_Test.compare "resolution (up to 30 results)" 30 show
    (bires false false) (bires' false false) (take 1500 res);
  val rs = [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20,
    r21, r22, r23];
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
  val _ = writeln ("Elim-resolution, parameters after assumptions: the reference skips rules with results on " ^
    string_of_int (length skipped) ^ " of " ^ string_of_int (length ieres) ^ " problems");
  (*with the patches, no rule with results is skipped*)
  val _ = \<^assert> (not Test_System.patched orelse null skipped);
  (*the tests of error cases have exceptions only*)
  val _ = Bicompose_Test.check_with
    ["too many subgoals", "elim-resolution without premises", "elim-resolution without lifting",
      "subgoal out of range", "subgoal 0"] rs;
end
\<close>

end
