section \<open>Testing the Generated Code against \<open>Thm.bicompose_aux\<close>\<close>

theory Pure_Bicompose_Test
  imports Pure_Bicompose_Test_Base
begin

text \<open>The comparison on the problems of the infrastructure of
  \<^theory>\<open>Pure_Thm.Pure_Bicompose_Test_Base\<close>.\<close>

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
  fun bires match eres_flg (r, i, st) = Thm.biresolution (SOME ctxt) match [(eres_flg, r)] i st;
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
  fun mbires match (brules, i, st) = Thm.biresolution (SOME ctxt) match brules i st;
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
  val rs = [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13];
in
  val _ = writeln (cat_lines (map Bicompose_Test.report rs));
  val _ = Bicompose_Test.check rs;
end
\<close>

end
