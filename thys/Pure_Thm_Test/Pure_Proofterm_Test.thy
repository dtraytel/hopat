section \<open>Testing the Generated Code against \<open>Proofterm\<close>\<close>

theory Pure_Proofterm_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated proof functions are compared with \<open>Proofterm.lift_proof\<close>,
  \<open>Proofterm.bicompose_proof\<close> and \<open>Proofterm.map_proof_terms\<close> on the problems of
  \<^theory_text>\<open>Pure_Bicompose_Test_Base\<close>: lifting over the subgoals of the resolution problems,
  and composition with the results of the model's \<open>bicompose_aux\<close> for resolution,
  elim-resolution and composition. The proofs of the rules and proof states are synthetic: they
  contain all kinds of proofs, with the propositions, variables and type variables of the
  theorems, so that lifting and normalisation have something to do. The tight proof functions
  are compared with those of \<open>ZTerm\<close> likewise; lifting is compared with \<open>ZTerm.lift_proof\<close>
  with fixes \<open>zterm-lift-hyps\<close> and \<open>zterm-lift-frees\<close> applied to its result, and the report
  also counts the problems on which Isabelle2026 differs from the fixes. Composition is compared
  with a copy of \<open>ZTerm.bicompose_proof\<close> with fixes \<open>zterm-flatten\<close>, \<open>zterm-asm\<close> and
  \<open>zterm-norm-ofclass\<close>, also for elim-resolution with unlifted rules, and the report counts the
  problems on which Isabelle2026 differs from it. The conversion of terms (fix
  \<open>zterm-ofclass\<close>) only differs on terms that are not proper class membership propositions.
\<close>


ML \<open>
local
  val thy = \<^theory>;
  val ctxt = \<^context> |> Context_Position.set_visible false;
  val rules = Bicompose_Test.theorems thy 1000;
  val facts = Global_Theory.all_thms_of thy true |> map (Thm.transfer thy o snd) |> take 2000;
  val tab = Bicompose_Test.rule_table (rules @ facts);
  val states = take 300 rules;
  val goals = map (Bicompose_Test.goal_state thy) (take 300 rules);
  val res = Bicompose_Test.res_problems tab 2 (states @ goals);
  val eres = Bicompose_Test.eres_problems rules 1 (states @ goals);
  val comps = Bicompose_Test.comp_problems tab 2 states;
  val show = Bicompose_Test.show_problem;
  val r1 = Proofterm_Test.compare "lift_proof" show Proofterm_Test.lift_orig Proofterm_Test.lift_gen res;
  fun lifted_args flags eres_flg (r, i, st) =
    Proofterm_Test.compose_args ctxt flags true
      (eres_flg, Thm.lift_rule (Thm.cprem_of st i) r, Thm.nprems_of r) i st;
  fun plain_args flags (r, i, st) =
    Proofterm_Test.compose_args ctxt flags false (false, r, 0) i st;
  val bflags = {flatten = true, match = false, incremented = true};
  val cflags1 = {flatten = true, match = false, incremented = false};
  val cflags2 = {flatten = false, match = true, incremented = false};
  val bres = maps (lifted_args bflags false) res;
  val beres = maps (lifted_args bflags true) eres;
  val bcomp1 = maps (plain_args cflags1) comps;
  val bcomp2 = maps (plain_args cflags2) comps;
  val r2 = Proofterm_Test.compare "bicompose_proof (resolution)" Proofterm_Test.show_comp
    Proofterm_Test.comp_orig Proofterm_Test.comp_gen bres;
  val r3 = Proofterm_Test.compare "bicompose_proof (elim-resolution)" Proofterm_Test.show_comp
    Proofterm_Test.comp_orig Proofterm_Test.comp_gen beres;
  val r4 = Proofterm_Test.compare "bicompose_proof (composition)" Proofterm_Test.show_comp
    Proofterm_Test.comp_orig Proofterm_Test.comp_gen bcomp1;
  val r5 = Proofterm_Test.compare "bicompose_proof (composition, no flattening)"
    Proofterm_Test.show_comp Proofterm_Test.comp_orig Proofterm_Test.comp_gen bcomp2;
  val ren = map (fn (r, _, _) => (Logic.incr_indexes ([], 1), Proofterm_Test.synth r)) res;
  val r6 = Proofterm_Test.compare "map_proof_terms" (K "") Proofterm_Test.ren_orig
    Proofterm_Test.ren_gen ren;
  val z0 = Proofterm_Test.zcompare "lift_proof (tight proofs, Isabelle2026 vs. fixes zterm-lift-hyps/frees)" show
    Proofterm_Test.zlift_orig Proofterm_Test.zlift_ref res;
  val z1 = Proofterm_Test.zcompare "lift_proof (tight proofs, with fixes zterm-lift-hyps/frees)" show
    Proofterm_Test.zlift_ref Proofterm_Test.zlift_gen res;
  fun zargs flags eres_flg (r, i, st) =
    let val orule = Thm.lift_rule (Thm.cprem_of st i) r in
      map (Proofterm_Test.zcomp_args orule st)
        (Proofterm_Test.compose_args ctxt flags true (eres_flg, orule, Thm.nprems_of r) i st)
    end;
  fun zplain flags (r, i, st) =
    map (Proofterm_Test.zcomp_args r st) (Proofterm_Test.compose_args ctxt flags false (false, r, 0) i st);
  val zres = maps (zargs bflags false) res;
  val zeres = maps (zargs bflags true) eres;
  val zcomps = maps (zplain cflags1) comps;
  fun zplain_eres flags (r, i, st) =
    map (Proofterm_Test.zcomp_args r st)
      (Proofterm_Test.compose_args ctxt flags false (true, r, Thm.nprems_of r) i st);
  (*elim-resolution with unlifted rules whose first premise has fewer assumptions than the
    subgoal (fix zterm-asm)*)
  val sctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt;
  fun rd s = Syntax.read_prop sctxt s;
  val unl_rules = map (Skip_Proof.make_thm thy o rd)
    ["((PROP ?A \<Longrightarrow> PROP ?B) \<Longrightarrow> PROP ?Q) \<Longrightarrow> PROP ?R",
     "(PROP ?A \<Longrightarrow> PROP ?Q) \<Longrightarrow> PROP ?R",
     "((PROP ?A \<Longrightarrow> PROP ?B \<Longrightarrow> PROP ?C) \<Longrightarrow> PROP ?Q) \<Longrightarrow> PROP ?R",
     "(\<And>x::'a. PROP ?P x \<Longrightarrow> PROP ?Q x) \<Longrightarrow> PROP ?R"];
  val unl_states = map (Goal.init o Thm.cterm_of ctxt o rd)
    ["PROP h1 \<Longrightarrow> PROP h2 \<Longrightarrow> PROP k",
     "(PROP a \<Longrightarrow> PROP b) \<Longrightarrow> PROP h2 \<Longrightarrow> PROP h3 \<Longrightarrow> PROP k",
     "(PROP a \<Longrightarrow> PROP b \<Longrightarrow> PROP c) \<Longrightarrow> PROP h2 \<Longrightarrow> PROP k",
     "(\<And>x::'b. PROP p x \<Longrightarrow> PROP q x) \<Longrightarrow> PROP h \<Longrightarrow> PROP k"];
  val unl = maps (fn r => map (fn st => (r, 1, st)) unl_states) unl_rules;
  val zeres_plain = maps (zplain_eres cflags1) (eres @ unl);
  val z5 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, Isabelle2026 vs. fixes zterm-flatten/asm/norm-ofclass)"
    Proofterm_Test.show_zcomp Proofterm_Test.zcomp_orig Proofterm_Test.zcomp_ref
    (zres @ zeres @ zcomps @ zeres_plain);
  val z2 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, resolution, with fixes zterm-flatten/asm/norm-ofclass)"
    Proofterm_Test.show_zcomp Proofterm_Test.zcomp_ref Proofterm_Test.zcomp_gen zres;
  val z3 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, elim-resolution, with fixes zterm-flatten/asm/norm-ofclass)"
    Proofterm_Test.show_zcomp Proofterm_Test.zcomp_ref Proofterm_Test.zcomp_gen zeres;
  val z4 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, composition, with fixes zterm-flatten/asm/norm-ofclass)"
    Proofterm_Test.show_zcomp Proofterm_Test.zcomp_ref Proofterm_Test.zcomp_gen zcomps;
  val z7 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, elim-resolution with unlifted rules, with fixes zterm-flatten/asm/norm-ofclass)"
    Proofterm_Test.show_zcomp Proofterm_Test.zcomp_ref Proofterm_Test.zcomp_gen zeres_plain;
  val z6 = Proofterm_Test.zcompare "renaming of tight proofs (fix zterm-rename)" (K "")
    Proofterm_Test.zren_orig Proofterm_Test.zren_gen
    (maps (fn (r, _, _) => map (fn smax => (Proofterm_Test.zren_tab r, smax, Proofterm_Test.zsynth r))
      [~1, 0, 1]) res);
  val rs = [r1, r2, r3, r4, r5, r6, z1, z2, z3, z4, z6, z7];
in
  val _ = writeln (cat_lines (map Proofterm_Test.report (z0 :: z5 :: rs)));
  val _ = Proofterm_Test.check rs;
end
\<close>

end
