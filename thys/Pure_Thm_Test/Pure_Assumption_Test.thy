section \<open>Testing the Generated Code against \<open>Thm.assumption\<close>, \<open>Thm.eq_assumption\<close> and
  \<open>Thm.flexflex_rule\<close>\<close>

theory Pure_Assumption_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated code of theory \<^theory_text>\<open>Pure_Assumption\<close> is compared with
  \<open>Thm.assumption\<close>, \<open>Thm.eq_assumption\<close> and \<open>Thm.flexflex_rule\<close>: the logical content of the
  new theorems (as in \<^theory_text>\<open>Pure_Bicompose_Test\<close>), and their classic and tight
  proofs, from the synthetic proofs of \<^theory_text>\<open>Pure_Proofterm_Test_Base\<close>, with
  \<open>Proofterm.assumption_proof\<close>, \<open>Proofterm.norm_proof_remove_types\<close>,
  \<open>ZTerm.assumption_proof\<close> and \<open>ZTerm.norm_proof\<close>. The proof states are the theorems of HOL
  with their premises as subgoals (the subgoals of elimination rules are solved by assumption
  with instantiations), the theorems as the only subgoal of a proof state, the results of
  resolution, and synthetic subgoals whose conclusion is one of their assumptions, also
  up to \<open>\<eta>\<close>-expansion, or a variable that an implication instantiates. The references
  for the proofs are those of the functions with the fixes of \<open>patches/18-thm-assumption.patch\<close>
  (and \<open>09-zterm-norm-ofclass.patch\<close>). The theorems for \<open>flexflex_rule\<close> are the results of resolution and
  proof by assumption, among them those with flex-flex pairs from synthetic problems, also
  instantiated so that their pairs are no longer flex-flex.
\<close>

ML \<open>
structure Assumption_Test =
struct

structure G = Bicompose_Generated;

fun result_of_rep th' : Bicompose_Test.result = (G.th_prop th', G.th_tpairs th', G.th_maxidx th');


(* the wrapper of bicompose_wrapper.ML, without the construction of theorems *)

fun assumption_seq ctxt i state =
  let
    val context = Context.Proof ctxt;
    fun eval r = Bicompose_Test.run context (state, state) r;
    val s0 = eval (G.assumption i (Bicompose_Test.rep_of state));
    fun to_seq s =
      Seq.make (fn () =>
        (case eval (G.apull (Bicompose_Test.ops context) s) of
          NONE => NONE
        | SOME (res, s') => SOME (res, to_seq s')));
  in (G.aseq_ctx s0, to_seq s0) end;

fun assumption ctxt i state =
  Seq.map (fn G.ARes (_, _, th') => result_of_rep th') (#2 (assumption_seq ctxt i state));

fun eq_assumption ctxt i state =
  let
    val (_, th') =
      Bicompose_Test.run (Context.Proof ctxt) (state, state)
        (G.eq_assumption i (Bicompose_Test.rep_of state));
  in Seq.single (result_of_rep th') end;

fun flexflex_ops context =
  G.BOps
    (fn env => fn tus =>
      SOME ([], G.Ok (Seq.map (rpair []) (Unify.smash_unifiers context tus env))),
     fn xq => SOME ([], G.Ok (Seq.pull xq)),
     Name.variant_list []);

fun flexflex_seq ctxt th =
  let
    val context = Context.Proof ctxt;
    fun eval r = Bicompose_Test.run context (th, th) r;
    val ops = flexflex_ops context;
    fun smash (env, _) = SOME ([], G.Ok env);
    val rep = Bicompose_Test.rep_of th;
    fun to_seq s =
      Seq.make (fn () =>
        (case eval (G.fpull ops smash rep s) of
          NONE => NONE
        | SOME (x, s') => SOME (x, to_seq s')));
  in to_seq (eval (G.flexflex_rule ops rep)) end;

fun flexflex_rule ctxt th = Seq.map (result_of_rep o snd) (flexflex_seq ctxt th);


(* proofs *)

fun take_list n xq =
  (case Exn.result (Timeout.apply (seconds 5.0) (fn () => Seq.list_of (Seq.take n xq))) () of
    Exn.Res xs => xs
  | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else []);

(*the arguments of the proofs of the first results of Thm.assumption*)
fun assumption_args ctxt (i, state) =
  (case Exn.result (fn () => assumption_seq ctxt i state) () of
    Exn.Res (actx, xq) =>
      let val (_, Bs, Bi, _) = Thm.dest_state (state, i) in
        take_list 3 xq |> map (fn res => (state, actx, res, Bs, Bi))
      end
  | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else []);

fun show_asm (state, _, G.ARes (env, n, _), _, _) =
  \<^make_string> (Thm.prop_of state, Envir.maxidx_of env, n);

(*Proofterm.assumption_proof in Thm.assumption with fix thm-assumption: the proof of the subgoal
  follows the subgoal before normalisation*)
fun asm_orig (state, _, G.ARes (env, n, _), Bs, Bi) =
  let val normt = Envir.norm_term env in
    ([], Proofterm.assumption_proof (map normt Bs) Bi n (Proofterm_Test.synth state)
      |> not (Envir.is_empty env) ? Proofterm.norm_proof_remove_types env)
  end;
fun asm_gen (state, actx, res, _, _) =
  Proofterm_Test.run (G.ares_proof actx res (Proofterm_Test.synth state));

(*ZTerm.assumption_proof with fixes thm-assumption and zterm-norm-ofclass: the proof of the
  subgoal strips as many assumptions from the normalised subgoal as Logic.assum_problems from the
  subgoal before normalisation; the normalisation of terms also normalises the types of class
  memberships (as in Proofterm_Test.zcomp_ref)*)
fun zasm_ref thy env Bs Bi n visible prf =
  let
    val {zterm, ...} = ZTerm.zterm_cache thy;
    val normt =
      zterm #> ZTerm.norm_term thy env #> ZTerm.map_types (ZTerm.norm_type thy (Envir.type_env env));
  in
    ZTerm.ZAbsps (map normt Bs)
      (ZTerm.ZAppps (prf, map ZBoundp (length Bs - 1 downto 0) @
        [Proofterm_Test.zmk_asm_prf (normt Bi) n (length (#2 (Logic.assum_problems (~1, Bi))))]))
    |> ZTerm.norm_proof thy env visible
  end;

fun zasm_orig (state, _, G.ARes (env, n, _), Bs, Bi) =
  ([], zasm_ref (Thm.theory_of_thm state) env Bs Bi n [Thm.full_prop_of state]
    (Proofterm_Test.zsynth state));
fun zasm_gen (state, actx, res, _, _) =
  Proofterm_Test.zrun (G.ares_zproof (Proofterm_Test.ztypargs (Thm.theory_of_thm state))
    (Bicompose_Test.rep_of state) actx res (Proofterm_Test.zsynth state));

(*the arguments of the proofs of Thm.eq_assumption*)
fun eq_assumption_args ctxt (i, state) =
  (case Exn.result (fn () =>
      Bicompose_Test.run (Context.Proof ctxt) (state, state)
        (G.eq_assumption i (Bicompose_Test.rep_of state))) () of
    Exn.Res (n, _) =>
      let val (_, Bs, Bi, _) = Thm.dest_state (state, i) in [(state, Bs, Bi, n)] end
  | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else []);

fun show_eq (state, _, _, n) = \<^make_string> (Thm.prop_of state, n);

fun eq_orig (state, Bs, Bi, n) =
  ([], Proofterm.assumption_proof Bs Bi n (Proofterm_Test.synth state));
fun eq_gen (state, Bs, Bi, n) = ([], G.assumption_proof Bs Bi n (Proofterm_Test.synth state));

fun zeq_orig (state, Bs, Bi, n) =
  ([], zasm_ref (Thm.theory_of_thm state) Envir.init Bs Bi n [] (Proofterm_Test.zsynth state));
fun zeq_gen (state, Bs, Bi, n) =
  Proofterm_Test.zrun (G.eq_assumption_zproof (Proofterm_Test.ztypargs (Thm.theory_of_thm state))
    Bs Bi n (Proofterm_Test.zsynth state));

(*the arguments of the proofs of the first results of Thm.flexflex_rule with a non-empty
  environment or trivial flex-flex pairs (fix thm-flexflex-trivial)*)
fun flexflex_args ctxt th =
  take_list 3 (flexflex_seq ctxt th)
  |> filter_out (fn (env, _) => Envir.is_empty env andalso not (exists (op aconv) (Thm.tpairs_of th)))
  |> map (fn (env, _) => (th, env));

fun show_ff (th, env) = \<^make_string> (Thm.prop_of th, Thm.tpairs_of th, Envir.maxidx_of env);

fun ff_orig (th, env) = ([], Proofterm.norm_proof_remove_types env (Proofterm_Test.synth th));
fun ff_gen (th, env) = Proofterm_Test.run (G.norm_proof_remove_types env (Proofterm_Test.synth th));

fun zff_orig (th, env) =
  ([], ZTerm.norm_proof (Thm.theory_of_thm th) env [Thm.full_prop_of th] (Proofterm_Test.zsynth th));
fun zff_gen (th, env) =
  Proofterm_Test.zrun (G.flexflex_zproof (Proofterm_Test.ztypargs (Thm.theory_of_thm th))
    (Bicompose_Test.rep_of th) env (Proofterm_Test.zsynth th));


(* test data *)

(*instances of a theorem whose first flex-flex pair is no longer flex-flex: the head of one of
  its sides is replaced by a constant function or by a projection*)
fun unflex thy th =
  (case Thm.tpairs_of th of
    (t, _) :: _ =>
      (case Term.head_of t of
        Var (xi, T) =>
          let
            val (Ts, U) = strip_type T;
            val proj =
              (case find_index (fn S => S = U) Ts of
                ~1 => []
              | k => [fold_rev (fn S => fn u => Abs ("x", S, u)) Ts (Bound (length Ts - 1 - k))]);
            val const = [fold_rev (fn S => fn u => Abs ("x", S, u)) Ts (Free ("c", U))];
          in
            (proj @ const) |> map_filter (fn u =>
              try (Thm.instantiate (TVars.empty, Vars.make1 ((xi, T), Thm.global_cterm_of thy u))) th)
          end
      | _ => [])
  | [] => []);

end;
\<close>

ML \<open>
local
  val thy = \<^theory>;
  val ctxt = \<^context> |> Context_Position.set_visible false;
  fun bcompare name n show f g xs =
    let val r = Bicompose_Test.compare name n show f g xs
    in tracing (Bicompose_Test.report r); r end;
  fun timed cmp =
    let val (t, r) = Timing.timing cmp ()
    in tracing (Proofterm_Test.report r ^ "; time " ^ Time.toString (#elapsed t) ^ "s"); r end;
  val sctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt;
  fun rd s = Syntax.read_prop sctxt s;
  val rules = Bicompose_Test.theorems thy 600;
  val facts = Global_Theory.all_thms_of thy true |> map (Thm.transfer thy o snd) |> take 1200;
  val tab = Bicompose_Test.rule_table (rules @ facts);
  val show = Bicompose_Test.show_problem;
  fun subgoals st = map (fn i => (i, st)) (1 upto Thm.nprems_of st);
  (*proof states: the rules, the rules as the only subgoal, the first results of resolution*)
  val inits = map (Goal.init o Thm.cprop_of) (take 100 rules);
  val res = Bicompose_Test.res_problems tab 1 (take 200 rules);
  val resolvents =
    res |> maps (fn (r, i, st) =>
      Assumption_Test.take_list 2 (Thm.biresolution (SOME ctxt) false [(false, r)] i st));
  (*synthetic subgoals whose conclusion is one of their assumptions, also eta-expanded, and
    subgoals whose conclusion is a variable that an implication instantiates*)
  fun synth_states r =
    (case Thm.prems_of r of
      A :: Bs =>
        [Logic.mk_implies (A, A), Logic.list_implies (Bs @ [Envir.eta_long [] A], A),
          Logic.list_implies (A :: Bs, Envir.eta_long [] A),
          Logic.list_implies ([Thm.prop_of r, A], Var (("P", Thm.maxidx_of r + 1), propT))]
        |> map_filter (try (Goal.init o Thm.global_cterm_of thy))
    | [] => []);
  val synths = maps synth_states (take 300 rules);
  val asm_probs =
    maps subgoals (take 600 rules) @ map (pair 1) inits @
    maps subgoals (take 400 resolvents) @ maps subgoals synths;
  val out_of_range =
    maps (fn st => [(0, st), (Thm.nprems_of st + 1, st)]) (take 100 rules);
  fun mk (i, st) = (Thm.reflexive (Thm.global_cterm_of thy Term.dummy_prop), i, st);
  fun asm (_, i, st) = Thm.assumption (SOME ctxt) i st;
  fun asm' (_, i, st) = Assumption_Test.assumption ctxt i st;
  fun eq (_, i, st) = Seq.single (Thm.eq_assumption i st);
  fun eq' (_, i, st) = Assumption_Test.eq_assumption ctxt i st;
  val probs = map mk (asm_probs @ out_of_range);
  val r1 = bcompare "assumption" 3 show asm asm' probs;
  val r2 = bcompare "eq_assumption" 1 show eq eq' probs;
  (*theorems with flex-flex pairs*)
  val ff_rules = map (Skip_Proof.make_thm thy o rd)
    ["PROP ?P ?x", "PROP ?P (?f ?x)", "PROP ?P (?f ?x) \<Longrightarrow> PROP ?Q", "(\<And>z. PROP ?P z) \<Longrightarrow> PROP ?P ?y",
     "PROP ?P (\<lambda>z. ?f z ?x)"];
  val ff_states = map (Goal.init o Thm.cterm_of ctxt o rd)
    ["PROP ?Q (a::'a)", "\<And>y::'a. PROP ?Q y", "PROP ?Q (?g (b::'b))", "PROP ?Q a \<Longrightarrow> PROP ?R",
     "\<And>y::'a. PROP ?Q y (?h y) \<Longrightarrow> PROP ?R (?h y)", "PROP ?Q (\<lambda>z::'a. ?g z)"];
  val ff_results =
    ff_rules |> maps (fn r => ff_states |> maps (fn st =>
      Assumption_Test.take_list 3 (Thm.biresolution (SOME ctxt) false [(false, r)] 1 st)));
  val asm_results =
    take 800 asm_probs |> maps (fn (i, st) =>
      Assumption_Test.take_list 2 (Thm.assumption (SOME ctxt) i st));
  val ff_thms0 = ff_results @ resolvents @ asm_results;
  val ff_thms =
    ff_thms0 @ maps (Assumption_Test.unflex thy) (filter (not o null o Thm.tpairs_of) ff_thms0);
  fun ff (_, _, th) = Thm.flexflex_rule (SOME ctxt) th;
  fun ff' (_, _, th) = Assumption_Test.flexflex_rule ctxt th;
  val ff_probs = map (fn th => mk (0, th)) ff_thms;
  val r3 = bcompare "flexflex_rule" 3 show ff ff' ff_probs;
  (*fix thm-flexflex-trivial: the trivial pairs of a theorem are removed also by the empty unifier;
    the pairs are made trivial by instantiating both heads of the first pair with the same constant
    function*)
  fun trivialize th =
    (case Thm.tpairs_of th of
      (t, u) :: _ =>
        (case (Term.head_of t, Term.head_of u) of
          (Var (xi, T), Var (yi, U)) =>
            if xi = yi orelse body_type T <> body_type U then NONE
            else
              let
                fun const T = fold_rev (fn S => fn b => Abs ("x", S, b)) (binder_types T)
                  (Free ("c", body_type T));
              in
                try (Thm.instantiate_beta (TVars.empty, Vars.make
                  [((xi, T), Thm.global_cterm_of thy (const T)), ((yi, U), Thm.global_cterm_of thy (const U))])) th
              end
        | _ => NONE)
    | [] => NONE);
  val trivials = map_filter trivialize ff_thms0
    |> filter (fn th => exists (op aconv) (Thm.tpairs_of th));
  val _ = \<^assert> (not (null trivials));
  val _ = trivials |> List.app (fn th =>
    \<^assert> (forall (fn (t, u, _) => not (exists (op aconv) u))
      (Seq.list_of (Assumption_Test.flexflex_rule ctxt th))));
  val _ = tracing ("flexflex_rule: " ^ string_of_int (length trivials) ^
    " theorems with trivial pairs, none kept");
  val with_tpairs = length (filter (not o null o Thm.tpairs_of) ff_thms);
  (*proofs*)
  val aargs = maps (Assumption_Test.assumption_args ctxt) asm_probs;
  val eargs = maps (Assumption_Test.eq_assumption_args ctxt) asm_probs;
  val fargs = maps (Assumption_Test.flexflex_args ctxt) (ff_thms @ trivials);
  val p1 = timed (fn () => Proofterm_Test.compare "assumption (classic proofs)" Assumption_Test.show_asm
    Assumption_Test.asm_orig Assumption_Test.asm_gen aargs);
  val p2 = timed (fn () => Proofterm_Test.zcompare "assumption (tight proofs)" Assumption_Test.show_asm
    Assumption_Test.zasm_orig Assumption_Test.zasm_gen aargs);
  val p3 = timed (fn () => Proofterm_Test.compare "eq_assumption (classic proofs)" Assumption_Test.show_eq
    Assumption_Test.eq_orig Assumption_Test.eq_gen eargs);
  val p4 = timed (fn () => Proofterm_Test.zcompare "eq_assumption (tight proofs)" Assumption_Test.show_eq
    Assumption_Test.zeq_orig Assumption_Test.zeq_gen eargs);
  val p5 = timed (fn () => Proofterm_Test.compare "flexflex_rule (classic proofs)" Assumption_Test.show_ff
    Assumption_Test.ff_orig Assumption_Test.ff_gen fargs);
  val p6 = timed (fn () => Proofterm_Test.zcompare "flexflex_rule (tight proofs)" Assumption_Test.show_ff
    Assumption_Test.zff_orig Assumption_Test.zff_gen fargs);
in
  val _ = writeln (cat_lines (map Bicompose_Test.report [r1, r2, r3]));
  val _ = writeln ("flexflex_rule: " ^ string_of_int with_tpairs ^ " theorems with flex-flex pairs");
  val _ = writeln (cat_lines (map Proofterm_Test.report [p1, p2, p3, p4, p5, p6]));
  val _ = Bicompose_Test.check [r1, r2, r3];
  val _ = Proofterm_Test.check [p1, p2, p3, p4, p5, p6];
end
\<close>

end
