section \<open>Testing the Generated Code against \<open>Proofterm\<close>\<close>

theory Pure_Proofterm_Test
  imports Pure_Bicompose_Test_Base
begin

text \<open>
  The generated proof functions are compared with \<open>Proofterm.lift_proof\<close>,
  \<open>Proofterm.bicompose_proof\<close> and \<open>Proofterm.map_proof_terms\<close> on the problems of
  \<^theory>\<open>Pure_Thm.Pure_Bicompose_Test_Base\<close>: lifting over the subgoals of the resolution problems,
  and composition with the results of the model's \<open>bicompose_aux\<close> for resolution,
  elim-resolution and composition. The proofs of the rules and proof states are synthetic: they
  contain all kinds of proofs, with the propositions, variables and type variables of the
  theorems, so that lifting and normalisation have something to do. The tight proof functions
  are compared with those of \<open>ZTerm\<close> likewise; lifting is compared with \<open>ZTerm.lift_proof\<close>
  with fix \<open>zterm-lift-hyps\<close> applied to its result, and the report also counts the problems on
  which Isabelle2026 differs from the fix.
\<close>

ML \<open>
structure Proofterm_Test =
struct

structure G = Bicompose_Generated;
structure P = Bicompose_Generated;

fun raise_exn exn =
  (case exn of
    P.Unif _ => raise Pattern.Unif
  | P.Pattern => raise Pattern.Pattern
  | P.Match => raise Pattern.MATCH
  | P.TUnify => raise Type.TUNIFY
  | P.Type_Match => raise Type.TYPE_MATCH
  | P.Class_Error _ => raise Fail "unexpected CLASS_ERROR"
  | P.Type_Error (msg, Ts, ts) => raise TYPE (msg, Ts, ts)
  | P.Term_Error (msg, ts) => raise TERM (msg, ts)
  | P.Failure msg => raise Fail msg
  | P.Subscript => raise Subscript
  | P.Unequal_Lengths => raise ListPair.UnequalLengths
  | P.Dup xi => raise Vartab.DUP xi);

(*warnings are returned instead of printed*)
fun run r =
  (case r of
    SOME (ws, P.Ok p) => (ws, p)
  | SOME (_, P.Err exn) => raise_exn exn
  | NONE => raise Fail "undefined result");

(*a proof as a string; theorem boxes by their serial, proposition and type arguments*)
fun dump (PThm ({serial, prop, types, ...}, _)) =
      "PThm(" ^ string_of_int serial ^ "," ^ \<^make_string> (prop, types) ^ ")"
  | dump (Abst (a, T, p)) = "Abst(" ^ a ^ "," ^ \<^make_string> T ^ "," ^ dump p ^ ")"
  | dump (AbsP (a, t, p)) = "AbsP(" ^ a ^ "," ^ \<^make_string> t ^ "," ^ dump p ^ ")"
  | dump (p % t) = "(" ^ dump p ^ " % " ^ \<^make_string> t ^ ")"
  | dump (p %% q) = "(" ^ dump p ^ " %% " ^ dump q ^ ")"
  | dump p = \<^make_string> p;

val body =
  Proofterm.thm_body
    (Proofterm.PBody {oracles = [], thms = [], zboxes = [], zproof = ZNop, proof = MinProof});

(*a synthetic proof of a theorem*)
fun synth th =
  let
    val prop = Thm.full_prop_of th;
    val vars = Term.add_vars prop [] |> rev;
    val tvars = Term.add_tvars prop [] |> rev |> map TVar;
    val T = (case tvars of T :: _ => T | [] => propT);
    val ax = Proofterm.proof_combt' (PAxm ("ax", prop, SOME tvars), map (SOME o Var) vars);
    val thm =
      PThm (Proofterm.thm_header 42 Position.none "Thy" (Thm_Name.empty, Position.none) prop
        (SOME tvars), body);
    val t = (case vars of v :: _ => Var v | [] => Free ("c", T));
  in
    AbsP ("H", SOME prop,
      Abst ("x", SOME T,
        Proofterm.proof_combP (ax % NONE,
          [PBound 0, Hyp prop, PClass (T, "HOL.type"), Oracle ("or", prop, SOME tvars), thm,
            MinProof, AbsP ("H", NONE, PBound 1)]) % SOME t)) %%
      (thm % SOME t)
  end;

fun outcome f x =
  (case Exn.result (Timeout.apply (seconds 5.0) f) x of
    Exn.Res (ws, p) => cat_lines ws ^ dump p
  | Exn.Exn exn => "EXN " ^ Bicompose_Test.exn_name exn);

type report = {name: string, tests: int, mismatches: (string * string * string) list};

fun compare name show f g xs : report =
  let
    val results = map (fn x => (show x, outcome f x, outcome g x)) xs;
  in {name = name, tests = length xs, mismatches = filter (fn (_, a, b) => a <> b) results} end;

fun report ({name, tests, mismatches}: report) =
  name ^ ": " ^ string_of_int tests ^ " tests, " ^ string_of_int (length mismatches) ^ " mismatches";

fun check (rs: report list) =
  if forall (null o #mismatches) rs then ()
  else error (cat_lines (map (fn r => #name r ^ ": " ^ \<^make_string> (take 2 (#mismatches r))) rs));


(* lifting *)

fun lift_args (r, i, st) =
  let
    val gprop = Thm.term_of (Thm.cprem_of st i);
    val inc = Thm.maxidx_of st + 1;
    val prems = map (Logic.lift_all inc gprop) (Thm.prems_of r);
  in (gprop, inc, prems, synth r) end;

fun lift_orig x = let val (g, inc, prems, p) = lift_args x in ([], Proofterm.lift_proof g inc prems p) end;
fun lift_gen x = let val (g, inc, prems, p) = lift_args x in ([], P.lift_proof g inc prems p) end;


(* composition: the arguments of bicompose_proof from the results of the model *)

fun ops context = Bicompose_Test.ops context;

fun compose_args ctxt flags lifted (eres_flg, orule, nsubgoal) i state =
  (case Exn.result (Timeout.apply (seconds 5.0) (fn () =>
  let
    val context = Context.Proof ctxt;
    val (stpairs, Bs, Bi, C) = Thm.dest_state (state, i);
    val nlift = Logic.count_prems (strip_all_body Bi) + (if eres_flg then ~1 else 0);
    val {flatten, match, incremented} = flags;
    val alg = Sign.classes_of (Context.theory_of context);
    fun eval r = Bicompose_Test.run context (state, orule) r;
    fun results 0 _ = []
      | results k s =
          (case eval (G.bpull (ops context) s) of
            NONE => []
          | SOME (res, s') => res :: results (k - 1) s');
    val s0 = eval (G.bicompose_aux (ops context) alg flatten match incremented
      (Thm.maxidx_of state, (Thm.tpairs_of state, Thm.prop_of state))
      (stpairs, (Bs, (Bi, C))) lifted eres_flg
      (Thm.maxidx_of orule, (Thm.tpairs_of orule, Thm.prop_of orule)) nsubgoal);
    val rprf = synth orule and sprf = synth state;
  in
    results 3 s0 |> map (fn G.BRes (env, _, _, A, G.NewAs (As, oldAs, _, n)) =>
      (env, Thm.maxidx_of state, flatten, Bs, As, A, oldAs, n, nlift + 1, rprf, sprf))
  end)) () of Exn.Res xs => xs | Exn.Exn _ => []);

fun comp_orig (env, smax, flatten, Bs, As, A, oldAs, n, m, rprf, sprf) =
  ([], Proofterm.bicompose_proof env smax flatten Bs As A oldAs n m rprf sprf);
fun comp_gen (env, smax, flatten, Bs, As, A, oldAs, n, m, rprf, sprf) =
  run (P.bicompose_proof env smax flatten Bs As A oldAs n m rprf sprf);

fun show_comp (env, smax, _, Bs, As, A, _, n, m, _, _) =
  \<^make_string> (Envir.maxidx_of env, smax, Bs, As, A, n, m);


(* renaming *)

fun ren_orig (f, p) = ([], Proofterm.map_proof_terms f I p);
fun ren_gen (f, p) = ([], P.map_proof_terms f I p);


(* tight proofs *)

fun ztypargs thy =
  let val consts = Sign.consts_of thy in
    fn c => fn T =>
      (SOME (P.Ok (Consts.typargs consts (c, T)))
        handle TYPE (msg, Ts, ts) => SOME (P.Err (P.Type_Error (msg, Ts, ts)))
          | Subscript => SOME (P.Err P.Subscript))
  end;

fun zrun r =
  (case r of
    SOME (P.ZOk p) => ([], p)
  | SOME (P.ZErr (P.ZExn exn)) => raise_exn exn
  | SOME (P.ZErr (P.BAD_INST inst)) => raise ZTerm.BAD_INST inst
  | SOME (P.ZErr P.ZOption) => raise Option.Option
  | NONE => raise Fail "undefined result");

fun zdump (ZConstp ((_, A), (instT, inst))) =
      "ZConstp(" ^ \<^make_string> (A, ZTVars.dest instT, ZVars.dest inst) ^ ")"
  | zdump (ZAbst (a, T, p)) = "ZAbst(" ^ a ^ "," ^ \<^make_string> T ^ "," ^ zdump p ^ ")"
  | zdump (ZAbsp (a, t, p)) = "ZAbsp(" ^ a ^ "," ^ \<^make_string> t ^ "," ^ zdump p ^ ")"
  | zdump (ZAppt (p, t)) = "(" ^ zdump p ^ " % " ^ \<^make_string> t ^ ")"
  | zdump (ZAppp (p, q)) = "(" ^ zdump p ^ " %% " ^ zdump q ^ ")"
  | zdump p = \<^make_string> p;

fun zoutcome f x =
  (case Exn.result (Timeout.apply (seconds 5.0) f) x of
    Exn.Res (_, p) => zdump p
  | Exn.Exn exn => "EXN " ^ Bicompose_Test.exn_name exn);

fun zcompare name show f g xs : report =
  let
    val results = map (fn x => (show x, zoutcome f x, zoutcome g x)) xs;
  in {name = name, tests = length xs, mismatches = filter (fn (_, a, b) => a <> b) results} end;

(*a synthetic tight proof of a theorem, with a proof constant, redexes and all other kinds*)
fun zsynth th =
  let
    val thy = Thm.theory_of_thm th;
    val prop = Thm.full_prop_of th;
    val A = ZTerm.zterm_of thy prop;
    val ax = ZTerm.axiom_proof thy "ax" prop;
    val T = ZTerm.ztyp_of (case Term.add_tvars prop [] of v :: _ => TVar v | [] => propT);
    val t = (case Term.add_vars prop [] of (xi, U) :: _ => ZVar (xi, ZTerm.ztyp_of U) | [] => ZVar (("c", ~1), T));
    val redex = ZApp (ZAbs ("z", T, ZBound 0), t);
  in
    ZAbsp ("H", A,
      ZAbst ("x", T,
        ZTerm.ZAppps (ZAppt (ax, redex),
          [ZBoundp 0, ZHyp A, OFCLASSp (T, "HOL.type"), ZAppt (ZAbst ("y", T, ZAppt (ax, ZBound 0)), t),
            ZAbsp ("H", A, ZBoundp 1), ZNop])))
  end;

fun zlift_orig (r, i, st) =
  let
    val gprop = Thm.term_of (Thm.cprem_of st i);
    val inc = Thm.maxidx_of st + 1;
    val prems = map (Logic.lift_all inc gprop) (Thm.prems_of r);
  in ([], ZTerm.lift_proof (Thm.theory_of_thm st) gprop inc prems (zsynth r)) end;

(*ZTerm.lift_proof with fix zterm-lift-hyps: the assumptions of the subgoal are annotated as they
  are, not lifted like the terms of the rule*)
fun zlift_fix_hyps thy gprop k prf =
  let
    val {zterm, ...} = ZTerm.zterm_cache thy;
    fun walk (Const ("Pure.imp", _) $ A $ B) (ZAbsp (a, _, p)) = ZAbsp (a, zterm A, walk B p)
      | walk (Const ("Pure.all", _) $ Abs (_, _, t)) (ZAbst (a, T, p)) = ZAbst (a, T, walk t p)
      | walk _ p = p;
    fun top 0 p = walk gprop p
      | top n (ZAbsp (a, t, p)) = ZAbsp (a, t, top (n - 1) p)
      | top _ p = p;
  in top k prf end;

fun zlift_ref (r, i, st) =
  let
    val gprop = Thm.term_of (Thm.cprem_of st i);
    val (ws, p) = zlift_orig (r, i, st);
  in (ws, zlift_fix_hyps (Thm.theory_of_thm st) gprop (Thm.nprems_of r) p) end;

fun zlift_gen (r, i, st) =
  let
    val thy = Thm.theory_of_thm st;
    val gprop = Thm.term_of (Thm.cprem_of st i);
    val inc = Thm.maxidx_of st + 1;
    val prems = map (Logic.lift_all inc gprop) (Thm.prems_of r);
  in zrun (P.zlift_proof (ztypargs thy) gprop inc prems (zsynth r)) end;

(*the arguments of ZTerm.bicompose_proof from those of Proofterm.bicompose_proof*)
fun zcomp_args orule state ((env, smax, flatten, Bs, As, A, oldAs, n, m, _, _)) =
  (Thm.theory_of_thm state, env, smax, flatten, Bs, As, A, oldAs, n, m,
    [Thm.full_prop_of state, Thm.full_prop_of orule], zsynth orule, zsynth state);

fun zcomp_orig (thy, env, smax, flatten, Bs, As, A, oldAs, n, m, visible, rprf, sprf) =
  ([], ZTerm.bicompose_proof thy env smax flatten Bs As A oldAs n m visible rprf sprf);
fun zcomp_gen (thy, env, smax, flatten, Bs, As, A, oldAs, n, m, visible, rprf, sprf) =
  zrun (P.zbicompose_proof (ztypargs thy) env smax flatten Bs As A oldAs n m visible rprf sprf);

fun show_zcomp (_, env, smax, _, Bs, As, A, _, n, m, _, _, _) =
  \<^make_string> (Envir.maxidx_of env, smax, Bs, As, A, n, m);

end;
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
  val z0 = Proofterm_Test.zcompare "lift_proof (tight proofs, Isabelle2026 vs. fix zterm-lift-hyps)" show
    Proofterm_Test.zlift_orig Proofterm_Test.zlift_ref res;
  val z1 = Proofterm_Test.zcompare "lift_proof (tight proofs, with fix zterm-lift-hyps)" show
    Proofterm_Test.zlift_ref Proofterm_Test.zlift_gen res;
  fun zargs flags eres_flg (r, i, st) =
    let val orule = Thm.lift_rule (Thm.cprem_of st i) r in
      map (Proofterm_Test.zcomp_args orule st)
        (Proofterm_Test.compose_args ctxt flags true (eres_flg, orule, Thm.nprems_of r) i st)
    end;
  fun zplain flags (r, i, st) =
    map (Proofterm_Test.zcomp_args r st) (Proofterm_Test.compose_args ctxt flags false (false, r, 0) i st);
  val z2 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, resolution)" Proofterm_Test.show_zcomp
    Proofterm_Test.zcomp_orig Proofterm_Test.zcomp_gen (maps (zargs bflags false) res);
  val z3 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, elim-resolution)" Proofterm_Test.show_zcomp
    Proofterm_Test.zcomp_orig Proofterm_Test.zcomp_gen (maps (zargs bflags true) eres);
  val z4 = Proofterm_Test.zcompare "bicompose_proof (tight proofs, composition)" Proofterm_Test.show_zcomp
    Proofterm_Test.zcomp_orig Proofterm_Test.zcomp_gen (maps (zplain cflags1) comps);
  val rs = [r1, r2, r3, r4, r5, r6, z1, z2, z3, z4];
in
  val _ = writeln (cat_lines (map Proofterm_Test.report (z0 :: rs)));
  val _ = Proofterm_Test.check rs;
end
\<close>

end
