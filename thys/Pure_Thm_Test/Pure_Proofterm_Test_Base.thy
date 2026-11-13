section \<open>Test Infrastructure for the Generated Proof Functions\<close>

theory Pure_Proofterm_Test_Base
  imports Pure_Bicompose_Test_Base
begin

text \<open>
  Synthetic classic and tight proofs of theorems and the comparison of proofs, for the tests of
  theories \<^theory_text>\<open>Pure_Proofterm_Test\<close>, \<^theory_text>\<open>Pure_Assumption_Test\<close> and
  \<^theory_text>\<open>Pure_Rules_Test\<close>.
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

(*a proof in full; theorem boxes by their serial, proposition and type arguments*)
local
  val types = Exact.option (Exact.list Exact.typ);
  fun prf MinProof = Buffer.add "MinProof"
    | prf (PBound i) = Exact.con "PBound" Exact.int i
    | prf (Abst (a, T, p)) = Exact.con "Abst" (Exact.triple Exact.string (Exact.option Exact.typ) prf) (a, T, p)
    | prf (AbsP (a, t, p)) = Exact.con "AbsP" (Exact.triple Exact.string (Exact.option Exact.term) prf) (a, t, p)
    | prf (p % t) = Exact.con "Appt" (Exact.pair prf (Exact.option Exact.term)) (p, t)
    | prf (p %% q) = Exact.con "AppP" (Exact.pair prf prf) (p, q)
    | prf (Hyp t) = Exact.con "Hyp" Exact.term t
    | prf (PAxm (a, t, Ts)) = Exact.con "PAxm" (Exact.triple Exact.string Exact.term types) (a, t, Ts)
    | prf (PClass (T, c)) = Exact.con "PClass" (Exact.pair Exact.typ Exact.string) (T, c)
    | prf (Oracle (a, t, Ts)) = Exact.con "Oracle" (Exact.triple Exact.string Exact.term types) (a, t, Ts)
    | prf (PThm ({serial, prop, types = Ts, ...}, _)) =
        Exact.con "PThm" (Exact.triple Exact.int Exact.term types) (serial, prop, Ts);
in
  val dump = Exact.content prf;
end;

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

type report = Test_Stat.report;

fun compare name show f g xs : report =
  Test_Stat.compare name show (SOME o outcome f) (SOME o outcome g) xs;

val report = Test_Stat.report;
val check = Test_Stat.check;
val check_with = Test_Stat.check_with;


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
    SOME (P.Ok p) => ([], p)
  | SOME (P.Err (P.ZExn exn)) => raise_exn exn
  | SOME (P.Err (P.BAD_INST inst)) => raise ZTerm.BAD_INST inst
  | SOME (P.Err P.ZOption) => raise Option.Option
  | NONE => raise Fail "undefined result");

(*a tight proof in full; proof constants of theorems without their names, which have serials*)
local
  fun name (ZAxiom a) = Exact.con "ZAxiom" Exact.string a
    | name (ZOracle a) = Exact.con "ZOracle" Exact.string a
    | name (ZThm _) = Buffer.add "ZThm";
  fun prf ZNop = Buffer.add "ZNop"
    | prf (ZConstp ((a, A), insts)) =
        Exact.con "ZConstp" (Exact.triple name Exact.zterm Exact.zinsts) (a, A, insts)
    | prf (ZBoundp i) = Exact.con "ZBoundp" Exact.int i
    | prf (ZAbst (a, T, p)) = Exact.con "ZAbst" (Exact.triple Exact.string Exact.ztyp prf) (a, T, p)
    | prf (ZAbsp (a, t, p)) = Exact.con "ZAbsp" (Exact.triple Exact.string Exact.zterm prf) (a, t, p)
    | prf (ZAppt (p, t)) = Exact.con "ZAppt" (Exact.pair prf Exact.zterm) (p, t)
    | prf (ZAppp (p, q)) = Exact.con "ZAppp" (Exact.pair prf prf) (p, q)
    | prf (ZHyp t) = Exact.con "ZHyp" Exact.zterm t
    | prf (OFCLASSp (T, c)) = Exact.con "OFCLASSp" (Exact.pair Exact.ztyp Exact.string) (T, c);
in
  val zdump = Exact.content prf;
end;

fun zoutcome f x =
  (case Exn.result (Timeout.apply (seconds 5.0) f) x of
    Exn.Res (_, p) => zdump p
  | Exn.Exn exn => "EXN " ^ Bicompose_Test.exn_name exn);

fun zcompare name show f g xs : report =
  Test_Stat.compare name show (SOME o zoutcome f) (SOME o zoutcome g) xs;

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

(*ZTerm.lift_proof with fixes zterm-lift-hyps and zterm-lift-frees: the assumptions of the subgoal
  are annotated as they are, not lifted like the terms of the rule, and the types of free
  variables in the lifted proof of the rule are incremented*)
fun zlift_fix_hyps thy gprop inc k prf =
  let
    val {zterm, ...} = ZTerm.zterm_cache thy;
    val incrT = ZTerm.map_tvars (fn ((a, i), S) => ZTVar ((a, if i >= 0 then i + inc else i), S));
    fun frees t =
      let val t' = ZTerm.map_vars (fn ((x, i), T) => ZVar ((x, i), if i = ~1 then incrT T else T)) t
      in if t' = t then raise Same.SAME else t' end;
    fun leaf 0 p = Same.commit (ZTerm.map_proof {hyps = false} Same.same frees) p
      | leaf n (ZAppp (p, q)) = ZAppp (leaf (n - 1) p, q)
      | leaf _ p = p;
    fun walk (Const ("Pure.imp", _) $ A $ B) (ZAbsp (a, _, p)) = ZAbsp (a, zterm A, walk B p)
      | walk (Const ("Pure.all", _) $ Abs (_, _, t)) (ZAbst (a, T, p)) = ZAbst (a, T, walk t p)
      | walk _ p = leaf k p;
    fun top 0 p = walk gprop p
      | top n (ZAbsp (a, t, p)) = ZAbsp (a, t, top (n - 1) p)
      | top _ p = p;
  in top k prf end;

fun zlift_ref (r, i, st) =
  let
    val gprop = Thm.term_of (Thm.cprem_of st i);
    val (ws, p) = zlift_orig (r, i, st);
  in (ws, zlift_fix_hyps (Thm.theory_of_thm st) gprop (Thm.maxidx_of st + 1) (Thm.nprems_of r) p) end;

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
(*ZTerm.bicompose_proof with fixes zterm-flatten, zterm-asm and zterm-norm-ofclass: the proofs of
  flattened premises follow the premises before normalisation and are normalised like the proofs
  of the theorems; the proof by assumption strips as many assumptions from the normalised premise
  as Logic.assum_problems from the premise before normalisation; the normalisation of terms also
  normalises the types of class memberships (it normalises all other types, and normalisation of
  types is idempotent)*)
fun zmk_asm_prf C i m =
  let
    fun imp _ i 0 = ZBoundp i
      | imp (ZApp (ZApp (ZConst0 "Pure.imp", A), B)) i m = ZAbsp ("H", A, imp B (i + 1) (m - 1))
      | imp _ i _ = ZBoundp i;
    fun all (ZApp (ZConst1 ("Pure.all", _), ZAbs (a, T, t))) = ZAbst (a, T, all t)
      | all t = imp t (~ i) m
  in all C end;

fun zflatten_params_proof i j n (ZApp (ZApp (ZConst0 "Pure.imp", A), B), k) =
      ZAbsp ("H", A, zflatten_params_proof (i + 1) j n (B, k))
  | zflatten_params_proof i j n (ZApp (ZConst1 ("Pure.all", _), ZAbs (a, T, t)), k) =
      ZAbst (a, T, zflatten_params_proof i (j + 1) n (t, k))
  | zflatten_params_proof i j n (_, k) =
      ZTerm.ZAppps (ZTerm.ZAppts (ZBoundp (k + i),
        map ZBound (j - 1 downto 0)), map ZBoundp (remove (op =) (i - n) (i - 1 downto 0)));

fun zcomp_ref (thy, env, smax, flatten, Bs, As, A, oldAs, n, m, visible, rprf, sprf) =
  let
    val {zterm, ...} = ZTerm.zterm_cache thy;
    val normt = zterm #> ZTerm.norm_term thy env #> ZTerm.map_types (ZTerm.norm_type thy (Envir.type_env env));
    val normp = ZTerm.norm_proof thy env visible;
    val lb = length Bs;
    val la = length As;
    fun asm_prf A = zmk_asm_prf (normt A) n (length (#2 (Logic.assum_problems (m, A))));
    fun proof p q =
      ZTerm.ZAbsps (map normt (Bs @ As))
        (ZAppp (ZTerm.ZAppps (q, map ZBoundp (lb + la - 1 downto la)),
          ZTerm.ZAppps (p, (if n > 0 then [asm_prf (the A)] else []) @
            map (if flatten then normp o zflatten_params_proof 0 0 n else ZBoundp o snd)
              (map zterm oldAs ~~ (la - 1 downto 0)))));
  in
    ([], if Envir.is_empty env then proof rprf sprf
      else proof (normp rprf) (if Envir.above env smax then sprf else normp sprf))
  end;

fun zcomp_gen (thy, env, smax, flatten, Bs, As, A, oldAs, n, m, visible, rprf, sprf) =
  zrun (P.zbicompose_proof (ztypargs thy) env smax flatten Bs As A oldAs n m visible rprf sprf);

(*renaming of the variables of the tight proof of the rule with those of its new premises, as in
  Thm.bicompose_aux with fix zterm-rename: only variables with indices above the
  maximal index smax of the proof state*)
fun zren_tab th =
  distinct (op =) (map (fst o fst) (Term.add_vars (Thm.full_prop_of th) [])) |> map (fn x => (x, x ^ "'"));
fun zren_orig (tab, smax, p) =
  let
    fun term (Var ((x, i), T)) =
          (case AList.lookup (op =) tab x of SOME y => Var ((y, i), T) | NONE => raise Same.SAME)
      | term _ = raise Same.SAME;
    fun zvar ((x, i), T) =
      if i <= smax then raise Same.SAME
      else
        (case term (Var ((x, i), dummyT)) of Var ((y, _), _) => ZVar ((y, i), T) | _ => raise Same.SAME);
  in ([], ZTerm.map_proof {hyps = false} Same.same (Same.function_eq (op =) (ZTerm.map_vars zvar)) p) end;
fun zren_gen (tab, smax, p) = zrun (P.zren_proof (tab, []) smax p);

fun show_zcomp (_, env, smax, _, Bs, As, A, _, n, m, _, _, _) =
  \<^make_string> (Envir.maxidx_of env, smax, Bs, As, A, n, m);

end;
\<close>

end
