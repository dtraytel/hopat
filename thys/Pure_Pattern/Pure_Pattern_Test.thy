section \<open>Testing the Generated Code against \<open>Pattern\<close>\<close>

theory Pure_Pattern_Test
  imports Pure_Pattern_Code
begin

text \<open>
  The generated code is compiled into the running ML environment, and the functor of
  \<open>pattern_wrapper.ML\<close> yields \<open>Pattern_New\<close> with the same signature as Pure's \<open>Pattern\<close>.
  On problems taken from the theorems of HOL, both must produce the same results, or raise the
  same exceptions.
\<close>

code_reflect Pattern_Generated
  datatypes res = Ok | Err
    and exn = Unif | Pattern | Match | TUnify | Type_Match | Class_Error | Type_Error | Term_Error
      | Failure | Subscript | Unequal_Lengths | Dup
    and unif_trace = No_Trace | Typ_Clash | Clash | Clash_BB | Clash_B | Proj_Fail | Ocheck_Fail
    and class_error = No_Classrel | No_Arity | No_Subsort
  functions unify_types unify match first_order_match pattern

ML_file \<open>pattern_wrapper.ML\<close>

ML \<open>
structure Pattern_New = Pattern_Fun(val unify_trace_failure = Pattern.unify_trace_failure);
\<close>

ML \<open>
structure Pattern_Test =
struct

datatype outcome = OK of string | EXN of string;

fun exn_name exn =
  (case exn of
    Pattern.Unif => "Unif"
  | Pattern.Pattern => "Pattern"
  | Pattern.MATCH => "MATCH"
  | Pattern_New.Unif => "Unif"
  | Pattern_New.Pattern => "Pattern"
  | Pattern_New.MATCH => "MATCH"
  | TYPE (msg, Ts, ts) => "TYPE " ^ msg ^ " " ^ \<^make_string> (Ts, ts)
  | TERM (msg, ts) => "TERM " ^ msg ^ " " ^ \<^make_string> ts
  | Fail msg => "Fail " ^ msg
  | Subscript => "Subscript"
  | ListPair.UnequalLengths => "UnequalLengths"
  | Vartab.DUP xi => "DUP " ^ \<^make_string> xi
  | exn => if Exn.is_interrupt exn then Exn.reraise exn else "other: " ^ General.exnMessage exn);

fun dump_env (Envir.Envir {maxidx, tenv, tyenv}) =
  \<^make_string> (maxidx, Vartab.dest tenv, Vartab.dest tyenv);

fun dump_menv (tyenv, tenv) = \<^make_string> (Vartab.dest tyenv, Vartab.dest tenv);

fun outcome f x =
  (case Exn.result f x of
    Exn.Res y => OK y
  | Exn.Exn exn => EXN (exn_name exn));

(*statistics: number of tests, number of successes, mismatches*)
fun compare name f g xs =
  let
    val (time1, r1) = Timing.timing (map (outcome f)) xs;
    val (time2, r2) = Timing.timing (map (outcome g)) xs;
    val pairs = xs ~~ (r1 ~~ r2);
    val mismatches = filter (fn (_, (a, b)) => a <> b) pairs;
    val oks = length (filter (fn (_, (a, _)) => (case a of OK _ => true | _ => false)) pairs);
  in
    {name = name, tests = length xs, ok = oks, mismatches = mismatches,
     time_orig = #elapsed time1, time_new = #elapsed time2}
  end;

fun report {name, tests, ok, mismatches, time_orig, time_new} =
  name ^ ": " ^ string_of_int tests ^ " tests, " ^ string_of_int ok ^ " successful, " ^
  string_of_int (length mismatches) ^ " mismatches; time Pattern " ^ Time.toString time_orig ^
  "s, generated " ^ Time.toString time_new ^ "s";


(* test data from the theorems of a theory *)

fun theorems thy n =
  Global_Theory.all_thms_of thy true
  |> map (Thm.prop_of o snd)
  |> take n;

fun subterms t =
  (case t of
    Abs (_, _, u) => t :: subterms u
  | u $ v => t :: subterms u @ subterms v
  | _ => [t]);

fun head_key t =
  (case Term.head_of (Term.strip_abs_body t) of
    Const (c, _) => SOME c
  | Free (x, _) => SOME x
  | _ => NONE);

(*unification problems:
  (1) premises of rules against conclusions of rules with the same head (resolution),
  (2) premises with a flexible head against arbitrary conclusions,
  (3) propositions against variants of themselves (always unifiable, exercises flex-flex),
  (4) conclusions against conclusions with the same head*)
fun unif_problems thy n k =
  let
    val props = theorems thy n;
    val maxidx = fold (Integer.max o Term.maxidx_of_term) props 0;
    val shift = Logic.incr_indexes ([], maxidx + 1);
    val concls = map (shift o Logic.strip_imp_concl) props;
    val prems = maps Logic.strip_imp_prems props;
    val tab = fold (fn t => case head_key t of SOME c => Symtab.cons_list (c, t) | NONE => I)
      concls Symtab.empty;
    val p1 = prems |> maps (fn p =>
      (case head_key p of
        SOME c => take k (Symtab.lookup_list tab c) |> map (fn q => (p, q))
      | NONE => []));
    val flex = prems |> filter (fn p => is_none (head_key p));
    val p2 = flex |> map_index (fn (i, p) =>
      map (fn j => (p, nth concls ((i * 7919 + j * 104729) mod length concls))) (0 upto k - 1))
      |> flat;
    val p3 = map (fn t => (t, shift t)) props;
    val p4 = concls |> maps (fn q =>
      (case head_key q of
        SOME c => take k (Symtab.lookup_list tab c) |> map (fn q' => (Logic.incr_indexes ([], maxidx + 1) q, q'))
      | NONE => []));
  in
    (p1 @ p2 @ p3 @ p4) |> map (fn (p, q) => ((p, q), Envir.empty (3 * maxidx + 3)))
  end;

(*matching problems:
  (1) left-hand sides of equations against subterms of propositions with the same head,
  (2) left-hand sides against left-hand sides,
  (3) propositions against variants of themselves*)
fun match_problems thy n k =
  let
    val props = theorems thy n;
    val maxidx = fold (Integer.max o Term.maxidx_of_term) props 0;
    val lhss = props |> map_filter (fn t =>
      (case Logic.strip_imp_concl t of
        Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ l $ _) => SOME l
      | Const (\<^const_name>\<open>Pure.eq\<close>, _) $ l $ _ => SOME l
      | _ => NONE));
    val objs = props |> maps subterms |> filter_out Term.is_open;
    val tab = fold (fn t => case head_key t of SOME c => Symtab.cons_list (c, t) | NONE => I)
      objs Symtab.empty;
    val ltab = fold (fn t => case head_key t of SOME c => Symtab.cons_list (c, t) | NONE => I)
      lhss Symtab.empty;
    val m1 = lhss |> maps (fn l =>
      (case head_key l of
        SOME c => take k (Symtab.lookup_list tab c) |> map (fn obj => (l, obj))
      | NONE => []));
    val m2 = lhss |> maps (fn l =>
      (case head_key l of
        SOME c => take k (Symtab.lookup_list ltab c)
          |> map (fn obj => (l, Logic.incr_indexes ([], maxidx + 1) obj))
      | NONE => []));
    val m3 = map (fn t => (t, Logic.incr_indexes ([], maxidx + 1) t)) props;
  in m1 @ m2 @ m3 end;

end;
\<close>

ML \<open>
local
  val thy = \<^theory>;
  val context = Context.Proof \<^context>;
  val ups = Pattern_Test.unif_problems thy 20000 5;
  val mps = Pattern_Test.match_problems thy 20000 5;
  val r1 = Pattern_Test.compare "unify"
    (fn (st, env) => Pattern_Test.dump_env (Pattern.unify context st env))
    (fn (st, env) => Pattern_Test.dump_env (Pattern_New.unify context st env)) ups;
  val r2 = Pattern_Test.compare "match"
    (fn po => Pattern_Test.dump_menv (Pattern.match thy po (Vartab.empty, Vartab.empty)))
    (fn po => Pattern_Test.dump_menv (Pattern_New.match thy po (Vartab.empty, Vartab.empty))) mps;
  val r3 = Pattern_Test.compare "first_order_match"
    (fn po => Pattern_Test.dump_menv (Pattern.first_order_match thy po (Vartab.empty, Vartab.empty)))
    (fn po => Pattern_Test.dump_menv (Pattern_New.first_order_match thy po (Vartab.empty, Vartab.empty)))
    mps;
  val r4 = Pattern_Test.compare "pattern"
    (fn t => Bool.toString (Pattern.pattern t)) (fn t => Bool.toString (Pattern_New.pattern t))
    (map fst mps @ map snd mps);
in
  val _ = writeln (cat_lines
    [Pattern_Test.report r1, Pattern_Test.report r2, Pattern_Test.report r3, Pattern_Test.report r4]);
  val _ =
    if null (#mismatches r1) andalso null (#mismatches r2) andalso null (#mismatches r3)
      andalso null (#mismatches r4) then ()
    else error ("Mismatches:\n" ^ \<^make_string> (take 3 (#mismatches r1)) ^ "\n" ^
      \<^make_string> (take 3 (#mismatches r2)) ^ "\n" ^ \<^make_string> (take 3 (#mismatches r3)))
end
\<close>

text \<open>
  The rigid occurs check: problems with a non-rigid occurrence of the flexible head and a
  unifier. Pure's \<open>Pattern\<close> reports \<open>Unif\<close> (no unifier); the model gives up with \<open>Pattern\<close>.
  A rigid occurrence still yields \<open>Unif\<close>.
\<close>

ML \<open>
local
  val context = Context.Proof \<^context>;
  val nat = \<^typ>\<open>nat\<close>;
  val natnat = nat --> nat;
  fun var x T = Var ((x, 0), T);
  fun free x T = Free (x, T);
  val F = var "F" natnat and G = var "G" natnat;
  val env0 = Envir.empty 0;
  (*C1: ?p =?= \<not> (?f ?p), unifier ?p := \<not> False, ?f := \<lambda>_. False*)
  val p = var "p" \<^typ>\<open>bool\<close> and f = var "f" (\<^typ>\<open>bool\<close> --> \<^typ>\<open>bool\<close>);
  val c1 = ((p, \<^const>\<open>Not\<close> $ (f $ p)), env0);
  (*C2: ?F x =?= f (?G x) with ?G := \<lambda>x. (\<lambda>y. c) (?F x), unifier ?F := \<lambda>x. f c*)
  val env2 = Envir.update ((("G", 0), natnat),
      Abs ("x", nat, Abs ("y", nat, free "c" nat) $ (F $ Bound 0))) env0;
  val c2 = ((Abs ("x", nat, F $ Bound 0), Abs ("x", nat, free "f" natnat $ (G $ Bound 0))), env2);
  (*C3: \<lambda>x. ?F x =?= \<lambda>x. c ((\<lambda>y. d) (?F x)), unifier ?F := \<lambda>x. c d*)
  val c3 = ((Abs ("x", nat, F $ Bound 0),
      Abs ("x", nat, free "c" natnat $ (Abs ("y", nat, free "d" nat) $ (F $ Bound 0)))), env0);
  (*C4: \<lambda>x. ?H x =?= \<lambda>x. x (?H (\<lambda>z. a)), unifier ?H := \<lambda>x. x a*)
  val H = var "H" (natnat --> nat);
  val c4 = ((Abs ("x", natnat, H $ Bound 0),
      Abs ("x", natnat, Bound 0 $ (H $ Abs ("z", nat, free "a" nat)))), env0);
  (*rigid occurrence: \<lambda>x. ?F x =?= \<lambda>x. c (?F x) has no unifier*)
  val r = ((Abs ("x", nat, F $ Bound 0), Abs ("x", nat, free "c" natnat $ (F $ Bound 0))), env0);
  fun test (name, (st, env), orig, new) =
    let
      val o1 = Pattern_Test.outcome (fn () => Pattern_Test.dump_env (Pattern.unify context st env)) ();
      val o2 = Pattern_Test.outcome (fn () => Pattern_Test.dump_env (Pattern_New.unify context st env)) ();
    in
      if o1 = orig andalso o2 = new then writeln (name ^ ": ok")
      else error (name ^ ": unexpected outcome " ^ \<^make_string> (o1, o2))
    end;
  val unif = Pattern_Test.EXN "Unif" and pat = Pattern_Test.EXN "Pattern";
in
  val _ = List.app test
    [("C1", c1, unif, pat), ("C2", c2, unif, pat), ("C3", c3, unif, pat), ("C4", c4, unif, pat),
     ("rigid", r, unif, unif)]
end
\<close>

end
