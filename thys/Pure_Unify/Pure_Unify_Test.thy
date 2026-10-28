section \<open>Testing the Generated Code against \<open>Unify\<close>\<close>

theory Pure_Unify_Test
  imports Pure_Unify_Code
begin

text \<open>
  The generated code is compiled into the running ML environment, and the functor of
  \<open>unify_wrapper.ML\<close> yields \<open>Unify_New\<close> with the same signature as Pure's \<open>Unify\<close>. The
  formalization deviates from \<open>unify.ML\<close> in the treatment of flex-flex pairs
  (\<^const>\<open>clean_term\<close>), where \<open>unify.ML\<close> loses unifiers. The reference for the test is
  therefore \<open>Unify_Reference\<close> of \<^file>\<open>unify_reference.ML\<close>: Pure's \<open>unify.ML\<close> with the same
  two changes. On problems taken from the theorems of HOL, the first unifiers of both must
  agree, and so must the exceptions raised. We also report on how often the result differs
  from Pure's \<open>Unify\<close>.
\<close>

code_reflect Unify_Generated
  datatypes ures = UOk | UErr
    and uexn = PExn | CANTUNIFY | ASSIGN | CHANGE_FAIL | Bind
    and exn = Unif | Pattern | Match | TUnify | Type_Match | Class_Error | Type_Error | Term_Error
      | Failure | Subscript | Unequal_Lengths | Dup
    and unif_trace = No_Trace | Typ_Clash | Clash | Clash_BB | Clash_B | Proj_Fail | Ocheck_Fail
    and class_error = No_Classrel | No_Arity | No_Subsort
    and event = Ev_Unif | Ev_Loss | Ev_Dpairs | Ev_Failure_Node | Ev_Bound_Exceeded
    and elem = El_R | El_E | El_C | El_D
    and cfg = Cfg
  functions hounifiers pull smash_flexflex

ML_file \<open>unify_wrapper.ML\<close>
ML_file \<open>unify_reference.ML\<close>

ML \<open>
structure Unify_New =
  Unify_Fun(
    val search_bound = Unify.search_bound
    val unify_trace = Unify.unify_trace
    val unify_trace_bound = Unify.unify_trace_bound
    val unify_trace_simp = Unify.unify_trace_simp
    val unify_trace_types = Unify.unify_trace_types);
\<close>

ML \<open>
structure Unify_Test =
struct

fun exn_name exn =
  (case exn of
    Pattern.Unif => "Unif"
  | Pattern.Pattern => "Pattern"
  | Pattern.MATCH => "MATCH"
  | TYPE (msg, Ts, ts) => "TYPE " ^ msg ^ " " ^ \<^make_string> (Ts, ts)
  | TERM (msg, ts) => "TERM " ^ msg ^ " " ^ \<^make_string> ts
  | Fail msg => "Fail " ^ msg
  | Subscript => "Subscript"
  | ListPair.UnequalLengths => "UnequalLengths"
  | Vartab.DUP xi => "DUP " ^ \<^make_string> xi
  | Bind => "Bind"
  | exn => if Exn.is_interrupt exn then Exn.reraise exn else "other: " ^ General.exnMessage exn);

fun dump_env (Envir.Envir {maxidx, tenv, tyenv}) =
  \<^make_string> (maxidx, Vartab.dest tenv, Vartab.dest tyenv);

fun dump_unifier (env, tpairs: (term * term) list) = dump_env env ^ " " ^ \<^make_string> tpairs;

(*the first n elements of a sequence, or the exception raised*)
fun take_seq n dump xq =
  let
    fun go 0 _ acc = rev acc
      | go k xq acc =
          (case Exn.result Seq.pull xq of
            Exn.Res NONE => rev ("END" :: acc)
          | Exn.Res (SOME (x, xq')) => go (k - 1) xq' (dump x :: acc)
          | Exn.Exn exn => rev (("EXN " ^ exn_name exn) :: acc))
  in cat_lines (go n xq []) end;

fun outcome f x =
  (case Exn.result f x of
    Exn.Res y => y
  | Exn.Exn exn => "EXN " ^ exn_name exn);

end;
\<close>

ML \<open>
local
  val context = Context.Proof \<^context>;
  val read = Syntax.read_term (Proof_Context.set_mode Proof_Context.mode_schematic \<^context>);
  val tests = map (apply2 read)
   [("?P (Suc 0) :: bool", "Suc 0 = Suc 0"),
    ("?f (?x :: nat) :: nat", "Suc (Suc 0)"),
    ("\<lambda>x::nat. ?F (?G x) :: nat", "\<lambda>x::nat. x + x"),
    ("?P (?a :: nat) (?b :: nat) :: bool", "?Q (?b :: nat) :: bool")];
  fun test (t, u) =
    let
      val env = Envir.empty (Integer.max (maxidx_of_term t) (maxidx_of_term u));
      val r1 = Unify_Test.take_seq 10 Unify_Test.dump_unifier (Unify_Reference.hounifiers [] (context, env, [(t, u)]));
      val r2 = Unify_Test.take_seq 10 Unify_Test.dump_unifier (Unify_New.hounifiers [] (context, env, [(t, u)]));
    in (r1 = r2, r1, r2) end;
in
  val res = map test tests;
  val _ = map (fn (b, r1, r2) => writeln (Bool.toString b ^ "\n" ^ r1 ^ "\n----\n" ^ r2)) res;
end
\<close>

ML \<open>
structure Unify_Test =
struct

open Unify_Test;

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

fun pick xs i = nth xs (i mod length xs);

(*unification problems:
  (1) premises of rules against conclusions of rules with the same head (resolution),
  (2) premises with a flexible head against arbitrary conclusions,
  (3) propositions against variants of themselves (flex-flex pairs),
  (4) non-patterns ?F s =?= t, where s is a closed subterm of t (as in rule_tac or subst),
  (5) non-patterns ?F (?G s) =?= t*)
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
      map (fn j => (p, pick concls (i * 7919 + j * 104729))) (0 upto k - 1))
      |> flat;
    val p3 = map (fn t => (t, shift t)) props;
    val idx = 3 * maxidx + 3;
    (*flex-rigid non-pattern problems, exercising MATCH: ?F s and ?F (?G s) against a small
      rigid object c s, where s is a closed subterm and c a fresh constant. The objects are
      kept small so that Huet's procedure does not build large terms.*)
    fun nonpat i t =
      let
        val ss = subterms t |> filter (fn s =>
          not (Term.is_open s) andalso not (is_Var s) andalso fastype_of s <> propT);
      in
        if null ss then []
        else
          let
            val s = pick ss (i * 31);
            val U = fastype_of s;
            val c = Free ("obj", U --> U);
            val F = Var (("F", idx), U --> U);
          in [(F $ s, c $ s)] end
      end;
    val p45 = props |> map_index (uncurry nonpat) |> flat;
  in
    (p1 @ p2 @ p3 @ p45) |> map (fn (p, q) => ((p, q), Envir.empty (3 * maxidx + 4)))
  end;

(*Compare the outcomes of the original (f) and the generated code (g) on each problem. The
  generated code is interpreted and may, like the original, diverge on ill-typed or cyclic
  problems; a generous timeout on the generated side keeps the test terminating. A timeout is
  not counted as a mismatch (the original is given the same bound and is just faster).*)
fun compare name f g xs =
  let
    fun outcome h x =
      (case Exn.result (Timeout.apply (seconds 10.0) h) x of
        Exn.Res y => SOME y
      | Exn.Exn (Timeout.TIMEOUT _) => NONE
      | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else SOME (Unify_Test.exn_name exn));
    fun run1 x = (x, SOME (f x), outcome g x);
    val (time, results) = Timing.timing (map run1) xs;
    val mismatches =
      filter (fn (_, a, b) => is_some a andalso is_some b andalso a <> b) results;
    val timeouts = filter (fn (_, a, b) => not (is_some a) orelse not (is_some b)) results;
  in
    {name = name, tests = length xs, run = length results - length timeouts,
      mismatches = mismatches, time = #elapsed time}
  end;

fun report {name, tests, run, mismatches, time} =
  name ^ ": " ^ string_of_int tests ^ " problems, " ^ string_of_int run ^ " run, " ^
  string_of_int (length mismatches) ^ " mismatches; time " ^ Time.toString time ^ "s";

end;
\<close>

ML \<open>
local
  val thy = \<^theory>;
  (*A small search bound keeps the (interpreted) generated code fast; both implementations
    read the same bound, so the comparison stays faithful.*)
  val context = Context.Proof (\<^context>
    |> Context_Position.set_visible false
    |> Config.put Unify.search_bound 10);
  val ups = Unify_Test.unif_problems thy 500 2;
  val r1 = Unify_Test.compare "hounifiers"
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_unifier (Unify_Reference.hounifiers [] (context, env, [(t, u)])))
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_unifier (Unify_New.hounifiers [] (context, env, [(t, u)])))
    ups;
  val r2 = Unify_Test.compare "unifiers"
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_unifier (Unify_Reference.unifiers (context, env, [(t, u)])))
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_unifier (Unify_New.unifiers (context, env, [(t, u)])))
    ups;
  val r3 = Unify_Test.compare "smash_unifiers"
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_env (Unify_Reference.smash_unifiers context [(t, u)] env))
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_env (Unify_New.smash_unifiers context [(t, u)] env))
    ups;
in
  (*the deviation: how often do the results differ from Pure's Unify?*)
  val r0 = Unify_Test.compare "hounifiers (Pure's Unify vs. the formalization)"
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_unifier (Unify.hounifiers [] (context, env, [(t, u)])))
    (fn ((t, u), env) => Unify_Test.take_seq 2 Unify_Test.dump_unifier (Unify_New.hounifiers [] (context, env, [(t, u)])))
    ups;
  val _ = writeln (cat_lines (map Unify_Test.report [r1, r2, r3, r0]));
  val _ =
    if forall (null o #mismatches) [r1, r2, r3] then ()
    else error (\<^make_string> (map (take 2 o #mismatches) [r1, r2, r3]))
end
\<close>

text \<open>
  The unifier that \<open>unify.ML\<close> loses: for \<open>\<lambda>j. ?F (\<lambda>z. z j) =?= \<lambda>j. ?G\<close>, Pure's \<open>Unify\<close> only
  returns \<open>?F := \<lambda>x. ?G\<close>, which does not cover \<open>?F := \<lambda>x. x (\<lambda>w. c), ?G := c\<close>. The
  formalization keeps the flex-flex pair.
\<close>

ML \<open>
local
  val context = Context.Proof \<^context>;
  val a = TFree ("'a", []) and b = TFree ("'b", []);
  val t = Abs ("j", a, Var (("F", 0), ((a --> b) --> b) --> b) $ Abs ("z", a --> b, Bound 0 $ Bound 1));
  val u = Abs ("j", a, Var (("G", 0), b));
  fun results unifiers = Seq.list_of (unifiers [] (context, Envir.empty 0, [(t, u)]));
  fun bound (env, _) xi = Vartab.defined (Envir.term_env env) xi;
  val [r_pure] = results Unify.hounifiers;
  val [r_new] = results Unify_New.hounifiers;
  val [r_ref] = results Unify_Reference.hounifiers;
in
  val _ = \<^assert> (bound r_pure ("F", 0));
  val _ = \<^assert> (not (bound r_new ("F", 0)) andalso length (snd r_new) = 1);
  val _ = \<^assert> (Unify_Test.dump_unifier r_new = Unify_Test.dump_unifier r_ref);
end
\<close>

end
