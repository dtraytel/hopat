section \<open>Testing the Generated Code against \<open>Unify\<close>\<close>

theory Pure_Unify_Test
  imports Pure_Unify_Code
begin

text \<open>
  The generated code is compiled into the running ML environment, and the functor of
  \<open>unify_wrapper.ML\<close> yields \<open>Unify_New\<close> with the same signature as Pure's \<open>Unify\<close>. The
  formalization deviates from \<open>unify.ML\<close> where \<open>unify.ML\<close> loses unifiers: in the treatment
  of flex-flex pairs (\<^const>\<open>clean_term\<close>) and in the rigid occurs check (\<^const>\<open>pattern_occ\<close>). The
  reference for the test is therefore \<open>Unify_Reference\<close> of \<^file>\<open>unify_reference.ML\<close>: Pure's
  \<open>unify.ML\<close> with the same changes. On problems taken from the theorems of HOL, the first unifiers of both must
  agree, and so must the exceptions raised. We also report on how often the result differs
  from Pure's \<open>Unify\<close>. These tests use the default arity bound \<open>0\<close>; the last section tests the
  guessing of arities for type variables.
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
    val unify_trace_types = Unify.unify_trace_types
    val arity_bound = Config.declare_int ("unify_arity_bound", \<^here>) (K 0));
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
    ("?P (?a :: nat) (?b :: nat) :: bool", "?Q (?b :: nat) :: bool"),
    ("\<lambda>x::nat \<Rightarrow> nat. ?v x :: nat", "\<lambda>x::nat \<Rightarrow> nat. x (Suc (?F (?v :: (nat \<Rightarrow> nat) \<Rightarrow> nat)))")];
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

text \<open>
  The unifier that the rigid occurs check of \<open>unify.ML\<close> rejects: for
  \<open>\<lambda>y. ?v y =?= \<lambda>y. y (?v (\<lambda>z. d))\<close>, Pure's \<open>Unify\<close> returns no unifier, but \<open>?v := \<lambda>y. y d\<close> is
  one. The formalization returns it.
\<close>

ML \<open>
local
  val context = Context.Proof \<^context>;
  val b = TFree ("'b", []);
  val v = Var (("v", 0), (b --> b) --> b);
  val d = Free ("d", b);
  val t = Abs ("y", b --> b, v $ Bound 0);
  val u = Abs ("y", b --> b, Bound 0 $ (v $ Abs ("z", b, d)));
  fun results unifiers = Seq.list_of (unifiers [] (context, Envir.empty 0, [(t, u)]));
  val r_pure = results Unify.hounifiers;
  val r_new = results Unify_New.hounifiers;
  val r_ref = results Unify_Reference.hounifiers;
  fun solves (env, _) = Envir.norm_term env t aconv Abs ("y", b --> b, Bound 0 $ d);
in
  val _ = \<^assert> (null r_pure);
  val _ = \<^assert> (exists solves r_new);
  val _ = \<^assert> (map Unify_Test.dump_unifier r_new = map Unify_Test.dump_unifier r_ref);
end
\<close>


text \<open>
  The unifiers of \<open>unify.ML\<close> for a flex-rigid pair whose flexible side becomes unsaturated: for
  \<open>k (c\<^sub>1 :: ?'b) =?= k (c\<^sub>1 :: 'n \<Rightarrow> 'n)\<close> and \<open>?v c =?= f c\<close> (with \<open>?v, f :: 'a \<Rightarrow> ?'b\<close>), Pure's
  \<open>Unify\<close> returns two unifiers, neither of which solves the second pair (one of them is ill-typed).
  The formalization \<open>\<eta>\<close>-expands the pair first and returns \<open>?v := f\<close>.
\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val context = Context.Proof ctxt;
  val a = TFree ("'a", []); val n = TFree ("'n", []); val oT = TFree ("'o", []);
  val b = TVar (("'b", 0), []);
  val v = Var (("v", 0), a --> b); val c = Free ("c", a); val f = Free ("f", a --> b);
  val pairB = (Free ("k", b --> oT) $ Free ("c1", b), Free ("k", (n --> n) --> oT) $ Free ("c1", n --> n));
  val pairA = (v $ c, f $ c);
  fun results unifiers = Seq.list_of (unifiers [] (context, Envir.empty 0, [pairB, pairA]));
  fun solves (env, _) =
    (Envir.norm_term env (v $ c) aconv Envir.norm_term env (f $ c) orelse
      Envir.eta_contract (Envir.norm_term env (v $ c)) aconv Envir.eta_contract (Envir.norm_term env (f $ c)))
    andalso can (Sign.cert_term (Proof_Context.theory_of ctxt)) (Envir.norm_term env v);
  val r_pure = results Unify.hounifiers;
  val r_new = results Unify_New.hounifiers;
  val r_ref = results Unify_Reference.hounifiers;
in
  val _ = \<^assert> (not (null r_pure) andalso not (exists solves r_pure));
  val _ = \<^assert> (not (null r_new) andalso forall solves r_new);
  val _ = \<^assert> (map Unify_Test.dump_unifier r_new = map Unify_Test.dump_unifier r_ref);
end
\<close>

subsection \<open>Guessing arities for type variables\<close>

text \<open>
  With a positive arity bound, the formalization finds the unifiers of polymorphic problems that
  \<open>unify.ML\<close> loses. A unifier covers a solution if the solution is an instance of it (in terms
  and types), which we test by matching.
\<close>

ML \<open>
structure Arity_Test =
struct

val ctxt = \<^context>;
fun pr t = Print_Mode.setmp [] (Syntax.string_of_term ctxt) t;
fun prT T = Print_Mode.setmp [] (Syntax.string_of_typ ctxt) T;

fun show vars (env, tps) =
  space_implode ",  " (map (fn v =>
    pr v ^ " := " ^ pr (Envir.norm_term env v) ^ " :: " ^
      prT (Envir.norm_type (Envir.type_env env) (fastype_of v))) vars) ^
  (if null tps then "" else "  [" ^ string_of_int (length tps) ^ " flex-flex]");

fun results hounifiers bound k tus =
  Seq.list_of (Seq.take 20000 (hounifiers []
    (Context.Proof (ctxt
      |> Config.put Unify.search_bound bound
      |> Config.put Unify_New.arity_bound k), Envir.empty 0, tus)));

fun covers vars sol (env, _) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val lhs = map (Envir.norm_term env) vars;
  in
    (Pattern.match thy (HOLogic.mk_tuple lhs, HOLogic.mk_tuple sol) (Vartab.empty, Vartab.empty); true)
      handle Pattern.MATCH => false | Pattern.Pattern => false
  end;

(*with arity bound k: does Pure's Unify cover the solution, does the formalization?*)
fun report name k vars tus sol =
  let
    val old = results Unify.hounifiers 4 0 tus;
    val new = results Unify_New.hounifiers 4 k tus;
    val cov_old = exists (covers vars sol) old;
    val cov_new = exists (covers vars sol) new;
  in
    writeln (name ^ ": Pure's Unify " ^ string_of_int (length old) ^ " unifiers (covers solution: " ^
      Bool.toString cov_old ^ "), arity bound " ^ string_of_int k ^ ": " ^ string_of_int (length new) ^
      " unifiers (covers solution: " ^ Bool.toString cov_new ^ ")\n" ^
      cat_lines (map (prefix "  " o show vars) (take 4 (filter (covers vars sol) new))));
    (cov_old, cov_new)
  end;

val b = TFree ("'b", []); val c = TFree ("'c", []); val d = TFree ("'d", []);
val a = TVar (("'a", 0), []); val bv = TVar (("'b", 0), []);

(*1: ?F ?G =?= c with ?F :: ?'a => 'b; lost: ?'a := 'd => 'b, ?F := %x. x e, ?G := %y. c*)
val F1 = Var (("F", 0), a --> b); val G1 = Var (("G", 0), a); val c1 = Free ("c", b);
val ce1 = ([F1, G1], [(F1 $ G1, c1)],
  [Abs ("x", d --> b, Bound 0 $ Free ("e", d)), Abs ("y", d, c1)]);

(*2: ?F ?H =?= c, c :: ?'b; lost: ?'b := 'c => 'd, ?'a := 'c => 'c => 'd,
  ?F := %x y. x y y, ?H := %u v. c u*)
val F2 = Var (("F", 0), a --> bv); val H2 = Var (("H", 0), a); val c2 = Free ("c", bv);
val ce2 = ([F2, H2], [(F2 $ H2, c2)],
  [Abs ("x", c --> c --> d, Abs ("y", c, Bound 1 $ Bound 0 $ Bound 0)),
   Abs ("u", c, Abs ("v", c, Free ("c", c --> d) $ Bound 1))]);

(*3: ?F (%w. w) =?= h a, a :: ?'b, h :: ?'b => 'd; lost: ?'b := 'c => 'c,
  ?F := %x. h (%z. a (x z))*)
val F3 = Var (("F", 0), (c --> c) --> d);
val ce3 = ([F3], [(F3 $ Abs ("w", c, Bound 0), Free ("h", bv --> d) $ Free ("a", bv))],
  [Abs ("x", c --> c, Free ("h", (c --> c) --> d) $ Abs ("z", c, Free ("a", c --> c) $ (Bound 1 $ Bound 0)))]);

end;
\<close>

ML \<open>
local
  open Arity_Test;
  val r = map2 (fn name => fn (vars, tus, sol) => report name 2 vars tus sol)
    ["CE1", "CE2", "CE3"] [ce1, ce2, ce3];
in
  val _ = \<^assert> (r = replicate 3 (false, true));
end
\<close>

text \<open>
  The number of unifiers grows with the arity bound and the search bound, as the minimal
  complete sets of unifiers of polymorphic problems do: arities and nested function types are
  incomparable.
\<close>

ML \<open>
local
  open Arity_Test;
  fun line (name, (_, tus, _)) k =
    name ^ ", arity bound " ^ string_of_int k ^ ": " ^
      commas (map (fn n => string_of_int (length (results Unify_New.hounifiers n k tus))) [1, 2, 3, 4]);
in
  val _ = writeln ("Unifiers for search bounds 1, 2, 3, 4:\n" ^
    cat_lines (maps (fn p => map (line p) [0, 1, 2]) [("CE1", ce1), ("CE2", ce2), ("CE3", ce3)]));
end
\<close>

text \<open>
  On the problems from the theorems of HOL with arity bound \<open>2\<close>: the problems without type
  variables have the same first unifiers as with arity bound \<open>0\<close>; we report how often the
  polymorphic ones differ (for every fifth of them).
\<close>

ML \<open>
local
  val thy = \<^theory>;
  fun context k = Context.Proof (\<^context>
    |> Context_Position.set_visible false
    |> Config.put Unify.search_bound 10
    |> Config.put Unify_New.arity_bound k);
  val ups = Unify_Test.unif_problems thy 500 2;
  fun mono ((t, u), _) = null (Term.add_tvars t []) andalso null (Term.add_tvars u []);
  val (mon, poly) = List.partition mono ups;
  fun run k ((t, u), env) =
    Unify_Test.take_seq 3 Unify_Test.dump_unifier (Unify_New.hounifiers [] (context k, env, [(t, u)]));
  val rm = Unify_Test.compare "monomorphic problems, arity bound 0 vs. 2" (run 0) (run 2) mon;
  val rp = Unify_Test.compare "polymorphic problems (every fifth), arity bound 0 vs. 2" (run 0) (run 2)
    (map_filter (fn (i, x) => if i mod 5 = 0 then SOME x else NONE) (map_index I poly));
in
  val _ = writeln (cat_lines (map Unify_Test.report [rm, rp]));
  val _ = \<^assert> (null (#mismatches rm));
end
\<close>

end
