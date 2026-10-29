section \<open>Testing the Prototype of Complete Matching\<close>

theory Pure_Unify_Poly_Test
  imports Pure_Unify_Poly Pure_Unify_Test
begin

declare pullc.simps[code]

text \<open>The datatypes of the model are those of \<open>Unify_Generated\<close> of \<^theory>\<open>Pure_Unify.Pure_Unify_Test\<close>.\<close>

code_reflect Unify_Poly_Generated
  functions hounifiersc pullc

ML \<open>
structure Unify_Poly =
struct

structure G = Unify_Generated;
structure P = Unify_Poly_Generated;

fun cfg_of context =
  G.Cfg (Sign.classes_of (Context.theory_of context),
    Config.get_generic context Unify.search_bound, 1000, false, false);

fun run r =
  (case r of
    SOME (_, G.UOk x) => x
  | SOME (_, G.UErr _) => raise Fail "Unify_Poly: exception"
  | NONE => raise Fail "Unify_Poly: undefined result");

fun to_seq cfg s =
  Seq.make (fn () =>
    (case run (P.pullc cfg s) of
      NONE => NONE
    | SOME (G.El_R (env, tpairs), s') => SOME ((env, tpairs), to_seq cfg s')
    | SOME _ => raise Fail "Unify_Poly: unexpected element"));

fun hounifiers binders (context, env, tus) =
  to_seq (cfg_of context) (P.hounifiersc binders env tus);

end;
\<close>

subsection \<open>The unifiers that \<^const>\<open>hounifiers\<close> misses\<close>

ML \<open>
structure Poly_Test =
struct

val ctxt = \<^context>;
fun pr t = Print_Mode.setmp [] (Syntax.string_of_term ctxt) t;
fun prT T = Print_Mode.setmp [] (Syntax.string_of_typ ctxt) T;

fun show vars (env, tps) =
  space_implode ",  " (map (fn v =>
    pr v ^ " := " ^ pr (Envir.norm_term env v) ^ " :: " ^
      prT (Envir.norm_type (Envir.type_env env) (fastype_of v))) vars) ^
  (if null tps then "" else "  [" ^ string_of_int (length tps) ^ " flex-flex]");

val bound = Unsynchronized.ref 5;
val cap = Unsynchronized.ref 20000;

fun results hounifiers tus =
  Seq.list_of (Seq.take (!cap) (hounifiers []
    (Context.Proof (Config.put Unify.search_bound (!bound) ctxt), Envir.empty 0, tus)));

(*Is there a unifier and a type instantiation of it such that the solution is an instance?
  We test this by unifying the instances of the variables with the solution (Pattern.match
  of the solution against the unifier, modulo types).*)
fun covers vars sol (env, _) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val lhs = map (Envir.norm_term env) vars;
  in
    (Pattern.match thy (HOLogic.mk_tuple lhs, HOLogic.mk_tuple sol) (Vartab.empty, Vartab.empty); true)
      handle Pattern.MATCH => false | Pattern.Pattern => false
  end;

fun report name vars tus sol =
  let
    val old = results Unify_New.hounifiers tus;
    val new = results Unify_Poly.hounifiers tus;
    val cov_old = exists (covers vars sol) old;
    val cov_new = exists (covers vars sol) new;
  in
    writeln (name ^ " (bound " ^ string_of_int (!bound) ^ "): old " ^ string_of_int (length old) ^ " unifiers (covers solution: " ^
      Bool.toString cov_old ^ "), new " ^ string_of_int (length new) ^
      " unifiers (covers solution: " ^ Bool.toString cov_new ^ ")\n" ^
      cat_lines (map (prefix "  " o show vars) (take 8 (filter (covers vars sol) new))));
    (cov_old, cov_new)
  end;

end;
\<close>

ML \<open>
local
  open Poly_Test;
  val b = TFree ("'b", []); val c = TFree ("'c", []); val d = TFree ("'d", []);
  val a = TVar (("'a", 0), []); val bv = TVar (("'b", 0), []);

  (*1: ?F ?G =?= c with ?F :: ?'a => 'b; lost: ?'a := 'd => 'b, ?F := %x. x e, ?G := %y. c*)
  val F1 = Var (("F", 0), a --> b); val G1 = Var (("G", 0), a);
  val c1 = Free ("c", b); val e1 = Free ("e", d);
  val sol1 = [Abs ("x", d --> b, Bound 0 $ e1), Abs ("y", d, c1)];
  val _ = List.app (fn n => (bound := n; report "CE1" [F1, G1] [(F1 $ G1, c1)] sol1; ())) [1, 2, 3, 4];
  val _ = bound := 4;
  val r1 = report "CE1" [F1, G1] [(F1 $ G1, c1)] sol1;

  (*2: ?F ?H =?= c, c :: ?'b; lost: ?'b := 'c => 'd, ?'a := 'c => 'c => 'd,
    ?F := %x y. x y y, ?H := %u v. c u*)
  val F2 = Var (("F", 0), a --> bv); val H2 = Var (("H", 0), a); val c2 = Free ("c", bv);
  val c2' = Free ("c", c --> d);
  val r2 = report "CE2" [F2, H2] [(F2 $ H2, c2)]
    [Abs ("x", c --> c --> d, Abs ("y", c, Bound 1 $ Bound 0 $ Bound 0)),
     Abs ("u", c, Abs ("v", c, c2' $ Bound 1))];

  (*3: ?F (%w. w) =?= h a, a :: ?'b, h :: ?'b => 'd; lost: ?'b := 'c => 'c,
    ?F := %x. h (%z. a (x z))*)
  val F3 = Var (("F", 0), (c --> c) --> d);
  val a3 = Free ("a", bv); val h3 = Free ("h", bv --> d);
  val a3' = Free ("a", c --> c); val h3' = Free ("h", (c --> c) --> d);
  val r3 = report "CE3" [F3] [(F3 $ Abs ("w", c, Bound 0), h3 $ a3)]
    [Abs ("x", c --> c, h3' $ Abs ("z", c, a3' $ (Bound 1 $ Bound 0)))];
in
  val _ = \<^assert> (map #2 [r1, r2, r3] = [true, true, true]);
end
\<close>

subsection \<open>Monomorphic problems are unaffected\<close>

text \<open>
  On the problems of \<^theory>\<open>Pure_Unify.Pure_Unify_Test\<close>, we compare the first three unifiers
  of \<^const>\<open>hounifiers\<close> and of the prototype, with a timeout of two seconds for each.
\<close>

ML \<open>
structure Poly_Compare =
struct

fun classify f g x =
  let
    fun outcome h =
      (case Exn.result (Timeout.apply (seconds 2.0) h) x of
        Exn.Res y => SOME y
      | Exn.Exn (Timeout.TIMEOUT _) => NONE
      | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else SOME (Unify_Test.exn_name exn));
  in
    (case (outcome f, outcome g) of
      (SOME a, SOME b) => if a = b then "same" else "different"
    | (SOME _, NONE) => "timeout (new)"
    | (NONE, SOME _) => "timeout (old)"
    | (NONE, NONE) => "timeout (both)")
  end;

fun stats name f g xs =
  let
    val (time, cs) = Timing.timing (map (classify f g)) xs;
    val keys = distinct (op =) cs;
  in
    name ^ ": " ^ string_of_int (length xs) ^ " problems, " ^
      commas (map (fn k => string_of_int (length (filter (fn c => c = k) cs)) ^ " " ^ k) keys) ^
      "; time " ^ Time.toString (#elapsed time) ^ "s"
  end;

end;
\<close>

ML \<open>
local
  val thy = \<^theory>;
  val context = Context.Proof (\<^context>
    |> Context_Position.set_visible false
    |> Config.put Unify.search_bound 10);
  val ups = Unify_Test.unif_problems thy 500 2;
  fun mono ((t, u), _) = null (Term.add_tvars t []) andalso null (Term.add_tvars u []);
  val (mon, poly) = List.partition mono ups;
  val old = fn ((t, u), env) =>
    Unify_Test.take_seq 3 Unify_Test.dump_unifier (Unify_New.hounifiers [] (context, env, [(t, u)]));
  val new = fn ((t, u), env) =>
    Unify_Test.take_seq 3 Unify_Test.dump_unifier (Unify_Poly.hounifiers [] (context, env, [(t, u)]));
  val sm = Poly_Compare.stats "monomorphic problems" old new mon;
  val sp = Poly_Compare.stats "polymorphic problems (every fifth)" old new
    (map_filter (fn (i, x) => if i mod 5 = 0 then SOME x else NONE) (map_index I poly));
in
  val _ = writeln (sm ^ "\n" ^ sp);
  val _ = \<^assert> (forall (fn x => Poly_Compare.classify old new x = "same") mon);
end
\<close>

subsection \<open>Where the unifiers come from\<close>

ML \<open>
local
  open Poly_Test;
  val b = TFree ("'b", []);
  val a = TVar (("'a", 0), []);
  val F1 = Var (("F", 0), a --> b); val G1 = Var (("G", 0), a);
  val c1 = Free ("c", b);
  val _ = bound := 4;
  val new = results Unify_Poly.hounifiers [(F1 $ G1, c1)];
in
  val _ = writeln (cat_lines (map_index (fn (i, u) => string_of_int i ^ ": " ^ show [F1, G1] u) new));
end
\<close>

end
