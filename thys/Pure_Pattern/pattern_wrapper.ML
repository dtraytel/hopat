(*  Title:      pattern_wrapper.ML

The operations of signature PATTERN (src/Pure/pattern.ML) on top of the code generated
from theory Pure_Pattern_Code (structure Pattern_Generated).  Only the tracing of failures
(option unify_trace_failure) and the translation of exceptions are implemented here.

The replacement of src/Pure/pattern.ML consists of the generated code, this functor, and

  structure Pattern =
    Pattern_Fun(val unify_trace_failure =
      Config.declare_bool ("unify_trace_failure", \<^here>) (K false));
*)

signature PATTERN_GENERATED =
sig
  exception Unif
  exception Pattern
  val unify_trace_failure: bool Config.T
  val unify_types: Context.generic -> typ * typ -> Envir.env -> Envir.env
  val unify: Context.generic -> term * term -> Envir.env -> Envir.env
  exception MATCH
  val match: theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
  val first_order_match: theory -> term * term
    -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
  val pattern: term -> bool
end;

functor Pattern_Fun(val unify_trace_failure: bool Config.T): PATTERN_GENERATED =
struct

structure G = Pattern_Generated;

exception Unif;
exception Pattern;
exception MATCH;

val unify_trace_failure = unify_trace_failure;


(* tracing, as in src/Pure/pattern.ML *)

fun string_of_term ctxt env binders t =
  Syntax.string_of_term ctxt (Envir.norm_term env (subst_bounds (map Free binders, t)));

fun bname binders i = fst (nth binders i);
fun bnames binders is = implode_space (map (bname binders) is);

fun typ_clash context (tye,T,U) =
  let
    val ctxt = Context.proof_of context;
    val t = Syntax.string_of_typ ctxt (Envir.norm_type tye T);
    val u = Syntax.string_of_typ ctxt (Envir.norm_type tye U);
  in tracing ("The following types do not unify:\n" ^ t ^ "\n" ^ u) end;

fun clash a b = tracing ("Clash: " ^ a ^ " =/= " ^ b);

fun boundVar binders i =
  "bound variable " ^ bname binders i ^ " (depth " ^ string_of_int i ^ ")";

fun clashBB binders i j = clash (boundVar binders i) (boundVar binders j);

fun clashB binders i s = clash (boundVar binders i) s;

fun proj_fail context (env,binders,F,is,t) =
  let
    val ctxt = Context.proof_of context
    val f = Term.string_of_vname F
    val xs = bnames binders is
    val u = string_of_term ctxt env binders t
    val ys = bnames binders (subtract (op =) is (loose_bnos t))
  in
    tracing ("Cannot unify variable " ^ f ^
      " (depending on bound variables " ^ xs ^ ")\nwith term " ^ u ^
      "\nTerm contains additional bound variable(s) " ^ ys)
  end;

fun ocheck_fail context (F,t,binders,env) =
  let
    val ctxt = Context.proof_of context
    val f = Term.string_of_vname F
    val u = string_of_term ctxt env binders t
  in tracing ("Variable " ^ f ^ " occurs in term\n" ^ u ^ "\nCannot unify!\n") end;

fun trace_unif context tr =
  if Config.get_generic context unify_trace_failure then
    (case tr of
      G.No_Trace => ()
    | G.Typ_Clash (tye, T, U) => typ_clash context (tye, T, U)
    | G.Clash (a, b) => clash a b
    | G.Clash_BB (binders, i, j) => clashBB binders i j
    | G.Clash_B (binders, i, s) => clashB binders i s
    | G.Proj_Fail (env, binders, F, is, t) => proj_fail context (env, binders, F, is, t)
    | G.Ocheck_Fail (F, t, binders, env) => ocheck_fail context (F, t, binders, env))
  else ();


(* exceptions *)

(*Type.TUNIFY, Type.TYPE_MATCH and Sorts.CLASS_ERROR are caught internally and never escape;
  Sorts.class_error is abstract, so CLASS_ERROR cannot be reconstructed here*)
fun raise_exn context exn =
  (case exn of
    G.Unif tr => (trace_unif context tr; raise Unif)
  | G.Pattern => raise Pattern
  | G.Match => raise MATCH
  | G.TUnify => raise Type.TUNIFY
  | G.Type_Match => raise Type.TYPE_MATCH
  | G.Class_Error _ => raise Fail "Pattern: unexpected CLASS_ERROR"
  | G.Type_Error (msg, Ts, ts) => raise TYPE (msg, Ts, ts)
  | G.Term_Error (msg, ts) => raise TERM (msg, ts)
  | G.Failure msg => raise Fail msg
  | G.Subscript => raise Subscript
  | G.Unequal_Lengths => raise ListPair.UnequalLengths
  | G.Dup xi => raise Vartab.DUP xi);

fun run context r =
  (case r of
    SOME (G.Ok x) => x
  | SOME (G.Err exn) => raise_exn context exn
  | NONE => raise Fail "Pattern: undefined result");


(* operations *)

fun unify_types context (T, U) env =
  run context (G.unify_types (Sign.classes_of (Context.theory_of context)) T U env);

fun unify context (t, u) env =
  run context (G.unify (Sign.classes_of (Context.theory_of context)) t u env);

fun match thy (pat, obj) env =
  run (Context.Theory thy) (G.match (Sign.classes_of thy) pat obj env);

fun first_order_match thy (pat, obj) env =
  run (Context.Theory thy) (G.first_order_match (Sign.classes_of thy) pat obj env);

val pattern = G.pattern;

end;
