(*  Title:      unify_wrapper.ML

The operations of signature UNIFY (src/Pure/unify.ML) on top of the code generated from
theory Pure_Unify_Code (structure Unify_Generated).  Only the following is implemented here:
the conversion of the sequences of the model into Seq.seq, the printing of the tracing
messages, the translation of exceptions, and unifiers and smash_unifiers, which call
Pure's Pattern.unify (as in the model, with the model of pattern.ML).

The replacement of src/Pure/unify.ML consists of the signature UNIFY (identical to
UNIFY_GENERATED), the generated code, this functor, and the declaration of the
configuration options:

  structure Unify: UNIFY =
    Unify_Fun(
      val search_bound = Config.declare_int ("unify_search_bound", \<^here>) (K 60)
      val unify_trace = Config.declare_bool ("unify_trace", \<^here>) (K false)
      val unify_trace_bound = Config.declare_int ("unify_trace_bound", \<^here>) (K 50)
      val unify_trace_simp = Config.declare_bool ("unify_trace_simp", \<^here>) (K false)
      val unify_trace_types = Config.declare_bool ("unify_trace_types", \<^here>) (K false));
*)

signature UNIFY_GENERATED =
sig
  val search_bound: int Config.T
  val unify_trace: bool Config.T
  val unify_trace_bound: int Config.T
  val unify_trace_simp: bool Config.T
  val unify_trace_types: bool Config.T
  val hounifiers: (string * typ) list -> Context.generic * Envir.env * ((term * term) list) ->
    (Envir.env * (term * term) list) Seq.seq
  val unifiers: Context.generic * Envir.env * ((term * term) list) ->
    (Envir.env * (term * term) list) Seq.seq
  val smash_unifiers: Context.generic -> (term * term) list -> Envir.env -> Envir.env Seq.seq
end;

functor Unify_Fun(
  val search_bound: int Config.T
  val unify_trace: bool Config.T
  val unify_trace_bound: int Config.T
  val unify_trace_simp: bool Config.T
  val unify_trace_types: bool Config.T): UNIFY_GENERATED =
struct

structure G = Unify_Generated;

val search_bound = search_bound;
val unify_trace = unify_trace;
val unify_trace_bound = unify_trace_bound;
val unify_trace_simp = unify_trace_simp;
val unify_trace_types = unify_trace_types;


(* tracing, as in src/Pure/unify.ML and src/Pure/pattern.ML *)

fun cond_tracing ctxt msg =
  if Config.get_generic ctxt unify_trace andalso Context_Position.is_visible_generic ctxt then
    tracing (msg ())
  else ();

fun typ_clash context (tye, T, U) =
  if Config.get_generic context Pattern.unify_trace_failure then
    let
      val ctxt = Context.proof_of context;
      val t = Syntax.string_of_typ ctxt (Envir.norm_type tye T);
      val u = Syntax.string_of_typ ctxt (Envir.norm_type tye U);
    in tracing ("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ();

(*disagreement pairs of the model are nested pairs (rbinder, (t, u))*)
fun print_dpairs context msg (env, dpairs) =
  let
    fun pdp (rbinder, (t, u)) =
      let
        val ctxt = Context.proof_of context;
        fun termT t =
          Syntax.pretty_term ctxt (Envir.norm_term env (Logic.rlist_abs (rbinder, t)));
      in Pretty.string_of (Pretty.block0 [termT u, Pretty.str " \<equiv>\<^sup>?", Pretty.brk 1, termT t]) end;
  in
    cond_tracing context (fn () => msg);
    List.app (fn dp => cond_tracing context (fn () => pdp dp)) dpairs
  end;

fun event context ev =
  (case ev of
    G.Ev_Unif (G.Typ_Clash (tye, T, U)) => typ_clash context (tye, T, U)
  | G.Ev_Unif _ => ()
  | G.Ev_Loss (T, U) =>
      let
        fun msg () =
          let val str_of = Syntax.string_of_typ (Context.proof_of context)
          in "Potential loss of completeness: " ^ str_of U ^ " = " ^ str_of T end
      in cond_tracing context msg end
  | G.Ev_Dpairs (msg, env, dpairs) => print_dpairs context msg (env, dpairs)
  | G.Ev_Failure_Node => cond_tracing context (fn () => "Failure node")
  | G.Ev_Bound_Exceeded =>
      if Context_Position.is_visible_generic context then
        warning "Unification bound exceeded -- see unify trace for details"
      else ());


(* exceptions *)

exception CANTUNIFY;
exception ASSIGN;
exception CHANGE_FAIL;

(*Sorts.class_error is abstract, so CLASS_ERROR cannot be reconstructed here*)
fun raise_exn exn =
  (case exn of
    G.PExn (G.Unif _) => raise Pattern.Unif
  | G.PExn G.Pattern => raise Pattern.Pattern
  | G.PExn G.Match => raise Pattern.MATCH
  | G.PExn G.TUnify => raise Type.TUNIFY
  | G.PExn G.Type_Match => raise Type.TYPE_MATCH
  | G.PExn (G.Class_Error _) => raise Fail "Unify: unexpected CLASS_ERROR"
  | G.PExn (G.Type_Error (msg, Ts, ts)) => raise TYPE (msg, Ts, ts)
  | G.PExn (G.Term_Error (msg, ts)) => raise TERM (msg, ts)
  | G.PExn (G.Failure msg) => raise Fail msg
  | G.PExn G.Subscript => raise Subscript
  | G.PExn G.Unequal_Lengths => raise ListPair.UnequalLengths
  | G.PExn (G.Dup xi) => raise Vartab.DUP xi
  | G.CANTUNIFY => raise CANTUNIFY
  | G.ASSIGN => raise ASSIGN
  | G.CHANGE_FAIL => raise CHANGE_FAIL
  | G.Bind => raise Bind);

(*the messages of a computation are printed when it is finished*)
fun run context r =
  (case r of
    SOME (evs, res) =>
      (List.app (event context) evs;
        (case res of
          G.UOk x => x
        | G.UErr exn => raise_exn exn))
  | NONE => raise Fail "Unify: undefined result");


(* sequences *)

fun cfg_of context =
  G.Cfg (Sign.classes_of (Context.theory_of context),
    Config.get_generic context search_bound,
    Config.get_generic context unify_trace_bound,
    Config.get_generic context unify_trace_simp,
    Config.get_generic context unify_trace_types);

fun to_seq context cfg s =
  Seq.make (fn () =>
    (case run context (G.pull cfg s) of
      NONE => NONE
    | SOME (G.El_R (env, tpairs), s') => SOME ((env, tpairs), to_seq context cfg s')
    | SOME _ => raise Fail "Unify: unexpected element"));


(* operations *)

fun hounifiers binders (context, env, tus) =
  to_seq context (cfg_of context) (G.hounifiers binders env tus);

fun unifiers (params as (context, env, tus)) =
  Seq.cons (fold (Pattern.unify context) tus env, []) Seq.empty
    handle Pattern.Unif => Seq.empty
      | Pattern.Pattern => hounifiers [] params;

fun smash_unifiers context tus env =
  Seq.map (fn et => run context (G.smash_flexflex et)) (unifiers (context, env, tus));

end;
