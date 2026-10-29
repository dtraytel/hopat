(*  Title:      bicompose_wrapper.ML

The function bicompose_aux of src/Pure/thm.ML on top of the code generated from theory
Pure_Bicompose_Code (structure Bicompose_Generated).  It replaces bicompose_aux in the
structure Thm, where the type thm is concrete.  Only the following is implemented here:
the operations that the model is parameterised by (Pure's Unify.unifiers, Seq.pull and
Name.variant_list []), the printing of the tracing messages, the translation of exceptions,
the conversion of the result sequence into Seq.seq, and the construction of the theorems
(derivations and proof terms, hypotheses, sort hypotheses and constraints, certificates)
from the results of the model.
*)

(*Composition of object rule r=(A1...Am/B) with proof state s=(B1...Bn/C)
  Unifies B with Bi, replacing subgoal i    (1 <= i <= n)
  If match then forbid instantiations in proof state
  If lifted then shorten the dpair using strip_assums2.
  If eres_flg then simultaneously proves A1 by assumption.
  nsubgoal is the number of new subgoals (written m above).
  Curried so that resolution calls dest_state only once.
*)
local

structure G = Bicompose_Generated;

fun typ_clash context (tye, T, U) =
  if Config.get_generic context Pattern.unify_trace_failure then
    let
      val ctxt = Context.proof_of context;
      val t = Syntax.string_of_typ ctxt (Envir.norm_type tye T);
      val u = Syntax.string_of_typ ctxt (Envir.norm_type tye U);
    in tracing ("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ();

(*the model only emits failures of type unification; the unifier traces itself*)
fun event context ev =
  (case ev of
    G.Ev_Unif (G.Typ_Clash (tye, T, U)) => typ_clash context (tye, T, U)
  | _ => ());

(*Sorts.class_error is abstract, so CLASS_ERROR cannot be reconstructed here*)
fun raise_exn (state, orule) exn =
  (case exn of
    G.UExn (G.PExn (G.Unif _)) => raise Pattern.Unif
  | G.UExn (G.PExn G.Pattern) => raise Pattern.Pattern
  | G.UExn (G.PExn G.Match) => raise Pattern.MATCH
  | G.UExn (G.PExn G.TUnify) => raise Type.TUNIFY
  | G.UExn (G.PExn G.Type_Match) => raise Type.TYPE_MATCH
  | G.UExn (G.PExn (G.Class_Error _)) => raise Fail "bicompose: unexpected CLASS_ERROR"
  | G.UExn (G.PExn (G.Type_Error (msg, Ts, ts))) => raise TYPE (msg, Ts, ts)
  | G.UExn (G.PExn (G.Term_Error (msg, ts))) => raise TERM (msg, ts)
  | G.UExn (G.PExn (G.Failure msg)) => raise Fail msg
  | G.UExn (G.PExn G.Subscript) => raise Subscript
  | G.UExn (G.PExn G.Unequal_Lengths) => raise ListPair.UnequalLengths
  | G.UExn (G.PExn (G.Dup xi)) => raise Vartab.DUP xi
  | G.UExn G.Bind => raise Bind
  | G.UExn _ => raise Fail "bicompose: unexpected exception of the unifier"
  | G.THM (msg, i, G.Orule) => raise THM (msg, i, [orule])
  | G.THM (msg, i, G.Orule_State) => raise THM (msg, i, [orule, state])
  | G.ERROR msg => error msg
  | G.COMPOSE => raise Fail "bicompose: COMPOSE");

(*the messages of a computation are printed when it is finished*)
fun run context thms r =
  (case r of
    SOME (evs, res) =>
      (List.app (event context) evs;
        (case res of
          G.TOk x => x
        | G.TErr exn => raise_exn thms exn))
  | NONE => raise Fail "bicompose: undefined result");

(*Pure's operations as computations of the model; they raise their exceptions directly*)
fun ops context =
  G.BOps
    (fn env => fn tus => SOME ([], G.TOk (Unify.unifiers (context, env, tus))),
     fn xq => SOME ([], G.TOk (Seq.pull xq)),
     Name.variant_list []);

in

fun bicompose_aux opt_ctxt {flatten, match, incremented} (state, (stpairs, Bs, Bi, C), lifted)
    (eres_flg, orule, nsubgoal) =
  let
    val Thm (sder, {maxidx=smax, constraints = constraints2, shyps = shyps2, hyps = hyps2,
      tpairs = stpairs0, prop = sprop, ...}) = state
    and Thm (rder, {maxidx=rmax, constraints = constraints1, shyps = shyps1, hyps = hyps1,
      tpairs = rtpairs, prop = rprop, ...}) = orule
    (*How many hyps to skip over during normalization*)
    and nlift = Logic.count_prems (strip_all_body Bi) + (if eres_flg then ~1 else 0);
    val (context, cert) =
      make_context_certificate [state, orule] opt_ctxt (join_certificate2 (state, orule));
    val ops = ops context;
    fun eval r = run context (state, orule) r;
    (*the new theorem with prop = "\<lbrakk>Bs; As\<rbrakk> \<Longrightarrow> C"*)
    fun mk_thm (G.BRes (env, ntpairs, prop, A, G.NewAs (As, oldAs, ren, n))) =
      let
        val rder' =
          (case ren of
            NONE => rder
          | SOME r =>
              let fun proof p = Proofterm.map_proof_terms (G.ren_term r) I p
              in deriv_rule1 I proof rder end);
        val thy' = Context.certificate_theory cert handle ERROR msg =>
          raise CONTEXT (msg, [], [], [state, orule], Option.map Context.Proof opt_ctxt);
        val constraints' =
          union_constraints constraints1 constraints2
          |> insert_constraints_env thy' env;
        fun zproof p q =
          ZTerm.bicompose_proof thy' env smax flatten Bs As A oldAs n (nlift + 1)
            [full_prop_of state, full_prop_of orule] p q;
        fun proof p q =
          Proofterm.bicompose_proof env smax flatten Bs As A oldAs n (nlift + 1) p q;
      in
        Thm (deriv_rule2 zproof proof rder' sder,
         {tags = [],
          maxidx = Envir.maxidx_of env,
          constraints = constraints',
          shyps = Envir.insert_sorts env (Sorts.union shyps1 shyps2),
          hyps = union_hyps hyps1 hyps2,
          tpairs = ntpairs,
          prop = prop,
          cert = cert})
      end;
    fun to_seq s =
      Seq.make (fn () =>
        (case eval (G.bpull ops s) of
          NONE => NONE
        | SOME (res, s') => SOME (mk_thm res, to_seq s')));
    val alg = Sign.classes_of (Context.theory_of context);
  in
    to_seq (eval (G.bicompose_aux ops alg flatten match incremented (smax, (stpairs0, sprop))
      (stpairs, (Bs, (Bi, C))) lifted eres_flg (rmax, (rtpairs, rprop)) nsubgoal))
  end;

end;
