(*  Title:      bicompose_wrapper.ML

lift_rule, bicompose_aux and biresolution of src/Pure/thm.ML on top of the code generated
from theory Pure_Bicompose_Code.
*)

(*** tight proofs: type arguments of constants, exceptions ***)

local

structure G = Bicompose_Generated;

in

fun ztypargs thy =
  let val consts = Sign.consts_of thy in
    fn c => fn T =>
      (SOME (G.Ok (Consts.typargs consts (c, T)))
        handle TYPE (msg, Ts, ts) => SOME (G.Err (G.Type_Error (msg, Ts, ts)))
          | Subscript => SOME (G.Err G.Subscript))
  end;

fun raise_pexn exn =
  (case exn of
    G.Unif _ => raise Pattern.Unif
  | G.Pattern => raise Pattern.Pattern
  | G.Match => raise Pattern.MATCH
  | G.TUnify => raise Type.TUNIFY
  | G.Type_Match => raise Type.TYPE_MATCH
  | G.Class_Error _ => raise Fail "bicompose: unexpected CLASS_ERROR"
  | G.Type_Error (msg, Ts, ts) => raise TYPE (msg, Ts, ts)
  | G.Term_Error (msg, ts) => raise TERM (msg, ts)
  | G.Failure msg => raise Fail msg
  | G.Subscript => raise Subscript
  | G.Unequal_Lengths => raise ListPair.UnequalLengths
  | G.Dup xi => raise Vartab.DUP xi);

fun run_zproof r =
  (case r of
    SOME (G.Ok p) => p
  | SOME (G.Err (G.ZExn exn)) => raise_pexn exn
  | SOME (G.Err (G.BAD_INST inst)) => raise ZTerm.BAD_INST inst
  | SOME (G.Err G.ZOption) => raise Option.Option
  | NONE => raise Fail "zproof: undefined result");

end;


(*** lift_rule ***)

(*Prepare orule for resolution by lifting it over the parameters and
assumptions of goal.  The logical part of the lifted rule is computed by the generated code.*)
fun lift_rule goal orule =
  let
    val Cterm {t = gprop, T, maxidx = gmax, sorts, ...} = goal;
    val Thm (der, {maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = orule;
  in
    if T <> propT then raise THM ("lift_rule: the term must have type prop", 0, [])
    else
      let
        val cert = join_certificate1 (goal, orule);
        val rep = Bicompose_Generated.make maxidx tpairs prop;
        fun zproof p =
          let
            val thy = Context.certificate_theory cert
              handle ERROR msg => raise CONTEXT (msg, [], [goal], [orule], NONE);
          in
            run_zproof (Bicompose_Generated.lift_rule_zproof (ztypargs thy) gprop gmax rep p)
          end;
        fun proof p = Bicompose_Generated.lift_rule_proof gprop gmax rep p;
        val lifted = Bicompose_Generated.lift_rule gprop gmax rep;
      in
        Thm (deriv_rule1 zproof proof der,
         {cert = cert,
          tags = [],
          maxidx = Bicompose_Generated.th_maxidx lifted,
          constraints = constraints,
          shyps = Sorts.union shyps sorts,  (*sic!*)
          hyps = hyps,
          tpairs = Bicompose_Generated.th_tpairs lifted,
          prop = Bicompose_Generated.th_prop lifted})
      end
  end;

(*** RESOLUTION ***)

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

fun event context ev =
  (case ev of
    G.Ev_Unif (G.Typ_Clash (tye, T, U)) => typ_clash context (tye, T, U)
  | _ => ());

fun raise_exn thms exn =
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
  | G.THM (msg, i, G.Orule) => raise THM (msg, i, [#2 (thms ())])
  | G.THM (msg, i, G.Orule_State) => raise THM (msg, i, [#2 (thms ()), #1 (thms ())])
  | G.THM (msg, i, G.State) => raise THM (msg, i, [#1 (thms ())])
  | G.ERROR msg => error msg
  | G.COMPOSE => raise Fail "bicompose: COMPOSE");

fun run context thms r =
  (case r of
    SOME (evs, res) =>
      (List.app (event context) evs;
        (case res of
          G.Ok x => x
        | G.Err exn => raise_exn thms exn))
  | NONE => raise Fail "bicompose: undefined result");

fun run_proof thms r =
  (case r of
    SOME (ws, res) =>
      (List.app (fn s => warning ("type conflict in norm_proof:\n" ^ s)) ws;
        (case res of
          G.Ok p => p
        | G.Err exn => raise_exn thms (G.UExn (G.PExn exn))))
  | NONE => raise Fail "bicompose_proof: undefined result");

fun ops context =
  G.BOps
    (fn env => fn tus => SOME ([], G.Ok (Unify.unifiers (context, env, tus))),
     fn xq => SOME ([], G.Ok (Seq.pull xq)),
     Name.variant_list []);

fun rep_of (Thm (_, {maxidx, tpairs, prop, ...})) = G.make maxidx tpairs prop;

fun mk_thm opt_ctxt cert flatten (state, Bs, nlift) orule
    (res as G.BRes (env, ntpairs, prop, _, _)) =
  let
    val Thm (sder, {constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) = state
    and Thm (rder, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = orule;
    val thy' = Context.certificate_theory cert handle ERROR msg =>
      raise CONTEXT (msg, [], [], [state, orule], Option.map Context.Proof opt_ctxt);
    val constraints' =
      union_constraints constraints1 constraints2
      |> insert_constraints_env thy' env;
    fun zproof p q =
      run_zproof
        (G.bres_zproof (ztypargs thy') (rep_of state) Bs nlift flatten (rep_of orule) res p q);
    fun proof p q =
      run_proof (fn () => (state, orule)) (G.bres_proof (rep_of state) Bs nlift flatten res p q);
  in
    Thm (deriv_rule2 zproof proof rder sder,
     {tags = [],
      maxidx = Envir.maxidx_of env,
      constraints = constraints',
      shyps = Envir.insert_sorts env (Sorts.union shyps1 shyps2),
      hyps = union_hyps hyps1 hyps2,
      tpairs = ntpairs,
      prop = prop,
      cert = cert})
  end;

in

fun bicompose_aux opt_ctxt {flatten, match, incremented} (state, (stpairs, Bs, Bi, C), lifted)
    (eres_flg, orule, nsubgoal) =
  let
    val Thm (_, {maxidx=smax, tpairs = stpairs0, prop = sprop, ...}) = state
    and Thm (_, {maxidx=rmax, tpairs = rtpairs, prop = rprop, ...}) = orule
    (*How many hyps to skip over during normalization*)
    and nlift = G.bres_nlift Bi eres_flg;
    val (context, cert) =
      make_context_certificate [state, orule] opt_ctxt (join_certificate2 (state, orule));
    val ops = ops context;
    fun eval r = run context (fn () => (state, orule)) r;
    fun to_seq s =
      Seq.make (fn () =>
        (case eval (G.bpull ops s) of
          NONE => NONE
        | SOME (res, s') => SOME (mk_thm opt_ctxt cert flatten (state, Bs, nlift) orule res, to_seq s')));
    val alg = Sign.classes_of (Context.theory_of context);
  in
    to_seq (eval (G.bicompose_aux ops alg flatten match incremented (smax, (stpairs0, sprop))
      (stpairs, (Bs, (Bi, C))) lifted eres_flg (rmax, (rtpairs, rprop)) nsubgoal))
  end;

(*Bi-resolution of a state with a list of (flag,rule) pairs.
  Puts the rule above:  rule/state.  Renames vars in the rules. *)
fun biresolution opt_ctxt match brules i state =
  let
    val context0 = make_context [state] opt_ctxt (cert_of state);
    val trace = Config.get_generic context0 Pattern.unify_trace_failure;
    val s0 =
      run context0 (fn () => (state, state))
        (G.biresolution trace match rep_of brules i (rep_of state));
    val (_, Bs, Bi, _) = dest_state (state, i);
    val lift = lift_rule (cprem_of state i);
    fun pull s =
      let
        val orule = Lazy.lazy (fn () =>
          (case G.brrule s of SOME (_, rule) => lift rule | NONE => state));
        val (context, cert) =
          (case G.brrule s of
            SOME _ =>
              make_context_certificate [state, Lazy.force orule] opt_ctxt
                (join_certificate2 (state, Lazy.force orule))
          | NONE => (context0, cert_of state));
        val alg = Sign.classes_of (Context.theory_of context);
      in
        (case run context (fn () => (state, Lazy.force orule)) (G.brstep (ops context) alg rep_of s) of
          G.RS_Done => NONE
        | G.RS_Skip s' => pull s'
        | G.RS_Result ((res, (eres_flg, _)), s') =>
            SOME (mk_thm opt_ctxt cert true (state, Bs, G.bres_nlift Bi eres_flg) (Lazy.force orule) res,
              to_seq s'))
      end
    and to_seq s = Seq.make (fn () => pull s);
  in to_seq s0 end;

end;
