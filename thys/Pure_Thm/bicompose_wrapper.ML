(*  Title:      bicompose_wrapper.ML

The functions lift_rule, bicompose_aux and biresolution of src/Pure/thm.ML on top of the code
generated from theory Pure_Bicompose_Code (structure Bicompose_Generated).  They replace these
functions in the structure Thm, where the type thm is concrete.  Only the following is
implemented here: the operations that the model is parameterised by (Pure's Unify.unifiers,
Seq.pull and Name.variant_list []), the printing of the tracing messages, the translation of
exceptions, the conversion of the result sequences into Seq.seq, and the construction of the
theorems (derivations and proof terms, hypotheses, sort hypotheses and constraints,
certificates) from the results of the model.

The file has two parts: lift_rule, which replaces the function of the same name, and the
resolution part, which replaces bicompose_aux and its auxiliary functions; the original
biresolution and could_bires are dropped.
*)

(*** tight proofs: type arguments of constants, exceptions ***)

local

structure G = Bicompose_Generated;

in

(*Consts.typargs as a computation of the model*)
fun ztypargs thy =
  let val consts = Sign.consts_of thy in
    fn c => fn T =>
      (SOME (G.Ok (Consts.typargs consts (c, T)))
        handle TYPE (msg, Ts, ts) => SOME (G.Err (G.Type_Error (msg, Ts, ts)))
          | Subscript => SOME (G.Err G.Subscript))
  end;

(*the exceptions of session Pure_Pattern*)
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
    SOME (G.ZOk p) => p
  | SOME (G.ZErr (G.ZExn exn)) => raise_pexn exn
  | SOME (G.ZErr (G.BAD_INST inst)) => raise ZTerm.BAD_INST inst
  | SOME (G.ZErr G.ZOption) => raise Option.Option
  | NONE => raise Fail "zproof: undefined result");

end;


(*** lift_rule ***)

(*Prepare orule for resolution by lifting it over the parameters and
assumptions of goal.  The logical part of the lifted rule is computed by the generated code.*)
fun lift_rule goal orule =
  let
    val Cterm {t = gprop, T, maxidx = gmax, sorts, ...} = goal;
    val inc = gmax + 1;
    val Thm (der, {maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = orule;
    val (As, _) = Logic.strip_horn prop;
  in
    if T <> propT then raise THM ("lift_rule: the term must have type prop", 0, [])
    else
      let
        val cert = join_certificate1 (goal, orule);
        val prems = map (Logic.lift_all inc gprop) As;
        fun zproof p =
          let
            val thy = Context.certificate_theory cert
              handle ERROR msg => raise CONTEXT (msg, [], [goal], [orule], NONE);
          in
            run_zproof (Bicompose_Generated.zlift_proof (ztypargs thy) gprop inc prems p)
          end;
        fun proof p = Bicompose_Generated.lift_proof gprop inc prems p;
        val lifted =
          Bicompose_Generated.lift_rule gprop gmax (Bicompose_Generated.make maxidx tpairs prop);
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

(*the model only emits failures of type unification; the unifier traces itself*)
fun event context ev =
  (case ev of
    G.Ev_Unif (G.Typ_Clash (tye, T, U)) => typ_clash context (tye, T, U)
  | _ => ());

(*Sorts.class_error is abstract, so CLASS_ERROR cannot be reconstructed here;
  thms () are the proof state and the rule*)
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

(*the messages of a computation are printed when it is finished*)
fun run context thms r =
  (case r of
    SOME (evs, res) =>
      (List.app (event context) evs;
        (case res of
          G.TOk x => x
        | G.TErr exn => raise_exn thms exn))
  | NONE => raise Fail "bicompose: undefined result");

(*the warnings of the normalisation of a proof are printed when it is finished*)
fun run_proof thms r =
  (case r of
    SOME (ws, res) =>
      (List.app (fn s => warning ("type conflict in norm_proof:\n" ^ s)) ws;
        (case res of
          G.Ok p => p
        | G.Err exn => raise_exn thms (G.UExn (G.PExn exn))))
  | NONE => raise Fail "bicompose_proof: undefined result");

(*Pure's operations as computations of the model; they raise their exceptions directly*)
fun ops context =
  G.BOps
    (fn env => fn tus => SOME ([], G.TOk (Unify.unifiers (context, env, tus))),
     fn xq => SOME ([], G.TOk (Seq.pull xq)),
     Name.variant_list []);

(*the new theorem with prop = "\<lbrakk>Bs; As\<rbrakk> \<Longrightarrow> C"*)
fun mk_thm opt_ctxt cert flatten (state, Bs, nlift) orule
    (G.BRes (env, ntpairs, prop, A, G.NewAs (As, oldAs, ren, n))) =
  let
    val Thm (sder, {maxidx=smax, constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) =
      state
    and Thm (rder, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = orule;
    val rder' =
      (case ren of
        NONE => rder
      | SOME r =>
          let fun proof p = G.map_proof_terms (G.ren_term r) I p
          in deriv_rule1 I proof rder end);
    val thy' = Context.certificate_theory cert handle ERROR msg =>
      raise CONTEXT (msg, [], [], [state, orule], Option.map Context.Proof opt_ctxt);
    val constraints' =
      union_constraints constraints1 constraints2
      |> insert_constraints_env thy' env;
    fun zproof p q =
      run_zproof (G.zbicompose_proof (ztypargs thy') env smax flatten Bs As A oldAs n (nlift + 1)
        [full_prop_of state, full_prop_of orule] p q);
    fun proof p q =
      run_proof (fn () => (state, orule))
        (G.bicompose_proof env smax flatten Bs As A oldAs n (nlift + 1) p q);
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

fun rep_of (Thm (_, {maxidx, tpairs, prop, ...})) = G.make maxidx tpairs prop;

in

fun bicompose_aux opt_ctxt {flatten, match, incremented} (state, (stpairs, Bs, Bi, C), lifted)
    (eres_flg, orule, nsubgoal) =
  let
    val Thm (_, {maxidx=smax, tpairs = stpairs0, prop = sprop, ...}) = state
    and Thm (_, {maxidx=rmax, tpairs = rtpairs, prop = rprop, ...}) = orule
    (*How many hyps to skip over during normalization*)
    and nlift = Logic.count_prems (strip_all_body Bi) + (if eres_flg then ~1 else 0);
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
  Puts the rule above:  rule/state.  Renames vars in the rules.
  A step of pulling the result sequence evaluates the computation of one rule, whose
  lifted form is the rule of the exceptions of the step.*)
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
            let val nlift = Logic.count_prems (strip_all_body Bi) + (if eres_flg then ~1 else 0)
            in SOME (mk_thm opt_ctxt cert true (state, Bs, nlift) (Lazy.force orule) res, to_seq s') end)
      end
    and to_seq s = Seq.make (fn () => pull s);
  in to_seq s0 end;

end;
