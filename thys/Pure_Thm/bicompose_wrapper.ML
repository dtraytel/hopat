(*  Title:      bicompose_wrapper.ML

The inference rules of src/Pure/thm.ML on top of the code generated from theory
Pure_Bicompose_Code.  Each section replaces a part of thm.ML (see make_thm_ML).
*)

(*** SECTION: cterm ***)

(** generated code for certified terms **)

structure G = Bicompose_Generated;

fun cterm_raise cts exn =
  (case exn of
    G.CTERM msg => raise CTERM (msg, cts)
  | G.USED_FREE (x, t) => raise Term.USED_FREE (x, t)
  | G.UExn (G.PExn (G.Type_Error (msg, Ts, ts))) => raise TYPE (msg, Ts, ts)
  | G.UExn (G.PExn (G.Term_Error (msg, ts))) => raise TERM (msg, ts)
  | _ => raise Fail "cterm: unexpected exception");

fun cterm_run cts r =
  (case r of
    SOME (_, G.Ok x) => x
  | SOME (_, G.Err exn) => cterm_raise cts exn
  | NONE => raise Fail "cterm: undefined result");

fun cterm_rep (Cterm {t, T, maxidx, ...}) = G.CTerm (t, T, maxidx);

fun mk_cterm cert sorts (G.CTerm (t, T, maxidx)) =
  Cterm {cert = cert, t = t, T = T, maxidx = maxidx, sorts = sorts};


(* destructors *)

fun dest_comb (ct as Cterm {cert, sorts, ...}) =
  let val (c, a) = cterm_run [ct] (G.dest_comb (cterm_rep ct))
  in (mk_cterm cert sorts c, mk_cterm cert sorts a) end;

fun dest_fun (ct as Cterm {cert, sorts, ...}) =
  mk_cterm cert sorts (cterm_run [ct] (G.dest_fun (cterm_rep ct)));

fun dest_arg (ct as Cterm {cert, sorts, ...}) =
  mk_cterm cert sorts (cterm_run [ct] (G.dest_arg (cterm_rep ct)));

fun dest_fun2 (ct as Cterm {cert, sorts, ...}) =
  mk_cterm cert sorts (cterm_run [ct] (G.dest_fun2 (cterm_rep ct)));

fun dest_arg1 (ct as Cterm {cert, sorts, ...}) =
  mk_cterm cert sorts (cterm_run [ct] (G.dest_arg1 (cterm_rep ct)));

fun dest_abs_fresh x (ct as Cterm {cert, sorts, ...}) =
  let val (v, b) = cterm_run [ct] (G.dest_abs_fresh x (cterm_rep ct))
  in (mk_cterm cert sorts v, mk_cterm cert sorts b) end;

fun dest_abs_global (ct as Cterm {cert, sorts, ...}) =
  let val (v, b) = cterm_run [ct] (G.dest_abs_global Name.variant_list (cterm_rep ct))
  in (mk_cterm cert sorts v, mk_cterm cert sorts b) end;


(* constructors *)

fun rename_tvar (a, i) (Ctyp {cert, T, maxidx = _, sorts = _}) =
  let
    val S =
      (case T of
        TFree (_, S) => S
      | TVar (_, S) => S
      | _ => raise TYPE ("rename_tvar: no variable", [T], []));
    val _ = if i < 0 then raise TYPE ("rename_tvar: bad index", [TVar ((a, i), S)], []) else ();
  in Ctyp {cert = cert, T = TVar ((a, i), S), maxidx = i, sorts = [S]} end;

fun free (x, Ctyp {cert, T, maxidx, sorts}) = mk_cterm cert sorts (G.free_cterm x T maxidx);

fun var ((x, i), Ctyp {cert, T, maxidx, sorts}) =
  mk_cterm cert sorts (cterm_run [] (G.var_cterm (x, i) T maxidx));

fun apply (cf as Cterm {sorts = sorts1, ...}) (cx as Cterm {sorts = sorts2, ...}) =
  let val r = cterm_run [cf, cx] (G.apply_cterm (cterm_rep cf) (cterm_rep cx))
  in mk_cterm (join_certificate0 (cf, cx)) (G.sorts_union sorts1 sorts2) r end;

fun lambda_name (x, ct1 as Cterm {sorts = sorts1, ...}) (ct2 as Cterm {sorts = sorts2, ...}) =
  let val r = cterm_run [ct1, ct2] (G.lambda_name x (cterm_rep ct1) (cterm_rep ct2))
  in mk_cterm (join_certificate0 (ct1, ct2)) (G.sorts_union sorts1 sorts2) r end;

fun lambda (t as Cterm {sorts = sorts1, ...}) (u as Cterm {sorts = sorts2, ...}) =
  let val r = cterm_run [t, u] (G.lambda_cterm (cterm_rep t) (cterm_rep u))
  in mk_cterm (join_certificate0 (t, u)) (G.sorts_union sorts1 sorts2) r end;


(* indexes *)

fun adjust_maxidx_cterm i (ct as Cterm {cert, sorts, maxidx, ...}) =
  if maxidx = i then ct else mk_cterm cert sorts (G.adjust_maxidx_cterm i (cterm_rep ct));

fun incr_indexes_cterm i (ct as Cterm {cert, sorts, ...}) =
  mk_cterm cert sorts (cterm_run [ct] (G.incr_indexes_cterm i (cterm_rep ct)));


(*** SECTION: renamed_prop ***)

(** generated code: type arguments of constants, exceptions, evaluation **)

structure G = Bicompose_Generated;


(* the data of theorems: sort hypotheses, hypotheses, sort constraints *)

val union_hyps = G.union_hyps;
val insert_hyps = G.insert_hyps;
val remove_hyps = G.remove_hyps;

fun constraint_tord thy1 thy2 =
  (case Context.theory_id_ord (Context.theory_id thy1, Context.theory_id thy2) of
    LESS => G.LESS
  | EQUAL => G.EQUAL
  | GREATER => G.GREATER);

val to_gconstraints = map (fn {theory, typ, sort} => (theory, (typ, sort)));
val from_gconstraints = map (fn (theory, (typ, sort)) => {theory = theory, typ = typ, sort = sort});

fun union_constraints cs1 cs2 =
  from_gconstraints (G.union_constraints constraint_tord (to_gconstraints cs1) (to_gconstraints cs2));

fun insert_constraints thy TS cs =
  from_gconstraints (G.insert_constraint constraint_tord thy TS (to_gconstraints cs));

fun insert_constraints_env thy env cs =
  (case G.env_insert_constraints constraint_tord thy (Envir.type_env env) (to_gconstraints cs) of
    SOME (G.Ok cs') => from_gconstraints cs'
  | _ => raise Fail "insert_constraints_env: undefined result");


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


(* evaluation of the generated code: events, exceptions, unifiers *)

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
  | G.THM (msg, i, G.No_Thm) => raise THM (msg, i, [])
  | G.ERROR msg => error msg
  | G.COMPOSE => raise Fail "bicompose: COMPOSE"
  | G.NOT_OF_SORT _ => raise Fail "unexpected NOT_OF_SORT"
  | G.INST_CONFLICT _ => raise Fail "unexpected INST_CONFLICT"
  | G.CTERM _ => raise Fail "unexpected CTERM"
  | G.USED_FREE (x, t) => raise Term.USED_FREE (x, t));

fun run_with evf thms r =
  (case r of
    SOME (evs, res) =>
      (List.app evf evs;
        (case res of
          G.Ok x => x
        | G.Err exn => raise_exn thms exn))
  | NONE => raise Fail "bicompose: undefined result");

fun run context = run_with (event context);

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

fun no_thms () = raise Fail "no theorems";
fun run1 th r = run_with (K ()) (fn () => (th, th)) r;
fun run2 th1 th2 r = run_with (K ()) (fn () => (th2, th1)) r;
fun run0 r = run_with (K ()) no_thms r;
fun ct_rep (Cterm {t, T, maxidx, ...}) = G.CTerm (t, T, maxidx);


(*implicit alpha-conversion*)
fun renamed_prop prop' (th as Thm (der, {cert, tags, constraints, shyps, hyps, ...})) =
  let val rep = run1 th (G.renamed_prop prop' (rep_of th)) in
    Thm (der, {cert = cert, tags = tags, maxidx = G.th_maxidx rep, constraints = constraints,
      shyps = shyps, hyps = hyps, tpairs = G.th_tpairs rep, prop = G.th_prop rep})
  end;

(*** SECTION: weaken ***)

fun weaken raw_ct th =
  let
    val ct as Cterm {t = A, sorts, ...} = adjust_maxidx_cterm ~1 raw_ct;
    val Thm (der, {tags, constraints, shyps, hyps, ...}) = th;
    val rep = run1 th (G.weaken (ct_rep raw_ct) (rep_of th));
  in
    Thm (der,
     {cert = join_certificate1 (ct, th),
      tags = tags,
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = G.sorts_union sorts shyps,
      hyps = insert_hyps A hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: axiom ***)

fun run_axiom_proof r =
  (case r of
    SOME (G.Ok p) => p
  | SOME (G.Err exn) => raise_pexn exn
  | NONE => raise Fail "axiom_proof: undefined result");

fun axiom thy name =
  (case Name_Space.lookup (Theory.axiom_table thy) name of
    SOME prop =>
      let
        fun zproof () = run_zproof (G.zaxiom_proof_of (ztypargs thy) name prop);
        fun proof () = run_axiom_proof (G.axiom_proof Name.invent_global_types name prop);
        val cert = Context.Certificate thy;
        val rep = G.axiom_rule prop;
        val shyps = G.insert_term_sorts prop [];
      in
        Thm (deriv_rule0 zproof proof,
          {cert = cert, tags = [], maxidx = G.th_maxidx rep,
            constraints = [], shyps = shyps, hyps = [], tpairs = G.th_tpairs rep, prop = G.th_prop rep})
      end
  | NONE => raise THEORY ("No axiom " ^ quote name, [thy]));

(*** SECTION: strip_shyps ***)

fun run_strip_proof r =
  (case r of
    SOME (_, G.Ok p) => p
  | SOME (_, G.Err exn) => raise_pexn exn
  | NONE => raise Fail "strip_shyps: undefined result");

(*Remove extra sorts that are witnessed by type signature information*)
fun strip_shyps thm =
  (case thm of
    Thm (_, {shyps = [], ...}) => thm
  | Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, tpairs, prop}) =>
      let
        val Deriv {promises, body = PBody {oracles, thms, zboxes, zproof, proof}} = der;

        val thy = theory_of_thm thm;
        val algebra = Sign.classes_of thy;
        val le = Sorts.sort_le algebra;
        fun rel (S1, S2) = if S1 = S2 then [] else [(Term.aT S1, S2)];

        val d = the (G.strip_shyps_rep algebra (Sign.logical_types thy) shyps hyps (rep_of thm));
        val witnessed = G.sd_witnessed d;
        val non_witnessed = G.sd_non_witnessed d;
        val extra' = G.sd_extra d;

        val non_witnessed_constraints =
          non_witnessed |> maps (fn (S1, S2) =>
            let val S0 = the (find_first (fn S => le (S, S1)) extra')
            in rel (S0, S1) @ rel (S1, S2) end);

        val constraints' = constraints
          |> fold (insert_constraints thy) witnessed
          |> fold (insert_constraints thy) non_witnessed_constraints;

        val shyps' = G.sd_shyps d;

        val zproof' = run_zproof (G.zstrip_proof algebra d zproof);
        val proof' = run_strip_proof (G.strip_proof algebra d proof);
      in
        Thm (make_deriv promises oracles thms zboxes zproof' proof',
         {cert = cert, tags = tags, maxidx = maxidx, constraints = constraints',
          shyps = shyps', hyps = hyps, tpairs = tpairs, prop = prop})
      end)
  |> solve_constraints;

(*** SECTION: adjust_maxidx_thm ***)

fun adjust_maxidx_thm i
    (th as Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, ...})) =
  if maxidx = i then th
  else
    let val rep = G.adjust_maxidx_thm i (rep_of th) in
      Thm (der, {maxidx = G.th_maxidx rep, cert = cert, tags = tags, constraints = constraints,
        shyps = shyps, hyps = hyps, tpairs = G.th_tpairs rep, prop = G.th_prop rep})
    end;



(*** SECTION: assume ***)

fun thy_of cert cts ths = Context.certificate_theory cert handle ERROR msg =>
  raise CONTEXT (msg, [], cts, ths, NONE);

(*the theorem of a certified term without hypotheses*)
fun conversion_thm (ct as Cterm {cert, t, T, sorts, ...}) rep =
  let
    fun zproof () = run_zproof (G.zreflexive_proof (ztypargs (thy_of cert [ct] [])) T t);
    fun proof () = G.reflexive_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*The assumption rule A |- A*)
fun assume raw_ct =
  let
    val rep = run0 (G.assume_rule (ct_rep raw_ct));
    val ct as Cterm {cert, t = prop, sorts, ...} = adjust_maxidx_cterm ~1 raw_ct;
    fun zproof () = run_zproof (G.zassume_proof (ztypargs (thy_of cert [ct] [])) prop);
    fun proof () = Proofterm.Hyp prop;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = [],
      shyps = sorts,
      hyps = [prop],
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

fun assume_cterm A = assume A
  handle THM (msg, _, _) => raise CTERM (msg, [A]);

(*** SECTION: implies_intr ***)

(*Implication introduction*)
fun implies_intr
    (ct as Cterm {t = A, sorts, ...})
    (th as Thm (der, {hyps, constraints, shyps, ...})) =
  let
    val rep = run1 th (G.implies_intr (ct_rep ct) (rep_of th));
    val cert = join_certificate1 (ct, th);
    fun zproof p = run_zproof (G.zimplies_intr_proof (ztypargs (thy_of cert [ct] [th])) A p);
    fun proof p = G.implies_intr_proof A p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = G.sorts_union sorts shyps,
      hyps = remove_hyps A hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: implies_elim ***)

(*Implication elimination*)
fun implies_elim thAB thA =
  let
    val Thm (derA, {hyps = hypsA, constraints = constraintsA, shyps = shypsA, ...}) = thA
    and Thm (der, {hyps, constraints, shyps, ...}) = thAB;
    val rep = run2 thAB thA (G.implies_elim (rep_of thAB) (rep_of thA));
  in
    Thm (deriv_rule2 (curry ZAppp) (curry Proofterm.%%) der derA,
     {cert = join_certificate2 (thAB, thA),
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraintsA constraints,
      shyps = G.sorts_union shypsA shyps,
      hyps = union_hyps hypsA hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: forall_intr ***)

(*Forall introduction.  The Free or Var x must not be free in the hypotheses.*)
fun occs x ts tpairs =
  let fun occs t = Logic.occs (x, t)
  in exists occs ts orelse exists (occs o fst) tpairs orelse exists (occs o snd) tpairs end;

fun forall_intr
    (ct as Cterm {t = x, T, sorts, ...})
    (th as Thm (der, {constraints, shyps, hyps, ...})) =
  let
    val rep = run1 th (G.forall_intr hyps (ct_rep ct) (rep_of th));
    val a = (case x of Free (a, _) => a | Var ((a, _), _) => a | _ => raise Match);
    val cert = join_certificate1 (ct, th);
    fun zproof p = run_zproof (G.zforall_intr_proof (ztypargs (thy_of cert [ct] [th])) T a x p);
    fun proof p = G.forall_intr_proof a x p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = G.sorts_union sorts shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: forall_elim ***)

(*Forall elimination*)
fun forall_elim
    (ct as Cterm {t, sorts, ...})
    (th as Thm (der, {constraints, shyps, hyps, ...})) =
  let
    val rep = run1 th (G.forall_elim (ct_rep ct) (rep_of th));
    val cert = join_certificate1 (ct, th);
    fun zproof p = run_zproof (G.zforall_elim_proof (ztypargs (thy_of cert [ct] [th])) t p);
    fun proof p = p % SOME t;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = G.sorts_union sorts shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: reflexive ***)

(*Reflexivity*)
fun reflexive ct = conversion_thm ct (run0 (G.reflexive (ct_rep ct)));

(*** SECTION: symmetric ***)

(*Symmetry*)
fun symmetric (th as Thm (der, {cert, constraints, shyps, hyps, prop, ...})) =
  let
    val rep = run1 th (G.symmetric (rep_of th));
    val (T, t, u) = (case prop of Const (_, Type (_, [T, _])) $ t $ u => (T, t, u) | _ => raise Match);
    fun zproof p = run_zproof (G.zsymmetric_proof (ztypargs (thy_of cert [] [th])) T t u p);
  in
    Thm (deriv_rule1 zproof G.symmetric_proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: transitive ***)

(*Transitivity*)
fun transitive th1 th2 =
  let
    val Thm (der1, {hyps = hyps1, constraints = constraints1, shyps = shyps1, prop = prop1, ...}) = th1
    and Thm (der2, {hyps = hyps2, constraints = constraints2, shyps = shyps2, prop = prop2, ...}) = th2;
    val rep = run2 th1 th2 (G.transitive (rep_of th1) (rep_of th2));
    val (T, t1, u, t2) =
      (case (prop1, prop2) of
        (Const (_, Type (_, [T, _])) $ t1 $ u, _ $ _ $ t2) => (T, t1, u, t2)
      | _ => raise Match);
    val cert = join_certificate2 (th1, th2);
    fun zproof p q = run_zproof (G.ztransitive_proof (ztypargs (thy_of cert [] [th1, th2])) T t1 u t2 p q);
    fun proof p = G.transitive_proof T u p;
  in
    Thm (deriv_rule2 zproof proof der1 der2,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraints1 constraints2,
      shyps = G.sorts_union shyps1 shyps2,
      hyps = union_hyps hyps1 hyps2,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: conversions ***)

(*Beta-conversion: fully beta-reduces the term if full = true*)
fun beta_conversion full ct = conversion_thm ct (run0 (G.beta_conversion full (ct_rep ct)));

fun eta_conversion ct = conversion_thm ct (run0 (G.eta_conversion (ct_rep ct)));

fun eta_long_conversion ct = conversion_thm ct (run0 (G.eta_long_conversion (ct_rep ct)));

(*** SECTION: abstract_rule ***)

(*The abstraction rule.  The Free or Var x must not be free in the hypotheses.*)
fun abstract_rule b
    (ct as Cterm {t = x, T, sorts, ...})
    (th as Thm (der, {hyps, constraints, shyps, ...})) =
  let
    val (rep, (U, (f, g))) = run1 th (G.abstract_rule_res b hyps (ct_rep ct) (rep_of th));
    val cert = join_certificate1 (ct, th);
    fun zproof p =
      run_zproof (G.zabstract_rule_proof (ztypargs (thy_of cert [ct] [th])) T U b x f g p);
    fun proof p = G.abstract_rule_proof b x p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = G.sorts_union sorts shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: combination ***)

(*The combination rule*)
fun combination th1 th2 =
  let
    val Thm (der1, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = th1
    and Thm (der2, {constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) = th2;
    val (rep, (fT, (U, (f, (g, (t, u)))))) = run2 th1 th2 (G.combination_res (rep_of th1) (rep_of th2));
    val cert = join_certificate2 (th1, th2);
    fun zproof p q =
      run_zproof (G.zcombination_proof (ztypargs (thy_of cert [] [th1, th2])) fT U f g t u p q);
    fun proof p q = run_proof (fn () => (th2, th1)) (G.combination_proof f g t u p q);
  in
    Thm (deriv_rule2 zproof proof der1 der2,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraints1 constraints2,
      shyps = G.sorts_union shyps1 shyps2,
      hyps = union_hyps hyps1 hyps2,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: equal_intr ***)

(*Equality introduction and the equal propositions rule*)
fun gen_equal model zproof_of proof_of (A, B) th1 th2 =
  let
    val Thm (der1, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = th1
    and Thm (der2, {constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) = th2;
    val rep = run2 th1 th2 (model (rep_of th1) (rep_of th2));
    val cert = join_certificate2 (th1, th2);
    fun proof p q = proof_of (A ()) (B ()) p q;
    fun zproof p q =
      run_zproof (zproof_of (ztypargs (thy_of cert [] [th1, th2])) (A ()) (B ()) p q);
  in
    Thm (deriv_rule2 zproof proof der1 der2,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraints1 constraints2,
      shyps = G.sorts_union shyps1 shyps2,
      hyps = union_hyps hyps1 hyps2,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

fun equal_intr th1 th2 =
  let val (A, B) = (case prop_of th1 of _ $ A $ B => (A, B) | _ => (Term.dummy, Term.dummy)) in
    gen_equal G.equal_intr G.zequal_intr_proof G.equal_intr_proof (K A, K B) th1 th2
  end;

(*** SECTION: equal_elim ***)

fun equal_elim th1 th2 =
  let val (A, B) = (case prop_of th1 of _ $ A $ B => (A, B) | _ => (Term.dummy, Term.dummy)) in
    gen_equal G.equal_elim G.zequal_elim_proof G.equal_elim_proof (K A, K B) th1 th2
  end;



(*** SECTION: flexflex_generalize ***)

(*Smash unifies the list of term pairs leaving no flex-flex pairs.
  Instantiates the theorem and deletes trivial tpairs.  Resulting
  sequence may contain multiple elements if the tpairs are not all
  flex-flex.  The new theorems are computed by the generated code.*)
fun flexflex_rule opt_ctxt =
  solve_constraints #> (fn th =>
    let
      val Thm (der, {cert, constraints, shyps, hyps, ...}) = th;
      val (context, cert') = make_context_certificate [th] opt_ctxt cert;
      val ops =
        Bicompose_Generated.BOps
          (fn env => fn tus =>
            SOME ([], Bicompose_Generated.Ok (Seq.map (rpair []) (Unify.smash_unifiers context tus env))),
           fn xq => SOME ([], Bicompose_Generated.Ok (Seq.pull xq)),
           Name.variant_list []);
      fun smash (env, _) = SOME ([], Bicompose_Generated.Ok env);
      fun eval r = run context (fn () => (th, th)) r;
      val rep = rep_of th;
      fun mk (env, th') =
        if Envir.is_empty env andalso not (exists (op aconv) (tpairs_of th)) then th
        else
          let
            val thy' = Context.certificate_theory cert' handle ERROR msg =>
              raise CONTEXT (msg, [], [], [th], Option.map Context.Proof opt_ctxt);
            fun zproof p = run_zproof (Bicompose_Generated.flexflex_zproof (ztypargs thy') rep env p);
            fun proof p =
              run_proof (fn () => (th, th)) (Bicompose_Generated.norm_proof_remove_types env p);
          in
            Thm (deriv_rule1 zproof proof der,
             {cert = cert',
              tags = [],
              maxidx = Bicompose_Generated.th_maxidx th',
              constraints = insert_constraints_env thy' env constraints,
              shyps = G.env_insert_sorts (Envir.type_env env) shyps,
              hyps = hyps,
              tpairs = Bicompose_Generated.th_tpairs th',
              prop = Bicompose_Generated.th_prop th'})
          end;
      fun to_seq s =
        Seq.make (fn () =>
          (case eval (Bicompose_Generated.fpull ops smash rep s) of
            NONE => NONE
          | SOME (x, s') => SOME (mk x, to_seq s')));
    in to_seq (eval (Bicompose_Generated.flexflex_rule ops rep)) end);


(*Generalization of fixed variables
           A
  --------------------
  A[?'a/'a, ?x/x, ...]
*)

fun generalize (tfrees, frees) idx th =
  if Names.is_empty tfrees andalso Names.is_empty frees then th
  else
    let
      val Thm (der, {cert, constraints, shyps, hyps, tpairs, prop, ...}) = th;
      val tfrees' = Names.list_set tfrees and frees' = Names.list_set frees;
      val rep = run1 th (G.generalize tfrees' frees' idx hyps (rep_of th));
      val zproof = run_zproof o G.zgeneralize_proof tfrees' frees' idx;
      val proof = G.generalize_thm_proof tfrees' frees' idx tpairs prop;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert,
        tags = [],
        maxidx = G.th_maxidx rep,
        constraints = constraints,
        shyps = shyps,
        hyps = hyps,
        tpairs = G.th_tpairs rep,
        prop = G.th_prop rep})
    end;

(*** SECTION: generalize_cterm ***)

fun generalize_cterm (tfrees, frees) idx (ct as Cterm {cert, sorts, ...}) =
  if Names.is_empty tfrees andalso Names.is_empty frees then ct
  else
    mk_cterm cert sorts
      (cterm_run [ct] (G.generalize_cterm (Names.list_set tfrees) (Names.list_set frees) idx (cterm_rep ct)));

(*** SECTION: instantiate ***)

(*Left-to-right replacements: ctpairs = [..., (vi, ti), ...].
  Instantiates distinct Vars by terms of same type.
  Does NOT normalize the resulting theorem!*)
fun gen_instantiate beta (instT, inst) th =
  if TVars.is_empty instT andalso Vars.is_empty inst then th
  else
    let
      val Thm (der, {cert, hyps, constraints, shyps, ...}) = th;
      val cert' = cert
        |> TVars.fold add_instT_cert instT
        |> Vars.fold add_inst_cert inst;
      val thy' =
        Context.certificate_theory cert' handle ERROR msg =>
          raise CONTEXT (msg, TVars.dest instT |> map #2, Vars.dest inst |> map #2, [th], NONE);
      val shyps' = shyps
        |> TVars.fold (fn (_, Ctyp {sorts, ...}) => G.sorts_union sorts) instT
        |> Vars.fold (fn (_, Cterm {sorts, ...}) => G.sorts_union sorts) inst;
      val instT' = TVars.dest instT |> map (fn (v, Ctyp {T, maxidx, ...}) => (v, (T, maxidx)));
      val inst' = Vars.dest inst |> map (fn (v, Cterm {t, T, maxidx, ...}) => (v, (t, (T, maxidx))));
      val rep =
        (case G.instantiate (Sign.classes_of thy') beta instT' inst' (rep_of th) of
          SOME (_, G.Err (G.NOT_OF_SORT (_, S))) =>
            raise THM ("Type not of sort " ^ Syntax.string_of_sort_global thy' S, 0, [th])
        | SOME (_, G.Err (G.INST_CONFLICT (v as (_, T), u, U))) =>
            let
              fun pretty_typing t ty =
                Pretty.block [Syntax.pretty_term_global thy' t, Pretty.str " ::",
                  Pretty.brk 1, Syntax.pretty_typ_global thy' ty];
              val msg =
                Pretty.string_of (Pretty.big_list "instantiate: type conflict"
                 [Pretty.item [pretty_typing (Var v) T],
                  Pretty.item [pretty_typing u U]]);
            in raise THM (msg, 0, [th]) end
        | r => run1 th r);
      val constraints' =
        fold (fn ((_, S), (T, _)) => insert_constraints thy' (T, S)) instT' constraints;
      val Ts = map (fn (v, (T, _)) => (v, T)) instT';
      val ts = map (fn (v, (t, _)) => (v, t)) inst';
      fun zproof p = run_zproof (G.zinstantiate_proof (ztypargs thy') Ts ts p);
      fun proof p = G.instantiate_proof Ts ts p;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert',
        tags = [],
        maxidx = G.th_maxidx rep,
        constraints = constraints',
        shyps = shyps',
        hyps = hyps,
        tpairs = G.th_tpairs rep,
        prop = G.th_prop rep})
      |> solve_constraints
    end
    handle TYPE (msg, _, _) => raise THM (msg, 0, [th]);

val instantiate = gen_instantiate false;
val instantiate_beta = gen_instantiate true;

fun gen_instantiate_cterm beta (instT, inst) ct =
  if TVars.is_empty instT andalso Vars.is_empty inst then ct
  else
    let
      val Cterm {cert, sorts, ...} = ct;
      val cert' = cert
        |> TVars.fold add_instT_cert instT
        |> Vars.fold add_inst_cert inst;
      val thy' =
        Context.certificate_theory cert' handle ERROR msg =>
          raise CONTEXT (msg, TVars.dest instT |> map #2, Vars.dest inst |> map #2, [], NONE);
      val sorts' = sorts
        |> TVars.fold (fn (_, Ctyp {sorts, ...}) => G.sorts_union sorts) instT
        |> Vars.fold (fn (_, Cterm {sorts, ...}) => G.sorts_union sorts) inst;
      val instT' = TVars.dest instT |> map (fn (v, Ctyp {T, maxidx, ...}) => (v, (T, maxidx)));
      val inst' = Vars.dest inst |> map (fn (v, Cterm {t, T, maxidx, ...}) => (v, (t, (T, maxidx))));
      val r =
        (case G.instantiate_cterm (Sign.classes_of thy') beta instT' inst' (cterm_rep ct) of
          SOME (_, G.Err (G.NOT_OF_SORT (_, S))) =>
            raise CTERM ("Type not of sort " ^ Syntax.string_of_sort_global thy' S, [ct])
        | SOME (_, G.Err (G.INST_CONFLICT (v as (_, T), u, U))) =>
            let
              fun pretty_typing t ty =
                Pretty.block [Syntax.pretty_term_global thy' t, Pretty.str " ::",
                  Pretty.brk 1, Syntax.pretty_typ_global thy' ty];
              val msg =
                Pretty.string_of (Pretty.big_list "instantiate: type conflict"
                 [Pretty.item [pretty_typing (Var v) T],
                  Pretty.item [pretty_typing u U]]);
            in raise CTERM (msg, [ct]) end
        | r => cterm_run [ct] r);
    in mk_cterm cert' sorts' r end
    handle TYPE (msg, _, _) => raise CTERM (msg, [ct]);

val instantiate_cterm = gen_instantiate_cterm false;
val instantiate_beta_cterm = gen_instantiate_cterm true;

end;


(*** SECTION: trivial_of_class ***)

(*The trivial implication A \<Longrightarrow> A, justified by assume and forall rules.
  A can contain Vars, not so for assume!*)
fun trivial (ct as Cterm {cert, t = A, sorts, ...}) =
  let
    val rep = run0 (G.trivial (ct_rep ct));
    fun zproof () = run_zproof (G.ztrivial_proof (ztypargs (thy_of cert [ct] [])) A);
    fun proof () = G.trivial_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*Axiom-scheme reflecting signature contents
        T :: c
  -------------------
  OFCLASS(T, c_class)
*)
fun of_class (cT, raw_c) =
  let
    val Ctyp {cert, T, ...} = cT;
    val thy = Context.certificate_theory cert
      handle ERROR msg => raise CONTEXT (msg, [cT], [], [], NONE);
    val c = Sign.certify_class thy raw_c;

    val prop = Logic.mk_of_class (T, c);
    val Cterm {t = prop', sorts, ...} = global_cterm_of thy prop;

    fun zproof () = ZTerm.of_class_proof (T, c);
    fun proof () = Proofterm.PClass (T, c);
  in
    if prop <> prop' then raise THM ("of_class: bad proposition via cterm_of", 0, [])
    else
      (case G.of_class (Sign.classes_of thy) T c of
        SOME (_, G.Err (G.NOT_OF_SORT _)) =>
          raise THM ("of_class: type not of class " ^ Syntax.string_of_sort_global thy [c], 0, [])
      | r =>
          let val rep = run0 r in
            Thm (deriv_rule0 zproof proof,
             {cert = cert,
              tags = [],
              maxidx = G.th_maxidx rep,
              constraints = insert_constraints thy (T, [c]) [],
              shyps = sorts,
              hyps = [],
              tpairs = G.th_tpairs rep,
              prop = G.th_prop rep})
          end)
  end |> solve_constraints;

(*** SECTION: unconstrainT ***)

(*Sort constraints within the logic*)
val unconstrainT =
  strip_shyps #> (fn thm as Thm (der, args) =>
    let
      val Deriv {promises, body} = der;
      val {cert, shyps, hyps, prop, ...} = args;
      val thy = theory_of_thm thm;
      val rep = run1 thm (G.unconstrainT_rep Name.invent_global_types shyps hyps (rep_of thm));
      val ps = map (apsnd (Future.map fulfill_body)) promises;
      val (prop', body') = Proofterm.unconstrain_thm_proof thy (sorts_proof thy) shyps prop ps body;
      val _ = prop' = G.th_prop rep orelse raise Fail "unconstrainT: proposition";
    in
      Thm (make_deriv0 [] body',
       {cert = cert,
        tags = [],
        maxidx = G.th_maxidx rep,
        constraints = [],
        shyps = [[]],  (*potentially redundant*)
        hyps = [],
        tpairs = [],
        prop = G.th_prop rep})
    end);

(*** SECTION: varify_freeze ***)

(*Replace all TFrees not fixed or in the hyps by new TVars*)
fun varifyT_global' fixed (th as Thm (der, {cert, constraints, shyps, hyps, ...})) =
  let
    val (al, rep) =
      run1 th (G.varifyT_global Name.variant_list (TFrees.list_set fixed) hyps (rep_of th));
    fun zproof p = run_zproof (G.zvarifyT_proof al p);
    fun proof p = G.varifyT_proof al p;
  in
    (al, Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep}))
  end;

val varifyT_global = #2 o varifyT_global' TFrees.empty;

(*Replace all TVars by TFrees that are often new*)
fun legacy_freezeT (th as Thm (der, {cert, constraints, shyps, hyps, tpairs, prop, ...})) =
  let
    val rep = run1 th (G.legacy_freezeT Name.variant_list (rep_of th));
    val prop1 = attach_tpairs tpairs prop;
    fun zproof p = run_zproof (G.zlegacy_freezeT_proof Name.variant_list prop1 p);
    fun proof p = G.legacy_freezeT_proof Name.variant_list prop1 p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*** SECTION: lift_incr ***)

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
          shyps = G.sorts_union shyps sorts,  (*sic!*)
          hyps = hyps,
          tpairs = Bicompose_Generated.th_tpairs lifted,
          prop = Bicompose_Generated.th_prop lifted})
      end
  end;

fun incr_indexes i (thm as Thm (der, {cert, constraints, shyps, hyps, ...})) =
  if i < 0 then raise THM ("negative increment", 0, [thm])
  else if i = 0 then thm
  else
    let
      val rep = run1 thm (G.incr_indexes_thm i (rep_of thm));
      fun zproof p = run_zproof (G.zincr_indexes_proof i p);
      fun proof p = G.incr_indexes_proof i p;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert,
        tags = [],
        maxidx = G.th_maxidx rep,
        constraints = constraints,
        shyps = shyps,
        hyps = hyps,
        tpairs = G.th_tpairs rep,
        prop = G.th_prop rep})
    end;

(*** SECTION: assumption ***)

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  The new theorems are computed by the generated code. *)
fun assumption opt_ctxt i state =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = state;
    val (context, cert') = make_context_certificate [state] opt_ctxt cert;
    fun eval r = run context (fn () => (state, state)) r;
    val rep = rep_of state;
    val s0 = eval (Bicompose_Generated.assumption i rep);
    val ctx = Bicompose_Generated.aseq_ctx s0;
    fun mk (res as Bicompose_Generated.ARes (env, _, th')) =
      let
        val thy' = Context.certificate_theory cert' handle ERROR msg =>
          raise CONTEXT (msg, [], [], [state], Option.map Context.Proof opt_ctxt);
        fun zproof p = run_zproof (Bicompose_Generated.ares_zproof (ztypargs thy') rep ctx res p);
        fun proof p = run_proof (fn () => (state, state)) (Bicompose_Generated.ares_proof ctx res p);
      in
        Thm (deriv_rule1 zproof proof der,
         {tags = [],
          maxidx = Bicompose_Generated.th_maxidx th',
          constraints = insert_constraints_env thy' env constraints,
          shyps = G.env_insert_sorts (Envir.type_env env) shyps,
          hyps = hyps,
          tpairs = Bicompose_Generated.th_tpairs th',
          prop = Bicompose_Generated.th_prop th',
          cert = cert'})
      end;
    fun to_seq s =
      Seq.make (fn () =>
        (case eval (Bicompose_Generated.apull (ops context) s) of
          NONE => NONE
        | SOME (res, s') => SOME (mk res, to_seq s')));
  in to_seq s0 end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha/eta-convertible to one of its assumptions.
  The new theorem is computed by the generated code.*)
fun eq_assumption i state =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = state;
    val (n, th') =
      run_with (K ()) (fn () => (state, state)) (Bicompose_Generated.eq_assumption i (rep_of state));
    val (_, Bs, Bi, _) = dest_state (state, i);
    fun zproof p =
      let
        val thy = Context.certificate_theory cert
          handle ERROR msg => raise CONTEXT (msg, [], [], [state], NONE);
      in run_zproof (Bicompose_Generated.eq_assumption_zproof (ztypargs thy) Bs Bi n p) end;
    fun proof p = Bicompose_Generated.assumption_proof Bs Bi n p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = Bicompose_Generated.th_maxidx th',
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = Bicompose_Generated.th_tpairs th',
      prop = Bicompose_Generated.th_prop th'})
  end;

(*** SECTION: rotate_permute ***)

(*For rotate_tac: fast rotation of assumptions of subgoal i*)
fun rotate_rule k i state =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = state;
    val (rep, (Bs, (Bi', (params, (asms, m))))) = run1 state (G.rotate_data k i (rep_of state));
    fun zproof p =
      run_zproof (G.zrotate_proof (ztypargs (thy_of cert [] [state])) Bs Bi' params asms m p);
    fun proof p = G.rotate_proof Bs Bi' params asms m p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;


(*Rotates a rule's premises to the left by k, leaving the first j premises
  unchanged.  Does nothing if k=0 or if k equals n-j, where n is the
  number of premises.  Useful with eresolve_tac and underlies defer_tac*)
fun permute_prems j k rl =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = rl;
    val (rep, (prems', m)) = run1 rl (G.permute_data j k (rep_of rl));
    fun zproof p =
      run_zproof (G.zpermute_prems_proof (ztypargs (thy_of cert [] [rl])) prems' j m p);
    fun proof p = G.permute_prems_proof prems' j m p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;


(*** SECTION: resolution ***)

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
      shyps = G.env_insert_sorts (Envir.type_env env) (G.sorts_union shyps1 shyps2),
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
