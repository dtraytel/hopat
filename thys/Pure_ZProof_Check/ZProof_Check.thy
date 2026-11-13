section \<open>Checking the Tight Proofs of the Kernel\<close>

theory ZProof_Check
  imports "Pure_Pattern.Pure_Test_Support"
begin

text \<open>
  A test of the tight proofs that the inference rules of the running Isabelle build, which does
  not use the models: \<open>zprop\<close> computes the proposition that a tight proof proves and fails if
  the proof is not well-formed (an application to a term of the wrong type, to a proof of
  another proposition, or of something that is no quantification or implication). An instance
  of a proof constant proves its proposition under the type instances and the instances of the
  variables that the constant records, so the type instances count (the proof judgment of
  session \<open>Thm_Correctness\<close> does not look at those of the equality axioms), and the instance
  of a variable must have the type of the variable under the type instances. Propositions are
  compared modulo \<open>\<alpha>\<beta>\<eta>\<close>, and the result must be a certified term.

  The theorems are derived by the rules from oracle copies of propositions of HOL, so that every
  proof is complete. With all patches, every tight proof must prove the proposition of its
  theorem from its hypotheses. Without them, the test reports the failures and requires some
  (the release builds wrong tight proofs, see \<^verbatim>\<open>patches/\<close>).
\<close>

ML \<open>
structure ZProof_Check =
struct

val norm = Envir.beta_eta_contract;
fun eq (t, u) = norm t aconv norm u;

fun dest_all t =
  (case Envir.beta_norm t of
    Const ("Pure.all", _) $ Abs (_, T, b) => (T, fn u => Term.subst_bound (u, b))
  | Const ("Pure.all", Type (_, [Type (_, [T, _]), _])) $ f => (T, fn u => f $ u)
  | _ => raise Fail "application to a term: no quantification");

fun dest_imp t =
  (case Envir.beta_norm t of
    Const ("Pure.imp", _) $ A $ B => (A, B)
  | _ => raise Fail "application to a proof: no implication");

(*Ts: the types of the bound variables, Hs: the propositions of the bound proofs*)
fun zprop thy Ts Hs prf =
  (case prf of
    ZBoundp i => nth Hs i
  | ZAbsp (_, t, p) =>
      let val A = ZTerm.term_of thy t in Logic.mk_implies (A, zprop thy Ts (A :: Hs) p) end
  | ZAbst (a, T, p) =>
      let val T' = ZTerm.typ_of T
      in Logic.all_const T' $ Abs (a, T', zprop thy (T' :: Ts) (map (Term.incr_boundvars 1) Hs) p) end
  | ZAppt (p, t) =>
      let
        val (T, inst) = dest_all (zprop thy Ts Hs p);
        val u = ZTerm.term_of thy t;
        val _ = Term.fastype_of1 (Ts, u) = T orelse raise Fail "application to a term of another type";
      in Envir.beta_norm (inst u) end
  | ZAppp (p, q) =>
      let val (A, B) = dest_imp (zprop thy Ts Hs p) in
        if eq (A, zprop thy Ts Hs q) then B
        else raise Fail "application to a proof of another proposition"
      end
  | ZConstp ((_, A), (instT, inst)) =>
      (*the proposition of the constant under its instances; variables with index ~1 are the
        free (type) variables of the proposition*)
      let
        fun atyp (T as TVar (v, S)) = (case ZTVars.lookup instT (v, S) of SOME U => ZTerm.typ_of U | NONE => T)
          | atyp (T as TFree (a, S)) =
              (case ZTVars.lookup instT ((a, ~1), S) of SOME U => ZTerm.typ_of U | NONE => T)
          | atyp T = T;
        val typ = Term.map_atyps atyp;
        fun var lev v T t =
          (case ZVars.lookup inst (v, ZTerm.ztyp_of T) of
            SOME u =>
              let
                val u' = ZTerm.term_of thy u;
                val _ = Term.fastype_of1 (Ts, u') = T orelse
                  raise Fail "instance of a variable of a proof constant of another type";
              in Term.incr_boundvars lev u' end
          | NONE => t);
        fun term lev (Var (v, T)) = let val T' = typ T in var lev v T' (Var (v, T')) end
          | term lev (Free (x, T)) = let val T' = typ T in var lev (x, ~1) T' (Free (x, T')) end
          | term _ (Const (c, T)) = Const (c, typ T)
          | term lev (Abs (a, T, b)) = Abs (a, typ T, term (lev + 1) b)
          | term lev (t $ u) = term lev t $ term lev u
          | term _ t = t;
      in term 0 (ZTerm.term_of thy A) end
  | ZHyp t => ZTerm.term_of thy t
  | OFCLASSp (T, c) => Logic.mk_of_class (ZTerm.typ_of T, c)
  | ZNop => raise Fail "no proof");

fun hyps_of (ZHyp t) = [t]
  | hyps_of (ZAbst (_, _, p)) = hyps_of p
  | hyps_of (ZAbsp (_, _, p)) = hyps_of p
  | hyps_of (ZAppt (p, _)) = hyps_of p
  | hyps_of (ZAppp (p, q)) = hyps_of p @ hyps_of q
  | hyps_of _ = [];

(*NONE: the tight proof proves the theorem; SOME msg otherwise*)
fun check th =
  let
    val thy = Thm.theory_of_thm th;
    val prf = Thm.zproof_of th;
  in
    (let
      val P = zprop thy [] [] prf;
      val _ = Thm.global_cterm_of thy P;
      val _ =
        forall (fn h => exists (fn h' => ZTerm.term_of thy h aconv h') (Thm.hyps_of th)) (hyps_of prf)
          orelse raise Fail "hypothesis of the proof is no hypothesis of the theorem";
    in if eq (P, Thm.prop_of th) then NONE else SOME "the proof proves another proposition" end)
    handle Fail msg => SOME msg
      | TYPE (msg, _, _) => SOME ("TYPE " ^ msg)
      | TERM (msg, _) => SOME ("TERM " ^ msg)
      | Subscript => SOME "Subscript"
  end;

end;
\<close>

ML \<open>
local
  val thy = \<^theory>;
  val cert = Thm.global_cterm_of thy;
  fun with_proofs n f x =
    let
      val proofs = ! Proofterm.proofs;
      val _ = Proofterm.proofs := n;
      val r = Exn.result f x;
      val _ = Proofterm.proofs := proofs;
    in Exn.release r end;

  fun freeze t =
    t |> Term.map_aterms (fn Var ((x, i), T) => Free (x ^ "_" ^ string_of_int i, T) | u => u)
      |> Term.map_types (Term.map_atyps (fn TVar ((a, i), S) => TFree (a ^ "_" ^ string_of_int i, S)
        | T => T));
  fun subterms (t as u $ v) = t :: subterms u @ subterms v
    | subterms (t as Abs (_, _, b)) = t :: subterms b
    | subterms t = [t];
  fun closed_subterms t = filter_out Term.is_open (subterms t);
  fun cterms ts = map_filter (try cert) ts;
  fun take_seq n f =
    (case Exn.result (Timeout.apply (seconds 5.0) (fn () => Seq.list_of (Seq.take n (f ())))) () of
      Exn.Res xs => xs
    | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else []);
  infix 4 ~~~;
  fun xs ~~~ ys = let val n = Int.min (length xs, length ys) in take n xs ~~ take n ys end;

  (*a test: the name of a rule and the theorems that it derives*)
  fun derive () =
    let
      val props =
        Global_Theory.all_thms_of thy true |> map (Thm.prop_of o snd)
        |> filter (fn t => size_of_term t < 60) |> take 400;
      (*oracle copies: theorems with complete tight proofs*)
      val ax = Skip_Proof.make_thm thy;
      val facts = map ax props;
      val frozen = map (ax o freeze) props;
      val rules = filter (fn th => Thm.nprems_of th > 0) facts;
      val cprops = map (cert o freeze) (take 200 props);
      val assumed = map Thm.assume cprops;
      val subs = cterms (maps (take 6 o closed_subterms) (take 200 props));
      val fsubs = cterms (maps (take 6 o closed_subterms o freeze) (take 200 props));
      fun eqn th =
        (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) th of
          SOME (t, u) => try ax (Logic.mk_equals (t, u))
        | NONE => NONE);
      val eqs = map_filter eqn (facts @ frozen);
      val peqs = map_filter (fn th =>
        (case try (HOLogic.dest_Trueprop o Thm.prop_of) th of
          SOME (Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [\<^typ>\<open>bool\<close>, _])) $ A $ B) =>
            try ax (Logic.mk_equals (HOLogic.mk_Trueprop A, HOLogic.mk_Trueprop B))
        | _ => NONE)) (facts @ frozen);
      fun vars_of th =
        cterms (map Var (Term.add_vars (Thm.prop_of th) []) @ map Free (Term.add_frees (Thm.prop_of th) []));
      fun tries f xs = map_filter (try f) xs;
      val refls = map Thm.reflexive (take 300 (subs @ fsubs));
      val fun_refls = filter (fn th =>
        (case Thm.prop_of th of _ $ f $ _ => can dest_funT (fastype_of f) | _ => false)) refls;
      fun comb_args th1 =
        let val T = domain_type (fastype_of (#2 (Logic.dest_equals (Thm.prop_of th1)))) in
          filter (fn th2 => fastype_of (#1 (Logic.dest_equals (Thm.prop_of th2))) = T) (eqs @ refls)
          |> take 3 |> map (pair th1)
        end;
      val fun_eqs = filter (fn th => can dest_funT (fastype_of (#1 (Logic.dest_equals (Thm.prop_of th))))) eqs;
      fun inst_of th =
        let
          val vs = take 2 (Term.add_vars (Thm.prop_of th) []);
          val Ts = take 1 (Term.add_tvars (Thm.prop_of th) []);
          val instT = TVars.make (map (fn v as (_, S) => (v, Thm.global_ctyp_of thy (TFree ("'k", S)))) Ts);
          val th' = Thm.instantiate (instT, Vars.empty) th;
          val vs' = take 2 (Term.add_vars (Thm.prop_of th') []);
        in
          [th', Thm.instantiate (TVars.empty, Vars.make (map (fn v as ((x, _), T) => (v, cert (Free (x ^ "'", T)))) vs)) th,
           Thm.instantiate (TVars.empty, Vars.make (map (fn v as ((x, i), T) => (v, cert (Var ((x, i + 3), T)))) vs')) th']
        end;
      fun gen_of th =
        let
          val frees = map #1 (Term.add_frees (Thm.prop_of th) []);
          val tfrees = map #1 (Term.add_tfrees (Thm.prop_of th) []);
          val idx = Thm.maxidx_of th + 1;
        in
          [Thm.generalize (Names.empty, Names.make_set (take 2 frees)) idx th,
           Thm.generalize (Names.make_set tfrees, Names.empty) idx th,
           Thm.generalize (Names.make_set tfrees, Names.make_set frees) idx th]
        end;
      (*states with a subgoal that has its conclusion among its assumptions*)
      fun asm_state th =
        (case Thm.prems_of th of
          Hs as _ :: _ =>
            try ax (Logic.mk_implies (Logic.list_implies (Hs, List.last Hs), Thm.concl_of th))
        | [] => NONE);
      val asm_states = map_filter asm_state (rules @ filter (fn th => Thm.nprems_of th > 0) frozen);
      val tab = fold (fn th =>
        (case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of th) handle TERM _ => Thm.concl_of th) of
          Const (c, _) => Symtab.cons_list (c, th) | _ => I)) facts Symtab.empty;
      fun res_problems st =
        Thm.prems_of st |> map_index (fn (i, Bi) =>
          (case Term.head_of (HOLogic.dest_Trueprop (Logic.strip_assums_concl Bi)
              handle TERM _ => Logic.strip_assums_concl Bi) of
            Const (c, _) => map (fn r => (r, i + 1, st)) (take 2 (Symtab.lookup_list tab c))
          | _ => [])) |> flat;
      val res = maps res_problems (take 150 rules @ take 150 (filter (fn th => Thm.nprems_of th > 0) frozen));
      val eres = maps (fn st => map (fn r => (r, 1, st)) (take 2 rules)) (take 100 asm_states);
    in
     [("oracle", facts @ frozen),
      ("assume", assumed),
      ("trivial", map Thm.trivial cprops),
      ("implies_intr", map2 Thm.implies_intr cprops assumed @
        tries (uncurry Thm.implies_intr) (cprops ~~~ facts)),
      ("implies_elim", tries (fn th => Thm.implies_elim (Thm.trivial (Thm.cprop_of th)) th) (take 200 facts) @
        tries (fn th => Thm.implies_elim th (ax (hd (Thm.prems_of th)))) (rules @ frozen)),
      ("forall_intr", maps (fn th => tries (fn v => Thm.forall_intr v th) (take 2 (vars_of th)))
        (take 150 facts @ take 150 frozen @ take 50 eqs)),
      ("forall_elim", maps (fn th => maps (fn v =>
          tries (fn t => Thm.forall_elim t (Thm.forall_intr v th))
            (filter (fn t => Thm.typ_of_cterm t = Thm.typ_of_cterm v) (take 400 (subs @ fsubs)) |> take 2))
          (take 1 (vars_of th))) (take 200 facts @ take 100 frozen)),
      ("reflexive", refls),
      ("symmetric", tries Thm.symmetric (eqs @ take 50 refls)),
      ("transitive", tries (fn th => Thm.transitive th (Thm.symmetric th)) eqs @
        tries (fn th => Thm.transitive (Thm.symmetric th) th) eqs @
        tries (fn th => Thm.transitive th (Thm.reflexive (Thm.rhs_of th))) eqs),
      ("combination", tries (uncurry Thm.combination) (maps comb_args (fun_refls @ fun_eqs))),
      ("abstract_rule", maps (fn th => tries (fn v => Thm.abstract_rule "x" v th) (take 2 (vars_of th)))
        (eqs @ take 100 refls)),
      ("equal_intr", tries (fn th =>
          let val (A, B) = Logic.dest_equals (Thm.prop_of th)
          in Thm.equal_intr (ax (Logic.mk_implies (A, B))) (ax (Logic.mk_implies (B, A))) end) peqs),
      ("equal_elim", tries (fn th =>
          Thm.equal_elim th (ax (#1 (Logic.dest_equals (Thm.prop_of th))))) peqs),
      ("beta_conversion", tries (Thm.beta_conversion true) (take 300 (subs @ fsubs)) @
        tries (Thm.beta_conversion false) (take 300 (subs @ fsubs))),
      ("eta_conversion", tries Thm.eta_conversion (take 300 (subs @ fsubs))),
      ("eta_long_conversion", tries Thm.eta_long_conversion (take 300 (subs @ fsubs))),
      ("instantiate", maps (fn th => these (try inst_of th)) (take 300 facts @ take 50 eqs)),
      ("generalize", maps (fn th => these (try gen_of th)) (take 300 frozen)),
      ("incr_indexes", map (Thm.incr_indexes 3) (take 200 facts)),
      ("varifyT_global", tries Thm.varifyT_global (take 200 frozen)),
      ("legacy_freezeT", tries Thm.legacy_freezeT (take 200 facts)),
      ("rotate_rule", tries (Thm.rotate_rule 1 1) (take 200 rules)),
      ("permute_prems", tries (Thm.permute_prems 0 1) (take 200 rules)),
      ("lift_rule", tries (fn (r, i, st) => Thm.lift_rule (Thm.cprem_of st i) r) (take 300 res)),
      ("eq_assumption", tries (Thm.eq_assumption 1) asm_states),
      ("assumption", maps (fn st => take_seq 2 (fn () => Thm.assumption NONE 1 st)) asm_states),
      ("resolution", maps (fn (r, i, st) => take_seq 2 (fn () => Thm.biresolution NONE false [(false, r)] i st)) res),
      ("resolution (match)",
        maps (fn (r, i, st) => take_seq 2 (fn () => Thm.biresolution NONE true [(false, r)] i st)) res),
      ("elim-resolution",
        maps (fn (r, i, st) => take_seq 2 (fn () => Thm.biresolution NONE false [(true, r)] i st)) eres),
      ("composition", maps (fn (r, i, st) =>
        take_seq 2 (fn () =>
          Thm.bicompose NONE {flatten = true, match = false, incremented = false} (false, r, 0) i st))
        (filter (fn (r, _, _) => Thm.nprems_of r = 0) res))]
    end;

  val tests = with_proofs 4 derive ();
  (*theorems with flex-flex pairs are left out: their tight proofs do not show the pairs*)
  val results = tests |> map (fn (name, ths) =>
    let
      val ths' = filter (null o Thm.tpairs_of) ths;
      val bad = map_filter (fn th => Option.map (pair th) (ZProof_Check.check th)) ths';
    in (name, length ths', bad) end);
  fun report (name, n, bad) =
    name ^ ": " ^ string_of_int n ^ " theorems, " ^ string_of_int (length bad) ^ " tight proofs fail" ^
    (case bad of
      (th, msg) :: _ =>
        let val t = Exact.content Exact.term (Thm.prop_of th)
        in " (" ^ msg ^ ": " ^ (if size t > 200 then String.substring (t, 0, 200) ^ " ..." else t) ^ ")" end
    | [] => "");
  val _ = writeln (cat_lines (map report results));
  val _ = writeln ("Tight proofs checked: " ^ string_of_int (fold (fn (_, n, _) => fn m => m + n) results 0) ^
    ", failures: " ^ string_of_int (fold (fn (_, _, bad) => fn m => m + length bad) results 0));
  (*every test has theorems*)
  val _ =
    (case filter (fn (_, n, _) => n = 0) results of
      [] => ()
    | empty => error ("Tests without theorems: " ^ commas_quote (map #1 empty)));
  val failures = filter (fn (_, _, bad) => not (null bad)) results;
in
  val _ =
    if Test_System.patched then
      null failures orelse error ("Tight proofs fail: " ^ commas_quote (map #1 failures))
    else not (null failures) orelse error "No tight proof fails without the patches";
end
\<close>

end
