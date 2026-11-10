section \<open>Testing the Generated Code of the Axiom Rule\<close>

theory Pure_Axiom_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated code of theory \<^theory_text>\<open>Pure_Axiom\<close> is compared with \<open>Thm.axiom\<close>,
  \<open>Proofterm.axiom_proof\<close> and \<open>ZTerm.axiom_proof\<close> on all axioms of HOL, and on their
  instances with sorts, free variables and further type variables (for \<open>Logic.unconstrainT\<close>
  and \<open>Proofterm.prop_args\<close>).
\<close>

ML \<open>
local
  structure A = Bicompose_Generated and G = Bicompose_Generated;
  val thy = \<^theory>;
  fun run r =
    (case r of
      SOME (G.Ok p) => ([], p)
    | SOME (G.Err exn) => Proofterm_Test.raise_exn exn
    | NONE => raise Fail "undefined result");
  val zrun = Proofterm_Test.zrun;
  val ta = Proofterm_Test.ztypargs thy;
  val axioms = Theory.all_axioms_of thy;
  (*further propositions: the axioms with sorts on their type variables, with free (type)
    variables, and with the type variables renamed*)
  fun sorted t = map_types (map_atyps (fn TVar (v, []) => TVar (v, [\<^class>\<open>type\<close>]) | T => T)) t;
  fun freed t =
    map_types (map_atyps (fn TVar ((a, _), S) => TFree (a, S) | T => T))
      (Term.map_aterms (fn Var ((x, _), T) => Free (x, T) | t => t) t);
  fun renamed t = map_types (map_atyps (fn TVar ((a, i), S) => TVar (("'z" ^ a, i + 1), S) | T => T)) t;
  val props = map (fn (a, t) => (a, t)) axioms @
    maps (fn (a, t) => [(a, sorted t), (a, freed t), (a, renamed t), (a, sorted (renamed t))]) axioms;
  (*the logical part: proposition, flex-flex pairs and maximal index*)
  val ax_mism = axioms |> filter_out (fn (a, t) =>
    let val th = Thm.axiom thy a and r = A.axiom_rule t
    in (Thm.prop_of th, Thm.tpairs_of th, Thm.maxidx_of th) = (A.th_prop r, A.th_tpairs r, A.th_maxidx r) end);
  val p_ax = Proofterm_Test.compare "axiom (proofs)" (fn (a, t) => a ^ " " ^ \<^make_string> t)
    (fn (a, t) => ([], Proofterm.axiom_proof a t))
    (fn (a, t) => run (A.axiom_proof Name.invent_global_types a t)) props;
  val z_ax = Proofterm_Test.zcompare "axiom (tight proofs)" (fn (a, t) => a ^ " " ^ \<^make_string> t)
    (fn (a, t) => ([], ZTerm.axiom_proof thy a t))
    (fn (a, t) => zrun (A.zaxiom_proof_of ta a t)) props;
in
  val _ = writeln ("axiom (logical part): " ^ string_of_int (length axioms) ^ " tests, " ^
    string_of_int (length ax_mism) ^ " mismatches");
  val _ = writeln (cat_lines (map Proofterm_Test.report [p_ax, z_ax]));
  val _ = null ax_mism orelse error (\<^make_string> (take 2 ax_mism));
  val _ = Proofterm_Test.check [p_ax, z_ax];
end
\<close>

end
