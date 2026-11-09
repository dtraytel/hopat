section \<open>Testing the Generated Code against the Inference Rules of \<open>Thm\<close>\<close>

theory Pure_Rules_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated code of theories \<^theory_text>\<open>Pure_Rules\<close> and
  \<^theory_text>\<open>Pure_Subst_Rules\<close> is compared with the inference rules of \<open>Thm\<close>: the
  logical content of the new theorems and the exceptions raised, as in
  \<^theory_text>\<open>Pure_Bicompose_Test\<close>, and the classic and tight proofs of the rules, from the synthetic
  proofs of \<^theory_text>\<open>Pure_Proofterm_Test_Base\<close>, with those of \<open>Proofterm\<close> and \<open>ZTerm\<close>.
  The arguments are taken from the theorems of HOL: their propositions, subterms, variables
  and types, frozen and not, and theorems derived from them by the rules themselves.
\<close>

ML \<open>
structure Rules_Test =
struct

structure G = Bicompose_Generated;

val rep_of = Bicompose_Test.rep_of;
fun result_of_rep th' : Bicompose_Test.result = (G.th_prop th', G.th_tpairs th', G.th_maxidx th');
fun ct c = G.CTerm (Thm.term_of c, Thm.typ_of_cterm c, Thm.maxidx_of_cterm c);

(*evaluation with the theorems of exceptions: one theorem, or two in order*)
fun run thy thms r =
  (case r of
    SOME (_, G.Err (G.NOT_OF_SORT (_, S))) =>
      raise THM ("Type not of sort " ^ Syntax.string_of_sort_global thy S, 0, [#1 thms])
  | SOME (_, G.Err (G.INST_CONFLICT (v as (_, T), u, U))) =>
      let
        fun pretty_typing t ty =
          Pretty.block [Syntax.pretty_term_global thy t, Pretty.str " ::",
            Pretty.brk 1, Syntax.pretty_typ_global thy ty];
        val msg =
          Pretty.string_of (Pretty.big_list "instantiate: type conflict"
           [Pretty.item [pretty_typing (Var v) T],
            Pretty.item [pretty_typing u U]]);
      in raise THM (msg, 0, [#1 thms]) end
  | _ => Bicompose_Test.run (Context.Theory thy) thms r);

fun one thy th r = run thy (th, th) r;
fun two thy th1 th2 r = run thy (th2, th1) r;
val none = Thm.reflexive (Thm.global_cterm_of \<^theory>\<open>Pure\<close> Term.dummy_prop);
fun zero thy r = run thy (none, none) r;

fun res th' = Seq.single (result_of_rep th');

(* data *)

fun closed_subterms t =
  let
    fun subs (t as u $ v) = t :: subs u @ subs v
      | subs (t as Abs (_, _, b)) = t :: subs b
      | subs t = [t];
  in filter (fn u => not (Term.is_open u)) (subs t) end;

fun cterms thy ts = map_filter (try (Thm.global_cterm_of thy)) ts;

(*rename the bound variables*)
fun rename_bounds (Abs (_, T, b)) = Abs ("z", T, rename_bounds b)
  | rename_bounds (t $ u) = rename_bounds t $ rename_bounds u
  | rename_bounds t = t;

fun show_thm th = \<^make_string> (Thm.prop_of th, Thm.tpairs_of th);
fun show_ct c = \<^make_string> (Thm.term_of c);

(*the comparisons, with their reports as they are done*)
fun compare name show f g xs =
  let val r = Bicompose_Test.compare name 3 show f g xs
  in tracing (Bicompose_Test.report r); r end;
fun timed_report name cmp =
  let val (t, r) = Timing.timing cmp ()
  in tracing (Proofterm_Test.report r ^ "; time " ^ Time.toString (#elapsed t) ^ "s"); r end;
fun pcompare name show f g xs = timed_report name (fn () => Proofterm_Test.compare name show f g xs);
fun zcompare name show f g xs = timed_report name (fn () => Proofterm_Test.zcompare name show f g xs);

end;
\<close>

ML \<open>
local
  open Rules_Test;
  infix 4 ~~~;
  fun xs ~~~ ys = let val n = Int.min (length xs, length ys) in take n xs ~~ take n ys end;
  val thy = \<^theory>;
  val ctxt = \<^context> |> Context_Position.set_visible false;
  val alg = Sign.classes_of thy;
  val ta = Proofterm_Test.ztypargs thy;
  fun take_list n xq =
    (case Exn.result (Timeout.apply (seconds 5.0) (fn () => Seq.list_of (Seq.take n xq))) () of
      Exn.Res xs => xs
    | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else []);
  val facts = Global_Theory.all_thms_of thy true |> map (Thm.transfer thy o snd) |> take 300;
  val rules = filter (fn th => Thm.nprems_of th > 0) facts;
  val props = map Thm.cprop_of (take 600 facts);
  val fprops = cterms thy (map (Bicompose_Test.freeze o Thm.prop_of) (take 600 facts));
  val subterms = cterms thy (maps (take 8 o closed_subterms o Thm.prop_of) (take 400 facts));
  val fsubterms = cterms thy (maps (take 8 o closed_subterms o Bicompose_Test.freeze o Thm.prop_of) (take 400 facts));
  val assumed = map Thm.assume (take 300 fprops);
  val frozen = map_filter (fn c => try (Thm.implies_elim (Thm.trivial c)) (Thm.assume c)) (take 300 fprops);
  (*theorems with flex-flex pairs*)
  val sctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt;
  fun rd s = Syntax.read_prop sctxt s;
  val ff_rules = map (Skip_Proof.make_thm thy o rd) ["PROP ?P ?x", "PROP ?P (?f ?x) \<Longrightarrow> PROP ?Q"];
  val ff_states = map (Goal.init o Thm.cterm_of ctxt o rd)
    ["PROP ?Q (a::'a)", "\<And>y::'a. PROP ?Q y", "PROP ?Q a \<Longrightarrow> PROP ?R"];
  val ffs = ff_rules |> maps (fn r => ff_states |> maps (fn st =>
    take_list 3 (Thm.biresolution (SOME ctxt) false [(false, r)] 1 st)));
  val thms = take 600 facts @ assumed @ frozen @ ffs;
  val meta_eqs =
    map_filter (fn th => try (fn th => th RS @{thm eq_reflection}) th) (take 800 facts) @
    map Thm.reflexive (take 200 subterms) @
    map_filter (try (Thm.beta_conversion true)) (take 200 subterms);
  val show_ct2 = fn (c, th) => show_ct c ^ " " ^ show_thm th;

  (* primitive rules *)
  val r_assume = compare "assume" show_ct (Seq.single o Thm.assume)
    (fn c => res (zero thy (G.assume_rule (ct c)))) (props @ fprops @ take 200 subterms);
  val ii = map (fn (c, th) => (c, th)) ((props ~~~ thms) @ (fprops ~~~ assumed) @
    (map Thm.cprop_of assumed ~~~ assumed) @ (take 100 subterms ~~~ thms));
  val r_ii = compare "implies_intr" show_ct2 (fn (c, th) => Seq.single (Thm.implies_intr c th))
    (fn (c, th) => res (one thy th (G.implies_intr (ct c) (rep_of th)))) ii;
  val ie = map (fn th => (Thm.trivial (Thm.cprop_of th), th)) thms @ (rules ~~~ thms) @
    map (fn th => (Thm.implies_intr (Thm.cprop_of th) th, th)) (ffs @ assumed);
  val r_ie = compare "implies_elim" (fn (a, b) => show_thm a ^ show_thm b)
    (fn (a, b) => Seq.single (Thm.implies_elim a b))
    (fn (a, b) => res (two thy a b (G.implies_elim (rep_of a) (rep_of b)))) ie;
  fun vars_of th = cterms thy (map Var (Term.add_vars (Thm.full_prop_of th) []) @
    map Free (Term.add_frees (Thm.full_prop_of th) []));
  val fi = maps (fn th => map (rpair th) (take 3 (vars_of th))) (thms @ meta_eqs) @
    (take 100 subterms ~~~ thms);
  fun hyps_of th = Thm.hyps_of th;
  val r_fi = compare "forall_intr" show_ct2 (fn (c, th) => Seq.single (Thm.forall_intr c th))
    (fn (c, th) => res (one thy th (G.forall_intr (hyps_of th) (ct c) (rep_of th)))) fi;
  val alls = map_filter (fn (c, th) => try (Thm.forall_intr c) th) fi;
  val fe = maps (fn th => map (rpair th) (take 3 subterms)) (take 300 alls) @
    maps (fn th => map (rpair th) (take 2 (vars_of th))) (take 300 alls) @ (take 100 subterms ~~~ thms);
  val r_fe = compare "forall_elim" show_ct2 (fn (c, th) => Seq.single (Thm.forall_elim c th))
    (fn (c, th) => res (one thy th (G.forall_elim (ct c) (rep_of th)))) fe;
  val r_refl = compare "reflexive" show_ct (Seq.single o Thm.reflexive)
    (fn c => res (zero thy (G.reflexive (ct c)))) (subterms @ fsubterms);
  val r_sym = compare "symmetric" show_thm (Seq.single o Thm.symmetric)
    (fn th => res (one thy th (G.symmetric (rep_of th)))) (meta_eqs @ take 200 thms);
  val tr = map_filter (try (fn th => (th, Thm.symmetric th))) meta_eqs @ (meta_eqs ~~~ rev meta_eqs) @
    map_filter (try (fn th => (th, Thm.reflexive (Thm.rhs_of th)))) meta_eqs @ (take 100 thms ~~~ meta_eqs);
  val r_trans = compare "transitive" (fn (a, b) => show_thm a ^ show_thm b)
    (fn (a, b) => Seq.single (Thm.transitive a b))
    (fn (a, b) => res (two thy a b (G.transitive (rep_of a) (rep_of b)))) tr;
  val redexes = map_filter (fn c =>
    (case Thm.term_of c of
      Abs (_, T, _) => try (Thm.global_cterm_of thy) (Thm.term_of c $ Free ("c", T))
    | _ => NONE)) (subterms @ fsubterms);
  val r_beta = compare "beta_conversion" show_ct (Seq.single o Thm.beta_conversion false)
    (fn c => res (zero thy (G.beta_conversion false (ct c)))) (redexes @ take 100 subterms);
  val r_betaf = compare "beta_conversion (full)" show_ct (Seq.single o Thm.beta_conversion true)
    (fn c => res (zero thy (G.beta_conversion true (ct c)))) (redexes @ subterms);
  val r_eta = compare "eta_conversion" show_ct (Seq.single o Thm.eta_conversion)
    (fn c => res (zero thy (G.eta_conversion (ct c)))) (subterms @ fsubterms @ redexes);
  val r_etal = compare "eta_long_conversion" show_ct (Seq.single o Thm.eta_long_conversion)
    (fn c => res (zero thy (G.eta_long_conversion (ct c)))) (subterms @ fsubterms @ redexes);
  val fmeta = map Thm.reflexive (take 200 fsubterms) @ map Thm.assume
    (map_filter (fn c => try (fn c => Thm.global_cterm_of thy (Logic.mk_equals (Thm.term_of c, Thm.term_of c))) c)
      (take 100 fsubterms));
  val ab = maps (fn th => map (rpair th) (take 3 (vars_of th))) (fmeta @ meta_eqs) @
    (take 100 subterms ~~~ meta_eqs) @ (take 100 subterms ~~~ thms);
  val r_abs = compare "abstract_rule" show_ct2 (fn (c, th) => Seq.single (Thm.abstract_rule "b" c th))
    (fn (c, th) => res (one thy th (G.abstract_rule "b" (hyps_of th) (ct c) (rep_of th)))) ab;
  val apps = map_filter (fn c =>
    (case Thm.term_of c of
      f $ t => SOME (Thm.reflexive (Thm.global_cterm_of thy f), Thm.reflexive (Thm.global_cterm_of thy t))
    | _ => NONE) handle TERM _ => NONE | TYPE _ => NONE) (subterms @ fsubterms);
  val cb = apps @ (map fst apps ~~~ rev (map snd apps)) @ (take 100 meta_eqs ~~~ take 100 thms);
  val r_comb = compare "combination" (fn (a, b) => show_thm a ^ show_thm b)
    (fn (a, b) => Seq.single (Thm.combination a b))
    (fn (a, b) => res (two thy a b (G.combination (rep_of a) (rep_of b)))) cb;
  val ei = map (fn c => (Thm.trivial c, Thm.trivial c)) (take 200 props) @
    (take 200 rules ~~~ rev (take 200 rules)) @ (take 100 rules ~~~ take 100 thms) @
    map (fn th => (Thm.implies_intr (Thm.cprop_of th) th, Thm.implies_intr (Thm.cprop_of th) th)) (take 100 assumed);
  val r_ei = compare "equal_intr" (fn (a, b) => show_thm a ^ show_thm b)
    (fn (a, b) => Seq.single (Thm.equal_intr a b))
    (fn (a, b) => res (two thy a b (G.equal_intr (rep_of a) (rep_of b)))) ei;
  val ee = map (fn th => (Thm.reflexive (Thm.cprop_of th), th)) thms @ (meta_eqs ~~~ thms) @
    (take 100 thms ~~~ thms);
  val r_ee = compare "equal_elim" (fn (a, b) => show_thm a ^ show_thm b)
    (fn (a, b) => Seq.single (Thm.equal_elim a b))
    (fn (a, b) => res (two thy a b (G.equal_elim (rep_of a) (rep_of b)))) ee;
  val r_triv = compare "trivial" show_ct (Seq.single o Thm.trivial)
    (fn c => res (zero thy (G.trivial (ct c)))) (props @ fprops @ take 100 subterms);
  val wk = (fprops ~~~ thms) @ (props ~~~ thms) @ (take 100 subterms ~~~ thms);
  val r_weak = compare "weaken" show_ct2 (fn (c, th) => Seq.single (Thm.weaken c th))
    (fn (c, th) => res (one thy th (G.weaken (ct c) (rep_of th)))) wk;
  val rn = map (fn th => (rename_bounds (Thm.prop_of th), th)) thms @
    (map Thm.prop_of (rev (take 100 thms)) ~~~ take 100 thms);
  val r_ren = compare "renamed_prop" (fn (t, th) => \<^make_string> t ^ show_thm th)
    (fn (t, th) => Seq.single (Thm.renamed_prop t th))
    (fn (t, th) => res (one thy th (G.renamed_prop t (rep_of th)))) rn;
  val am = maps (fn th => map (rpair th) [~1, Thm.maxidx_of th, Thm.maxidx_of th + 3]) thms;
  val r_adj = compare "adjust_maxidx_thm" (fn (i, th) => string_of_int i ^ show_thm th)
    (fn (i, th) => Seq.single (Thm.adjust_maxidx_thm i th))
    (fn (i, th) => res (G.adjust_maxidx_thm i (rep_of th))) am;

  (* derived rules *)
  fun tfree_names th = Term.add_tfree_names (Thm.full_prop_of th) [];
  fun free_names th = map #1 (Term.add_frees (Thm.full_prop_of th) []);
  val gen_args = (frozen @ assumed @ take 200 thms) |> maps (fn th =>
    let val i = Thm.maxidx_of th + 1 in
      [(take 1 (tfree_names th), take 2 (free_names th), i, th),
       (tfree_names th, [], i, th), ([], free_names th, i, th),
       (tfree_names th, free_names th, Int.max (0, Thm.maxidx_of th), th), ([], [], 0, th)]
    end);
  fun names xs = Names.make_set xs;
  val r_gen = compare "generalize" (fn (a, b, i, th) => \<^make_string> (a, b, i) ^ show_thm th)
    (fn (a, b, i, th) => Seq.single (Thm.generalize (names a, names b) i th))
    (fn (a, b, i, th) => res (one thy th (G.generalize a b i (hyps_of th) (rep_of th)))) gen_args;
  fun inst_args th =
    let
      val prop = Thm.full_prop_of th;
      val tvars = Term.add_tvars prop [];
      val instT = map (fn v as (_, S) => (v, Thm.global_ctyp_of thy (if S = [] then propT else \<^typ>\<open>bool\<close>))) (take 1 tvars);
      val instT' = map (fn v => (v, Thm.global_ctyp_of thy propT)) (take 1 tvars);
      val tyenv = TVars.make (map (apsnd Thm.typ_of) instT);
      val vars = Term.add_vars prop [] |> map (fn (xi, T) => (xi, Term_Subst.instantiateT tyenv T));
      fun inst_of (xi, T) =
        let
          val (Ts, U) = strip_type T;
          val body = Free ("c", U);
          val t = fold_rev (fn S => fn b => Abs ("x", S, b)) Ts body;
        in try (Thm.global_cterm_of thy) t |> Option.map (pair (xi, T)) end;
      val inst = map_filter inst_of (take 2 vars);
      val bad = map_filter (fn (xi, T) => try (Thm.global_cterm_of thy) (Free ("d", propT --> T)) |> Option.map (pair (xi, T))) (take 1 vars);
    in [(instT, inst, th), (instT', [], th), ([], bad, th), (instT, [], th), ([], inst, th)] end;
  val ins = maps inst_args (take 300 thms @ ffs);
  fun mkT xs = TVars.make xs and mkV xs = Vars.make xs;
  fun gT xs = map (fn (v, c) => (v, (Thm.typ_of c, Thm.maxidx_of_ctyp c))) xs;
  fun gV xs = map (fn (v, c) => (v, (Thm.term_of c, (Thm.typ_of_cterm c, Thm.maxidx_of_cterm c)))) xs;
  fun show_inst (a, b, th) = \<^make_string> (map (apsnd Thm.typ_of) a, map (apsnd Thm.term_of) b) ^ show_thm th;
  val r_inst = compare "instantiate" show_inst
    (fn (a, b, th) => Seq.single (Thm.instantiate (mkT a, mkV b) th))
    (fn (a, b, th) => res (one thy th (G.instantiate alg false (gT a) (gV b) (rep_of th)))) ins;
  val r_instb = compare "instantiate_beta" show_inst
    (fn (a, b, th) => Seq.single (Thm.instantiate_beta (mkT a, mkV b) th))
    (fn (a, b, th) => res (one thy th (G.instantiate alg true (gT a) (gV b) (rep_of th)))) ins;
  val incr = maps (fn th => map (rpair th) [~1, 0, 2]) thms;
  val r_incr = compare "incr_indexes" (fn (i, th) => string_of_int i ^ show_thm th)
    (fn (i, th) => Seq.single (Thm.incr_indexes i th))
    (fn (i, th) => res (one thy th (G.incr_indexes_thm i (rep_of th)))) incr;
  val goals = map (Bicompose_Test.goal_state thy) (take 200 rules);
  val states = take 400 rules @ goals @ ffs;
  val rot = states |> maps (fn st => maps (fn i => map (fn k => (k, i, st)) [~1, 1, 2, 5])
    [1, Thm.nprems_of st, Thm.nprems_of st + 1]);
  val r_rot = compare "rotate_rule" (fn (k, i, st) => \<^make_string> (k, i) ^ show_thm st)
    (fn (k, i, st) => Seq.single (Thm.rotate_rule k i st))
    (fn (k, i, st) => res (one thy st (G.rotate_rule k i (rep_of st)))) rot;
  val perm = states |> maps (fn st => maps (fn j => map (fn k => (j, k, st)) [~1, 1, 2])
    [~1, 0, 1, Thm.nprems_of st, Thm.nprems_of st + 1]);
  val r_perm = compare "permute_prems" (fn (j, k, st) => \<^make_string> (j, k) ^ show_thm st)
    (fn (j, k, st) => Seq.single (Thm.permute_prems j k st))
    (fn (j, k, st) => res (one thy st (G.permute_prems j k (rep_of st)))) perm;
  val vl = Name.variant_list;
  fun tfrees_of th = Term.add_tfrees (Thm.full_prop_of th) [];
  val vary = (frozen @ assumed @ take 200 thms) |> maps (fn th => [([], th), (take 1 (tfrees_of th), th)]);
  fun result_vary (al, th) = (al, Thm.prop_of th, Thm.tpairs_of th, Thm.maxidx_of th);
  val vary_cmp = vary |> map (fn (fixed, th) =>
    let
      val a = Exn.result (fn () => result_vary (Thm.varifyT_global' (TFrees.make_set fixed) th)) ();
      val b = Exn.result (fn () =>
        let val (al, th') = one thy th (G.varifyT_global vl fixed (hyps_of th) (rep_of th))
        in (al, G.th_prop th', G.th_tpairs th', G.th_maxidx th') end) ();
      fun str (Exn.Res x) = \<^make_string> x
        | str (Exn.Exn e) = "EXN " ^ Bicompose_Test.exn_name e;
    in (show_thm th, str a, str b) end);
  val vary_mism = filter (fn (_, a, b) => a <> b) vary_cmp;
  val r_frz = compare "legacy_freezeT" show_thm (Seq.single o Thm.legacy_freezeT)
    (fn th => res (one thy th (G.legacy_freezeT vl (rep_of th)))) (thms @ frozen);
  val classes = ["HOL.type", "Orderings.ord", "Groups.plus", "Nat.semiring_char_0", "HOL.equal"];
  val types = [propT, \<^typ>\<open>bool\<close>, \<^typ>\<open>nat\<close>, \<^typ>\<open>'a\<close>, \<^typ>\<open>'a::ord\<close>, \<^typ>\<open>nat \<Rightarrow> bool\<close>,
    \<^typ>\<open>'a list\<close>, TVar (("'b", 0), [\<^class>\<open>plus\<close>]), \<^typ>\<open>int set\<close>];
  val oc = maps (fn T => map (pair (Thm.global_ctyp_of thy T)) classes) types;
  val r_ofc = compare "of_class" (fn (T, c) => \<^make_string> (Thm.typ_of T, c))
    (fn (T, c) => Seq.single (Thm.of_class (T, c)))
    (fn (T, c) =>
      let val c' = Sign.certify_class thy c in
        (case G.of_class alg (Thm.typ_of T) c' of
          SOME (_, G.Err (G.NOT_OF_SORT _)) =>
            raise THM ("of_class: type not of class " ^ Syntax.string_of_sort_global thy [c'], 0, [])
        | r => res (zero thy r))
      end) oc;
  val rs = [r_assume, r_ii, r_ie, r_fi, r_fe, r_refl, r_sym, r_trans, r_beta, r_betaf, r_eta, r_etal,
    r_abs, r_comb, r_ei, r_ee, r_triv, r_weak, r_ren, r_adj, r_gen, r_inst, r_instb, r_incr, r_rot,
    r_perm, r_frz, r_ofc];

  (* proofs *)
  val P = Proofterm_Test.synth and Z = Proofterm_Test.zsynth;
  val zrun = Proofterm_Test.zrun;
  fun prun r = Proofterm_Test.run r;
  val p_ii = pcompare "implies_intr (proofs)" (fn (c, th) => show_ct c)
    (fn (c, th) => ([], Proofterm.implies_intr_proof (Thm.term_of c) (P th)))
    (fn (c, th) => ([], G.implies_intr_proof (Thm.term_of c) (P th))) (map (fn th => (Thm.cprop_of th, th)) thms @ ii);
  val z_ii = zcompare "implies_intr (tight proofs)" (fn (c, th) => show_ct c)
    (fn (c, th) => ([], ZTerm.implies_intr_proof thy (Thm.term_of c) (Z th)))
    (fn (c, th) => zrun (G.zimplies_intr_proof ta (Thm.term_of c) (Z th))) (map (fn th => (Thm.cprop_of th, th)) thms @ ii);
  fun var_name c = (case Thm.term_of c of Free (a, _) => a | Var ((a, _), _) => a | _ => "a");
  val fi' = filter (fn (c, th) => can (Thm.forall_intr c) th) fi;
  val p_fi = pcompare "forall_intr (proofs)" (fn (c, _) => show_ct c)
    (fn (c, th) => ([], Proofterm.forall_intr_proof (var_name c, Thm.term_of c) NONE (P th)))
    (fn (c, th) => ([], G.forall_intr_proof (var_name c) (Thm.term_of c) (P th))) fi';
  val z_fi = zcompare "forall_intr (tight proofs)" (fn (c, _) => show_ct c)
    (fn (c, th) => ([], ZTerm.forall_intr_proof thy (Thm.typ_of_cterm c) (var_name c, Thm.term_of c) (Z th)))
    (fn (c, th) => zrun (G.zforall_intr_proof ta (Thm.typ_of_cterm c) (var_name c) (Thm.term_of c) (Z th))) fi';
  val z_fe = zcompare "forall_elim (tight proofs)" (fn (c, _) => show_ct c)
    (fn (c, th) => ([], ZTerm.forall_elim_proof thy (Thm.term_of c) (Z th)))
    (fn (c, th) => zrun (G.zforall_elim_proof ta (Thm.term_of c) (Z th))) fe;
  val z_as = zcompare "assume (tight proofs)" show_ct
    (fn c => ([], ZTerm.assume_proof thy (Thm.term_of c)))
    (fn c => zrun (G.zassume_proof ta (Thm.term_of c))) (props @ fprops);
  val z_tr = zcompare "trivial (tight proofs)" show_ct
    (fn c => ([], ZTerm.trivial_proof thy (Thm.term_of c)))
    (fn c => zrun (G.ztrivial_proof ta (Thm.term_of c))) (props @ fprops);
  val p_misc = pcompare "reflexive/trivial (proofs)" (K "")
    (fn () => ([], Proofterm.reflexive_proof %% Proofterm.trivial_proof))
    (fn () => ([], G.reflexive_proof %% G.trivial_proof)) [()];
  val z_refl = zcompare "reflexive (tight proofs)" show_ct
    (fn c => ([], ZTerm.reflexive_proof thy (Thm.typ_of_cterm c) (Thm.term_of c)))
    (fn c => zrun (G.zreflexive_proof ta (Thm.typ_of_cterm c) (Thm.term_of c))) subterms;
  fun eq_parts th = (case Thm.prop_of th of Const ("Pure.eq", Type ("fun", [T, _])) $ t $ u => SOME (T, t, u) | _ => NONE);
  val eqs = map_filter (fn th => Option.map (pair th) (eq_parts th)) meta_eqs;
  val prfs = [fn th => P th, K Proofterm.reflexive_proof];
  val zprfs = [fn th => Z th, fn th => (case eq_parts th of SOME (T, t, _) => ZTerm.reflexive_proof thy T t | NONE => Z th)];
  val p_sym = pcompare "symmetric (proofs)" (fn (th, _) => show_thm th)
    (fn (th, f) => ([], Proofterm.symmetric_proof (f th))) (fn (th, f) => ([], G.symmetric_proof (f th)))
    (maps (fn (th, _) => map (pair th) prfs) eqs);
  val z_sym = zcompare "symmetric (tight proofs)" (fn ((th, _), _) => show_thm th)
    (fn ((th, (T, t, u)), f) => ([], ZTerm.symmetric_proof thy T t u (f th)))
    (fn ((th, (T, t, u)), f) => zrun (G.zsymmetric_proof ta T t u (f th)))
    (maps (fn x => map (pair x) zprfs) eqs);
  val treqs = map_filter (fn (a, b) => (case (eq_parts a, eq_parts b) of (SOME (T, t, u), SOME (_, _, v)) => SOME (a, b, T, t, u, v) | _ => NONE)) tr;
  val p_trans = pcompare "transitive (proofs)" (fn ((a, _, _, _, _, _), _) => show_thm a)
    (fn ((a, b, T, t, u, v), (f, g)) => ([], Proofterm.transitive_proof T u (f a) (g b)))
    (fn ((a, b, T, t, u, v), (f, g)) => ([], G.transitive_proof T u (f a) (g b)))
    (maps (fn x => maps (fn f => map (pair x o pair f) prfs) prfs) treqs);
  val z_trans = zcompare "transitive (tight proofs)" (fn ((a, _, _, _, _, _), _) => show_thm a)
    (fn ((a, b, T, t, u, v), (f, g)) => ([], ZTerm.transitive_proof thy T t u v (f a) (g b)))
    (fn ((a, b, T, t, u, v), (f, g)) => zrun (G.ztransitive_proof ta T t u v (f a) (g b)))
    (maps (fn x => maps (fn f => map (pair x o pair f) zprfs) zprfs) treqs);
  val imps = map_filter (fn th => (case Thm.prop_of th of Const ("Pure.imp", _) $ A $ B => SOME (th, A, B) | _ => NONE)) (take 300 thms);
  val p_eq = pcompare "equal_intr/equal_elim (proofs)" (fn (th, _, _) => show_thm th)
    (fn (th, A, B) => ([], Proofterm.equal_intr_proof A B (P th) (P th) %% Proofterm.equal_elim_proof A B (P th) (P th)))
    (fn (th, A, B) => ([], G.equal_intr_proof A B (P th) (P th) %% G.equal_elim_proof A B (P th) (P th))) imps;
  val z_eq = zcompare "equal_intr/equal_elim (tight proofs)" (fn (th, _, _) => show_thm th)
    (fn (th, A, B) => ([], ZAppp (ZTerm.equal_intr_proof thy A B (Z th) (Z th), ZTerm.equal_elim_proof thy A B (Z th) (Z th))))
    (fn (th, A, B) => ([], ZAppp (#2 (zrun (G.zequal_intr_proof ta A B (Z th) (Z th))), #2 (zrun (G.zequal_elim_proof ta A B (Z th) (Z th)))))) imps;
  val ab' = filter (fn (c, th) => can (Thm.abstract_rule "b" c) th) ab;
  val p_abs = pcompare "abstract_rule (proofs)" (fn (c, _) => show_ct c)
    (fn (c, th) => ([], Proofterm.abstract_rule_proof ("b", Thm.term_of c) (P th)))
    (fn (c, th) => ([], G.abstract_rule_proof "b" (Thm.term_of c) (P th))) ab';
  val z_abs = zcompare "abstract_rule (tight proofs)" (fn (c, _) => show_ct c)
    (fn (c, th) =>
      let val (U, (f, g)) = one thy th (G.abstract_rule_data "b" (hyps_of th) (ct c) (rep_of th))
      in ([], ZTerm.abstract_rule_proof thy (Thm.typ_of_cterm c) U ("b", Thm.term_of c) f g (Z th)) end)
    (fn (c, th) =>
      let val (U, (f, g)) = one thy th (G.abstract_rule_data "b" (hyps_of th) (ct c) (rep_of th))
      in zrun (G.zabstract_rule_proof ta (Thm.typ_of_cterm c) U "b" (Thm.term_of c) f g (Z th)) end) ab';
  val cb' = filter (fn (a, b) => can (Thm.combination a) b) cb;
  fun comb_prfs a = [P a, Proofterm.reflexive_proof,
    Proofterm.combination_proof (Free ("f", dummyT)) (Free ("g", dummyT)) (Var (("x", 0), dummyT)) (Bound 0) (P a) (P a)];
  val p_comb = pcompare "combination (proofs)" (fn ((a, b), _) => show_thm a)
    (fn ((a, b), p) =>
      let val (_, (_, (f, (g, (t, u))))) = two thy a b (G.combination_data (rep_of a) (rep_of b))
      in ([], Proofterm.combination_proof f g t u p (P b)) end)
    (fn ((a, b), p) =>
      let val (_, (_, (f, (g, (t, u))))) = two thy a b (G.combination_data (rep_of a) (rep_of b))
      in prun (G.combination_proof f g t u p (P b)) end)
    (maps (fn x => map (pair x) (comb_prfs (fst x))) cb');
  val z_comb = zcompare "combination (tight proofs)" (fn (a, b) => show_thm a)
    (fn (a, b) =>
      let val (fT, (U, (f, (g, (t, u))))) = two thy a b (G.combination_data (rep_of a) (rep_of b))
      in ([], ZTerm.combination_proof thy fT U f g t u (Z a) (Z b)) end)
    (fn (a, b) =>
      let val (fT, (U, (f, (g, (t, u))))) = two thy a b (G.combination_data (rep_of a) (rep_of b))
      in zrun (G.zcombination_proof ta fT U f g t u (Z a) (Z b)) end) cb';
  val gen' = filter (fn (a, b, i, th) => can (Thm.generalize (names a, names b) i) th) gen_args;
  val p_gen = pcompare "generalize (proofs)" (fn (a, b, i, th) => show_thm th)
    (fn (a, b, i, th) => ([], Proofterm.generalize_proof (names a, names b) i (Thm.prop_of th) (P th)))
    (fn (a, b, i, th) => ([], G.generalize_proof a b i (Thm.prop_of th) (P th))) gen';
  val z_gen = zcompare "generalize (tight proofs)" (fn (a, b, i, th) => show_thm th)
    (fn (a, b, i, th) => ([], ZTerm.generalize_proof (names a, names b) i (Z th)))
    (fn (a, b, i, th) => zrun (G.zgeneralize_proof a b i (Z th))) gen';
  val ins' = filter (fn (a, b, th) => can (Thm.instantiate (mkT a, mkV b)) th) ins;
  val p_inst = pcompare "instantiate (proofs)" (fn x => show_inst x)
    (fn (a, b, th) => ([], Proofterm.instantiate (TVars.make (map (apsnd Thm.typ_of) a), Vars.make (map (apsnd Thm.term_of) b)) (P th)))
    (fn (a, b, th) => ([], G.instantiate_proof (map (apsnd Thm.typ_of) a) (map (apsnd Thm.term_of) b) (P th))) ins';
  val z_inst = zcompare "instantiate (tight proofs)" (fn x => show_inst x)
    (fn (a, b, th) => ([], ZTerm.instantiate_proof thy (map (apsnd Thm.typ_of) a, map (apsnd Thm.term_of) b) (Z th)))
    (fn (a, b, th) => zrun (G.zinstantiate_proof ta (map (apsnd Thm.typ_of) a) (map (apsnd Thm.term_of) b) (Z th))) ins';
  val p_incr = pcompare "incr_indexes (proofs)" (fn th => show_thm th)
    (fn th => ([], Proofterm.incr_indexes 2 (P th))) (fn th => ([], G.incr_indexes_proof 2 (P th))) thms;
  val z_incr = zcompare "incr_indexes (tight proofs)" (fn th => show_thm th)
    (fn th => ([], ZTerm.incr_indexes_proof 2 (Z th))) (fn th => zrun (G.zincr_indexes_proof 2 (Z th))) thms;
  val rot' = filter (fn (k, i, st) => can (Thm.rotate_rule k i) st) rot;
  fun rot_data (k, i, st) = one thy st (G.rotate_data k i (rep_of st));
  val p_rot = pcompare "rotate_rule (proofs)" (fn (_, _, st) => show_thm st)
    (fn x as (_, _, st) => let val (_, (Bs, (Bi', (params, (asms, m))))) = rot_data x
      in ([], Proofterm.rotate_proof Bs Bi' params asms m (P st)) end)
    (fn x as (_, _, st) => let val (_, (Bs, (Bi', (params, (asms, m))))) = rot_data x
      in ([], G.rotate_proof Bs Bi' params asms m (P st)) end) rot';
  val z_rot = zcompare "rotate_rule (tight proofs)" (fn (_, _, st) => show_thm st)
    (fn x as (_, _, st) => let val (_, (Bs, (Bi', (params, (asms, m))))) = rot_data x
      in ([], ZTerm.rotate_proof thy Bs Bi' params asms m (Z st)) end)
    (fn x as (_, _, st) => let val (_, (Bs, (Bi', (params, (asms, m))))) = rot_data x
      in zrun (G.zrotate_proof ta Bs Bi' params asms m (Z st)) end) rot';
  val perm' = filter (fn (j, k, st) => can (Thm.permute_prems j k) st) perm;
  fun perm_data (j, k, st) = one thy st (G.permute_data j k (rep_of st));
  val p_perm = pcompare "permute_prems (proofs)" (fn (_, _, st) => show_thm st)
    (fn x as (j, _, st) => let val (_, (prems', m)) = perm_data x in ([], Proofterm.permute_prems_proof prems' j m (P st)) end)
    (fn x as (j, _, st) => let val (_, (prems', m)) = perm_data x in ([], G.permute_prems_proof prems' j m (P st)) end) perm';
  val z_perm = zcompare "permute_prems (tight proofs)" (fn (_, _, st) => show_thm st)
    (fn x as (j, _, st) => let val (_, (prems', m)) = perm_data x in ([], ZTerm.permute_prems_proof thy prems' j m (Z st)) end)
    (fn x as (j, _, st) => let val (_, (prems', m)) = perm_data x in zrun (G.zpermute_prems_proof ta prems' j m (Z st)) end) perm';
  fun vary_names (fixed, th) = #1 (Thm.varifyT_global' (TFrees.make_set fixed) th);
  val p_vary = pcompare "varifyT_global' (proofs)" (fn (_, th) => show_thm th)
    (fn x as (_, th) => ([], Proofterm.varifyT_proof (vary_names x) (P th)))
    (fn x as (_, th) => ([], G.varifyT_proof (vary_names x) (P th))) vary;
  val z_vary = zcompare "varifyT_global' (tight proofs)" (fn (_, th) => show_thm th)
    (fn x as (_, th) => ([], ZTerm.varifyT_proof (vary_names x) (Z th)))
    (fn x as (_, th) => zrun (G.zvarifyT_proof (vary_names x) (Z th))) vary;
  val p_frz = pcompare "legacy_freezeT (proofs)" show_thm
    (fn th => ([], Proofterm.legacy_freezeT (Thm.full_prop_of th) (P th)))
    (fn th => ([], G.legacy_freezeT_proof vl (Thm.full_prop_of th) (P th))) (thms @ frozen);
  val z_frz = zcompare "legacy_freezeT (tight proofs)" show_thm
    (fn th => ([], ZTerm.legacy_freezeT_proof (Thm.full_prop_of th) (Z th)))
    (fn th => zrun (G.zlegacy_freezeT_proof vl (Thm.full_prop_of th) (Z th))) (thms @ frozen);
  val ps = [p_ii, z_ii, p_fi, z_fi, z_fe, z_as, z_tr, p_misc, z_refl, p_sym, z_sym, p_trans, z_trans,
    p_eq, z_eq, p_abs, z_abs, p_comb, z_comb, p_gen, z_gen, p_inst, z_inst, p_incr, z_incr, p_rot,
    z_rot, p_perm, z_perm, p_vary, z_vary, p_frz, z_frz];
in
  val _ = writeln (cat_lines (map Bicompose_Test.report rs));
  val _ = writeln ("varifyT_global': " ^ string_of_int (length vary_cmp) ^ " problems, " ^
    string_of_int (length vary_mism) ^ " mismatches");
  val _ = writeln (cat_lines (map Proofterm_Test.report ps));
  val _ = Bicompose_Test.check rs;
  val _ = null vary_mism orelse error (\<^make_string> (take 2 vary_mism));
  val _ = Proofterm_Test.check ps;
end
\<close>

end
