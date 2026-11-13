section \<open>Testing the Generated Code of the Operations on Certified Terms\<close>

theory Pure_Cterm_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated code of theory \<^theory_text>\<open>Pure_Cterm\<close> is compared with the destructors,
  constructors, generalization and instantiation of certified terms of \<open>Thm\<close> on the closed subterms of theorems of HOL and on
  terms with free variables: the term, type and maximal index of the results, and the exceptions
  (with their messages).
\<close>

ML \<open>
local
  structure G = Bicompose_Generated;
  val thy = \<^theory>;
  fun cert t = Thm.global_cterm_of thy t;
  fun rep ct = G.CTerm (Thm.term_of ct, Thm.typ_of_cterm ct, Thm.maxidx_of_cterm ct);
  (*certified terms in full: term, type (with sorts) and maximal index*)
  val show_term = Exact.content (Exact.triple Exact.term Exact.typ Exact.int);
  fun show_ct ct = show_term (Thm.term_of ct, Thm.typ_of_cterm ct, Thm.maxidx_of_cterm ct);
  fun show_rep (G.CTerm (t, T, m)) = show_term (t, T, m);
  fun exn_str exn =
    (case exn of
      CTERM (msg, _) => "EXN CTERM " ^ msg
    | Term.USED_FREE (x, t) => "EXN USED_FREE " ^ x ^ Exact.content Exact.term t
    | _ => "EXN " ^ Bicompose_Test.exn_name exn);
  fun outcome f x =
    (case Exn.result (Timeout.apply (seconds 5.0) f) x of
      Exn.Res y => y
    | Exn.Exn exn => exn_str exn);
  fun compare name show f g xs : Proofterm_Test.report =
    Test_Stat.compare name show (SOME o outcome f) (SOME o outcome g) xs;
  fun run r = Bicompose_Test.run (Context.Theory thy) (Drule.dummy_thm, Drule.dummy_thm) r;

  (*closed subterms of theorems of HOL, and terms with free variables*)
  fun subterms t =
    t :: (case t of
      u $ v => subterms u @ subterms v
    | Abs (_, _, b) => subterms b
    | _ => []);
  val thms = map (Thm.prop_of o snd) (take 400 (Global_Theory.all_thms_of thy false));
  val extra_terms =
    [\<^term>\<open>\<lambda>x::nat. f x y\<close>, \<^term>\<open>\<lambda>y::nat. f x y\<close>, \<^term>\<open>\<lambda>x::'a. x\<close>, \<^term>\<open>\<lambda>(x::nat) y. x + y\<close>,
     Abs ("y", \<^typ>\<open>nat\<close>, \<^term>\<open>(+) :: nat \<Rightarrow> _\<close> $ Free ("y", \<^typ>\<open>nat\<close>) $ Bound 0),
     Abs ("y", \<^typ>\<open>nat\<close>, \<^term>\<open>(+) :: nat \<Rightarrow> _\<close> $ Free ("y", \<^typ>\<open>nat\<close>) $ Free ("ya", \<^typ>\<open>nat\<close>)),
     \<^term>\<open>Suc 0\<close>, \<^term>\<open>f (x::nat) (y::bool)\<close>, \<^term>\<open>Trueprop True\<close>, \<^term>\<open>(\<lambda>x. x) (0::nat)\<close>];
  val cts =
    distinct (op aconv) (maps subterms (take 60 thms @ extra_terms))
    |> filter (fn t => not (Term.is_open t))
    |> map_filter (fn t => SOME (cert t) handle TYPE _ => NONE | TERM _ => NONE)
    |> take 600;
  fun cmp1 name f g = compare name show_ct (show_ct o f) (show_rep o run o g o rep) cts;
  fun cmp2 name f g = compare name show_ct ((fn (a, b) => show_ct a ^ show_ct b) o f)
    ((fn (a, b) => show_rep a ^ show_rep b) o run o g o rep) cts;
  val r_comb = cmp2 "dest_comb" Thm.dest_comb G.dest_comb;
  val r_fun = cmp1 "dest_fun" Thm.dest_fun G.dest_fun;
  val r_arg = cmp1 "dest_arg" Thm.dest_arg G.dest_arg;
  val r_fun2 = cmp1 "dest_fun2" Thm.dest_fun2 G.dest_fun2;
  val r_arg1 = cmp1 "dest_arg1" Thm.dest_arg1 G.dest_arg1;
  val r_glob = cmp2 "dest_abs_global" Thm.dest_abs_global (G.dest_abs_global Name.variant_list);
  val names = ["x", "y", "ya", "P", "f"];
  val fresh_ins = maps (fn ct => map (rpair ct) names) cts;
  val r_fresh = compare "dest_abs_fresh" (fn (x, ct) => x ^ " " ^ show_ct ct)
    (fn (x, ct) => let val (a, b) = Thm.dest_abs_fresh x ct in show_ct a ^ show_ct b end)
    (fn (x, ct) => let val (a, b) = run (G.dest_abs_fresh x (rep ct)) in show_rep a ^ show_rep b end)
    fresh_ins;
  (*apply: the parts of combinations, also mismatched*)
  val combs = map_filter (fn ct => SOME (Thm.dest_comb ct) handle CTERM _ => NONE) cts;
  val app_ins = combs @ map (fn ((f, _), (_, x)) => (f, x)) (take (length combs - 1) combs ~~ tl combs) @
    map (fn ct => (ct, ct)) (take 40 cts);
  val r_apply = compare "apply" (fn (a, b) => show_ct a ^ show_ct b)
    (show_ct o uncurry Thm.apply) (fn (a, b) => show_rep (run (G.apply_cterm (rep a) (rep b)))) app_ins;
  (*lambda_name: abstraction over atoms of the terms*)
  val atoms = filter (fn ct => is_Free (Thm.term_of ct) orelse is_Var (Thm.term_of ct) orelse
    is_Const (Thm.term_of ct)) cts;
  val lam_ins = maps (fn v => map (fn ct => (v, ct)) (take 25 cts)) (take 25 atoms);
  val r_lam = compare "lambda_name" (fn (a, b) => show_ct a ^ show_ct b)
    (fn (v, ct) => show_ct (Thm.lambda_name ("", v) ct) ^ show_ct (Thm.lambda_name ("z", v) ct))
    (fn (v, ct) => show_rep (run (G.lambda_name "" (rep v) (rep ct))) ^
      show_rep (run (G.lambda_name "z" (rep v) (rep ct)))) lam_ins;
  val incr_ins = maps (fn ct => map (rpair ct) [~1, 0, 2]) (take 200 cts);
  val r_incr = compare "incr_indexes_cterm" (fn (i, ct) => string_of_int i ^ " " ^ show_ct ct)
    (fn (i, ct) => show_ct (Thm.incr_indexes_cterm i ct))
    (fn (i, ct) => show_rep (run (G.incr_indexes_cterm i (rep ct)))) incr_ins;
  (*free and var: the types of the terms as certified types*)
  val ctyps = distinct (fn ((T1, _), (T2, _)) => T1 = T2) (map Thm.ctyp_of_cterm cts |> map (fn cT => (Thm.typ_of cT, cT)))
    |> map #2 |> take 60;
  fun show_ctyp cT = Exact.content (Exact.pair Exact.typ Exact.int) (Thm.typ_of cT, Thm.maxidx_of_ctyp cT);
  val r_free = compare "free" (fn (x, cT) => x ^ " " ^ show_ctyp cT)
    (fn (x, cT) => show_ct (Thm.free (x, cT)))
    (fn (x, cT) => show_rep (G.free_cterm x (Thm.typ_of cT) (Thm.maxidx_of_ctyp cT)))
    (maps (fn cT => map (rpair cT) ["x", "y"]) ctyps);
  val r_var = compare "var" (fn (xi, cT) => \<^make_string> xi ^ " " ^ show_ctyp cT)
    (fn (xi, cT) => show_ct (Thm.var (xi, cT)))
    (fn (xi, cT) => show_rep (run (G.var_cterm xi (Thm.typ_of cT) (Thm.maxidx_of_ctyp cT))))
    (maps (fn cT => map (rpair cT) [("x", ~1), ("x", 0), ("y", 3)]) ctyps);
  val r_lambda = compare "lambda" (fn (a, b) => show_ct a ^ show_ct b)
    (fn (v, ct) => show_ct (Thm.lambda v ct))
    (fn (v, ct) => show_rep (run (G.lambda_cterm (rep v) (rep ct)))) lam_ins;
  val r_adjust = compare "adjust_maxidx_cterm" (fn (i, ct) => string_of_int i ^ " " ^ show_ct ct)
    (fn (i, ct) => show_ct (Thm.adjust_maxidx_cterm i ct))
    (fn (i, ct) => show_rep (G.adjust_maxidx_cterm i (rep ct)))
    (maps (fn ct => map (rpair ct) [~1, 0, 1, 5]) (take 200 cts));
  (*generalize_cterm: the free (type) variables of terms, at a good and a bad index*)
  val gen_cts = map cert
    [\<^term>\<open>f (x::'a) (y::nat)\<close>, \<^term>\<open>\<lambda>z::'b. (x::'a, z)\<close>, \<^term>\<open>(x::'a::order) \<le> y\<close>,
     \<^term>\<open>Suc n\<close>, (Logic.varify_global \<^term>\<open>x + (y::nat)\<close>), \<^term>\<open>\<lambda>x::'a. x\<close>, \<^term>\<open>True\<close>] @ take 40 cts;
  fun gen_args ct =
    let
      val t = Thm.term_of ct;
      val tfs = Term.add_tfree_names t [] and fs = Term.add_free_names t [];
      val m = Thm.maxidx_of_cterm ct;
    in
      [([], [], m + 1), (tfs, fs, m + 1), (tfs, [], m + 2), ([], fs, m + 1), (tfs, fs, m),
       (take 1 tfs, take 1 fs, m + 3)]
      |> map (fn (a, b, i) => (a, b, i, ct))
    end;
  val r_gen = compare "generalize_cterm" (fn (a, b, i, ct) => \<^make_string> (a, b, i) ^ show_ct ct)
    (fn (a, b, i, ct) => show_ct (Thm.generalize_cterm (Names.make_set a, Names.make_set b) i ct))
    (fn (a, b, i, ct) => show_rep (run (G.generalize_cterm (Names.list_set (Names.make_set a))
      (Names.list_set (Names.make_set b)) i (rep ct)))) (maps gen_args gen_cts);
  (*instantiate_cterm: schematic (type) variables by renamed ones, by types not of their sort,
    by terms of another type, and function variables by abstractions (for beta)*)
  val inst_cts = map cert
    [(Logic.varify_global \<^term>\<open>f (x::'a) (y::nat)\<close>), (Logic.varify_global \<^term>\<open>(x::'a::order) \<le> y\<close>), (Logic.varify_global \<^term>\<open>P (x::nat) \<and> Q\<close>),
     (Logic.varify_global \<^term>\<open>\<lambda>z::'b. (x::'a, z)\<close>), (Logic.varify_global \<^term>\<open>Suc n\<close>), \<^term>\<open>True\<close>] @
    map_filter (fn ct => SOME (cert (Logic.varify_global (Thm.term_of ct))) handle TERM _ => NONE) (take 300 cts);
  fun cT T = Thm.global_ctyp_of thy T;
  fun inst_args ct =
    let
      val t = Thm.term_of ct;
      val tvs = Term.add_tvars t [] and vs = Term.add_vars t [];
      val m = Thm.maxidx_of_cterm ct;
      val ren = TVars.make (map (fn v as ((a, i), S) => (v, cT (TVar ((a, i + m + 1), S)))) tvs);
      val bad = TVars.make (map (fn v => (v, cT \<^typ>\<open>nat \<Rightarrow> nat\<close>)) (take 1 (filter (not o null o #2) tvs)));
      val renv = Vars.make (map (fn v as ((x, i), T) => (v, cert (Var ((x, i + m + 1), T)))) vs);
      val conf = Vars.make (map (fn v => (v, cert \<^term>\<open>True\<close>)) (take 1 (filter (fn (_, T) => T <> \<^typ>\<open>bool\<close>) vs)));
      val abss = Vars.make (map_filter (fn v as (_, T) =>
        (case T of
          Type ("fun", [A, B]) => SOME (v, cert (Abs ("u", A, Var (("w", m + 1), B))))
        | _ => NONE)) vs);
    in
      [(TVars.empty, Vars.empty), (ren, Vars.empty), (TVars.empty, renv), (ren, renv), (bad, Vars.empty),
       (TVars.empty, conf), (TVars.empty, abss)]
      |> map (rpair ct)
    end;
  fun model_inst beta ((instT, inst), ct) =
    let
      val instT' = TVars.dest instT |> map (fn (v, c) => (v, (Thm.typ_of c, Thm.maxidx_of_ctyp c)));
      val inst' = Vars.dest inst |> map (fn (v, c) => (v, (Thm.term_of c, (Thm.typ_of_cterm c, Thm.maxidx_of_cterm c))));
    in
      (case G.instantiate_cterm (Sign.classes_of thy) beta instT' inst' (rep ct) of
        SOME (_, G.Err (G.NOT_OF_SORT _)) => "EXN CTERM sort"
      | SOME (_, G.Err (G.INST_CONFLICT _)) => "EXN CTERM conflict"
      | r => show_rep (run r))
    end;
  fun isa_inst f ((instT, inst), ct) =
    show_ct (f (instT, inst) ct)
      handle CTERM (msg, _) =>
        if String.isPrefix "Type not of sort" (XML.content_of (YXML.parse_body msg)) then "EXN CTERM sort"
        else if String.isPrefix "instantiate: type conflict" (XML.content_of (YXML.parse_body msg)) then "EXN CTERM conflict"
        else raise CTERM (msg, []);
  val inst_ins = maps inst_args inst_cts;
  val show_inst = fn ((instT, inst), ct) =>
    \<^make_string> (map (apsnd Thm.typ_of) (TVars.dest instT), map (apsnd Thm.term_of) (Vars.dest inst)) ^ show_ct ct;
  val r_inst = compare "instantiate_cterm" show_inst (isa_inst Thm.instantiate_cterm) (model_inst false) inst_ins;
  val r_instb = compare "instantiate_beta_cterm" show_inst (isa_inst Thm.instantiate_beta_cterm) (model_inst true) inst_ins;
  (*variables of index -1 as the keys of an instantiation: Isabelle2026 without the fix
    thm-instantiate-index leaves the term as it is; with the fix, the function raises CTERM*)
  val inst_neg = inst_cts |> maps (fn ct =>
    let
      val t = Thm.term_of ct;
      val tvs = take 1 (Term.add_tvars t []) and vs = take 1 (Term.add_vars t []);
      val instT = TVars.make (map (fn ((a, _), S) => (((a, ~1), S), cT (TFree ("'c", S)))) tvs);
      val inst = Vars.make (map (fn ((x, _), T) => (((x, ~1), T), cert (Free ("c", T)))) vs);
    in
      [(instT, Vars.empty), (TVars.empty, inst)]
      |> filter (fn (a, b) => not (TVars.is_empty a andalso Vars.is_empty b))
      |> map (rpair ct)
    end);
  val r_inst_neg = compare "instantiate_cterm (a variable of index -1)" show_inst
    (isa_inst Thm.instantiate_cterm) (model_inst false) inst_neg;
  val _ = \<^assert> (#exns r_inst_neg = (if Test_System.patched then #run r_inst_neg else 0));
  val _ = \<^assert> (Test_System.patched orelse length (#mismatches r_inst_neg) = #run r_inst_neg);
  val rs = [r_comb, r_fun, r_arg, r_fun2, r_arg1, r_glob, r_fresh, r_apply, r_lam, r_incr,
    r_free, r_var, r_lambda, r_adjust, r_gen, r_inst, r_instb];
in
  val _ = writeln (cat_lines (map Proofterm_Test.report (rs @ [r_inst_neg])));
  val _ = Proofterm_Test.check rs;
  val _ = Proofterm_Test.check_with [#name r_inst_neg] (if Test_System.patched then [r_inst_neg] else []);
end
\<close>

end
