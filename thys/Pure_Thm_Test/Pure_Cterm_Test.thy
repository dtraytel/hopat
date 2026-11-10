section \<open>Testing the Generated Code of the Operations on Certified Terms\<close>

theory Pure_Cterm_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated code of theory \<^theory_text>\<open>Pure_Cterm\<close> is compared with the destructors and
  constructors of certified terms of \<open>Thm\<close> on the closed subterms of theorems of HOL and on
  terms with free variables: the term, type and maximal index of the results, and the exceptions
  (with their messages).
\<close>

ML \<open>
local
  structure G = Bicompose_Generated;
  val thy = \<^theory>;
  fun cert t = Thm.global_cterm_of thy t;
  fun rep ct = G.CTerm (Thm.term_of ct, Thm.typ_of_cterm ct, Thm.maxidx_of_cterm ct);
  fun show_ct ct = \<^make_string> (Thm.term_of ct, Thm.typ_of_cterm ct, Thm.maxidx_of_cterm ct);
  fun show_rep (G.CTerm (t, T, m)) = \<^make_string> (t, T, m);
  fun exn_str exn =
    (case exn of
      CTERM (msg, _) => "CTERM " ^ msg
    | TYPE (msg, Ts, ts) => "TYPE " ^ msg ^ \<^make_string> (Ts, ts)
    | TERM (msg, ts) => "TERM " ^ msg ^ \<^make_string> ts
    | Term.USED_FREE (x, t) => "USED_FREE " ^ x ^ \<^make_string> t
    | _ => "EXN " ^ Bicompose_Test.exn_name exn);
  fun outcome f x =
    (case Exn.result (Timeout.apply (seconds 5.0) f) x of
      Exn.Res y => y
    | Exn.Exn exn => exn_str exn);
  fun compare name show f g xs : Proofterm_Test.report =
    let val results = map (fn x => (show x, outcome f x, outcome g x)) xs
    in {name = name, tests = length xs, mismatches = filter (fn (_, a, b) => a <> b) results} end;
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
  val rs = [r_comb, r_fun, r_arg, r_fun2, r_arg1, r_glob, r_fresh, r_apply, r_lam, r_incr];
in
  val _ = writeln (cat_lines (map Proofterm_Test.report rs));
  val _ = Proofterm_Test.check rs;
end
\<close>

end
