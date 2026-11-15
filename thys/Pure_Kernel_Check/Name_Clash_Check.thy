(* Results of the rules that unify whose environment binds a name with two types *)

theory Name_Clash_Check
  imports Main
begin

text \<open>
  The rules \<open>assumption\<close>, \<open>bicompose\<close> and \<open>biresolution\<close> of \<open>derivable\<close> (session
  \<open>Thm_Correctness\<close>) have a premise that the kernel does not check: the environment of the
  result binds no name of a schematic variable that occurs with two types; \<open>flexflex_rule\<close>
  asks for one type for each name. This theory runs the kernel on arguments for which a
  unifier has to bind such a name, and records what the kernel does. It is a list of
  experiments, not a proof: in each of them the kernel raises an exception, has no result, or
  returns an instance of its arguments.

  A theorem with a name at two types is made with \<open>Thm.instantiate\<close>, which admits it.
\<close>

ML \<open>
fun inst1 ctxt (x, T) t th =
  Thm.instantiate (TVars.empty, Vars.make1 ((x, T), Thm.cterm_of ctxt t)) th;

datatype outcome = Result of thm | No_Result | Exn of string;

fun outcome (f: unit -> thm Seq.seq) =
  (case Seq.pull (f ()) of NONE => No_Result | SOME (th, _) => Result th)
  handle TYPE (msg, _, _) => Exn ("TYPE: " ^ msg)
    | TERM (msg, _) => Exn ("TERM: " ^ msg)
    | THM (msg, _, _) => Exn ("THM: " ^ msg);

val type_clash = Exn "TYPE: Variable has two distinct types";

fun expect name expected f =
  let val res = outcome f in
    (case (expected, res) of
      (Exn msg, Exn msg') =>
        if msg = msg' then writeln (name ^ ": exception " ^ msg)
        else error (name ^ ": other exception " ^ msg')
    | (No_Result, No_Result) => writeln (name ^ ": no result")
    | (Result th, Result th') =>
        if Thm.full_prop_of th aconv Thm.full_prop_of th'
        then writeln (name ^ ": result " ^ Thm.string_of_thm_global (Thm.theory_of_thm th') th')
        else error (name ^ ": other result " ^ Thm.string_of_thm_global (Thm.theory_of_thm th') th')
    | (_, Result th') =>
        error (name ^ ": unexpected result " ^ Thm.string_of_thm_global (Thm.theory_of_thm th') th')
    | _ => error (name ^ ": unexpected outcome"))
  end;

fun res1 ctxt rule i st = Thm.biresolution (SOME ctxt) false [(false, rule)] i st;
\<close>


section \<open>The bound name occurs at a second type in what remains: exception\<close>

lemma L1: "((0::nat) = a \<Longrightarrow> y = a) \<Longrightarrow> z \<or> \<not> z \<Longrightarrow> (0 = a \<longrightarrow> y = a)"
  by simp

lemma R3: "(v::bool) = v \<Longrightarrow> (u::nat) = 3 \<Longrightarrow> u = 3"
  by simp

lemma R4: "(u::nat) = u \<and> (v::bool) = v"
  by simp

lemma S5: "(w::bool) = w \<Longrightarrow> (3::nat) = 3 \<Longrightarrow> w \<or> \<not> w"
  by simp

lemma R5: "(u::nat) = u"
  by simp

ML \<open>
(*assumption binds ?y at nat; ?y at bool is in the second premise*)
val st1 = inst1 \<^context> (("z", 0), \<^typ>\<open>bool\<close>) (Var (("y", 0), \<^typ>\<open>bool\<close>)) @{thm L1};
val _ = expect "assumption" type_clash (fn () => Thm.assumption (SOME \<^context>) 1 st1);

(*resolution binds ?u at nat; the first premise of the rule has ?u at bool*)
val rule3 = inst1 \<^context> (("v", 0), \<^typ>\<open>bool\<close>) (Var (("u", 0), \<^typ>\<open>bool\<close>)) @{thm R3};
val _ = expect "resolution, premise of the rule" type_clash (fn () =>
  res1 \<^context> rule3 1 (Thm.trivial \<^cprop>\<open>(3::nat) = 3\<close>));

(*both types in the conclusion of the rule, which resolution drops; also for a false goal*)
val rule4 = inst1 \<^context> (("v", 0), \<^typ>\<open>bool\<close>) (Var (("u", 0), \<^typ>\<open>bool\<close>)) @{thm R4};
val _ = expect "resolution, conclusion of the rule" type_clash (fn () =>
  res1 \<^context> rule4 1 (Thm.trivial \<^cprop>\<open>(3::nat) = 3 \<and> True = True\<close>));
val _ = expect "resolution, conclusion of the rule, false goal" type_clash (fn () =>
  res1 \<^context> rule4 1 (Thm.trivial \<^cprop>\<open>(3::nat) = 3 \<and> True = False\<close>));

(*composition: the state has ?u at bool, the rule at nat*)
val st5 = inst1 \<^context> (("w", 0), \<^typ>\<open>bool\<close>) (Var (("u", 0), \<^typ>\<open>bool\<close>)) @{thm S5};
val _ = expect "bicompose, incremented" type_clash (fn () =>
  Thm.bicompose (SOME \<^context>) {flatten = true, match = false, incremented = true}
    (false, @{thm R5}, 0) 2 st5);
val _ = expect "bicompose, not incremented" No_Result (fn () =>
  Thm.bicompose (SOME \<^context>) {flatten = true, match = false, incremented = false}
    (false, @{thm R5}, 0) 2 st5);
\<close>


section \<open>The occurrence at the second type is in an argument that normalization discards\<close>

text \<open>
  \<open>Envir.norm_term\<close> looks a variable up when it reaches it. An argument of a variable that is
  bound to a function which ignores it is dropped by \<open>\<beta>\<close>-reduction before it is reached. So an
  occurrence of a bound name at another type in what the rule keeps does not raise the exception
  if it is inside such an argument; it is not in the result.
\<close>

lemma L3: "(((\<lambda>x::nat. 0::nat), True) = p \<Longrightarrow> (f, y) = p) \<Longrightarrow> Suc (f (z::nat)) = Suc (f z)"
  by simp

lemma L3_inst: "Suc (0::nat) = Suc 0"
  by simp

lemma L3': "(((\<lambda>x::nat. x), True) = p \<Longrightarrow> (f, y) = p) \<Longrightarrow> Suc (f (z::nat)) = Suc (f z)"
  by simp

ML \<open>
(*assumption binds ?f to \<lambda>x. 0 and ?y at bool; ?y at nat is the argument of ?f in the conclusion*)
val st3 = inst1 \<^context> (("z", 0), \<^typ>\<open>nat\<close>) (Var (("y", 0), \<^typ>\<open>nat\<close>)) @{thm L3};
val _ = expect "assumption, discarded argument" (Result @{thm L3_inst}) (fn () =>
  Thm.assumption (SOME \<^context>) 1 st3);

(*the same with ?f bound to the identity: the argument is kept and looked up*)
val st3' = inst1 \<^context> (("z", 0), \<^typ>\<open>nat\<close>) (Var (("y", 0), \<^typ>\<open>nat\<close>)) @{thm L3'};
val _ = expect "assumption, argument kept" type_clash (fn () =>
  Thm.assumption (SOME \<^context>) 1 st3');
\<close>


section \<open>The two types are unified: an instance\<close>

lemma L2: "((0::nat) = 0 \<Longrightarrow> (y::'b) = y) \<Longrightarrow> (z::nat) = 5 \<Longrightarrow> z = 5"
  by simp

lemma L2_inst: "(0::nat) = 5 \<Longrightarrow> (0::nat) = 5"
  by simp

ML \<open>
(*?y at ?'b and at nat; assumption binds ?'b to nat and ?y to 0*)
val st2 = inst1 \<^context> (("z", 0), \<^typ>\<open>nat\<close>) (Var (("y", 0), \<^typ>\<open>nat\<close>)) @{thm L2};
val _ = expect "assumption, types unified" (Result @{thm L2_inst}) (fn () =>
  Thm.assumption (SOME \<^context>) 1 st2);
\<close>


section \<open>The second type occurs only in what the rule drops\<close>

text \<open>
  Pattern unification compares the heads of a flex-flex pair by name. For \<open>?x \<equiv> (\<lambda>u v. ?x v u)\<close>
  with \<open>?x\<close> at \<open>'a \<Rightarrow> 'b \<Rightarrow> 'r\<close> on the left and at \<open>'b \<Rightarrow> 'a \<Rightarrow> 'r\<close> on the right it binds the
  variable of the left type to a constant function and looks up nothing at the other type. If
  the occurrence at the other type is only in the solved premise, there is a result. It is
  the result for the value \<open>\<lambda>v u. ?x'\<close> of the variable at the other type, so it is an instance
  of the state. If that variable, or a variable identified with it, is in what remains, the
  kernel raises the exception.
\<close>

lemma Va: "(x::'a \<Rightarrow> 'b \<Rightarrow> 'r) \<equiv> (\<lambda>u v. y v u) \<Longrightarrow> x \<equiv> x"
  by simp

lemma Vb: "(z, x::'a \<Rightarrow> 'b \<Rightarrow> 'r) = (y, \<lambda>u v. y v u) \<Longrightarrow> x a b = x a b"
  by simp

lemma Vc: "(z, x::'a \<Rightarrow> 'b \<Rightarrow> 'r) = (y, \<lambda>u v. y v u) \<Longrightarrow> x a b = z b a"
  by simp

lemma Vd: "(x::'a \<Rightarrow> 'b \<Rightarrow> 'r) \<equiv> (\<lambda>u v. y v u) \<Longrightarrow> y \<equiv> y' \<Longrightarrow> x a b = y' b a"
  by simp

ML \<open>
val Ty = \<^typ>\<open>'b \<Rightarrow> 'a \<Rightarrow> 'r\<close> |> Logic.varifyT_global;
fun clash th = inst1 \<^context> (("y", 0), Ty) (Var (("x", 0), Ty)) th;
val R = TVar (("'r", 0), \<^sort>\<open>type\<close>);
val A = TVar (("'a", 0), \<^sort>\<open>type\<close>) and B = TVar (("'b", 0), \<^sort>\<open>type\<close>);
val x2 = Var (("x", 2), R);

(*the result is (\<lambda>u v. ?x2) \<equiv> (\<lambda>u v. ?x2)*)
val ra = Thm.reflexive (Thm.cterm_of \<^context> (Abs ("u", A, Abs ("v", B, x2))));
val _ = expect "vanishing occurrence" (Result ra) (fn () =>
  res1 \<^context> @{thm Pure.reflexive} 1 (clash @{thm Va}));

(*?z is identified with the occurrence at the second type and vanishes with it: ?x2 = ?x2*)
val rb = inst1 \<^context> (("t", 0), R) x2 (Thm.instantiate' [SOME (Thm.ctyp_of \<^context> R)] [] @{thm refl});
val _ = expect "vanishing occurrence and a second variable" (Result rb) (fn () =>
  res1 \<^context> @{thm refl} 1 (clash @{thm Vb}));

(*?z remains in the conclusion*)
val _ = expect "second variable remains" type_clash (fn () =>
  res1 \<^context> @{thm refl} 1 (clash @{thm Vc}));

(*the occurrence at the second type remains in another premise, in both orders*)
val _ = expect "occurrence remains, premise 1" type_clash (fn () =>
  res1 \<^context> @{thm Pure.reflexive} 1 (clash @{thm Vd}));
val _ = expect "occurrence remains, premise 2 then 1" type_clash (fn () =>
  res1 \<^context> @{thm Pure.reflexive} 2 (clash @{thm Vd})
  |> Seq.maps (res1 \<^context> @{thm Pure.reflexive} 1));
\<close>


section \<open>Both: the second type is in the solved premise and in a discarded argument\<close>

text \<open>
  The two cases without an exception combined. The solved premise has \<open>?x\<close> at both types as
  heads of a flex-flex pair, so pattern unification binds the variable of the left type and
  looks nothing up at the other; the conclusion has the occurrence at the other type as the
  argument of \<open>?f\<close>, which the same unifier binds to a constant function. The result does not
  contain the occurrence. It is the instance of the state for the bindings of \<open>?f\<close> and of
  \<open>?x\<close> at the left type and for the value \<open>\<lambda>v u. ?x'\<close> of \<open>?x\<close> at the other type.
\<close>

lemma Ve: "(f, x::'a \<Rightarrow> 'b \<Rightarrow> 'r) \<equiv> (\<lambda>z::'b \<Rightarrow> 'a \<Rightarrow> 'r. c::nat, \<lambda>u v. y v u) \<Longrightarrow> f y = c"
  unfolding atomize_eq by simp

lemma Vf: "(f, x::'a \<Rightarrow> 'b \<Rightarrow> 'r) \<equiv> (\<lambda>z::'b \<Rightarrow> 'a \<Rightarrow> 'r. z, \<lambda>u v. y v u) \<Longrightarrow> f y = y"
  unfolding atomize_eq by simp

ML \<open>
val re = inst1 \<^context> (("t", 0), \<^typ>\<open>nat\<close>) (Var (("c", 0), \<^typ>\<open>nat\<close>))
  (Thm.instantiate' [SOME \<^ctyp>\<open>nat\<close>] [] @{thm refl});
val _ = expect "vanishing occurrence in a discarded argument" (Result re) (fn () =>
  res1 \<^context> @{thm Pure.reflexive} 1 (clash @{thm Ve}));

(*with ?f bound to the identity the occurrence is kept and looked up*)
val _ = expect "vanishing occurrence in a kept argument" type_clash (fn () =>
  res1 \<^context> @{thm Pure.reflexive} 1 (clash @{thm Vf}));
\<close>


section \<open>flexflex_rule on a pair whose heads are one name at two types: exception\<close>

lemma F7: "Q (f (a::nat) :: int) \<Longrightarrow> Q (f a)"
  by simp

lemma G7: "Q ((g (b::bool))::nat) \<Longrightarrow> Q (g b) \<and> g b = g b"
  by simp

ML \<open>
(*a theorem with the flex-flex pair ?Q1 (?f1 ?a1) \<equiv> ?Q (?g ?b), ?Q1 at int \<Rightarrow> bool and ?Q at nat \<Rightarrow> bool*)
val th7 = Seq.hd (res1 \<^context> @{thm F7} 1 @{thm G7});
val _ = \<^assert> (length (Thm.tpairs_of th7) = 1);
val _ = \<^assert> (is_some (Seq.pull (Thm.flexflex_rule (SOME \<^context>) th7)));
(*rename ?Q to ?Q1*)
val th7' = inst1 \<^context> (("Q", 0), \<^typ>\<open>nat \<Rightarrow> bool\<close>) (Var (("Q", 1), \<^typ>\<open>nat \<Rightarrow> bool\<close>)) th7;
val _ = expect "flexflex_rule" (Exn "TERM: add_ffpair: Var name confusion") (fn () =>
  Thm.flexflex_rule (SOME \<^context>) th7');
\<close>

end
