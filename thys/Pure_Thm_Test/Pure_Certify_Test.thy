section \<open>Tests of the Certification of Types and Terms\<close>

theory Pure_Certify_Test
  imports "Pure_Thm.Pure_Certify" Pure_Bicompose_Test_Base
begin

text \<open>
  The code generated from the models of theory \<^theory_text>\<open>Pure_Certify\<close> is compared with
  \<open>Sign.certify_term\<close>, \<open>Thm.global_cterm_of\<close> and \<open>Thm.global_ctyp_of\<close>: on propositions,
  subterms and types of theorems of HOL, on terms and types with one violation of
  well-formedness each, on terms that certification changes or accepts beyond the obvious
  (a type abbreviation, a sort with redundant classes, a constant at an instance outside the
  sorts of its type scheme), and on terms with constants that are abbreviations, which
  certification expands. An exception of Isabelle corresponds to the result \<open>None\<close> of the
  model. The model takes the right-hand sides that certification inserts for the
  abbreviations as a table (\<open>normal_rhs\<close>, which \<open>consts.ML\<close> does not export: it is
  \<open>Consts.certify\<close> of the exported right-hand side, as in \<open>Consts.abbreviate\<close>). The sorts of a certified term or type are not accessible outside the kernel; they are
  read off the sort hypotheses of a reflexivity theorem.
\<close>

code_printing
  constant class_mem \<rightharpoonup>
    (SML) "(fn alg => fn c => (ignore (Sorts.cert'_class alg c); true) handle TYPE x => false)"
| constant is_qualified \<rightharpoonup> (SML) "Long'_Name.is'_qualified"

code_reflect Certify_Generated
  datatypes tdecl = Logical_Type | Abbreviation | Nonterminal
  functions certify_typ certify_term global_ctyp_of global_cterm_of need_expand

ML \<open>
local
  structure C = Certify_Generated;
  structure G = Bicompose_Generated;
  val thy = \<^theory>;
  val tsig = Sign.tsig_of thy;
  val consts = Sign.consts_of thy;
  val alg = Sign.classes_of thy;

  (*the parts of the signature*)
  fun td a =
    (case try (Type.the_decl tsig) (a, Position.none) of
      SOME (Type.Logical_Type n) => SOME (C.Logical_Type n)
    | SOME (Type.Abbreviation (vs, U, syntactic)) => SOME (C.Abbreviation (vs, U, syntactic))
    | SOME Type.Nonterminal => SOME C.Nonterminal
    | NONE => NONE);
  fun ctab c = try (Consts.type_scheme consts) c;
  fun abbrs c =
    (case try (Consts.the_abbreviation consts) c of
      SOME (_, rhs) => SOME (Consts.certify {normalize = true} (Context.Theory thy) tsig consts rhs)
    | NONE => NONE);

  fun attempt f x = SOME (f x) handle TYPE _ => NONE | ERROR _ => NONE;
  fun sorts_of ct = Thm.shyps_of (Thm.reflexive ct);

  (*an exception of Isabelle and the result None of the model are the outcome "EXN"*)
  fun str f = fn NONE => "EXN" | SOME x => Exact.content f x;
  val str_term = str (Exact.pair Exact.term Exact.typ);
  val str_cterm = str (Exact.pair (Exact.triple Exact.term Exact.typ Exact.int) (Exact.list Exact.sort));
  val str_ctyp = str (Exact.triple Exact.typ Exact.int (Exact.list Exact.sort));

  fun isa_term t = str_term (attempt (Sign.certify_term thy) t);
  fun gen_term t = str_term (C.certify_term alg td ctab abbrs t);
  fun isa_cterm t =
    str_cterm (attempt (fn t =>
      let val ct = Thm.global_cterm_of thy t
      in ((Thm.term_of ct, Thm.typ_of_cterm ct, Thm.maxidx_of_cterm ct), sorts_of ct) end) t);
  fun gen_cterm t =
    str_cterm (Option.map (fn (G.CTerm (t, T, i), Ss) => ((t, T, i), Ss))
      (C.global_cterm_of alg td ctab abbrs t));
  fun isa_ctyp T =
    str_ctyp (attempt (fn T =>
      let val cT = Thm.global_ctyp_of thy T
      in (Thm.typ_of cT, Thm.maxidx_of_ctyp cT, sorts_of (Thm.free ("x", cT))) end) T);
  fun gen_ctyp T = str_ctyp (Option.map (fn (T, (i, Ss)) => (T, i, Ss)) (C.global_ctyp_of alg td T));

  fun subterms (t as u $ v) = t :: subterms u @ subterms v
    | subterms (t as Abs (_, _, b)) = t :: subterms b
    | subterms t = [t];
  val props =
    Global_Theory.all_thms_of thy true |> map (Thm.full_prop_of o snd)
    |> filter (fn t => size_of_term t < 200) |> take 6000;
  val closed = maps (take 6 o filter_out Term.is_open o subterms) (take 2000 props);
  val base = take 1500 props;

  val undeclared = \<^unchecked_name>\<open>Certify_Check.undeclared\<close>;
  val x = "x";
  val bad_terms =
   [("an application of a term that is no function", fn t => t $ t),
    ("an argument of another type",
      fn t => Abs (x, propT, t) $ Const (\<^const_name>\<open>True\<close>, \<^typ>\<open>bool\<close>)),
    ("an undeclared constant",
      Term.map_aterms (fn Const (_, T) => Const (undeclared, T) | a => a)),
    ("a constant at a type that is not an instance",
      fn t => Abs (x, \<^typ>\<open>bool \<Rightarrow> bool\<close>, t) $ Const (\<^const_name>\<open>True\<close>, \<^typ>\<open>bool \<Rightarrow> bool\<close>)),
    ("a constant at two instances of one type variable",
      fn t => Abs (x, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> bool\<close>, t) $ Const (\<^const_name>\<open>HOL.eq\<close>, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> bool\<close>)),
    ("a type constructor without an argument",
      Term.map_types (fn Type ("fun", [A, _]) => Type ("fun", [A]) | T => Type ("fun", [T]))),
    ("an undeclared type constructor", Term.map_types (fn T => Type (undeclared, [T]))),
    ("an undeclared class", fn t => Abs (x, TFree ("'x", [undeclared]), t)),
    ("a variable of index -1", fn t => Abs (x, propT, t) $ Var ((x, ~1), propT)),
    ("a type variable of index -1", fn t => Abs (x, TVar (("'x", ~1), []), t)),
    ("a loose bound variable", fn t => Abs (x, propT, t) $ Bound 0),
    ("a negative bound variable", fn t => Abs (x, propT, Abs (x, propT, t) $ Bound ~1)),
    ("a free variable with a qualified name", fn t => Abs (x, propT, t) $ Free ("a.b", propT)),
    ("a nonterminal", fn t => Abs (x, Type ("logic", []), t)),
    ("a type variable at two sorts in the type of a constant",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $
        (Const (\<^const_name>\<open>HOL.eq\<close>, TVar (("'a", 0), []) --> TVar (("'a", 0), \<^sort>\<open>type\<close>) --> \<^typ>\<open>bool\<close>) $
          Var (("y", 0), TVar (("'a", 0), [])) $ Var (("z", 0), TVar (("'a", 0), \<^sort>\<open>type\<close>))))];
  val odd_terms =
   [("a sort with redundant classes",
      fn t => Abs (x, TFree ("'x", [\<^class>\<open>ord\<close>, \<^class>\<open>order\<close>, \<^class>\<open>type\<close>]), t)),
    ("a type abbreviation", fn t => Abs (x, Type (\<^type_abbrev>\<open>rel\<close>, [\<^typ>\<open>nat\<close>]), t)),
    ("a type abbreviation in the type of a constant",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $
        (Const (\<^const_name>\<open>HOL.eq\<close>, Type (\<^type_abbrev>\<open>rel\<close>, [\<^typ>\<open>nat\<close>]) -->
          Type (\<^type_abbrev>\<open>rel\<close>, [\<^typ>\<open>nat\<close>]) --> \<^typ>\<open>bool\<close>) $
          Free ("r", Type (\<^type_abbrev>\<open>rel\<close>, [\<^typ>\<open>nat\<close>])) $ Free ("r", \<^typ>\<open>(nat \<times> nat) set\<close>))),
    ("a constant outside the sort of its declared type",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $ Const (\<^const_name>\<open>zero_class.zero\<close>, \<^typ>\<open>bool\<close>))];

  fun cmp name show f g xs = Test_Stat.compare name show (SOME o f) (SOME o g) xs;
  val show = Exact.content Exact.term;
  fun term_groups name ts =
    [cmp ("certify_term: " ^ name) show isa_term gen_term ts,
     cmp ("global_cterm_of: " ^ name) show isa_cterm gen_cterm ts];
  val r_good = term_groups "propositions of theorems" props @ term_groups "closed subterms" closed;
  val r_bad = maps (fn (name, f) => term_groups name (map f base)) bad_terms;
  val r_odd = maps (fn (name, f) => term_groups name (map f base)) odd_terms;

  val typs = fold (fold_types (insert (op =))) (take 3000 props) [] |> take 4000;
  val bad_typs =
   [("a type constructor without an argument", fn T => Type ("fun", [T])),
    ("an undeclared type constructor", fn T => Type (undeclared, [T])),
    ("an undeclared class", fn T => T --> TFree ("'x", [undeclared])),
    ("a type variable of index -1", fn T => T --> TVar (("'x", ~1), [])),
    ("a nonterminal", fn T => T --> Type ("logic", []))];
  val odd_typs =
   [("a type abbreviation", fn T => Type (\<^type_abbrev>\<open>rel\<close>, [T])),
    ("a type abbreviation with a free type variable of its parameter's name",
      fn T => Type (\<^type_abbrev>\<open>rel\<close>, [T --> TFree ("'a", []) --> TFree ("'a", \<^sort>\<open>type\<close>)]))];
  val showT = Exact.content Exact.typ;
  fun typ_group name Ts = cmp ("global_ctyp_of: " ^ name) showT isa_ctyp gen_ctyp Ts;
  val rT_good = [typ_group "types of theorems" typs];
  val rT_bad = map (fn (name, f) => typ_group name (map f (take 1500 typs))) bad_typs;
  val rT_odd = map (fn (name, f) => typ_group name (map f (take 1500 typs))) odd_typs;

  (*constants that are abbreviations: Isabelle expands them*)
  val ne = Const (\<^const_abbrev>\<open>not_equal\<close>, \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>);
  val abbrev_terms =
   [("an abbreviation with its arguments",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $ (ne $ \<^term>\<open>0::nat\<close> $ \<^term>\<open>1::nat\<close>)),
    ("an abbreviation without arguments", fn t => Abs (x, \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>, t) $ ne),
    ("an abbreviation with a bound variable as argument",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $ (Abs ("n", \<^typ>\<open>nat\<close>, ne $ Bound 0 $ \<^term>\<open>0::nat\<close>) $ \<^term>\<open>1::nat\<close>)),
    ("an abbreviation as argument of an abbreviation",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $
        (Const (\<^const_abbrev>\<open>not_equal\<close>, \<^typ>\<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>) $
          (ne $ \<^term>\<open>0::nat\<close> $ \<^term>\<open>1::nat\<close>) $ (ne $ Var (("n", 0), \<^typ>\<open>nat\<close>) $ Free ("m", \<^typ>\<open>nat\<close>))))];
  val bad_abbrev_terms =
   [("an abbreviation at a type that is not an instance",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $ Const (\<^const_abbrev>\<open>not_equal\<close>, \<^typ>\<open>bool\<close>)),
    ("an abbreviation at two instances of one type variable",
      fn t => Abs (x, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> bool\<close>, t) $ Const (\<^const_abbrev>\<open>not_equal\<close>, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> bool\<close>))];
  (*each abbreviation of the theory at its declared type*)
  val abbrev_consts =
    map_filter (fn (c, (T, SOME _)) => SOME (Const (c, T)) | _ => NONE) (#constants (Consts.dest consts));
  val abase = take 300 base;
  val r_abbr =
    maps (fn (name, f) => term_groups name (map f abase)) abbrev_terms @
    term_groups "the abbreviations of the theory" abbrev_consts;
  val r_bad_abbr = maps (fn (name, f) => term_groups name (map f abase)) bad_abbrev_terms;

  val bad = r_bad @ rT_bad @ r_bad_abbr;
  val all = r_good @ rT_good @ bad @ r_odd @ rT_odd @ r_abbr;
in
  val _ = writeln (cat_lines (map Test_Stat.report all));
  (*the tests of violations have exceptions only; the others have results only*)
  val _ = Test_Stat.check_with (map #name bad) all;
  val _ = \<^assert> (forall (fn r => #exns r = #run r) bad);
  val _ = \<^assert> (forall (fn r => #exns r = 0) (r_good @ rT_good @ r_odd @ rT_odd @ r_abbr));
  (*no term of the other tests has an abbreviation; each term of the tests of abbreviations has one*)
  val _ = \<^assert> (not (exists (C.need_expand abbrs) (props @ closed)));
  val _ = \<^assert> (forall (C.need_expand abbrs) (abbrev_consts @ maps (fn (_, f) => map f abase) abbrev_terms));
  val _ = \<^assert> (length abbrev_consts > 20);
end
\<close>

end
