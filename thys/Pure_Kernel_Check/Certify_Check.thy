section \<open>Checking Certified Terms and Types\<close>

theory Certify_Check
  imports "Pure_Pattern.Pure_Test_Support"
begin

text \<open>
  The models of the inference rules take certified terms and types as they are: a certified term
  is closed and well-typed over the signature, with the recorded type, its indices are between
  \<open>0\<close> and the recorded maximal index, and its sorts are recorded (\<open>cterm_ok\<close> in session
  \<open>Thm_Correctness\<close>). The certification itself, \<open>Sign.certify_term\<close> and \<open>Type.cert_typ\<close> behind
  \<open>Thm.global_cterm_of\<close> and \<open>Thm.global_ctyp_of\<close>, is not modelled. This test checks that
  assumption on the running system, with a checker of its own: the propositions of the theorems
  of HOL and their subterms are certified and pass the checker, and terms that violate one of
  the conditions are rejected. Certification expands type abbreviations, and it keeps a sort
  as it is (its classes are declared; it need not be minimal): such terms are certified, to
  terms that pass the checker.

  The checker follows the definition of the models. A type is well formed if its constructors
  are declared with their number of arguments, its classes are declared, and its variables have
  indices from \<open>0\<close>. A constant has an instance of its declared type; as in Isabelle, the
  instance need not respect the sorts of the declared type.
\<close>

ML \<open>
structure Certify_Check =
struct

exception CHECK of string;

fun typ_ok thy =
  let
    val classes = Symtab.make_set (Sign.all_classes thy);
    fun sort_ok S = forall (Symtab.defined classes) S;
    fun ok (Type (a, Ts)) =
          (Sign.arity_number thy a = length Ts handle ERROR _ => false) andalso forall ok Ts
      | ok (TFree (_, S)) = sort_ok S
      | ok (TVar ((_, i), S)) = i >= 0 andalso sort_ok S;
  in ok end;

(*the declared type (with schematic type variables) against an instance*)
fun match_typ (TVar (v, _), T) tab =
      (case AList.lookup (op =) tab v of
        NONE => (v, T) :: tab
      | SOME U => if U = T then tab else raise CHECK "instance")
  | match_typ (Type (a, Ts), Type (b, Us)) tab =
      if a = b andalso length Ts = length Us then fold match_typ (Ts ~~ Us) tab
      else raise CHECK "instance"
  | match_typ _ _ = raise CHECK "instance";

(*the type of a closed term, CHECK if it is not well formed*)
fun type_of thy =
  let
    val tok = typ_ok thy;
    fun check_typ T = if tok T then T else raise CHECK "type";
    fun typ _ (Const (c, T)) =
          (case Sign.const_type thy c of
            SOME U => (ignore (match_typ (U, T) []); check_typ T)
          | NONE => raise CHECK "constant")
      | typ _ (Free (_, T)) = check_typ T
      | typ _ (Var ((_, i), T)) = if i >= 0 then check_typ T else raise CHECK "index"
      | typ Ts (Bound i) =
          if 0 <= i andalso i < length Ts then nth Ts i else raise CHECK "loose bound variable"
      | typ Ts (Abs (_, T, b)) = check_typ T --> typ (T :: Ts) b
      | typ Ts (f $ u) =
          (case typ Ts f of
            Type ("fun", [A, B]) => if A = typ Ts u then B else raise CHECK "argument"
          | _ => raise CHECK "function");
  in typ [] end;

fun term_ok thy t = (ignore (type_of thy t); true) handle CHECK _ => false;

val sorts_of_typ = fold_atyps (fn TFree (_, S) => insert (op =) S | TVar (_, S) => insert (op =) S | _ => I);
fun sorts_of_term t = fold_types sorts_of_typ t [];

val maxidx_of_typ = fn T => fold_atyps (fn TVar ((_, i), _) => Integer.max i | _ => I) T ~1;
fun maxidx_of_term t =
  fold_aterms (fn Var ((_, i), _) => Integer.max i | _ => I) t
    (fold_types (fn T => Integer.max (maxidx_of_typ T)) t ~1);

(*the defects of a certified term: the sorts are those that a theorem takes from it*)
fun cterm_defects thy ct =
  let
    val t = Thm.term_of ct;
    val shyps = Thm.shyps_of (Thm.reflexive ct);
  in
    (case try (type_of thy) t of
      NONE => ["not well formed"]
    | SOME T => if T = Thm.typ_of_cterm ct then [] else ["recorded type"]) @
    (if maxidx_of_term t <= Thm.maxidx_of_cterm ct andalso ~1 <= Thm.maxidx_of_cterm ct then []
     else ["maximal index"]) @
    (if subset (op =) (sorts_of_term t, shyps) then [] else ["sorts"])
  end;

fun ctyp_defects thy cT =
  let val T = Thm.typ_of cT in
    (if typ_ok thy T then [] else ["not well formed"]) @
    (if maxidx_of_typ T <= Thm.maxidx_of_ctyp cT then [] else ["maximal index"])
  end;

(*the outcome of the certification of the terms of one group: the number of terms, of certified
  terms, of certified terms that the certification has changed, of terms that the checker
  accepts as they are, the defects of certified terms, and the terms that the checker accepts
  but the certification rejects*)
type report =
  {name: string, tests: int, certified: int, changed: int, accepted: int,
    defects: (string * string list) list, lax: string list};

fun run_group cert term_of defects accepts show name xs : report =
  let
    fun step x (certified, changed, accepted, bad, lax) =
      let
        val acc = accepts x;
        val accepted' = if acc then accepted + 1 else accepted;
      in
        (case try cert x of
          NONE => (certified, changed, accepted', bad, if acc then show x :: lax else lax)
        | SOME c =>
            let val ds = defects c in
              (certified + 1, if term_of c = x then changed else changed + 1, accepted',
                if null ds then bad else (show x, ds) :: bad, lax)
            end)
      end;
    val (certified, changed, accepted, bad, lax) = fold step xs (0, 0, 0, [], []);
  in
    {name = name, tests = length xs, certified = certified, changed = changed, accepted = accepted,
      defects = rev bad, lax = rev lax}
  end;

fun report ({name, tests, certified, changed, accepted, defects, lax}: report) =
  name ^ ": " ^ string_of_int tests ^ " problems, " ^ string_of_int certified ^ " certified (" ^
  string_of_int changed ^ " changed), " ^ string_of_int accepted ^ " accepted by the checker, " ^
  string_of_int (length defects) ^ " defects, " ^ string_of_int (length lax) ^
  " accepted by the checker only";

end;
\<close>

ML \<open>
local
  open Certify_Check;
  val thy = \<^theory>;
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
  (*terms that violate one condition of well-formedness*)
  val bad_terms =
   [("an argument of another type", fn t => t $ t),
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
    ("a negative bound variable", fn t => Abs (x, propT, Abs (x, propT, t) $ Bound ~1))];
  (*terms that certification accepts, some of them after a change*)
  val odd_terms =
   [("a sort with redundant classes",
      fn t => Abs (x, TFree ("'x", [\<^class>\<open>ord\<close>, \<^class>\<open>order\<close>, \<^class>\<open>type\<close>]), t)),
    ("a type abbreviation", fn t => Abs (x, Type (\<^type_abbrev>\<open>rel\<close>, [\<^typ>\<open>nat\<close>]), t)),
    ("a constant outside the sort of its declared type",
      fn t => Abs (x, \<^typ>\<open>bool\<close>, t) $ Const (\<^const_name>\<open>zero_class.zero\<close>, \<^typ>\<open>bool\<close>))];

  val show = Exact.content Exact.term;
  fun group name ts =
    run_group (Thm.global_cterm_of thy) Thm.term_of (cterm_defects thy) (term_ok thy) show name ts;
  val r_props = group "propositions of theorems" props;
  val r_closed = group "closed subterms" closed;
  val r_bad = map (fn (name, f) => group name (map f base)) bad_terms;
  val r_odd = map (fn (name, f) => group name (map f base)) odd_terms;

  (*types*)
  val typs = fold (fold_types (insert (op =))) (take 3000 props) [] |> take 4000;
  val bad_typs =
   [("types: a type constructor without an argument", fn T => Type ("fun", [T])),
    ("types: an undeclared type constructor", fn T => Type (undeclared, [T])),
    ("types: an undeclared class", fn T => T --> TFree ("'x", [undeclared])),
    ("types: a type variable of index -1", fn T => T --> TVar (("'x", ~1), []))];
  val showT = Exact.content Exact.typ;
  fun groupT name Ts =
    run_group (Thm.global_ctyp_of thy) Thm.typ_of (ctyp_defects thy) (typ_ok thy) showT name Ts;
  val r_typs = groupT "types of theorems" typs;
  val r_bad_typs = map (fn (name, f) => groupT name (map f (take 1500 typs))) bad_typs;

  val good = [r_props, r_closed, r_typs];
  val bad = r_bad @ r_bad_typs;
  val all = good @ bad @ r_odd;
in
  val _ = writeln (cat_lines (map report all));
  (*no certified term or type has a defect*)
  val _ =
    (case maps #defects all of
      [] => ()
    | ds => error ("Certified terms with defects: " ^ \<^make_string> (take 3 ds)));
  (*the terms of the theorems are certified as they are, and the checker accepts them*)
  val _ = \<^assert> (forall (fn r => #certified r = #tests r andalso #changed r = 0 andalso
    #accepted r = #tests r andalso #tests r > 0) good);
  (*no term with a violation is certified, and the checker rejects each of them*)
  val _ = \<^assert> (forall (fn r => #certified r = 0 andalso #accepted r = 0 andalso #tests r > 0) bad);
  (*the other terms are certified; the checker accepts no term that certification rejects*)
  val _ = \<^assert> (forall (fn r => #certified r = #tests r) r_odd);
  val _ = \<^assert> (forall (null o #lax) all);
end
\<close>

end
