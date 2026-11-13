section \<open>Support for the differential tests\<close>

theory Pure_Test_Support
  imports Main
begin

text \<open>
  The differential tests compare the outcomes of Isabelle's functions and of the generated code
  as strings. \<open>Exact\<close> writes the values in full: unlike \<^verbatim>\<open>\<^make_string>\<close>, it has no print
  depth and shows the sorts of type variables. A value whose text is longer than 64 KB is
  represented by the first characters, the length and a 64-bit hash value of its text, so that
  the comparison of such values is exact up to collisions of the hash function. A value whose
  text is longer than 2 MB is represented by its first 1000 characters only; the reports count
  the problems with such outcomes (\<open>large\<close>), on which the comparison is not exact.
  \<open>Test_Stat\<close> compares the outcomes of a list of problems and keeps only the mismatches.
\<close>

ML \<open>
structure Exact =
struct

(*A buffer that holds its content up to a limit. Beyond the limit it holds the first characters,
  the length and a hash value (FNV-1a, 64 bit) of the content, and beyond the cap it gives up:
  the text of some terms of HOL, whose types are shared, has hundreds of megabytes.*)
datatype buf =
  Buf of {chunks: string list, pending: int, hash: LargeWord.word, total: int, head: string,
    hashed: bool};

val limit = 65536;
val cap = 2000000;

exception LARGE of string;

val empty =
  Buf {chunks = [], pending = 0, hash = 0wxcbf29ce484222325, total = 0, head = "", hashed = false};

fun hash_string s h =
  CharVector.foldl (fn (c, h) =>
    LargeWord.* (LargeWord.xorb (h, LargeWord.fromInt (Char.ord c)), 0wx100000001b3)) h s;

fun flush (Buf {chunks, hash, total, head, ...}) =
  let val s = String.concat (rev chunks) in
    Buf {chunks = [], pending = 0, hash = hash_string s hash, total = total,
      head = if head = "" then String.substring (s, 0, Int.min (String.size s, 1000)) else head,
      hashed = true}
  end;

fun add s (Buf {chunks, pending, hash, total, head, hashed}) =
  let
    val n = String.size s;
    val b =
      Buf {chunks = s :: chunks, pending = pending + n, hash = hash, total = total + n,
        head = head, hashed = hashed};
  in
    if total + n > cap then raise LARGE head
    else if pending + n > limit then flush b
    else b
  end;

type 'a T = 'a -> buf -> buf;

fun string s = add (ML_Syntax.print_string s);
fun int (i: int) = add (string_of_int i);
fun bool b = add (Bool.toString b);
fun con c (f: 'a T) x = add c #> add "(" #> f x #> add ")";
fun list (f: 'a T) xs = add "[" #> fold (fn x => f x #> add ";") xs #> add "]";
fun pair (f: 'a T) (g: 'b T) (x, y) = f x #> add "," #> g y;
fun triple (f: 'a T) (g: 'b T) (h: 'c T) (x, y, z) =
  f x #> add "," #> g y #> add "," #> h z;
fun option _ NONE = add "NONE"
  | option f (SOME x) = con "SOME" f x;

val sort: sort T = list string;
val indexname: indexname T = con "" (pair string int);

fun typ (Type (a, Ts)) = con "Type" (pair string (list typ)) (a, Ts)
  | typ (TFree (a, S)) = con "TFree" (pair string sort) (a, S)
  | typ (TVar (xi, S)) = con "TVar" (pair indexname sort) (xi, S);

fun term (Const (c, T)) = con "Const" (pair string typ) (c, T)
  | term (Free (x, T)) = con "Free" (pair string typ) (x, T)
  | term (Var (xi, T)) = con "Var" (pair indexname typ) (xi, T)
  | term (Bound i) = con "Bound" int i
  | term (Abs (a, T, t)) = con "Abs" (triple string typ term) (a, T, t)
  | term (t $ u) = con "App" (pair term term) (t, u);

val tpairs: (term * term) list T = list (con "" (pair term term));

fun ztyp (ZTVar (xi, S)) = con "ZTVar" (pair indexname sort) (xi, S)
  | ztyp (ZFun (T, U)) = con "ZFun" (pair ztyp ztyp) (T, U)
  | ztyp ZProp = add "ZProp"
  | ztyp (ZType0 a) = con "ZType0" string a
  | ztyp (ZType1 (a, T)) = con "ZType1" (pair string ztyp) (a, T)
  | ztyp (ZType (a, Ts)) = con "ZType" (pair string (list ztyp)) (a, Ts);

fun zterm (ZVar (xi, T)) = con "ZVar" (pair indexname ztyp) (xi, T)
  | zterm (ZBound i) = con "ZBound" int i
  | zterm (ZConst0 c) = con "ZConst0" string c
  | zterm (ZConst1 (c, T)) = con "ZConst1" (pair string ztyp) (c, T)
  | zterm (ZConst (c, Ts)) = con "ZConst" (pair string (list ztyp)) (c, Ts)
  | zterm (ZAbs (a, T, t)) = con "ZAbs" (triple string ztyp zterm) (a, T, t)
  | zterm (ZApp (t, u)) = con "ZApp" (pair zterm zterm) (t, u)
  | zterm (OFCLASS (T, c)) = con "OFCLASS" (pair ztyp string) (T, c);

(*the instances of a proof constant, in the order of their keys*)
val zinsts: (ztyp ZTVars.table * zterm ZVars.table) T =
  pair (list (con "" (pair (pair indexname sort) ztyp)) o ZTVars.dest)
    (list (con "" (pair (pair indexname ztyp) zterm)) o ZVars.dest);

val env: Envir.env T = fn Envir.Envir {maxidx, tenv, tyenv} =>
  triple int
    (list (con "" (pair indexname (pair typ term))) o Vartab.dest)
    (list (con "" (pair indexname (pair sort typ))) o Vartab.dest) (maxidx, tenv, tyenv);

(*the content in full, or its first characters, length and hash value, or only its first
  characters*)
val large = " ... (large)";

fun content (f: 'a T) x =
  (case f x empty of
    Buf {hashed = false, chunks, ...} => String.concat (rev chunks)
  | b =>
      let val Buf {hash, total, head, ...} = flush b in
        head ^ " ... (" ^ string_of_int total ^ " characters, hash " ^ LargeWord.toString hash ^ ")"
      end)
  handle LARGE head => head ^ large;

val is_large = String.isSubstring large;

end;
\<close>

ML \<open>
structure Test_Stat =
struct

(*the outcomes of the original (first) and of the generated code (second) on one problem; NONE
  stands for a timeout*)
type mismatch = string * string option * string option;

type report =
  {name: string, tests: int, run: int, nonempty: int, exns: int, large: int,
    mismatches: mismatch list};

(*Compare the outcomes on each problem. Only the mismatches are kept, the first few in full.
  An outcome that begins with "END" is an empty sequence, one that begins with "EXN" an
  exception.*)
fun compare name (show: 'a -> string) (f: 'a -> string option) (g: 'a -> string option)
    (xs: 'a list) : report =
  let
    fun cut s = if size s > 4000 then String.substring (s, 0, 4000) ^ " ..." else s;
    fun step x (run, nonempty, exns, large, mism) =
      let
        val a = f x;
        (*a problem on which the original runs out of time is not given to the generated code*)
        val b = if is_none a then NONE else g x;
        val timeout = is_none a orelse is_none b;
        fun first_is pre = (case a of SOME s => String.isPrefix pre s | NONE => false);
        val mism' =
          if not timeout andalso a <> b then
            (if length mism < 5 then (show x, Option.map cut a, Option.map cut b)
             else ("", NONE, NONE)) :: mism
          else mism;
      in
        (if timeout then run else run + 1,
         if is_some a andalso not (first_is "END" orelse first_is "EXN") then nonempty + 1
         else nonempty,
         if first_is "EXN" then exns + 1 else exns,
         if (case a of SOME s => Exact.is_large s | NONE => false) then large + 1 else large,
         mism')
      end;
    val (run, nonempty, exns, large, mism) = fold step xs (0, 0, 0, 0, []);
  in
    {name = name, tests = length xs, run = run, nonempty = nonempty, exns = exns, large = large,
      mismatches = rev mism}
  end;

fun report ({name, tests, run, nonempty, exns, large, mismatches}: report) =
  name ^ ": " ^ string_of_int tests ^ " problems, " ^ string_of_int run ^ " run, " ^
  string_of_int nonempty ^ " with results, " ^ string_of_int exns ^ " with exceptions, " ^
  string_of_int large ^ " large, " ^ string_of_int (length mismatches) ^ " mismatches";

fun show_mismatches ({name, mismatches, ...}: report) =
  name ^ ":\n" ^ cat_lines (take 2 mismatches |> map (fn (x, a, b) =>
    "  problem " ^ x ^ "\n  original " ^ the_default "TIMEOUT" a ^
    "\n  generated " ^ the_default "TIMEOUT" b));

(*No mismatch, and each test has run on some problem and has had a result that is not an
  exception on some problem (unless it is listed in exns_only).*)
fun check_with (exns_only: string list) (rs: report list) =
  let
    val bad = filter (not o null o #mismatches) rs;
    val idle = filter (fn r => #run r = 0) rs;
    val no_results =
      filter (fn r => #nonempty r = 0 andalso not (member (op =) exns_only (#name r))) rs;
  in
    if not (null bad) then error (cat_lines (map show_mismatches bad))
    else if not (null idle) then error ("Tests without problems: " ^ commas_quote (map #name idle))
    else if not (null no_results) then
      error ("Tests without results: " ^ commas_quote (map #name no_results))
    else ()
  end;

val check = check_with [];

end;
\<close>

text \<open>
  The reference of the tests is the running Isabelle. \<open>Test_System.patched\<close> tells whether it has
  the patches of \<^verbatim>\<open>patches/\<close>: the probes below show the behaviour of one patch of each group
  (\<^verbatim>\<open>pattern.ML\<close>, \<^verbatim>\<open>unify.ML\<close>, the classic proofs of \<^verbatim>\<open>thm.ML\<close>, tight proofs, the last patch), and they
  must agree, since the tests support Isabelle2026 as released (with patches 07 and 08, which
  the installed system may have) and with all patches, but nothing in between.
\<close>

ML \<open>
structure Test_System =
struct

local
  val ctxt = \<^context>;
  val thy = \<^theory>;
  val context = Context.Proof ctxt;
  val cert = Thm.cterm_of ctxt;

  (*patch 01: a non-rigid occurrence of the flexible head raises Pattern, not Unif*)
  val pattern =
    let
      val p = Var (("p", 0), \<^typ>\<open>bool\<close>) and f = Var (("f", 0), \<^typ>\<open>bool \<Rightarrow> bool\<close>);
    in
      (Pattern.unify context (p, \<^Const>\<open>Not\<close> $ (f $ p)) (Envir.empty 0); false)
        handle Pattern.Pattern => true | Pattern.Unif => false
    end;

  (*patch 03: the flex-flex pair \<lambda>j. ?F (\<lambda>z. z j) =?= \<lambda>j. ?G is kept*)
  val unify =
    let
      val a = TFree ("'a", []) and b = TFree ("'b", []);
      val t = Abs ("j", a, Var (("F", 0), ((a --> b) --> b) --> b) $ Abs ("z", a --> b, Bound 0 $ Bound 1));
      val u = Abs ("j", a, Var (("G", 0), b));
    in
      (case Seq.list_of (Unify.hounifiers [] (context, Envir.empty 0, [(t, u)])) of
        [(env, _)] => not (Vartab.defined (Envir.term_env env) ("F", 0))
      | _ => error "Test_System: unexpected unifiers")
    end;

  fun with_proofs n f x =
    let
      val proofs = ! Proofterm.proofs;
      val _ = Proofterm.proofs := n;
      val r = Exn.result f x;
      val _ = Proofterm.proofs := proofs;
    in Exn.release r end;

  (*patch 10: the classic proof of Thm.assumption checks if the unifier instantiates the
    conclusion by an implication*)
  val thm =
    let
      val A = Free ("A", propT) and B = Free ("B", propT);
      val th = with_proofs 2 (fn () =>
        Seq.hd (Thm.assumption (SOME ctxt) 1
          (Goal.init (cert (Logic.mk_implies (Logic.mk_implies (A, B), Var (("P", 0), propT))))))) ();
    in
      can (Proof_Checker.thm_of_proof thy o Proofterm.reconstruct_proof thy (Thm.prop_of th))
        (Thm.proof_of th)
    end;

  (*patch 25: the tight proof of Thm.combination instantiates 'a by the type of the arguments*)
  val zterm =
    let
      val T = TFree ("'t", []) and U = TFree ("'u", []);
      val th = with_proofs 4 (fn () =>
        Thm.combination
          (Thm.assume (cert (Logic.mk_equals (Free ("f", T --> U), Free ("g", T --> U)))))
          (Thm.assume (cert (Logic.mk_equals (Free ("x", T), Free ("y", T)))))) ();
    in
      (case Thm.zproof_of th of
        ZAppp (ZAppp (ZConstp (_, (instT, _)), _), _) =>
          exists (fn (((a, _), _), A) => a = "'a" andalso ZTerm.typ_of A = T) (ZTVars.dest instT)
      | _ => error "Test_System: unexpected proof")
    end;

  (*patch 26: Thm.instantiate rejects a variable of index -1*)
  val inst =
    (Thm.instantiate (TVars.empty, Vars.make1 ((("x", ~1), propT), cert (Free ("c", propT))))
      (Thm.trivial (cert (Free ("x", propT)))); false)
    handle THM _ => true;

  val probes =
    [("pattern", pattern), ("unify", unify), ("thm", thm), ("zterm", zterm), ("instantiate", inst)];
in

val patched =
  if forall #2 probes then true
  else if not (exists #2 probes) then false
  else
    error ("The patches are applied in part: " ^
      commas (map (fn (a, b) => a ^ (if b then " patched" else " not patched")) probes));

end;

end;
\<close>

ML \<open>
  writeln ("The reference is Isabelle " ^
    (if Test_System.patched then "with all patches" else "without the patches"))
\<close>

end
