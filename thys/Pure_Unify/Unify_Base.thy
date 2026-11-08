section \<open>Exceptions, Tracing and Environments for \<open>unify.ML\<close>\<close>

theory Unify_Base
  imports "Pure_Pattern.Pure_Pattern"
begin

text \<open>
  The model of \<^file>\<open>~~/src/Pure/unify.ML\<close> builds on the model of Pure's terms,
  environments and pattern unification (session \<open>Pure_Pattern\<close>). This theory adds the
  exceptions and the tracing of \<open>unify.ML\<close>, a monad for them, and further operations of
  \<^file>\<open>~~/src/Pure/envir.ML\<close>, \<^file>\<open>~~/src/Pure/term.ML\<close> and \<^file>\<open>~~/src/Pure/logic.ML\<close>.
\<close>


subsection \<open>Exceptions\<close>

text \<open>
  The exceptions of \<open>unify.ML\<close> (\<open>CANTUNIFY\<close>, \<open>ASSIGN\<close>, \<open>CHANGE_FAIL\<close>), the failure of an ML
  pattern binding (\<open>Bind\<close>), and the exceptions of the functions of session \<open>Pure_Pattern\<close>.
\<close>

datatype uexn =
  PExn exn
| CANTUNIFY
| ASSIGN
| CHANGE_FAIL
| Bind


subsection \<open>Tracing\<close>

type_synonym dpair = "binders \<times> pterm \<times> pterm"

text \<open>
  The messages that \<open>unify.ML\<close> prints while it searches: failures of type unification
  (traced by \<open>Pattern.unify_types\<close> under \<open>unify_trace_failure\<close>), potential losses of
  completeness in type unification (\<open>unify_trace_types\<close>), the disagreement pairs before
  \<open>SIMPL\<close> and \<open>MATCH\<close>, failure nodes, and the warning that the search bound was exceeded.
  The ML wrapper prints them, subject to the configuration options of the context.
\<close>

datatype event =
  Ev_Unif unif_trace
| Ev_Loss ptyp ptyp
| Ev_Dpairs String.literal env "dpair list"
| Ev_Failure_Node
| Ev_Bound_Exceeded


subsection \<open>The monad\<close>

text \<open>
  A computation produces a list of events, and then returns a value or raises an exception;
  the outer \<^typ>\<open>'a option\<close> models divergence, as in \<^typ>\<open>'a M\<close>.
\<close>

type_synonym ('a, 'l, 'e) WE = "('l list \<times> ('a, 'e) xres) option"

type_synonym 'a W = "('a, event, uexn) WE"

definition returnW :: "'a \<Rightarrow> ('a, 'l, 'e) WE" where
  "returnW x = Some ([], Ok x)"

definition raiseW :: "'e \<Rightarrow> ('a, 'l, 'e) WE" where
  "raiseW e = Some ([], Err e)"

definition emit :: "'l \<Rightarrow> (unit, 'l, 'e) WE" where
  "emit ev = Some ([ev], Ok ())"

definition bindW :: "('a, 'l, 'e) WE \<Rightarrow> ('a \<Rightarrow> ('b, 'l, 'e) WE) \<Rightarrow> ('b, 'l, 'e) WE" where
  "bindW m f =
    (case m of
      None \<Rightarrow> None
    | Some (evs, Err e) \<Rightarrow> Some (evs, Err e)
    | Some (evs, Ok x) \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (f x))"

definition handleW :: "('a, 'l, 'e) WE \<Rightarrow> ('e \<Rightarrow> ('a, 'l, 'e) WE) \<Rightarrow> ('a, 'l, 'e) WE" where
  "handleW m h =
    (case m of
      Some (evs, Err e) \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (h e)
    | _ \<Rightarrow> m)"

text \<open>Computations of session \<open>Pure_Pattern\<close> produce no events.\<close>

definition liftM :: "'a M \<Rightarrow> 'a W" where
  "liftM m =
    (case m of
      None \<Rightarrow> None
    | Some (Ok x) \<Rightarrow> Some ([], Ok x)
    | Some (Err e) \<Rightarrow> Some ([], Err (PExn e)))"

definition whenW :: "bool \<Rightarrow> (unit, 'l, 'e) WE \<Rightarrow> (unit, 'l, 'e) WE" where
  "whenW b m = (if b then m else returnW ())"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bindW

lemma bindW_simps[simp]:
  "bindW (returnW x) f = f x"
  "bindW (raiseW e) f = raiseW e"
  "bindW None f = None"
  by (auto simp: bindW_def returnW_def raiseW_def option.map_id split: option.splits)

lemma bindW_returnW[simp]: "bindW m returnW = m"
  by (auto simp: bindW_def returnW_def split: option.splits xres.splits)

lemma bindW_assoc: "bindW (bindW m f) g = bindW m (\<lambda>x. bindW (f x) g)"
  by (auto simp: bindW_def option.map_comp o_def split: option.splits xres.splits prod.splits
    intro!: option.map_cong)

lemma handleW_simps[simp]:
  "handleW (returnW x) h = returnW x"
  "handleW (raiseW e) h = h e"
  "handleW None h = None"
  by (auto simp: handleW_def returnW_def raiseW_def option.map_id split: option.splits)

lemma liftM_simps[simp]:
  "liftM (return x) = returnW x"
  "liftM (raise e) = raiseW (PExn e)"
  "liftM None = None"
  by (simp_all add: liftM_def return_def raise_def returnW_def raiseW_def)

lemma bindW_cong[fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>x. (\<exists>evs. m' = Some (evs, Ok x)) \<Longrightarrow> f x = f' x) \<Longrightarrow>
    bindW m f = bindW m' f'"
  by (auto simp: bindW_def split: option.splits xres.splits)

lemma handleW_cong[fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>e. (\<exists>evs. m' = Some (evs, Err e)) \<Longrightarrow> h e = h' e) \<Longrightarrow>
    handleW m h = handleW m' h'"
  by (auto simp: handleW_def split: option.splits xres.splits)

lemma map_option_mono:
  assumes "mono_option B"
  shows "mono_option (\<lambda>f. map_option g (B f))"
proof -
  have "map_option g (B f) = Option.bind (B f) (\<lambda>x. Some (g x))" for f
    by (cases "B f") simp_all
  then show ?thesis by (simp add: bind_mono[OF assms] option.const_mono)
qed

lemma bindW_alt:
  "bindW m f = Option.bind m (\<lambda>p. case snd p of
      Ok y \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (f y)
    | Err e \<Rightarrow> Some (fst p, Err e))"
  by (auto simp: bindW_def split: option.splits xres.splits)

lemma handleW_alt:
  "handleW m h = Option.bind m (\<lambda>p. case snd p of
      Ok y \<Rightarrow> Some (fst p, Ok y)
    | Err e \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (h e))"
  by (auto simp: handleW_def split: option.splits xres.splits)

lemma bindW_mono[partial_function_mono]:
  assumes "mono_option B" "\<And>y. mono_option (\<lambda>f. C y f)"
  shows "mono_option (\<lambda>f. bindW (B f) (\<lambda>y. C y f))"
  unfolding bindW_alt
proof (rule bind_mono[OF assms(1)])
  fix p
  show "mono_option (\<lambda>f. case snd p of
      Ok y \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (C y f)
    | Err e \<Rightarrow> Some (fst p, Err e))"
    using assms(2) by (cases "snd p") (simp_all add: map_option_mono option.const_mono)
qed

lemma handleW_mono[partial_function_mono]:
  assumes "mono_option B" "\<And>e. mono_option (\<lambda>f. H e f)"
  shows "mono_option (\<lambda>f. handleW (B f) (\<lambda>e. H e f))"
  unfolding handleW_alt
proof (rule bind_mono[OF assms(1)])
  fix p
  show "mono_option (\<lambda>f. case snd p of
      Ok y \<Rightarrow> Some (fst p, Ok y)
    | Err e \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (H e f))"
    using assms(2) by (cases "snd p") (simp_all add: map_option_mono option.const_mono)
qed

text \<open>Code equations that avoid appending empty lists of events.\<close>

lemma bindW_code[code]:
  "bindW m f =
    (case m of
      None \<Rightarrow> None
    | Some (evs, Err e) \<Rightarrow> Some (evs, Err e)
    | Some (evs, Ok x) \<Rightarrow>
        (case evs of [] \<Rightarrow> f x | _ \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (f x)))"
  by (auto simp: bindW_def option.map_id split: option.splits xres.splits list.splits)

lemma handleW_code[code]:
  "handleW m h =
    (case m of
      Some (evs, Err e) \<Rightarrow>
        (case evs of [] \<Rightarrow> h e | _ \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (h e))
    | _ \<Rightarrow> m)"
  by (auto simp: handleW_def option.map_id split: option.splits xres.splits list.splits)


subsection \<open>Monadic iteration\<close>

text \<open>\<open>fold\<close>, \<open>fold_rev\<close>, \<open>map\<close> and \<open>exists\<close> with a monadic function.\<close>

fun foldW :: "('a \<Rightarrow> 'b \<Rightarrow> ('b, 'l, 'e) WE) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> ('b, 'l, 'e) WE" where
  "foldW f [] b = returnW b"
| "foldW f (x # xs) b = do {b' \<leftarrow> f x b; foldW f xs b'}"

fun foldrW :: "('a \<Rightarrow> 'b \<Rightarrow> ('b, 'l, 'e) WE) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> ('b, 'l, 'e) WE" where
  "foldrW f [] b = returnW b"
| "foldrW f (x # xs) b = do {b' \<leftarrow> foldrW f xs b; f x b'}"

fun mapW :: "('a \<Rightarrow> ('b, 'l, 'e) WE) \<Rightarrow> 'a list \<Rightarrow> ('b list, 'l, 'e) WE" where
  "mapW f [] = returnW []"
| "mapW f (x # xs) = do {y \<leftarrow> f x; ys \<leftarrow> mapW f xs; returnW (y # ys)}"

lemma foldW_mono[partial_function_mono]:
  assumes "\<And>x b. mono_option (\<lambda>f. C x b f)"
  shows "mono_option (\<lambda>f. foldW (\<lambda>x b. C x b f) xs b)"
  using assms
  by (induction xs arbitrary: b) (auto intro!: bindW_mono simp: returnW_def option.const_mono)

lemma foldrW_mono[partial_function_mono]:
  assumes "\<And>x b. mono_option (\<lambda>f. C x b f)"
  shows "mono_option (\<lambda>f. foldrW (\<lambda>x b. C x b f) xs b)"
  using assms
  by (induction xs arbitrary: b) (auto intro!: bindW_mono simp: returnW_def option.const_mono)

lemma mapW_mono[partial_function_mono]:
  assumes "\<And>x. mono_option (\<lambda>f. C x f)"
  shows "mono_option (\<lambda>f. mapW (\<lambda>x. C x f) xs)"
  using assms
  by (induction xs) (auto intro!: bindW_mono simp: returnW_def option.const_mono)

lemma foldW_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> b = b' \<Longrightarrow> (\<And>x b. x \<in> set ys \<Longrightarrow> f x b = g x b) \<Longrightarrow> foldW f xs b = foldW g ys b'"
  by (induction ys arbitrary: xs b b') (auto intro!: bindW_cong)

lemma foldrW_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> b = b' \<Longrightarrow> (\<And>x b. x \<in> set ys \<Longrightarrow> f x b = g x b) \<Longrightarrow> foldrW f xs b = foldrW g ys b'"
  by (induction ys arbitrary: xs b b') (auto intro!: bindW_cong)

lemma mapW_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> mapW f xs = mapW g ys"
  by (induction ys arbitrary: xs) (auto intro!: bindW_cong)


subsection \<open>Operations on types and terms\<close>

text \<open>Functions of \<^file>\<open>~~/src/Pure/term.ML\<close> and \<^file>\<open>~~/src/Pure/logic.ML\<close>.\<close>

fun is_TVar :: "ptyp \<Rightarrow> bool" where
  "is_TVar (TVar _ _) = True"
| "is_TVar _ = False"

fun head_of :: "pterm \<Rightarrow> pterm" where
  "head_of (f $ _) = head_of f"
| "head_of t = t"

fun strip_abs_body :: "pterm \<Rightarrow> pterm" where
  "strip_abs_body (Abs _ _ t) = strip_abs_body t"
| "strip_abs_body t = t"

text \<open>\<open>Logic.rlist_abs ([xn,...,x1], t) = \<lambda>x1 ... xn. t\<close>\<close>

fun rlist_abs :: "binders \<Rightarrow> pterm \<Rightarrow> pterm" where
  "rlist_abs [] body = body"
| "rlist_abs ((a, T) # ps) body = rlist_abs ps (Abs a T body)"

text \<open>\<open>Logic.combound (t, n, k) = t (Bound (n + k - 1)) ... (Bound n)\<close>\<close>

fun combound :: "pterm \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> pterm" where
  "combound t n 0 = t"
| "combound t n (Suc k) = combound t (n + 1) k $ Bound n"

text \<open>Abstraction over a list of types (\<open>types_abs\<close> of \<open>unify.ML\<close>).\<close>

fun types_abs :: "ptyp list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "types_abs [] u = u"
| "types_abs (T # Ts) u = Abs STR '''' T (types_abs Ts u)"

text \<open>\<open>k - 1 downto 0\<close> and \<open>0 upto k - 1\<close> of the ML library.\<close>

definition downto0_list :: "nat \<Rightarrow> integer list" where
  "downto0_list k = rev (map integer_of_nat [0..<k])"

definition upto_list :: "nat \<Rightarrow> integer list" where
  "upto_list k = map integer_of_nat [0..<k]"


subsection \<open>Environments\<close>

text \<open>Functions of \<^file>\<open>~~/src/Pure/envir.ML\<close>.\<close>

text \<open>\<open>radixstring (26, "a", n)\<close> of the ML library, for \<open>n \<ge> 0\<close>.\<close>

fun radix26 :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "radix26 n tail = (if n < 26 then n # tail else radix26 (n div 26) ((n mod 26) # tail))"

declare radix26.simps[simp del]

definition radixstring :: "integer \<Rightarrow> String.literal" where
  "radixstring n = String.implode (map (\<lambda>d. char_of (97 + d)) (radix26 (nat_of_integer n) []))"

text \<open>\<open>Envir.genvars\<close>: new variables with index \<open>maxidx + 1\<close>; the last one has the given name.\<close>

fun genvs :: "name \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> ptyp list \<Rightarrow> pterm list" where
  "genvs name i n [] = []"
| "genvs name i n [T] = [Var (name, i) T]"
| "genvs name i n (T # Ts) = Var (name + radixstring n, i) T # genvs name i (n + 1) Ts"

definition genvars :: "name \<Rightarrow> env \<Rightarrow> ptyp list \<Rightarrow> env \<times> pterm list" where
  "genvars name env Ts =
    (case env of Envir i te tye \<Rightarrow> (Envir (i + 1) te tye, genvs name (i + 1) 0 Ts))"

text \<open>\<open>Envir.vupdate\<close>: update, checking \<open>Var\<close>-\<open>Var\<close> assignments.\<close>

partial_function (option) vupdate :: "indexname \<times> ptyp \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> env M" where
  "vupdate aU t env =
    (case t of
      Var name' T \<Rightarrow>
        if fst aU = name' then return env
        else if indexname_less (fst aU) name' then do {
          r \<leftarrow> lookup env name' T;
          case r of
            None \<Rightarrow> update (name', T) (Var (fst aU) T) env
          | Some u \<Rightarrow> vupdate aU u env}
        else update aU t env
    | _ \<Rightarrow> update aU t env)"

text \<open>\<open>Envir.body_type\<close>, \<open>Envir.binder_types\<close> and \<open>Envir.strip_type\<close>; they may diverge on
  cyclic type environments.\<close>

partial_function (option) body_type :: "env \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "body_type env T =
    (case T of
      Type a Ts \<Rightarrow> (case Ts of [_, U] \<Rightarrow> if a = STR ''fun'' then body_type env U else return T | _ \<Rightarrow> return T)
    | TVar v S \<Rightarrow> do {
        r \<leftarrow> type_lookup (tyenv env) v S;
        case r of None \<Rightarrow> return T | Some T' \<Rightarrow> body_type env T'}
    | _ \<Rightarrow> return T)"

partial_function (option) binder_types :: "env \<Rightarrow> ptyp \<Rightarrow> ptyp list M" where
  "binder_types env T =
    (case T of
      Type a Ts \<Rightarrow>
        (case Ts of
          [T1, U] \<Rightarrow>
            if a = STR ''fun'' then do {Us \<leftarrow> binder_types env U; return (T1 # Us)} else return []
        | _ \<Rightarrow> return [])
    | TVar v S \<Rightarrow> do {
        r \<leftarrow> type_lookup (tyenv env) v S;
        case r of None \<Rightarrow> return [] | Some T' \<Rightarrow> binder_types env T'}
    | _ \<Rightarrow> return [])"

definition strip_type :: "env \<Rightarrow> ptyp \<Rightarrow> (ptyp list \<times> ptyp) M" where
  "strip_type env T = do {Ts \<leftarrow> binder_types env T; U \<leftarrow> body_type env T; return (Ts, U)}"

text \<open>\<open>Envir.fastype\<close>: the type of a term, without checking that applications are consistent.\<close>

definition funerr :: String.literal where
  "funerr = STR ''fastype: expected function type''"

fun env_fastype :: "env \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp M" where
  "env_fastype env Ts (f $ u) =
    do {
      T \<leftarrow> env_fastype env Ts f;
      T' \<leftarrow> devar (tyenv env) T;
      case T' of
        Type a Us \<Rightarrow>
          (case Us of
            [_, U] \<Rightarrow> if a = STR ''fun'' then return U else raise (Term_Error funerr [f $ u])
          | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])
    }"
| "env_fastype env Ts (Const _ T) = return T"
| "env_fastype env Ts (Free _ T) = return T"
| "env_fastype env Ts (Bound i) =
    handle (nth Ts i)
      (\<lambda>e. case e of Subscript \<Rightarrow> raise (Term_Error (STR ''fastype: Bound'') [Bound i]) | _ \<Rightarrow> raise e)"
| "env_fastype env Ts (Var _ T) = return T"
| "env_fastype env Ts (Abs _ T u) = do {U \<leftarrow> env_fastype env (T # Ts) u; return (T \<rightarrow>\<^sub>T U)}"

end
