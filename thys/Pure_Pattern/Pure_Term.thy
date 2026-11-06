section \<open>Pure Terms, Tables and the Exception Monad\<close>

theory Pure_Term
  imports "HOL-Library.Monad_Syntax"
begin

text \<open>
  This theory models the parts of Isabelle/Pure's ML code that \<^file>\<open>~~/src/Pure/pattern.ML\<close>
  relies on: types and terms (\<^file>\<open>~~/src/Pure/term.ML\<close>), the tables \<open>Vartab\<close>, and ML
  exceptions. Every definition follows the corresponding ML function literally, so that
  the generated code (see theory \<open>Pure_Pattern_Code\<close>) behaves exactly like the original,
  including failures with exceptions and divergence.

  Integers of ML (indices of variables and de Bruijn indices) are modelled by \<^typ>\<open>integer\<close>,
  strings by \<^typ>\<open>String.literal\<close>; both are mapped to the corresponding ML types.
\<close>


subsection \<open>Types and terms\<close>

type_synonym name = String.literal
type_synonym indexname = "String.literal \<times> integer"
type_synonym pclass = String.literal
type_synonym psort = "pclass list"

datatype ptyp =
  Type name "ptyp list"
| TFree name psort
| TVar indexname psort

datatype pterm =
  Const name ptyp
| Free name ptyp
| Var indexname ptyp
| Bound integer
| Abs name ptyp pterm
| App pterm pterm (infixl \<open>$\<close> 200)

abbreviation fun_type :: "ptyp \<Rightarrow> ptyp \<Rightarrow> ptyp" (infixr \<open>\<rightarrow>\<^sub>T\<close> 200) where
  "T \<rightarrow>\<^sub>T U \<equiv> Type (STR ''fun'') [T, U]"

type_synonym binders = "(name \<times> ptyp) list"


subsection \<open>Tables indexed by \<open>indexname\<close>\<close>

text \<open>The ML structure \<open>Vartab\<close>: finite maps with \<open>indexname\<close> keys.\<close>

typedef 'a vartab = "{m :: indexname \<rightharpoonup> 'a. finite (dom m)}"
  by (intro exI[of _ Map.empty]) simp

setup_lifting type_definition_vartab

lift_definition vt_empty :: "'a vartab" is Map.empty by simp
lift_definition vt_lookup :: "'a vartab \<Rightarrow> indexname \<Rightarrow> 'a option" is "\<lambda>m k. m k" .
lift_definition vt_update :: "indexname \<times> 'a \<Rightarrow> 'a vartab \<Rightarrow> 'a vartab" is
  "\<lambda>(k, x) m. m(k \<mapsto> x)" by auto
lift_definition vt_defined :: "'a vartab \<Rightarrow> indexname \<Rightarrow> bool" is "\<lambda>m k. k \<in> dom m" .
lift_definition vt_is_empty :: "'a vartab \<Rightarrow> bool" is "\<lambda>m. m = Map.empty" .

lemma vt_lookup_empty[simp]: "vt_lookup vt_empty k = None"
  by transfer simp

lemma vt_lookup_update[simp]: "vt_lookup (vt_update (k, x) t) k' = (if k' = k then Some x else vt_lookup t k')"
  by transfer simp

lemma vt_defined_lookup: "vt_defined t k \<longleftrightarrow> vt_lookup t k \<noteq> None"
  by transfer auto

lemma finite_vt_lookup: "finite {k. vt_lookup t k \<noteq> None}"
  by transfer (simp add: dom_def)


subsection \<open>Environments\<close>

text \<open>The datatype \<open>Envir.env\<close> of \<^file>\<open>~~/src/Pure/envir.ML\<close>.\<close>

type_synonym tyenv = "(psort \<times> ptyp) vartab"
type_synonym tenv = "(ptyp \<times> pterm) vartab"

datatype env = Envir (maxidx: integer) (tenv: tenv) (tyenv: tyenv)


subsection \<open>Exceptions\<close>

text \<open>
  Failures of unification carry the information needed to reproduce the tracing output of
  \<open>pattern.ML\<close> (option \<open>unify_trace_failure\<close>). Each constructor corresponds to one of the
  tracing functions \<open>typ_clash\<close>, \<open>clash\<close>, \<open>clashBB\<close>, \<open>clashB\<close>, \<open>proj_fail\<close> and \<open>ocheck_fail\<close>.
\<close>

datatype unif_trace =
  No_Trace
| Typ_Clash tyenv ptyp ptyp
| Clash name name
| Clash_BB binders integer integer
| Clash_B binders integer name
| Proj_Fail env binders indexname "integer list" pterm
| Ocheck_Fail indexname pterm binders env

datatype class_error =
  No_Classrel pclass pclass
| No_Arity name pclass
| No_Subsort psort psort

datatype exn =
  Unif unif_trace  \<comment> \<open>\<open>Pattern.Unif\<close>\<close>
| Pattern  \<comment> \<open>\<open>Pattern.Pattern\<close>\<close>
| Match  \<comment> \<open>\<open>Pattern.MATCH\<close>\<close>
| TUnify  \<comment> \<open>\<open>Type.TUNIFY\<close>\<close>
| Type_Match  \<comment> \<open>\<open>Type.TYPE_MATCH\<close>\<close>
| Class_Error class_error  \<comment> \<open>\<open>Sorts.CLASS_ERROR\<close>\<close>
| Type_Error String.literal "ptyp list" "pterm list"
| Term_Error String.literal "pterm list"
| Failure String.literal
| Subscript
| Unequal_Lengths  \<comment> \<open>\<open>ListPair.UnequalLengths\<close>\<close>
| Dup indexname  \<comment> \<open>\<open>Vartab.DUP\<close>\<close>


subsection \<open>The monad\<close>

text \<open>
  A computation either returns a value or raises an exception. The outer \<^typ>\<open>'a option\<close>
  models divergence: functions that may diverge (e.g.\ head normalization of untyped terms)
  are defined with \<^theory_text>\<open>partial_function (option)\<close>, and the generated code diverges exactly
  where the ML code does. Terminating functions never return \<^const>\<open>None\<close>.
\<close>

datatype 'a res = Ok 'a | Err exn

type_synonym 'a M = "'a res option"

definition return :: "'a \<Rightarrow> 'a M" where
  "return x = Some (Ok x)"

definition raise :: "exn \<Rightarrow> 'a M" where
  "raise e = Some (Err e)"

definition bindM :: "'a M \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> 'b M" where
  "bindM m f = (case m of None \<Rightarrow> None | Some (Ok x) \<Rightarrow> f x | Some (Err e) \<Rightarrow> Some (Err e))"

definition handle :: "'a M \<Rightarrow> (exn \<Rightarrow> 'a M) \<Rightarrow> 'a M" where
  "handle m h = (case m of Some (Err e) \<Rightarrow> h e | _ \<Rightarrow> m)"

no_adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> Option.bind
adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bindM

lemma bindM_simps[simp]:
  "bindM (return x) f = f x"
  "bindM (raise e) f = raise e"
  "bindM None f = None"
  by (simp_all add: bindM_def return_def raise_def)

lemma bindM_return[simp]: "bindM m return = m"
  by (auto simp: bindM_def return_def split: option.splits res.splits)

lemma bindM_assoc: "bindM (bindM m f) g = bindM m (\<lambda>x. bindM (f x) g)"
  by (auto simp: bindM_def raise_def split: option.splits res.splits)

lemma handle_simps[simp]:
  "handle (return x) h = return x"
  "handle (raise e) h = h e"
  "handle None h = None"
  by (simp_all add: handle_def return_def raise_def)

lemma bindM_cong[fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>x. m' = return x \<Longrightarrow> f x = f' x) \<Longrightarrow> bindM m f = bindM m' f'"
  by (auto simp: bindM_def return_def split: option.splits res.splits)

lemma bindM_mono[partial_function_mono]:
  assumes "mono_option B" "\<And>y. mono_option (\<lambda>f. C y f)"
  shows "mono_option (\<lambda>f. bindM (B f) (\<lambda>y. C y f))"
proof -
  have "bindM (B f) (\<lambda>y. C y f) =
    Option.bind (B f) (\<lambda>r. case r of Ok y \<Rightarrow> C y f | Err e \<Rightarrow> Some (Err e))" for f
    by (auto simp: bindM_def split: option.splits res.splits)
  moreover have "mono_option (\<lambda>f. Option.bind (B f) (\<lambda>r. case r of Ok y \<Rightarrow> C y f | Err e \<Rightarrow> Some (Err e)))"
  proof (rule bind_mono[OF assms(1)])
    fix r
    show "mono_option (\<lambda>f. case r of Ok y \<Rightarrow> C y f | Err e \<Rightarrow> Some (Err e))"
      using assms(2) by (cases r) (simp_all add: option.const_mono)
  qed
  ultimately show ?thesis by simp
qed

lemma handle_mono[partial_function_mono]:
  assumes "mono_option B" "\<And>e. mono_option (\<lambda>f. H e f)"
  shows "mono_option (\<lambda>f. handle (B f) (\<lambda>e. H e f))"
proof -
  have "handle (B f) (\<lambda>e. H e f) =
    Option.bind (B f) (\<lambda>r. case r of Ok y \<Rightarrow> Some (Ok y) | Err e \<Rightarrow> H e f)" for f
    by (auto simp: handle_def split: option.splits res.splits)
  moreover have "mono_option (\<lambda>f. Option.bind (B f) (\<lambda>r. case r of Ok y \<Rightarrow> Some (Ok y) | Err e \<Rightarrow> H e f))"
  proof (rule bind_mono[OF assms(1)])
    fix r
    show "mono_option (\<lambda>f. case r of Ok y \<Rightarrow> Some (Ok y) | Err e \<Rightarrow> H e f)"
      using assms(2) by (cases r) (simp_all add: option.const_mono)
  qed
  ultimately show ?thesis by simp
qed

text \<open>Monadic iteration over lists (\<open>fold\<close> and \<open>map\<close> with a raising function).\<close>

fun foldM :: "('a \<Rightarrow> 'b \<Rightarrow> 'b M) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b M" where
  "foldM f [] b = return b"
| "foldM f (x # xs) b = do {b' \<leftarrow> f x b; foldM f xs b'}"

fun mapM :: "('a \<Rightarrow> 'b M) \<Rightarrow> 'a list \<Rightarrow> 'b list M" where
  "mapM f [] = return []"
| "mapM f (x # xs) = do {y \<leftarrow> f x; ys \<leftarrow> mapM f xs; return (y # ys)}"

lemma foldM_mono[partial_function_mono]:
  assumes "\<And>x b. mono_option (\<lambda>f. C x b f)"
  shows "mono_option (\<lambda>f. foldM (\<lambda>x b. C x b f) xs b)"
  using assms
  by (induction xs arbitrary: b) (auto intro!: bindM_mono simp: return_def option.const_mono)

lemma mapM_mono[partial_function_mono]:
  assumes "\<And>x. mono_option (\<lambda>f. C x f)"
  shows "mono_option (\<lambda>f. mapM (\<lambda>x. C x f) xs)"
  using assms
  by (induction xs) (auto intro!: bindM_mono simp: return_def option.const_mono)

lemma foldM_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> b = b' \<Longrightarrow> (\<And>x b. x \<in> set ys \<Longrightarrow> f x b = g x b) \<Longrightarrow> foldM f xs b = foldM g ys b'"
  by (induction ys arbitrary: xs b b') (auto intro!: bindM_cong)

lemma mapM_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> mapM f xs = mapM g ys"
  by (induction ys arbitrary: xs) (auto intro!: bindM_cong)


subsection \<open>List functions of the ML library\<close>

text \<open>\<open>length\<close> and \<open>nth\<close> with ML integers; \<open>nth\<close> raises \<open>Subscript\<close>.\<close>

fun ilength :: "'a list \<Rightarrow> integer" where
  "ilength [] = 0"
| "ilength (x # xs) = ilength xs + 1"

fun nth :: "'a list \<Rightarrow> integer \<Rightarrow> 'a M" where
  "nth [] i = raise Subscript"
| "nth (x # xs) i = (if i < 0 then raise Subscript else if i = 0 then return x else nth xs (i - 1))"

text \<open>\<open>xs ~~ ys\<close> (\<open>zip\<close> raising \<open>ListPair.UnequalLengths\<close>).\<close>

fun zip_eq :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list M" where
  "zip_eq [] [] = return []"
| "zip_eq (x # xs) (y # ys) = do {zs \<leftarrow> zip_eq xs ys; return ((x, y) # zs)}"
| "zip_eq _ _ = raise Unequal_Lengths"

text \<open>\<open>subtract (op =)\<close>, \<open>subset (op =)\<close> and \<open>inter (op =)\<close> of the ML library.\<close>

definition subtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "subtract xs ys = fold removeAll xs ys"

definition subset :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "subset xs ys \<longleftrightarrow> list_all (\<lambda>x. x \<in> set ys) xs"

definition inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inter xs ys = filter (\<lambda>y. y \<in> set xs) ys"

fun has_duplicates :: "'a list \<Rightarrow> bool" where
  "has_duplicates [] = False"
| "has_duplicates (x # xs) = (x \<in> set xs \<or> has_duplicates xs)"


subsection \<open>Operations on terms\<close>

text \<open>Functions of \<^file>\<open>~~/src/Pure/term.ML\<close>.\<close>

fun is_Bound :: "pterm \<Rightarrow> bool" where
  "is_Bound (Bound _) = True"
| "is_Bound _ = False"

fun is_Abs :: "pterm \<Rightarrow> bool" where
  "is_Abs (Abs _ _ _) = True"
| "is_Abs _ = False"

fun is_Var :: "pterm \<Rightarrow> bool" where
  "is_Var (Var _ _) = True"
| "is_Var _ = False"

definition list_comb :: "pterm \<Rightarrow> pterm list \<Rightarrow> pterm" where
  "list_comb t ts = foldl App t ts"

fun strip_comb_acc :: "pterm \<Rightarrow> pterm list \<Rightarrow> pterm \<times> pterm list" where
  "strip_comb_acc (f $ t) ts = strip_comb_acc f (t # ts)"
| "strip_comb_acc f ts = (f, ts)"

definition strip_comb :: "pterm \<Rightarrow> pterm \<times> pterm list" where
  "strip_comb t = strip_comb_acc t []"

fun add_loose_bnos :: "pterm \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list" where
  "add_loose_bnos (Bound i) lev js = (if i < lev then js else List.insert (i - lev) js)"
| "add_loose_bnos (Abs _ _ t) lev js = add_loose_bnos t (lev + 1) js"
| "add_loose_bnos (f $ t) lev js = add_loose_bnos f lev (add_loose_bnos t lev js)"
| "add_loose_bnos _ _ js = js"

definition loose_bnos :: "pterm \<Rightarrow> integer list" where
  "loose_bnos t = add_loose_bnos t 0 []"

fun loose_bvar :: "pterm \<Rightarrow> integer \<Rightarrow> bool" where
  "loose_bvar (Bound i) k = (i \<ge> k)"
| "loose_bvar (f $ t) k = (loose_bvar f k \<or> loose_bvar t k)"
| "loose_bvar (Abs _ _ t) k = loose_bvar t (k + 1)"
| "loose_bvar _ _ = False"

fun loose_bvar1 :: "pterm \<Rightarrow> integer \<Rightarrow> bool" where
  "loose_bvar1 (Bound i) k = (i = k)"
| "loose_bvar1 (f $ t) k = (loose_bvar1 f k \<or> loose_bvar1 t k)"
| "loose_bvar1 (Abs _ _ t) k = loose_bvar1 t (k + 1)"
| "loose_bvar1 _ _ = False"

definition is_open :: "pterm \<Rightarrow> bool" where
  "is_open t = loose_bvar t 0"

definition is_dependent :: "pterm \<Rightarrow> bool" where
  "is_dependent t = loose_bvar1 t 0"

fun incr_bv :: "integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "incr_bv inc lev (Bound i) = (if i \<ge> lev then Bound (i + inc) else Bound i)"
| "incr_bv inc lev (Abs a T t) = Abs a T (incr_bv inc (lev + 1) t)"
| "incr_bv inc lev (t $ u) = incr_bv inc lev t $ incr_bv inc lev u"
| "incr_bv inc lev t = t"

definition incr_boundvars :: "integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "incr_boundvars inc t = (if inc = 0 then t else incr_bv inc 0 t)"

fun subst_bound_aux :: "pterm \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "subst_bound_aux arg lev (Bound i) =
    (if i < lev then Bound i else if i = lev then incr_boundvars lev arg else Bound (i - 1))"
| "subst_bound_aux arg lev (Abs a T t) = Abs a T (subst_bound_aux arg (lev + 1) t)"
| "subst_bound_aux arg lev (t $ u) = subst_bound_aux arg lev t $ subst_bound_aux arg lev u"
| "subst_bound_aux arg lev t = t"

text \<open>\<open>subst_bound (arg, body)\<close>: substitute \<open>arg\<close> for \<open>Bound 0\<close> in \<open>body\<close>.\<close>

definition subst_bound :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "subst_bound arg body = subst_bound_aux arg 0 body"

text \<open>Alpha-equivalence (\<open>aconv_term\<close>): names of bound variables are ignored.\<close>

fun aconv_term :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "aconv_term (t1 $ u1) (t2 $ u2) = (aconv_term t1 t2 \<and> aconv_term u1 u2)"
| "aconv_term (Abs _ T1 t1) (Abs _ T2 t2) = (aconv_term t1 t2 \<and> T1 = T2)"
| "aconv_term a1 a2 = (a1 = a2)"

text \<open>Eta-contraction (\<open>Envir.eta_contract\<close>).\<close>

fun decr :: "integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "decr lev (Bound i) = (if i \<ge> lev then Bound (i - 1) else Bound i)"
| "decr lev (Abs a T body) = Abs a T (decr (lev + 1) body)"
| "decr lev (t $ u) = decr lev t $ decr lev u"
| "decr lev t = t"

fun eta_contract :: "pterm \<Rightarrow> pterm" where
  "eta_contract (Abs a T body) =
    (let body' = eta_contract body in
      case body' of
        f $ Bound i \<Rightarrow> if i = 0 \<and> \<not> is_dependent f then decr 0 f else Abs a T body'
      | _ \<Rightarrow> Abs a T body')"
| "eta_contract (t $ u) = eta_contract t $ eta_contract u"
| "eta_contract t = t"

definition aeconv :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "aeconv t u \<longleftrightarrow> aconv_term t u \<or> aconv_term (eta_contract t) (eta_contract u)"

text \<open>Types of terms (\<open>fastype_of\<close>), raising \<open>TERM\<close> on ill-formed terms.\<close>

fun fastype_of_bound :: "ptyp list \<Rightarrow> integer \<Rightarrow> ptyp M" where
  "fastype_of_bound (T # Ts) i = (if i = 0 then return T else fastype_of_bound Ts (i - 1))"
| "fastype_of_bound [] i = raise (Term_Error (STR ''fastype_of: Bound'') [Bound i])"

fun fastype_of_atom :: "ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp M" where
  "fastype_of_atom _ (Const _ T) = return T"
| "fastype_of_atom _ (Free _ T) = return T"
| "fastype_of_atom _ (Var _ T) = return T"
| "fastype_of_atom Ts (Bound i) = fastype_of_bound Ts i"
| "fastype_of_atom _ _ = raise (Failure (STR ''fastype_of_atom''))"

fun range_type_ofT :: "pterm \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "range_type_ofT t (Type n [T, U]) =
    (if n = STR ''fun'' then return U else raise (Term_Error (STR ''fastype_of: expected function type'') [t]))"
| "range_type_ofT t _ = raise (Term_Error (STR ''fastype_of: expected function type'') [t])"

fun fastype_of_term :: "ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp M"
  and range_type_of :: "ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp M" where
  "fastype_of_term Ts (Abs _ T t) = do {U \<leftarrow> fastype_of_term (T # Ts) t; return (T \<rightarrow>\<^sub>T U)}"
| "fastype_of_term Ts (t $ _) = range_type_of Ts t"
| "fastype_of_term Ts a = fastype_of_atom Ts a"
| "range_type_of Ts (Abs _ T u) = fastype_of_term (T # Ts) u"
| "range_type_of Ts (t $ u) = do {T \<leftarrow> range_type_of Ts t; range_type_ofT (t $ u) T}"
| "range_type_of Ts a = do {T \<leftarrow> fastype_of_atom Ts a; range_type_ofT a T}"

definition fastype_of :: "pterm \<Rightarrow> ptyp M" where
  "fastype_of t = fastype_of_term [] t"

end
