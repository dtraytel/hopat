section \<open>Composition of Theorems: \<open>bicompose_aux\<close>\<close>

theory Pure_Bicompose
  imports "Pure_Unify.Pure_Unify"
begin

text \<open>
  A literal model of \<open>bicompose_aux\<close> of \<^file>\<open>~~/src/Pure/thm.ML\<close>, the inference behind
  resolution, elim-resolution and the composition of rules (Paulson): it unifies the
  conclusion of a rule with a subgoal of a proof state and replaces the subgoal by the
  premises of the rule. The model covers the logical part of the function: the
  unification problems, the renaming of bound variables and schematic variables, the
  flattening of parameters, the normalization of the new theorem, and the lazy sequence of
  results. The construction of the theorems (derivations, proof terms, hypotheses, sort
  constraints and certificates) is left to the ML wrapper; the model returns the data it
  needs.

  Function names follow the ML code, and so does the order of evaluation, which determines
  the exception that is raised. Two operations of Pure are parameters of the model:
  \<^item> the enumeration of unifiers (\<open>Unify.unifiers\<close> and \<open>Seq.pull\<close>): the model works for an
    abstract type of sequences of unifiers. It is instantiated with the model of
    \<open>unify.ML\<close> of theory \<^theory>\<open>Pure_Unify.Pure_Unify\<close> below, and with Pure's own
    \<open>Unify\<close> in the generated code;
  \<^item> \<open>Name.variant_list []\<close>, which invents names for parameters; it only produces names of
    bound variables.
\<close>


subsection \<open>Exceptions and the monad\<close>

text \<open>
  The exceptions of \<open>bicompose_aux\<close>: those of the unifier and of the functions of
  \<^theory>\<open>Pure_Unify.Pure_Unify\<close>, \<open>THM\<close> (raised with the rule, or with the rule and the proof
  state, as the theorems of the exception), \<open>ERROR\<close> (raised by \<open>error\<close>), and the local
  exception \<open>COMPOSE\<close>, which never escapes.
\<close>

datatype thm_args = Orule | Orule_State

datatype texn =
  UExn uexn
| THM String.literal integer thm_args
| ERROR String.literal
| COMPOSE

datatype 'a tres = TOk 'a | TErr texn

text \<open>
  As \<^typ>\<open>'a W\<close>, the monad produces a list of events and then returns a value or raises an
  exception; \<^const>\<open>None\<close> models divergence.
\<close>

type_synonym 'a T = "(event list \<times> 'a tres) option"

definition returnT :: "'a \<Rightarrow> 'a T" where
  "returnT x = Some ([], TOk x)"

definition raiseT :: "texn \<Rightarrow> 'a T" where
  "raiseT e = Some ([], TErr e)"

definition emitT :: "event \<Rightarrow> unit T" where
  "emitT ev = Some ([ev], TOk ())"

definition bindT :: "'a T \<Rightarrow> ('a \<Rightarrow> 'b T) \<Rightarrow> 'b T" where
  "bindT m f =
    (case m of
      None \<Rightarrow> None
    | Some (evs, TErr e) \<Rightarrow> Some (evs, TErr e)
    | Some (evs, TOk x) \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (f x))"

definition handleT :: "'a T \<Rightarrow> (texn \<Rightarrow> 'a T) \<Rightarrow> 'a T" where
  "handleT m h =
    (case m of
      Some (evs, TErr e) \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (h e)
    | _ \<Rightarrow> m)"

text \<open>Computations of the unifier and of session \<open>Pure_Pattern\<close>.\<close>

definition liftWT :: "'a W \<Rightarrow> 'a T" where
  "liftWT m =
    (case m of
      None \<Rightarrow> None
    | Some (evs, UOk x) \<Rightarrow> Some (evs, TOk x)
    | Some (evs, UErr e) \<Rightarrow> Some (evs, TErr (UExn e)))"

definition liftMT :: "'a M \<Rightarrow> 'a T" where
  "liftMT m = liftWT (liftM m)"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bindT

lemma bindT_simps[simp]:
  "bindT (returnT x) f = f x"
  "bindT (raiseT e) f = raiseT e"
  "bindT None f = None"
  by (auto simp: bindT_def returnT_def raiseT_def option.map_id split: option.splits)

lemma bindT_returnT[simp]: "bindT m returnT = m"
  by (auto simp: bindT_def returnT_def split: option.splits tres.splits)

lemma bindT_assoc: "bindT (bindT m f) g = bindT m (\<lambda>x. bindT (f x) g)"
  by (auto simp: bindT_def option.map_comp o_def split: option.splits tres.splits prod.splits
    intro!: option.map_cong)

lemma handleT_simps[simp]:
  "handleT (returnT x) h = returnT x"
  "handleT (raiseT e) h = h e"
  "handleT None h = None"
  by (auto simp: handleT_def returnT_def raiseT_def option.map_id split: option.splits)

lemma liftWT_simps[simp]:
  "liftWT (returnW x) = returnT x"
  "liftWT (raiseW e) = raiseT (UExn e)"
  "liftWT None = None"
  by (simp_all add: liftWT_def returnW_def raiseW_def returnT_def raiseT_def)

lemma liftMT_simps[simp]:
  "liftMT (return x) = returnT x"
  "liftMT (raise e) = raiseT (UExn (PExn e))"
  "liftMT None = None"
  by (simp_all add: liftMT_def)

lemma bindT_cong[fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>x. (\<exists>evs. m' = Some (evs, TOk x)) \<Longrightarrow> f x = f' x) \<Longrightarrow>
    bindT m f = bindT m' f'"
  by (auto simp: bindT_def split: option.splits tres.splits)

lemma handleT_cong[fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>e. (\<exists>evs. m' = Some (evs, TErr e)) \<Longrightarrow> h e = h' e) \<Longrightarrow>
    handleT m h = handleT m' h'"
  by (auto simp: handleT_def split: option.splits tres.splits)

lemma bindT_alt:
  "bindT m f = Option.bind m (\<lambda>p. case snd p of
      TOk y \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (f y)
    | TErr e \<Rightarrow> Some (fst p, TErr e))"
  by (auto simp: bindT_def split: option.splits tres.splits)

lemma handleT_alt:
  "handleT m h = Option.bind m (\<lambda>p. case snd p of
      TOk y \<Rightarrow> Some (fst p, TOk y)
    | TErr e \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (h e))"
  by (auto simp: handleT_def split: option.splits tres.splits)

lemma bindT_mono[partial_function_mono]:
  assumes "mono_option B" "\<And>y. mono_option (\<lambda>f. C y f)"
  shows "mono_option (\<lambda>f. bindT (B f) (\<lambda>y. C y f))"
  unfolding bindT_alt
proof (rule bind_mono[OF assms(1)])
  fix p
  show "mono_option (\<lambda>f. case snd p of
      TOk y \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (C y f)
    | TErr e \<Rightarrow> Some (fst p, TErr e))"
    using assms(2) by (cases "snd p") (simp_all add: map_option_mono option.const_mono)
qed

lemma handleT_mono[partial_function_mono]:
  assumes "mono_option B" "\<And>e. mono_option (\<lambda>f. H e f)"
  shows "mono_option (\<lambda>f. handleT (B f) (\<lambda>e. H e f))"
  unfolding handleT_alt
proof (rule bind_mono[OF assms(1)])
  fix p
  show "mono_option (\<lambda>f. case snd p of
      TOk y \<Rightarrow> Some (fst p, TOk y)
    | TErr e \<Rightarrow> map_option (\<lambda>(evs', r). (fst p @ evs', r)) (H e f))"
    using assms(2) by (cases "snd p") (simp_all add: map_option_mono option.const_mono)
qed

text \<open>Code equations that avoid appending empty lists of events.\<close>

lemma bindT_code[code]:
  "bindT m f =
    (case m of
      None \<Rightarrow> None
    | Some (evs, TErr e) \<Rightarrow> Some (evs, TErr e)
    | Some (evs, TOk x) \<Rightarrow>
        (case evs of [] \<Rightarrow> f x | _ \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (f x)))"
  by (auto simp: bindT_def option.map_id split: option.splits tres.splits list.splits)

lemma handleT_code[code]:
  "handleT m h =
    (case m of
      Some (evs, TErr e) \<Rightarrow>
        (case evs of [] \<Rightarrow> h e | _ \<Rightarrow> map_option (\<lambda>(evs', r). (evs @ evs', r)) (h e))
    | _ \<Rightarrow> m)"
  by (auto simp: handleT_def option.map_id split: option.splits tres.splits list.splits)

fun mapT :: "('a \<Rightarrow> 'b T) \<Rightarrow> 'a list \<Rightarrow> 'b list T" where
  "mapT f [] = returnT []"
| "mapT f (x # xs) = do {y \<leftarrow> f x; ys \<leftarrow> mapT f xs; returnT (y # ys)}"

lemma mapT_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> mapT f xs = mapT g ys"
  by (induction ys arbitrary: xs) (auto intro!: bindT_cong)


subsection \<open>Propositions\<close>

text \<open>Functions of \<^file>\<open>~~/src/Pure/logic.ML\<close> and \<^file>\<open>~~/src/Pure/term.ML\<close>.\<close>

definition propT :: ptyp where
  "propT = Type STR ''prop'' []"

definition implies :: pterm where
  "implies = Const STR ''Pure.imp'' (propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT)"

definition all_const :: "ptyp \<Rightarrow> pterm" where
  "all_const T = Const STR ''Pure.all'' ((T \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT)"

definition mk_implies :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "mk_implies A B = implies $ A $ B"

fun list_implies :: "pterm list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "list_implies [] B = B"
| "list_implies (A # As) B = implies $ A $ list_implies As B"

text \<open>\<open>Logic.list_all\<close>\<close>

fun list_forall :: "binders \<Rightarrow> pterm \<Rightarrow> pterm" where
  "list_forall [] t = t"
| "list_forall ((a, T) # vars) t = all_const T $ Abs a T (list_forall vars t)"

text \<open>The patterns \<open>Const ("Pure.imp", _) $ A $ B\<close> and \<open>Const ("Pure.all", _) $ Abs (a, T, t)\<close>.\<close>

fun dest_imp :: "pterm \<Rightarrow> (pterm \<times> pterm) option" where
  "dest_imp (Const c _ $ A $ B) = (if c = STR ''Pure.imp'' then Some (A, B) else None)"
| "dest_imp _ = None"

fun dest_all :: "pterm \<Rightarrow> (name \<times> ptyp \<times> pterm) option" where
  "dest_all (Const c _ $ Abs a T t) = (if c = STR ''Pure.all'' then Some (a, T, t) else None)"
| "dest_all _ = None"

lemma dest_imp_Some: "dest_imp t = Some (A, B) \<longleftrightarrow> (\<exists>U. t = Const STR ''Pure.imp'' U $ A $ B)"
  by (cases t rule: dest_imp.cases) auto

lemma dest_all_Some: "dest_all t = Some (a, T, b) \<longleftrightarrow> (\<exists>U. t = Const STR ''Pure.all'' U $ Abs a T b)"
  by (cases t rule: dest_all.cases) auto

lemma dest_imp_size: "dest_imp t = Some (A, B) \<Longrightarrow> size A < size t \<and> size B < size t"
  by (auto simp: dest_imp_Some)

lemma dest_all_size: "dest_all t = Some (a, T, b) \<Longrightarrow> size b < size t"
  by (auto simp: dest_all_Some)

lemmas dest_size = dest_imp_size dest_all_size dest_imp_size[OF sym] dest_all_size[OF sym]

text \<open>\<open>Logic.count_prems\<close> and \<open>Term.strip_all_body\<close>.\<close>

function count_prems :: "pterm \<Rightarrow> integer" where
  "count_prems t = (case dest_imp t of Some (_, B) \<Rightarrow> 1 + count_prems B | None \<Rightarrow> 0)"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare count_prems.simps[simp del]

function strip_all_body :: "pterm \<Rightarrow> pterm" where
  "strip_all_body t = (case dest_all t of Some (_, _, b) \<Rightarrow> strip_all_body b | None \<Rightarrow> t)"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare strip_all_body.simps[simp del]

text \<open>
  \<open>Logic.strip_prems (i, As, B)\<close>: strip \<open>i\<close> premises, returning them in reverse order, and
  raise \<open>TERM\<close> if there are too few.
\<close>

function strip_prems :: "integer \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> (pterm list \<times> pterm) M" where
  "strip_prems i As B =
    (if i = 0 then return (As, B)
     else case dest_imp B of
       Some (A, B') \<Rightarrow> strip_prems (i - 1) (A # As) B'
     | None \<Rightarrow> raise (Term_Error (STR ''strip_prems'') (B # As)))"
  by auto
termination by (relation "measure (\<lambda>(_, _, B). size B)") (auto dest: dest_size)

declare strip_prems.simps[simp del]

text \<open>
  \<open>strip_assums2\<close> of \<open>thm.ML\<close>: strip off pairs of assumptions and parameters in parallel; they
  are identical because of lifting.
\<close>

function strip_assums2 :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm \<times> pterm" where
  "strip_assums2 B Bi =
    (case (dest_imp B, dest_imp Bi) of
      (Some (_, B1), Some (_, B2)) \<Rightarrow> strip_assums2 B1 B2
    | _ \<Rightarrow>
      (case (dest_all B, dest_all Bi) of
        (Some (a, T, t1), Some (_, _, t2)) \<Rightarrow>
          (case strip_assums2 t1 t2 of (B1, B2) \<Rightarrow> (Abs a T B1, Abs a T B2))
      | _ \<Rightarrow> (B, Bi)))"
  by auto
termination by (relation "measure (\<lambda>(B, _). size B)") (auto dest: dest_size)

declare strip_assums2.simps[simp del]

text \<open>
  \<open>strip_apply f B A\<close> of \<open>thm.ML\<close>: strip off all assumptions and parameters from \<open>A\<close> that
  were introduced by lifting over \<open>B\<close>, and apply \<open>f\<close> to the remaining part of \<open>A\<close>. The
  connectives of the result are those of \<open>B\<close>.
\<close>

function strip_apply :: "(pterm \<Rightarrow> pterm) \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "strip_apply f B A =
    (case (B, dest_imp B, dest_imp A) of
      (c $ _ $ _, Some (_, B1), Some (A2, B2)) \<Rightarrow> c $ A2 $ strip_apply f B1 B2
    | _ \<Rightarrow>
      (case (B, dest_all B, dest_all A) of
        (c $ _, Some (_, _, t1), Some (a, T, t2)) \<Rightarrow> c $ Abs a T (strip_apply f t1 t2)
      | _ \<Rightarrow> f A))"
  by auto
termination by (relation "measure (\<lambda>(_, B, _). size B)") (auto dest: dest_size)

declare strip_apply.simps[simp del]

function strip_lifted :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "strip_lifted B A =
    (case (dest_imp B, dest_imp A) of
      (Some (_, B1), Some (_, B2)) \<Rightarrow> strip_lifted B1 B2
    | _ \<Rightarrow>
      (case (dest_all B, dest_all A) of
        (Some (_, _, t1), Some (_, _, t2)) \<Rightarrow> strip_lifted t1 t2
      | _ \<Rightarrow> A))"
  by auto
termination by (relation "measure (\<lambda>(B, _). size B)") (auto dest: dest_size)

declare strip_lifted.simps[simp del]


subsection \<open>Renaming bound variables and schematic variables\<close>

text \<open>\<open>Term.match_bvars\<close>: scan a pair of terms; while they are similar, accumulate
  corresponding bound variables.\<close>

fun match_bvs :: "pterm \<Rightarrow> pterm \<Rightarrow> (name \<times> name) list \<Rightarrow> (name \<times> name) list" where
  "match_bvs (Abs x _ s) (Abs y _ t) acc =
    match_bvs s t (if x \<noteq> STR '''' \<and> y \<noteq> STR '''' then (x, y) # acc else acc)"
| "match_bvs (f $ s) (g $ t) acc = match_bvs f g (match_bvs s t acc)"
| "match_bvs _ _ acc = acc"

definition match_bvars :: "pterm \<times> pterm \<Rightarrow> (name \<times> name) list \<Rightarrow> (name \<times> name) list" where
  "match_bvars tu acc = match_bvs (strip_abs_body (fst tu)) (strip_abs_body (snd tu)) acc"

text \<open>
  The names of schematic variables (\<open>fold_aterms\<close> with \<open>Symset.insert\<close>). Sets of names
  (\<open>Symset\<close>) are lists; only membership matters.
\<close>

fun add_var_names :: "pterm \<Rightarrow> name list \<Rightarrow> name list" where
  "add_var_names (Var (x, _) _) xs = (if x \<in> set xs then xs else x # xs)"
| "add_var_names (Abs _ _ t) xs = add_var_names t xs"
| "add_var_names (t $ u) xs = add_var_names u (add_var_names t xs)"
| "add_var_names _ xs = xs"

text \<open>
  Tables of names (\<open>Symtab\<close>, built by \<open>Symtab.make_distinct\<close>) are association lists with
  distinct keys; the first entry for a key wins.
\<close>

fun distinct_fst :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "distinct_fst [] = []"
| "distinct_fst ((x, y) # ps) = (x, y) # distinct_fst (filter (\<lambda>p. fst p \<noteq> x) ps)"

text \<open>
  \<open>del_clashing\<close> of \<open>rename_bvs\<close>: drop renamings whose target clashes with an unchanged name
  or with the target of an earlier renaming; the source of a dropped renaming then stays
  unchanged, so repeat until nothing is dropped. \<open>del_round\<close> is one pass of the ML function.
\<close>

fun del_round :: "name list \<Rightarrow> name list \<Rightarrow> (name \<times> name) list \<Rightarrow> (name \<times> name) list \<Rightarrow> bool \<Rightarrow>
    bool \<times> name list \<times> (name \<times> name) list" where
  "del_round xs ys [] qs clash = (clash, xs, qs)"
| "del_round xs ys ((x, y) # ps) qs clash =
    (if y \<in> set ys then del_round (x # xs) (x # ys) ps qs True
     else del_round xs (y # ys) ps ((x, y) # qs) clash)"

lemma del_round_length:
  "del_round xs ys ps qs clash = (clash', xs', qs') \<Longrightarrow>
    length qs' + (if clash' \<and> \<not> clash then 1 else 0) \<le> length ps + length qs"
  by (induction xs ys ps qs clash rule: del_round.induct) (fastforce split: if_splits)+

function del_clashing :: "name list \<Rightarrow> (name \<times> name) list \<Rightarrow> (name \<times> name) list" where
  "del_clashing xs ps =
    (case del_round xs xs ps [] False of (clash, xs', qs) \<Rightarrow> if clash then del_clashing xs' qs else qs)"
  by auto
termination
  by (relation "measure (\<lambda>(_, ps). length ps)")
    (auto dest!: del_round_length[OF sym] split: prod.splits)

declare del_clashing.simps[simp del]

text \<open>
  \<open>rename_bvs dpairs tpairs B As\<close>: the renaming of bound variables and unknowns in the new
  assumptions \<open>As\<close> (lifted over \<open>B\<close>), from the bound variables of the current disagreement
  pairs \<open>dpairs\<close>. It preserves unknowns in the flex-flex pairs \<open>tpairs\<close> and on the left of
  \<open>dpairs\<close>. The result consists of the tables \<open>vars\<close> and \<open>bounds\<close>.
\<close>

type_synonym ren = "(name \<times> name) list \<times> (name \<times> name) list"

definition rename_bvs :: "(pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> ren" where
  "rename_bvs dpairs tpairs B As =
    (let al = foldr match_bvars dpairs [] in
      if al = [] then ([], [])
      else
        let
          unknowns =
            fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tpairs
              (fold (add_var_names \<circ> fst) dpairs []);
          unknowns' = fold (add_var_names \<circ> strip_lifted B) As [];
          al' = distinct_fst
            (filter (\<lambda>(x, y). \<not> (x \<notin> set unknowns' \<or> x \<in> set unknowns \<or> y \<in> set unknowns)) al);
          unchanged = filter (\<lambda>x. map_of al' x = None) unknowns';
          al'' = del_clashing unchanged al'
        in (distinct_fst al'', distinct_fst al))"

text \<open>
  The renaming function \<open>term\<close> of \<open>rename_bvars\<close>; \<open>perhaps (Symtab.lookup tab)\<close> is
  \<open>ren_name tab\<close>.
\<close>

definition ren_name :: "(name \<times> name) list \<Rightarrow> name \<Rightarrow> name" where
  "ren_name tab x = (case map_of tab x of Some y \<Rightarrow> y | None \<Rightarrow> x)"

fun ren_term :: "ren \<Rightarrow> pterm \<Rightarrow> pterm" where
  "ren_term r (Var (x, i) T) = Var (ren_name (fst r) x, i) T"
| "ren_term r (Abs x T t) = Abs (ren_name (snd r) x) T (ren_term r t)"
| "ren_term r (t $ u) = ren_term r t $ ren_term r u"
| "ren_term r t = t"

text \<open>\<open>rename_bvars\<close>: \<^const>\<open>None\<close> if the renaming is the identity.\<close>

definition rename_bvars :: "(pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow>
    ren option" where
  "rename_bvars dpairs tpairs B As =
    (let r = rename_bvs dpairs tpairs B As in
      if list_all (\<lambda>(x, y). x = y) (fst r) \<and> list_all (\<lambda>(x, y). x = y) (snd r) then None
      else Some r)"


subsection \<open>Flattening parameters\<close>

text \<open>\<open>Logic.strip_params\<close>: all parameters of a subgoal, even nested ones.\<close>

function strip_params :: "pterm \<Rightarrow> binders" where
  "strip_params t =
    (case dest_imp t of
      Some (_, B) \<Rightarrow> strip_params B
    | None \<Rightarrow> (case dest_all t of Some (a, T, b) \<Rightarrow> (a, T) # strip_params b | None \<Rightarrow> []))"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare strip_params.simps[simp del]

text \<open>
  \<open>Logic.remove_params j n A\<close>: remove the parameters from a subgoal and renumber bound
  variables in the hypotheses, where \<open>j\<close> is the total number of parameters; if \<open>n > 0\<close>,
  delete assumption \<open>n\<close>.
\<close>

function remove_params :: "integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "remove_params j n A =
    (if j = 0 \<and> n \<le> 0 then return A
     else case dest_imp A of
       Some (H, B) \<Rightarrow>
         if n = 1 then remove_params j (n - 1) B
         else do {B' \<leftarrow> remove_params j (n - 1) B; return (implies $ incr_boundvars j H $ B')}
     | None \<Rightarrow>
       (case dest_all A of
         Some (_, _, t) \<Rightarrow> remove_params (j - 1) n t
       | None \<Rightarrow> if n > 0 then raise (Term_Error (STR ''remove_params'') [A]) else return A))"
  by auto
termination by (relation "measure (\<lambda>(_, _, A). size A)") (auto dest: dest_size)

declare remove_params.simps[simp del]

text \<open>
  \<open>Logic.flatten_params n A\<close>: move all parameters to the front of the subgoal, renaming them
  apart with \<open>variants\<close> (\<open>Name.variant_list []\<close>); if \<open>n > 0\<close>, delete assumption \<open>n\<close>.
  \<open>ListPair.zip\<close> is \<^const>\<open>zip\<close>.
\<close>

definition flatten_params :: "(name list \<Rightarrow> name list) \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "flatten_params variants n A =
    (let
      params = strip_params A;
      vars = zip (variants (map fst params)) (map snd params)
    in do {A' \<leftarrow> remove_params (ilength vars) n A; return (list_forall vars A')})"


subsection \<open>Normalization\<close>

text \<open>
  \<open>norm_term_skip env n t\<close> of \<open>thm.ML\<close>: normalize \<open>t\<close>, but skip \<open>n\<close> assumptions that were
  lifted over and so cannot be affected by the environment. The types of parameters are
  normalized, because they are flattened.
\<close>

function norm_term_skip :: "env \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm T" where
  "norm_term_skip env n t =
    (if n = 0 then liftMT (norm_term env t)
     else case dest_all t of
       Some (a, T, b) \<Rightarrow> do {
         T' \<leftarrow> liftMT (norm_type (tyenv env) T);
         b' \<leftarrow> norm_term_skip env n b;
         returnT (all_const T' $ Abs a T' b')}
     | None \<Rightarrow>
       (case dest_imp t of
         Some (A, B) \<Rightarrow> do {B' \<leftarrow> norm_term_skip env (n - 1) B; returnT (mk_implies A B')}
       | None \<Rightarrow> raiseT (ERROR (STR ''norm_term_skip: too few assumptions??''))))"
  by auto
termination by (relation "measure (\<lambda>(_, _, t). size t)") (auto dest: dest_size)

declare norm_term_skip.simps[simp del]

text \<open>\<open>Envir.above env lim\<close>: all variables bound by \<open>env\<close> have an index above \<open>lim\<close>.\<close>

lift_definition vt_above :: "'a vartab \<Rightarrow> integer \<Rightarrow> bool" is
  "\<lambda>m lim. \<forall>x \<in> dom m. snd x > lim" .

definition above :: "env \<Rightarrow> integer \<Rightarrow> bool" where
  "above env lim \<longleftrightarrow> vt_above (tenv env) lim \<and> vt_above (tyenv env) lim"

text \<open>\<open>Envir.empty maxidx\<close>\<close>

definition empty_env :: "integer \<Rightarrow> env" where
  "empty_env m = Envir m vt_empty vt_empty"


subsection \<open>Elim-resolution and quick tests\<close>

text \<open>\<open>Logic.strip_assums_all\<close> and \<open>Logic.strip_assums_imp\<close>.\<close>

function strip_assums_all :: "binders \<Rightarrow> pterm \<Rightarrow> binders \<times> pterm" where
  "strip_assums_all params t =
    (case dest_all t of Some (a, T, b) \<Rightarrow> strip_assums_all ((a, T) # params) b | None \<Rightarrow> (params, t))"
  by auto
termination by (relation "measure (\<lambda>(_, t). size t)") (auto dest: dest_size)

declare strip_assums_all.simps[simp del]

function strip_assums_imp :: "integer \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> pterm list \<times> pterm" where
  "strip_assums_imp nasms Hs B =
    (if nasms = 0 then (Hs, B)
     else case dest_imp B of
       Some (H, B') \<Rightarrow> strip_assums_imp (nasms - 1) (H # Hs) B'
     | None \<Rightarrow> (Hs, B))"
  by auto
termination by (relation "measure (\<lambda>(_, _, B). size B)") (auto dest: dest_size)

declare strip_assums_imp.simps[simp del]

text \<open>
  \<open>Logic.assum_problems (nasms, A)\<close>: the parameters of \<open>A\<close> (to close the terms), its first
  \<open>nasms\<close> assumptions, and the rest.
\<close>

definition assum_problems :: "integer \<Rightarrow> pterm \<Rightarrow> binders \<times> pterm list \<times> pterm" where
  "assum_problems nasms A =
    (case strip_assums_all [] A of (params, A') \<Rightarrow>
      (case strip_assums_imp nasms [] A' of (Hs, B) \<Rightarrow> (params, rev Hs, B)))"

text \<open>\<open>Term.could_unify\<close>: a quick test whether two terms might be unifiable.\<close>

function could_unify :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"
  and matchrands :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "could_unify t u =
    (case (head_of t, head_of u) of
      (_, Var _ _) \<Rightarrow> True
    | (Var _ _, _) \<Rightarrow> True
    | (Const a _, Const b _) \<Rightarrow> a = b \<and> matchrands t u
    | (Free a _, Free b _) \<Rightarrow> a = b \<and> matchrands t u
    | (Bound i, Bound j) \<Rightarrow> i = j \<and> matchrands t u
    | (Abs _ _ _, _) \<Rightarrow> True
    | (_, Abs _ _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "matchrands (f $ t) (g $ u) = (could_unify t u \<and> matchrands f g)"
| "matchrands (Const v va) _ = True"
| "matchrands (Free v va) _ = True"
| "matchrands (Var v va) _ = True"
| "matchrands (Bound v) _ = True"
| "matchrands (Abs v va vb) _ = True"
| "matchrands (v $ va) (Const vb vc) = True"
| "matchrands (v $ va) (Free vb vc) = True"
| "matchrands (v $ va) (Var vb vc) = True"
| "matchrands (v $ va) (Bound vb) = True"
| "matchrands (v $ va) (Abs vb vc vd) = True"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>x. case x of
      Inl (t, u) \<Rightarrow> 2 * (size t + size u) + 1
    | Inr (t, u) \<Rightarrow> 2 * (size t + size u))") auto

declare could_unify.simps[simp del]


subsection \<open>Unification of the types of variables\<close>

text \<open>
  \<open>Thm.full_prop_of\<close>: the proposition with the flex-flex pairs as assumptions
  (\<open>attach_tpairs\<close>); \<open>Logic.mk_equals\<close> computes the type of the left-hand side.
\<close>

definition mk_equals :: "pterm \<times> pterm \<Rightarrow> pterm M" where
  "mk_equals tu =
    (case tu of (t, u) \<Rightarrow> do {
      T \<leftarrow> fastype_of t;
      return (Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u)})"

definition full_prop_of :: "(pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "full_prop_of tpairs prop = do {eqs \<leftarrow> mapM mk_equals tpairs; return (list_implies eqs prop)}"

text \<open>
  The table \<open>vars\<close> of \<open>unify_var_types\<close> maps each variable to the list of its types, the most
  recent first (\<open>Vartab.insert_list (op =)\<close>). Its entries are visited in the order of the
  keys (\<open>Vartab.fold\<close>), which is \<open>Term_Ord.fast_indexname_ord\<close>: by index, then by the size of
  the name, then by the name.
\<close>

text \<open>\<open>String.size\<close>\<close>

definition literal_size :: "String.literal \<Rightarrow> integer" where
  "literal_size s = integer_of_nat (size s)"

definition fast_indexname_less :: "indexname \<Rightarrow> indexname \<Rightarrow> bool" where
  "fast_indexname_less xi yj \<longleftrightarrow>
    snd xi < snd yj \<or>
    (snd xi = snd yj \<and>
      (literal_size (fst xi) < literal_size (fst yj) \<or>
        (literal_size (fst xi) = literal_size (fst yj) \<and> fst xi < fst yj)))"

fun insert_key :: "indexname \<times> 'a \<Rightarrow> (indexname \<times> 'a) list \<Rightarrow> (indexname \<times> 'a) list" where
  "insert_key p [] = [p]"
| "insert_key p (q # qs) = (if fast_indexname_less (fst q) (fst p) then q # insert_key p qs else p # q # qs)"

fun insert_list :: "indexname \<times> ptyp \<Rightarrow> (indexname \<times> ptyp list) list \<Rightarrow> (indexname \<times> ptyp list) list" where
  "insert_list (xi, T) [] = [(xi, [T])]"
| "insert_list (xi, T) ((yj, Ts) # tab) =
    (if xi = yj then (yj, if list_ex (\<lambda>U. T = U) Ts then Ts else T # Ts) # tab
     else (yj, Ts) # insert_list (xi, T) tab)"

fun add_vars :: "pterm \<Rightarrow> (indexname \<times> ptyp list) list \<Rightarrow> (indexname \<times> ptyp list) list" where
  "add_vars (Var xi T) tab = insert_list (xi, T) tab"
| "add_vars (Abs _ _ t) tab = add_vars t tab"
| "add_vars (t $ u) tab = add_vars u (add_vars t tab)"
| "add_vars _ tab = tab"

definition sort_keys :: "(indexname \<times> 'a) list \<Rightarrow> (indexname \<times> 'a) list" where
  "sort_keys tab = foldr insert_key tab []"

text \<open>
  \<open>Pattern.unify_types\<close> traces a failure (option \<open>unify_trace_failure\<close>), which is the event
  \<^const>\<open>Ev_Unif\<close>.
\<close>

fun unify_vars :: "algebra \<Rightarrow> ptyp list \<Rightarrow> env \<Rightarrow> env M" where
  "unify_vars alg (T # Us) env = foldM (\<lambda>U env. unify_types alg T U env) Us env"
| "unify_vars alg [] env = return env"

definition unify_var_types :: "algebra \<Rightarrow> (pterm \<times> pterm) list \<times> pterm \<Rightarrow> (pterm \<times> pterm) list \<times> pterm \<Rightarrow>
    env \<Rightarrow> env option T" where
  "unify_var_types alg th1 th2 env =
    (case
      do {
        p1 \<leftarrow> full_prop_of (fst th1) (snd th1);
        p2 \<leftarrow> full_prop_of (fst th2) (snd th2);
        let vars = sort_keys (add_vars p2 (add_vars p1 []));
        foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) vars env
      } of
      Some (Err (Unif tr)) \<Rightarrow> do {emitT (Ev_Unif tr); returnT None}
    | r \<Rightarrow> liftMT (map_option (map_res Some) r))"


subsection \<open>Lazy sequences of results\<close>

text \<open>
  The operations of Pure that the model is parameterised by: \<open>Unify.unifiers (context, env,
  dpairs)\<close>, \<open>Seq.pull\<close> on its result, and \<open>Name.variant_list []\<close>. The sequences of unifiers
  have the abstract type \<open>'u\<close>.
\<close>

datatype 'u bops = BOps
  (bo_unifiers: "env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> 'u T")
  (bo_pull: "'u \<Rightarrow> ((env \<times> (pterm \<times> pterm) list) \<times> 'u) option T")
  (bo_variants: "name list \<Rightarrow> name list")

text \<open>
  The data of a call of \<open>bicompose_aux\<close> that the closures of its result sequence refer to:
  the flags \<open>flatten\<close>, \<open>match\<close> and \<open>lifted\<close>, the maximal index \<open>smax\<close> of the proof state,
  its other subgoals \<open>Bs\<close>, the subgoal \<open>Bi\<close>, its conclusion \<open>C\<close>, the flex-flex pairs
  \<open>rtpairs\<close> of the rule, the number \<open>nlift\<close> of assumptions to skip in normalization, the
  pair \<open>BBi\<close> of the conclusion of the rule and the subgoal, and all disagreement pairs
  \<open>dpairs\<close>.
\<close>

datatype bctx = BCtx
  (bc_flatten: bool) (bc_match: bool) (bc_lifted: bool) (bc_smax: integer)
  (bc_Bs: "pterm list") (bc_Bi: pterm) (bc_C: pterm) (bc_rtpairs: "(pterm \<times> pterm) list")
  (bc_nlift: integer) (bc_BBi: "pterm \<times> pterm") (bc_dpairs: "(pterm \<times> pterm) list")

text \<open>
  The result of \<open>newAs\<close>: the new assumptions \<open>As\<close> (renamed and flattened), the renamed ones
  \<open>oldAs\<close> before flattening, the renaming (which the wrapper also applies to the proof of the
  rule), and the number \<open>n\<close> of the assumption used by elim-resolution.
\<close>

datatype newas = NewAs (na_As: "pterm list") (na_oldAs: "pterm list") (na_ren: "ren option") (na_n: integer)

text \<open>
  A result: the environment, the flex-flex pairs and the proposition of the new theorem, and
  the data for its proof term (\<open>A\<close>, \<open>As\<close>, \<open>oldAs\<close>, \<open>n\<close> of \<open>Proofterm.bicompose_proof\<close>).
\<close>

datatype bres = BRes
  (br_env: env) (br_tpairs: "(pterm \<times> pterm) list") (br_prop: pterm)
  (br_A: "pterm option") (br_newas: newas)

text \<open>
  The data of elim-resolution (\<open>eres\<close>): the environment, the parameters of the first premise
  \<open>A1\<close> of the rule, its conclusion \<open>concl\<close> and closed conclusion \<open>concl'\<close>, and the other
  premises.
\<close>

datatype eres_data = ER (er_env: env) (er_params: binders) (er_concl: pterm) (er_concl': pterm)
  (er_A1: pterm) (er_As: "pterm list")

text \<open>
  The closures of the result sequence. \<open>Seq.it_right (addth A newas) (xq, yq)\<close> pulls the
  unifiers \<open>xq\<close>, the first of which has already been pulled (\<open>UQ_Cell\<close>), and continues
  with \<open>yq\<close>; \<open>BS_Tryasms\<close> is the closure \<open>Seq.make (fn () => Seq.pull (tryasms rest
  n))\<close> of elim-resolution.
\<close>

datatype 'u uq = UQ_Cell "(env \<times> (pterm \<times> pterm) list) \<times> 'u" | UQ_Seq 'u

datatype 'u bseq =
  BS_Empty
| BS_Its bctx "pterm option" newas "'u uq" "'u bseq"
| BS_Tryasms bctx eres_data "pterm list" integer


subsection \<open>The new theorem\<close>

text \<open>
  \<open>newAs (As0, n, dpairs, tpairs)\<close>: modify the assumptions, deleting the \<open>n\<close>-th if \<open>n > 0\<close>
  for elim-resolution.
\<close>

definition newAs :: "(name list \<Rightarrow> name list) \<Rightarrow> bctx \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow>
    (pterm \<times> pterm) list \<Rightarrow> newas T" where
  "newAs variants ctx As0 n dpairs tpairs =
    (let (As1, r) =
      if bc_lifted ctx then
        (case rename_bvars dpairs (bc_rtpairs ctx @ tpairs) (bc_Bi ctx) As0 of
          Some r \<Rightarrow> (map (strip_apply (ren_term r) (bc_Bi ctx)) As0, Some r)
        | None \<Rightarrow> (As0, None))
      else (As0, None)
    in
      handleT
        (do {
          As2 \<leftarrow> if bc_flatten ctx then liftMT (mapM (flatten_params variants n) As1) else returnT As1;
          returnT (NewAs As2 As1 r n)})
        (\<lambda>e. case e of
          UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: 1st premise'') 0 Orule)
        | _ \<Rightarrow> raiseT e))"

definition norm_tpair :: "env \<Rightarrow> pterm \<times> pterm \<Rightarrow> (pterm \<times> pterm) M" where
  "norm_tpair env tu = (case tu of (t, u) \<Rightarrow> do {t' \<leftarrow> norm_term env t; u' \<leftarrow> norm_term env u; return (t', u')})"

text \<open>
  \<open>addth A newas (env, tpairs)\<close>: the new theorem with proposition \<open>\<lbrakk>Bs; As\<rbrakk> \<Longrightarrow> C\<close>; it
  normalizes only as much as needed. If \<open>match\<close>, instantiations of the proof state are
  forbidden: it raises \<open>COMPOSE\<close>.
\<close>

definition addth :: "bctx \<Rightarrow> pterm option \<Rightarrow> newas \<Rightarrow> env \<times> (pterm \<times> pterm) list \<Rightarrow> bres T" where
  "addth ctx A na et =
    (case et of (env, tpairs) \<Rightarrow> do {
      (ntpairs, Hs, C') \<leftarrow>
        if env_is_empty env then returnT (tpairs, bc_Bs ctx @ na_As na, bc_C ctx)
        else do {
          ntps \<leftarrow> liftMT (mapM (norm_tpair env) tpairs);
          if above env (bc_smax ctx) then
            if bc_lifted ctx then do {
              As' \<leftarrow> mapT (norm_term_skip env (bc_nlift ctx)) (na_As na);
              returnT (ntps, bc_Bs ctx @ As', bc_C ctx)}
            else do {
              As' \<leftarrow> liftMT (mapM (norm_term env) (na_As na));
              returnT (ntps, bc_Bs ctx @ As', bc_C ctx)}
          else if bc_match ctx then raiseT COMPOSE
          else do {
            Hs \<leftarrow> liftMT (mapM (norm_term env) (bc_Bs ctx @ na_As na));
            C' \<leftarrow> liftMT (norm_term env (bc_C ctx));
            returnT (ntps, Hs, C')}};
      returnT (BRes env ntpairs (list_implies Hs C') A na)})"

text \<open>
  \<open>tryasms asms n\<close> of elim-resolution: try to solve the first premise of the rule by each
  assumption of the subgoal in turn, together with the other disagreement pairs.
\<close>

fun tryasms :: "'u bops \<Rightarrow> bctx \<Rightarrow> eres_data \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> 'u bseq T" where
  "tryasms ops ctx er [] n = returnT BS_Empty"
| "tryasms ops ctx er (asm # rest) n =
    (if could_unify asm (er_concl er) then do {
      let asm' = rlist_abs (er_params er) asm;
      us \<leftarrow> bo_unifiers ops (er_env er) ((asm', er_concl' er) # bc_dpairs ctx);
      r \<leftarrow> bo_pull ops us;
      case r of
        None \<Rightarrow> tryasms ops ctx er rest (n + 1)
      | Some ((env, tpairs), us') \<Rightarrow> do {
          na \<leftarrow> newAs (bo_variants ops) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, asm')] tpairs;
          returnT (BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env, tpairs), us'))
            (BS_Tryasms ctx er rest (n + 1)))}}
     else tryasms ops ctx er rest (n + 1))"

text \<open>
  \<open>bpull\<close> evaluates the closures of the result sequence, as \<open>Seq.pull\<close>. It may diverge if
  the sequence of unifiers is infinite and every unifier instantiates the proof state when
  this is forbidden (\<open>match\<close>).
\<close>

partial_function (option) bpull :: "'u bops \<Rightarrow> 'u bseq \<Rightarrow> (bres \<times> 'u bseq) option T" where
  "bpull ops s =
    (case s of
      BS_Empty \<Rightarrow> returnT None
    | BS_Its ctx A na xq yq \<Rightarrow> do {
        r \<leftarrow> (case xq of UQ_Cell c \<Rightarrow> returnT (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us);
        case r of
          None \<Rightarrow> bpull ops yq
        | Some (et, us') \<Rightarrow>
            handleT
              (do {th \<leftarrow> addth ctx A na et; returnT (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
              (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseT e)}
    | BS_Tryasms ctx er asms n \<Rightarrow> do {s' \<leftarrow> tryasms ops ctx er asms n; bpull ops s'})"


subsection \<open>Composition\<close>

text \<open>
  The search for unifiers, after the unification of the types of variables: elim-resolution tries
  the assumptions of the subgoal in turn (\<open>eres\<close>), resolution unifies the disagreement pairs
  (\<open>res\<close>).
\<close>

definition bicompose_body :: "'u bops \<Rightarrow> bctx \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> pterm list \<Rightarrow> 'u bseq T" where
  "bicompose_body ops ctx env eres_flg rAs =
    (if eres_flg then
      (case rev rAs of
        [] \<Rightarrow> raiseT (THM (STR ''bicompose: no premises'') 0 Orule_State)
      | A1 # As \<Rightarrow>
          (case assum_problems (bc_nlift ctx + 1) A1 of (params, asms, concl) \<Rightarrow>
            tryasms ops ctx (ER env params concl (rlist_abs params concl) A1 As) asms 1))
    else do {
      us \<leftarrow> bo_unifiers ops env (bc_dpairs ctx);
      r \<leftarrow> bo_pull ops us;
      case r of
        None \<Rightarrow> returnT BS_Empty
      | Some ((env', tpairs), us') \<Rightarrow> do {
          na \<leftarrow> newAs (bo_variants ops) ctx (rev rAs) 0 [bc_BBi ctx] tpairs;
          returnT (BS_Its ctx None na (UQ_Cell ((env', tpairs), us')) BS_Empty)}})"

text \<open>
  \<open>bicompose_aux {flatten, match, incremented} (state, (stpairs, Bs, Bi, C), lifted)
  (eres_flg, orule, nsubgoal)\<close>: composition of the rule \<open>orule = \<lbrakk>A1; \<dots>; Am\<rbrakk> \<Longrightarrow> B\<close> with the
  proof state \<open>\<lbrakk>B1; \<dots>; Bn\<rbrakk> \<Longrightarrow> C\<close>, where \<open>Bi\<close> is the subgoal to be replaced and \<open>Bs\<close> are the
  others. If \<open>match\<close>, instantiations of the proof state are forbidden; if \<open>lifted\<close>, the rule
  is lifted over \<open>Bi\<close> and the common assumptions and parameters are stripped off; if
  \<open>eres_flg\<close>, the first premise of the rule is proved by an assumption of \<open>Bi\<close>
  (elim-resolution); \<open>nsubgoal\<close> is the number \<open>m\<close> of new subgoals. Of a theorem
  (\<open>pthm\<close>), the model takes its maximal index, its flex-flex pairs and its
  proposition; \<open>(stpairs, Bs, Bi, C)\<close> is the result of \<open>dest_state (state, i)\<close>.
\<close>

type_synonym pthm = "integer \<times> (pterm \<times> pterm) list \<times> pterm"

definition bicompose_aux :: "'u bops \<Rightarrow> algebra \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    pthm \<Rightarrow> (pterm \<times> pterm) list \<times> pterm list \<times> pterm \<times> pterm \<Rightarrow> bool \<Rightarrow>
    bool \<Rightarrow> pthm \<Rightarrow> integer \<Rightarrow> 'u bseq T" where
  "bicompose_aux ops alg flatten match_flg incremented state dst lifted eres_flg orule nsubgoal =
    (case state of (smax, _, _) \<Rightarrow> case dst of (stpairs, Bs, Bi, C) \<Rightarrow>
     case orule of (rmax, rtpairs, rprop) \<Rightarrow>
    (let nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) in
    do {
      (rAs, B) \<leftarrow>
        handleT (liftMT (strip_prems nsubgoal [] rprop))
          (\<lambda>e. case e of
            UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: rule'') 0 Orule_State)
          | _ \<Rightarrow> raiseT e);
      let BBi = (if lifted then strip_assums2 B Bi else (B, Bi));
      let ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs);
      r \<leftarrow> if incremented then returnT (Some (empty_env (max rmax smax)))
        else unify_var_types alg (snd state) (snd orule) (empty_env (max rmax smax));
      case r of
        None \<Rightarrow> returnT BS_Empty
      | Some env \<Rightarrow> bicompose_body ops ctx env eres_flg rAs
    }))"


subsection \<open>Instantiation with the model of \<open>unify.ML\<close>\<close>

text \<open>
  The sequences of unifiers of \<^const>\<open>unifiers\<close>, pulled with \<^const>\<open>pull\<close>; their elements are
  unifiers (\<^const>\<open>El_R\<close>).
\<close>

definition upull :: "cfg \<Rightarrow> seq \<Rightarrow> ((env \<times> (pterm \<times> pterm) list) \<times> seq) option T" where
  "upull cfg s =
    liftWT (do {
      r \<leftarrow> pull cfg s;
      case r of
        None \<Rightarrow> returnW None
      | Some (x, s') \<Rightarrow> (case x of
            El_R env tps \<Rightarrow> returnW (Some ((env, tps), s'))
          | _ \<Rightarrow> raiseW (PExn (Failure (STR ''Unify: unexpected element''))))})"

definition unify_ops :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> seq bops" where
  "unify_ops cfg variants =
    BOps (\<lambda>env tus. liftMT (unifiers (cfg_alg cfg) env tus)) (upull cfg) variants"

end
