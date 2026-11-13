section \<open>The sort hypotheses, hypotheses and sort constraints of theorems\<close>

theory Pure_Extra
  imports Pure_Sorts Pure_Subst_Rules
begin

text \<open>
  Besides its logical part, a theorem of \<^file>\<open>~~/src/Pure/thm.ML\<close> has sort hypotheses
  (an ordered list of sorts, \<open>Sorts.union\<close>, \<open>Sorts.insert_term\<close>, \<open>Envir.insert_sorts\<close>),
  hypotheses (an ordered list of terms, \<open>union_hyps\<close>, \<open>insert_hyps\<close>, \<open>remove_hyps\<close> with
  \<open>Term_Ord.fast_term_ord\<close>) and sort constraints (an ordered list of a theory, a type and a
  sort, \<open>union_constraints\<close>, \<open>insert_constraints\<close>, \<open>insert_constraints_env\<close>). These are
  models of these operations; the rules of \<open>thm.ML\<close> compute the data of their results with
  them (\<open>Pure_Bicompose_Code\<close>). The theory of a constraint is a parameter (\<open>'t\<close>), with its order
  (\<open>Context.theory_id_ord\<close>).
\<close>


subsection \<open>Ordered lists\<close>

text \<open>\<open>Ord_List.union\<close> (its exception \<open>SAME\<close> only avoids copying):\<close>

fun ord_union :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ord_union ord [] ys = ys"
| "ord_union ord (x # xs) [] = x # xs"
| "ord_union ord (x # xs) (y # ys) =
    (case ord x y of
      LESS \<Rightarrow> x # ord_union ord xs (y # ys)
    | EQUAL \<Rightarrow> y # ord_union ord xs ys
    | GREATER \<Rightarrow> y # ord_union ord (x # xs) ys)"

lemma set_ord_union_sub: "set (ord_union ord xs ys) \<subseteq> set xs \<union> set ys"
  by (induction ord xs ys rule: ord_union.induct) (auto split: order.splits)

lemma set_ord_union_cover:
  "x \<in> set xs \<union> set ys \<Longrightarrow> \<exists>y\<in>set (ord_union ord xs ys). y = x \<or> ord x y = EQUAL"
  by (induction ord xs ys rule: ord_union.induct) (auto split: order.splits)

lemma set_ord_union:
  "(\<And>x y. ord x y = EQUAL \<Longrightarrow> x = y) \<Longrightarrow> set (ord_union ord xs ys) = set xs \<union> set ys"
  using set_ord_union_sub[of ord xs ys] set_ord_union_cover[of _ xs ys ord] by blast

lemma set_ord_insert_sub: "set (ord_insert ord x xs) \<subseteq> insert x (set xs)"
  by (induction xs) (auto split: order.splits)

lemma set_ord_insert_keep: "set xs \<subseteq> set (ord_insert ord x xs)"
  by (induction xs) (auto split: order.splits)

lemma set_ord_insert_cover: "\<exists>y\<in>set (ord_insert ord x xs). y = x \<or> ord x y = EQUAL"
  by (induction xs) (auto split: order.splits)

lemma set_ord_insert:
  "(\<And>x y. ord x y = EQUAL \<Longrightarrow> x = y) \<Longrightarrow> set (ord_insert ord x xs) = insert x (set xs)"
  using set_ord_insert_sub[of ord x xs] set_ord_insert_keep[of xs ord x] set_ord_insert_cover[of ord x xs]
  by blast

lemma set_ord_remove_sub: "set (ord_remove ord x xs) \<subseteq> set xs"
  by (induction xs) (auto split: order.splits)

lemma set_ord_remove_keep: "y \<in> set xs \<Longrightarrow> ord x y \<noteq> EQUAL \<Longrightarrow> y \<in> set (ord_remove ord x xs)"
  by (induction xs) (auto split: order.splits)


subsection \<open>Orders of \<open>Term_Ord\<close>\<close>

text \<open>
  The orders of \<open>Term_Ord\<close> and \<open>Ord_List.union\<close> return at once if their arguments are the
  same in memory (\<open>pointer_eq\<close>), which makes them fast on shared terms. In the logic,
  \<open>pointer_eq\<close> is only known to hold for equal arguments (\<open>pointer_eqD\<close>): it is the conjunction of
  equality with an unspecified relation. The generated code uses ML's \<open>pointer_eq\<close>
  (\<open>Pure_Bicompose_Code\<close>), which has this property. The results below are proved from it alone,
  so they hold whatever \<open>pointer_eq\<close> answers on equal arguments.
\<close>

consts same_object :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

definition pointer_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "pointer_eq x y \<longleftrightarrow> x = y \<and> same_object x y"

lemma pointer_eqD: "pointer_eq x y \<Longrightarrow> x = y"
  by (simp add: pointer_eq_def)

lemma int_ord_EQUAL: "int_ord i j = EQUAL \<longleftrightarrow> i = j"
  by (simp add: int_ord_def)

lemma string_ord_EQUAL: "string_ord a b = EQUAL \<longleftrightarrow> a = b"
  by (simp add: string_ord_def)

lemma fast_string_ord_EQUAL: "fast_string_ord a b = EQUAL \<longleftrightarrow> a = b"
  by (auto simp: fast_string_ord_def int_ord_def string_ord_def split: order.splits)

lemma dict_ord_EQUAL: "(\<And>x y. ord x y = EQUAL \<longleftrightarrow> x = y) \<Longrightarrow> dict_ord ord xs ys = EQUAL \<longleftrightarrow> xs = ys"
proof (induction ord xs ys rule: dict_ord.induct)
  case (1 ord x xs y ys)
  have e: "ord x y = EQUAL \<longleftrightarrow> x = y" and rf: "ord z z = EQUAL" for z using 1(2) by blast+
  from e show ?case using 1 by (cases "ord x y") (auto simp: rf)
qed auto

lemma sort_ord_EQUAL: "sort_ord S S' = EQUAL \<longleftrightarrow> S = S'"
  unfolding sort_ord_def by (rule dict_ord_EQUAL) (rule fast_string_ord_EQUAL)

lemma fast_string_ord_refl [simp]: "fast_string_ord a a = EQUAL"
  and sort_ord_refl [simp]: "sort_ord S S = EQUAL"
  by (simp_all add: fast_string_ord_EQUAL sort_ord_EQUAL)

definition fast_indexname_ord :: "indexname \<Rightarrow> indexname \<Rightarrow> order" where
  "fast_indexname_ord xi yj =
    (case int_ord (snd xi) (snd yj) of EQUAL \<Rightarrow> fast_string_ord (fst xi) (fst yj) | r \<Rightarrow> r)"

lemma fast_indexname_ord_EQUAL: "fast_indexname_ord xi yj = EQUAL \<longleftrightarrow> xi = yj"
  by (cases xi; cases yj) (auto simp: fast_indexname_ord_def int_ord_def fast_string_ord_EQUAL
    split: order.splits if_splits)

lemma fast_indexname_ord_refl [simp]: "fast_indexname_ord xi xi = EQUAL"
  by (simp add: fast_indexname_ord_EQUAL)

fun typ_cons_nr :: "ptyp \<Rightarrow> integer" where
  "typ_cons_nr (TVar _ _) = 0"
| "typ_cons_nr (TFree _ _) = 1"
| "typ_cons_nr (Type _ _) = 2"

fun typ_ord :: "ptyp \<Rightarrow> ptyp \<Rightarrow> order" and typs_ord :: "ptyp list \<Rightarrow> ptyp list \<Rightarrow> order" where
  "typ_ord (Type a Ts) (Type b Us) = (case fast_string_ord a b of EQUAL \<Rightarrow> typs_ord Ts Us | r \<Rightarrow> r)"
| "typ_ord (TFree a S) (TFree b S') = (case fast_string_ord a b of EQUAL \<Rightarrow> sort_ord S S' | r \<Rightarrow> r)"
| "typ_ord (TVar xi S) (TVar yj S') = (case fast_indexname_ord xi yj of EQUAL \<Rightarrow> sort_ord S S' | r \<Rightarrow> r)"
| "typ_ord (Type a Ts) (TFree b S) = int_ord 2 1"
| "typ_ord (Type a Ts) (TVar v S) = int_ord 2 0"
| "typ_ord (TFree a S) (Type b Us) = int_ord 1 2"
| "typ_ord (TFree a S) (TVar v S') = int_ord 1 0"
| "typ_ord (TVar v S) (Type b Us) = int_ord 0 2"
| "typ_ord (TVar v S) (TFree b S') = int_ord 0 1"
| "typs_ord [] [] = EQUAL"
| "typs_ord [] (_ # _) = LESS"
| "typs_ord (_ # _) [] = GREATER"
| "typs_ord (T # Ts) (U # Us) =
    (case if pointer_eq T U then EQUAL else typ_ord T U of EQUAL \<Rightarrow> typs_ord Ts Us | r \<Rightarrow> r)"

lemma typ_ord_EQUAL: "typ_ord T U = EQUAL \<longleftrightarrow> T = U" and typs_ord_EQUAL: "typs_ord Ts Us = EQUAL \<longleftrightarrow> Ts = Us"
  by (induction T U and Ts Us rule: typ_ord_typs_ord.induct)
    (auto simp: fast_string_ord_EQUAL fast_indexname_ord_EQUAL sort_ord_EQUAL int_ord_def
      dest: pointer_eqD split: order.splits)

fun term_cons_nr :: "pterm \<Rightarrow> integer" where
  "term_cons_nr (Const _ _) = 0"
| "term_cons_nr (Free _ _) = 1"
| "term_cons_nr (Var _ _) = 2"
| "term_cons_nr (Bound _) = 3"
| "term_cons_nr (Abs _ _ _) = 4"
| "term_cons_nr (_ $ _) = 5"

fun struct_ord :: "pterm \<Rightarrow> pterm \<Rightarrow> order" where
  "struct_ord (Abs _ _ t) (Abs _ _ u) = (if pointer_eq t u then EQUAL else struct_ord t u)"
| "struct_ord (t1 $ t2) (u1 $ u2) =
    (case if pointer_eq t1 u1 then EQUAL else struct_ord t1 u1 of
      EQUAL \<Rightarrow> if pointer_eq t2 u2 then EQUAL else struct_ord t2 u2 | r \<Rightarrow> r)"
| "struct_ord t u = int_ord (term_cons_nr t) (term_cons_nr u)"

fun atoms_ord :: "pterm \<Rightarrow> pterm \<Rightarrow> order" where
  "atoms_ord (Abs _ _ t) (Abs _ _ u) = (if pointer_eq t u then EQUAL else atoms_ord t u)"
| "atoms_ord (t1 $ t2) (u1 $ u2) =
    (case if pointer_eq t1 u1 then EQUAL else atoms_ord t1 u1 of
      EQUAL \<Rightarrow> if pointer_eq t2 u2 then EQUAL else atoms_ord t2 u2 | r \<Rightarrow> r)"
| "atoms_ord (Const a _) (Const b _) = fast_string_ord a b"
| "atoms_ord (Free x _) (Free y _) = fast_string_ord x y"
| "atoms_ord (Var xi _) (Var yj _) = fast_indexname_ord xi yj"
| "atoms_ord (Bound i) (Bound j) = int_ord i j"
| "atoms_ord _ _ = EQUAL"

fun types_ord :: "pterm \<Rightarrow> pterm \<Rightarrow> order" where
  "types_ord (Abs _ T t) (Abs _ U u) =
    (case if pointer_eq T U then EQUAL else typ_ord T U of
      EQUAL \<Rightarrow> if pointer_eq t u then EQUAL else types_ord t u | r \<Rightarrow> r)"
| "types_ord (t1 $ t2) (u1 $ u2) =
    (case if pointer_eq t1 u1 then EQUAL else types_ord t1 u1 of
      EQUAL \<Rightarrow> if pointer_eq t2 u2 then EQUAL else types_ord t2 u2 | r \<Rightarrow> r)"
| "types_ord (Const _ T) (Const _ U) = (if pointer_eq T U then EQUAL else typ_ord T U)"
| "types_ord (Free _ T) (Free _ U) = (if pointer_eq T U then EQUAL else typ_ord T U)"
| "types_ord (Var _ T) (Var _ U) = (if pointer_eq T U then EQUAL else typ_ord T U)"
| "types_ord _ _ = EQUAL"

text \<open>\<open>Term_Ord.fast_term_ord\<close> (\<open>struct_ord ||| atoms_ord ||| types_ord\<close>):\<close>

definition fast_term_ord :: "pterm \<Rightarrow> pterm \<Rightarrow> order" where
  "fast_term_ord t u =
    (if pointer_eq t u then EQUAL else case struct_ord t u of
      EQUAL \<Rightarrow> (case atoms_ord t u of EQUAL \<Rightarrow> types_ord t u | r \<Rightarrow> r)
    | r \<Rightarrow> r)"

text \<open>The orders return \<open>EQUAL\<close> on identical arguments (the case of \<open>pointer_eq\<close>):\<close>

lemma typ_ord_refl: "typ_ord T T = EQUAL"
  by (simp add: typ_ord_EQUAL)

lemma struct_ord_refl: "struct_ord t t = EQUAL"
  and atoms_ord_refl: "atoms_ord t t = EQUAL"
  and types_ord_refl: "types_ord t t = EQUAL"
  by (induction t) (simp_all add: int_ord_def typ_ord_refl)

lemma fast_term_ord_refl: "fast_term_ord t t = EQUAL"
  by (simp add: fast_term_ord_def struct_ord_refl atoms_ord_refl types_ord_refl)

lemma ord_union_refl: "(\<And>x. ord x x = EQUAL) \<Longrightarrow> ord_union ord xs xs = xs"
  by (induction xs) auto

lemma aconv_term_refl [simp]: "aconv_term t t"
  by (induction t) auto

lemma fast_term_ord_EQUAL_aconv: "fast_term_ord t u = EQUAL \<Longrightarrow> aconv_term t u"
proof -
  have "struct_ord t u = EQUAL \<Longrightarrow> atoms_ord t u = EQUAL \<Longrightarrow> types_ord t u = EQUAL \<Longrightarrow> aconv_term t u"
    by (induction t arbitrary: u; case_tac u)
      (auto simp: int_ord_def fast_string_ord_EQUAL fast_indexname_ord_EQUAL typ_ord_EQUAL
        dest!: pointer_eqD split: order.splits if_splits)
  then show "fast_term_ord t u = EQUAL \<Longrightarrow> aconv_term t u"
    unfolding fast_term_ord_def by (auto dest!: pointer_eqD split: order.splits if_splits)
qed


subsection \<open>Sort hypotheses\<close>

definition sorts_union :: "psort list \<Rightarrow> psort list \<Rightarrow> psort list" where
  "sorts_union Ss Ss' = (if pointer_eq Ss Ss' then Ss else ord_union sort_ord Ss Ss')"

definition insert_sort :: "psort \<Rightarrow> psort list \<Rightarrow> psort list" where
  "insert_sort = ord_insert sort_ord"

fun insert_typ_sorts :: "ptyp \<Rightarrow> psort list \<Rightarrow> psort list" and insert_typs_sorts :: "ptyp list \<Rightarrow> psort list \<Rightarrow> psort list" where
  "insert_typ_sorts (TFree _ S) Ss = insert_sort S Ss"
| "insert_typ_sorts (TVar _ S) Ss = insert_sort S Ss"
| "insert_typ_sorts (Type _ Ts) Ss = insert_typs_sorts Ts Ss"
| "insert_typs_sorts [] Ss = Ss"
| "insert_typs_sorts (T # Ts) Ss = insert_typs_sorts Ts (insert_typ_sorts T Ss)"

text \<open>\<open>Sorts.insert_term\<close> (the argument of an application first):\<close>

fun insert_term_sorts :: "pterm \<Rightarrow> psort list \<Rightarrow> psort list" where
  "insert_term_sorts (Const _ T) Ss = insert_typ_sorts T Ss"
| "insert_term_sorts (Free _ T) Ss = insert_typ_sorts T Ss"
| "insert_term_sorts (Var _ T) Ss = insert_typ_sorts T Ss"
| "insert_term_sorts (Bound _) Ss = Ss"
| "insert_term_sorts (Abs _ T t) Ss = insert_term_sorts t (insert_typ_sorts T Ss)"
| "insert_term_sorts (t $ u) Ss = insert_term_sorts t (insert_term_sorts u Ss)"

lemma set_sorts_union [simp]: "set (sorts_union Ss Ss') = set Ss \<union> set Ss'"
proof (cases "pointer_eq Ss Ss'")
  case True
  then show ?thesis by (auto simp: sorts_union_def dest: pointer_eqD)
next
  case False
  show ?thesis unfolding sorts_union_def if_not_P[OF False]
    by (rule set_ord_union) (simp add: sort_ord_EQUAL)
qed

lemma set_insert_sort [simp]: "set (insert_sort S Ss) = insert S (set Ss)"
  unfolding insert_sort_def by (rule set_ord_insert) (simp add: sort_ord_EQUAL)

fun typ_sorts :: "ptyp \<Rightarrow> psort set" where
  "typ_sorts (Type a Ts) = (\<Union>T\<in>set Ts. typ_sorts T)"
| "typ_sorts (TFree a S) = {S}"
| "typ_sorts (TVar v S) = {S}"

fun term_sorts :: "pterm \<Rightarrow> psort set" where
  "term_sorts (Const c T) = typ_sorts T"
| "term_sorts (Free x T) = typ_sorts T"
| "term_sorts (Var x T) = typ_sorts T"
| "term_sorts (Bound i) = {}"
| "term_sorts (Abs a T t) = typ_sorts T \<union> term_sorts t"
| "term_sorts (s $ t) = term_sorts s \<union> term_sorts t"

lemma set_insert_typ_sorts [simp]: "set (insert_typ_sorts T Ss) = typ_sorts T \<union> set Ss"
  and set_insert_typs_sorts [simp]: "set (insert_typs_sorts Ts Ss) = (\<Union>T\<in>set Ts. typ_sorts T) \<union> set Ss"
  by (induction T Ss and Ts Ss rule: insert_typ_sorts_insert_typs_sorts.induct) auto

lemma set_insert_term_sorts [simp]: "set (insert_term_sorts t Ss) = term_sorts t \<union> set Ss"
  by (induction t Ss rule: insert_term_sorts.induct) auto


subsection \<open>Hypotheses\<close>

definition union_hyps :: "pterm list \<Rightarrow> pterm list \<Rightarrow> pterm list" where
  "union_hyps hs hs' = (if pointer_eq hs hs' then hs else ord_union fast_term_ord hs hs')"

definition insert_hyps :: "pterm \<Rightarrow> pterm list \<Rightarrow> pterm list" where
  "insert_hyps = ord_insert fast_term_ord"

definition remove_hyps :: "pterm \<Rightarrow> pterm list \<Rightarrow> pterm list" where
  "remove_hyps = ord_remove fast_term_ord"

text \<open>Every hypothesis of \<open>hs\<close> has an \<open>\<alpha>\<close>-equivalent one in \<open>hs'\<close>:\<close>

definition hyps_cover :: "pterm list \<Rightarrow> pterm list \<Rightarrow> bool" where
  "hyps_cover hs hs' \<longleftrightarrow> (\<forall>h\<in>set hs. \<exists>h'\<in>set hs'. aconv_term h h')"

lemma hyps_cover_union_hyps: "hyps_cover (hs1 @ hs2) (union_hyps hs1 hs2)"
proof (cases "pointer_eq hs1 hs2")
  case True
  then have "hs1 = hs2" by (rule pointer_eqD)
  with True show ?thesis
    by (simp add: hyps_cover_def union_hyps_def) (use aconv_term_refl in blast)
next
  case False
  show ?thesis unfolding hyps_cover_def union_hyps_def if_not_P[OF False]
    using set_ord_union_cover[of _ hs1 hs2 fast_term_ord] fast_term_ord_EQUAL_aconv
    by (metis Un_iff aconv_term_refl set_append)
qed

lemma hyps_cover_insert_hyps: "hyps_cover (A # hs) (insert_hyps A hs)"
  unfolding hyps_cover_def insert_hyps_def
proof
  fix h assume h: "h \<in> set (A # hs)"
  show "\<exists>h'\<in>set (ord_insert fast_term_ord A hs). aconv_term h h'"
  proof (cases "h = A")
    case True
    from set_ord_insert_cover[of fast_term_ord A hs] obtain y
      where "y \<in> set (ord_insert fast_term_ord A hs)" "y = A \<or> fast_term_ord A y = EQUAL" by blast
    then show ?thesis using True fast_term_ord_EQUAL_aconv aconv_term_refl by blast
  next
    case False
    with h have "h \<in> set (ord_insert fast_term_ord A hs)" using set_ord_insert_keep[of hs fast_term_ord A] by auto
    then show ?thesis using aconv_term_refl by blast
  qed
qed

lemma hyps_cover_remove_hyps:
  "hyps_cover (filter (\<lambda>h. \<not> aconv_term A h) hs) (remove_hyps A hs)"
  unfolding hyps_cover_def remove_hyps_def
  using set_ord_remove_keep[of _ hs fast_term_ord A] fast_term_ord_EQUAL_aconv aconv_term_refl
  by fastforce


subsection \<open>Sort constraints\<close>

type_synonym 't constraint = "'t \<times> ptyp \<times> psort"

definition constraint_ord :: "('t \<Rightarrow> 't \<Rightarrow> order) \<Rightarrow> 't constraint \<Rightarrow> 't constraint \<Rightarrow> order" where
  "constraint_ord tord c1 c2 =
    (case tord (fst c1) (fst c2) of
      EQUAL \<Rightarrow> (case typ_ord (fst (snd c1)) (fst (snd c2)) of
        EQUAL \<Rightarrow> sort_ord (snd (snd c1)) (snd (snd c2)) | r \<Rightarrow> r)
    | r \<Rightarrow> r)"

definition union_constraints :: "('t \<Rightarrow> 't \<Rightarrow> order) \<Rightarrow> 't constraint list \<Rightarrow> 't constraint list \<Rightarrow> 't constraint list" where
  "union_constraints tord cs cs' = (if pointer_eq cs cs' then cs else ord_union (constraint_ord tord) cs cs')"

text \<open>\<open>smash_atyps\<close> of \<open>thm.ML\<close>: atomic types become \<open>'a\<close> with their sort.\<close>

definition smash_atyps :: "ptyp \<Rightarrow> ptyp" where
  "smash_atyps = map_atyps (\<lambda>T. case T of TVar _ S \<Rightarrow> TFree aT S | TFree _ S \<Rightarrow> TFree aT S | _ \<Rightarrow> T)"

definition insert_constraint :: "('t \<Rightarrow> 't \<Rightarrow> order) \<Rightarrow> 't \<Rightarrow> ptyp \<times> psort \<Rightarrow> 't constraint list \<Rightarrow> 't constraint list" where
  "insert_constraint tord thy TS cs =
    (case TS of (T, S) \<Rightarrow>
      if S = [] then cs
      else if (case T of TFree _ S' \<Rightarrow> S = S' | TVar _ S' \<Rightarrow> S = S' | _ \<Rightarrow> False) then cs
      else ord_insert (constraint_ord tord) (thy, smash_atyps T, S) cs)"

lemma constraint_ord_EQUAL:
  "(\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b) \<Longrightarrow> constraint_ord tord c1 c2 = EQUAL \<Longrightarrow> c1 = c2"
  by (cases c1; cases c2) (auto simp: constraint_ord_def typ_ord_EQUAL sort_ord_EQUAL split: order.splits)

lemma set_union_constraints:
  assumes "\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b"
  shows "set (union_constraints tord cs cs') = set cs \<union> set cs'"
proof (cases "pointer_eq cs cs'")
  case True
  then show ?thesis by (auto simp: union_constraints_def dest: pointer_eqD)
next
  case False
  show ?thesis unfolding union_constraints_def if_not_P[OF False]
    by (rule set_ord_union) (rule constraint_ord_EQUAL[OF assms])
qed

lemma set_insert_constraint:
  "(\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b) \<Longrightarrow> set (insert_constraint tord thy (T, S) cs) =
    (if S = [] \<or> (case T of TFree _ S' \<Rightarrow> S = S' | TVar _ S' \<Rightarrow> S = S' | _ \<Rightarrow> False) then set cs
     else insert (thy, smash_atyps T, S) (set cs))"
proof -
  assume t: "\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b"
  have "set (ord_insert (constraint_ord tord) c cs) = insert c (set cs)" for c
    by (rule set_ord_insert) (rule constraint_ord_EQUAL[OF t])
  then show ?thesis by (simp add: insert_constraint_def)
qed


subsection \<open>Type environments\<close>

text \<open>\<open>Vartab.dest\<close>: the entries of a table, in the order of the keys (left abstract):\<close>

lift_definition vt_dest :: "'a vartab \<Rightarrow> (indexname \<times> 'a) list" is
  "\<lambda>m. SOME xs. distinct (map fst xs) \<and> set xs = {(k, x). m k = Some x}" .

lemma set_vt_dest: "set (vt_dest t) = {(k, x). vt_lookup t k = Some x}"
proof transfer
  fix m :: "indexname \<rightharpoonup> 'a" assume "finite (dom m)"
  then have "finite {(k, x). m k = Some x}"
    by (rule finite_subset[rotated, OF finite_imageI[of _ "\<lambda>k. (k, the (m k))"]]) (auto simp: image_iff)
  then obtain xs where "distinct xs" "set xs = {(k, x). m k = Some x}" using finite_distinct_list by blast
  moreover have "distinct (map fst xs)"
    using calculation by (auto simp: distinct_map inj_on_def)
  ultimately have "\<exists>xs. distinct (map fst xs) \<and> set xs = {(k, x). m k = Some x}" by blast
  then show "set (SOME xs. distinct (map fst xs) \<and> set xs = {(k, x). m k = Some x}) = {(k, x). m k = Some x}"
    by (rule someI2_ex) blast
qed

text \<open>\<open>Envir.insert_sorts\<close>: the sorts of the bindings of the type environment.\<close>

definition env_insert_sorts :: "tyenv \<Rightarrow> psort list \<Rightarrow> psort list" where
  "env_insert_sorts tye Ss = fold (\<lambda>(_, (S, T)). insert_typ_sorts T) (vt_dest tye) Ss"

lemma set_env_insert_sorts:
  "set (env_insert_sorts tye Ss) = {S'. \<exists>v S T. vt_lookup tye v = Some (S, T) \<and> S' \<in> typ_sorts T} \<union> set Ss"
proof -
  have f: "set (fold (\<lambda>(_, (S, T)). insert_typ_sorts T) xs Ss) = (\<Union>(v, S, T)\<in>set xs. typ_sorts T) \<union> set Ss"
    for xs Ss by (induction xs arbitrary: Ss) auto
  show ?thesis unfolding env_insert_sorts_def f set_vt_dest by fastforce
qed

text \<open>
  \<open>insert_constraints_env\<close> of \<open>thm.ML\<close>: the constraints of the bindings of the type
  environment, with the bound types normalised (\<open>Envir.norm_type\<close>).
\<close>

definition constraint_ignored :: "ptyp \<Rightarrow> psort \<Rightarrow> bool" where
  "constraint_ignored T S \<longleftrightarrow> S = [] \<or> (case T of TFree _ S' \<Rightarrow> S = S' | TVar _ S' \<Rightarrow> S = S' | _ \<Rightarrow> False)"

definition env_insert_constraints ::
  "('t \<Rightarrow> 't \<Rightarrow> order) \<Rightarrow> 't \<Rightarrow> tyenv \<Rightarrow> 't constraint list \<Rightarrow> 't constraint list M" where
  "env_insert_constraints tord thy tye cs =
    foldM (\<lambda>(_, (S, T)) cs. if S = [] then return cs
      else bindM (norm_type tye T) (\<lambda>T'. return (insert_constraint tord thy (T', S) cs))) (vt_dest tye) cs"

lemma set_insert_constraint':
  "(\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b) \<Longrightarrow>
    set (insert_constraint tord thy (T, S) cs) = (if constraint_ignored T S then {} else {(thy, smash_atyps T, S)}) \<union> set cs"
  by (auto simp: set_insert_constraint constraint_ignored_def)

lemma set_env_insert_constraints:
  assumes t: "\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b"
    and n: "\<And>v S T T'. vt_lookup tye v = Some (S, T) \<Longrightarrow> norm_type tye T = Some (Ok T') \<Longrightarrow> T' = nf T"
    and ok: "env_insert_constraints tord thy tye cs = Some (Ok cs')"
  shows "set cs' = {(thy, smash_atyps (nf T), S) | v S T. vt_lookup tye v = Some (S, T) \<and> \<not> constraint_ignored (nf T) S}
    \<union> set cs"
proof -
  have "set cs' = {(thy, smash_atyps (nf T), S) | v S T. (v, S, T) \<in> set xs \<and> \<not> constraint_ignored (nf T) S} \<union> set cs"
    if "foldM (\<lambda>(_, (S, T)) cs. if S = [] then return cs
      else bindM (norm_type tye T) (\<lambda>T'. return (insert_constraint tord thy (T', S) cs))) xs cs = Some (Ok cs')"
      "set xs \<subseteq> set (vt_dest tye)"
    for xs cs
    using that
  proof (induction xs arbitrary: cs)
    case Nil
    then show ?case by (simp add: return_def)
  next
    case (Cons x xs)
    obtain v S T where x: "x = (v, S, T)" by (metis prod.collapse)
    show ?case
    proof (cases "S = []")
      case True
      with Cons.prems x have "set cs' = {(thy, smash_atyps (nf T'), S') | v' S' T'. (v', S', T') \<in> set xs \<and>
          \<not> constraint_ignored (nf T') S'} \<union> set cs"
        by (intro Cons.IH) (simp_all add: return_def bindM_def)
      with True x show ?thesis by (auto simp: constraint_ignored_def)
    next
      case False
      with Cons.prems x obtain T' where nt: "norm_type tye T = Some (Ok T')"
        and r: "foldM (\<lambda>(_, (S, T)) cs. if S = [] then return cs
          else bindM (norm_type tye T) (\<lambda>T'. return (insert_constraint tord thy (T', S) cs))) xs
          (insert_constraint tord thy (T', S) cs) = Some (Ok cs')"
        by (auto simp: bindM_def return_def split: option.splits xres.splits)
      have "vt_lookup tye v = Some (S, T)" using Cons.prems(2) x by (auto simp: set_vt_dest)
      then have "T' = nf T" by (rule n[OF _ nt])
      with Cons.IH[OF r] Cons.prems(2) False x show ?thesis by (cases v) (auto simp: set_insert_constraint'[OF t])
    qed
  qed
  from this[OF ok[unfolded env_insert_constraints_def] order_refl] show ?thesis by (auto simp: set_vt_dest)
qed

end
