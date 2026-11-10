section \<open>Witnesses of sorts and the stripping of sort hypotheses\<close>

theory Pure_Sorts
  imports Pure_Axiom
begin

text \<open>
  Literal models of \<open>Sorts.witness_sorts\<close> (with \<open>Sorts.mg_domain\<close> of theory
  \<^theory>\<open>Pure_Pattern.Pure_Envir\<close>), \<open>Sorts.minimize_sort\<close>, the ordered lists of sorts
  (\<open>Ord_List\<close> with \<open>Term_Ord.sort_ord\<close>) and \<open>Logic.present_sorts\<close>, as used by
  \<open>Thm.strip_shyps\<close>.
\<close>


subsection \<open>Orders\<close>

text \<open>\<open>General.order\<close>, \<open>string_ord\<close>, \<open>fast_string_ord\<close>, \<open>dict_ord\<close> and \<open>Term_Ord.sort_ord\<close>.\<close>

datatype order = LESS | EQUAL | GREATER

definition int_ord :: "integer \<Rightarrow> integer \<Rightarrow> order" where
  "int_ord i j = (if i < j then LESS else if i = j then EQUAL else GREATER)"

definition string_ord :: "String.literal \<Rightarrow> String.literal \<Rightarrow> order" where
  "string_ord a b = (if a < b then LESS else if a = b then EQUAL else GREATER)"

definition fast_string_ord :: "String.literal \<Rightarrow> String.literal \<Rightarrow> order" where
  "fast_string_ord a b =
    (if a = b then EQUAL
     else (case int_ord (literal_size a) (literal_size b) of EQUAL \<Rightarrow> string_ord a b | ord \<Rightarrow> ord))"

fun dict_ord :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> order" where
  "dict_ord ord (x # xs) (y # ys) = (case ord x y of EQUAL \<Rightarrow> dict_ord ord xs ys | r \<Rightarrow> r)"
| "dict_ord ord [] [] = EQUAL"
| "dict_ord ord [] (_ # _) = LESS"
| "dict_ord ord (_ # _) [] = GREATER"

definition sort_ord :: "psort \<Rightarrow> psort \<Rightarrow> order" where
  "sort_ord = dict_ord fast_string_ord"

text \<open>\<open>Ord_List.insert\<close>, \<open>Ord_List.remove\<close> and \<open>Ord_List.make\<close> (\<open>sort_distinct\<close>) on ordered lists.\<close>

fun ord_insert :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ord_insert ord x [] = [x]"
| "ord_insert ord x (y # ys) = (case ord x y of LESS \<Rightarrow> x # y # ys | EQUAL \<Rightarrow> y # ys | GREATER \<Rightarrow> y # ord_insert ord x ys)"

fun ord_remove :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ord_remove ord x [] = []"
| "ord_remove ord x (y # ys) = (case ord x y of LESS \<Rightarrow> y # ys | EQUAL \<Rightarrow> ys | GREATER \<Rightarrow> y # ord_remove ord x ys)"

definition ord_make :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ord_make ord xs = fold (ord_insert ord) xs []"


subsection \<open>Sorts\<close>

text \<open>\<open>Sorts.minimize_sort\<close>: the classes of the sort without proper superclasses in it, ordered.\<close>

definition minimize_sort :: "algebra \<Rightarrow> psort \<Rightarrow> psort" where
  "minimize_sort alg S =
    (case S of
      [] \<Rightarrow> []
    | [_] \<Rightarrow> S
    | _ \<Rightarrow> ord_make string_ord (filter (\<lambda>c. \<not> (\<exists>c'\<in>set S. class_less alg c' c)) S))"

text \<open>\<open>Sorts.mg_domain\<close> with \<open>CLASS_ERROR\<close> caught (\<open>mg_dom\<close> of \<open>Sorts.witness_sorts\<close>). For a
  non-empty sort, \<open>mg_domain\<close> raises no other exception (\<open>mg_domain_nonempty\<close> below).\<close>

definition mg_dom :: "algebra \<Rightarrow> name \<Rightarrow> psort \<Rightarrow> psort list option" where
  "mg_dom alg t S = (case mg_domain alg t S of Some (Ok Ss) \<Rightarrow> Some Ss | _ \<Rightarrow> None)"

text \<open>
  \<open>Sorts.witness_sorts algebra ground_types hyps sorts\<close>: witnesses of sorts, as types built from
  the given type constructors and from the types of the hypotheses \<open>hyps\<close> (with their sorts),
  with a state of solved and failed sorts. The recursion does not descend into domains that are
  stronger than a sort on the path.
\<close>

type_synonym witn_state = "(ptyp \<times> psort) list \<times> psort list"

definition witn_get :: "algebra \<Rightarrow> psort \<Rightarrow> ptyp \<times> psort \<Rightarrow> (ptyp \<times> psort) option" where
  "witn_get alg S2 w = (if sort_le alg (snd w) S2 then Some (fst w, S2) else None)"

text \<open>The universe of the sorts on the path, for the termination proof:\<close>

definition arity_classes :: "algebra \<Rightarrow> name list \<Rightarrow> pclass set" where
  "arity_classes alg ts = (\<Union>t\<in>set ts. \<Union>(c, Ss)\<in>set (arities alg t). \<Union>S\<in>set Ss. set S)"

definition path_measure :: "algebra \<Rightarrow> name list \<Rightarrow> psort list \<Rightarrow> nat" where
  "path_measure alg ts path = card (Pow (arity_classes alg ts) - set ` set path)"

definition fresh_sort :: "algebra \<Rightarrow> name list \<Rightarrow> psort list \<Rightarrow> psort \<Rightarrow> bool" where
  "fresh_sort alg ts path S \<longleftrightarrow> set S \<in> Pow (arity_classes alg ts) \<and> set S \<notin> set ` set path"

lemma ps_set_inter_class: "set (inter_class alg c S) \<subseteq> insert c (set S)"
  by (induction S) auto

lemma ps_set_inter_sort: "set (inter_sort alg S1 S2) \<subseteq> set S1 \<union> set S2"
proof -
  have "set (fold (inter_class alg) S1 S2) \<subseteq> set S1 \<union> set S2"
  proof (induction S1 arbitrary: S2)
    case (Cons c cs)
    then show ?case using ps_set_inter_class[of alg c S2] by fastforce
  qed simp
  then show ?thesis by (simp add: inter_sort_def)
qed

text \<open>The domains computed by \<open>mg_domain\<close> consist of classes of the domains of the arities:\<close>

lemma mg_dom_classes:
  assumes "mg_dom alg t S = Some Ds" "D \<in> set Ds"
  shows "set D \<subseteq> (\<Union>(c, Ss)\<in>set (arities alg t). \<Union>S\<in>set Ss. set S)"
proof -
  let ?C = "\<Union>(c, Ss)\<in>set (arities alg t). \<Union>S\<in>set Ss. set S"
  define dom where "dom = (\<lambda>c. case map_of (arities alg t) c of
      None \<Rightarrow> raise (Class_Error (No_Arity t c)) | Some Ss \<Rightarrow> return Ss)"
  define dom_inter where "dom_inter = (\<lambda>c Ss. do {Ds \<leftarrow> dom c; return (map2 (inter_sort alg) Ds Ss)})"
  have dom: "set S' \<subseteq> ?C" if "dom c = return Ss" "S' \<in> set Ss" for c Ss S'
  proof (cases "map_of (arities alg t) c")
    case (Some Ss')
    with that have "Ss' = Ss" by (simp add: dom_def return_def)
    with map_of_SomeD[OF Some] that(2) show ?thesis by blast
  qed (use that in \<open>simp add: dom_def return_def raise_def\<close>)
  have fold: "\<forall>D\<in>set Ds'. set D \<subseteq> ?C"
    if "foldM dom_inter xs Ds0 = Some (Ok Ds')" "\<forall>D\<in>set Ds0. set D \<subseteq> ?C" for xs Ds0 Ds'
    using that
  proof (induction xs arbitrary: Ds0)
    case (Cons x xs)
    from Cons.prems(1) obtain Sx where dx: "dom x = return Sx"
      and r: "foldM dom_inter xs (map2 (inter_sort alg) Sx Ds0) = Some (Ok Ds')"
      by (auto simp: dom_inter_def bindM_def return_def split: option.splits xres.splits)
    have "\<forall>D\<in>set (map2 (inter_sort alg) Sx Ds0). set D \<subseteq> ?C"
    proof
      fix D assume "D \<in> set (map2 (inter_sort alg) Sx Ds0)"
      then obtain a b where ab: "D = inter_sort alg a b" "(a, b) \<in> set (zip Sx Ds0)" by auto
      have "a \<in> set Sx" "b \<in> set Ds0" using set_zip_leftD[OF ab(2)] set_zip_rightD[OF ab(2)] by simp_all
      then show "set D \<subseteq> ?C" using ps_set_inter_sort[of alg a b] dom[OF dx] Cons.prems(2) ab(1) by blast
    qed
    with Cons.IH[OF r] show ?case by blast
  qed (simp add: return_def)
  from assms(1) have md: "mg_domain alg t S = Some (Ok Ds)"
    by (auto simp: mg_dom_def split: option.splits xres.splits)
  show ?thesis
  proof (cases S)
    case (Cons c cs)
    from md obtain Ds0 where d0: "dom c = return Ds0" and f: "foldM dom_inter cs Ds0 = Some (Ok Ds)"
      by (auto simp: mg_domain_def Let_def Cons dom_def dom_inter_def bindM_def return_def raise_def
        split: option.splits xres.splits)
    from fold[OF f] dom[OF d0] assms(2) show ?thesis by blast
  qed (use md in \<open>simp add: mg_domain_def raise_def\<close>)
qed

lemma finite_arity_classes: "finite (arity_classes alg ts)"
  by (auto simp: arity_classes_def)

lemma path_measure_mono: "path_measure alg ts (S # path) \<le> path_measure alg ts path"
  unfolding path_measure_def by (rule card_mono) (auto simp: finite_arity_classes)

lemma path_measure_less: "fresh_sort alg ts path S \<Longrightarrow> path_measure alg ts (S # path) < path_measure alg ts path"
  unfolding path_measure_def fresh_sort_def
  by (rule psubset_card_mono) (auto simp: finite_arity_classes)

lemma sort_le_set: "set S2 \<subseteq> set S1 \<Longrightarrow> sort_le alg S1 S2"
  by (auto simp: sort_le_def class_le_def list_all_iff list_ex_iff)

lemma fresh_domain:
  assumes "mg_dom alg t S = Some SS" "t \<in> set ts" "D \<in> set SS" "\<not> sort_le alg D S" "\<forall>P\<in>set path. \<not> sort_le alg D P"
  shows "fresh_sort alg ts (S # path) D"
proof -
  have "set D \<subseteq> arity_classes alg ts"
    using mg_dom_classes[OF assms(1,3)] assms(2) by (fastforce simp: arity_classes_def)
  moreover have "set D \<noteq> set P" if "P \<in> set (S # path)" for P
    using that assms(4,5) sort_le_set[of P D alg] by auto
  ultimately show ?thesis by (auto simp: fresh_sort_def)
qed

function (sequential) witn_sort :: "algebra \<Rightarrow> name list \<Rightarrow> (ptyp \<times> psort) list \<Rightarrow> psort list \<Rightarrow> psort \<Rightarrow>
    witn_state \<Rightarrow> (ptyp \<times> psort) option \<times> witn_state"
  and witn_sorts :: "algebra \<Rightarrow> name list \<Rightarrow> (ptyp \<times> psort) list \<Rightarrow> psort list \<Rightarrow> psort list \<Rightarrow>
    witn_state \<Rightarrow> (ptyp \<times> psort) option list \<times> witn_state"
  and witn_types :: "algebra \<Rightarrow> name list \<Rightarrow> (ptyp \<times> psort) list \<Rightarrow> psort list \<Rightarrow> name list \<Rightarrow> psort \<Rightarrow>
    witn_state \<Rightarrow> (ptyp \<times> psort) option \<times> witn_state"
where
  "witn_sort alg gts hyps path S (solved, failed) =
    (if S = [] then (Some (propT, []), (solved, failed))
     else if \<exists>F\<in>set failed. sort_le alg S F then (None, (solved, failed))
     else (case List.find (\<lambda>w. witn_get alg S w \<noteq> None) solved of
       Some w \<Rightarrow> (witn_get alg S w, (solved, failed))
     | None \<Rightarrow> (case List.find (\<lambda>w. witn_get alg S w \<noteq> None) hyps of
         Some w \<Rightarrow> (witn_get alg S w, (the (witn_get alg S w) # solved, failed))
       | None \<Rightarrow> witn_types alg gts hyps path gts S (solved, failed))))"
| "witn_sorts alg gts hyps path [] st = ([], st)"
| "witn_sorts alg gts hyps path (S # Ss) st =
    (let (w, st') = witn_sort alg gts hyps path S st; (ws, st'') = witn_sorts alg gts hyps path Ss st'
     in (w # ws, st''))"
| "witn_types alg gts hyps path [] S (solved, failed) = (None, (solved, S # failed))"
| "witn_types alg gts hyps path (t # ts) S st =
    (case mg_dom alg t S of
      Some SS \<Rightarrow>
        if \<exists>D\<in>set SS. sort_le alg D S \<or> (\<exists>P\<in>set path. sort_le alg D P) then witn_types alg gts hyps path ts S st
        else (let (ws, (solved', failed')) = witn_sorts alg gts hyps (S # path) SS st in
          if \<forall>w\<in>set ws. w \<noteq> None then
            (let w = (Type t (map (fst \<circ> the) ws), S) in (Some w, (w # solved', failed')))
          else witn_types alg gts hyps path ts S (solved', failed'))
    | None \<Rightarrow> witn_types alg gts hyps path ts S st)"
  by pat_completeness auto
termination
  apply (relation "measures
    [\<lambda>x. case x of
        Inl (alg, gts, hyps, path, S, st) \<Rightarrow>
          2 * path_measure alg gts path + (if fresh_sort alg gts path S then 0 else 1)
      | Inr (Inl (alg, gts, hyps, path, Ss, st)) \<Rightarrow>
          2 * path_measure alg gts path + (if \<forall>D\<in>set Ss. fresh_sort alg gts path D then 0 else 1)
      | Inr (Inr (alg, gts, hyps, path, ts, S, st)) \<Rightarrow>
          2 * path_measure alg gts path + (if fresh_sort alg gts path S then 0 else 1) +
          (if set ts \<subseteq> set gts then 0 else 2),
     \<lambda>x. case x of Inl _ \<Rightarrow> 2 | Inr (Inl _) \<Rightarrow> 3 | Inr (Inr _) \<Rightarrow> (1 :: nat),
     \<lambda>x. case x of Inl _ \<Rightarrow> 0 | Inr (Inl (_, _, _, _, Ss, _)) \<Rightarrow> length Ss
      | Inr (Inr (_, _, _, _, ts, _, _)) \<Rightarrow> length ts]")
   apply simp_all
  subgoal for alg gts path t ts S SS
  proof -
    assume m: "mg_dom alg t S = Some SS"
      and g: "\<forall>D\<in>set SS. \<not> sort_le alg D S \<and> (\<forall>x\<in>set path. \<not> sort_le alg D x)"
    have f: "t \<in> set gts \<Longrightarrow> \<forall>x\<in>set SS. fresh_sort alg gts (S # path) x"
      using fresh_domain[OF m] g by blast
    have "path_measure alg gts (S # path) \<le> path_measure alg gts path"
      "fresh_sort alg gts path S \<Longrightarrow> path_measure alg gts (S # path) < path_measure alg gts path"
      by (rule path_measure_mono, rule path_measure_less)
    with f show ?thesis by auto
  qed
  done

text \<open>\<open>Sorts.witness_sorts\<close>: the witnesses and the sorts without witness.\<close>

definition witness_sorts :: "algebra \<Rightarrow> name list \<Rightarrow> (ptyp \<times> psort) list \<Rightarrow> psort list \<Rightarrow>
    (ptyp \<times> psort) list \<times> psort list" where
  "witness_sorts alg gts hyps sorts =
    (let witnessed = List.map_filter (\<lambda>x. x) (fst (witn_sorts alg gts hyps [] sorts ([], [])))
     in (witnessed, fold (ord_remove sort_ord \<circ> snd) witnessed sorts))"


subsection \<open>Stripping sort hypotheses\<close>

text \<open>\<open>Type.sort_of_atyp\<close> on atomic types, and \<open>Logic.dummy_tfree\<close>.\<close>

fun atyp_sort :: "ptyp \<Rightarrow> psort" where
  "atyp_sort (TFree _ S) = S"
| "atyp_sort (TVar _ S) = S"
| "atyp_sort _ = []"

definition dummy_tfree :: "psort \<Rightarrow> ptyp" where
  "dummy_tfree S = TFree (String.implode (CHR 0x27 # ''dummy'')) S"

text \<open>
  \<open>Types.list_set (Types.build (fold_terms {hyps = true} Types.add_atyps thm))\<close>: the atomic types of
  a theorem, in the order of their first occurrence in its flex-flex pairs, proposition and
  hypotheses.
\<close>

definition thm_atyps :: "pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> ptyp list" where
  "thm_atyps hyps tpairs prop =
    rev (fold (\<lambda>T acc. if mem_typ T acc then acc else T # acc)
      (concat (map (\<lambda>t. concat (map atyps (term_typs t))) (concat (map (\<lambda>(t, u). [t, u]) tpairs) @ prop # hyps))) [])"

text \<open>\<open>Logic.present_sorts shyps present_set\<close>:\<close>

definition present_sorts :: "psort list \<Rightarrow> ptyp list \<Rightarrow> (ptyp \<times> psort) list \<times> psort list" where
  "present_sorts shyps Ts =
    (let present = map (\<lambda>T. (T, atyp_sort T)) Ts in (present, fold (ord_remove sort_ord \<circ> snd) present shyps))"

text \<open>
  The sort hypotheses of \<open>Thm.strip_shyps\<close>, with the data for its proofs and constraints: the
  present type variables with their sorts, the witnessed sorts, the sorts without witness with
  their minimal forms, and the remaining extra sorts. The ground types are \<open>Sign.logical_types\<close>.
\<close>

record strip_data =
  sd_shyps :: "psort list"
  sd_present :: "(ptyp \<times> psort) list"
  sd_witnessed :: "(ptyp \<times> psort) list"
  sd_non_witnessed :: "(psort \<times> psort) list"
  sd_extra :: "psort list"

definition strip_shyps_data :: "algebra \<Rightarrow> name list \<Rightarrow> psort list \<Rightarrow> ptyp list \<Rightarrow> strip_data" where
  "strip_shyps_data alg gts shyps Ts =
    (let
      lt = (\<lambda>S1 S2. sort_le alg S1 S2 \<and> \<not> sort_le alg S2 S1);
      (present, extra) = present_sorts shyps Ts;
      (witnessed, nw0) = witness_sorts alg gts present extra;
      nw = map (\<lambda>S. (minimize_sort alg S, S)) nw0;
      extra' = ord_make sort_ord (List.map_filter (\<lambda>(S, _). if \<exists>(S', _)\<in>set nw. lt S' S then None else Some S) nw)
     in \<lparr>sd_shyps = fold (ord_insert sort_ord \<circ> snd) present extra', sd_present = present,
       sd_witnessed = witnessed, sd_non_witnessed = nw, sd_extra = extra'\<rparr>)"

text \<open>
  The type of the proofs that replaces an atomic type that is not present: the first of the present
  types, the witnesses and the dummy types of the extra sorts whose sort is below its sort
  (\<open>map_atyp\<close> of \<open>Thm.strip_shyps\<close>; \<open>None\<close> if there is none, where Isabelle raises \<open>Fail\<close>).
\<close>

definition strip_atyp :: "algebra \<Rightarrow> strip_data \<Rightarrow> ptyp \<Rightarrow> ptyp option" where
  "strip_atyp alg d T =
    (if mem_typ T (map fst (sd_present d)) then Some T
     else map_option fst (List.find (\<lambda>(T', S'). sort_le alg S' (atyp_sort T))
       (sd_present d @ sd_witnessed d @ map (\<lambda>S. (dummy_tfree S, S)) (sd_extra d))))"

text \<open>
  The proofs of \<open>Thm.strip_shyps\<close>: the atomic types are mapped by \<open>map_atyp\<close> (\<^const>\<open>strip_atyp\<close>),
  in the classic proof with \<open>Proofterm.map_proof_types\<close> and in the tight proof with
  \<open>ZTerm.map_proof_types {hyps = true}\<close> (also in hypotheses and class proofs), followed by
  \<open>ZTerm.beta_norm_prooft\<close> of \<open>Thm.solve_constraints\<close>. An atomic type without replacement raises
  \<open>Fail\<close>; it is detected at the node of the proof where Isabelle first applies \<open>map_atyp\<close> to it
  (for the classic proof, where no other exception can arise, before the traversal).
\<close>

definition strip_fail :: exn where
  "strip_fail = Failure (STR ''strip_shyps: bad type variable in proof term'')"

definition strip_typ :: "algebra \<Rightarrow> strip_data \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "strip_typ alg d = map_atyps (\<lambda>T. case strip_atyp alg d T of Some T' \<Rightarrow> T' | None \<Rightarrow> T)"

definition strip_typ_ok :: "algebra \<Rightarrow> strip_data \<Rightarrow> ptyp \<Rightarrow> bool" where
  "strip_typ_ok alg d T \<longleftrightarrow> list_all (\<lambda>U. strip_atyp alg d U \<noteq> None) (atyps T)"

text \<open>The types to which \<open>Proofterm.map_proof_terms_same\<close> applies its functions:\<close>

fun proof_typs :: "prf \<Rightarrow> ptyp list" where
  "proof_typs (Abst a T p) = (case T of Some T \<Rightarrow> [T] | None \<Rightarrow> []) @ proof_typs p"
| "proof_typs (AbsP a t p) = (case t of Some t \<Rightarrow> term_typs t | None \<Rightarrow> []) @ proof_typs p"
| "proof_typs (PAppt p t) = proof_typs p @ (case t of Some t \<Rightarrow> term_typs t | None \<Rightarrow> [])"
| "proof_typs (PAppp p q) = proof_typs p @ proof_typs q"
| "proof_typs (PAxm a A Ts) = (case Ts of Some Ts \<Rightarrow> Ts | None \<Rightarrow> [])"
| "proof_typs (PClass T c) = [T]"
| "proof_typs (Oracle a A Ts) = (case Ts of Some Ts \<Rightarrow> Ts | None \<Rightarrow> [])"
| "proof_typs (PThm (h, b)) = (case hd_types h of Some Ts \<Rightarrow> Ts | None \<Rightarrow> [])"
| "proof_typs p = []"

definition strip_proof :: "algebra \<Rightarrow> strip_data \<Rightarrow> prf \<Rightarrow> prf P" where
  "strip_proof alg d p =
    (if list_all (strip_typ_ok alg d) (proof_typs p)
     then returnW (map_proof_terms (map_types (strip_typ alg d)) (strip_typ alg d) p)
     else raiseW strip_fail)"

text \<open>\<open>ZTVars.dest\<close>: the entries of a table of type variables (left abstract).\<close>

definition zt_dest :: "'a ztvtab \<Rightarrow> ((indexname \<times> psort) \<times> 'a) list" where
  "zt_dest t = (SOME xs. distinct (map fst xs) \<and> set xs = {(k, x). Rep_ztvtab t k = Some x})"

text \<open>\<open>map_ztyp\<close> of \<open>Thm.strip_shyps\<close>, with the check whether \<open>map_atyp\<close> succeeds:\<close>

definition zstrip_type :: "algebra \<Rightarrow> strip_data \<Rightarrow> ztyp \<Rightarrow> ztyp" where
  "zstrip_type alg d = zsubst_type (\<lambda>(v, S). map_option ztyp_of (strip_atyp alg d (typ_of (ZTVar v S))))"

definition zstrip_ok :: "algebra \<Rightarrow> strip_data \<Rightarrow> ztyp \<Rightarrow> bool" where
  "zstrip_ok alg d T \<longleftrightarrow> list_all (\<lambda>(v, S). strip_atyp alg d (typ_of (ZTVar v S)) \<noteq> None) (ztyp_tvars T)"

definition zstrip_check :: "bool \<Rightarrow> unit Z" where
  "zstrip_check b = (if b then return () else raise (ZExn strip_fail))"

definition zstrip_term :: "algebra \<Rightarrow> strip_data \<Rightarrow> zterm \<Rightarrow> zterm Z" where
  "zstrip_term alg d t = do {
    zstrip_check (list_all (zstrip_ok alg d) (zterm_types t));
    return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)}"

definition zstrip_insts_ok :: "algebra \<Rightarrow> strip_data \<Rightarrow> ztyp ztvtab \<times> zterm zvtab \<Rightarrow> bool" where
  "zstrip_insts_ok alg d insts = (case insts of (instT, inst) \<Rightarrow>
    list_all (zstrip_ok alg d \<circ> snd) (zt_dest instT) \<and>
    list_all (\<lambda>((x, T), t). zstrip_ok alg d T \<and> list_all (zstrip_ok alg d) (zterm_types t)) (zv_dest inst))"

fun zstrip_proof :: "algebra \<Rightarrow> strip_data \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zstrip_proof alg d (ZConstp (a, insts)) = do {
    zstrip_check (zstrip_insts_ok alg d insts);
    insts' \<leftarrow> map_insts (zstrip_type alg d) (zstrip_term alg d) insts;
    return (ZConstp (a, insts'))}"
| "zstrip_proof alg d (ZAbst a T p) = do {
    zstrip_check (zstrip_ok alg d T); p' \<leftarrow> zstrip_proof alg d p; return (ZAbst a (zstrip_type alg d T) p')}"
| "zstrip_proof alg d (ZAbsp a t p) = do {
    t' \<leftarrow> zstrip_term alg d t; p' \<leftarrow> zstrip_proof alg d p; return (ZAbsp a t' p')}"
| "zstrip_proof alg d (ZAppt p t) = do {
    p' \<leftarrow> zstrip_proof alg d p; t' \<leftarrow> zstrip_term alg d t; return (ZAppt p' t')}"
| "zstrip_proof alg d (ZAppp p q) = do {
    p' \<leftarrow> zstrip_proof alg d p; q' \<leftarrow> zstrip_proof alg d q; return (ZAppp p' q')}"
| "zstrip_proof alg d (ZHyp h) = do {h' \<leftarrow> zstrip_term alg d h; return (ZHyp h')}"
| "zstrip_proof alg d (OFCLASSp T c) = do {
    zstrip_check (zstrip_ok alg d T); return (OFCLASSp (zstrip_type alg d T) c)}"
| "zstrip_proof alg d p = return p"

text \<open>The tight proof after \<open>Thm.strip_shyps\<close> (with \<open>Thm.solve_constraints\<close>); if there are no
  sort hypotheses, the proof is only normalized.\<close>

definition zstrip_shyps_proof :: "algebra \<Rightarrow> strip_data option \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zstrip_shyps_proof alg d p = do {
    p' \<leftarrow> (case d of Some d \<Rightarrow> zstrip_proof alg d p | None \<Rightarrow> return p);
    liftOZ (beta_norm_prooft p')}"

definition strip_shyps_proof :: "algebra \<Rightarrow> strip_data option \<Rightarrow> prf \<Rightarrow> prf P" where
  "strip_shyps_proof alg d p = (case d of Some d \<Rightarrow> strip_proof alg d p | None \<Rightarrow> returnW p)"

text \<open>\<open>Thm.strip_shyps\<close> on the logical part: the data, if there are sort hypotheses.\<close>

definition strip_shyps_rep :: "algebra \<Rightarrow> name list \<Rightarrow> psort list \<Rightarrow> pterm list \<Rightarrow> thm_rep \<Rightarrow> strip_data option" where
  "strip_shyps_rep alg gts shyps hyps th =
    (if shyps = [] then None else Some (strip_shyps_data alg gts shyps (thm_atyps hyps (th_tpairs th) (th_prop th))))"

end