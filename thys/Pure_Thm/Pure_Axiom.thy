section \<open>The axiom rule of \<open>thm.ML\<close>\<close>

theory Pure_Axiom
  imports Pure_Subst_Rules
begin

text \<open>
  A literal model of \<open>Thm.axiom\<close> on the proposition of an axiom: the logical part, the classic
  proof \<open>Proofterm.axiom_proof\<close> (with \<open>Proofterm.prop_args\<close> and \<open>Logic.unconstrainT\<close>) and the
  tight proof \<open>ZTerm.axiom_proof\<close>. The lookup of the axiom in the theory is part of the
  signature (theory \<open>Thm_Correctness.Thm_Rules4\<close>). The names of the type variables that
  \<open>Logic.unconstrainT\<close> invents (\<open>Name.invent_global_types\<close>) are a parameter \<open>invent\<close>.
\<close>


subsection \<open>Sets of types\<close>

text \<open>
  \<open>Types.list_set (Types.build (Types.add_atyps t))\<close>: the atomic types of a term in the order of
  their first occurrence (the sets of \<open>Term_Items\<close> keep the order of addition). Types are
  compared with the equality of ML (theory \<open>Pure_Pattern_Code\<close>), without equality dictionaries.
\<close>

fun mem_typ :: "ptyp \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "mem_typ T [] = False"
| "mem_typ T (U # Us) = (T = U \<or> mem_typ T Us)"

lemma mem_typ_iff [simp]: "mem_typ T Us \<longleftrightarrow> T \<in> set Us"
  by (induction Us) auto

definition term_atyps :: "pterm \<Rightarrow> ptyp list" where
  "term_atyps t = rev (fold (\<lambda>T acc. if mem_typ T acc then acc else T # acc) (concat (map atyps (term_typs t))) [])"


subsection \<open>Unconstraining the type variables\<close>

text \<open>\<open>Type.sort_of_atyp\<close>, \<open>Term.strip_sortsT\<close> on the type variables of \<open>Logic.unconstrainT\<close>.\<close>

fun sort_of_atyp :: "ptyp \<Rightarrow> psort M" where
  "sort_of_atyp (TFree _ S) = return S"
| "sort_of_atyp (TVar _ S) = return S"
| "sort_of_atyp T = raise (Type_Error (STR ''sort_of_atyp'') [T] [])"

text \<open>\<open>Term.map_atyps\<close> and \<open>Term.map_types\<close> with an operation that may raise an exception.\<close>

fun map_atypsM :: "(ptyp \<Rightarrow> ptyp M) \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "map_atypsM f (Type a Ts) = do {Us \<leftarrow> mapM (map_atypsM f) Ts; return (Type a Us)}"
| "map_atypsM f T = f T"

fun map_typesM :: "(ptyp \<Rightarrow> ptyp M) \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "map_typesM f (Const c T) = do {U \<leftarrow> f T; return (Const c U)}"
| "map_typesM f (Free x T) = do {U \<leftarrow> f T; return (Free x U)}"
| "map_typesM f (Var xi T) = do {U \<leftarrow> f T; return (Var xi U)}"
| "map_typesM f (Bound i) = return (Bound i)"
| "map_typesM f (Abs x T b) = do {U \<leftarrow> f T; b' \<leftarrow> map_typesM f b; return (Abs x U b')}"
| "map_typesM f (t $ u) = do {t' \<leftarrow> map_typesM f t; u' \<leftarrow> map_typesM f u; return (t' $ u')}"

text \<open>
  \<open>Logic.unconstrainT [] prop\<close>: the atomic types of the proposition (all of them are present,
  there are no extra sorts) become schematic type variables with the invented names, index \<open>0\<close>
  and their sorts; the proposition gets them without sorts and the premises \<open>OFCLASS\<close> for the
  classes of their sorts. The result: the outer constraints and the new proposition.
\<close>

definition unconstrain_atyp :: "(ptyp \<times> ptyp) list \<Rightarrow> (psort \<times> ptyp) list \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "unconstrain_atyp present_map constraints_map T =
    (case map_of present_map T of
      Some T' \<Rightarrow> return (case T' of TVar ai _ \<Rightarrow> TVar ai [] | _ \<Rightarrow> T')
    | None \<Rightarrow> do {
        S \<leftarrow> sort_of_atyp T;
        case map_of constraints_map S of
          Some T' \<Rightarrow> return (case T' of TVar ai _ \<Rightarrow> TVar ai [] | _ \<Rightarrow> T')
        | None \<Rightarrow> raise (Type_Error (STR ''Dangling type variable '') [T] [])})"

definition unconstrainT :: "(integer \<Rightarrow> name list) \<Rightarrow> pterm \<Rightarrow> ((ptyp \<times> pclass) list \<times> pterm) M" where
  "unconstrainT invent prop = do {
    let Ts = term_atyps prop;
    present \<leftarrow> mapM (\<lambda>T. do {S \<leftarrow> sort_of_atyp T; return (T, S)}) Ts;
    let names1 = take (length present) (invent (integer_of_nat (length present)));
    let present_map = map2 (\<lambda>(T, S) a. (T, TVar (a, 0) S)) present names1;
    let constraints_map = map (\<lambda>(_, V). ((case V of TVar _ S \<Rightarrow> S | _ \<Rightarrow> []), V)) present_map;
    let constraints = concat (map (\<lambda>(_, V). case V of TVar ai S \<Rightarrow> map (\<lambda>c. mk_of_class (TVar ai []) c) S | _ \<Rightarrow> [])
      constraints_map);
    let outer_constraints = concat (map (\<lambda>(T, S). map (\<lambda>c. (T, c)) S) present);
    prop' \<leftarrow> map_typesM (map_atypsM (unconstrain_atyp present_map constraints_map)) prop;
    return (outer_constraints, list_implies constraints prop')}"


subsection \<open>The arguments of a proof constant\<close>

text \<open>\<open>Proofterm.variables_of\<close>, \<open>Proofterm.vars_of\<close> (the variables of a term in the order of their first
  occurrence).\<close>

definition variables_of :: "pterm \<Rightarrow> pterm list" where
  "variables_of t = rev (fold (\<lambda>a acc. case a of Var _ _ \<Rightarrow> List.insert a acc | Free _ _ \<Rightarrow> List.insert a acc
    | _ \<Rightarrow> acc) (aterms t) [])"

definition vars_of :: "pterm \<Rightarrow> pterm list" where
  "vars_of t = map (\<lambda>(xi, T). Var xi T)
    (rev (fold (\<lambda>a acc. case a of Var xi T \<Rightarrow> List.insert (xi, T) acc | _ \<Rightarrow> acc) (aterms t) []))"

fun test_args :: "integer list \<Rightarrow> pterm list \<Rightarrow> bool" where
  "test_args is [] = True"
| "test_args is (Bound i # ts) = (i \<notin> set is \<and> test_args (i # is) ts)"
| "test_args is _ = False"

fun is_fun :: "ptyp \<Rightarrow> bool" where
  "is_fun (Type a _) = (a = STR ''fun'')"
| "is_fun (TVar _ _) = True"
| "is_fun _ = False"

text \<open>\<open>union (op =)\<close> of the ML library: the elements of the first list are inserted into the second.\<close>

definition list_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_union xs ys = fold List.insert xs ys"

definition add_funvars :: "ptyp list \<Rightarrow> indexname list \<Rightarrow> pterm \<Rightarrow> indexname list M" where
  "add_funvars Ts vs t = do {
    T \<leftarrow> fastype_of_term Ts t;
    return (if is_fun T then
      list_union vs (List.map_filter (\<lambda>v. case v of Var ixn T \<Rightarrow> if is_fun T then Some ixn else None | _ \<Rightarrow> None) (vars_of t))
     else vs)}"

text \<open>\<open>AList.update (op =)\<close> and \<open>AList.lookup (op =)\<close>.\<close>

fun alist_update :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "alist_update (k, v) [] = [(k, v)]"
| "alist_update (k, v) ((k', v') # xs) = (if k = k' then (k, v) # xs else (k', v') # alist_update (k, v) xs)"

text \<open>
  A size of terms that decreases under the instantiation of a quantifier by a variable
  (\<open>add_npvars\<close> recurses on \<open>betapply (t, Var ((\<open>''''\<close>, 0), T))\<close>):
\<close>

fun npsize :: "pterm \<Rightarrow> nat" where
  "npsize (Const _ _) = 2"
| "npsize (Abs _ _ t) = Suc (npsize t)"
| "npsize (t $ u) = Suc (npsize t + npsize u)"
| "npsize _ = 1"

lemma npsize_pos: "0 < npsize t"
  by (cases t) simp_all

lemma npsize_subst_var: "npsize (subst_bound_aux (Var v T) i t) = npsize t"
  by (induction t arbitrary: i) (simp_all add: incr_boundvars_def)

lemma npsize_betapply_var: "npsize (betapply t (Var v T)) < Suc (Suc (Suc (npsize t)))"
  by (cases t) (simp_all add: subst_bound_def npsize_subst_var)

lemma npsize_strip_comb_acc:
  "strip_comb_acc t acc = (h, ts) \<Longrightarrow>
    npsize h + sum_list (map npsize ts) + length ts = npsize t + sum_list (map npsize acc) + length acc"
  by (induction t acc rule: strip_comb_acc.induct) auto

lemma npsize_strip_comb:
  assumes "strip_comb t = (h, ts)"
  shows "npsize h + sum_list (map npsize ts) + length ts = npsize t"
  using npsize_strip_comb_acc[of t "[]" h ts] assms by (simp add: strip_comb_def)

lemma strip_comb_args_less: "strip_comb t = (h, ts) \<Longrightarrow> sum_list (map npsize ts) < npsize t"
  using npsize_strip_comb[of t h ts] npsize_pos[of h] by linarith

lemma strip_comb_abs_less: "strip_comb t = (Abs x T u, ts) \<Longrightarrow> npsize u + sum_list (map npsize ts) < npsize t"
  using npsize_strip_comb[of t "Abs x T u" ts] by simp

function (sequential) add_npvars :: "bool \<Rightarrow> bool \<Rightarrow> ptyp list \<Rightarrow> (indexname \<times> indexname list) list \<Rightarrow> pterm \<Rightarrow>
    (indexname \<times> indexname list) list M"
  and add_npvars' :: "ptyp list \<Rightarrow> (indexname \<times> indexname list) list \<Rightarrow> pterm \<Rightarrow> (indexname \<times> indexname list) list M"
  and add_npvars'_list :: "ptyp list \<Rightarrow> (indexname \<times> indexname list) list \<Rightarrow> pterm list \<Rightarrow> (indexname \<times> indexname list) list M"
where
  "add_npvars q p Ts vs (Const c T $ t $ u) =
    (if c = STR ''Pure.imp'' then do {vs' \<leftarrow> add_npvars q (\<not> p) Ts vs t; add_npvars q p Ts vs' u}
     else add_npvars' Ts vs (Const c T $ t $ u))"
| "add_npvars q p Ts vs (Const c (Type f1 [Type f2 [T, U], V]) $ t) =
    (if c = STR ''Pure.all'' then add_npvars q p Ts vs (if p \<and> q then betapply t (Var (STR '''', 0) T) else t)
     else add_npvars' Ts vs (Const c (Type f1 [Type f2 [T, U], V]) $ t))"
| "add_npvars q p Ts vs (Abs _ T t) = add_npvars q p (T # Ts) vs t"
| "add_npvars q p Ts vs t = add_npvars' Ts vs t"
| "add_npvars' Ts vs t =
    (case strip_comb t of
      (Var ixn _, ts) \<Rightarrow>
        if test_args [] ts then return vs
        else do {
          fv \<leftarrow> foldM (\<lambda>t vs. add_funvars Ts vs t) ts (case map_of vs ixn of Some l \<Rightarrow> l | None \<Rightarrow> []);
          add_npvars'_list Ts (alist_update (ixn, fv) vs) ts}
    | (Abs _ T u, ts) \<Rightarrow> add_npvars'_list (T # Ts) vs (u # ts)
    | (_, ts) \<Rightarrow> add_npvars'_list Ts vs ts)"
| "add_npvars'_list Ts vs [] = return vs"
| "add_npvars'_list Ts vs (t # ts) = do {vs' \<leftarrow> add_npvars' Ts vs t; add_npvars'_list Ts vs' ts}"
  by pat_completeness auto
termination
  apply (relation "measures [\<lambda>x. case x of Inl (q, p, Ts, vs, t) \<Rightarrow> npsize t | Inr (Inl (Ts, vs, t)) \<Rightarrow> npsize t
      | Inr (Inr (Ts, vs, ts)) \<Rightarrow> sum_list (map npsize ts),
    \<lambda>x. case x of Inl _ \<Rightarrow> 2 | Inr (Inl _) \<Rightarrow> 0 | Inr (Inr _) \<Rightarrow> (1::nat)]")
  apply (simp_all add: npsize_betapply_var npsize_pos)
  apply (blast dest: sym[THEN strip_comb_args_less] sym[THEN strip_comb_abs_less])+
  apply (metis gr0I npsize_pos sum_list_eq_0_iff map_is_Nil_conv imageI list.set_map)
  done

fun prop_vars :: "pterm \<Rightarrow> indexname list" where
  "prop_vars (Const c T $ P $ Q) =
    (if c = STR ''Pure.imp'' then list_union (prop_vars P) (prop_vars Q)
     else (case strip_comb (Const c T $ P $ Q) of (Var ixn _, _) \<Rightarrow> [ixn] | _ \<Rightarrow> []))"
| "prop_vars (Const c T $ Abs x U t) =
    (if c = STR ''Pure.all'' then prop_vars t
     else (case strip_comb (Const c T $ Abs x U t) of (Var ixn _, _) \<Rightarrow> [ixn] | _ \<Rightarrow> []))"
| "prop_vars t = (case strip_comb t of (Var ixn _, _) \<Rightarrow> [ixn] | _ \<Rightarrow> [])"

text \<open>\<open>Proofterm.prop_args\<close>: the arguments of a proof constant for the variables of its
  proposition; those that the proposition does not need are omitted.\<close>

definition prop_args :: "pterm \<Rightarrow> pterm option list M" where
  "prop_args prop = do {
    npvs \<leftarrow> add_npvars True True [] [] prop;
    let needed = list_union (foldl list_union [] (map (\<lambda>(ixn, l). List.insert ixn l) npvs)) (prop_vars prop);
    return (map (\<lambda>v. case v of Var ixn _ \<Rightarrow> if ixn \<in> set needed then Some v else None | _ \<Rightarrow> Some v)
      (variables_of prop))}"


subsection \<open>Code equations\<close>

text \<open>
  The generated code compares types and terms with the equality of ML, without equality
  dictionaries (theory \<open>Pure_Pattern_Code\<close>): membership and lookup in lists of
  types and terms are monomorphic.
\<close>

fun mem_pterm :: "pterm \<Rightarrow> pterm list \<Rightarrow> bool" where
  "mem_pterm t [] = False"
| "mem_pterm t (u # us) = (t = u \<or> mem_pterm t us)"

fun mem_var :: "indexname \<times> ptyp \<Rightarrow> (indexname \<times> ptyp) list \<Rightarrow> bool" where
  "mem_var v [] = False"
| "mem_var v (w # ws) = ((fst v = fst w \<and> snd v = snd w) \<or> mem_var v ws)"

fun assoc_typ :: "(ptyp \<times> 'a) list \<Rightarrow> ptyp \<Rightarrow> 'a option" where
  "assoc_typ [] T = None"
| "assoc_typ ((U, x) # xs) T = (if T = U then Some x else assoc_typ xs T)"

lemma mem_pterm_iff [simp]: "mem_pterm t us \<longleftrightarrow> t \<in> set us"
  by (induction us) auto

lemma mem_var_iff [simp]: "mem_var v ws \<longleftrightarrow> v \<in> set ws"
  by (induction ws) (auto simp: prod_eq_iff)

lemma assoc_typ_map_of [simp]: "assoc_typ xs T = map_of xs T"
  by (induction xs) auto

lemma variables_of_code [code]:
  "variables_of t = rev (fold (\<lambda>a acc. if (case a of Var _ _ \<Rightarrow> True | Free _ _ \<Rightarrow> True | _ \<Rightarrow> False)
    then (if mem_pterm a acc then acc else a # acc) else acc) (aterms t) [])"
  unfolding variables_of_def by (rule arg_cong[where f = rev], rule fold_cong) (auto simp: List.insert_def split: pterm.splits)

lemma vars_of_code [code]:
  "vars_of t = map (\<lambda>(xi, T). Var xi T)
    (rev (fold (\<lambda>a acc. case a of Var xi T \<Rightarrow> if mem_var (xi, T) acc then acc else (xi, T) # acc | _ \<Rightarrow> acc)
      (aterms t) []))"
  by (simp add: vars_of_def List.insert_def cong: pterm.case_cong)

lemma unconstrain_atyp_code [code]:
  "unconstrain_atyp present_map constraints_map T =
    (case assoc_typ present_map T of
      Some T' \<Rightarrow> return (case T' of TVar ai _ \<Rightarrow> TVar ai [] | _ \<Rightarrow> T')
    | None \<Rightarrow> do {
        S \<leftarrow> sort_of_atyp T;
        case map_of constraints_map S of
          Some T' \<Rightarrow> return (case T' of TVar ai _ \<Rightarrow> TVar ai [] | _ \<Rightarrow> T')
        | None \<Rightarrow> raise (Type_Error (STR ''Dangling type variable '') [T] [])})"
  by (simp add: unconstrain_atyp_def)


subsection \<open>The rule\<close>

text \<open>\<open>Thm.axiom thy name\<close> on the proposition of the axiom: no hypotheses and flex-flex pairs.\<close>

definition axiom_rule :: "pterm \<Rightarrow> thm_rep" where
  "axiom_rule prop = mk_rep (maxidx_of_term prop) [] prop"

text \<open>\<open>Proofterm.axiom_proof name prop\<close> (\<open>Proofterm.const_proof PAxm\<close>):\<close>

definition axiom_proof :: "(integer \<Rightarrow> name list) \<Rightarrow> name \<Rightarrow> pterm \<Rightarrow> prf M" where
  "axiom_proof invent name prop = do {
    args \<leftarrow> prop_args prop;
    (outer, prop1) \<leftarrow> unconstrainT invent prop;
    return (proof_combP (foldl PAppt (PAxm name prop1 None) args) (map (\<lambda>(T, c). PClass T c) outer))}"

text \<open>\<open>ZTerm.axiom_proof thy name prop\<close> (\<open>ZTerm.zproof_const\<close>): the instantiation maps each
  type variable and variable of the encoded proposition to itself.\<close>

fun ztyp_tvars :: "ztyp \<Rightarrow> (indexname \<times> psort) list" where
  "ztyp_tvars (ZTVar v S) = [(v, S)]"
| "ztyp_tvars (ZFun T U) = ztyp_tvars T @ ztyp_tvars U"
| "ztyp_tvars (ZType1 _ T) = ztyp_tvars T"
| "ztyp_tvars (ZType _ Ts) = concat (map ztyp_tvars Ts)"
| "ztyp_tvars _ = []"

fun zterm_types :: "zterm \<Rightarrow> ztyp list" where
  "zterm_types (ZVar _ T) = [T]"
| "zterm_types (ZConst1 _ T) = [T]"
| "zterm_types (ZConst _ Ts) = Ts"
| "zterm_types (ZAbs _ T b) = T # zterm_types b"
| "zterm_types (ZApp t u) = zterm_types t @ zterm_types u"
| "zterm_types (ZOfclass T _) = [T]"
| "zterm_types _ = []"

fun zterm_vars :: "zterm \<Rightarrow> (indexname \<times> ztyp) list" where
  "zterm_vars (ZVar xi T) = [(xi, T)]"
| "zterm_vars (ZAbs _ _ b) = zterm_vars b"
| "zterm_vars (ZApp t u) = zterm_vars t @ zterm_vars u"
| "zterm_vars _ = []"

definition zproof_const :: "zproof_name \<Rightarrow> zterm \<Rightarrow> zproof_const" where
  "zproof_const a A =
    ((a, A),
     (fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) (concat (map ztyp_tvars (zterm_types A))) zt_empty,
      fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) (zterm_vars A) zv_empty))"

definition zaxiom_proof_of :: "ztypargs \<Rightarrow> name \<Rightarrow> pterm \<Rightarrow> zproof Z" where
  "zaxiom_proof_of ta name prop = do {A \<leftarrow> zterm_of ta prop; return (ZConstp (zproof_const (ZAxiom name) A))}"

end
