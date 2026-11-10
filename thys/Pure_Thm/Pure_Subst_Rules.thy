section \<open>Derived rules of \<open>thm.ML\<close>: substitution, indices, permutation and type variables\<close>

theory Pure_Subst_Rules
  imports Pure_Rules
begin

text \<open>
  Literal models of \<open>Thm.generalize\<close>, \<open>Thm.instantiate\<close>, \<open>Thm.instantiate_beta\<close>,
  \<open>Thm.incr_indexes\<close>, \<open>Thm.rotate_rule\<close>, \<open>Thm.permute_prems\<close>, \<open>Thm.varifyT_global'\<close>,
  \<open>Thm.legacy_freezeT\<close> and \<open>Thm.of_class\<close>, with their classic and tight proofs, on the logical
  part of theorems as in \<^theory_text>\<open>Pure_Rules\<close>. Tables of variables (\<open>TVars\<close>,
  \<open>Vars\<close>, \<open>Names\<close>, \<open>TFrees\<close>) are lists without duplicate keys, in the order of the keys. The
  generation of fresh names (\<open>Name.variant_list\<close>) is a parameter \<open>vl\<close>, as for
  \<^const>\<open>bicompose_aux\<close>; the certification of the instantiations (\<open>Sign.of_sort\<close>, the types
  of the instances) is modelled, but its error messages are left to the ML wrapper
  (\<^const>\<open>NOT_OF_SORT\<close>, \<^const>\<open>INST_CONFLICT\<close>).
\<close>


subsection \<open>Folds over terms\<close>

text \<open>The types of a term in the order of \<open>Term.fold_types\<close>, and the atomic types of a type in
  the order of \<open>Term.fold_atyps\<close>.\<close>

fun term_typs :: "pterm \<Rightarrow> ptyp list" where
  "term_typs (Const _ T) = [T]"
| "term_typs (Free _ T) = [T]"
| "term_typs (Var _ T) = [T]"
| "term_typs (Bound _) = []"
| "term_typs (Abs _ T b) = T # term_typs b"
| "term_typs (t $ u) = term_typs t @ term_typs u"

fun atyps :: "ptyp \<Rightarrow> ptyp list" where
  "atyps (Type _ Ts) = concat (map atyps Ts)"
| "atyps T = [T]"

text \<open>The atoms of a term in the order of \<open>Term.fold_aterms\<close>.\<close>

fun aterms :: "pterm \<Rightarrow> pterm list" where
  "aterms (t $ u) = aterms t @ aterms u"
| "aterms (Abs _ _ b) = aterms b"
| "aterms t = [t]"

text \<open>\<open>Term.add_tvars\<close>, \<open>Term.add_tfrees\<close>, \<open>Term.add_tfree_names\<close>: \<open>insert\<close> in the order of
  \<open>fold_types\<close>/\<open>fold_atyps\<close>.\<close>

definition add_tvars :: "pterm \<Rightarrow> (indexname \<times> psort) list \<Rightarrow> (indexname \<times> psort) list" where
  "add_tvars t xs =
    fold (\<lambda>T acc. case T of TVar v S \<Rightarrow> List.insert (v, S) acc | _ \<Rightarrow> acc) (concat (map atyps (term_typs t))) xs"

definition add_tfrees :: "pterm \<Rightarrow> (name \<times> psort) list \<Rightarrow> (name \<times> psort) list" where
  "add_tfrees t xs =
    fold (\<lambda>T acc. case T of TFree a S \<Rightarrow> List.insert (a, S) acc | _ \<Rightarrow> acc) (concat (map atyps (term_typs t))) xs"

definition add_tfree_names :: "pterm \<Rightarrow> name list \<Rightarrow> name list" where
  "add_tfree_names t xs =
    fold (\<lambda>T acc. case T of TFree a _ \<Rightarrow> List.insert a acc | _ \<Rightarrow> acc) (concat (map atyps (term_typs t))) xs"

definition tvar_names :: "pterm \<Rightarrow> name list" where
  "tvar_names t = concat (map (\<lambda>T. case T of TVar (a, _) _ \<Rightarrow> [a] | _ \<Rightarrow> []) (concat (map atyps (term_typs t))))"

text \<open>\<open>Term.map_types\<close> and \<open>Term.map_atyps\<close>.\<close>

fun map_atyps :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "map_atyps f (Type a Ts) = Type a (map (map_atyps f) Ts)"
| "map_atyps f T = f T"

fun map_types :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "map_types f (Const c T) = Const c (f T)"
| "map_types f (Free x T) = Free x (f T)"
| "map_types f (Var xi T) = Var xi (f T)"
| "map_types f (Bound i) = Bound i"
| "map_types f (Abs x T b) = Abs x (f T) (map_types f b)"
| "map_types f (t $ u) = map_types f t $ map_types f u"


text \<open>Association lists keyed by variables and lists of typed names (the equality of types is
  that of ML, which the generated code uses without equality dictionaries).\<close>

fun lookup_var :: "((indexname \<times> ptyp) \<times> 'a) list \<Rightarrow> indexname \<times> ptyp \<Rightarrow> 'a option" where
  "lookup_var [] v = None"
| "lookup_var (((xi, T), x) # xs) v = (if xi = fst v \<and> T = snd v then Some x else lookup_var xs v)"

fun lookup_zvar :: "((indexname \<times> ztyp) \<times> 'a) list \<Rightarrow> indexname \<times> ztyp \<Rightarrow> 'a option" where
  "lookup_zvar [] v = None"
| "lookup_zvar (((xi, T), x) # xs) v = (if xi = fst v \<and> T = snd v then Some x else lookup_zvar xs v)"

definition insert_free :: "name \<times> ptyp \<Rightarrow> (name \<times> ptyp) list \<Rightarrow> (name \<times> ptyp) list" where
  "insert_free v xs = (if (\<exists>(y, U)\<in>set xs. y = fst v \<and> U = snd v) then xs else v # xs)"


subsection \<open>Generalization\<close>

text \<open>\<open>Name.clean_index\<close>: trailing underscores of internal names become index increments.\<close>

function clean_index_aux :: "char list \<Rightarrow> integer \<Rightarrow> char list \<times> integer" where
  "clean_index_aux xs i =
    (if xs \<noteq> [] \<and> last xs = CHR ''_'' then clean_index_aux (butlast xs) (i + 1) else (xs, i))"
  by auto
termination by (relation "measure (\<lambda>(xs, _). length xs)") auto

definition clean_index :: "name \<times> integer \<Rightarrow> indexname" where
  "clean_index xi =
    (case clean_index_aux (String.explode (fst xi)) (snd xi) of (ys, j) \<Rightarrow> (String.implode ys, j))"

text \<open>\<open>Term_Subst.generalizeT\<close> and \<open>Term_Subst.generalize\<close>.\<close>

fun generalizeT :: "name list \<Rightarrow> integer \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "generalizeT tfrees gi (Type a Ts) = Type a (map (generalizeT tfrees gi) Ts)"
| "generalizeT tfrees gi (TFree a S) = (if a \<in> set tfrees then TVar (a, gi) S else TFree a S)"
| "generalizeT tfrees gi T = T"

fun generalize_term :: "name list \<Rightarrow> name list \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "generalize_term tfrees frees gi (Free x T) =
    (if x \<in> set frees then Var (clean_index (x, gi)) (generalizeT tfrees gi T)
     else Free x (generalizeT tfrees gi T))"
| "generalize_term tfrees frees gi (Var xi T) = Var xi (generalizeT tfrees gi T)"
| "generalize_term tfrees frees gi (Const c T) = Const c (generalizeT tfrees gi T)"
| "generalize_term tfrees frees gi (Bound i) = Bound i"
| "generalize_term tfrees frees gi (Abs x T t) = Abs x (generalizeT tfrees gi T) (generalize_term tfrees frees gi t)"
| "generalize_term tfrees frees gi (t $ u) = generalize_term tfrees frees gi t $ generalize_term tfrees frees gi u"

text \<open>The test of \<open>Thm.generalize\<close> for hypotheses with generalized variables.\<close>

fun has_tfree :: "name list \<Rightarrow> ptyp \<Rightarrow> bool" where
  "has_tfree tfrees (TFree a _) = (a \<in> set tfrees)"
| "has_tfree tfrees (Type _ Ts) = (\<exists>T\<in>set Ts. has_tfree tfrees T)"
| "has_tfree tfrees _ = False"

fun bad_term :: "name list \<Rightarrow> name list \<Rightarrow> pterm \<Rightarrow> bool" where
  "bad_term tfrees frees (Free x T) = (has_tfree tfrees T \<or> x \<in> set frees)"
| "bad_term tfrees frees (Var _ T) = has_tfree tfrees T"
| "bad_term tfrees frees (Const _ T) = has_tfree tfrees T"
| "bad_term tfrees frees (Abs _ T t) = (has_tfree tfrees T \<or> bad_term tfrees frees t)"
| "bad_term tfrees frees (t $ u) = (bad_term tfrees frees t \<or> bad_term tfrees frees u)"
| "bad_term tfrees frees (Bound _) = False"

text \<open>\<open>Thm.generalize (tfrees, frees) gi\<close>, with the hypotheses of the theorem.\<close>

definition generalize :: "name list \<Rightarrow> name list \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "generalize tfrees frees gi hyps th =
    (if tfrees = [] \<and> frees = [] then returnW th
     else if gi \<le> th_maxidx th then raiseW (THM (STR ''generalize: bad index'') gi State)
     else if (\<exists>h\<in>set hyps. bad_term tfrees frees h) then
       raiseW (THM (STR ''generalize: variable free in assumptions'') 0 State)
     else
       (let gen = generalize_term tfrees frees gi;
         P = gen (th_prop th);
         tps = map (\<lambda>(t, u). (gen t, gen u)) (th_tpairs th)
        in returnW (mk_rep (maxidx_tpairs tps (maxidx_of_term P)) tps P)))"

text \<open>\<open>Proofterm.generalize_proof\<close>.\<close>

definition generalize_proof :: "name list \<Rightarrow> name list \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf" where
  "generalize_proof tfrees frees gi prop prf =
    (let gen =
      (if frees = [] then []
       else fold (\<lambda>a acc. case a of Free x T \<Rightarrow> if x \<in> set frees then insert_free (x, T) acc else acc | _ \<Rightarrow> acc)
         (aterms (generalize_term tfrees [] gi prop)) []);
      p1 = map_proof_terms (generalize_term tfrees [] gi) (generalizeT tfrees gi) prf;
      p2 = fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) gen p1
     in foldr (\<lambda>(x, T) p. p %> Var (clean_index (x, gi)) T) gen p2)"

text \<open>
  The classic proof of \<^const>\<open>generalize\<close>, with the fix of
  \<open>patches/12-thm-generalize-tpairs.patch\<close>: the free variables that occur in the flex-flex pairs
  are substituted in the proof instead of abstracted (\<open>Thm.generalize\<close> passes only the
  proposition to \<open>Proofterm.generalize_proof\<close>, which abstracts the variables of the proposition
  and keeps those of the pairs fixed).
\<close>

definition has_free :: "name \<Rightarrow> pterm \<Rightarrow> bool" where
  "has_free x t = (\<exists>a\<in>set (aterms t). case a of Free y _ \<Rightarrow> y = x | _ \<Rightarrow> False)"

definition generalize_thm_proof :: "name list \<Rightarrow> name list \<Rightarrow> integer \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow>
    prf \<Rightarrow> prf" where
  "generalize_thm_proof tfrees frees gi tpairs prop prf =
    (let tf = filter (\<lambda>x. \<exists>(t, u)\<in>set tpairs. has_free x t \<or> has_free x u) frees;
      p = generalize_proof tfrees (filter (\<lambda>x. x \<notin> set tf) frees) gi prop prf
     in if tf = [] then p else map_proof_terms (generalize_term [] tf gi) (\<lambda>T. T) p)"

text \<open>\<open>ZTerm.generalize_proof\<close>: free variables become schematic with index \<open>gi\<close>. Fix
  (\<open>zterm-generalize-clean\<close>): their names are cleaned as in the theorem (\<^const>\<open>generalize_term\<close>);
  Isabelle2026 keeps the internal names, and the tight proof then proves another proposition.\<close>

definition zgeneralize_proof :: "name list \<Rightarrow> name list \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zgeneralize_proof tfrees frees gi prf =
    (let typ = zsubst_type (\<lambda>((a, i), S). if i = -1 \<and> a \<in> set tfrees then Some (ZTVar (a, gi) S) else None);
      var = (\<lambda>((x, i), T). if i = -1 \<and> x \<in> set frees then Some (ZVar (clean_index (x, gi)) T) else None)
     in map_zproof typ (\<lambda>t. return (zsubst_term typ var t)) prf)"


subsection \<open>Instantiation\<close>

type_synonym instT = "((indexname \<times> psort) \<times> ptyp) list"
type_synonym inst = "((indexname \<times> ptyp) \<times> pterm) list"
type_synonym instT_m = "((indexname \<times> psort) \<times> ptyp \<times> integer) list"
type_synonym inst_m = "((indexname \<times> ptyp) \<times> pterm \<times> integer) list"

text \<open>The certification of the instantiations of \<open>Thm.instantiate\<close> (\<open>make_instT\<close>, \<open>make_inst\<close>
  of \<open>prep_insts\<close>), in the order of the tables.\<close>

fun check_instT :: "algebra \<Rightarrow> instT_m \<Rightarrow> unit T" where
  "check_instT alg [] = returnW ()"
| "check_instT alg ((((a, i), S), (U, _)) # xs) = do {
    ok \<leftarrow> liftMT (of_sort alg U S);
    if ok then check_instT alg xs else raiseW (NOT_OF_SORT U S)}"

fun check_inst :: "((indexname \<times> ptyp) \<times> pterm \<times> ptyp \<times> integer) list \<Rightarrow> unit T" where
  "check_inst [] = returnW ()"
| "check_inst (((v, T), (u, U, _)) # xs) = (if T = U then check_inst xs else raiseW (INST_CONFLICT (v, T) u U))"

text \<open>
  \<open>Term_Subst.instantiate_maxidx\<close>: types before terms; the maximal index is that of the
  variables kept and of the instances of those replaced (the instances of variables are looked
  up with their instantiated types).
\<close>

fun instT_m :: "instT_m \<Rightarrow> ptyp \<Rightarrow> integer \<Rightarrow> ptyp \<times> integer"
  and instTs_m :: "instT_m \<Rightarrow> ptyp list \<Rightarrow> integer \<Rightarrow> ptyp list \<times> integer" where
  "instT_m tab (Type a Ts) m = (case instTs_m tab Ts m of (Ts', m') \<Rightarrow> (Type a Ts', m'))"
| "instT_m tab (TVar (a, i) S) m =
    (case map_of tab ((a, i), S) of Some (T', j) \<Rightarrow> (T', max m j) | None \<Rightarrow> (TVar (a, i) S, max m i))"
| "instT_m tab (TFree a S) m = (TFree a S, m)"
| "instTs_m tab [] m = ([], m)"
| "instTs_m tab (T # Ts) m =
    (case instT_m tab T m of (T', m1) \<Rightarrow> case instTs_m tab Ts m1 of (Ts', m2) \<Rightarrow> (T' # Ts', m2))"

fun inst_m :: "instT_m \<Rightarrow> inst_m \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> pterm \<times> integer" where
  "inst_m tT tt (Const c T) m = (case instT_m tT T m of (T', m') \<Rightarrow> (Const c T', m'))"
| "inst_m tT tt (Free x T) m = (case instT_m tT T m of (T', m') \<Rightarrow> (Free x T', m'))"
| "inst_m tT tt (Var (x, i) T) m =
    (case instT_m tT T m of (T', m1) \<Rightarrow>
      case lookup_var tt ((x, i), T') of
        Some (t', j) \<Rightarrow> (t', max m1 j)
      | None \<Rightarrow> (Var (x, i) T', max m1 i))"
| "inst_m tT tt (Bound i) m = (Bound i, m)"
| "inst_m tT tt (Abs x T b) m =
    (case instT_m tT T m of (T', m1) \<Rightarrow> case inst_m tT tt b m1 of (b', m2) \<Rightarrow> (Abs x T' b', m2))"
| "inst_m tT tt (t $ u) m =
    (case inst_m tT tt t m of (t', m1) \<Rightarrow> case inst_m tT tt u m1 of (u', m2) \<Rightarrow> (t' $ u', m2))"

text \<open>
  \<open>Term_Subst.instantiate_beta_maxidx\<close>: as \<^const>\<open>inst_m\<close>, but an instance of the head
  variable of an application that is an abstraction is applied to the instantiated arguments
  (\<open>Term.betapplys\<close>). \<open>inst_beta_spine\<close> instantiates the head of the spine of an application
  with its arguments already instantiated.
\<close>

fun betapplys :: "pterm \<Rightarrow> pterm list \<Rightarrow> pterm" where
  "betapplys t [] = t"
| "betapplys t (u # us) = betapplys (betapply t u) us"

function inst_beta_m :: "instT_m \<Rightarrow> inst_m \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> pterm \<times> integer"
  and inst_beta_spine :: "instT_m \<Rightarrow> inst_m \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> pterm \<times> integer" where
  "inst_beta_m tT tt (Const c T) m = (case instT_m tT T m of (T', m') \<Rightarrow> (Const c T', m'))"
| "inst_beta_m tT tt (Free x T) m = (case instT_m tT T m of (T', m') \<Rightarrow> (Free x T', m'))"
| "inst_beta_m tT tt (Var xi T) m = inst_beta_spine tT tt (Var xi T) [] m"
| "inst_beta_m tT tt (Bound i) m = (Bound i, m)"
| "inst_beta_m tT tt (Abs x T b) m =
    (case instT_m tT T m of (T', m1) \<Rightarrow> case inst_beta_m tT tt b m1 of (b', m2) \<Rightarrow> (Abs x T' b', m2))"
| "inst_beta_m tT tt (t $ u) m =
    (case inst_beta_m tT tt u m of (u', m1) \<Rightarrow> inst_beta_spine tT tt t [u'] m1)"
| "inst_beta_spine tT tt (t $ u) args m =
    (case inst_beta_m tT tt u m of (u', m1) \<Rightarrow> inst_beta_spine tT tt t (u' # args) m1)"
| "inst_beta_spine tT tt (Var (x, i) T) args m =
    (case instT_m tT T m of (T', m1) \<Rightarrow>
      case lookup_var tt ((x, i), T') of
        Some (t', j) \<Rightarrow> (if is_Abs t' then betapplys t' args else list_comb t' args, max m1 j)
      | None \<Rightarrow> (list_comb (Var (x, i) T') args, max m1 i))"
| "inst_beta_spine tT tt (Const c T) args m =
    (case instT_m tT T m of (T', m1) \<Rightarrow> (list_comb (Const c T') args, m1))"
| "inst_beta_spine tT tt (Free x T) args m =
    (case instT_m tT T m of (T', m1) \<Rightarrow> (list_comb (Free x T') args, m1))"
| "inst_beta_spine tT tt (Bound i) args m = (list_comb (Bound i) args, m)"
| "inst_beta_spine tT tt (Abs x T b) args m =
    (case instT_m tT T m of (T', m1) \<Rightarrow> case inst_beta_m tT tt b m1 of (b', m2) \<Rightarrow>
      (list_comb (Abs x T' b') args, m2))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>x. case x of Inl (_, _, t, _) \<Rightarrow> 2 * size t + 1 | Inr (_, _, t, _, _) \<Rightarrow> 2 * size t)")
    auto

text \<open>
  \<open>Thm.instantiate\<close> (\<open>beta = False\<close>) and \<open>Thm.instantiate_beta\<close> (\<open>beta = True\<close>): the
  instantiations with the maximal indices of their certified types and terms.
\<close>

definition instantiate :: "algebra \<Rightarrow> bool \<Rightarrow> instT_m \<Rightarrow> ((indexname \<times> ptyp) \<times> pterm \<times> ptyp \<times> integer) list \<Rightarrow>
    thm_rep \<Rightarrow> thm_rep T" where
  "instantiate alg beta instT insts th =
    (if instT = [] \<and> insts = [] then returnW th
     else do {
       check_instT alg instT;
       check_inst insts;
       let inst = map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts;
       let subst = (if beta then inst_beta_m instT inst else inst_m instT inst);
       (case subst (th_prop th) (-1) of
         (P, m1) \<Rightarrow>
           (case fold (\<lambda>(t, u) (acc, i). case subst t i of (t', i1) \<Rightarrow> case subst u i1 of (u', i2) \<Rightarrow>
               (acc @ [(t', u')], i2)) (th_tpairs th) ([], m1) of
             (tps, m) \<Rightarrow> returnW (mk_rep m tps P)))})"

text \<open>\<open>Proofterm.instantiate\<close> (instances without types, \<open>Proofterm.remove_types\<close>) and
  \<open>ZTerm.instantiate_proof\<close>.\<close>

definition instantiate_proof :: "instT \<Rightarrow> inst \<Rightarrow> prf \<Rightarrow> prf" where
  "instantiate_proof instT inst prf =
    (let tT = map (\<lambda>(v, T). (v, (T, -1))) instT;
      tt = map (\<lambda>(v, t). (v, (remove_types t, -1))) inst
     in map_proof_terms (\<lambda>t. fst (inst_m tT tt t (-1))) (\<lambda>T. fst (instT_m tT T (-1))) prf)"

definition zinstantiate_proof :: "ztypargs \<Rightarrow> instT \<Rightarrow> inst \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zinstantiate_proof ta instT inst prf = do {
    zinst \<leftarrow> mapM (\<lambda>((v, T), t). do {t' \<leftarrow> zterm_of ta t; return ((v, ztyp_of T), t')}) inst;
    let typ = zsubst_type (map_of (map (\<lambda>(v, T). (v, ztyp_of T)) instT));
    map_zproof typ (\<lambda>t. return (zsubst_term typ (lookup_zvar zinst) t)) prf}"


subsection \<open>Indices\<close>

text \<open>\<open>Thm.incr_indexes\<close>, \<open>Proofterm.incr_indexes\<close> and \<open>ZTerm.incr_indexes_proof\<close>.\<close>

definition incr_indexes_thm :: "integer \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "incr_indexes_thm i th =
    (if i < 0 then raiseW (THM (STR ''negative increment'') 0 State)
     else if i = 0 then returnW th
     else returnW (mk_rep (th_maxidx th + i)
       (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) (th_tpairs th))
       (incr_indexes [] i (th_prop th))))"

definition incr_indexes_proof :: "integer \<Rightarrow> prf \<Rightarrow> prf" where
  "incr_indexes_proof i prf = map_proof_terms (incr_indexes [] i) (incr_tvar i) prf"

definition zincr_indexes_proof :: "integer \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zincr_indexes_proof inc prf =
    (let typ = zincr_tvar inc;
      var = (\<lambda>((x, i), T). if i \<ge> 0 then Some (ZVar (x, i + inc) T) else None)
     in map_zproof typ (\<lambda>t. return (zsubst_term typ var t)) prf)"


subsection \<open>Permutation of premises\<close>

text \<open>\<open>Term.strip_all_vars\<close>.\<close>

function strip_all_vars :: "pterm \<Rightarrow> binders" where
  "strip_all_vars t = (case dest_all t of Some (a, T, b) \<Rightarrow> (a, T) # strip_all_vars b | None \<Rightarrow> [])"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

text \<open>\<open>Thm.rotate_rule k i\<close>; also the data of the proofs: the other subgoals \<open>Bs\<close>, the
  rotated subgoal, its parameters and assumptions, and the rotation \<open>m\<close>.\<close>

definition rotate_data :: "integer \<Rightarrow> integer \<Rightarrow> thm_rep \<Rightarrow>
    (thm_rep \<times> pterm list \<times> pterm \<times> binders \<times> pterm list \<times> integer) T" where
  "rotate_data k i state = do {
    (tpairs, Bs, Bi, C) \<leftarrow> dest_state state i;
    let params = strip_all_vars Bi;
    let rest = strip_all_body Bi;
    let asms = strip_imp_prems rest;
    let concl = strip_imp_concl rest;
    let n = integer_of_nat (length asms);
    let m = (if k < 0 then n + k else k);
    Bi' \<leftarrow>
      (if 0 = m \<or> m = n then returnW Bi
       else if 0 < m \<and> m < n then
         returnW (list_forall params (list_implies (drop (nat_of_integer m) asms @ take (nat_of_integer m) asms) concl))
       else raiseW (THM (STR ''rotate_rule'') k State));
    returnW (mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C), Bs, Bi', params, asms, m)}"

definition rotate_rule :: "integer \<Rightarrow> integer \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "rotate_rule k i state = do {(th, _) \<leftarrow> rotate_data k i state; returnW th}"

definition mk_Abst :: "binders \<Rightarrow> prf \<Rightarrow> prf" where
  "mk_Abst params prf = foldr (\<lambda>(s, _) p. Abst s None p) params prf"

definition rotate_proof :: "pterm list \<Rightarrow> pterm \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "rotate_proof Bs Bi' params asms m prf =
    (let i = integer_of_nat (length asms); j = integer_of_nat (length Bs)
     in mk_AbsP (Bs @ [Bi']) (proof_combP prf (map PBound (downto j 1) @
       [mk_Abst params (mk_AbsP asms
         (proof_combP (proof_combt (PBound i) (map Bound (downto (integer_of_nat (length params) - 1) 0)))
           (map PBound (downto (i - m - 1) 0 @ downto (i - 1) (i - m)))))])))"

definition ZAbsts :: "(name \<times> ztyp) list \<Rightarrow> zproof \<Rightarrow> zproof" where
  "ZAbsts xs prf = foldr (\<lambda>(x, T) p. ZAbst x T p) xs prf"

definition zrotate_proof :: "ztypargs \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow>
    zproof \<Rightarrow> zproof Z" where
  "zrotate_proof ta Bs Bi' params asms m prf = do {
    let i = integer_of_nat (length asms);
    let j = integer_of_nat (length Bs);
    Bs' \<leftarrow> mapM (zterm_of ta) (Bs @ [Bi']);
    asms' \<leftarrow> mapM (zterm_of ta) asms;
    return (ZAbsps Bs' (ZAppps prf (map ZBoundp (downto j 1) @
      [ZAbsts (map (\<lambda>(a, T). (a, ztyp_of T)) params) (ZAbsps asms'
        (ZAppps (ZAppts (ZBoundp i) (map ZBound (downto (integer_of_nat (length params) - 1) 0)))
          (map ZBoundp (downto (i - m - 1) 0 @ downto (i - 1) (i - m)))))])))}"

text \<open>\<open>Thm.permute_prems j k\<close>; also the new premises and the rotation \<open>m\<close>. A bad \<open>j\<close>
  raises \<open>Subscript\<close> (from \<open>List.drop\<close>, outside the handler of \<open>List.take\<close>).\<close>

definition permute_data :: "integer \<Rightarrow> integer \<Rightarrow> thm_rep \<Rightarrow> (thm_rep \<times> pterm list \<times> integer) T" where
  "permute_data j k rl = do {
    let prems = strip_imp_prems (th_prop rl);
    let concl = strip_imp_concl (th_prop rl);
    (if j < 0 \<or> integer_of_nat (length prems) < j then raiseW (UExn (PExn Subscript))
     else do {
       let moved = drop (nat_of_integer j) prems;
       let fixed = take (nat_of_integer j) prems;
       let n_j = integer_of_nat (length moved);
       let m = (if k < 0 then n_j + k else k);
       (prems', P) \<leftarrow>
         (if 0 = m \<or> m = n_j then returnW (prems, th_prop rl)
          else if 0 < m \<and> m < n_j then
            (let prems' = fixed @ drop (nat_of_integer m) moved @ take (nat_of_integer m) moved
             in returnW (prems', list_implies prems' concl))
          else raiseW (THM (STR ''permute_prems: k'') k State));
       returnW (mk_rep (th_maxidx rl) (th_tpairs rl) P, prems', m)})}"

definition permute_prems :: "integer \<Rightarrow> integer \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "permute_prems j k rl = do {(th, _) \<leftarrow> permute_data j k rl; returnW th}"

definition permute_prems_proof :: "pterm list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "permute_prems_proof prems' j k prf =
    (let n = integer_of_nat (length prems')
     in mk_AbsP prems' (proof_combP prf (map PBound (downto (n - 1) (n - j) @ downto (k - 1) 0 @ downto (n - j - 1) k))))"

definition zpermute_prems_proof :: "ztypargs \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zpermute_prems_proof ta prems' j k prf = do {
    let n = integer_of_nat (length prems');
    Ps \<leftarrow> mapM (zterm_of ta) prems';
    return (ZAbsps Ps (ZAppps prf (map ZBoundp (downto (n - 1) (n - j) @ downto (k - 1) 0 @ downto (n - j - 1) k))))}"


subsection \<open>Type variables\<close>

text \<open>\<open>Logic.dest_equals\<close> and \<open>Thm.attach_tpairs\<close>.\<close>

definition dest_equals :: "pterm \<Rightarrow> (pterm \<times> pterm) M" where
  "dest_equals t = (case dest_eq_any t of Some tu \<Rightarrow> return tu | None \<Rightarrow> raise (Term_Error (STR ''dest_equals'') [t]))"

text \<open>
  \<open>Type.varify_global fixed t\<close>: the free type variables not fixed become schematic with
  index \<open>0\<close>, renamed apart from the schematic type variables of the term (\<open>vl\<close> is
  \<open>Name.variant_list\<close>).
\<close>

definition varify_global_names :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> (name \<times> psort) list \<Rightarrow> pterm \<Rightarrow>
    ((name \<times> psort) \<times> (indexname \<times> psort)) list" where
  "varify_global_names vl fixed t =
    (let xs = fold (\<lambda>T acc. case T of TFree a S \<Rightarrow> if (a, S) \<in> set fixed then acc else List.insert (a, S) acc | _ \<Rightarrow> acc)
           (concat (map atyps (term_typs t))) [];
      ys = vl (tvar_names t) (map fst xs)
     in map2 (\<lambda>(a, S) b. ((a, S), ((b, 0), S))) xs ys)"

definition varify_tfree :: "((name \<times> psort) \<times> (indexname \<times> psort)) list \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "varify_tfree names T =
    (case T of TFree a S \<Rightarrow> (case map_of names (a, S) of Some (v, S') \<Rightarrow> TVar v S' | None \<Rightarrow> T) | _ \<Rightarrow> T)"

text \<open>\<open>Thm.varifyT_global' fixed\<close>, with the hypotheses of the theorem.\<close>

definition varifyT_global :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> (name \<times> psort) list \<Rightarrow> pterm list \<Rightarrow>
    thm_rep \<Rightarrow> (((name \<times> psort) \<times> (indexname \<times> psort)) list \<times> thm_rep) T" where
  "varifyT_global vl fixed hyps th = liftMT (do {
    let tfrees = fold add_tfrees hyps fixed;
    P1 \<leftarrow> full_prop_of (th_tpairs th) (th_prop th);
    let names = varify_global_names vl tfrees P1;
    let P2 = map_types (map_atyps (varify_tfree names)) P1;
    (ts, P3) \<leftarrow> strip_prems (integer_of_nat (length (th_tpairs th))) [] P2;
    tps \<leftarrow> mapM dest_equals ts;
    return (names, mk_rep (max 0 (th_maxidx th)) (rev tps) P3)})"

text \<open>\<open>Proofterm.varifyT_proof\<close> and \<open>ZTerm.varifyT_proof\<close>.\<close>

definition varifyT_proof :: "((name \<times> psort) \<times> (indexname \<times> psort)) list \<Rightarrow> prf \<Rightarrow> prf" where
  "varifyT_proof names prf =
    (if names = [] then prf
     else map_proof_terms (map_types (map_atyps (varify_tfree names))) (map_atyps (varify_tfree names)) prf)"

definition zvarifyT_proof :: "((name \<times> psort) \<times> (indexname \<times> psort)) list \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zvarifyT_proof names prf =
    (if names = [] then return prf
     else
       (let typ = zsubst_type (\<lambda>((a, i), S). if i = -1 then map_option (\<lambda>(v, S'). ZTVar v S') (map_of names (a, S)) else None)
        in map_zproof typ (\<lambda>t. return (zsubst_term typ (\<lambda>_. None) t)) prf))"

text \<open>\<open>Library.string_of_indexname\<close>, with \<open>string_of_int\<close>.\<close>

fun digits :: "nat \<Rightarrow> char list" where
  "digits n = (if n < 10 then [char_of (48 + n)] else digits (n div 10) @ [char_of (48 + n mod 10)])"

definition string_of_int :: "integer \<Rightarrow> String.literal" where
  "string_of_int i =
    String.implode (if i < 0 then CHR ''~'' # digits (nat_of_integer (- i)) else digits (nat_of_integer i))"

definition string_of_indexname :: "indexname \<Rightarrow> String.literal" where
  "string_of_indexname xi = (if snd xi = 0 then fst xi else fst xi + STR ''_'' + string_of_int (snd xi))"

text \<open>\<open>Type.legacy_freezeT t\<close>: the new names of the schematic type variables.\<close>

definition legacy_freeze_names :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> pterm \<Rightarrow> (indexname \<times> name) list" where
  "legacy_freeze_names vl t =
    fst (foldr (\<lambda>ix (pairs, used). let v = hd (vl used [string_of_indexname ix]) in ((ix, v) # pairs, v # used))
      (map fst (add_tvars t [])) ([], add_tfree_names t []))"

definition freeze_tvar :: "(indexname \<times> name) list \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "freeze_tvar alist T = (case T of TVar ix S \<Rightarrow> (case map_of alist ix of Some a \<Rightarrow> TFree a S | None \<Rightarrow> T) | _ \<Rightarrow> T)"

text \<open>\<open>Thm.legacy_freezeT\<close>.\<close>

definition legacy_freezeT :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "legacy_freezeT vl th = liftMT (do {
    P1 \<leftarrow> full_prop_of (th_tpairs th) (th_prop th);
    let alist = legacy_freeze_names vl P1;
    let P2 = (if alist = [] then P1 else map_types (map_atyps (freeze_tvar alist)) P1);
    (ts, P3) \<leftarrow> strip_prems (integer_of_nat (length (th_tpairs th))) [] P2;
    tps \<leftarrow> mapM dest_equals ts;
    return (mk_rep (maxidx_of_term P2) (rev tps) P3)})"

text \<open>\<open>Proofterm.legacy_freezeT\<close> and \<open>ZTerm.legacy_freezeT_proof\<close>, with the proposition \<open>t\<close>
  (with flex-flex pairs) of the theorem.\<close>

definition legacy_freezeT_proof :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf" where
  "legacy_freezeT_proof vl t prf =
    (let alist = legacy_freeze_names vl t
     in if alist = [] then prf
        else map_proof_terms (map_types (map_atyps (freeze_tvar alist))) (map_atyps (freeze_tvar alist)) prf)"

definition zlegacy_freezeT_proof :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zlegacy_freezeT_proof vl t prf =
    (let alist = legacy_freeze_names vl t
     in if alist = [] then return prf
        else
          (let typ = zsubst_type (\<lambda>(ix, S). map_option (\<lambda>a. ZTVar (a, -1) S) (map_of alist ix))
           in map_zproof typ (\<lambda>t. return (zsubst_term typ (\<lambda>_. None) t)) prf))"

text \<open>\<open>Thm.of_class (T, c)\<close>, with the certified class \<open>c\<close>: \<open>OFCLASS(T, c_class)\<close>.\<close>

definition of_class :: "algebra \<Rightarrow> ptyp \<Rightarrow> pclass \<Rightarrow> thm_rep T" where
  "of_class alg T c = do {
    let P = mk_of_class T c;
    ok \<leftarrow> liftMT (of_sort alg T [c]);
    if ok then returnW (mk_rep (maxidx_of_term P) [] P) else raiseW (NOT_OF_SORT T [c])}"

end
