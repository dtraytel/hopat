section \<open>Proof terms of lifting and composition\<close>

theory Pure_Proofterm
  imports Pure_Biresolution
begin

text \<open>
  A model of the proof terms of \<^file>\<open>~~/src/Pure/proofterm.ML\<close> and of the functions that
  \<open>Thm.lift_rule\<close> and \<open>Thm.bicompose_aux\<close> apply to the proofs of their arguments:
  \<open>Proofterm.lift_proof\<close>, \<open>Proofterm.bicompose_proof\<close> (with \<open>mk_asm_prf\<close>,
  \<open>flatten_params_proof\<close> and \<open>norm_proof_remove_types\<close>) and \<open>Proofterm.map_proof_terms\<close>,
  which the wrapper uses to rename bound variables in the proof of the rule.

  The data of theorem boxes (\<open>thm_header\<close> without the proposition and the type arguments,
  and \<open>thm_body\<close>) is opaque. The constructors are those of \<open>Proofterm.proof\<close>, so that the
  generated code operates on Pure's proofs directly.
\<close>


subsection \<open>Proofs\<close>

typedecl header_info  \<comment> \<open>serial, position, theory and theorem name of a \<open>thm_header\<close>\<close>
typedecl thm_body

datatype thm_header = Thm_Header (hd_info: header_info) (hd_prop: pterm) (hd_types: "ptyp list option")

definition hd_set_types :: "thm_header \<Rightarrow> ptyp list option \<Rightarrow> thm_header" where
  "hd_set_types h Ts = Thm_Header (hd_info h) (hd_prop h) Ts"

lemma hd_set_types_simps[simp]:
  "hd_prop (hd_set_types h Ts) = hd_prop h" "hd_types (hd_set_types h Ts) = Ts"
  "hd_info (hd_set_types h Ts) = hd_info h"
  by (simp_all add: hd_set_types_def)

datatype "prf" =
  MinProof
| PBound integer
| Abst name "ptyp option" "prf"
| AbsP name "pterm option" "prf"
| PAppt "prf" "pterm option"  \<comment> \<open>\<open>p % t\<close>\<close>
| PAppp "prf" "prf"  \<comment> \<open>\<open>p %% q\<close>\<close>
| Hyp pterm
| PAxm name pterm "ptyp list option"
| PClass ptyp pclass
| Oracle name pterm "ptyp list option"
| PThm "thm_header \<times> thm_body"

text \<open>\<open>proof_combt\<close>, \<open>proof_combP\<close>, \<open>mk_AbsP\<close> (which only uses the length of its list).\<close>

definition proof_combt :: "prf \<Rightarrow> pterm list \<Rightarrow> prf" where
  "proof_combt p ts = foldl (\<lambda>p t. PAppt p (Some t)) p ts"

definition proof_combP :: "prf \<Rightarrow> prf list \<Rightarrow> prf" where
  "proof_combP p qs = foldl PAppp p qs"

definition mk_AbsP :: "'a list \<Rightarrow> prf \<Rightarrow> prf" where
  "mk_AbsP xs p = foldr (\<lambda>_ p. AbsP (STR ''H'') None p) xs p"

text \<open>\<open>a downto b\<close>\<close>

function downto :: "integer \<Rightarrow> integer \<Rightarrow> integer list" where
  "downto a b = (if a < b then [] else a # downto (a - 1) b)"
  by auto
termination by (relation "measure (\<lambda>(a, b). nat (int_of_integer (a - b) + 1))")
  (auto simp: less_integer.rep_eq)

declare downto.simps[simp del]

text \<open>
  \<open>Proofterm.map_proof_terms f g\<close>: \<open>f\<close> on the term arguments and assumptions, \<open>g\<close> on the
  types of the parameters, the type arguments of axioms, oracles and theorems (if present)
  and the types of class proofs.
\<close>

fun map_proof_terms :: "(pterm \<Rightarrow> pterm) \<Rightarrow> (ptyp \<Rightarrow> ptyp) \<Rightarrow> prf \<Rightarrow> prf" where
  "map_proof_terms f g (Abst a T p) = Abst a (map_option g T) (map_proof_terms f g p)"
| "map_proof_terms f g (AbsP a t p) = AbsP a (map_option f t) (map_proof_terms f g p)"
| "map_proof_terms f g (PAppt p t) = PAppt (map_proof_terms f g p) (map_option f t)"
| "map_proof_terms f g (PAppp p q) = PAppp (map_proof_terms f g p) (map_proof_terms f g q)"
| "map_proof_terms f g (PAxm a A Ts) = PAxm a A (map_option (map g) Ts)"
| "map_proof_terms f g (PClass T c) = PClass (g T) c"
| "map_proof_terms f g (Oracle a A Ts) = Oracle a A (map_option (map g) Ts)"
| "map_proof_terms f g (PThm (h, b)) = PThm (hd_set_types h (map_option (map g) (hd_types h)), b)"
| "map_proof_terms f g p = p"


subsection \<open>Lifting\<close>

text \<open>
  \<open>Proofterm.lift_proof gprop inc prems prf\<close>: the proof of the rule lifted over the
  subgoal \<open>gprop\<close>. Inside the parameters \<open>Ts\<close> of the subgoal, at abstraction level \<open>lev\<close>,
  the indices of schematic (type) variables are incremented by \<open>inc\<close> and the variables are
  lifted over \<open>Ts\<close> (\<open>Logic.incr_indexes_operation\<close>); hypotheses and the propositions of
  axioms, oracles and theorems are unchanged.
\<close>

fun lift_prf :: "integer \<Rightarrow> ptyp list \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "lift_prf inc Ts lev (Abst a T p) = Abst a (map_option (incr_tvar inc) T) (lift_prf inc Ts (lev + 1) p)"
| "lift_prf inc Ts lev (AbsP a t p) = AbsP a (map_option (incr_idx Ts inc lev) t) (lift_prf inc Ts lev p)"
| "lift_prf inc Ts lev (PAppt p t) = PAppt (lift_prf inc Ts lev p) (map_option (incr_idx Ts inc lev) t)"
| "lift_prf inc Ts lev (PAppp p q) = PAppp (lift_prf inc Ts lev p) (lift_prf inc Ts lev q)"
| "lift_prf inc Ts lev (PAxm a A Us) = PAxm a A (map_option (map (incr_tvar inc)) Us)"
| "lift_prf inc Ts lev (PClass T c) = PClass (incr_tvar inc T) c"
| "lift_prf inc Ts lev (Oracle a A Us) = Oracle a A (map_option (map (incr_tvar inc)) Us)"
| "lift_prf inc Ts lev (PThm (h, b)) =
    PThm (hd_set_types h (map_option (map (incr_tvar inc)) (hd_types h)), b)"
| "lift_prf inc Ts lev p = p"

definition mk_app :: "bool \<Rightarrow> integer \<times> integer \<times> prf \<Rightarrow> integer \<times> integer \<times> prf" where
  "mk_app b x = (case x of (i, j, p) \<Rightarrow>
    if b then (i - 1, j, PAppp p (PBound i)) else (i, j - 1, PAppt p (Some (Bound j))))"

fun lift_prems :: "integer \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> ptyp list \<Rightarrow> bool list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> prf" where
  "lift_prems inc k prf Ts bs i j (Const c U $ A $ B) =
    (if c = STR ''Pure.imp'' then AbsP (STR ''H'') None (lift_prems inc k prf Ts (True # bs) (i + 1) j B)
     else proof_combP (lift_prf inc (rev Ts) 0 prf)
       (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i)))"
| "lift_prems inc k prf Ts bs i j (Const c U $ Abs a T t) =
    (if c = STR ''Pure.all'' then Abst a None (lift_prems inc k prf (T # Ts) (False # bs) i (j + 1) t)
     else proof_combP (lift_prf inc (rev Ts) 0 prf)
       (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i)))"
| "lift_prems inc k prf Ts bs i j _ =
    proof_combP (lift_prf inc (rev Ts) 0 prf)
      (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"

definition lift_proof :: "pterm \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> prf \<Rightarrow> prf" where
  "lift_proof gprop inc prems prf =
    mk_AbsP prems (lift_prems inc (integer_of_nat (length prems)) prf [] [] 0 0 gprop)"


subsection \<open>Proofs by assumption and of flattened parameters\<close>

fun imp_prf :: "pterm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "imp_prf (Const c U $ A $ B) i m =
    (if m = 0 then PBound i
     else if c = STR ''Pure.imp'' then AbsP (STR ''H'') None (imp_prf B (i + 1) (m - 1))
     else PBound i)"
| "imp_prf _ i m = PBound i"

fun all_prf :: "integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> prf" where
  "all_prf i m (Const c U $ Abs a T t) =
    (if c = STR ''Pure.all'' then Abst a None (all_prf i m t) else imp_prf (Const c U $ Abs a T t) (- i) m)"
| "all_prf i m t = imp_prf t (- i) m"

text \<open>\<open>Proofterm.mk_asm_prf C i m\<close>\<close>

definition mk_asm_prf :: "pterm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "mk_asm_prf C i m = all_prf i m C"

text \<open>\<open>Proofterm.flatten_params_proof i j n (A, k)\<close>; \<open>remove (op =)\<close> removes all occurrences.\<close>

fun flatten_params_proof :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm \<times> integer \<Rightarrow> prf" where
  "flatten_params_proof i j n (Const c U $ A $ B, k) =
    (if c = STR ''Pure.imp'' then AbsP (STR ''H'') None (flatten_params_proof (i + 1) j n (B, k))
     else proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
       (map PBound (removeAll (i - n) (downto (i - 1) 0))))"
| "flatten_params_proof i j n (Const c U $ Abs a T t, k) =
    (if c = STR ''Pure.all'' then Abst a None (flatten_params_proof i (j + 1) n (t, k))
     else proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
       (map PBound (removeAll (i - n) (downto (i - 1) 0))))"
| "flatten_params_proof i j n (_, k) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
      (map PBound (removeAll (i - n) (downto (i - 1) 0)))"


subsection \<open>The monad of proof normalisation\<close>

text \<open>
  Normalisation of proofs may print warnings (\<open>type conflict in norm_proof\<close>), raise an
  exception or diverge. A warning is represented by the message of the exception \<open>TYPE\<close>
  that caused it; the wrapper prints it with the prefix \<open>type conflict in norm_proof:\<close>.
\<close>

type_synonym 'a P = "(String.literal list \<times> 'a res) option"

definition returnP :: "'a \<Rightarrow> 'a P" where
  "returnP x = Some ([], Ok x)"

definition raiseP :: "exn \<Rightarrow> 'a P" where
  "raiseP e = Some ([], Err e)"

definition warnP :: "String.literal \<Rightarrow> unit P" where
  "warnP s = Some ([s], Ok ())"

definition bindP :: "'a P \<Rightarrow> ('a \<Rightarrow> 'b P) \<Rightarrow> 'b P" where
  "bindP m f =
    (case m of
      None \<Rightarrow> None
    | Some (ws, Err e) \<Rightarrow> Some (ws, Err e)
    | Some (ws, Ok x) \<Rightarrow> map_option (\<lambda>(ws', r). (ws @ ws', r)) (f x))"

definition handleP :: "'a P \<Rightarrow> (exn \<Rightarrow> 'a P) \<Rightarrow> 'a P" where
  "handleP m h =
    (case m of
      Some (ws, Err e) \<Rightarrow> map_option (\<lambda>(ws', r). (ws @ ws', r)) (h e)
    | _ \<Rightarrow> m)"

definition liftMP :: "'a M \<Rightarrow> 'a P" where
  "liftMP m = map_option (\<lambda>r. ([], r)) m"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bindP

lemma bindP_simps[simp]:
  "bindP (returnP x) f = f x"
  "bindP (raiseP e) f = raiseP e"
  "bindP None f = None"
  by (auto simp: bindP_def returnP_def raiseP_def option.map_id split: option.splits)

lemma bindP_returnP[simp]: "bindP m returnP = m"
  by (auto simp: bindP_def returnP_def split: option.splits res.splits)

lemma handleP_simps[simp]:
  "handleP (returnP x) h = returnP x"
  "handleP (raiseP e) h = h e"
  "handleP None h = None"
  by (auto simp: handleP_def returnP_def raiseP_def option.map_id split: option.splits)

lemma liftMP_simps[simp]:
  "liftMP (return x) = returnP x"
  "liftMP (raise e) = raiseP e"
  "liftMP None = None"
  by (simp_all add: liftMP_def return_def raise_def returnP_def raiseP_def)

lemma bindP_cong[fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>x. (\<exists>ws. m' = Some (ws, Ok x)) \<Longrightarrow> f x = f' x) \<Longrightarrow> bindP m f = bindP m' f'"
  by (auto simp: bindP_def split: option.splits res.splits)

lemma bindP_code[code]:
  "bindP m f =
    (case m of
      None \<Rightarrow> None
    | Some (ws, Err e) \<Rightarrow> Some (ws, Err e)
    | Some (ws, Ok x) \<Rightarrow> (case ws of [] \<Rightarrow> f x | _ \<Rightarrow> map_option (\<lambda>(ws', r). (ws @ ws', r)) (f x)))"
  by (auto simp: bindP_def option.map_id split: option.splits res.splits list.splits)

fun mapP :: "('a \<Rightarrow> 'b P) \<Rightarrow> 'a list \<Rightarrow> 'b list P" where
  "mapP f [] = returnP []"
| "mapP f (x # xs) = do {y \<leftarrow> f x; ys \<leftarrow> mapP f xs; returnP (y # ys)}"

lemma mapP_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> mapP f xs = mapP g ys"
  by (induction ys arbitrary: xs) (auto intro!: bindP_cong)

definition map_optionP :: "('a \<Rightarrow> 'b P) \<Rightarrow> 'a option \<Rightarrow> 'b option P" where
  "map_optionP f x = (case x of None \<Rightarrow> returnP None | Some y \<Rightarrow> do {z \<leftarrow> f y; returnP (Some z)})"

lemma map_optionP_cong[fundef_cong]:
  "x = y \<Longrightarrow> (\<And>z. y = Some z \<Longrightarrow> f z = g z) \<Longrightarrow> map_optionP f x = map_optionP g y"
  by (auto simp: map_optionP_def split: option.splits)


subsection \<open>Normalisation of proofs\<close>

text \<open>
  On a type conflict (exception \<open>TYPE\<close>), \<open>norm_proof\<close> replaces the type variables and
  variables whose lookup in the environment raises an exception (\<open>Type.lookup\<close> with a
  different sort, \<open>Envir.lookup\<close> with an incompatible type) by \<open>'dummy\<close> and \<open>dummy\<close> and
  normalises again. The replacement is \<open>Term_Subst.instantiate\<close>, which looks up a variable
  with its instantiated type.
\<close>

fun typ_tvars :: "ptyp \<Rightarrow> (indexname \<times> psort) list" where
  "typ_tvars (Type a Ts) = concat (map typ_tvars Ts)"
| "typ_tvars (TFree a S) = []"
| "typ_tvars (TVar xi S) = [(xi, S)]"

fun term_types :: "pterm \<Rightarrow> ptyp list" where
  "term_types (Const c T) = [T]"
| "term_types (Free x T) = [T]"
| "term_types (Var xi T) = [T]"
| "term_types (Bound i) = []"
| "term_types (Abs x T t) = T # term_types t"
| "term_types (t $ u) = term_types t @ term_types u"

fun term_vars :: "pterm \<Rightarrow> (indexname \<times> ptyp) list" where
  "term_vars (Var xi T) = [(xi, T)]"
| "term_vars (Abs x T t) = term_vars t"
| "term_vars (t $ u) = term_vars t @ term_vars u"
| "term_vars _ = []"

definition tvar_conflict :: "tyenv \<Rightarrow> indexname \<times> psort \<Rightarrow> bool" where
  "tvar_conflict tye v = (case vt_lookup tye (fst v) of None \<Rightarrow> False | Some (S', U) \<Rightarrow> snd v \<noteq> S')"

lemma tvar_conflict_lookup: "tvar_conflict tye (xi, S) \<longleftrightarrow> (\<exists>e. type_lookup tye xi S = raise e)"
  by (auto simp: tvar_conflict_def type_lookup_def tvar_clash_def return_def raise_def split: option.splits)

text \<open>\<open>Term_Subst.instantiateT\<close>, \<open>Term_Subst.instantiate\<close>\<close>

fun inst_typ :: "((indexname \<times> psort) \<times> ptyp) list \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "inst_typ iT (Type a Ts) = Type a (map (inst_typ iT) Ts)"
| "inst_typ iT (TFree a S) = TFree a S"
| "inst_typ iT (TVar xi S) = (case map_of iT (xi, S) of Some T \<Rightarrow> T | None \<Rightarrow> TVar xi S)"

text \<open>
  Variables are compared componentwise, so that the generated code compares their types with
  ML's equality on \<open>typ\<close>.
\<close>

definition var_eq :: "indexname \<times> ptyp \<Rightarrow> indexname \<times> ptyp \<Rightarrow> bool" where
  "var_eq v w \<longleftrightarrow> fst v = fst w \<and> snd v = snd w"

lemma var_eq_iff[simp]: "var_eq v w \<longleftrightarrow> v = w"
  by (cases v; cases w) (simp add: var_eq_def)

fun lookup_var :: "((indexname \<times> ptyp) \<times> 'a) list \<Rightarrow> indexname \<times> ptyp \<Rightarrow> 'a option" where
  "lookup_var [] v = None"
| "lookup_var ((w, x) # xs) v = (if var_eq w v then Some x else lookup_var xs v)"

lemma lookup_var_map_of: "lookup_var xs v = map_of xs v"
  by (induction xs) auto

fun remdups_vars :: "(indexname \<times> ptyp) list \<Rightarrow> (indexname \<times> ptyp) list" where
  "remdups_vars [] = []"
| "remdups_vars (v # vs) = (if list_ex (var_eq v) vs then remdups_vars vs else v # remdups_vars vs)"

lemma remdups_vars_remdups: "remdups_vars vs = remdups vs"
  by (induction vs) (auto simp: list_ex_iff)

fun inst_term :: "((indexname \<times> psort) \<times> ptyp) list \<Rightarrow> ((indexname \<times> ptyp) \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "inst_term iT it (Const c T) = Const c (inst_typ iT T)"
| "inst_term iT it (Free x T) = Free x (inst_typ iT T)"
| "inst_term iT it (Var xi T) =
    (case lookup_var it (xi, inst_typ iT T) of Some t \<Rightarrow> t | None \<Rightarrow> Var xi (inst_typ iT T))"
| "inst_term iT it (Bound i) = Bound i"
| "inst_term iT it (Abs x T t) = Abs x (inst_typ iT T) (inst_term iT it t)"
| "inst_term iT it (t $ u) = inst_term iT it t $ inst_term iT it u"

definition dummy_tfree :: "psort \<Rightarrow> ptyp" where
  "dummy_tfree S = TFree (STR 0x27 + STR ''dummy'') S"

definition conflicting_tvars :: "tyenv \<Rightarrow> ptyp list \<Rightarrow> ((indexname \<times> psort) \<times> ptyp) list" where
  "conflicting_tvars tye Ts =
    map (\<lambda>v. (v, dummy_tfree (snd v))) (remdups (filter (tvar_conflict tye) (concat (map typ_tvars Ts))))"

text \<open>\<open>can (Envir.lookup env) v\<close>: the lookup terminates without an exception.\<close>

definition can_lookup :: "env \<Rightarrow> indexname \<times> ptyp \<Rightarrow> bool M" where
  "can_lookup env v =
    (case lookup env (fst v) (snd v) of None \<Rightarrow> None | Some (Ok _) \<Rightarrow> return True | Some (Err _) \<Rightarrow> return False)"

text \<open>The elements for which a test returns \<open>False\<close>, tested from left to right.\<close>

fun filter_outM :: "('a \<Rightarrow> bool M) \<Rightarrow> 'a list \<Rightarrow> 'a list M" where
  "filter_outM P [] = return []"
| "filter_outM P (x # xs) = do {b \<leftarrow> P x; ys \<leftarrow> filter_outM P xs; return (if b then ys else x # ys)}"

definition del_conflicting_tvars :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "del_conflicting_tvars tye T = inst_typ (conflicting_tvars tye [T]) T"

definition del_conflicting_vars :: "env \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "del_conflicting_vars env t = do {
    vs \<leftarrow> filter_outM (can_lookup env) (remdups_vars (term_vars t));
    return (inst_term (conflicting_tvars (tyenv env) (term_types t)) (map (\<lambda>v. (v, Free (STR ''dummy'') (snd v))) vs) t)}"

text \<open>
  \<open>Envir.norm_term_same\<close> raises \<open>Same.SAME\<close> if the term does not change: it has no
  \<open>\<beta>\<close>-redex, none of its variables is bound, and its types are normal. After a type
  conflict, \<open>norm_proof\<close> normalises the term without conflicts; if that raises \<open>SAME\<close>,
  the result is the original term.
\<close>

definition norm_same :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "norm_same env t t' \<longleftrightarrow> \<not> could_beta_contract t \<and> (\<forall>v\<in>set (term_vars t). vt_lookup (tenv env) (fst v) = None) \<and>
    t' = t"

definition norm_type_same :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> bool" where
  "norm_type_same tye T T' \<longleftrightarrow> (\<forall>v\<in>set (typ_tvars T). vt_lookup tye (fst v) = None) \<and> T' = T"

definition norm_term_P :: "env \<Rightarrow> pterm \<Rightarrow> pterm P" where
  "norm_term_P env t =
    handleP (liftMP (norm_term env t)) (\<lambda>e. case e of
      Type_Error s _ _ \<Rightarrow> do {
        warnP s;
        t' \<leftarrow> liftMP (del_conflicting_vars env t);
        t'' \<leftarrow> liftMP (norm_term env t');
        returnP (if norm_same env t' t'' then t else t'')}
    | _ \<Rightarrow> raiseP e)"

definition norm_type_P :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp P" where
  "norm_type_P tye T =
    handleP (liftMP (norm_type tye T)) (\<lambda>e. case e of
      Type_Error s _ _ \<Rightarrow> do {
        warnP s;
        let T' = del_conflicting_tvars tye T;
        T'' \<leftarrow> liftMP (norm_type tye T');
        returnP (if norm_type_same tye T' T'' then T else T'')}
    | _ \<Rightarrow> raiseP e)"

definition norm_types_P :: "tyenv \<Rightarrow> ptyp list \<Rightarrow> ptyp list P" where
  "norm_types_P tye Ts =
    handleP (liftMP (if vt_is_empty tye then return Ts else mapM (norm_type_aux tye) Ts)) (\<lambda>e. case e of
      Type_Error s _ _ \<Rightarrow> do {
        warnP s;
        let Ts' = map (del_conflicting_tvars tye) Ts;
        Ts'' \<leftarrow> liftMP (if vt_is_empty tye then return Ts' else mapM (norm_type_aux tye) Ts');
        returnP (if vt_is_empty tye \<or> list_all2 (norm_type_same tye) Ts' Ts'' then Ts else Ts'')}
    | _ \<Rightarrow> raiseP e)"

text \<open>\<open>Proofterm.norm_proof\<close>: the parameter types are normalised before the body, a proof
  before its argument.\<close>

fun norm_proof :: "env \<Rightarrow> prf \<Rightarrow> prf P" where
  "norm_proof env (Abst a T p) = do {
    T' \<leftarrow> map_optionP (norm_type_P (tyenv env)) T; p' \<leftarrow> norm_proof env p; returnP (Abst a T' p')}"
| "norm_proof env (AbsP a t p) = do {
    t' \<leftarrow> map_optionP (norm_term_P env) t; p' \<leftarrow> norm_proof env p; returnP (AbsP a t' p')}"
| "norm_proof env (PAppt p t) = do {
    p' \<leftarrow> norm_proof env p; t' \<leftarrow> map_optionP (norm_term_P env) t; returnP (PAppt p' t')}"
| "norm_proof env (PAppp p q) = do {
    p' \<leftarrow> norm_proof env p; q' \<leftarrow> norm_proof env q; returnP (PAppp p' q')}"
| "norm_proof env (PAxm a A Ts) = do {
    Ts' \<leftarrow> map_optionP (norm_types_P (tyenv env)) Ts; returnP (PAxm a A Ts')}"
| "norm_proof env (PClass T c) = do {T' \<leftarrow> norm_type_P (tyenv env) T; returnP (PClass T' c)}"
| "norm_proof env (Oracle a A Ts) = do {
    Ts' \<leftarrow> map_optionP (norm_types_P (tyenv env)) Ts; returnP (Oracle a A Ts')}"
| "norm_proof env (PThm (h, b)) = do {
    Ts' \<leftarrow> map_optionP (norm_types_P (tyenv env)) (hd_types h); returnP (PThm (hd_set_types h Ts', b))}"
| "norm_proof env p = returnP p"

text \<open>\<open>remove_types\<close>, \<open>remove_types_env\<close>: \<open>dummyT\<close> for the types of abstractions and
  constants, in the bindings of the term environment.\<close>

definition dummyT :: ptyp where
  "dummyT = Type (STR ''dummy'') []"

fun remove_types :: "pterm \<Rightarrow> pterm" where
  "remove_types (Abs s T t) = Abs s dummyT (remove_types t)"
| "remove_types (t $ u) = remove_types t $ remove_types u"
| "remove_types (Const s T) = Const s dummyT"
| "remove_types t = t"

lift_definition vt_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a vartab \<Rightarrow> 'b vartab" is "\<lambda>f m. map_option f \<circ> m"
  by (simp add: dom_def)

lemma vt_lookup_map[simp]: "vt_lookup (vt_map f t) k = map_option f (vt_lookup t k)"
  by transfer simp

definition remove_types_env :: "env \<Rightarrow> env" where
  "remove_types_env env = Envir (maxidx env) (vt_map (\<lambda>(T, t). (T, remove_types t)) (tenv env)) (tyenv env)"

definition norm_proof_remove_types :: "env \<Rightarrow> prf \<Rightarrow> prf P" where
  "norm_proof_remove_types env p = norm_proof (remove_types_env env) p"


subsection \<open>Composition\<close>

text \<open>
  \<open>Proofterm.bicompose_proof env smax flatten Bs As A oldAs n m rprf sprf\<close>: the proof of
  the result of the composition, from the proof \<open>rprf\<close> of the (lifted) rule and \<open>sprf\<close> of the
  proof state; \<open>Bs\<close> are the other subgoals, \<open>As\<close> the new subgoals (before flattening:
  \<open>oldAs\<close>), \<open>A\<close> the assumption of elim-resolution, which closes premise \<open>n\<close> of the rule.
  The terms of \<open>Bs @ As\<close> are normalised (which may raise an exception) although
  \<open>mk_AbsP\<close> only uses their number. With \<open>n > 0\<close>, \<open>A\<close> is present: the model raises
  \<open>Failure\<close> where \<open>the\<close> would raise \<open>Option\<close>.
\<close>

definition bicompose_core :: "env \<Rightarrow> bool \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> pterm option \<Rightarrow> pterm list \<Rightarrow>
    integer \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf P" where
  "bicompose_core env flatten Bs As A oldAs n m sprf p = do {
    Ns \<leftarrow> liftMP (mapM (norm_term env) (Bs @ As));
    let lb = integer_of_nat (length Bs);
    let la = integer_of_nat (length As);
    let q = proof_combP sprf (map PBound (downto (lb + la - 1) la));
    asm \<leftarrow> (if n > 0 then (case A of None \<Rightarrow> raiseP (Failure (STR ''Option'')) | Some C \<Rightarrow> returnP [mk_asm_prf C n m])
            else returnP []);
    ks \<leftarrow> liftMP (zip_eq oldAs (downto (la - 1) 0));
    returnP (mk_AbsP Ns (PAppp q
      (proof_combP p (asm @ map (if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x))) ks))))}"

definition bicompose_proof :: "env \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> pterm option \<Rightarrow>
    pterm list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf P" where
  "bicompose_proof env smax flatten Bs As A oldAs n m rprf sprf =
    (if env_is_empty env then bicompose_core env flatten Bs As A oldAs n m sprf rprf
     else if above env smax then do {
       rprf' \<leftarrow> norm_proof_remove_types env rprf;
       bicompose_core env flatten Bs As A oldAs n m sprf rprf'}
     else do {
       p \<leftarrow> bicompose_core env flatten Bs As A oldAs n m sprf rprf;
       norm_proof_remove_types env p})"

end
