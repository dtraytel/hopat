section \<open>Tight proof terms (\<open>ZTerm\<close>) of lifting and composition\<close>

theory Pure_ZTerm
  imports Pure_Proofterm
begin

text \<open>
  A model of the tight representation of types, terms and proofs of
  \<^file>\<open>~~/src/Pure/zterm.ML\<close> and of the functions that \<open>Thm.lift_rule\<close> and
  \<open>Thm.bicompose_aux\<close> apply to the tight proofs of their arguments: \<open>ZTerm.lift_proof\<close> and
  \<open>ZTerm.bicompose_proof\<close>, with the conversion of terms (\<open>ZTerm.zterm_cache\<close>), the
  normalisation with respect to an environment of the variables visible in the propositions of
  the theorems (\<open>norm_proof_cache\<close>), and \<open>\<beta>\<close>-normalisation of term arguments
  (\<open>beta_norm_prooft\<close>).

  The conversion of a term depends on the type arguments of its constants in the theory
  (\<open>Consts.typargs\<close>); it is a parameter (\<open>ztypargs\<close>), which may raise an exception
  (undeclared constants). The caches of \<open>zterm.ML\<close> are not modelled: they memoize functions.
\<close>


subsection \<open>Types, terms and proofs\<close>

datatype ztyp =
  ZTVar indexname psort  \<comment> \<open>free: index \<open>-1\<close>\<close>
| ZFun ztyp ztyp
| ZProp
| ZType0 name
| ZType1 name ztyp
| ZType name "ztyp list"

datatype zterm =
  ZVar indexname ztyp  \<comment> \<open>free: index \<open>-1\<close>\<close>
| ZBound integer
| ZConst0 name
| ZConst1 name ztyp
| ZConst name "ztyp list"
| ZAbs name ztyp zterm
| ZApp zterm zterm
| ZOfclass ztyp pclass

text \<open>The instantiations of proof constants: tables \<open>ZTVars\<close> and \<open>ZVars\<close>.\<close>

typedef 'a ztvtab = "{m :: indexname \<times> psort \<rightharpoonup> 'a. finite (dom m)}"
  by (intro exI[of _ Map.empty]) simp

typedef 'a zvtab = "{m :: indexname \<times> ztyp \<rightharpoonup> 'a. finite (dom m)}"
  by (intro exI[of _ Map.empty]) simp

setup_lifting type_definition_ztvtab
setup_lifting type_definition_zvtab

lift_definition zt_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ztvtab \<Rightarrow> 'b ztvtab" is "\<lambda>f m. map_option f \<circ> m"
  by (simp add: dom_def)

lift_definition zv_empty :: "'a zvtab" is Map.empty by simp
lift_definition zv_lookup :: "'a zvtab \<Rightarrow> indexname \<times> ztyp \<Rightarrow> 'a option" is "\<lambda>m k. m k" .
lift_definition zv_update :: "(indexname \<times> ztyp) \<times> 'a \<Rightarrow> 'a zvtab \<Rightarrow> 'a zvtab" is
  "\<lambda>(k, x) m. m(k \<mapsto> x)" by auto
lift_definition zv_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a zvtab \<Rightarrow> 'b zvtab" is "\<lambda>f m. map_option f \<circ> m"
  by (simp add: dom_def)

text \<open>\<open>ZVars.dest\<close>: the entries in the order of the keys of the table (left abstract).\<close>

definition zv_dest :: "'a zvtab \<Rightarrow> ((indexname \<times> ztyp) \<times> 'a) list" where
  "zv_dest t = (SOME xs. distinct (map fst xs) \<and> set xs = {(k, x). zv_lookup t k = Some x})"

typedecl zproof_name

type_synonym zproof_const = "(zproof_name \<times> zterm) \<times> (ztyp ztvtab \<times> zterm zvtab)"

datatype zproof =
  ZNop
| ZConstp zproof_const
| ZBoundp integer
| ZAbst name ztyp zproof
| ZAbsp name zterm zproof
| ZAppt zproof zterm
| ZAppp zproof zproof
| ZHyp zterm
| OFCLASSp ztyp pclass

definition ZFuns :: "ztyp list \<Rightarrow> ztyp \<Rightarrow> ztyp" where
  "ZFuns Ts T = foldr ZFun Ts T"

definition ZAbsps :: "zterm list \<Rightarrow> zproof \<Rightarrow> zproof" where
  "ZAbsps ts p = foldr (\<lambda>t p. ZAbsp (STR ''H'') t p) ts p"

definition ZAppts :: "zproof \<Rightarrow> zterm list \<Rightarrow> zproof" where
  "ZAppts p ts = foldl ZAppt p ts"

definition ZAppps :: "zproof \<Rightarrow> zproof list \<Rightarrow> zproof" where
  "ZAppps p qs = foldl ZAppp p qs"

fun zcombound :: "zterm \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> zterm" where
  "zcombound t n 0 = t"
| "zcombound t n (Suc k) = ZApp (zcombound t (n + 1) k) (ZBound n)"


subsection \<open>The monad\<close>

text \<open>
  Besides the exceptions of session \<open>Pure_Pattern\<close>, the tight proof functions may raise
  \<open>ZTerm.BAD_INST\<close> (when an instantiation of the types of the variables of a proof constant
  identifies two of them with different instances) and \<open>Option\<close> (\<open>the\<close>).
\<close>

datatype zexn = ZExn exn | BAD_INST "((indexname \<times> ztyp) \<times> zterm) list" | ZOption

datatype 'a zres = ZOk 'a | ZErr zexn

type_synonym 'a Z = "'a zres option"

definition returnZ :: "'a \<Rightarrow> 'a Z" where
  "returnZ x = Some (ZOk x)"

definition raiseZ :: "zexn \<Rightarrow> 'a Z" where
  "raiseZ e = Some (ZErr e)"

definition bindZ :: "'a Z \<Rightarrow> ('a \<Rightarrow> 'b Z) \<Rightarrow> 'b Z" where
  "bindZ m f = (case m of None \<Rightarrow> None | Some (ZErr e) \<Rightarrow> Some (ZErr e) | Some (ZOk x) \<Rightarrow> f x)"

definition liftMZ :: "'a M \<Rightarrow> 'a Z" where
  "liftMZ m = (case m of None \<Rightarrow> None | Some (Ok x) \<Rightarrow> Some (ZOk x) | Some (Err e) \<Rightarrow> Some (ZErr (ZExn e)))"

definition liftOZ :: "'a option \<Rightarrow> 'a Z" where
  "liftOZ m = map_option ZOk m"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bindZ

lemma bindZ_simps[simp]:
  "bindZ (returnZ x) f = f x" "bindZ (raiseZ e) f = raiseZ e" "bindZ None f = None"
  by (simp_all add: bindZ_def returnZ_def raiseZ_def)

lemma bindZ_returnZ[simp]: "bindZ m returnZ = m"
  by (auto simp: bindZ_def returnZ_def split: option.splits zres.splits)

lemma liftMZ_simps[simp]:
  "liftMZ (return x) = returnZ x" "liftMZ (raise e) = raiseZ (ZExn e)" "liftMZ None = None"
  by (simp_all add: liftMZ_def return_def raise_def returnZ_def raiseZ_def)

lemma bindZ_cong[fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>x. m' = Some (ZOk x) \<Longrightarrow> f x = f' x) \<Longrightarrow> bindZ m f = bindZ m' f'"
  by (auto simp: bindZ_def split: option.splits zres.splits)

lemma bindZ_mono[partial_function_mono]:
  assumes "mono_option B" "\<And>y. mono_option (\<lambda>f. C y f)"
  shows "mono_option (\<lambda>f. bindZ (B f) (\<lambda>y. C y f))"
proof -
  have "bindZ m g = Option.bind m (\<lambda>r. case r of ZOk y \<Rightarrow> g y | ZErr e \<Rightarrow> Some (ZErr e))" for m and g :: "'c \<Rightarrow> 'd Z"
    by (auto simp: bindZ_def split: option.splits zres.splits)
  then show ?thesis
    using assms by (simp only:) (rule bind_mono, simp, rename_tac r, case_tac r, simp_all add: option.const_mono)
qed

fun mapZ :: "('a \<Rightarrow> 'b Z) \<Rightarrow> 'a list \<Rightarrow> 'b list Z" where
  "mapZ f [] = returnZ []"
| "mapZ f (x # xs) = do {y \<leftarrow> f x; ys \<leftarrow> mapZ f xs; returnZ (y # ys)}"

lemma mapZ_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> mapZ f xs = mapZ g ys"
  by (induction ys arbitrary: xs) (auto intro!: bindZ_cong)

lemma mapZ_mono[partial_function_mono]:
  assumes "\<And>x. mono_option (\<lambda>f. C x f)"
  shows "mono_option (\<lambda>f. mapZ (\<lambda>x. C x f) xs)"
  by (induction xs) (simp_all add: option.const_mono bindZ_mono assms returnZ_def)


subsection \<open>Conversion of types and terms\<close>

text \<open>\<open>ZTerm.ztyp_of\<close>, \<open>ZTerm.typ_of\<close>\<close>

fun ztyp_of :: "ptyp \<Rightarrow> ztyp" where
  "ztyp_of (TFree a S) = ZTVar (a, -1) S"
| "ztyp_of (TVar v S) = ZTVar v S"
| "ztyp_of (Type c []) = (if c = STR ''prop'' then ZProp else ZType0 c)"
| "ztyp_of (Type c [T]) = ZType1 c (ztyp_of T)"
| "ztyp_of (Type c [T, U]) =
    (if c = STR ''fun'' then ZFun (ztyp_of T) (ztyp_of U) else ZType c [ztyp_of T, ztyp_of U])"
| "ztyp_of (Type c (T # U # V # Ts)) = ZType c (map ztyp_of (T # U # V # Ts))"

fun typ_of :: "ztyp \<Rightarrow> ptyp" where
  "typ_of (ZTVar v S) = (if snd v = -1 then TFree (fst v) S else TVar v S)"
| "typ_of (ZFun T U) = typ_of T \<rightarrow>\<^sub>T typ_of U"
| "typ_of ZProp = propT"
| "typ_of (ZType0 c) = Type c []"
| "typ_of (ZType1 c T) = Type c [typ_of T]"
| "typ_of (ZType c Ts) = Type c (map typ_of Ts)"

text \<open>\<open>Logic.match_of_class\<close> (with \<open>try\<close>): a proposition \<open>OFCLASS(T, c)\<close>.\<close>

definition class_suffix :: String.literal where
  "class_suffix = STR ''_class''"

definition match_of_class :: "pterm \<Rightarrow> (ptyp \<times> pclass) option" where
  "match_of_class t =
    (case t of
      Const c _ $ Const d (Type e [T]) \<Rightarrow>
        let s = String.explode class_suffix; cs = String.explode c in
        if d = STR ''Pure.type'' \<and> e = STR ''itself'' \<and> length s \<le> length cs \<and>
          drop (length cs - length s) cs = s
        then Some (T, String.implode (take (length cs - length s) cs))
        else None
    | _ \<Rightarrow> None)"

text \<open>\<open>Logic.mk_of_class\<close>\<close>

definition mk_of_class :: "ptyp \<Rightarrow> pclass \<Rightarrow> pterm" where
  "mk_of_class T c = Const (c + class_suffix) (Type STR ''itself'' [T] \<rightarrow>\<^sub>T Type STR ''prop'' []) $
    Const STR ''Pure.type'' (Type STR ''itself'' [T])"

text \<open>
  \<open>ZTerm.zterm_cache thy\<close>: the term conversion; constants with no, one or several type
  arguments (\<open>Consts.typargs\<close>) become \<open>ZConst0\<close>, \<open>ZConst1\<close>, \<open>ZConst\<close>; propositions
  \<open>OFCLASS(T, c)\<close> become \<open>ZOfclass\<close> (\<open>OFCLASS\<close>). Fix (\<open>zterm-ofclass\<close>):
  \<open>Logic.match_of_class\<close> only checks the name of the constant, so that Isabelle2026 also
  converts other terms \<open>c TYPE(T)\<close> with a constant \<open>c\<close> whose name ends with \<open>_class\<close>,
  and \<open>ZTerm.term_of\<close> changes the type of the constant (see session \<open>Unpatched_Examples\<close>);
  only proper class membership propositions are converted.
\<close>

type_synonym ztypargs = "name \<Rightarrow> ptyp \<Rightarrow> ptyp list M"

fun zterm_of :: "ztypargs \<Rightarrow> pterm \<Rightarrow> zterm Z" where
  "zterm_of ta (Free x T) = returnZ (ZVar (x, -1) (ztyp_of T))"
| "zterm_of ta (Var xi T) = returnZ (ZVar xi (ztyp_of T))"
| "zterm_of ta (Bound i) = returnZ (ZBound i)"
| "zterm_of ta (Const c T) = do {
    Ts \<leftarrow> liftMZ (ta c T);
    returnZ (case Ts of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Ts))}"
| "zterm_of ta (Abs a T b) = do {b' \<leftarrow> zterm_of ta b; returnZ (ZAbs a (ztyp_of T) b')}"
| "zterm_of ta (t $ u) =
    (case match_of_class (t $ u) of
      Some Tc \<Rightarrow>
        if t $ u = mk_of_class (fst Tc) (snd Tc) then returnZ (ZOfclass (ztyp_of (fst Tc)) (snd Tc))
        else do {t' \<leftarrow> zterm_of ta t; u' \<leftarrow> zterm_of ta u; returnZ (ZApp t' u')}
    | None \<Rightarrow> do {t' \<leftarrow> zterm_of ta t; u' \<leftarrow> zterm_of ta u; returnZ (ZApp t' u')})"


subsection \<open>Bound variables and \<open>\<beta>\<close>-normalisation\<close>

fun zincr_bv :: "integer \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zincr_bv inc lev (ZBound i) = (if i \<ge> lev then ZBound (i + inc) else ZBound i)"
| "zincr_bv inc lev (ZAbs a T t) = ZAbs a T (zincr_bv inc (lev + 1) t)"
| "zincr_bv inc lev (ZApp t u) = ZApp (zincr_bv inc lev t) (zincr_bv inc lev u)"
| "zincr_bv inc lev t = t"

definition zincr_boundvars :: "integer \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zincr_boundvars inc t = (if inc = 0 then t else zincr_bv inc 0 t)"

fun zsubst_bound :: "zterm \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zsubst_bound arg lev (ZBound i) =
    (if i < lev then ZBound i else if i = lev then zincr_boundvars lev arg else ZBound (i - 1))"
| "zsubst_bound arg lev (ZAbs a T t) = ZAbs a T (zsubst_bound arg (lev + 1) t)"
| "zsubst_bound arg lev (ZApp t u) = ZApp (zsubst_bound arg lev t) (zsubst_bound arg lev u)"
| "zsubst_bound arg lev t = t"

definition subst_term_bound :: "zterm \<Rightarrow> zterm \<Rightarrow> zterm" where
  "subst_term_bound arg body = zsubst_bound arg 0 body"

text \<open>\<open>subst_proof_bound\<close>: in the term arguments and assumptions, not in instantiations of
  constants or hypotheses.\<close>

fun zsubst_proof_bound :: "zterm \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof" where
  "zsubst_proof_bound arg lev (ZAbsp a t p) = ZAbsp a (zsubst_bound arg lev t) (zsubst_proof_bound arg lev p)"
| "zsubst_proof_bound arg lev (ZAbst a T p) = ZAbst a T (zsubst_proof_bound arg (lev + 1) p)"
| "zsubst_proof_bound arg lev (ZAppp p q) = ZAppp (zsubst_proof_bound arg lev p) (zsubst_proof_bound arg lev q)"
| "zsubst_proof_bound arg lev (ZAppt p t) = ZAppt (zsubst_proof_bound arg lev p) (zsubst_bound arg lev t)"
| "zsubst_proof_bound arg lev p = p"

definition subst_proof_bound :: "zterm \<Rightarrow> zproof \<Rightarrow> zproof" where
  "subst_proof_bound arg body = zsubst_proof_bound arg 0 body"

text \<open>\<open>beta_norm_term_same\<close>, \<open>beta_norm_prooft_same\<close>; they may diverge on untyped terms.
  Proof normalisation contracts the \<open>\<beta>\<close>-redexes of term arguments; it does not descend into
  abstractions over assumptions and applications to proofs.\<close>

partial_function (option) beta_norm_term :: "zterm \<Rightarrow> zterm option" where
  "beta_norm_term t =
    (case t of
      ZAbs a T b \<Rightarrow> Option.bind (beta_norm_term b) (\<lambda>b'. Some (ZAbs a T b'))
    | ZApp f u \<Rightarrow>
        (case f of
          ZAbs _ _ body \<Rightarrow> beta_norm_term (subst_term_bound u body)
        | _ \<Rightarrow> Option.bind (beta_norm_term f) (\<lambda>nf.
            case nf of
              ZAbs _ _ body \<Rightarrow> beta_norm_term (subst_term_bound u body)
            | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZApp nf nu))))
    | _ \<Rightarrow> Some t)"

partial_function (option) beta_norm_prooft :: "zproof \<Rightarrow> zproof option" where
  "beta_norm_prooft p =
    (case p of
      ZAbst a T q \<Rightarrow> Option.bind (beta_norm_prooft q) (\<lambda>q'. Some (ZAbst a T q'))
    | ZAppt f u \<Rightarrow>
        (case f of
          ZAbst _ _ body \<Rightarrow> beta_norm_prooft (subst_proof_bound u body)
        | _ \<Rightarrow> Option.bind (beta_norm_prooft f) (\<lambda>nf.
            case nf of
              ZAbst _ _ body \<Rightarrow> beta_norm_prooft (subst_proof_bound u body)
            | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZAppt nf nu))))
    | _ \<Rightarrow> Some p)"


subsection \<open>Instantiation\<close>

text \<open>\<open>aconv_zterm\<close>: equality up to the names of bound variables.\<close>

fun aconv_zterm :: "zterm \<Rightarrow> zterm \<Rightarrow> bool" where
  "aconv_zterm (ZApp t1 u1) (ZApp t2 u2) \<longleftrightarrow> aconv_zterm t1 t2 \<and> aconv_zterm u1 u2"
| "aconv_zterm (ZAbs _ T1 t1) (ZAbs _ T2 t2) \<longleftrightarrow> aconv_zterm t1 t2 \<and> T1 = T2"
| "aconv_zterm a1 a2 \<longleftrightarrow> a1 = a2"

text \<open>\<open>make_inst\<close>: the table of a list of instances, keeping the first of instances of
  the same variable that are \<open>\<alpha>\<close>-convertible (\<open>ZVars.insert (op aconv_zterm)\<close>).\<close>

fun zv_insert_list :: "((indexname \<times> ztyp) \<times> zterm) list \<Rightarrow> zterm zvtab \<Rightarrow> zterm zvtab option" where
  "zv_insert_list [] t = Some t"
| "zv_insert_list ((k, x) # xs) t =
    (case zv_lookup t k of
      None \<Rightarrow> zv_insert_list xs (zv_update (k, x) t)
    | Some y \<Rightarrow> if aconv_zterm y x then zv_insert_list xs t else None)"

definition make_inst :: "((indexname \<times> ztyp) \<times> zterm) list \<Rightarrow> zterm zvtab Z" where
  "make_inst xs = (case zv_insert_list xs zv_empty of Some t \<Rightarrow> returnZ t | None \<Rightarrow> raiseZ (BAD_INST xs))"

text \<open>
  \<open>map_insts_same typ term\<close>: the types of the type instantiation, the instances and the types
  of the variables of a proof constant. If the types of the variables change, the table of
  instances is rebuilt (in the order of its keys), which raises \<open>BAD_INST\<close> if two variables
  become one with different instances. The values agree with those of the implementation,
  which only rebuilds the table if a type changes.
\<close>

definition map_insts :: "(ztyp \<Rightarrow> ztyp) \<Rightarrow> (zterm \<Rightarrow> zterm Z) \<Rightarrow> ztyp ztvtab \<times> zterm zvtab \<Rightarrow>
    (ztyp ztvtab \<times> zterm zvtab) Z" where
  "map_insts typ term insts = (case insts of (instT, inst) \<Rightarrow> do {
    xs \<leftarrow> mapZ (\<lambda>((x, T), t). do {t' \<leftarrow> term t; returnZ ((x, typ T), t')}) (zv_dest inst);
    inst' \<leftarrow> make_inst xs;
    returnZ (zt_map typ instT, inst')})"

text \<open>\<open>subst_type_same\<close>, \<open>subst_term_same\<close> with the instantiation of type variables
  \<open>tvar\<close> and variables \<open>var\<close>; the instance of a variable is looked up with its instantiated
  type.\<close>

fun zsubst_type :: "(indexname \<times> psort \<Rightarrow> ztyp option) \<Rightarrow> ztyp \<Rightarrow> ztyp" where
  "zsubst_type tvar (ZTVar v S) = (case tvar (v, S) of Some T \<Rightarrow> T | None \<Rightarrow> ZTVar v S)"
| "zsubst_type tvar (ZFun T U) = ZFun (zsubst_type tvar T) (zsubst_type tvar U)"
| "zsubst_type tvar ZProp = ZProp"
| "zsubst_type tvar (ZType0 a) = ZType0 a"
| "zsubst_type tvar (ZType1 a T) = ZType1 a (zsubst_type tvar T)"
| "zsubst_type tvar (ZType a Ts) = ZType a (map (zsubst_type tvar) Ts)"

fun zsubst_term :: "(ztyp \<Rightarrow> ztyp) \<Rightarrow> (indexname \<times> ztyp \<Rightarrow> zterm option) \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zsubst_term typ var (ZVar x T) = (case var (x, typ T) of Some t \<Rightarrow> t | None \<Rightarrow> ZVar x (typ T))"
| "zsubst_term typ var (ZBound i) = ZBound i"
| "zsubst_term typ var (ZConst0 a) = ZConst0 a"
| "zsubst_term typ var (ZConst1 a T) = ZConst1 a (typ T)"
| "zsubst_term typ var (ZConst a Ts) = ZConst a (map typ Ts)"
| "zsubst_term typ var (ZAbs a T t) = ZAbs a (typ T) (zsubst_term typ var t)"
| "zsubst_term typ var (ZApp t u) = ZApp (zsubst_term typ var t) (zsubst_term typ var u)"
| "zsubst_term typ var (ZOfclass T c) = ZOfclass (typ T) c"

text \<open>\<open>map_proof {hyps = false} typ term\<close>: not in hypotheses and class proofs.\<close>

fun map_zproof :: "(ztyp \<Rightarrow> ztyp) \<Rightarrow> (zterm \<Rightarrow> zterm Z) \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "map_zproof typ term (ZConstp (a, insts)) = do {insts' \<leftarrow> map_insts typ term insts; returnZ (ZConstp (a, insts'))}"
| "map_zproof typ term (ZAbst a T p) = do {p' \<leftarrow> map_zproof typ term p; returnZ (ZAbst a (typ T) p')}"
| "map_zproof typ term (ZAbsp a t p) = do {t' \<leftarrow> term t; p' \<leftarrow> map_zproof typ term p; returnZ (ZAbsp a t' p')}"
| "map_zproof typ term (ZAppt p t) = do {p' \<leftarrow> map_zproof typ term p; t' \<leftarrow> term t; returnZ (ZAppt p' t')}"
| "map_zproof typ term (ZAppp p q) = do {p' \<leftarrow> map_zproof typ term p; q' \<leftarrow> map_zproof typ term q; returnZ (ZAppp p' q')}"
| "map_zproof typ term p = returnZ p"


subsection \<open>Lifting\<close>

text \<open>\<open>ZTerm.incr_tvar_same\<close>: only the indices of schematic type variables (not \<open>-1\<close>).\<close>

definition zincr_tvar :: "integer \<Rightarrow> ztyp \<Rightarrow> ztyp" where
  "zincr_tvar inc T =
    (if inc = 0 then T else zsubst_type (\<lambda>((a, i), S). if i \<ge> 0 then Some (ZTVar (a, i + inc) S) else None) T)"

text \<open>
  The term operation of \<open>ZTerm.lift_proof\<close>: at abstraction level \<open>lev\<close>, the schematic
  variables are lifted over the types \<open>Ts\<close>. Fix (\<open>zterm-lift-frees\<close>): the types of free
  variables are incremented as well (as by \<open>Logic.incr_indexes\<close>); Isabelle2026 keeps them,
  so that the lifted proof of a rule with a free variable of a schematic type does not fit the
  lifted rule (see session \<open>Unpatched_Examples\<close>).
\<close>

fun zlift_term :: "integer \<Rightarrow> ztyp list \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zlift_term inc Ts lev (ZVar (x, i) T) =
    (if i \<ge> 0 then zcombound (ZVar (x, i + inc) (ZFuns Ts (zincr_tvar inc T))) lev (length Ts)
     else ZVar (x, i) (zincr_tvar inc T))"
| "zlift_term inc Ts lev (ZBound i) = ZBound i"
| "zlift_term inc Ts lev (ZConst0 c) = ZConst0 c"
| "zlift_term inc Ts lev (ZConst1 c T) = ZConst1 c (zincr_tvar inc T)"
| "zlift_term inc Ts lev (ZConst c Us) = ZConst c (map (zincr_tvar inc) Us)"
| "zlift_term inc Ts lev (ZAbs x T t) = ZAbs x (zincr_tvar inc T) (zlift_term inc Ts (lev + 1) t)"
| "zlift_term inc Ts lev (ZApp t u) = ZApp (zlift_term inc Ts lev t) (zlift_term inc Ts lev u)"
| "zlift_term inc Ts lev (ZOfclass T c) = ZOfclass (zincr_tvar inc T) c"

definition zlift_term' :: "integer \<Rightarrow> ztyp list \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zlift_term' inc Ts lev t = (if Ts = [] \<and> inc = 0 then t else zlift_term inc Ts lev t)"

fun zlift_prf :: "integer \<Rightarrow> ztyp list \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zlift_prf inc Ts lev (ZAbst a T p) = do {p' \<leftarrow> zlift_prf inc Ts (lev + 1) p; returnZ (ZAbst a (zincr_tvar inc T) p')}"
| "zlift_prf inc Ts lev (ZAbsp a t p) = do {p' \<leftarrow> zlift_prf inc Ts lev p; returnZ (ZAbsp a (zlift_term' inc Ts lev t) p')}"
| "zlift_prf inc Ts lev (ZAppt p t) = do {p' \<leftarrow> zlift_prf inc Ts lev p; returnZ (ZAppt p' (zlift_term' inc Ts lev t))}"
| "zlift_prf inc Ts lev (ZAppp p q) = do {
    p' \<leftarrow> zlift_prf inc Ts lev p; q' \<leftarrow> zlift_prf inc Ts lev q; returnZ (ZAppp p' q')}"
| "zlift_prf inc Ts lev (ZConstp (a, insts)) = do {
    insts' \<leftarrow> map_insts (zincr_tvar inc) (\<lambda>t. returnZ (zlift_term' inc Ts lev t)) insts;
    returnZ (ZConstp (a, insts'))}"
| "zlift_prf inc Ts lev (OFCLASSp T c) = returnZ (OFCLASSp (zincr_tvar inc T) c)"
| "zlift_prf inc Ts lev p = returnZ p"

definition zmk_app :: "bool \<Rightarrow> integer \<times> integer \<times> zproof \<Rightarrow> integer \<times> integer \<times> zproof" where
  "zmk_app b x = (case x of (i, j, p) \<Rightarrow>
    if b then (i - 1, j, ZAppp p (ZBoundp i)) else (i, j - 1, ZAppt p (ZBound j)))"

text \<open>
  The assumptions of the subgoal are converted; they occur unchanged in the lifted rule
  (\<open>Logic.lift_all\<close>). Fix (\<open>zterm-lift-hyps\<close>): \<open>ZTerm.lift_proof\<close> of Isabelle2026 lifts them
  like the terms of the rule (\<open>term Ts 0\<close>), which increments the indices of their schematic
  variables and applies these to the parameters, so that the annotation differs from the
  assumption if it has schematic variables (see session \<open>Unpatched_Examples\<close>).
\<close>

fun zlift_prems :: "ztypargs \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> ztyp list \<Rightarrow> bool list \<Rightarrow>
    integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> zproof Z" where
  "zlift_prems ta inc k prf Ts bs i j (Const c U $ A $ B) =
    (if c = STR ''Pure.imp'' then do {
       A' \<leftarrow> zterm_of ta A;
       p \<leftarrow> zlift_prems ta inc k prf Ts (True # bs) (i + 1) j B;
       returnZ (ZAbsp (STR ''H'') A' p)}
     else do {
       p \<leftarrow> zlift_prf inc (rev Ts) 0 prf;
       returnZ (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))})"
| "zlift_prems ta inc k prf Ts bs i j (Const c U $ Abs a T t) =
    (if c = STR ''Pure.all'' then do {
       p \<leftarrow> zlift_prems ta inc k prf (ztyp_of T # Ts) (False # bs) i (j + 1) t;
       returnZ (ZAbst a (ztyp_of T) p)}
     else do {
       p \<leftarrow> zlift_prf inc (rev Ts) 0 prf;
       returnZ (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))})"
| "zlift_prems ta inc k prf Ts bs i j _ = do {
    p \<leftarrow> zlift_prf inc (rev Ts) 0 prf;
    returnZ (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))}"

text \<open>\<open>ZTerm.lift_proof thy gprop inc prems prf\<close>\<close>

definition zlift_proof :: "ztypargs \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zlift_proof ta gprop inc prems prf = do {
    As \<leftarrow> mapZ (zterm_of ta) prems;
    p \<leftarrow> zlift_prems ta inc (integer_of_nat (length prems)) prf [] [] 0 0 gprop;
    returnZ (ZAbsps As p)}"


subsection \<open>Proofs by assumption and of flattened parameters\<close>

fun zimp_prf :: "zterm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> zproof" where
  "zimp_prf (ZApp (ZApp (ZConst0 c) A) B) i m =
    (if m = 0 then ZBoundp i
     else if c = STR ''Pure.imp'' then ZAbsp (STR ''H'') A (zimp_prf B (i + 1) (m - 1))
     else ZBoundp i)"
| "zimp_prf _ i m = ZBoundp i"

fun zall_prf :: "integer \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> zproof" where
  "zall_prf i m (ZApp (ZConst1 c U) (ZAbs a T t)) =
    (if c = STR ''Pure.all'' then ZAbst a T (zall_prf i m t) else zimp_prf (ZApp (ZConst1 c U) (ZAbs a T t)) (- i) m)"
| "zall_prf i m t = zimp_prf t (- i) m"

definition zmk_asm_prf :: "zterm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> zproof" where
  "zmk_asm_prf C i m = zall_prf i m C"

fun zflatten_params_proof :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> zterm \<times> integer \<Rightarrow> zproof" where
  "zflatten_params_proof i j n (ZApp (ZApp (ZConst0 c) A) B, k) =
    (if c = STR ''Pure.imp'' then ZAbsp (STR ''H'') A (zflatten_params_proof (i + 1) j n (B, k))
     else ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0)))
       (map ZBoundp (removeAll (i - n) (downto (i - 1) 0))))"
| "zflatten_params_proof i j n (ZApp (ZConst1 c U) (ZAbs a T t), k) =
    (if c = STR ''Pure.all'' then ZAbst a T (zflatten_params_proof i (j + 1) n (t, k))
     else ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0)))
       (map ZBoundp (removeAll (i - n) (downto (i - 1) 0))))"
| "zflatten_params_proof i j n (_, k) =
    ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0)))
      (map ZBoundp (removeAll (i - n) (downto (i - 1) 0)))"


subsection \<open>Normalisation with respect to an environment\<close>

text \<open>\<open>ZTerm.norm_type_same\<close>: type variables are looked up with \<open>Type.lookup\<close>, which raises
  \<open>TYPE\<close> on a different sort.\<close>

partial_function (option) znorm_type_aux :: "tyenv \<Rightarrow> ztyp \<Rightarrow> ztyp Z" where
  "znorm_type_aux tye T =
    (case T of
      ZTVar v S \<Rightarrow> do {
        r \<leftarrow> liftMZ (type_lookup tye v S);
        case r of Some U \<Rightarrow> znorm_type_aux tye (ztyp_of U) | None \<Rightarrow> returnZ T}
    | ZFun U V \<Rightarrow> do {U' \<leftarrow> znorm_type_aux tye U; V' \<leftarrow> znorm_type_aux tye V; returnZ (ZFun U' V')}
    | ZType1 a U \<Rightarrow> do {U' \<leftarrow> znorm_type_aux tye U; returnZ (ZType1 a U')}
    | ZType a Us \<Rightarrow> do {Us' \<leftarrow> mapZ (znorm_type_aux tye) Us; returnZ (ZType a Us')}
    | _ \<Rightarrow> returnZ T)"

definition znorm_type :: "tyenv \<Rightarrow> ztyp \<Rightarrow> ztyp Z" where
  "znorm_type tye T = (if vt_is_empty tye then returnZ T else znorm_type_aux tye T)"

text \<open>
  \<open>ZTerm.norm_term_same\<close>: variables are looked up with \<open>Envir.lookup\<close> at their regular type,
  and the result is converted; the type of a class membership is not normalised.
\<close>

definition zlookup :: "ztypargs \<Rightarrow> env \<Rightarrow> indexname \<Rightarrow> ztyp \<Rightarrow> zterm option Z" where
  "zlookup ta env xi T =
    (if vt_is_empty (tenv env) then returnZ None
     else do {
       r \<leftarrow> liftMZ (lookup env xi (typ_of T));
       case r of None \<Rightarrow> returnZ None | Some u \<Rightarrow> do {u' \<leftarrow> zterm_of ta u; returnZ (Some u')}})"

partial_function (option) znorm_term_aux :: "(ztypargs \<times> env) \<times> zterm \<Rightarrow> zterm Z" where
  "znorm_term_aux x =
    (case snd x of
      ZVar xi T \<Rightarrow> do {
        r \<leftarrow> zlookup (fst (fst x)) (snd (fst x)) xi T;
        case r of
          Some u \<Rightarrow> znorm_term_aux (fst x, u)
        | None \<Rightarrow> do {T' \<leftarrow> znorm_type (tyenv (snd (fst x))) T; returnZ (ZVar xi T')}}
    | ZConst1 a T \<Rightarrow> do {T' \<leftarrow> znorm_type (tyenv (snd (fst x))) T; returnZ (ZConst1 a T')}
    | ZConst a Ts \<Rightarrow> do {Ts' \<leftarrow> mapZ (znorm_type (tyenv (snd (fst x)))) Ts; returnZ (ZConst a Ts')}
    | ZAbs a T b \<Rightarrow> do {T' \<leftarrow> znorm_type (tyenv (snd (fst x))) T; b' \<leftarrow> znorm_term_aux (fst x, b); returnZ (ZAbs a T' b')}
    | ZApp g u \<Rightarrow>
        (case g of
          ZAbs _ _ body \<Rightarrow> znorm_term_aux (fst x, subst_term_bound u body)
        | _ \<Rightarrow> do {
            nf \<leftarrow> znorm_term_aux (fst x, g);
            case nf of
              ZAbs _ _ body \<Rightarrow> znorm_term_aux (fst x, subst_term_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> znorm_term_aux (fst x, u); returnZ (ZApp nf nu)}})
    | t \<Rightarrow> returnZ t)"

definition znorm_term :: "ztypargs \<Rightarrow> env \<Rightarrow> zterm \<Rightarrow> zterm Z" where
  "znorm_term ta env t = (if env_is_empty env then liftOZ (beta_norm_term t) else znorm_term_aux ((ta, env), t))"

text \<open>
  \<open>norm_proof_cache\<close>: only the type variables and variables of the visible propositions are
  instantiated, by their normal forms; then the term arguments are \<open>\<beta>\<close>-normalised. The
  instantiations are computed first, in the order of the occurrences in the propositions.
\<close>

fun dedup :: "'a list \<Rightarrow> 'a list" where
  "dedup [] = []"
| "dedup (x # xs) = x # dedup (filter (\<lambda>y. y \<noteq> x) xs)"

definition visible_tvars :: "pterm list \<Rightarrow> (indexname \<times> psort) list" where
  "visible_tvars ts = dedup (concat (map (\<lambda>t. concat (map typ_tvars (term_types t))) ts))"

definition visible_vars :: "pterm list \<Rightarrow> (indexname \<times> ptyp) list" where
  "visible_vars ts = concat (map term_vars ts)"

text \<open>Variables of tight terms are compared componentwise (ML's equality on \<open>ztyp\<close>).\<close>

definition zvar_eq :: "indexname \<times> ztyp \<Rightarrow> indexname \<times> ztyp \<Rightarrow> bool" where
  "zvar_eq v w \<longleftrightarrow> fst v = fst w \<and> snd v = snd w"

lemma zvar_eq_iff[simp]: "zvar_eq v w \<longleftrightarrow> v = w"
  by (cases v; cases w) (simp add: zvar_eq_def)

fun zdedup_vars :: "(indexname \<times> ztyp) list \<Rightarrow> (indexname \<times> ztyp) list" where
  "zdedup_vars [] = []"
| "zdedup_vars (v # vs) = v # zdedup_vars (filter (\<lambda>w. \<not> zvar_eq w v) vs)"

fun zlookup_var :: "((indexname \<times> ztyp) \<times> 'a) list \<Rightarrow> indexname \<times> ztyp \<Rightarrow> 'a option" where
  "zlookup_var [] v = None"
| "zlookup_var ((w, x) # xs) v = (if zvar_eq w v then Some x else zlookup_var xs v)"

definition znorm_proof :: "ztypargs \<Rightarrow> env \<Rightarrow> pterm list \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "znorm_proof ta env visible prf =
    (if env_is_empty env \<or> visible = [] then liftOZ (beta_norm_prooft prf)
     else do {
       instT \<leftarrow> (if vt_is_empty (tyenv env) then returnZ None
                else do {
                  Us \<leftarrow> mapZ (\<lambda>(v, S). znorm_type (tyenv env) (ZTVar v S)) (visible_tvars visible);
                  returnZ (Some (zip (visible_tvars visible) Us))});
       let inst_typ = (case instT of None \<Rightarrow> id
         | Some xs \<Rightarrow> if List.null xs then id else zsubst_type (map_of xs));
       let vs = zdedup_vars (map (\<lambda>(a, T). (a, inst_typ (ztyp_of T))) (visible_vars visible));
       us \<leftarrow> mapZ (\<lambda>(a, T). znorm_term ta env (ZVar a T)) vs;
       let inst_term = zsubst_term inst_typ (zlookup_var (zip vs us));
       p \<leftarrow> map_zproof inst_typ (\<lambda>t. liftOZ (beta_norm_term (inst_term t))) prf;
       liftOZ (beta_norm_prooft p)})"


subsection \<open>Composition\<close>

text \<open>
  \<open>ZTerm.bicompose_proof thy env smax flatten Bs As A oldAs n m visible rprf sprf\<close>: the
  proofs of the rule and of the proof state are normalised first (the proof state only if the
  environment instantiates its variables), then the terms of \<open>Bs @ As\<close>, \<open>A\<close> and \<open>oldAs\<close>.
\<close>

definition zbicompose_core :: "ztypargs \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> pterm option \<Rightarrow>
    pterm list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zbicompose_core ta env flatten Bs As A oldAs n m p q = do {
    let normt = (\<lambda>t. do {t' \<leftarrow> zterm_of ta t; znorm_term ta env t'});
    Ns \<leftarrow> mapZ normt (Bs @ As);
    let lb = integer_of_nat (length Bs);
    let la = integer_of_nat (length As);
    let q' = ZAppps q (map ZBoundp (downto (lb + la - 1) la));
    asm \<leftarrow> (if n > 0 then (case A of None \<Rightarrow> raiseZ ZOption
                             | Some C \<Rightarrow> do {C' \<leftarrow> normt C; returnZ [zmk_asm_prf C' n m]})
            else returnZ []);
    Os \<leftarrow> mapZ normt oldAs;
    ks \<leftarrow> liftMZ (zip_eq Os (downto (la - 1) 0));
    returnZ (ZAbsps Ns (ZAppp q'
      (ZAppps p (asm @ map (if flatten then zflatten_params_proof 0 0 n else (\<lambda>x. ZBoundp (snd x))) ks))))}"

definition zbicompose_proof :: "ztypargs \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow>
    pterm option \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zbicompose_proof ta env smax flatten Bs As A oldAs n m visible rprf sprf =
    (if env_is_empty env then zbicompose_core ta env flatten Bs As A oldAs n m rprf sprf
     else do {
       rprf' \<leftarrow> znorm_proof ta env visible rprf;
       sprf' \<leftarrow> (if above env smax then returnZ sprf else znorm_proof ta env visible sprf);
       zbicompose_core ta env flatten Bs As A oldAs n m rprf' sprf'})"

end
