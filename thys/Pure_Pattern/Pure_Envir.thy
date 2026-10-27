section \<open>Sorts, Type Unification and Environments\<close>

theory Pure_Envir
  imports Pure_Term
begin

text \<open>
  Models of \<^file>\<open>~~/src/Pure/sorts.ML\<close> (the operations on the order-sorted algebra),
  \<^file>\<open>~~/src/Pure/type.ML\<close> (matching and order-sorted unification of types) and
  \<^file>\<open>~~/src/Pure/envir.ML\<close> (environments and head normalization).
\<close>


subsection \<open>The sort algebra\<close>

text \<open>
  The class algebra of a theory (\<open>Sorts.algebra\<close>) is an abstract type. We only access the
  proper subclass relation and the arities of type constructors; everything else is defined
  in terms of them, following \<^file>\<open>~~/src/Pure/sorts.ML\<close>.
\<close>

typedecl algebra

consts
  class_less :: "algebra \<Rightarrow> pclass \<Rightarrow> pclass \<Rightarrow> bool"
  arities :: "algebra \<Rightarrow> name \<Rightarrow> (pclass \<times> psort list) list"

definition class_le :: "algebra \<Rightarrow> pclass \<Rightarrow> pclass \<Rightarrow> bool" where
  "class_le alg c1 c2 \<longleftrightarrow> c1 = c2 \<or> class_less alg c1 c2"

definition sort_le :: "algebra \<Rightarrow> psort \<Rightarrow> psort \<Rightarrow> bool" where
  "sort_le alg S1 S2 \<longleftrightarrow> S1 = S2 \<or> list_all (\<lambda>c2. list_ex (\<lambda>c1. class_le alg c1 c2) S1) S2"

fun inter_class :: "algebra \<Rightarrow> pclass \<Rightarrow> psort \<Rightarrow> psort" where
  "inter_class alg c [] = [c]"
| "inter_class alg c (c' # cs) =
    (if class_le alg c' c then c' # cs
     else if class_le alg c c' then inter_class alg c cs
     else c' # inter_class alg c cs)"

definition inter_sort :: "algebra \<Rightarrow> psort \<Rightarrow> psort \<Rightarrow> psort" where
  "inter_sort alg S1 S2 = sort (fold (inter_class alg) S1 S2)"

definition mg_domain :: "algebra \<Rightarrow> name \<Rightarrow> psort \<Rightarrow> psort list M" where
  "mg_domain alg a S =
    (let
      dom = (\<lambda>c. case map_of (arities alg a) c of
        None \<Rightarrow> raise (Class_Error (No_Arity a c))
      | Some Ss \<Rightarrow> return Ss);
      dom_inter = (\<lambda>c Ss. do {Ds \<leftarrow> dom c; return (map2 (inter_sort alg) Ds Ss)})
    in
      case S of
        [] \<Rightarrow> raise (Fail (STR ''Unknown domain of empty intersection''))
      | c # cs \<Rightarrow> do {Ds \<leftarrow> dom c; foldM dom_inter cs Ds})"

text \<open>\<open>ListPair.all\<close> with a monadic predicate (ignores excess elements).\<close>

fun allM :: "('a \<Rightarrow> bool M) \<Rightarrow> 'a list \<Rightarrow> bool M" where
  "allM P [] = return True"
| "allM P (x # xs) = do {b \<leftarrow> P x; if b then allM P xs else return False}"

fun existsM :: "('a \<Rightarrow> bool M) \<Rightarrow> 'a list \<Rightarrow> bool M" where
  "existsM P [] = return False"
| "existsM P (x # xs) = do {b \<leftarrow> P x; if b then return True else existsM P xs}"

lemma allM_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> P x = Q x) \<Longrightarrow> allM P xs = allM Q ys"
  by (induction ys arbitrary: xs) (auto intro!: bindM_cong)

lemma existsM_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> P x = Q x) \<Longrightarrow> existsM P xs = existsM Q ys"
  by (induction ys arbitrary: xs) (auto intro!: bindM_cong)

lemma if_mono_option:
  "mono_option A \<Longrightarrow> mono_option B \<Longrightarrow> mono_option (\<lambda>f. if b then A f else B f)"
  by (cases b) simp_all

lemma allM_mono[partial_function_mono]:
  assumes "\<And>x. mono_option (\<lambda>f. C x f)"
  shows "mono_option (\<lambda>f. allM (\<lambda>x. C x f) xs)"
  using assms
  by (induction xs) (auto intro!: bindM_mono if_mono_option simp: return_def option.const_mono)

lemma existsM_mono[partial_function_mono]:
  assumes "\<And>x. mono_option (\<lambda>f. C x f)"
  shows "mono_option (\<lambda>f. existsM (\<lambda>x. C x f) xs)"
  using assms
  by (induction xs) (auto intro!: bindM_mono if_mono_option simp: return_def option.const_mono)

text \<open>\<open>Sorts.of_sort\<close>: \<open>CLASS_ERROR\<close> is caught and yields \<^const>\<open>False\<close>.\<close>

function of_sort :: "algebra \<Rightarrow> ptyp \<Rightarrow> psort \<Rightarrow> bool M" where
  "of_sort alg T S =
    (if S = [] then return True else
      case T of
        TFree _ S' \<Rightarrow> return (sort_le alg S' S)
      | TVar _ S' \<Rightarrow> return (sort_le alg S' S)
      | Type a Ts \<Rightarrow>
          handle (do {Ss \<leftarrow> mg_domain alg a S; allM (\<lambda>(T, S). of_sort alg T S) (zip Ts Ss)})
            (\<lambda>e. case e of Class_Error _ \<Rightarrow> return False | _ \<Rightarrow> raise e))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(alg, T, S). size T)")
    (fastforce dest: set_zip_leftD intro: size_list_estimation' simp: less_Suc_eq_le)+

declare of_sort.simps[simp del]


subsection \<open>Matching and unification of types\<close>

text \<open>\<open>Type.lookup\<close>: the sort is part of the name of a type variable.\<close>

definition tvar_clash :: "indexname \<Rightarrow> psort \<Rightarrow> psort \<Rightarrow> 'a M" where
  "tvar_clash ixn S S' =
    raise (Type_Error (STR ''Type variable has two distinct sorts'') [TVar ixn S, TVar ixn S'] [])"

definition type_lookup :: "tyenv \<Rightarrow> indexname \<Rightarrow> psort \<Rightarrow> ptyp option M" where
  "type_lookup tye ixn S =
    (case vt_lookup tye ixn of
      None \<Rightarrow> return None
    | Some (S', T) \<Rightarrow> if S = S' then return (Some T) else tvar_clash ixn S S')"

definition update_new :: "indexname \<times> 'a \<Rightarrow> 'a vartab \<Rightarrow> 'a vartab M" where
  "update_new kx t = (if vt_defined t (fst kx) then raise (Dup (fst kx)) else return (vt_update kx t))"

text \<open>\<open>Type.typ_match\<close> (matching with sort constraints).\<close>

function (sequential) typ_match :: "algebra \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> tyenv \<Rightarrow> tyenv M" where
  "typ_match alg (TVar v S) T subs =
    do {
      r \<leftarrow> type_lookup subs v S;
      case r of
        None \<Rightarrow> do {b \<leftarrow> of_sort alg T S; if b then update_new (v, (S, T)) subs else raise Type_Match}
      | Some U \<Rightarrow> if U = T then return subs else raise Type_Match
    }"
| "typ_match alg (Type a Ts) (Type b Us) subs =
    (if a \<noteq> b then raise Type_Match
     else foldM (\<lambda>(T, U) subs. typ_match alg T U subs) (zip Ts Us) subs)"
| "typ_match alg (TFree a S) (TFree b S') subs =
    (if (a, S) = (b, S') then return subs else raise Type_Match)"
| "typ_match alg _ _ subs = raise Type_Match"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(alg, T, U, subs). size T)")
    (fastforce dest: set_zip_leftD intro: size_list_estimation' simp: less_Suc_eq_le)+

text \<open>\<open>Type.devar\<close>: chase variable assignments; may diverge on cyclic environments.\<close>

partial_function (option) devar :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "devar tye T =
    (case T of
      TVar ixn S \<Rightarrow> do {r \<leftarrow> type_lookup tye ixn S; case r of Some U \<Rightarrow> devar tye U | None \<Rightarrow> return T}
    | _ \<Rightarrow> return T)"

text \<open>\<open>Type.occurs\<close>.\<close>

partial_function (option) type_occurs :: "indexname \<Rightarrow> tyenv \<Rightarrow> ptyp \<Rightarrow> bool M" where
  "type_occurs v tye T =
    (case T of
      Type _ Ts \<Rightarrow> existsM (type_occurs v tye) Ts
    | TFree _ _ \<Rightarrow> return False
    | TVar w S \<Rightarrow>
        if v = w then return True
        else do {r \<leftarrow> type_lookup tye w S; case r of None \<Rightarrow> return False | Some U \<Rightarrow> type_occurs v tye U})"

text \<open>\<open>Type.unified\<close>: equality of types modulo a type environment.\<close>

partial_function (option) unified_aux :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> bool M" where
  "unified_aux tye T T' =
    do {
      U \<leftarrow> devar tye T;
      U' \<leftarrow> devar tye T';
      case (U, U') of
        (Type s Ts, Type s' Ts') \<Rightarrow>
          if s = s' then do {
            b \<leftarrow> allM (\<lambda>(T, T'). unified_aux tye T T') (zip Ts Ts');
            return (b \<and> length Ts = length Ts')}
          else return False
      | _ \<Rightarrow> return (U = U')
    }"

definition unified :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> bool M" where
  "unified tye T T' = (if vt_is_empty tye then return (T = T') else unified_aux tye T T')"

text \<open>
  \<open>Type.unify\<close>: order-sorted unification. The state consists of the type environment and the
  counter for new type variables, which are named \<open>'a\<close> (\<open>Name.aT\<close>).
\<close>

type_synonym tstate = "tyenv \<times> integer"

definition aT :: name where
  "aT = String.implode [CHR 0x27, CHR ''a'']"

definition gen_tyvar :: "psort \<Rightarrow> integer \<Rightarrow> ptyp \<times> integer" where
  "gen_tyvar S cnt = (TVar (aT, cnt + 1) S, cnt + 1)"

definition mg_domain_unif :: "algebra \<Rightarrow> name \<Rightarrow> psort \<Rightarrow> psort list M" where
  "mg_domain_unif alg a S =
    handle (mg_domain alg a S) (\<lambda>e. case e of Class_Error _ \<Rightarrow> raise TUnify | _ \<Rightarrow> raise e)"

partial_function (option) meet :: "algebra \<Rightarrow> ptyp \<Rightarrow> psort \<Rightarrow> tstate \<Rightarrow> tstate M" where
  "meet alg T S st =
    (if S = [] then return st else
      let (tye, cnt) = st in
      case T of
        TVar xi S' \<Rightarrow>
          if sort_le alg S' S then return st
          else do {
            let (V, cnt') = gen_tyvar (inter_sort alg S' S) cnt;
            tye' \<leftarrow> update_new (xi, (S', V)) tye;
            return (tye', cnt')}
      | TFree _ S' \<Rightarrow> if sort_le alg S' S then return st else raise TUnify
      | Type a Ts \<Rightarrow> do {
          Ss \<leftarrow> mg_domain_unif alg a S;
          foldM (\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; meet alg T' S st}) (zip Ts Ss) st})"

partial_function (option) unify_aux :: "algebra \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> tstate \<Rightarrow> tstate M" where
  "unify_aux alg ty1 ty2 st =
    (let (tye, cnt) = st in do {
      T \<leftarrow> devar tye ty1;
      U \<leftarrow> devar tye ty2;
      case (T, U) of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return st else tvar_clash v S1 S2)
          else if sort_le alg S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T)) tye; return (tye', cnt)}
          else if sort_le alg S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U)) tye; return (tye', cnt)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg S1 S2) cnt;
            tye' \<leftarrow> update_new (w, (S2, S)) tye;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye U;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U)) tye; meet alg U S (tye', cnt)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye T;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T)) tye; meet alg T S (tye', cnt)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. unify_aux alg T U st) (zip Ts Us) st
      | _ \<Rightarrow> if T = U then return st else raise TUnify
    })"

definition type_unify :: "algebra \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> tstate \<Rightarrow> tstate M" where
  "type_unify alg T U st = unify_aux alg T U st"


subsection \<open>Environments\<close>

definition genvar :: "name \<Rightarrow> env \<Rightarrow> ptyp \<Rightarrow> env \<times> pterm" where
  "genvar a env T =
    (case env of Envir i te tye \<Rightarrow> (Envir (i + 1) te tye, Var (a, i + 1) T))"

definition var_clash :: "indexname \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> 'a M" where
  "var_clash xi T T' =
    raise (Type_Error (STR ''Variable has two distinct types'') [] [Var xi T', Var xi T])"

text \<open>\<open>Envir.lookup1\<close> (for matching: types are compared literally).\<close>

definition lookup1 :: "tenv \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> pterm option M" where
  "lookup1 te xi T =
    (case vt_lookup te xi of
      None \<Rightarrow> return None
    | Some (U, t) \<Rightarrow> if T = U then return (Some t) else var_clash xi T U)"

text \<open>\<open>Envir.lookup\<close> (for unification: types are compared modulo the type environment).\<close>

definition lookup :: "env \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> pterm option M" where
  "lookup env xi T =
    (case vt_lookup (tenv env) xi of
      None \<Rightarrow> return None
    | Some (U, t) \<Rightarrow> do {b \<leftarrow> unified (tyenv env) T U; if b then return (Some t) else var_clash xi T U})"

definition update :: "indexname \<times> ptyp \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> env M" where
  "update xT t env =
    (case env of Envir i te tye \<Rightarrow> do {
      te' \<leftarrow> update_new (fst xT, (snd xT, t)) te;
      return (Envir i te' tye)})"

text \<open>\<open>Envir.head_norm\<close>; may diverge (untyped terms, cyclic environments).\<close>

partial_function (option) head_norm :: "env \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "head_norm env t =
    (case t of
      Var xi T \<Rightarrow> do {r \<leftarrow> lookup env xi T; case r of Some u \<Rightarrow> head_norm env u | None \<Rightarrow> return t}
    | Abs a T body \<Rightarrow> do {body' \<leftarrow> head_norm env body; return (Abs a T body')}
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> head_norm env (subst_bound u body)
        | _ \<Rightarrow> do {
            nf \<leftarrow> head_norm env f;
            case nf of
              Abs _ _ body \<Rightarrow> head_norm env (subst_bound u body)
            | _ \<Rightarrow> return (nf $ u)})
    | _ \<Rightarrow> return t)"

text \<open>\<open>Envir.norm_type\<close>; may diverge on cyclic type environments.\<close>

partial_function (option) norm_type_aux :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "norm_type_aux tye T =
    (case T of
      Type a Ts \<Rightarrow> do {Ts' \<leftarrow> mapM (norm_type_aux tye) Ts; return (Type a Ts')}
    | TFree _ _ \<Rightarrow> return T
    | TVar v S \<Rightarrow> do {r \<leftarrow> type_lookup tye v S; case r of Some U \<Rightarrow> norm_type_aux tye U | None \<Rightarrow> return T})"

definition norm_type :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "norm_type tye T = (if vt_is_empty tye then return T else norm_type_aux tye T)"

text \<open>\<open>Envir.subst_type\<close>: plain substitution without chasing.\<close>

fun subst_type_aux :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "subst_type_aux tye (Type a Ts) = do {Ts' \<leftarrow> mapM (subst_type_aux tye) Ts; return (Type a Ts')}"
| "subst_type_aux tye (TVar v S) =
    do {r \<leftarrow> type_lookup tye v S; case r of Some U \<Rightarrow> return U | None \<Rightarrow> return (TVar v S)}"
| "subst_type_aux tye T = return T"

definition subst_type :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "subst_type tye T = (if vt_is_empty tye then return T else subst_type_aux tye T)"

end
