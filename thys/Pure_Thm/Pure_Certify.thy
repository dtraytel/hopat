section \<open>Certification of Types and Terms\<close>

theory Pure_Certify
  imports Pure_Cterm Pure_Extra
begin

text \<open>
  Models of the certification behind \<open>Thm.global_ctyp_of\<close> and \<open>Thm.global_cterm_of\<close>:
  \<open>Type.certify_typ\<close> with the default mode (\<^file>\<open>~~/src/Pure/type.ML\<close>), \<open>Sign.certify_term\<close>
  (\<^file>\<open>~~/src/Pure/sign.ML\<close>) with \<open>Type.raw_instance\<close> for the types of constants
  (\<open>Consts.certify\<close>, \<^file>\<open>~~/src/Pure/consts.ML\<close>), and the records that \<open>thm.ML\<close> makes of the
  results. A result \<open>None\<close> stands for an exception (\<open>TYPE\<close>, or \<open>ERROR\<close> for an undeclared type
  constructor).

  The signature is given by its parts: the sort algebra, the declarations of the type
  constructors, the type schemes of the constants, and the abbreviations of constants with the
  right-hand sides that certification inserts (\<open>normal_rhs\<close>, in which the abbreviations are
  expanded). One part of the code is left out: \<open>Soft_Type_System.global_purge\<close> is the identity
  unless a theory installs a soft type system.
\<close>

subsection \<open>The signature\<close>

text \<open>\<open>Type.decl\<close>: a type constructor with its number of arguments, a type abbreviation
  with its parameters, right-hand side and the flag for syntactic types, or a nonterminal.\<close>

datatype tdecl = Logical_Type integer | Abbreviation "name list" ptyp bool | Nonterminal

text \<open>A class of the algebra (\<open>Sorts.cert_class\<close> without its exception):\<close>

definition class_mem :: "algebra \<Rightarrow> pclass \<Rightarrow> bool" where
  "class_mem alg c \<longleftrightarrow> c \<in> classes alg"

text \<open>\<open>Long_Name.is_qualified\<close>:\<close>

definition is_qualified :: "name \<Rightarrow> bool" where
  "is_qualified x \<longleftrightarrow> CHR ''.'' \<in> set (String.explode x)"

fun len :: "'a list \<Rightarrow> integer" where
  "len [] = 0"
| "len (x # xs) = len xs + 1"

fun nth_opt :: "'a list \<Rightarrow> integer \<Rightarrow> 'a option" where
  "nth_opt [] i = None"
| "nth_opt (x # xs) i = (if i = 0 then Some x else if i < 0 then None else nth_opt xs (i - 1))"

fun those_map :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "those_map f [] = Some []"
| "those_map f (x # xs) =
    (case f x of
      None \<Rightarrow> None
    | Some y \<Rightarrow> (case those_map f xs of None \<Rightarrow> None | Some ys \<Rightarrow> Some (y # ys)))"

lemma those_map_cong [fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> those_map f xs = those_map g ys"
  by (induction ys arbitrary: xs) (auto split: option.splits)


subsection \<open>Types\<close>

text \<open>\<open>Sorts.cert_sort\<close>: the classes of the sort are declared (the sort is kept as it is).\<close>

definition cert_sort :: "algebra \<Rightarrow> psort \<Rightarrow> bool" where
  "cert_sort alg S \<longleftrightarrow> list_all (class_mem alg) S"

text \<open>
  \<open>Term_Subst.instantiateT_frees\<close> for the table of \<open>inst_typ\<close>, whose keys are the parameters
  of a type abbreviation with the empty sort (the first entry of a name counts).
\<close>

fun inst_frees :: "(name \<times> ptyp) list \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "inst_frees tab (Type a Ts) = Type a (map (inst_frees tab) Ts)"
| "inst_frees tab (TFree a S) =
    (if S = [] then (case map_of tab a of Some T \<Rightarrow> T | None \<Rightarrow> TFree a S) else TFree a S)"
| "inst_frees tab (TVar v S) = TVar v S"

text \<open>\<open>Type.certify_typ Type.mode_default\<close> (\<open>normalize\<close> and \<open>logical\<close> are true).\<close>

fun certify_typ :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> ptyp \<Rightarrow> ptyp option" where
  "certify_typ alg td (Type c args) =
    (case td c of
      None \<Rightarrow> None
    | Some (Logical_Type n) \<Rightarrow>
        if len args \<noteq> n then None
        else map_option (Type c) (those_map (certify_typ alg td) args)
    | Some (Abbreviation vs U syntactic) \<Rightarrow>
        if len args \<noteq> len vs then None
        else if syntactic then None
        else map_option (\<lambda>args'. inst_frees (zip vs args') U) (those_map (certify_typ alg td) args)
    | Some Nonterminal \<Rightarrow> None)"
| "certify_typ alg td (TFree a S) = (if cert_sort alg S then Some (TFree a S) else None)"
| "certify_typ alg td (TVar (x, i) S) =
    (if i < 0 then None else if cert_sort alg S then Some (TVar (x, i) S) else None)"

text \<open>\<open>Type.certify_types\<close>:\<close>

fun certify_types :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> pterm \<Rightarrow> pterm option" where
  "certify_types alg td (Const c T) = map_option (Const c) (certify_typ alg td T)"
| "certify_types alg td (Free x T) = map_option (Free x) (certify_typ alg td T)"
| "certify_types alg td (Var v T) = map_option (Var v) (certify_typ alg td T)"
| "certify_types alg td (Bound i) = Some (Bound i)"
| "certify_types alg td (Abs a T t) =
    (case certify_typ alg td T of
      None \<Rightarrow> None
    | Some T' \<Rightarrow> map_option (Abs a T') (certify_types alg td t))"
| "certify_types alg td (t $ u) =
    (case certify_types alg td t of
      None \<Rightarrow> None
    | Some t' \<Rightarrow> map_option (App t') (certify_types alg td u))"


subsection \<open>Terms\<close>

text \<open>\<open>check_vars\<close> of \<open>sign.ML\<close>:\<close>

fun check_vars :: "pterm \<Rightarrow> bool" where
  "check_vars (t $ u) \<longleftrightarrow> check_vars t \<and> check_vars u"
| "check_vars (Abs _ _ t) \<longleftrightarrow> check_vars t"
| "check_vars (Free x _) \<longleftrightarrow> \<not> is_qualified x"
| "check_vars (Var (_, i) _) \<longleftrightarrow> \<not> i < 0"
| "check_vars _ \<longleftrightarrow> True"

text \<open>\<open>type_check\<close> of \<open>sign.ML\<close>: the type of a term, with the types of its loose bound
  variables.\<close>

fun typ_of :: "ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp option" where
  "typ_of bs (Const _ T) = Some T"
| "typ_of bs (Free _ T) = Some T"
| "typ_of bs (Var _ T) = Some T"
| "typ_of bs (Bound i) = nth_opt bs i"
| "typ_of bs (Abs _ T body) = map_option (\<lambda>U. T \<rightarrow>\<^sub>T U) (typ_of (T # bs) body)"
| "typ_of bs (t $ u) =
    (case typ_of bs t of
      None \<Rightarrow> None
    | Some T \<Rightarrow>
        (case typ_of bs u of
          None \<Rightarrow> None
        | Some U \<Rightarrow>
            (case T of
              Type c [T1, T2] \<Rightarrow> if c = STR ''fun'' \<and> T1 = U then Some T2 else None
            | _ \<Rightarrow> None)))"

text \<open>
  \<open>Type.raw_match\<close>: matching without sorts. \<open>Type.lookup\<close> raises \<open>TYPE\<close> for a type variable
  with two sorts.
\<close>

fun raw_match :: "ptyp \<Rightarrow> ptyp \<Rightarrow> tyenv \<Rightarrow> tyenv option"
  and raw_matches :: "ptyp list \<Rightarrow> ptyp list \<Rightarrow> tyenv \<Rightarrow> tyenv option" where
  "raw_match (TVar v S) T subs =
    (case vt_lookup subs v of
      None \<Rightarrow> Some (vt_update (v, (S, T)) subs)
    | Some (S', U) \<Rightarrow> if S = S' \<and> U = T then Some subs else None)"
| "raw_match (Type a Ts) (Type b Us) subs = (if a \<noteq> b then None else raw_matches Ts Us subs)"
| "raw_match (TFree a S) (TFree b S') subs = (if a = b \<and> S = S' then Some subs else None)"
| "raw_match (Type a Ts) (TFree b S') subs = None"
| "raw_match (Type a Ts) (TVar w S') subs = None"
| "raw_match (TFree a S) (Type b Us) subs = None"
| "raw_match (TFree a S) (TVar w S') subs = None"
| "raw_matches (T # Ts) (U # Us) subs =
    (case raw_match T U subs of None \<Rightarrow> None | Some subs' \<Rightarrow> raw_matches Ts Us subs')"
| "raw_matches [] [] subs = Some subs"
| "raw_matches [] (U # Us) subs = None"
| "raw_matches (T # Ts) [] subs = None"

text \<open>\<open>Type.could_match\<close>, the filter before matching, and \<open>Type.raw_instance (T, U)\<close>:\<close>

fun could_match :: "ptyp \<Rightarrow> ptyp \<Rightarrow> bool"
  and could_matches :: "ptyp list \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "could_match (Type a Ts) (Type b Us) \<longleftrightarrow> a = b \<and> could_matches Ts Us"
| "could_match (TFree a _) (TFree b _) \<longleftrightarrow> a = b"
| "could_match (TVar _ _) _ \<longleftrightarrow> True"
| "could_match _ _ \<longleftrightarrow> False"
| "could_matches (T # Ts) (U # Us) \<longleftrightarrow> could_match T U \<and> could_matches Ts Us"
| "could_matches [] [] \<longleftrightarrow> True"
| "could_matches _ _ \<longleftrightarrow> False"

definition raw_instance :: "ptyp \<Rightarrow> ptyp \<Rightarrow> bool" where
  "raw_instance T U \<longleftrightarrow> could_match U T \<and> raw_match U T vt_empty \<noteq> None"


subsection \<open>Constants\<close>

text \<open>
  \<open>Envir.subst_term_types\<close> with \<open>Type.lookup\<close> (which raises \<open>TYPE\<close> for a type variable with
  another sort than in the table), and \<open>Envir.expand_atom\<close>: the right-hand side of an
  abbreviation of type \<open>U\<close> at the instance \<open>T\<close>.
\<close>

fun subst_typ0 :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp option" where
  "subst_typ0 \<theta> (Type a Ts) = map_option (Type a) (those_map (subst_typ0 \<theta>) Ts)"
| "subst_typ0 \<theta> (TFree a S) = Some (TFree a S)"
| "subst_typ0 \<theta> (TVar v S) =
    (case vt_lookup \<theta> v of
      None \<Rightarrow> Some (TVar v S)
    | Some (S', T) \<Rightarrow> if S = S' then Some T else None)"

fun subst_term_types :: "tyenv \<Rightarrow> pterm \<Rightarrow> pterm option" where
  "subst_term_types \<theta> (Const c T) = map_option (Const c) (subst_typ0 \<theta> T)"
| "subst_term_types \<theta> (Free x T) = map_option (Free x) (subst_typ0 \<theta> T)"
| "subst_term_types \<theta> (Var v T) = map_option (Var v) (subst_typ0 \<theta> T)"
| "subst_term_types \<theta> (Bound i) = Some (Bound i)"
| "subst_term_types \<theta> (Abs a T t) =
    (case subst_typ0 \<theta> T of
      None \<Rightarrow> None
    | Some T' \<Rightarrow> map_option (Abs a T') (subst_term_types \<theta> t))"
| "subst_term_types \<theta> (t $ u) =
    (case subst_term_types \<theta> t of
      None \<Rightarrow> None
    | Some t' \<Rightarrow> map_option (App t') (subst_term_types \<theta> u))"

definition expand_atom :: "ptyp \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> pterm option" where
  "expand_atom T U u =
    (case raw_match U T vt_empty of None \<Rightarrow> None | Some \<theta> \<Rightarrow> subst_term_types \<theta> u)"

text \<open>
  \<open>Consts.certify {normalize = true}\<close>. A term with a constant that is an abbreviation
  (\<open>need_expand\<close>) is rebuilt by \<open>expand_term\<close>: the code takes an application apart
  (\<open>Term.strip_comb\<close>), expands the arguments, and applies the head to them, the right-hand side
  of an abbreviation with \<open>Term.betapplys\<close>. Here \<open>expand_term \<dots> t args\<close> is the result for the
  application of \<open>t\<close> to arguments with the results \<open>args\<close>. The types are certified again; the
  type of a constant that is no abbreviation is kept as it is.
\<close>

fun need_expand :: "(name \<Rightarrow> pterm option) \<Rightarrow> pterm \<Rightarrow> bool" where
  "need_expand abbrs (Const c _) \<longleftrightarrow> abbrs c \<noteq> None"
| "need_expand abbrs (Abs _ _ t) \<longleftrightarrow> need_expand abbrs t"
| "need_expand abbrs (t $ u) \<longleftrightarrow> need_expand abbrs t \<or> need_expand abbrs u"
| "need_expand abbrs _ \<longleftrightarrow> False"

fun expand_term :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> (name \<Rightarrow> ptyp option) \<Rightarrow>
    (name \<Rightarrow> pterm option) \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> pterm option" where
  "expand_term alg td ctab abbrs (t $ u) args =
    (case expand_term alg td ctab abbrs u [] of
      None \<Rightarrow> None
    | Some u' \<Rightarrow> expand_term alg td ctab abbrs t (u' # args))"
| "expand_term alg td ctab abbrs (Const c T) args =
    (case certify_typ alg td T of
      None \<Rightarrow> None
    | Some T' \<Rightarrow>
        (case ctab c of
          None \<Rightarrow> None
        | Some U \<Rightarrow>
            if \<not> raw_instance T' U then None
            else
              (case abbrs c of
                Some rhs \<Rightarrow> map_option (\<lambda>r. betapplys r args) (expand_atom T' U rhs)
              | None \<Rightarrow> Some (list_comb (Const c T) args))))"
| "expand_term alg td ctab abbrs (Abs x T t) args =
    (case certify_typ alg td T of
      None \<Rightarrow> None
    | Some T' \<Rightarrow>
        map_option (\<lambda>t'. list_comb (Abs x T' t') args) (expand_term alg td ctab abbrs t []))"
| "expand_term alg td ctab abbrs (Free x T) args =
    map_option (\<lambda>T'. list_comb (Free x T') args) (certify_typ alg td T)"
| "expand_term alg td ctab abbrs (Var v T) args =
    map_option (\<lambda>T'. list_comb (Var v T') args) (certify_typ alg td T)"
| "expand_term alg td ctab abbrs (Bound i) args = Some (list_comb (Bound i) args)"

text \<open>The function \<open>term\<close> of \<open>Consts.certify\<close>, for a term without abbreviations: the types
  are certified again, and each constant is declared, at an instance of its type scheme.\<close>

fun certify_plain :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> (name \<Rightarrow> ptyp option) \<Rightarrow>
    pterm \<Rightarrow> pterm option" where
  "certify_plain alg td ctab (Const c T) =
    (case certify_typ alg td T of
      None \<Rightarrow> None
    | Some T' \<Rightarrow>
        (case ctab c of
          None \<Rightarrow> None
        | Some U \<Rightarrow> if raw_instance T' U then Some (Const c T') else None))"
| "certify_plain alg td ctab (Free x T) = map_option (Free x) (certify_typ alg td T)"
| "certify_plain alg td ctab (Var v T) = map_option (Var v) (certify_typ alg td T)"
| "certify_plain alg td ctab (Bound i) = Some (Bound i)"
| "certify_plain alg td ctab (Abs x T t) =
    (case certify_typ alg td T of
      None \<Rightarrow> None
    | Some T' \<Rightarrow> map_option (Abs x T') (certify_plain alg td ctab t))"
| "certify_plain alg td ctab (t $ u) =
    (case certify_plain alg td ctab t of
      None \<Rightarrow> None
    | Some t' \<Rightarrow> map_option (App t') (certify_plain alg td ctab u))"

definition consts_certify :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> (name \<Rightarrow> ptyp option) \<Rightarrow>
    (name \<Rightarrow> pterm option) \<Rightarrow> pterm \<Rightarrow> pterm option" where
  "consts_certify alg td ctab abbrs t =
    (if need_expand abbrs t then expand_term alg td ctab abbrs t [] else certify_plain alg td ctab t)"

text \<open>\<open>Sign.certify_term\<close>: the type is that of the term before \<open>Consts.certify\<close>.\<close>

definition certify_term :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> (name \<Rightarrow> ptyp option) \<Rightarrow>
    (name \<Rightarrow> pterm option) \<Rightarrow> pterm \<Rightarrow> (pterm \<times> ptyp) option" where
  "certify_term alg td ctab abbrs tm =
    (if \<not> check_vars tm then None
     else
      (case certify_types alg td tm of
        None \<Rightarrow> None
      | Some t \<Rightarrow>
          (case typ_of [] t of
            None \<Rightarrow> None
          | Some T \<Rightarrow> map_option (\<lambda>t'. (t', T)) (consts_certify alg td ctab abbrs t))))"


subsection \<open>The records of the kernel\<close>

text \<open>
  \<open>Thm.global_ctyp_of\<close> and \<open>Thm.global_cterm_of\<close>: the type or term with its maximal index and
  its sorts.
\<close>

definition global_ctyp_of :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> ptyp \<Rightarrow>
    (ptyp \<times> integer \<times> psort list) option" where
  "global_ctyp_of alg td T =
    map_option (\<lambda>T'. (T', maxidx_typ T' (-1), insert_typ_sorts T' [])) (certify_typ alg td T)"

definition global_cterm_of :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> (name \<Rightarrow> ptyp option) \<Rightarrow>
    (name \<Rightarrow> pterm option) \<Rightarrow> pterm \<Rightarrow> (cterm_rep \<times> psort list) option" where
  "global_cterm_of alg td ctab abbrs tm =
    map_option (\<lambda>(t, T). (CTerm t T (maxidx_of_term t), insert_term_sorts t []))
      (certify_term alg td ctab abbrs tm)"

end
