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
  constructors, the type schemes of the constants, and the set of the constants that are
  abbreviations. Two parts of the code are left out. \<open>Consts.certify\<close> expands the
  abbreviations of a term; the model has no result for a term with such a constant
  (\<open>has_abbrev\<close>). \<open>Soft_Type_System.global_purge\<close> is the identity unless a theory installs a
  soft type system.
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

text \<open>\<open>Type.raw_instance (T, U)\<close> (\<open>could_match\<close> is a filter for it):\<close>

definition raw_instance :: "ptyp \<Rightarrow> ptyp \<Rightarrow> bool" where
  "raw_instance T U \<longleftrightarrow> raw_match U T vt_empty \<noteq> None"

text \<open>
  \<open>Consts.certify\<close> for a term without abbreviations and with certified types: each constant
  is declared, at an instance of its type scheme.
\<close>

fun certify_consts :: "(name \<Rightarrow> ptyp option) \<Rightarrow> pterm \<Rightarrow> bool" where
  "certify_consts ctab (Const c T) \<longleftrightarrow> (case ctab c of None \<Rightarrow> False | Some U \<Rightarrow> raw_instance T U)"
| "certify_consts ctab (Abs _ _ t) \<longleftrightarrow> certify_consts ctab t"
| "certify_consts ctab (t $ u) \<longleftrightarrow> certify_consts ctab t \<and> certify_consts ctab u"
| "certify_consts ctab _ \<longleftrightarrow> True"

fun has_abbrev :: "(name \<Rightarrow> bool) \<Rightarrow> pterm \<Rightarrow> bool" where
  "has_abbrev abbr (Const c _) \<longleftrightarrow> abbr c"
| "has_abbrev abbr (Abs _ _ t) \<longleftrightarrow> has_abbrev abbr t"
| "has_abbrev abbr (t $ u) \<longleftrightarrow> has_abbrev abbr t \<or> has_abbrev abbr u"
| "has_abbrev abbr _ \<longleftrightarrow> False"

text \<open>\<open>Sign.certify_term\<close>, for terms whose constants are not abbreviations:\<close>

definition certify_term :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> (name \<Rightarrow> ptyp option) \<Rightarrow>
    (name \<Rightarrow> bool) \<Rightarrow> pterm \<Rightarrow> (pterm \<times> ptyp) option" where
  "certify_term alg td ctab abbr tm =
    (if \<not> check_vars tm then None
     else
      (case certify_types alg td tm of
        None \<Rightarrow> None
      | Some t \<Rightarrow>
          (case typ_of [] t of
            None \<Rightarrow> None
          | Some T \<Rightarrow>
              if has_abbrev abbr t then None
              else if certify_consts ctab t then Some (t, T) else None)))"


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
    (name \<Rightarrow> bool) \<Rightarrow> pterm \<Rightarrow> (cterm_rep \<times> psort list) option" where
  "global_cterm_of alg td ctab abbr tm =
    map_option (\<lambda>(t, T). (CTerm t T (maxidx_of_term t), insert_term_sorts t []))
      (certify_term alg td ctab abbr tm)"

end
