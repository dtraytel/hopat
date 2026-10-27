section \<open>Code Generation: a Drop-in Replacement for \<open>pattern.ML\<close>\<close>

theory Pure_Pattern_Code
  imports Pure_Pattern
begin

text \<open>
  The HOL model of Pure's data structures is mapped onto the actual ML data structures of
  Isabelle/Pure: types and terms onto \<open>typ\<close> and \<open>term\<close> (\<^file>\<open>~~/src/Pure/term.ML\<close>), tables
  onto \<open>Vartab\<close>, environments onto \<open>Envir.env\<close>, and the class algebra onto \<open>Sorts.algebra\<close>.
  Hence the generated code operates directly on Pure's terms, and can be wrapped into a
  structure \<open>Pattern\<close> with the signature \<open>PATTERN\<close> (see file \<open>pattern_wrapper.ML\<close>).

  The mapping of the abstract operations (tables, class algebra, \<open>Name.aT\<close>) is the only
  unverified part of the setup.
\<close>

code_printing
  type_constructor ptyp \<rightharpoonup> (SML) "typ"
| constant Type \<rightharpoonup> (SML) "Type/ ((_),/ (_))"
| constant TFree \<rightharpoonup> (SML) "TFree/ ((_),/ (_))"
| constant TVar \<rightharpoonup> (SML) "TVar/ ((_),/ (_))"
| type_constructor pterm \<rightharpoonup> (SML) "term"
| constant Const \<rightharpoonup> (SML) "Const/ ((_),/ (_))"
| constant Free \<rightharpoonup> (SML) "Free/ ((_),/ (_))"
| constant Var \<rightharpoonup> (SML) "Var/ ((_),/ (_))"
| constant Bound \<rightharpoonup> (SML) "Bound"
| constant Abs \<rightharpoonup> (SML) "Abs/ ((_),/ (_),/ (_))"
| constant App \<rightharpoonup> (SML) infixl 9 "$"
| class_instance ptyp :: equal \<rightharpoonup> (SML) -
| class_instance pterm :: equal \<rightharpoonup> (SML) -
| constant "HOL.equal :: ptyp \<Rightarrow> ptyp \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : typ) = _)"
| constant "HOL.equal :: pterm \<Rightarrow> pterm \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : term) = _)"

code_printing
  type_constructor vartab \<rightharpoonup> (SML) "_ Vartab.table"
| constant vt_empty \<rightharpoonup> (SML) "Vartab.empty"
| constant vt_lookup \<rightharpoonup> (SML) "Vartab.lookup"
| constant vt_update \<rightharpoonup> (SML) "Vartab.update"
| constant vt_defined \<rightharpoonup> (SML) "Vartab.defined"
| constant vt_is_empty \<rightharpoonup> (SML) "Vartab.is'_empty"

code_printing
  type_constructor env \<rightharpoonup> (SML) "Envir.env"
| constant Envir \<rightharpoonup> (SML) "Envir.Envir/ {maxidx = _,/ tenv = _,/ tyenv = _}"
| constant maxidx \<rightharpoonup> (SML) "Envir.maxidx'_of"
| constant tenv \<rightharpoonup> (SML) "Envir.term'_env"
| constant tyenv \<rightharpoonup> (SML) "Envir.type'_env"

code_printing
  type_constructor algebra \<rightharpoonup> (SML) "Sorts.algebra"
| constant class_less \<rightharpoonup> (SML) "Sorts.class'_less/ _/ ((_),/ (_))"
| constant arities \<rightharpoonup> (SML) "Symtab.lookup'_list/ (Sorts.arities'_of/ _)"
| constant aT \<rightharpoonup> (SML) "Name.aT"

text \<open>
  The operations on tables and the class algebra are implemented by the corresponding ML
  operations; their logical definitions are not used for code generation.
\<close>

declare [[code abort: vt_empty vt_lookup vt_update vt_defined vt_is_empty class_less arities]]

text \<open>Code equations of recursive functions defined by \<^theory_text>\<open>partial_function\<close>.\<close>

declare devar.simps[code] type_occurs.simps[code] unified_aux.simps[code] meet.simps[code]
  unify_aux.simps[code] head_norm.simps[code] norm_type_aux.simps[code] occurs.simps[code]
  pr.simps[code] unif.simps[code] fo_mtch.simps[code] mtch.simps[code]

text \<open>The exported functions: the operations of signature \<open>PATTERN\<close>.\<close>

export_code unify_types unify match first_order_match pattern
  Ok Err Unif Pattern Match TUnify Type_Match Class_Error Type_Error Term_Error Failure Subscript
  Unequal_Lengths Dup No_Trace Typ_Clash Clash Clash_BB Clash_B Proj_Fail Ocheck_Fail
  No_Classrel No_Arity No_Subsort
  in SML module_name Pattern_Generated file_prefix pattern_generated

end
