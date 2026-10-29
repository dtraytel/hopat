section \<open>Code Generation: \<open>bicompose_aux\<close> for \<open>thm.ML\<close>\<close>

theory Pure_Bicompose_Code
  imports Pure_Bicompose "Pure_Pattern.Pure_Pattern_Code"
begin

text \<open>
  The mapping of Pure's types, terms, tables, environments and class algebra onto the ML data
  structures is the one of theory \<^theory>\<open>Pure_Pattern.Pure_Pattern_Code\<close>. In addition,
  \<^const>\<open>vt_above\<close> is \<open>Envir.above\<close> on one table: the keys of \<open>Vartab\<close> are ordered by
  their index first (\<open>Term_Ord.fast_indexname_ord\<close>), so the least key has the least index.
  The length of a literal (\<^const>\<open>literal_size\<close>) is \<open>String.size\<close>, which also works for
  names with non-ASCII characters.

  The generated code is placed in front of the structure \<open>Thm\<close> of \<open>thm.ML\<close>, and the
  function \<open>bicompose_aux\<close> of \<open>thm.ML\<close> is replaced by the wrapper of file
  \<open>bicompose_wrapper.ML\<close>. The wrapper instantiates the operations of the model with Pure's
  \<open>Unify.unifiers\<close>, \<open>Seq.pull\<close> and \<open>Name.variant_list []\<close>, and builds the theorems.
\<close>

code_printing
  constant literal_size \<rightharpoonup> (SML) "IntInf.fromInt (String.size _)"
| constant vt_above \<rightharpoonup> (SML)
    "(fn tab => fn lim => case Vartab.min tab of NONE => true | SOME ((x, i), y) => i > lim)"

declare [[code abort: literal_size vt_above]]

text \<open>Code equations of recursive functions defined by \<^theory_text>\<open>partial_function\<close>.\<close>

declare norm_term1.simps[code] norm_term2.simps[code] bpull.simps[code]

text \<open>The exported functions.\<close>

export_code bicompose_aux bpull ren_term BOps BRes NewAs
  TOk TErr UExn THM ERROR COMPOSE Orule Orule_State
  PExn CANTUNIFY ASSIGN CHANGE_FAIL Bind
  Ev_Unif Ev_Loss Ev_Dpairs Ev_Failure_Node Ev_Bound_Exceeded
  Unif Pattern Match TUnify Type_Match Class_Error Type_Error Term_Error Failure Subscript
  Unequal_Lengths Dup No_Trace Typ_Clash Clash Clash_BB Clash_B Proj_Fail Ocheck_Fail
  No_Classrel No_Arity No_Subsort
  in SML module_name Bicompose_Generated file_prefix bicompose_generated

end
