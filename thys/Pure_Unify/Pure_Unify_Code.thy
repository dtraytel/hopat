section \<open>Code Generation: a Drop-in Replacement for \<open>unify.ML\<close>\<close>

theory Pure_Unify_Code
  imports Pure_Unify "Pure_Pattern.Pure_Pattern_Code"
begin

text \<open>
  The mapping of Pure's types, terms, tables, environments and class algebra onto the ML
  data structures is the one of theory \<^theory>\<open>Pure_Pattern.Pure_Pattern_Code\<close>. The generated
  code is wrapped into a structure \<open>Unify\<close> with signature \<open>UNIFY\<close> by the functor in file
  \<open>unify_wrapper.ML\<close>, which turns the sequences of the model into \<open>Seq.seq\<close>, prints the
  tracing messages, and raises Pure's exceptions.
\<close>

text \<open>Code equations of recursive functions defined by \<^theory_text>\<open>partial_function\<close>.\<close>

declare vupdate.simps[code] body_type.simps[code] binder_types.simps[code]
  norm_term1.simps[code] norm_term2.simps[code] etif.simps[code] occur.simps[code]
  head_of_in.simps[code] rocc.simps[code] SIMPL0.simps[code] SIMPL.simps[code] pull.simps[code]

text \<open>The exported functions.\<close>

export_code hounifiers pull smash_flexflex Cfg
  UOk UErr PExn CANTUNIFY ASSIGN CHANGE_FAIL Bind
  Ev_Unif Ev_Loss Ev_Dpairs Ev_Failure_Node Ev_Bound_Exceeded
  El_R El_E El_C El_D
  Unif Pattern Match TUnify Type_Match Class_Error Type_Error Term_Error Failure Subscript
  Unequal_Lengths Dup No_Trace Typ_Clash Clash Clash_BB Clash_B Proj_Fail Ocheck_Fail
  No_Classrel No_Arity No_Subsort
  in SML module_name Unify_Generated file_prefix unify_generated

end
