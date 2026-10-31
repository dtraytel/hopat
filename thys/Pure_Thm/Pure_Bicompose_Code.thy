section \<open>Code Generation: \<open>bicompose_aux\<close> and \<open>biresolution\<close> for \<open>thm.ML\<close>\<close>

theory Pure_Bicompose_Code
  imports Pure_Biresolution Pure_Proofterm "Pure_Pattern.Pure_Pattern_Code"
begin

text \<open>
  The mapping of Pure's types, terms, tables, environments and class algebra onto the ML data
  structures is the one of theory \<^theory>\<open>Pure_Pattern.Pure_Pattern_Code\<close>. In addition,
  \<^const>\<open>vt_above\<close> is \<open>Envir.above\<close> on one table: the keys of \<open>Vartab\<close> are ordered by
  their index first (\<open>Term_Ord.fast_indexname_ord\<close>), so the least key has the least index.
  The length of a literal (\<^const>\<open>literal_size\<close>) is \<open>String.size\<close>, which also works for
  names with non-ASCII characters.

  The generated code is placed in front of the structure \<open>Thm\<close> of \<open>thm.ML\<close>, and the
  functions \<open>bicompose_aux\<close> and \<open>biresolution\<close> of \<open>thm.ML\<close> are replaced by the wrapper of file
  \<open>bicompose_wrapper.ML\<close>; \<open>lift_rule\<close> of \<open>thm.ML\<close> takes the logical part of the lifted rule
  from \<^const>\<open>lift_rule\<close>. The wrapper instantiates the operations of the model with Pure's
  \<open>Unify.unifiers\<close>, \<open>Seq.pull\<close> and \<open>Name.variant_list []\<close>, and builds the theorems.
\<close>

code_printing
  constant literal_size \<rightharpoonup> (SML) "IntInf.fromInt (String.size _)"
| constant vt_above \<rightharpoonup> (SML)
    "(fn tab => fn lim => case Vartab.min tab of NONE => true | SOME ((x, i), y) => i > lim)"

declare [[code abort: literal_size vt_above]]

text \<open>
  Proofs are Pure's proofs (\<open>Proofterm.proof\<close>); the header of a theorem box is accessed
  and updated through its record fields \<open>prop\<close> and \<open>types\<close>; \<^const>\<open>vt_map\<close> is
  \<open>Vartab.map\<close>.
\<close>

code_printing
  type_constructor "prf" \<rightharpoonup> (SML) "Proofterm.proof"
| constant MinProof \<rightharpoonup> (SML) "Proofterm.MinProof"
| constant PBound \<rightharpoonup> (SML) "Proofterm.PBound"
| constant Abst \<rightharpoonup> (SML) "Proofterm.Abst/ ((_),/ (_),/ (_))"
| constant AbsP \<rightharpoonup> (SML) "Proofterm.AbsP/ ((_),/ (_),/ (_))"
| constant PAppt \<rightharpoonup> (SML) infixl 8 "%"
| constant PAppp \<rightharpoonup> (SML) infixl 8 "%%"
| constant Hyp \<rightharpoonup> (SML) "Proofterm.Hyp"
| constant PAxm \<rightharpoonup> (SML) "Proofterm.PAxm/ ((_),/ (_),/ (_))"
| constant PClass \<rightharpoonup> (SML) "Proofterm.PClass/ ((_),/ (_))"
| constant Oracle \<rightharpoonup> (SML) "Proofterm.Oracle/ ((_),/ (_),/ (_))"
| constant PThm \<rightharpoonup> (SML) "Proofterm.PThm"
| type_constructor thm_header \<rightharpoonup> (SML) "Proofterm.thm'_header"
| type_constructor thm_body \<rightharpoonup> (SML) "Proofterm.thm'_body"
| constant hd_prop \<rightharpoonup> (SML) "(fn h : Proofterm.thm'_header => #prop h)"
| constant hd_types \<rightharpoonup> (SML) "(fn h : Proofterm.thm'_header => #types h)"
| constant hd_set_types \<rightharpoonup> (SML)
    "(fn {serial, command'_pos, theory'_name, thm'_name, prop, ...} : Proofterm.thm'_header =>
      fn types => Proofterm.thm'_header serial command'_pos theory'_name thm'_name prop types)"
| constant vt_map \<rightharpoonup> (SML) "(fn f => Vartab.map (K f))"

declare [[code abort: hd_prop hd_types hd_set_types vt_map]]

text \<open>Code equations of recursive functions defined by \<^theory_text>\<open>partial_function\<close>.\<close>

declare norm_term1.simps[code] norm_term2.simps[code] bpull.simps[code]

text \<open>The exported functions.\<close>

export_code bicompose_aux bpull ren_term BOps BRes NewAs
  lift_proof bicompose_proof map_proof_terms Ok Err
  biresolution brstep brrule lift_rule thm_rep.make th_maxidx th_tpairs th_prop
  RS_Done RS_Skip RS_Result
  TOk TErr UExn THM ERROR COMPOSE Orule Orule_State State
  PExn CANTUNIFY ASSIGN CHANGE_FAIL Bind
  Ev_Unif Ev_Loss Ev_Dpairs Ev_Failure_Node Ev_Bound_Exceeded
  Unif Pattern Match TUnify Type_Match Class_Error Type_Error Term_Error Failure Subscript
  Unequal_Lengths Dup No_Trace Typ_Clash Clash Clash_BB Clash_B Proj_Fail Ocheck_Fail
  No_Classrel No_Arity No_Subsort
  in SML module_name Bicompose_Generated file_prefix bicompose_generated

end
