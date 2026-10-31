section \<open>Code Generation: \<open>bicompose_aux\<close> and \<open>biresolution\<close> for \<open>thm.ML\<close>\<close>

theory Pure_Bicompose_Code
  imports Pure_Biresolution Pure_ZTerm "Pure_Pattern.Pure_Pattern_Code"
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

text \<open>
  Tight types, terms and proofs are those of \<^file>\<open>~~/src/Pure/zterm.ML\<close>, with the tables
  \<open>ZTVars\<close> and \<open>ZVars\<close>; \<^const>\<open>zv_dest\<close> is \<open>ZVars.dest\<close> (in the order of the keys).
\<close>

code_printing
  type_constructor ztyp \<rightharpoonup> (SML) "ztyp"
| constant ZTVar \<rightharpoonup> (SML) "ZTVar/ ((_),/ (_))"
| constant ZFun \<rightharpoonup> (SML) "ZFun/ ((_),/ (_))"
| constant ZProp \<rightharpoonup> (SML) "ZProp"
| constant ZType0 \<rightharpoonup> (SML) "ZType0"
| constant ZType1 \<rightharpoonup> (SML) "ZType1/ ((_),/ (_))"
| constant ZType \<rightharpoonup> (SML) "ZType/ ((_),/ (_))"
| type_constructor zterm \<rightharpoonup> (SML) "zterm"
| constant ZVar \<rightharpoonup> (SML) "ZVar/ ((_),/ (_))"
| constant ZBound \<rightharpoonup> (SML) "ZBound"
| constant ZConst0 \<rightharpoonup> (SML) "ZConst0"
| constant ZConst1 \<rightharpoonup> (SML) "ZConst1/ ((_),/ (_))"
| constant ZConst \<rightharpoonup> (SML) "ZConst/ ((_),/ (_))"
| constant ZAbs \<rightharpoonup> (SML) "ZAbs/ ((_),/ (_),/ (_))"
| constant ZApp \<rightharpoonup> (SML) "ZApp/ ((_),/ (_))"
| constant ZOfclass \<rightharpoonup> (SML) "OFCLASS/ ((_),/ (_))"
| class_instance ztyp :: equal \<rightharpoonup> (SML) -
| class_instance zterm :: equal \<rightharpoonup> (SML) -
| constant "HOL.equal :: ztyp \<Rightarrow> ztyp \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : ztyp) = _)"
| constant "HOL.equal :: zterm \<Rightarrow> zterm \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : zterm) = _)"
| type_constructor ztvtab \<rightharpoonup> (SML) "_ ZTVars.table"
| constant zt_map \<rightharpoonup> (SML) "(fn f => ZTVars.map (K f))"
| type_constructor zvtab \<rightharpoonup> (SML) "_ ZVars.table"
| constant zv_empty \<rightharpoonup> (SML) "ZVars.empty"
| constant zv_lookup \<rightharpoonup> (SML) "ZVars.lookup"
| constant zv_update \<rightharpoonup> (SML) "ZVars.update"
| constant zv_map \<rightharpoonup> (SML) "(fn f => ZVars.map (K f))"
| constant zv_dest \<rightharpoonup> (SML) "ZVars.dest"
| type_constructor zproof_name \<rightharpoonup> (SML) "zproof'_name"
| type_constructor zproof \<rightharpoonup> (SML) "zproof"
| constant ZNop \<rightharpoonup> (SML) "ZNop"
| constant ZConstp \<rightharpoonup> (SML) "ZConstp"
| constant ZBoundp \<rightharpoonup> (SML) "ZBoundp"
| constant ZAbst \<rightharpoonup> (SML) "ZAbst/ ((_),/ (_),/ (_))"
| constant ZAbsp \<rightharpoonup> (SML) "ZAbsp/ ((_),/ (_),/ (_))"
| constant ZAppt \<rightharpoonup> (SML) "ZAppt/ ((_),/ (_))"
| constant ZAppp \<rightharpoonup> (SML) "ZAppp/ ((_),/ (_))"
| constant ZHyp \<rightharpoonup> (SML) "ZHyp"
| constant OFCLASSp \<rightharpoonup> (SML) "OFCLASSp/ ((_),/ (_))"

declare [[code abort: zt_map zv_empty zv_lookup zv_update zv_map zv_dest]]

declare beta_norm_term.simps[code] beta_norm_prooft.simps[code] znorm_type_aux.simps[code]
  znorm_term_aux.simps[code]

text \<open>Code equations of recursive functions defined by \<^theory_text>\<open>partial_function\<close>.\<close>

declare norm_term1.simps[code] norm_term2.simps[code] bpull.simps[code]

text \<open>The exported functions.\<close>

export_code bicompose_aux bpull ren_term BOps BRes NewAs
  lift_proof bicompose_proof map_proof_terms Ok Err
  zlift_proof zbicompose_proof ZOk ZErr ZExn BAD_INST ZOption
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
