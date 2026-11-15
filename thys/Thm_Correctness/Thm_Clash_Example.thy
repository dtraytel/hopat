section \<open>A Derivation on a Theorem With a Variable Name at Two Types\<close>

theory Thm_Clash_Example
  imports Thm_Example
begin

text \<open>
  The rules of \<^const>\<open>derivable\<close> for \<open>assumption\<close>, \<open>flexflex_rule\<close>, \<open>bicompose\<close> and
  \<open>biresolution\<close> do not ask for one type for each name of a schematic variable; they ask that the
  environment of the result binds no name that occurs with two types. This theory gives a
  derivation in the signature \<^const>\<open>pure0\<close> that uses this: a proof by assumption on a state in
  which \<open>?x\<close> occurs with two types, whose unifier binds another variable. The run of the model
  of the unifier is computed by simplification.
\<close>

text \<open>
  The state: \<open>(H \<Longrightarrow> ?y) \<Longrightarrow> (H \<Longrightarrow> ?y)\<close> with \<open>H = (?x \<Longrightarrow> (\<And>a. ?x a))\<close>, where \<open>?x\<close> has the type
  \<open>prop\<close> at its first and the type \<open>prop \<Rightarrow> prop\<close> at its second occurrence. It is the result of
  \<open>trivial\<close> on a certified term.
\<close>

definition Vx :: pterm where "Vx = Var (STR ''x'', 0) propT"
definition Vx' :: pterm where "Vx' = Var (STR ''x'', 0) (propT \<rightarrow>\<^sub>T propT)"
definition Vy :: pterm where "Vy = Var (STR ''y'', 0) propT"

definition H1 :: pterm where
  "H1 = mk_implies Vx (all_const propT $ Abs STR ''a'' propT (Vx' $ Bound 0))"

definition ct1 :: cterm_data where
  "ct1 = \<lparr>cd_rep = CTerm (mk_implies H1 Vy) propT 0, cd_sorts = {}, cd_sign = pure0\<rparr>"

definition st1 :: thm_data where
  "st1 = mk_thm (mk_rep 0 [] (mk_implies (mk_implies H1 Vy) (mk_implies H1 Vy))) {} [] pure0
    (returnW trivial_proof) (ztrivial_proof ztargs0 (mk_implies H1 Vy))"

text \<open>
  Proof by assumption on its first subgoal \<open>H \<Longrightarrow> ?y\<close>: the sequence of \<^const>\<open>assumption\<close>, the
  unifier of \<open>H\<close> and \<open>?y\<close> (pattern unification binds \<open>?y\<close> to \<open>H\<close>), and the first result of the
  sequence, the theorem \<open>H \<Longrightarrow> H\<close>.
\<close>

definition cfg1 :: cfg where "cfg1 = Cfg alg0 60 50 False False 0"

definition s1 :: "seq aseq" where
  "s1 = AQ_Try (ACtx 0 [] [] (mk_implies H1 Vy) (mk_implies H1 Vy) [] Vy) [H1] 1"

lemmas w_defs = H1_def Vx_def Vx'_def Vy_def mk_implies_def all_const_def implies_def

definition env1 :: env where
  "env1 = Envir 0 (vt_update ((STR ''y'', 0), (propT, H1)) vt_empty) vt_empty"

lemma unify1: "unify alg0 H1 Vy (empty_env 0) = return env1"
  apply (simp add: unify_def unif.simps w_defs head_norm.simps flexrigid_def occurs.simps proj_def
      lookup_def empty_env_def strip_comb_def ints_of'_def update_def update_new_def vt_defined_lookup)
  apply (simp add: handle_def return_def env1_def w_defs)
  done

lemma unifiers1: "unifiers alg0 (empty_env 0) [(H1, Vy)] = return (S_Single (El_R env1 []))"
  by (simp add: unifiers_def unify1 handle_def return_def bindM_def)

lemma cu1: "could_unify H1 Vy"
  by (subst could_unify.simps) (simp add: w_defs)

lemma vt_is_empty_iff: "vt_is_empty t \<longleftrightarrow> (\<forall>k. vt_lookup t k = None)"
  by transfer auto

lemma nt1: "norm_term env1 (mk_implies H1 Vy) = return (mk_implies H1 H1)"
  apply (simp add: norm_term_def env1_def env_is_empty_def vt_is_empty_iff)
  apply (simp add: norm_term1.simps w_defs lookup1_def)
  done

definition r1 :: ares where
  "r1 = ARes env1 1 \<lparr>th_maxidx = 0, th_tpairs = [], th_prop = mk_implies H1 H1\<rparr>"

lemma ne1: "\<not> env_is_empty env1"
  by (simp add: env1_def env_is_empty_def vt_is_empty_iff)

definition s1' :: "seq aseq" where
  "s1' = AQ_Map (ACtx 0 [] [] (mk_implies H1 Vy) (mk_implies H1 Vy) [] Vy) 1 S_Empty [] 2"

lemma a1: "okT (apull (unify_ops cfg1 vl) s1) (Some (r1, s1'))"
  unfolding s1'_def
  apply (subst apull.simps)
  apply (simp add: s1_def cu1 unify_ops_def cfg1_def unifiers1[unfolded empty_env_def] empty_env_def)
  apply (subst apull.simps)
  apply (simp add: upull_def pull.simps newth_def ne1 nt1 r1_def)
  apply (simp add: env1_def)
  done

text \<open>The premises of the rules \<open>trivial\<close> and \<open>assumption\<close> of \<^const>\<open>derivable\<close>:\<close>

lemmas vars_thm0 = pure_sig_gen.vars_thm_def[OF pure_sig0[of "\<lambda>_. 0", unfolded pure_sig_def]]
lemmas tvars_thm0 = pure_sig_gen.tvars_thm_def[OF pure_sig0[of "\<lambda>_. 0", unfolded pure_sig_def]]
lemmas vtcons0 = pure_sig_gen.vtcons_def[OF pure_sig0[of "\<lambda>_. 0", unfolded pure_sig_def]]

lemma cert0 [simp]: "cert_typ alg0 (\<lambda>_. 0) (propT \<rightarrow>\<^sub>T propT)"
  "cert_typ alg0 (\<lambda>_. 0) (propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT)"
  "cert_typ alg0 (\<lambda>_. 0) ((propT \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT)"
  by (simp_all add: cert_typ_def propT_def tarity_def)

lemma const0 [simp]: "const_typ_ok ctab0 STR ''Pure.imp'' (propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT)"
  "const_typ_ok ctab0 STR ''Pure.all'' ((propT \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT)"
  by (simp_all add: const_typ_ok_def propT_def)

lemma typing_ct1: "typing0 e (mk_implies H1 Vy) propT"
  unfolding w_defs by (force intro: typing0_intros)

lemma cterm_ok_ct1: "cterm_ok ct1"
  using typing_ct1 by (auto simp: cterm_ok_def ct1_def cterm_wf0 closed_def ibelow0 w_defs propT_def)

lemma derivable_st1: "derivable st1"
  using derivable.trivial[OF cterm_ok_ct1, of "mk_rep 0 [] (mk_implies (mk_implies H1 Vy) (mk_implies H1 Vy))"]
  by (simp add: st1_def ct1_def trivial_def)

lemma assumption1': "assumption 1 (mk_rep 0 [] (mk_implies (mk_implies H1 Vy) (mk_implies H1 Vy))) = returnW s1"
  by (simp add: assumption_def dest_state_def mk_rep_def s1_def w_defs strip_prems.simps
      assum_problems_def strip_assums_all.simps strip_assums_imp.simps)

lemma assumption1: "okT (assumption 1 (rp st1)) s1"
  using assumption1' by (simp add: st1_def mk_thm_def mk_rep_def thm_rep.truncate_def)

lemma scons_st1: "data_scons st1"
  by (simp add: data_scons_def st1_def mk_rep_def tvars_thm0 scons_def w_defs propT_def)

lemma clash_st1: "data_clash st1 = {(STR ''x'', 0)}"
  by (auto simp: data_clash_def data_vars_def st1_def mk_rep_def vars_thm0 vclash_def w_defs propT_def)

lemma binds1: "binds_none (ar_env r1) (data_clash st1)"
  by (simp add: clash_st1 binds_none_def r1_def env1_def)

text \<open>
  The environment binds \<open>?y\<close> and not \<open>?x\<close>, the only name with two types. So the result is
  derivable, although the state does not have one type for each name:
\<close>

theorem derivable_clash: "derivable (ares_data st1 (aseq_ctx s1) r1)"
  by (rule derivable.assumption[OF derivable_st1 _ scons_st1 assumption1 aresult.First[OF a1] binds1])
    (simp add: cfg1_def st1_def)

lemma not_cons_st1: "\<not> data_cons st1"
  by (auto simp: data_cons_def st1_def mk_rep_def vars_thm0 vtcons0 w_defs propT_def)

lemma prop_clash: "th_prop (ares_data st1 (aseq_ctx s1) r1) = mk_implies H1 H1"
  by (simp add: ares_data_def r1_def)

text \<open>Hence it satisfies the invariant of theorems:\<close>

corollary dok_clash: "dok TYPE('u) (ares_data st1 (aseq_ctx s1) r1)"
  by (rule derivable_sound[OF derivable_clash])

end
