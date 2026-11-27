section \<open>The theorems that the rules derive\<close>

theory Thm_Derivable
  imports Thm_Consistency Thm_Transfer Thm_Hyps Thm_Unconstrain Thm_Bicompose Thm_Cterm Thm_Lift
    Thm_Axiom Thm_Strip_Shyps
begin

text \<open>
  One statement of what the theories \<open>Thm_Rules\<close> to \<open>Thm_Unconstrain\<close> prove rule by rule. The
  predicate \<^term>\<open>derivable\<close> is defined on the data of theorems (\<^typ>\<open>thm_data\<close>), without
  reference to models or to the abstract type \<^typ>\<open>'u pure_thm\<close>: it has one introduction rule per
  inference rule of the kernel, whose premises are the certified terms that the rule takes
  (\<^const>\<open>cterm_ok\<close>; their certification by \<open>Sign.certify\<close> is not modelled), the theorems it takes,
  the success \<open>okT\<close> of the model of the rule (session \<open>Pure_Thm\<close>), and every further condition under
  which the rule is covered. The conclusion gives the data of the new theorem as the wrappers of
  \<open>thm.ML\<close> compute them. Theorem \<open>derivable_sem\<close> states that derivable data are well formed
  and valid in every model of their signature (\<open>dsem\<close>). That their proofs are valid is theorem
  \<open>derivable_proofs\<close> of theory \<open>Thm_Derivable_Proofs\<close>; nothing here depends on it.

  A premise that the model of a rule does not check is a condition that Isabelle does not check
  either. These premises are what the soundness result assumes beyond the code:
  \<^item> equal signatures of the arguments (Isabelle joins the theories of the arguments);
  \<^item> \<^const>\<open>sign_eq\<close>, \<^const>\<open>sign_closed\<close>, \<^const>\<open>sign_axioms\<close>: properties of the signature;
  \<^item> for the rules that unify: one sort for each name of a schematic type variable
    (\<open>data_scons\<close>, \<open>data_scons2\<close>). There is no condition on the names of the schematic
    variables: a name may occur with several types in the arguments, and the unifier may bind it;
  \<^item> the conditions of \<open>unconstrainT\<close>, and that \<open>transfer\<close> goes to an extension of the signature
    (\<open>sign_le\<close>).

  The certified terms and types record finitely many sorts over the classes of their signature
  (\<open>csorts_ok\<close>; theory \<open>Thm_Certify\<close> of session \<open>Thm_Extras\<close> shows this of the results of certification). Theorem
  \<open>derivable_shyps\<close> states that the sort hypotheses of derivable data are of this kind again,
  which \<open>strip_shyps\<close> and \<open>unconstrainT\<close> need.
\<close>


subsection \<open>The invariant on data\<close>

abbreviation (input) rp :: "thm_data \<Rightarrow> thm_rep" where
  "rp d \<equiv> thm_rep.truncate d"

definition dsem :: "'u itself \<Rightarrow> thm_data \<Rightarrow> bool" where
  "dsem U d \<longleftrightarrow> thm_sem U d \<and> cons_ok (th_sign d) (th_constraints d)"

lemma dsem_nosig: "\<not> pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d)) \<Longrightarrow> dsem U d"
  by (auto simp: dsem_def thm_sem_def cons_ok_def)

lemma rep_Abs: "dsem TYPE('u) d \<Longrightarrow> rep_thm (Abs_thm d :: 'u pure_thm) = d"
  by (simp add: dsem_def rep_Abs_thm)

lemma rep_Abs_cterm: "cterm_ok c \<Longrightarrow> rep_cterm (Abs_cterm c) = c"
  by (simp add: Abs_cterm_inverse)

lemma rp_sel [simp]:
  "th_maxidx (rp d) = th_maxidx d" "th_tpairs (rp d) = th_tpairs d" "th_prop (rp d) = th_prop d"
  by (simp_all add: thm_rep.truncate_def)

text \<open>The proofs of the equality rules with two premises, on data:\<close>

definition prf2r :: "(pterm \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf) \<Rightarrow> thm_data \<Rightarrow> thm_data \<Rightarrow> prf P" where
  "prf2r f d1 d2 = bindW (th_proof d1) (\<lambda>p. bindW (th_proof d2) (\<lambda>q.
    case app2_args (th_prop d1) of Some (A, B) \<Rightarrow> returnW (f A B p q) | None \<Rightarrow> raiseW undefined))"

definition zprf2r :: "(ztypargs \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow> zproof Z) \<Rightarrow> thm_data \<Rightarrow> thm_data \<Rightarrow>
    zproof Z" where
  "zprf2r f d1 d2 = bindM (th_zproof d1) (\<lambda>p. bindM (th_zproof d2) (\<lambda>q.
    case app2_args (th_prop d1) of
      Some (A, B) \<Rightarrow> f (pure_sig_gen.ztargs (sg_consts (th_sign d1))) A B p q
    | None \<Rightarrow> raise undefined))"

lemma prf2_raw [simp]: "prf2 f th1 th2 = prf2r f (rep_thm th1) (rep_thm th2)"
  and zprf2_raw [simp]: "zprf2 g th1 th2 = zprf2r g (rep_thm th1) (rep_thm th2)"
  by (simp_all add: prf2_def zprf2_def prf2r_def zprf2r_def)

text \<open>The theorem of a conversion (\<^const>\<open>conv_data\<close>), on data:\<close>

definition conv_datar :: "cterm_data \<Rightarrow> thm_rep \<Rightarrow> thm_data" where
  "conv_datar ct r = mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW reflexive_proof)
    (zreflexive_proof (pure_sig_gen.ztargs (sg_consts (cd_sign ct))) (ct_T (cd_rep ct)) (ct_t (cd_rep ct)))"

lemma conv_data_raw: "conv_data ct r = conv_datar (rep_cterm ct) r"
  by (simp add: conv_data_def conv_datar_def)


text \<open>
  The schematic variables of the data have one type for each name, and the schematic type
  variables one sort (\<^const>\<open>thm_cons\<close>). The soundness theorems do not use the part on the
  variables; it is preserved by the unifying rules (\<open>data_cons_biresolution\<close> to \<open>data_cons_bicompose\<close> below).
  For two theorems together, the part on sorts and the part on the variables:
\<close>

definition data_cons :: "thm_data \<Rightarrow> bool" where
  "data_cons d \<longleftrightarrow> scons (pure_sig_gen.tvars_thm (th_tpairs d) (th_prop d)) \<and>
    pure_sig_gen.vtcons (pure_sig_gen.vars_thm (th_tpairs d) (th_prop d))"

definition data_scons2 :: "thm_data \<Rightarrow> thm_data \<Rightarrow> bool" where
  "data_scons2 d1 d2 \<longleftrightarrow>
    scons (pure_sig_gen.tvars_thm (th_tpairs d1) (th_prop d1) \<union> pure_sig_gen.tvars_thm (th_tpairs d2) (th_prop d2))"

definition data_vcons2 :: "thm_data \<Rightarrow> thm_data \<Rightarrow> bool" where
  "data_vcons2 d1 d2 \<longleftrightarrow>
    pure_sig_gen.vtcons (pure_sig_gen.vars_thm (th_tpairs d1) (th_prop d1) \<union> pure_sig_gen.vars_thm (th_tpairs d2) (th_prop d2))"

lemma bc_scons_raw: "bc_scons th1 th2 \<longleftrightarrow> data_scons2 (rep_thm th1) (rep_thm th2)"
  by (simp add: bc_scons_def data_scons2_def)

text \<open>
  The rules that unify do not need one type for each name of a schematic variable. The part of
  \<open>data_cons\<close> on sorts, and the names with two types (\<^const>\<open>vclash\<close>) in the proof state, the
  lifted rule and the new premises of a result of \<open>biresolution\<close> (which the proof for that rule
  takes as loose names).
\<close>

definition data_scons :: "thm_data \<Rightarrow> bool" where
  "data_scons d \<longleftrightarrow> scons (pure_sig_gen.tvars_thm (th_tpairs d) (th_prop d))"

definition data_vars :: "thm_data \<Rightarrow> (indexname \<times> ptyp) set" where
  "data_vars d = pure_sig_gen.vars_thm (th_tpairs d) (th_prop d)"

definition data_clash_bres :: "thm_data \<Rightarrow> integer \<Rightarrow> thm_data \<Rightarrow> bres \<Rightarrow> indexname set" where
  "data_clash_bres st i rule x = (\<Union>goal\<in>{g. okT (cprem_of (rp st) i) g}.
    vclash (data_vars st \<union>
      pure_sig_gen.vars_thm (th_tpairs (lift_rule goal (th_maxidx st) (rp rule)))
        (th_prop (lift_rule goal (th_maxidx st) (rp rule))) \<union>
      (\<Union>A\<in>set (na_As (br_newas x)). vars A)))"

text \<open>
  The new theorems of the rules that unify, on data (\<^const>\<open>thm_of_ares\<close>, \<^const>\<open>thm_of_fres\<close>,
  \<^const>\<open>thm_of_bc\<close>, \<^const>\<open>thm_of_bres\<close>):
\<close>

definition ares_data :: "thm_data \<Rightarrow> actx \<Rightarrow> ares \<Rightarrow> thm_data" where
  "ares_data st ctx r = with_cons (th_constraints st \<union> env_constraints (ar_env r))
    (mk_thm (ar_thm r) (th_shyps st \<union> env_sorts (ar_env r)) (th_hyps st) (th_sign st)
      (bindW (th_proof st) (ares_proof ctx r))
      (bindM (th_zproof st) (ares_zproof (pure_sig_gen.ztargs (sg_consts (th_sign st))) (rp st) ctx r)))"

definition fres_data :: "thm_data \<Rightarrow> env \<Rightarrow> thm_rep \<Rightarrow> thm_data" where
  "fres_data th env r =
    (if env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u) then th
     else with_cons (env_constraints env) (mk_thm r (th_shyps th \<union> env_sorts env) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (norm_proof_remove_types env))
      (bindM (th_zproof th) (flexflex_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (rp th) env))))"

definition bc_data :: "sign \<Rightarrow> integer \<Rightarrow> thm_data \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> thm_data \<Rightarrow> bres \<Rightarrow> thm_data" where
  "bc_data c i st flatten e rule x = \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x,
    th_prop = br_prop x, th_shyps = th_shyps st \<union> th_shyps rule \<union> env_sorts (br_env x),
    th_hyps = th_hyps st @ th_hyps rule, th_sign = c,
    th_proof = bindW (th_proof rule) (\<lambda>rq. bindW (th_proof st) (\<lambda>sq.
      bc_proof (rp st) i e flatten x rq sq)),
    th_zproof = bindM (th_zproof rule) (\<lambda>rq. bindM (th_zproof st) (\<lambda>sq.
      bc_zproof (pure_sig_gen.ztargs (sg_consts c)) (rp st) i e flatten (rp rule) x rq sq)),
    th_constraints = th_constraints rule \<union> th_constraints st \<union> env_constraints (br_env x)\<rparr>"

definition bres_data :: "sign \<Rightarrow> integer \<Rightarrow> thm_data \<Rightarrow> bool \<Rightarrow> thm_data \<Rightarrow> bres \<Rightarrow> thm_data" where
  "bres_data c i st e rule x = \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x, th_prop = br_prop x,
    th_shyps = th_shyps st \<union> th_shyps rule \<union> env_sorts (br_env x),
    th_hyps = th_hyps st @ th_hyps rule, th_sign = c,
    th_proof = bindW (th_proof rule) (\<lambda>rq. bindW (th_proof st) (\<lambda>sq.
      bires_proof (rp st) i e (rp rule) x rq sq)),
    th_zproof = bindM (th_zproof rule) (\<lambda>rq. bindM (th_zproof st) (\<lambda>sq.
      bires_zproof (pure_sig_gen.ztargs (sg_consts c)) (rp st) i e (rp rule) x rq sq)),
    th_constraints = th_constraints st \<union> th_constraints rule \<union> env_constraints (br_env x)\<rparr>"

lemma thm_of_ares_raw: "thm_of_ares state ctx r = ares_data (rep_thm state) ctx r"
  and thm_of_fres_raw: "thm_of_fres th env r' = fres_data (rep_thm th) env r'"
  and thm_of_bc_raw: "thm_of_bc c i state flatten e rule x = bc_data c i (rep_thm state) flatten e (rep_thm rule) x"
  and thm_of_bres_raw: "thm_of_bres c i state e rule x = bres_data c i (rep_thm state) e (rep_thm rule) x"
  by (simp_all add: thm_of_ares_def ares_data_def thm_of_fres_def fres_data_def thm_of_bc_def bc_data_def
      thm_of_bres_def bres_data_def)

lemma fres_data_sign [simp]: "th_sign (fres_data d env r) = th_sign d"
  by (simp add: fres_data_def)


subsection \<open>Finitely many sorts\<close>

lemma finite_tsorts [simp]: "finite (tsorts T)"
  by (induction T) auto

lemma finite_tm_sorts [simp]: "finite (tm_sorts t)"
  by (induction t) auto

lemma finite_env_sorts [simp]: "finite (env_sorts env)"
proof -
  let ?\<theta> = "tyenv env"
  have "finite (dom (vt_lookup \<theta>))" for \<theta> :: tyenv by transfer simp
  then have f: "finite (dom (vt_lookup ?\<theta>))" .
  have "tyenv_sorts ?\<theta> \<subseteq> (\<Union>v\<in>dom (vt_lookup ?\<theta>). tsorts (snd (the (vt_lookup ?\<theta> v))))"
    unfolding tyenv_sorts_def by force
  moreover have "finite (\<Union>v\<in>dom (vt_lookup ?\<theta>). tsorts (snd (the (vt_lookup ?\<theta> v))))" using f by simp
  ultimately show ?thesis unfolding env_sorts_def by (rule finite_subset)
qed

text \<open>
  The sorts that a certified term or type records, and the sort hypotheses of a theorem: finitely
  many sorts over the classes of the signature.
\<close>

definition csorts_ok :: "sign \<Rightarrow> psort set \<Rightarrow> bool" where
  "csorts_ok c Ss \<longleftrightarrow> finite Ss \<and> (\<forall>S\<in>Ss. sort_ok (sg_alg c) S)"

lemma csorts_ok_Un [simp]: "csorts_ok c (A \<union> B) \<longleftrightarrow> csorts_ok c A \<and> csorts_ok c B"
  and csorts_ok_empty [simp]: "csorts_ok c {}"
  by (auto simp: csorts_ok_def)

lemma tm_sorts_typs: "tm_sorts t = (\<Union>U\<in>typs t. tsorts U)"
  by (induction t) auto

lemma (in pure_sig) typing_tm_sorts: "e \<turnstile> t : T \<Longrightarrow> S \<in> tm_sorts t \<Longrightarrow> sort_ok alg S"
  using typing_typs[of e t T] sorts_ok_tsorts by (fastforce simp: tm_sorts_typs cert_typ_def)

text \<open>
  The conditions of \<open>unconstrainT\<close> without the one on the sort hypotheses, which is an invariant
  of derivable theorems (\<^const>\<open>unc_ok\<close> has it):
\<close>

definition unc_sig_ok :: "(pterm \<Rightarrow> thm_header \<times> thm_body) \<Rightarrow> zthm_name \<Rightarrow> (integer \<Rightarrow> name list) \<Rightarrow> sign \<Rightarrow>
    psort list \<Rightarrow> pterm \<Rightarrow> thm_rep \<Rightarrow> bool" where
  "unc_sig_ok box zn invent c shyps P r \<longleftrightarrow>
    (\<forall>n. n \<le> length (invent (integer_of_nat n)) \<and> distinct (invent (integer_of_nat n))) \<and>
    (\<forall>B. hd_prop (fst (box B)) = B \<and> hd_types (fst (box B)) = None) \<and>
    sign_ofclass c \<and> vars_consistent P \<and>
    (is_prf_sig c \<longrightarrow> unc_box_ok c (th_prop r) \<and>
      (\<forall>z. zunconstrain_proof (pure_sig_gen.ztargs (sg_consts c)) zn invent shyps P = return z \<longrightarrow>
        unc_box_ok c (pure_sig_gen.zdec (sg_consts c) (zbox_prop z))))"

lemma unc_ok_iff:
  "unc_ok box zn invent c shyps P r \<longleftrightarrow>
    unc_sig_ok box zn invent c shyps P r \<and> (\<forall>S\<in>set shyps. sort_ok (sg_alg c) S)"
  unfolding unc_ok_def unc_sig_ok_def by blast


subsection \<open>Derivable theorems\<close>

inductive derivable :: "thm_data \<Rightarrow> bool" where
  assumeI: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> okT (assume_rule (cd_rep ct)) r \<Longrightarrow>
    derivable
     (mk_thm r (cd_sorts ct) [ct_t (cd_rep ct)] (cd_sign ct) (returnW (Hyp (ct_t (cd_rep ct))))
      (zassume_proof (pure_sig_gen.ztargs (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
| implies_intr: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> derivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> okT (implies_intr (cd_rep ct) (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (filter (\<lambda>h.
      \<not> aconv_term (ct_t (cd_rep ct)) h) (th_hyps th)) (th_sign th) (bindW (th_proof th)
      (\<lambda>p. returnW (implies_intr_proof (ct_t (cd_rep ct)) p))) (bindM (th_zproof th)
      (zimplies_intr_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))))))"
| implies_elim: "derivable thAB \<Longrightarrow> derivable thA \<Longrightarrow> th_sign thAB = th_sign thA
    \<Longrightarrow> okT (implies_elim (rp thAB) (rp thA)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints thA \<union> th_constraints thAB) (mk_thm r (th_shyps thAB \<union>
      th_shyps thA) (th_hyps thA @ th_hyps thAB) (th_sign thAB) (bindW (th_proof thAB)
      (\<lambda>p. bindW (th_proof thA) (\<lambda>q. returnW (PAppp p q)))) (bindM (th_zproof
      thAB) (\<lambda>p. bindM (th_zproof thA) (\<lambda>q. return (ZAppp p q))))))"
| forall_intr: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> derivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow> okT (forall_intr (th_hyps th)
    (cd_rep ct) (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (cd_rep
      ct))) (ct_t (cd_rep ct)) p))) (bindM (th_zproof th) (zforall_intr_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) (ct_T (cd_rep ct)) (var_name (ct_t (cd_rep ct))) (ct_t (cd_rep
      ct))))))"
| forall_elim: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> derivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> okT (forall_elim (cd_rep ct) (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (PAppt p (Some (ct_t (cd_rep ct)))))) (bindM
      (th_zproof th) (\<lambda>p. zforall_elim_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
      (ct_t (cd_rep ct)) p))))"
| symmetric: "derivable th \<Longrightarrow> sign_eq (th_sign th) \<Longrightarrow> okT (symmetric (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (symmetric_proof p))) (bindM (th_zproof th) (\<lambda>p. case
      eq_args (th_prop (rp th)) of Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) T t u p | None \<Rightarrow> raise undefined))))"
| transitive: "derivable th1 \<Longrightarrow> derivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (transitive (rp th1) (rp th2)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (bindW (th_proof th1) (\<lambda>p.
      bindW (th_proof th2) (\<lambda>q. case eq_args (th_prop (rp th1)) of Some (T, t1, u)
      \<Rightarrow> returnW (transitive_proof T u p q) | None \<Rightarrow> raiseW undefined)))
      (bindM (th_zproof th1) (\<lambda>p. bindM (th_zproof th2) (\<lambda>q. case (eq_args
      (th_prop (rp th1)), eq_args (th_prop (rp th2))) of (Some (T, t1, u), Some (_, _, t2))
      \<Rightarrow> ztransitive_proof (pure_sig_gen.ztargs (sg_consts (th_sign th1))) T t1 u t2 p q |
      _ \<Rightarrow> raise undefined)))))"
| abstract_rule: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> derivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> sign_eq (th_sign th) \<Longrightarrow> sign_closed (th_sign th)
    \<Longrightarrow> okT (abstract_rule_res b (th_hyps th) (cd_rep ct) (rp th)) (r, U, f, g) \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (cd_rep ct)) p)))
      (bindM (th_zproof th) (zabstract_rule_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_T
      (cd_rep ct)) U b (ct_t (cd_rep ct)) f g))))"
| combination: "derivable th1 \<Longrightarrow> derivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (combination_res (rp th1) (rp
    th2)) (r, T1, U, f, g, t, u) \<Longrightarrow>
    derivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (bindW (th_proof th1) (\<lambda>p.
      bindW (th_proof th2) (\<lambda>q. combination_proof f g t u p q))) (bindM (th_zproof th1)
      (\<lambda>p. bindM (th_zproof th2) (\<lambda>q. zcombination_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th1))) T1 U f g t u p q)))))"
| equal_intr: "derivable th1 \<Longrightarrow> derivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (equal_intr (rp th1) (rp th2)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_intr_proof th1 th2)
      (zprf2r zequal_intr_proof th1 th2)))"
| equal_elim: "derivable th1 \<Longrightarrow> derivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (equal_elim (rp th1) (rp th2)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_elim_proof th1 th2)
      (zprf2r zequal_elim_proof th1 th2)))"
| trivial: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> okT (trivial (cd_rep ct)) r \<Longrightarrow>
    derivable
     (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW trivial_proof) (ztrivial_proof (pure_sig_gen.ztargs
      (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
| weaken: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> derivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> okT (weaken (cd_rep ct) (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (ct_t (cd_rep ct) #
      th_hyps th) (th_sign th) (th_proof th) (th_zproof th)))"
| renamed_prop: "derivable th \<Longrightarrow> okT (renamed_prop P (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (th_proof th)
      (th_zproof th)))"
| incr_indexes: "derivable th \<Longrightarrow> okT (incr_indexes_thm i (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (incr_indexes_prf
      i (th_proof th)) (incr_indexes_zprf i (th_zproof th))))"
| permute_prems: "derivable th \<Longrightarrow> okT (permute_data j k (rp th)) (r, prems', m) \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (permute_prems_proof prems' j m p))) (bindM (th_zproof th)
      (zpermute_prems_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) prems' j m))))"
| rotate_rule: "derivable th \<Longrightarrow> okT (rotate_data k i (rp th)) (r, Bs, Bi', params, asms, m) \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p))) (bindM (th_zproof th)
      (zrotate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi' params asms m))))"
| varifyT_global: "derivable th \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow> okT (varifyT_global vl
    fixed (th_hyps th) (rp th)) (names, r) \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (th_zproof th) (zvarifyT_proof
      names))))"
| adjust_maxidx: "derivable th \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm (adjust_maxidx_thm i (rp th)) (th_shyps th) (th_hyps th)
      (th_sign th) (th_proof th) (th_zproof th)))"
| reflexive: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow> okT (reflexive (cd_rep ct)) r \<Longrightarrow>
    derivable (conv_datar ct r)"
| beta_conversion: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow> okT (beta_conversion full (cd_rep ct)) r \<Longrightarrow>
    derivable (conv_datar ct r)"
| eta_conversion: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow> okT (eta_conversion (cd_rep ct)) r \<Longrightarrow>
    derivable (conv_datar ct r)"
| eta_long_conversion: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow>
    okT (eta_long_conversion (cd_rep ct)) r \<Longrightarrow> derivable (conv_datar ct r)"
| generalize: "derivable th \<Longrightarrow> \<not> (tfrees = [] \<and> frees = []) \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow>
    okT (generalize tfrees frees gi (th_hyps th) (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs th) (th_prop th) p)))
      (bindM (th_zproof th) (zgeneralize_proof tfrees frees gi))))"
| legacy_freezeT: "derivable th \<Longrightarrow> ok (full_prop_of (th_tpairs th) (th_prop th)) P1 \<Longrightarrow>
    okT (legacy_freezeT vl (rp th)) r \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p)))
      (bindM (th_zproof th) (zlegacy_freezeT_proof vl P1))))"
| of_class: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> ct_t (cd_rep ct) = mk_of_class T c \<Longrightarrow>
    tm_sorts (mk_of_class T c) \<subseteq> cd_sorts ct \<Longrightarrow>
    pure_sig_gen.class_const (sg_alg (cd_sign ct)) (sg_consts (cd_sign ct)) (c + STR ''_class'') c \<Longrightarrow>
    sign_eq (cd_sign ct) \<Longrightarrow> okT (Pure_Subst_Rules.of_class (sg_alg (cd_sign ct)) T c) r \<Longrightarrow>
    derivable
     (solve_data (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW (PClass T c))
      (return (OFCLASSp (ztyp_of T) c))))"
| eq_assumption: "derivable th \<Longrightarrow> okT (eq_assumption i (rp th)) (n, r) \<Longrightarrow>
    okT (dest_state (rp th) i) (tpairs, Bs, Bi, C) \<Longrightarrow>
    derivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
      (bindM (th_zproof th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi n))))"
| lift_rule: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> derivable th \<Longrightarrow> ct_T (cd_rep ct) = propT \<Longrightarrow> cd_sign ct = th_sign th \<Longrightarrow>
    derivable
     (with_cons (th_constraints th)
      (mk_thm (lift_rule (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th)) (th_shyps th \<union> cd_sorts ct)
        (th_hyps th) (th_sign th)
        (bindW (th_proof th) (\<lambda>p. returnW (lift_rule_proof (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th) p)))
        (bindM (th_zproof th) (lift_rule_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))
          (ct_maxidx (cd_rep ct)) (rp th)))))"
| axiom: "sg_axioms c a = Some A \<Longrightarrow> sign_axioms invent c \<Longrightarrow> derivable (axiom_data invent c a A)"
| strip_shyps: "derivable th \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow>
    d = strip_shyps_rep (sg_alg (th_sign th)) gts (shyps_list (th_shyps th)) (th_hyps th) (rp th) \<Longrightarrow>
    derivable
     (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (strip_shyps_proof (sg_alg (th_sign th)) d))
      (bindM (th_zproof th) (zstrip_shyps_proof (sg_alg (th_sign th)) d)))"
| unconstrainT: "derivable th \<Longrightarrow>
    okT (unconstrainT_rep invent (shyps_list (th_shyps th)) (th_hyps th) (rp th)) r \<Longrightarrow>
    unc_sig_ok box zn invent (th_sign th) (shyps_list (th_shyps th)) (th_prop th) r \<Longrightarrow>
    derivable
     (mk_thm r {[]} [] (th_sign th)
      (bindW (th_proof th) (\<lambda>_. liftMP (unconstrain_thm_proof box invent (shyps_list (th_shyps th)) (th_prop th))))
      (bindM (th_zproof th) (\<lambda>_. zunconstrain_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) zn invent
        (shyps_list (th_shyps th)) (th_prop th))))"
| transfer: "derivable th \<Longrightarrow> sign_le (th_sign th) c' \<Longrightarrow> derivable (th\<lparr>th_sign := c'\<rparr>)"
| solve_constraints: "derivable th \<Longrightarrow> derivable (solve_data th)"
| instantiate: "derivable th \<Longrightarrow>
    \<forall>(v, cT)\<in>set cTs. ctyp_ok cT \<and> cty_sign cT = th_sign th \<Longrightarrow>
    \<forall>(v, ct)\<in>set cts. cterm_ok ct \<and> cd_sign ct = th_sign th \<Longrightarrow>
    \<forall>(v, cT)\<in>set cTs. csorts_ok (cty_sign cT) (cty_sorts cT) \<Longrightarrow>
    \<forall>(v, ct)\<in>set cts. csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow>
    \<not> (cTs = [] \<and> cts = []) \<Longrightarrow>
    okT (instantiate (sg_alg (th_sign th)) bt (map (\<lambda>(v, cT). (v, (cty_T cT, cty_maxidx cT))) cTs)
      (map (\<lambda>(v, ct). (v, (ct_t (cd_rep ct), ct_T (cd_rep ct), ct_maxidx (cd_rep ct)))) cts) (rp th)) r \<Longrightarrow>
    derivable
     (solve_data (mk_thm r
      (th_shyps th \<union> ((\<Union>(v, cT)\<in>set cTs. cty_sorts cT) \<union> (\<Union>(v, ct)\<in>set cts. cd_sorts ct)))
      (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (instantiate_proof (map (\<lambda>(v, cT). (v, cty_T cT)) cTs)
        (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts) p)))
      (bindM (th_zproof th) (zinstantiate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
        (map (\<lambda>(v, cT). (v, cty_T cT)) cTs) (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts)))))"
| assumption: "derivable st \<Longrightarrow> cfg_alg cfg = sg_alg (th_sign st) \<Longrightarrow> data_scons st \<Longrightarrow>
    okT (assumption i (rp st)) s0 \<Longrightarrow> aresult (unify_ops cfg vl) s0 r \<Longrightarrow>
    derivable (ares_data st (aseq_ctx s0) r)"
| flexflex_rule: "derivable th \<Longrightarrow> cfg_alg cfg = sg_alg (th_sign th) \<Longrightarrow> data_scons th \<Longrightarrow>
    okT (flexflex_rule (unify_ops cfg vl) (rp th)) s0 \<Longrightarrow>
    fresult (unify_ops cfg vl) smashT (rp th) s0 (env, r) \<Longrightarrow>
    derivable (fres_data (solve_data th) env r)"
| bicompose: "derivable st \<Longrightarrow> derivable rule \<Longrightarrow> cfg_alg cfg = sg_alg (th_sign st) \<Longrightarrow>
    \<forall>xs. length (vl xs) = length xs \<Longrightarrow> th_sign rule = th_sign st \<Longrightarrow>
    data_scons2 st rule \<Longrightarrow>
    okT (dest_state (rp st) i) (stpairs, Bs, Bi, C) \<Longrightarrow>
    okT (bicompose_aux (unify_ops cfg vl) (sg_alg (th_sign st)) flatten match_flg incremented (pthm_of (rp st))
      (stpairs, Bs, Bi, C) False e (pthm_of (rp rule)) nsubgoal) xq \<Longrightarrow>
    pure_sig_gen.bresult (unify_ops cfg vl) xq x \<Longrightarrow>
    derivable (bc_data (th_sign st) i st flatten e rule x)"
| biresolution: "derivable st \<Longrightarrow> \<forall>r\<in>set brules. derivable (snd r) \<Longrightarrow>
    cfg_alg cfg = sg_alg (th_sign st) \<Longrightarrow> \<forall>xs. length (vl xs) = length xs \<Longrightarrow>
    \<forall>r\<in>set brules. th_sign (snd r) = th_sign st \<Longrightarrow>
    data_scons st \<Longrightarrow> \<forall>r\<in>set brules. data_scons (snd r) \<Longrightarrow>
    okT (biresolution trace match_flg rp brules i (rp st)) s0 \<Longrightarrow>
    pure_sig_gen.brresult (sg_alg (th_sign st)) (unify_ops cfg vl) rp s0 (x, (e, rule)) \<Longrightarrow>
    derivable (bres_data (th_sign st) i st e rule x)"

subsection \<open>Each rule keeps the invariant\<close>

lemma sound_assumeI:
  assumes D: "cterm_ok ct"
    and H: "okT (assume_rule (cd_rep ct)) r"
  shows "dsem TYPE('u)
     (mk_thm r (cd_sorts ct) [ct_t (cd_rep ct)] (cd_sign ct) (returnW (Hyp (ct_t (cd_rep ct))))
      (zassume_proof (pure_sig_gen.ztargs (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_assume[where ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_implies_intr:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and H: "cd_sign ct = th_sign th" "okT (implies_intr (cd_rep ct) (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (filter (\<lambda>h.
      \<not> aconv_term (ct_t (cd_rep ct)) h) (th_hyps th)) (th_sign th) (bindW (th_proof th)
      (\<lambda>p. returnW (implies_intr_proof (ct_t (cd_rep ct)) p))) (bindM (th_zproof th)
      (zimplies_intr_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_implies_intr[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_implies_elim:
  assumes D: "dsem TYPE('u) thAB" "dsem TYPE('u) thA"
    and H: "th_sign thAB = th_sign thA" "okT (implies_elim (rp thAB) (rp thA)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints thA \<union> th_constraints thAB) (mk_thm r (th_shyps thAB \<union>
      th_shyps thA) (th_hyps thA @ th_hyps thAB) (th_sign thAB) (bindW (th_proof thAB)
      (\<lambda>p. bindW (th_proof thA) (\<lambda>q. returnW (PAppp p q)))) (bindM (th_zproof
      thAB) (\<lambda>p. bindM (th_zproof thA) (\<lambda>q. return (ZAppp p q))))))"
proof -
  let ?thAB = "Abs_thm thAB :: 'u pure_thm" and ?thA = "Abs_thm thA :: 'u pure_thm"
  have R: "rep_thm ?thAB = thAB" "rep_thm ?thA = thA"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_implies_elim[where thAB = ?thAB and thA = ?thA, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_forall_intr:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and H: "cd_sign ct = th_sign th" "sign_closed (th_sign th)" "okT (forall_intr (th_hyps th) (cd_rep ct)
      (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (cd_rep
      ct))) (ct_t (cd_rep ct)) p))) (bindM (th_zproof th) (zforall_intr_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) (ct_T (cd_rep ct)) (var_name (ct_t (cd_rep ct))) (ct_t (cd_rep
      ct))))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_forall_intr[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_forall_elim:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and H: "cd_sign ct = th_sign th" "okT (forall_elim (cd_rep ct) (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (PAppt p (Some (ct_t (cd_rep ct)))))) (bindM
      (th_zproof th) (\<lambda>p. zforall_elim_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
      (ct_t (cd_rep ct)) p))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_forall_elim[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_symmetric:
  assumes D: "dsem TYPE('u) th"
    and H: "sign_eq (th_sign th)" "okT (symmetric (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (symmetric_proof p))) (bindM (th_zproof th) (\<lambda>p. case
      eq_args (th_prop (rp th)) of Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) T t u p | None \<Rightarrow> raise undefined))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_symmetric[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_transitive:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (transitive (rp th1) (rp th2)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (bindW (th_proof th1) (\<lambda>p.
      bindW (th_proof th2) (\<lambda>q. case eq_args (th_prop (rp th1)) of Some (T, t1, u)
      \<Rightarrow> returnW (transitive_proof T u p q) | None \<Rightarrow> raiseW undefined)))
      (bindM (th_zproof th1) (\<lambda>p. bindM (th_zproof th2) (\<lambda>q. case (eq_args
      (th_prop (rp th1)), eq_args (th_prop (rp th2))) of (Some (T, t1, u), Some (_, _, t2))
      \<Rightarrow> ztransitive_proof (pure_sig_gen.ztargs (sg_consts (th_sign th1))) T t1 u t2 p q |
      _ \<Rightarrow> raise undefined)))))"
proof -
  let ?th1 = "Abs_thm th1 :: 'u pure_thm" and ?th2 = "Abs_thm th2 :: 'u pure_thm"
  have R: "rep_thm ?th1 = th1" "rep_thm ?th2 = th2"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_transitive[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_abstract_rule:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and H: "cd_sign ct = th_sign th" "sign_eq (th_sign th)" "sign_closed (th_sign th)" "okT
      (abstract_rule_res b (th_hyps th) (cd_rep ct) (rp th)) (r, U, f, g)"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (cd_rep ct)) p)))
      (bindM (th_zproof th) (zabstract_rule_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_T
      (cd_rep ct)) U b (ct_t (cd_rep ct)) f g))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_abstract_rule[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_combination:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (combination_res (rp th1) (rp th2)) (r,
      T1, U, f, g, t, u)"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (bindW (th_proof th1) (\<lambda>p.
      bindW (th_proof th2) (\<lambda>q. combination_proof f g t u p q))) (bindM (th_zproof th1)
      (\<lambda>p. bindM (th_zproof th2) (\<lambda>q. zcombination_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th1))) T1 U f g t u p q)))))"
proof -
  let ?th1 = "Abs_thm th1 :: 'u pure_thm" and ?th2 = "Abs_thm th2 :: 'u pure_thm"
  have R: "rep_thm ?th1 = th1" "rep_thm ?th2 = th2"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_combination[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_equal_intr:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (equal_intr (rp th1) (rp th2)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_intr_proof th1 th2)
      (zprf2r zequal_intr_proof th1 th2)))"
proof -
  let ?th1 = "Abs_thm th1 :: 'u pure_thm" and ?th2 = "Abs_thm th2 :: 'u pure_thm"
  have R: "rep_thm ?th1 = th1" "rep_thm ?th2 = th2"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_equal_intr[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded prf2_raw zprf2_raw R rp_sel]) (use D H in \<open>simp_all add: R prf2_raw zprf2_raw dsem_def\<close>)
qed

lemma sound_equal_elim:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (equal_elim (rp th1) (rp th2)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_elim_proof th1 th2)
      (zprf2r zequal_elim_proof th1 th2)))"
proof -
  let ?th1 = "Abs_thm th1 :: 'u pure_thm" and ?th2 = "Abs_thm th2 :: 'u pure_thm"
  have R: "rep_thm ?th1 = th1" "rep_thm ?th2 = th2"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_equal_elim[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded prf2_raw zprf2_raw R rp_sel]) (use D H in \<open>simp_all add: R prf2_raw zprf2_raw dsem_def\<close>)
qed

lemma sound_trivial:
  assumes D: "cterm_ok ct"
    and H: "okT (trivial (cd_rep ct)) r"
  shows "dsem TYPE('u)
     (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW trivial_proof) (ztrivial_proof (pure_sig_gen.ztargs
      (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_trivial[where ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_weaken:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and H: "cd_sign ct = th_sign th" "okT (weaken (cd_rep ct) (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (ct_t (cd_rep ct) #
      th_hyps th) (th_sign th) (th_proof th) (th_zproof th)))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_weaken[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_renamed_prop:
  assumes D: "dsem TYPE('u) th"
    and H: "okT (renamed_prop P (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (th_proof th)
      (th_zproof th)))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_renamed_prop[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_incr_indexes:
  assumes D: "dsem TYPE('u) th"
    and H: "okT (incr_indexes_thm i (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (incr_indexes_prf
      i (th_proof th)) (incr_indexes_zprf i (th_zproof th))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_incr_indexes[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_permute_prems:
  assumes D: "dsem TYPE('u) th"
    and H: "okT (permute_data j k (rp th)) (r, prems', m)"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (permute_prems_proof prems' j m p))) (bindM (th_zproof th)
      (zpermute_prems_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) prems' j m))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_permute_prems[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_rotate_rule:
  assumes D: "dsem TYPE('u) th"
    and H: "okT (rotate_data k i (rp th)) (r, Bs, Bi', params, asms, m)"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p))) (bindM (th_zproof th)
      (zrotate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi' params asms m))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_rotate_rule[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_varifyT_global:
  assumes D: "dsem TYPE('u) th"
    and H: "sign_closed (th_sign th)" "okT (varifyT_global vl fixed (th_hyps th) (rp th)) (names, r)"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (th_zproof th) (zvarifyT_proof
      names))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_varifyT_global[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_adjust_maxidx:
  assumes D: "dsem TYPE('u) th"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm (adjust_maxidx_thm i (rp th)) (th_shyps th) (th_hyps th)
      (th_sign th) (th_proof th) (th_zproof th)))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_adjust_maxidx[where th = ?th, unfolded R rp_sel]) (use D in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_reflexive:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (reflexive (cd_rep ct)) r"
  shows "dsem TYPE('u) (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use D H in \<open>auto simp: R conv_data_raw dsem_def conv_datar_def intro: pure_sig.conv_ok_reflexive\<close>)
qed

lemma sound_beta_conversion:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (beta_conversion full (cd_rep ct)) r"
  shows "dsem TYPE('u) (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use D H in \<open>auto simp: R conv_data_raw dsem_def conv_datar_def intro: pure_sig.conv_ok_beta_conversion\<close>)
qed

lemma sound_eta_conversion:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (eta_conversion (cd_rep ct)) r"
  shows "dsem TYPE('u) (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use D H in \<open>auto simp: R conv_data_raw dsem_def conv_datar_def intro: pure_sig.conv_ok_eta_conversion\<close>)
qed

lemma sound_eta_long_conversion:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (eta_long_conversion (cd_rep ct)) r"
  shows "dsem TYPE('u) (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use D H in \<open>auto simp: R conv_data_raw dsem_def conv_datar_def intro: pure_sig.conv_ok_eta_long_conversion\<close>)
qed

lemma sound_generalize:
  assumes D: "dsem TYPE('u) th"
    and H: "\<not> (tfrees = [] \<and> frees = [])" "sign_closed (th_sign th)"
      "okT (generalize tfrees frees gi (th_hyps th) (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs th) (th_prop th) p)))
      (bindM (th_zproof th) (zgeneralize_proof tfrees frees gi))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_generalize[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_legacy_freezeT:
  assumes D: "dsem TYPE('u) th"
    and H: "ok (full_prop_of (th_tpairs th) (th_prop th)) P1" "okT (legacy_freezeT vl (rp th)) r"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p)))
      (bindM (th_zproof th) (zlegacy_freezeT_proof vl P1))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_legacy_freezeT[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_of_class:
  assumes D: "cterm_ok ct"
    and H: "ct_t (cd_rep ct) = mk_of_class T c" "tm_sorts (mk_of_class T c) \<subseteq> cd_sorts ct"
      "pure_sig_gen.class_const (sg_alg (cd_sign ct)) (sg_consts (cd_sign ct)) (c + STR ''_class'') c"
      "sign_eq (cd_sign ct)" "okT (Pure_Subst_Rules.of_class (sg_alg (cd_sign ct)) T c) r"
  shows "dsem TYPE('u)
     (solve_data (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW (PClass T c))
      (return (OFCLASSp (ztyp_of T) c))))"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_of_class[where ct = ?ct, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_eq_assumption:
  assumes D: "dsem TYPE('u) th"
    and H: "okT (eq_assumption i (rp th)) (n, r)" "okT (dest_state (rp th) i) (tpairs, Bs, Bi, C)"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
      (bindM (th_zproof th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi n))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_eq_assumption[where th = ?th, unfolded R rp_sel]) (use D H in \<open>simp_all add: R dsem_def\<close>)
qed

lemma sound_lift_rule:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and H: "ct_T (cd_rep ct) = propT" "cd_sign ct = th_sign th"
  shows "dsem TYPE('u)
     (with_cons (th_constraints th)
      (mk_thm (lift_rule (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th)) (th_shyps th \<union> cd_sorts ct)
        (th_hyps th) (th_sign th)
        (bindW (th_proof th) (\<lambda>p. returnW (lift_rule_proof (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th) p)))
        (bindM (th_zproof th) (lift_rule_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))
          (ct_maxidx (cd_rep ct)) (rp th)))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct" using D by (simp_all add: rep_Abs rep_Abs_cterm)
  have "thm_sem TYPE('u) (lift_rule_data ?ct ?th)"
    by (rule thm_sem_lift_rule) (use H in \<open>simp_all add: R\<close>)
  then show ?thesis using D by (simp add: dsem_def lift_rule_data_def Let_def R)
qed

lemma sound_axiom:
  assumes H: "sg_axioms c a = Some A" "sign_axioms invent c"
  shows "dsem TYPE('u) (axiom_data invent c a A)"
  unfolding dsem_def by (rule conjI, rule thm_sem_axiom) (use H in \<open>simp_all add: axiom_data_def\<close>)

lemma sound_strip_shyps:
  assumes D: "dsem TYPE('u) th"
    and H: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> finite (th_shyps th)"
      "sign_closed (th_sign th)"
      "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> \<forall>S\<in>th_shyps th. sort_ok (sg_alg (th_sign th)) S"
      "d = strip_shyps_rep (sg_alg (th_sign th)) gts (shyps_list (th_shyps th)) (th_hyps th) (rp th)"
  shows "dsem TYPE('u)
     (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (strip_shyps_proof (sg_alg (th_sign th)) d))
      (bindM (th_zproof th) (zstrip_shyps_proof (sg_alg (th_sign th)) d)))"
proof (cases "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))")
  case False
  then show ?thesis by (simp add: dsem_nosig)
next
  case True
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis
    using thm_sem_strip_shyps[of ?th gts] H(1)[OF True] H(2) H(3)[OF True] H(4)
    by (simp add: R dsem_def mk_thm_def cong: option.case_cong)
qed

lemma sound_unconstrainT:
  assumes D: "dsem TYPE('u) th"
    and H: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> finite (th_shyps th)"
      "okT (unconstrainT_rep invent (shyps_list (th_shyps th)) (th_hyps th) (rp th)) r"
      "unc_sig_ok box zn invent (th_sign th) (shyps_list (th_shyps th)) (th_prop th) r"
      "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> \<forall>S\<in>th_shyps th. sort_ok (sg_alg (th_sign th)) S"
  shows "dsem TYPE('u)
     (mk_thm r {[]} [] (th_sign th)
      (bindW (th_proof th) (\<lambda>_. liftMP (unconstrain_thm_proof box invent (shyps_list (th_shyps th)) (th_prop th))))
      (bindM (th_zproof th) (\<lambda>_. zunconstrain_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) zn invent
        (shyps_list (th_shyps th)) (th_prop th))))"
proof (cases "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))")
  case False
  then show ?thesis by (simp add: dsem_nosig)
next
  case True
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  have "unc_ok box zn invent (th_sign th) (shyps_list (th_shyps th)) (th_prop th) r"
    using H(3) H(4)[OF True] set_shyps_list[OF H(1)[OF True]] by (simp add: unc_ok_iff)
  then show ?thesis
    using thm_sem_unconstrainT[of invent ?th r box zn] H(1)[OF True] H(2)
    by (simp add: R dsem_def unconstrainT_data_def mk_thm_def)
qed

lemma sound_transfer:
  assumes D: "dsem TYPE('u) th" and H: "sign_le (th_sign th) c'"
  shows "dsem TYPE('u) (th\<lparr>th_sign := c'\<rparr>)"
proof -
  have "cons_ok c' (th_constraints th)"
    using cons_ok_transfer[of "th_sign th" c' "th_constraints th"] D H by (simp add: dsem_def)
  then show ?thesis using thm_sem_transfer[OF conjunct1[OF D[unfolded dsem_def]] H] by (simp add: dsem_def)
qed

lemma sound_solve_constraints:
  assumes D: "dsem TYPE('u) th"
  shows "dsem TYPE('u) (solve_data th)"
  using thm_sem_solve_data[of "TYPE('u)" th] D by (simp add: dsem_def)

text \<open>The parts of the invariant:\<close>

lemma dsem_inv:
  assumes "dsem U d" "pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d))" "data_cons d"
  shows "pure_sig_gen.thm_inv (sg_alg (th_sign d)) (sg_ar (th_sign d)) (sg_consts (th_sign d)) {}
    (th_maxidx d) (th_hyps d) (th_tpairs d) (th_prop d)"
  using assms by (simp add: dsem_def thm_sem_def data_cons_def pure_sig.thm_inv_wf)

lemma dsem_inv0:
  assumes "dsem U d" "pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d))"
    "scons (pure_sig_gen.tvars_thm (th_tpairs d) (th_prop d))"
  shows "pure_sig_gen.thm_inv0 (sg_alg (th_sign d)) (sg_ar (th_sign d)) (sg_consts (th_sign d))
    (th_maxidx d) (th_hyps d) (th_tpairs d) (th_prop d)"
  using assms by (simp add: dsem_def thm_sem_def pure_sig.thm_inv0_wf)

lemma dsem_valid:
  fixes M :: "'u model"
  assumes "dsem TYPE('u) d" "is_model (th_sign d) M"
  shows "valid_in (th_sign d) M (th_shyps d) (th_hyps d) (th_tpairs d) (th_prop d)"
proof -
  have "pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d))"
    by (rule pure_model.axioms(1)[OF is_modelD[OF assms(2)]])
  with assms show ?thesis by (simp add: dsem_def thm_sem_def)
qed

lemma inst_raw:
  assumes "\<forall>(v, cT)\<in>set cTs. ctyp_ok cT" "\<forall>(v, ct)\<in>set cts. cterm_ok ct"
  shows "instT_of (map (apsnd Abs_ctyp) cTs) = map (\<lambda>(v, cT). (v, (cty_T cT, cty_maxidx cT))) cTs"
    "insts_of (map (apsnd Abs_cterm) cts) =
      map (\<lambda>(v, ct). (v, (ct_t (cd_rep ct), ct_T (cd_rep ct), ct_maxidx (cd_rep ct)))) cts"
    "inst_Ts (map (apsnd Abs_ctyp) cTs) = map (\<lambda>(v, cT). (v, cty_T cT)) cTs"
    "inst_ts (map (apsnd Abs_cterm) cts) = map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts"
    "inst_sorts (map (apsnd Abs_ctyp) cTs) (map (apsnd Abs_cterm) cts) =
      (\<Union>(v, cT)\<in>set cTs. cty_sorts cT) \<union> (\<Union>(v, ct)\<in>set cts. cd_sorts ct)"
  using assms
  by (auto simp: instT_of_def insts_of_def inst_Ts_def inst_ts_def inst_sorts_def Abs_ctyp_inverse
      Abs_cterm_inverse split: prod.splits)

lemma sound_instantiate:
  assumes D: "dsem TYPE('u) th"
    and H: "\<forall>(v, cT)\<in>set cTs. ctyp_ok cT \<and> cty_sign cT = th_sign th"
      "\<forall>(v, ct)\<in>set cts. cterm_ok ct \<and> cd_sign ct = th_sign th"
      "\<not> (cTs = [] \<and> cts = [])"
      "okT (instantiate (sg_alg (th_sign th)) bt (map (\<lambda>(v, cT). (v, (cty_T cT, cty_maxidx cT))) cTs)
        (map (\<lambda>(v, ct). (v, (ct_t (cd_rep ct), ct_T (cd_rep ct), ct_maxidx (cd_rep ct)))) cts) (rp th)) r"
  shows "dsem TYPE('u)
     (solve_data (mk_thm r
      (th_shyps th \<union> ((\<Union>(v, cT)\<in>set cTs. cty_sorts cT) \<union> (\<Union>(v, ct)\<in>set cts. cd_sorts ct)))
      (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (instantiate_proof (map (\<lambda>(v, cT). (v, cty_T cT)) cTs)
        (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts) p)))
      (bindM (th_zproof th) (zinstantiate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
        (map (\<lambda>(v, cT). (v, cty_T cT)) cTs) (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts)))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  let ?cTs = "map (apsnd Abs_ctyp) cTs" and ?cts = "map (apsnd Abs_cterm) cts"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  have ok: "\<forall>(v, cT)\<in>set cTs. ctyp_ok cT" "\<forall>(v, ct)\<in>set cts. cterm_ok ct" using H(1,2) by auto
  note I = inst_raw[OF ok]
  have g: "\<forall>(v, cT)\<in>set ?cTs. cty_sign (rep_ctyp cT) = th_sign th"
    "\<forall>(v, ct)\<in>set ?cts. csign_of ct = th_sign th"
    using H(1,2) by (auto simp: Abs_ctyp_inverse Abs_cterm_inverse)
  have ne: "\<not> (?cTs = [] \<and> ?cts = [])" using H(3) by simp
  show ?thesis unfolding dsem_def thm_sem_with_cons thm_sem_solve_data rp_sel
    by (rule conjI, rule thm_sem_instantiate[where th = ?th and cTs = ?cTs and cts = ?cts, unfolded I R rp_sel]) (use D H g ne in \<open>simp_all add: R I dsem_def\<close>)
qed

subsection \<open>The rules that unify, for results that bind no name with two types\<close>

context pure_sig_gen
begin

text \<open>
  The condition \<^const>\<open>pure_sig_gen.bres_names\<close> on a result of resolution, where the loose names are the
  names with two types in the proof state, the lifted rule and the new premises:
\<close>

lemma bres_names_vclash:
  assumes g: "okT (cprem_of state i) goal"
    and L: "loose = vclash (vars_thm (th_tpairs state) (th_prop state) \<union>
      vars_thm (th_tpairs (lift_rule goal (th_maxidx state) (rep rule)))
        (th_prop (lift_rule goal (th_maxidx state) (rep rule))) \<union>
      (\<Union>A\<in>set (na_As (br_newas x)). vars A))"
  shows "bres_names rep brules i state rule x"
    and "lvtcons (vars_thm (th_tpairs state) (th_prop state))"
proof -
  let ?Y = "vars_thm (th_tpairs state) (th_prop state) \<union>
      vars_thm (th_tpairs (lift_rule goal (th_maxidx state) (rep rule)))
        (th_prop (lift_rule goal (th_maxidx state) (rep rule)))"
  let ?V = "\<Union>A\<in>set (na_As (br_newas x)). vars A"
  have all: "\<forall>g'. okT (cprem_of state i) g' \<longrightarrow> P g'" if "P goal" for P
    using g that by (auto dest: okT_det)
  have n1: "vtcons ?Y" if "loose = {}"
    using that unfolding L by (fastforce simp: vclash_def vtcons_def)
  have n3: "lvtcons (?Y \<union> ?V)" by (rule lvtcons_vclash) (simp add: L)
  have n4: "loose \<subseteq> fst ` (?Y \<union> ?V)" unfolding L by (force simp: vclash_def)
  show "bres_names rep brules i state rule x"
    unfolding bres_names_def
    by ((intro conjI impI disjI2 all n3 n4 n1 | assumption)+)
  show "lvtcons (vars_thm (th_tpairs state) (th_prop state))"
    by (rule lvtcons_mono[OF n3]) blast
qed

end

text \<open>
  The rules keep the invariant without a condition on the names of the variables: the proofs take
  as loose names the names that occur with two types in the arguments.
\<close>

lemma sound_assumption_gen:
  assumes D: "dsem TYPE('u) st"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "data_scons st" "okT (assumption i (rp st)) s0"
      "aresult (unify_ops cfg vl) s0 r"
  shows "dsem TYPE('u) (ares_data st (aseq_ctx s0) r)"
proof (cases "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))")
  case False
  then show ?thesis by (simp add: dsem_nosig ares_data_def)
next
  case True
  let ?st = "Abs_thm st :: 'u pure_thm"
  have R: "rep_thm ?st = st" using D by (simp add: rep_Abs)
  have ps: "pure_sig (sg_alg (sign_of ?st)) (sg_ar (sign_of ?st))" using True by (simp add: R)
  have cfg: "cfg_alg cfg = sg_alg (sign_of ?st)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of ?st)) (th_prop (rep_of ?st)))"
    and a: "okT (assumption i (rep_of ?st)) s0"
    using H by (simp_all add: R data_scons_def)
  show ?thesis
    using thm_sem_thm_of_ares[OF ps cfg sc a H(4)] cons_ok_thm_of_ares[OF ps cfg sc a H(4)]
    by (simp add: dsem_def thm_of_ares_raw R ares_data_def)
qed

lemma sound_flexflex_rule_gen:
  assumes D: "dsem TYPE('u) th"
    and H: "cfg_alg cfg = sg_alg (th_sign th)" "data_scons th"
      "okT (flexflex_rule (unify_ops cfg vl) (rp th)) s0"
      "fresult (unify_ops cfg vl) smashT (rp th) s0 (env, r)"
  shows "dsem TYPE('u) (fres_data (solve_data th) env r)"
proof (cases "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))")
  case False
  then show ?thesis by (auto simp: dsem_nosig fres_data_def)
next
  case True
  have D': "dsem TYPE('u) (solve_data th)"
    using thm_sem_solve_data[of "TYPE('u)" th] D by (simp add: dsem_def)
  let ?th = "Abs_thm (solve_data th) :: 'u pure_thm"
  have R: "rep_thm ?th = solve_data th" using D' by (simp add: rep_Abs)
  have ps: "pure_sig (sg_alg (sign_of ?th)) (sg_ar (sign_of ?th))" using True by (simp add: R)
  have cfg: "cfg_alg cfg = sg_alg (sign_of ?th)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of ?th)) (th_prop (rep_of ?th)))"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of ?th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of ?th) s0 (env, r)"
    using H by (simp_all add: R data_scons_def)
  show ?thesis
    using thm_sem_thm_of_fres[OF ps cfg sc a res] cons_ok_thm_of_fres[OF ps cfg sc a res]
    by (simp add: dsem_def thm_of_fres_raw R)
qed

lemma sound_bicompose_gen:
  assumes D: "dsem TYPE('u) st" "dsem TYPE('u) rule"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "\<forall>xs. length (vl xs) = length xs" "th_sign rule = th_sign st"
      "data_scons2 st rule"
      "okT (dest_state (rp st) i) (stpairs, Bs, Bi, C)"
      "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (th_sign st)) flatten match_flg incremented (pthm_of (rp st))
        (stpairs, Bs, Bi, C) False e (pthm_of (rp rule)) nsubgoal) xq"
      "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
  shows "dsem TYPE('u) (bc_data (th_sign st) i st flatten e rule x)"
proof (cases "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))")
  case False
  then show ?thesis by (simp add: dsem_nosig bc_data_def)
next
  case True
  let ?st = "Abs_thm st :: 'u pure_thm" and ?rule = "Abs_thm rule :: 'u pure_thm"
  have R: "rep_thm ?st = st" "rep_thm ?rule = rule" using D by (simp_all add: rep_Abs)
  have ps: "pure_sig (sg_alg (sign_of ?st)) (sg_ar (sign_of ?st))" using True by (simp add: R)
  have cfg: "cfg_alg cfg = sg_alg (sign_of ?st)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of ?rule = sign_of ?st" and sc: "bc_scons ?st ?rule"
    and d: "okT (dest_state (rep_of ?st) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of ?st)) flatten match_flg incremented
      (pthm_of (rep_of ?st)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of ?rule)) nsubgoal) xq"
    using H by (simp_all add: R bc_scons_raw)
  show ?thesis
    using thm_sem_thm_of_bc[OF ps cfg vl sr sc d ok H(7)] cons_ok_thm_of_bc[OF ps cfg vl sr sc d ok H(7)]
    by (simp add: dsem_def thm_of_bc_raw R bc_data_def)
qed

lemma sound_biresolution_gen:
  assumes D: "dsem TYPE('u) st" "\<forall>r\<in>set brules. dsem TYPE('u) (snd r)"
    and cfg: "cfg_alg cfg = sg_alg (th_sign st)" and vl: "\<forall>xs. length (vl xs) = length xs"
    and sg: "\<forall>r\<in>set brules. th_sign (snd r) = th_sign st"
    and cs: "data_scons st" "\<forall>r\<in>set brules. data_scons (snd r)"
    and br: "okT (biresolution trace match_flg rp brules i (rp st)) s0"
    and res: "pure_sig_gen.brresult (sg_alg (th_sign st)) (unify_ops cfg vl) rp s0 (x, (e, rule))"
  shows "dsem TYPE('u) (bres_data (th_sign st) i st e rule x)"
proof (cases "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))")
  case False
  then show ?thesis by (simp add: dsem_nosig bres_data_def)
next
  case ps: True
  let ?c = "th_sign st" and ?L = "data_clash_bres st i rule x"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have vl': "\<And>xs. length (vl xs) = length xs" using vl by blast
  have st0: "thm_inv0 (th_maxidx (rp st)) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
    using dsem_inv0[OF D(1) ps] cs(1) by (simp add: data_scons_def thm_rep.truncate_def)
  have ru: "thm_inv0 (th_maxidx (rp r)) (th_hyps r) (th_tpairs (rp r)) (th_prop (rp r))"
    if "(e', r) \<in> set brules" for e' r
  proof -
    have "dsem TYPE('u) r" "th_sign r = ?c" "data_scons r" using D(2) sg cs(2) that by fastforce+
    with dsem_inv0[of "TYPE('u)" r] ps show ?thesis by (simp add: data_scons_def thm_rep.truncate_def)
  qed
  have "\<exists>goal. okT (cprem_of (rp st) i) goal \<and> (e, rule) \<in> set brules"
    by (rule biresolution_result[OF br res]) blast
  then obtain goal where g: "okT (cprem_of (rp st) i) goal" and r: "(e, rule) \<in> set brules" by blast
  have G: "{g. okT (cprem_of (rp st) i) g} = {goal}" using g by (auto dest: okT_det)
  have L: "?L = vclash (vars_thm (th_tpairs (rp st)) (th_prop (rp st)) \<union>
      vars_thm (th_tpairs (lift_rule goal (th_maxidx (rp st)) (rp rule)))
        (th_prop (lift_rule goal (th_maxidx (rp st)) (rp rule))) \<union>
      (\<Union>A\<in>set (na_As (br_newas x)). vars A))"
    unfolding data_clash_bres_def G by (simp add: data_vars_def thm_rep.truncate_def)
  note nm = bres_names_vclash[where rep = rp and rule = rule, OF g L]
  have st: "thm_inv (th_maxidx (rp st)) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 nm(2)]])
  from r have sr: "th_sign rule = ?c" and Dr: "dsem TYPE('u) rule" using sg D(2) by fastforce+
  have "thm_inv (maxidx (br_env x)) (th_hyps st @ th_hyps rule) (br_tpairs x) (br_prop x) \<and> bres_inv x"
    by (rule biresolution_thm_inv[OF br res cfg vl' st ru nm(1)])
  then have ti: "thm_inv (maxidx (br_env x)) (th_hyps st @ th_hyps rule) (br_tpairs x) (br_prop x)"
    and bi: "bres_inv x"
    by blast+
  have val: "valid_in ?c M (th_shyps st \<union> th_shyps rule \<union> env_sorts (br_env x)) (th_hyps st @ th_hyps rule)
      (br_tpairs x) (br_prop x)" if M: "is_model ?c M" for M :: "'u model"
  proof -
    interpret pure_model_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule pure_model_gen_of[OF is_modelD[OF M]])
    have vs: "valid (th_shyps st) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
      using dsem_valid[OF D(1) M] by (simp add: valid_in_def thm_rep.truncate_def)
    have vr: "valid (th_shyps r) (th_hyps r) (th_tpairs (rp r)) (th_prop (rp r)) \<and>
        thm_inv0 (th_maxidx (rp r)) (th_hyps r) (th_tpairs (rp r)) (th_prop (rp r))"
      if "(e', r) \<in> set brules" for e' r
    proof -
      have "dsem TYPE('u) r" "th_sign r = ?c" using D(2) sg that by fastforce+
      with dsem_valid[of r M] M ru[OF that] show ?thesis by (simp add: valid_in_def thm_rep.truncate_def)
    qed
    have "valid (th_shyps st \<union> th_shyps rule \<union> tyenv_sorts (tyenv (br_env x))) (th_hyps st @ th_hyps rule)
        (br_tpairs x) (br_prop x)"
      by (rule biresolution_valid[OF br res cfg vl' vs st vr nm(1)])
    then show ?thesis by (simp add: valid_in_def env_sorts_def)
  qed
  have "tsorted (sg_alg ?c) (tyenv (br_env x))" using bi by (simp add: bres_inv_def)
  then have co: "cons_ok ?c (th_constraints st \<union> th_constraints rule \<union> env_constraints (br_env x))"
    using D(1) Dr sr by (simp add: cons_ok_env dsem_def)
  show ?thesis using ti val co
    by (simp add: dsem_def thm_sem_def bres_data_def pure_sig.thm_inv0_wf[OF ps] thm_inv_iff)
qed

subsection \<open>The rules that unify keep the variables consistent\<close>

text \<open>
  The results of resolution, of proof by assumption and of \<open>flexflex_rule\<close> again have one type
  for each name of a schematic variable, so that these rules can be chained.
\<close>

lemma data_cons_biresolution:
  assumes D: "dsem TYPE('u) st" "\<forall>r\<in>set brules. dsem TYPE('u) (snd r)"
    and ps: "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))"
    and cfg: "cfg_alg cfg = sg_alg (th_sign st)" and vl: "\<forall>xs. length (vl xs) = length xs"
    and sg: "\<forall>r\<in>set brules. th_sign (snd r) = th_sign st"
    and cs: "data_cons st" "\<forall>r\<in>set brules. data_cons (snd r)"
    and br: "okT (biresolution trace match_flg rp brules i (rp st)) s0"
    and res: "pure_sig_gen.brresult (sg_alg (th_sign st)) (unify_ops cfg vl) rp s0 (x, (e, rule))"
  shows "data_cons (bres_data (th_sign st) i st e rule x)"
proof -
  let ?c = "th_sign st"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have vl': "\<And>xs. length (vl xs) = length xs" using vl by blast
  have st: "thm_inv (th_maxidx (rp st)) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
    using dsem_inv[OF D(1) ps cs(1)] by (simp add: thm_rep.truncate_def)
  have ru: "thm_inv (th_maxidx (rp r)) (th_hyps r) (th_tpairs (rp r)) (th_prop (rp r))"
    if "(e', r) \<in> set brules" for e' r
  proof -
    have "dsem TYPE('u) r" "th_sign r = ?c" "data_cons r" using D(2) sg cs(2) that by fastforce+
    with dsem_inv[of "TYPE('u)" r] ps show ?thesis by (simp add: thm_rep.truncate_def)
  qed
  have "thm_inv (maxidx (br_env x)) (th_hyps st @ th_hyps rule) (br_tpairs x) (br_prop x) \<and> bres_inv x"
    by (rule biresolution_thm_inv[OF br res cfg vl' st ru])
  then show ?thesis by (simp add: data_cons_def bres_data_def thm_inv_wf)
qed

lemma data_cons_assumption:
  assumes D: "dsem TYPE('u) st" and ps: "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "data_cons st" "okT (assumption i (rp st)) s0"
      "aresult (unify_ops cfg vl) s0 r"
  shows "data_cons (ares_data st (aseq_ctx s0) r)"
proof -
  let ?c = "th_sign st"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have st: "thm_inv (th_maxidx (rp st)) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
    using dsem_inv[OF D ps H(2)] by (simp add: thm_rep.truncate_def)
  from assumption_thm_inv[OF H(3,4,1) st] show ?thesis
    by (simp add: data_cons_def ares_data_def thm_inv_wf)
qed

lemma data_cons_flexflex_rule:
  assumes D: "dsem TYPE('u) th" and ps: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))"
    and H: "cfg_alg cfg = sg_alg (th_sign th)" "data_cons th"
      "okT (flexflex_rule (unify_ops cfg vl) (rp th)) s0"
      "fresult (unify_ops cfg vl) smashT (rp th) s0 (env, r)"
  shows "data_cons (fres_data (solve_data th) env r)"
proof -
  let ?c = "th_sign th"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have st: "thm_inv (th_maxidx (rp th)) (th_hyps th) (th_tpairs (rp th)) (th_prop (rp th))"
    using dsem_inv[OF D ps H(2)] by (simp add: thm_rep.truncate_def)
  from flexflex_thm_inv[OF H(3,4,1) st] H(2) show ?thesis
    by (auto simp: data_cons_def fres_data_def thm_inv_wf)
qed

lemma data_cons_bicompose:
  assumes D: "dsem TYPE('u) st" "dsem TYPE('u) rule"
    and ps: "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "\<forall>xs. length (vl xs) = length xs" "th_sign rule = th_sign st"
      "data_scons2 st rule" "incremented \<longrightarrow> data_vcons2 st rule"
      "okT (dest_state (rp st) i) (stpairs, Bs, Bi, C)"
      "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (th_sign st)) flatten match_flg incremented (pthm_of (rp st))
        (stpairs, Bs, Bi, C) False e (pthm_of (rp rule)) nsubgoal) xq"
      "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
  shows "data_cons (bc_data (th_sign st) i st flatten e rule x)"
proof -
  let ?c = "th_sign st"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have vl': "\<And>xs. length (vl xs) = length xs" using H(2) by blast
  have tv: "scons (tvars_thm (th_tpairs (rp st)) (th_prop (rp st)) \<union> tvars_thm (th_tpairs (rp rule)) (th_prop (rp rule)))"
    using H(4) by (simp add: data_scons2_def thm_rep.truncate_def)
  then have s1: "scons (tvars_thm (th_tpairs st) (th_prop st))" and s2: "scons (tvars_thm (th_tpairs rule) (th_prop rule))"
    by (auto simp: scons_def thm_rep.truncate_def)
  have vc: "incremented \<Longrightarrow>
      vtcons (vars_thm (th_tpairs (rp st)) (th_prop (rp st)) \<union> vars_thm (th_tpairs (rp rule)) (th_prop (rp rule)))"
    using H(5) by (simp add: data_vcons2_def thm_rep.truncate_def)
  have st: "thm_inv0 (th_maxidx (rp st)) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
    using dsem_inv0[OF D(1) ps s1] by (simp add: thm_rep.truncate_def)
  have ru: "thm_inv0 (th_maxidx (rp rule)) (th_hyps rule) (th_tpairs (rp rule)) (th_prop (rp rule))"
    using dsem_inv0[OF D(2) _ s2] ps H(3) by (simp add: thm_rep.truncate_def)
  have "thm_inv (maxidx (br_env x)) (th_hyps st @ th_hyps rule) (br_tpairs x) (br_prop x)"
    by (rule bicompose_setup[OF H(6,7,8,1) vl' st ru tv vc])
  then show ?thesis by (simp add: data_cons_def bc_data_def thm_inv_wf)
qed

lemma data_cons_axiom:
  assumes A: "sg_axioms c a = Some A" "sign_axioms invent c" and ps: "pure_sig (sg_alg c) (sg_ar c)"
  shows "data_cons (axiom_data invent c a A)"
proof -
  interpret pure_sig "sg_alg c" "sg_ar c" "sg_consts c" by (rule ps)
  from A have t: "\<forall>U\<in>tatoms A. \<exists>v. U = TVar v []" and v: "vtcons (vars A)"
    by (simp_all add: sign_axioms_def ax_ok_def)
  have "S = []" if "(w, S) \<in> ttvars A" for w S
    using Thm_Axiom.ttvars_tatoms[OF that] t by auto
  then have "scons (tvars_thm [] A)" unfolding scons_def tvars_thm_def by simp blast
  moreover have "vtcons (vars_thm [] A)" using v by (simp add: vars_thm_def)
  ultimately show ?thesis by (simp add: data_cons_def axiom_data_def axiom_rule_def mk_rep_def)
qed

text \<open>
  The results of these rules and axioms have one type for each name again if their arguments
  have (the five lemmas above, with \<^const>\<open>data_cons\<close>). Other rules do not keep this
  property: \<open>instantiate\<close> maps \<open>?x = 0 \<Longrightarrow> ?y = True \<Longrightarrow> \<dots>\<close> with \<open>?y := ?x\<close> to a theorem with \<open>?x\<close>
  at two types, and Isabelle admits it. Such a theorem is derivable, and it is an argument of
  \<open>assumption\<close>, \<open>flexflex_rule\<close>, \<open>bicompose\<close> and \<open>biresolution\<close> (lemmas
  \<open>sound_assumption_gen\<close>, \<open>sound_flexflex_rule_gen\<close>, \<open>sound_bicompose_gen\<close>,
  \<open>sound_biresolution_gen\<close>).
\<close>


subsection \<open>Soundness\<close>

lemmas sound_rules =
  sound_assumeI sound_implies_intr sound_implies_elim sound_forall_intr sound_forall_elim
  sound_symmetric sound_transitive sound_abstract_rule sound_combination sound_equal_intr
  sound_equal_elim sound_trivial sound_weaken sound_renamed_prop sound_incr_indexes
  sound_permute_prems sound_rotate_rule sound_varifyT_global sound_adjust_maxidx sound_reflexive
  sound_beta_conversion sound_eta_conversion sound_eta_long_conversion sound_generalize sound_legacy_freezeT
  sound_of_class sound_eq_assumption sound_lift_rule sound_axiom sound_strip_shyps
  sound_unconstrainT sound_transfer sound_solve_constraints sound_instantiate

subsection \<open>The sort hypotheses\<close>

text \<open>
  The sort hypotheses of a theorem over a well-formed signature are finitely many sorts over its
  classes. The rules that unify add the sorts of the types of their environments, which the
  unifiers keep certified.
\<close>

definition shyps_ok :: "thm_data \<Rightarrow> bool" where
  "shyps_ok d \<longleftrightarrow> (pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d)) \<longrightarrow> csorts_ok (th_sign d) (th_shyps d))"

lemma shyps_okD:
  "shyps_ok d \<Longrightarrow> pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d)) \<Longrightarrow> finite (th_shyps d)"
  "shyps_ok d \<Longrightarrow> pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d)) \<Longrightarrow> \<forall>S\<in>th_shyps d. sort_ok (sg_alg (th_sign d)) S"
  by (simp_all add: shyps_ok_def csorts_ok_def)

lemma sorts_assumption_gen:
  assumes D: "dsem TYPE('u) st" and S: "shyps_ok st"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "data_scons st" "okT (assumption i (rp st)) s0"
      "aresult (unify_ops cfg vl) s0 r"
  shows "shyps_ok (ares_data st (aseq_ctx s0) r)"
  unfolding shyps_ok_def
proof
  assume "pure_sig (sg_alg (th_sign (ares_data st (aseq_ctx s0) r))) (sg_ar (th_sign (ares_data st (aseq_ctx s0) r)))"
  then have True: "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))" by (simp add: ares_data_def)
  let ?st = "Abs_thm st :: 'u pure_thm"
  have R: "rep_thm ?st = st" using D by (simp add: rep_Abs)
  have ps: "pure_sig (sg_alg (sign_of ?st)) (sg_ar (sign_of ?st))" using True by (simp add: R)
  have cfg: "cfg_alg cfg = sg_alg (sign_of ?st)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of ?st)) (th_prop (rep_of ?st)))"
    and a: "okT (assumption i (rep_of ?st)) s0"
    using H by (simp_all add: R data_scons_def)
  from sorts_ok_thm_of_ares[OF ps cfg sc a H(4)]
  have "\<forall>S\<in>env_sorts (ar_env r). sort_ok (sg_alg (th_sign st)) S" by (simp add: R)
  with S True show "csorts_ok (th_sign (ares_data st (aseq_ctx s0) r)) (th_shyps (ares_data st (aseq_ctx s0) r))"
    by (auto simp: ares_data_def shyps_ok_def csorts_ok_def)
qed

lemma sorts_flexflex_rule_gen:
  assumes D: "dsem TYPE('u) th" and S: "shyps_ok th"
    and H: "cfg_alg cfg = sg_alg (th_sign th)" "data_scons th"
      "okT (flexflex_rule (unify_ops cfg vl) (rp th)) s0"
      "fresult (unify_ops cfg vl) smashT (rp th) s0 (env, r)"
  shows "shyps_ok (fres_data (solve_data th) env r)"
  unfolding shyps_ok_def
proof
  assume "pure_sig (sg_alg (th_sign (fres_data (solve_data th) env r))) (sg_ar (th_sign (fres_data (solve_data th) env r)))"
  then have True: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))" by simp
  have D': "dsem TYPE('u) (solve_data th)"
    using thm_sem_solve_data[of "TYPE('u)" th] D by (simp add: dsem_def)
  let ?th = "Abs_thm (solve_data th) :: 'u pure_thm"
  have R: "rep_thm ?th = solve_data th" using D' by (simp add: rep_Abs)
  have ps: "pure_sig (sg_alg (sign_of ?th)) (sg_ar (sign_of ?th))" using True by (simp add: R)
  have cfg: "cfg_alg cfg = sg_alg (sign_of ?th)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of ?th)) (th_prop (rep_of ?th)))"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of ?th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of ?th) s0 (env, r)"
    using H by (simp_all add: R data_scons_def)
  from sorts_ok_thm_of_fres[OF ps cfg sc a res]
  have "\<forall>S\<in>env_sorts env. sort_ok (sg_alg (th_sign th)) S" by (simp add: R)
  with S True show "csorts_ok (th_sign (fres_data (solve_data th) env r)) (th_shyps (fres_data (solve_data th) env r))"
    by (auto simp: fres_data_def shyps_ok_def csorts_ok_def)
qed

lemma sorts_bicompose_gen:
  assumes D: "dsem TYPE('u) st" "dsem TYPE('u) rule" and S: "shyps_ok st" "shyps_ok rule"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "\<forall>xs. length (vl xs) = length xs" "th_sign rule = th_sign st"
      "data_scons2 st rule"
      "okT (dest_state (rp st) i) (stpairs, Bs, Bi, C)"
      "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (th_sign st)) flatten match_flg incremented (pthm_of (rp st))
        (stpairs, Bs, Bi, C) False e (pthm_of (rp rule)) nsubgoal) xq"
      "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
  shows "shyps_ok (bc_data (th_sign st) i st flatten e rule x)"
  unfolding shyps_ok_def
proof
  assume "pure_sig (sg_alg (th_sign (bc_data (th_sign st) i st flatten e rule x)))
    (sg_ar (th_sign (bc_data (th_sign st) i st flatten e rule x)))"
  then have True: "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))" by (simp add: bc_data_def)
  let ?st = "Abs_thm st :: 'u pure_thm" and ?rule = "Abs_thm rule :: 'u pure_thm"
  have R: "rep_thm ?st = st" "rep_thm ?rule = rule" using D by (simp_all add: rep_Abs)
  have ps: "pure_sig (sg_alg (sign_of ?st)) (sg_ar (sign_of ?st))" using True by (simp add: R)
  have cfg: "cfg_alg cfg = sg_alg (sign_of ?st)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of ?rule = sign_of ?st" and sc: "bc_scons ?st ?rule"
    and d: "okT (dest_state (rep_of ?st) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of ?st)) flatten match_flg incremented
      (pthm_of (rep_of ?st)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of ?rule)) nsubgoal) xq"
    using H by (simp_all add: R bc_scons_raw)
  from sorts_ok_thm_of_bc[OF ps cfg vl sr sc d ok H(7)]
  have "\<forall>S\<in>env_sorts (br_env x). sort_ok (sg_alg (th_sign st)) S" by (simp add: R)
  with S True H(3) show "csorts_ok (th_sign (bc_data (th_sign st) i st flatten e rule x))
      (th_shyps (bc_data (th_sign st) i st flatten e rule x))"
    by (auto simp: bc_data_def shyps_ok_def csorts_ok_def)
qed

lemma sorts_biresolution_gen:
  assumes D: "dsem TYPE('u) st" "\<forall>r\<in>set brules. dsem TYPE('u) (snd r)"
    and S: "shyps_ok st" "\<forall>r\<in>set brules. shyps_ok (snd r)"
    and cfg: "cfg_alg cfg = sg_alg (th_sign st)" and vl: "\<forall>xs. length (vl xs) = length xs"
    and sg: "\<forall>r\<in>set brules. th_sign (snd r) = th_sign st"
    and cs: "data_scons st" "\<forall>r\<in>set brules. data_scons (snd r)"
    and br: "okT (biresolution trace match_flg rp brules i (rp st)) s0"
    and res: "pure_sig_gen.brresult (sg_alg (th_sign st)) (unify_ops cfg vl) rp s0 (x, (e, rule))"
  shows "shyps_ok (bres_data (th_sign st) i st e rule x)"
  unfolding shyps_ok_def
proof
  assume "pure_sig (sg_alg (th_sign (bres_data (th_sign st) i st e rule x)))
    (sg_ar (th_sign (bres_data (th_sign st) i st e rule x)))"
  then have ps: "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))" by (simp add: bres_data_def)
  let ?c = "th_sign st" and ?L = "data_clash_bres st i rule x"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have vl': "\<And>xs. length (vl xs) = length xs" using vl by blast
  have st0: "thm_inv0 (th_maxidx (rp st)) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
    using dsem_inv0[OF D(1) ps] cs(1) by (simp add: data_scons_def thm_rep.truncate_def)
  have ru: "thm_inv0 (th_maxidx (rp r)) (th_hyps r) (th_tpairs (rp r)) (th_prop (rp r))"
    if "(e', r) \<in> set brules" for e' r
  proof -
    have "dsem TYPE('u) r" "th_sign r = ?c" "data_scons r" using D(2) sg cs(2) that by fastforce+
    with dsem_inv0[of "TYPE('u)" r] ps show ?thesis by (simp add: data_scons_def thm_rep.truncate_def)
  qed
  have "\<exists>goal. okT (cprem_of (rp st) i) goal \<and> (e, rule) \<in> set brules"
    by (rule biresolution_result[OF br res]) blast
  then obtain goal where g: "okT (cprem_of (rp st) i) goal" and r: "(e, rule) \<in> set brules" by blast
  have G: "{g. okT (cprem_of (rp st) i) g} = {goal}" using g by (auto dest: okT_det)
  have L: "?L = vclash (vars_thm (th_tpairs (rp st)) (th_prop (rp st)) \<union>
      vars_thm (th_tpairs (lift_rule goal (th_maxidx (rp st)) (rp rule)))
        (th_prop (lift_rule goal (th_maxidx (rp st)) (rp rule))) \<union>
      (\<Union>A\<in>set (na_As (br_newas x)). vars A))"
    unfolding data_clash_bres_def G by (simp add: data_vars_def thm_rep.truncate_def)
  note nm = bres_names_vclash[where rep = rp and rule = rule, OF g L]
  have st: "thm_inv (th_maxidx (rp st)) (th_hyps st) (th_tpairs (rp st)) (th_prop (rp st))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 nm(2)]])
  from r have sr: "th_sign rule = ?c" and Sr: "shyps_ok rule" using sg S(2) by fastforce+
  have "thm_inv (maxidx (br_env x)) (th_hyps st @ th_hyps rule) (br_tpairs x) (br_prop x) \<and> bres_inv x"
    by (rule biresolution_thm_inv[OF br res cfg vl' st ru nm(1)])
  then have "scert (sg_alg ?c) (tyenv (br_env x))" by (simp add: bres_inv_def)
  then have "\<forall>S\<in>env_sorts (br_env x). sort_ok (sg_alg ?c) S" using scert_env_sorts by blast
  with S(1) Sr ps sr show "csorts_ok (th_sign (bres_data (th_sign st) i st e rule x))
      (th_shyps (bres_data (th_sign st) i st e rule x))"
    by (auto simp: bres_data_def shyps_ok_def csorts_ok_def)
qed

lemma sorts_axiom:
  assumes H: "sg_axioms c a = Some A" "sign_axioms invent c"
  shows "shyps_ok (axiom_data invent c a A)"
  unfolding shyps_ok_def
proof
  assume "pure_sig (sg_alg (th_sign (axiom_data invent c a A))) (sg_ar (th_sign (axiom_data invent c a A)))"
  then have ps: "pure_sig (sg_alg c) (sg_ar c)" by (simp add: axiom_data_def)
  interpret pure_sig "sg_alg c" "sg_ar c" "sg_consts c" by (rule ps)
  from H have "wtp A" by (auto simp: sign_axioms_def ax_ok_def)
  then have "sort_ok (sg_alg c) S" if "S \<in> tm_sorts A" for S
    using wtpD(2)[of A] typing_tm_sorts that by blast
  then show "csorts_ok (th_sign (axiom_data invent c a A)) (th_shyps (axiom_data invent c a A))"
    by (simp add: axiom_data_def csorts_ok_def)
qed

lemma sorts_strip_shyps:
  assumes D: "dsem TYPE('u) th" and S: "shyps_ok th"
    and d: "d = strip_shyps_rep (sg_alg (th_sign th)) gts (shyps_list (th_shyps th)) (th_hyps th) (rp th)"
  shows "shyps_ok (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th) (th_hyps th)
    (th_sign th) p z)"
  unfolding shyps_ok_def
proof
  assume "pure_sig (sg_alg (th_sign (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th)
    (th_hyps th) (th_sign th) p z))) (sg_ar (th_sign (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d)
    | None \<Rightarrow> th_shyps th) (th_hyps th) (th_sign th) p z)))"
  then have ps: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))" by simp
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  note s = shyps_okD[OF S ps]
  from sorts_ok_strip_shyps[of ?th gts] ps s
  have "\<forall>S\<in>(case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th). sort_ok (sg_alg (th_sign th)) S"
    by (simp add: R d cong: option.case_cong)
  moreover have "finite (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th)"
    using s(1) by (simp split: option.splits)
  ultimately show "csorts_ok (th_sign (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th)
      (th_hyps th) (th_sign th) p z)) (th_shyps (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d)
      | None \<Rightarrow> th_shyps th) (th_hyps th) (th_sign th) p z))"
    by (simp add: csorts_ok_def)
qed

lemma sorts_transfer:
  assumes S: "shyps_ok th" and H: "sign_le (th_sign th) c'"
  shows "shyps_ok (th\<lparr>th_sign := c'\<rparr>)"
proof -
  from H have ps: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))"
    and le: "alg_le (sg_alg (th_sign th)) (sg_alg c')"
    by (simp_all add: sign_le_def)
  from le have "sort_ok (sg_alg c') S" if "sort_ok (sg_alg (th_sign th)) S" for S
    using that by (auto simp: alg_le_def sort_ok_def)
  with shyps_okD[OF S ps] show ?thesis by (simp add: shyps_ok_def csorts_ok_def)
qed

text \<open>
  An extension of a signature keeps the conditions \<^const>\<open>sign_eq\<close> and \<^const>\<open>sign_closed\<close>, so
  a derivation can go on in the extension after \<open>transfer\<close> without new assumptions on these.
\<close>

lemma sign_closed_transfer: "sign_le c c' \<Longrightarrow> sign_closed c \<Longrightarrow> sign_closed c'"
  by (simp add: sign_le_def sign_closed_def)

lemma sign_eq_transfer:
  assumes sl: "sign_le c c'" and se: "sign_eq c"
  shows "sign_eq c'"
proof -
  have ps: "pure_sig (sg_alg c) (sg_ar c)" and ar: "sg_ar c' = sg_ar c" and cl: "sg_close c' = sg_close c"
    and ty: "sg_tyargs c' = sg_tyargs c" and ax: "\<And>A. sg_ax c A \<Longrightarrow> sg_ax c' A"
    and ct: "\<And>a T. sg_consts c a = Some T \<Longrightarrow> sg_consts c' a = Some T"
    using sl by (auto simp: sign_le_def)
  from se have "pure_sig_gen.eq_ok (sg_consts c)" by (simp add: sign_eq_def)
  then have eq: "pure_sig_gen.eq_ok (sg_consts c')"
    using ct by (auto simp: pure_sig_gen.eq_ok_def[OF ps[unfolded pure_sig_def]])
  have pr: "sg_ar c' STR ''prop'' = 0" using se ar by (simp add: sign_eq_def)
  have "prf_eq (sg_alg c') (sg_ar c') (sg_consts c') (sg_close c') (sg_tyargs c') (sg_ax c')" if ip: "is_prf_sig c'"
  proof -
    from ip have ip': "prf_sig (sg_alg c') (sg_ar c') (sg_close c') (sg_tyargs c')" by (simp add: is_prf_sig_def)
    then have "prf_sig (sg_alg c) (sg_ar c) (sg_close c) (sg_tyargs c)" using ps ar cl ty by (simp add: prf_sig_def)
    then have pe: "prf_eq (sg_alg c) (sg_ar c) (sg_consts c) (sg_close c) (sg_tyargs c) (sg_ax c)"
      using se by (simp add: sign_eq_def is_prf_sig_def)
    show ?thesis
      using ip' eq prf_eq.eq_ax[OF pe] prf_eq.eq_close[OF pe] prf_eq.eq_tyargs[OF pe] ax cl ty
      by (intro prf_eq.intro prf_eq_axioms.intro) auto
  qed
  with eq pr show ?thesis by (simp add: sign_eq_def)
qed


subsection \<open>Soundness\<close>

text \<open>Soundness and the invariant of the sort hypotheses, by one induction over the rules:\<close>

lemma derivable_inv: "derivable d \<Longrightarrow> dsem TYPE('u) d \<and> shyps_ok d"
proof (induction rule: derivable.induct)
  case (biresolution st brules cfg vl trace match_flg i s0 x e rule)
  then show ?case by (intro conjI sound_biresolution_gen sorts_biresolution_gen) auto
next
  case (bicompose st rule cfg vl i stpairs Bs Bi C flatten match_flg incremented e nsubgoal xq x)
  then show ?case by (intro conjI sound_bicompose_gen sorts_bicompose_gen) auto
next
  case (assumption st cfg i s0 vl r)
  then show ?case by (intro conjI sound_assumption_gen sorts_assumption_gen) auto
next
  case (flexflex_rule th cfg vl s0 env r)
  then show ?case by (intro conjI sound_flexflex_rule_gen sorts_flexflex_rule_gen) auto
next
  case (axiom c a A invent)
  then show ?case by (intro conjI sound_axiom sorts_axiom) auto
next
  case (strip_shyps th d gts)
  then have D: "dsem TYPE('u) th" and S: "shyps_ok th" by blast+
  show ?case
    by (intro conjI sound_strip_shyps[OF D] sorts_strip_shyps[OF D S])
      (use strip_shyps.hyps shyps_okD[OF S] in auto)
next
  case (unconstrainT th invent r box zn)
  then have D: "dsem TYPE('u) th" and S: "shyps_ok th" by blast+
  show ?case
    by (intro conjI sound_unconstrainT[OF D])
      (use unconstrainT.hyps shyps_okD[OF S] in \<open>auto simp: shyps_ok_def csorts_ok_def sort_ok_def\<close>)
next
  case (transfer th c')
  then show ?case by (intro conjI sound_transfer sorts_transfer) auto
qed ((elim conjE)?, rule conjI, (rule sound_rules; assumption),
  (auto simp: shyps_ok_def csorts_ok_def conv_datar_def split: prod.splits)[1])+

theorem derivable_sem: "derivable d \<Longrightarrow> dsem TYPE('u) d"
  using derivable_inv by blast

text \<open>
  The sort hypotheses of derivable data over a well-formed signature are finitely many sorts
  over its classes.
\<close>

theorem derivable_shyps:
  assumes "derivable d" "pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d))"
  shows "finite (th_shyps d)" "\<forall>S\<in>th_shyps d. sort_ok (sg_alg (th_sign d)) S"
  using derivable_inv[OF assms(1), where 'u = unit] assms(2) by (auto dest: shyps_okD)

lemmas derivable_finite_shyps = derivable_shyps(1)

text \<open>Derivable data are valid in every model of their signature:\<close>

corollary derivable_valid:
  fixes M :: "'u model"
  assumes "derivable d" "is_model (th_sign d) M"
  shows "valid_in (th_sign d) M (th_shyps d) (th_hyps d) (th_tpairs d) (th_prop d)"
  by (rule dsem_valid[OF derivable_sem[OF assms(1)] assms(2)])

text \<open>
  So no derivable theorem without hypotheses and flex-flex pairs, whose sort hypotheses are
  inhabited in a model of its signature, is \<open>\<And>P. P\<close>:
\<close>

corollary derivable_consistent:
  fixes M :: "'u model"
  assumes d: "derivable d" and M: "is_model (th_sign d) M"
    and H: "th_hyps d = []" "th_tpairs d = []" "\<forall>S\<in>th_shyps d. m_sinh M S"
  shows "th_prop d \<noteq> all_const propT $ Abs x propT (Bound 0)"
proof -
  let ?th = "Abs_thm d :: 'u pure_thm"
  have R: "rep_thm ?th = d" by (rule rep_Abs[OF derivable_sem[OF d]])
  have ps: "pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d))"
    by (rule pure_model.axioms(1)[OF is_modelD[OF M]])
  show ?thesis using pure_thm_consistent[of ?th M x] ps M H by (simp add: R)
qed

end
