section \<open>The proofs of derivable theorems\<close>

theory Thm_Derivable_Proofs
  imports "Thm_Soundness.Thm_Derivable" Thm_Transfer_Proofs
begin

text \<open>
  Theory \<open>Thm_Derivable\<close> shows that derivable data are well formed and valid in every model
  (\<open>derivable_sem\<close>). This theory adds the other part of the invariant of theorems: the classic and
  the tight proof of derivable data are valid proofs of their proposition (\<open>derivable_proofs\<close>),
  rule by rule from the theories \<open>Thm_Rules_Proofs\<close> to \<open>Thm_Transfer_Proofs\<close>. Theorem
  \<open>derivable_sound\<close> states both parts.
\<close>

subsection \<open>The invariant on data\<close>

definition dprf :: "thm_data \<Rightarrow> bool" where
  "dprf d \<longleftrightarrow> (is_prf_sig (th_sign d) \<longrightarrow> proofs_ok d)"

definition dok :: "'u itself \<Rightarrow> thm_data \<Rightarrow> bool" where
  "dok U d \<longleftrightarrow> thm_ok U d \<and> cons_ok (th_sign d) (th_constraints d)"

lemma dok_iff: "dok U d \<longleftrightarrow> dsem U d \<and> dprf d"
  by (auto simp: dok_def dsem_def dprf_def thm_ok_def)

lemma dprf_nosig: "\<not> pure_sig (sg_alg (th_sign d)) (sg_ar (th_sign d)) \<Longrightarrow> dprf d"
  by (auto simp: dprf_def is_prf_sig_def prf_sig_def)

subsection \<open>Each rule keeps the proofs valid\<close>

lemma prfs_assumeI:
  assumes D: "cterm_ok ct"
    and H: "okT (assume_rule (cd_rep ct)) r"
  shows "dprf (mk_thm r (cd_sorts ct) [ct_t (cd_rep ct)] (cd_sign ct) (returnW (Hyp (ct_t (cd_rep ct))))
      (zassume_proof (pure_sig_gen.ztargs (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_assume[where ct = ?ct, unfolded R rp_sel]) (use H in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_implies_intr:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "cd_sign ct = th_sign th" "okT (implies_intr (cd_rep ct) (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (filter (\<lambda>h.
      \<not> aconv_term (ct_t (cd_rep ct)) h) (th_hyps th)) (th_sign th) (bindW (th_proof th)
      (\<lambda>p. returnW (implies_intr_proof (ct_t (cd_rep ct)) p))) (bindM (th_zproof th)
      (zimplies_intr_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_implies_intr[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_implies_elim:
  assumes D: "dsem TYPE('u) thAB" "dsem TYPE('u) thA"
    and P: "dprf thAB" "dprf thA"
    and H: "th_sign thAB = th_sign thA" "okT (implies_elim (rp thAB) (rp thA)) r"
  shows "dprf (with_cons (th_constraints thA \<union> th_constraints thAB) (mk_thm r (th_shyps thAB \<union>
      th_shyps thA) (th_hyps thA @ th_hyps thAB) (th_sign thAB) (bindW (th_proof thAB)
      (\<lambda>p. bindW (th_proof thA) (\<lambda>q. returnW (PAppp p q)))) (bindM (th_zproof
      thAB) (\<lambda>p. bindM (th_zproof thA) (\<lambda>q. return (ZAppp p q))))))"
proof -
  let ?thAB = "Abs_thm thAB :: 'u pure_thm" and ?thA = "Abs_thm thA :: 'u pure_thm"
  have R: "rep_thm ?thAB = thAB" "rep_thm ?thA = thA"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_implies_elim[where thAB = ?thAB and thA = ?thA, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_forall_intr:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "cd_sign ct = th_sign th" "sign_closed (th_sign th)" "okT (forall_intr (th_hyps th) (cd_rep ct)
      (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (cd_rep
      ct))) (ct_t (cd_rep ct)) p))) (bindM (th_zproof th) (zforall_intr_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) (ct_T (cd_rep ct)) (var_name (ct_t (cd_rep ct))) (ct_t (cd_rep
      ct))))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_forall_intr[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_forall_elim:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "cd_sign ct = th_sign th" "okT (forall_elim (cd_rep ct) (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (PAppt p (Some (ct_t (cd_rep ct)))))) (bindM
      (th_zproof th) (\<lambda>p. zforall_elim_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
      (ct_t (cd_rep ct)) p))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_forall_elim[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_symmetric:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "sign_eq (th_sign th)" "okT (symmetric (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (symmetric_proof p))) (bindM (th_zproof th) (\<lambda>p. case
      eq_args (th_prop (rp th)) of Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) T t u p | None \<Rightarrow> raise undefined))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_symmetric[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_transitive:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and P: "dprf th1" "dprf th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (transitive (rp th1) (rp th2)) r"
  shows "dprf (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
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
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_transitive[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_abstract_rule:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "cd_sign ct = th_sign th" "sign_eq (th_sign th)" "sign_closed (th_sign th)" "okT
      (abstract_rule_res b (th_hyps th) (cd_rep ct) (rp th)) (r, U, f, g)"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (cd_rep ct)) p)))
      (bindM (th_zproof th) (zabstract_rule_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_T
      (cd_rep ct)) U b (ct_t (cd_rep ct)) f g))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_abstract_rule[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_combination:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and P: "dprf th1" "dprf th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (combination_res (rp th1) (rp th2)) (r,
      T1, U, f, g, t, u)"
  shows "dprf (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (bindW (th_proof th1) (\<lambda>p.
      bindW (th_proof th2) (\<lambda>q. combination_proof f g t u p q))) (bindM (th_zproof th1)
      (\<lambda>p. bindM (th_zproof th2) (\<lambda>q. zcombination_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th1))) T1 U f g t u p q)))))"
proof -
  let ?th1 = "Abs_thm th1 :: 'u pure_thm" and ?th2 = "Abs_thm th2 :: 'u pure_thm"
  have R: "rep_thm ?th1 = th1" "rep_thm ?th2 = th2"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_combination[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_equal_intr:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and P: "dprf th1" "dprf th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (equal_intr (rp th1) (rp th2)) r"
  shows "dprf (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_intr_proof th1 th2)
      (zprf2r zequal_intr_proof th1 th2)))"
proof -
  let ?th1 = "Abs_thm th1 :: 'u pure_thm" and ?th2 = "Abs_thm th2 :: 'u pure_thm"
  have R: "rep_thm ?th1 = th1" "rep_thm ?th2 = th2"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_equal_intr[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded prf2_raw zprf2_raw R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_equal_elim:
  assumes D: "dsem TYPE('u) th1" "dsem TYPE('u) th2"
    and P: "dprf th1" "dprf th2"
    and H: "th_sign th1 = th_sign th2" "sign_eq (th_sign th1)" "okT (equal_elim (rp th1) (rp th2)) r"
  shows "dprf (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_elim_proof th1 th2)
      (zprf2r zequal_elim_proof th1 th2)))"
proof -
  let ?th1 = "Abs_thm th1 :: 'u pure_thm" and ?th2 = "Abs_thm th2 :: 'u pure_thm"
  have R: "rep_thm ?th1 = th1" "rep_thm ?th2 = th2"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_equal_elim[where ?th1.0 = ?th1 and ?th2.0 = ?th2, unfolded prf2_raw zprf2_raw R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_trivial:
  assumes D: "cterm_ok ct"
    and H: "okT (trivial (cd_rep ct)) r"
  shows "dprf (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW trivial_proof) (ztrivial_proof (pure_sig_gen.ztargs
      (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_trivial[where ct = ?ct, unfolded R rp_sel]) (use H in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_weaken:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "cd_sign ct = th_sign th" "okT (weaken (cd_rep ct) (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (ct_t (cd_rep ct) #
      th_hyps th) (th_sign th) (th_proof th) (th_zproof th)))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_weaken[where th = ?th and ct = ?ct, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_renamed_prop:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "okT (renamed_prop P (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (th_proof th)
      (th_zproof th)))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_renamed_prop[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_incr_indexes:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "okT (incr_indexes_thm i (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (incr_indexes_prf
      i (th_proof th)) (incr_indexes_zprf i (th_zproof th))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_incr_indexes[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_permute_prems:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "okT (permute_data j k (rp th)) (r, prems', m)"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (permute_prems_proof prems' j m p))) (bindM (th_zproof th)
      (zpermute_prems_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) prems' j m))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_permute_prems[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_rotate_rule:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "okT (rotate_data k i (rp th)) (r, Bs, Bi', params, asms, m)"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p))) (bindM (th_zproof th)
      (zrotate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi' params asms m))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_rotate_rule[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_varifyT_global:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "sign_closed (th_sign th)" "okT (varifyT_global vl fixed (th_hyps th) (rp th)) (names, r)"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (th_zproof th) (zvarifyT_proof
      names))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th"
    using D by (simp_all add: rep_Abs rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_varifyT_global[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_adjust_maxidx:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
  shows "dprf (with_cons (th_constraints th) (mk_thm (adjust_maxidx_thm i (rp th)) (th_shyps th) (th_hyps th)
      (th_sign th) (th_proof th) (th_zproof th)))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_adjust_maxidx[where th = ?th, unfolded R rp_sel]) (use P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_reflexive:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (reflexive (cd_rep ct)) r"
  shows "dprf (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use H in \<open>auto simp: R conv_data_raw dprf_def intro: pure_sig.conv_ok_reflexive\<close>)
qed

lemma prfs_beta_conversion:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (beta_conversion full (cd_rep ct)) r"
  shows "dprf (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use H in \<open>auto simp: R conv_data_raw dprf_def intro: pure_sig.conv_ok_beta_conversion\<close>)
qed

lemma prfs_eta_conversion:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (eta_conversion (cd_rep ct)) r"
  shows "dprf (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use H in \<open>auto simp: R conv_data_raw dprf_def intro: pure_sig.conv_ok_eta_conversion\<close>)
qed

lemma prfs_eta_long_conversion:
  assumes D: "cterm_ok ct" and H: "sign_eq (cd_sign ct)" "okT (eta_long_conversion (cd_rep ct)) r"
  shows "dprf (conv_datar ct r)"
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_conversion[where ct = ?ct, unfolded conv_data_raw R rp_sel]) (use H in \<open>auto simp: R conv_data_raw dprf_def intro: pure_sig.conv_ok_eta_long_conversion\<close>)
qed

lemma prfs_generalize:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "\<not> (tfrees = [] \<and> frees = [])" "sign_closed (th_sign th)"
      "okT (generalize tfrees frees gi (th_hyps th) (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs th) (th_prop th) p)))
      (bindM (th_zproof th) (zgeneralize_proof tfrees frees gi))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_generalize[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_legacy_freezeT:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "ok (full_prop_of (th_tpairs th) (th_prop th)) P1" "okT (legacy_freezeT vl (rp th)) r"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p)))
      (bindM (th_zproof th) (zlegacy_freezeT_proof vl P1))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_legacy_freezeT[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_of_class:
  assumes D: "cterm_ok ct"
    and H: "ct_t (cd_rep ct) = mk_of_class T c" "tm_sorts (mk_of_class T c) \<subseteq> cd_sorts ct"
      "pure_sig_gen.class_const (sg_alg (cd_sign ct)) (sg_consts (cd_sign ct)) (c + STR ''_class'') c"
      "sign_eq (cd_sign ct)" "okT (Pure_Subst_Rules.of_class (sg_alg (cd_sign ct)) T c) r"
  shows "dprf (solve_data (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW (PClass T c))
      (return (OFCLASSp (ztyp_of T) c))))" (is "dprf (solve_data ?X)")
proof -
  let ?ct = "Abs_cterm ct"
  have R: "rep_cterm ?ct = ct" using D by (simp add: rep_Abs_cterm)
  have S: "thm_sem TYPE(unit) ?X" using sound_of_class[OF D H(1-3,5), where 'u = unit] by (simp add: dsem_def)
  have "proofs_ok ?X" if "is_prf_sig (th_sign ?X)"
    using that by - (rule proofs_ok_of_class[where ct = ?ct, unfolded R], use H in \<open>simp_all add: R\<close>)
  then show ?thesis using proofs_ok_solve_data[OF S] by (auto simp: dprf_def)
qed

lemma prfs_eq_assumption:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "okT (eq_assumption i (rp th)) (n, r)" "okT (dest_state (rp th) i) (tpairs, Bs, Bi, C)"
  shows "dprf (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
      (bindM (th_zproof th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi n))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis unfolding dprf_def proofs_ok_with_cons rp_sel
    by (rule impI, rule proofs_ok_eq_assumption[where th = ?th, unfolded R rp_sel]) (use H P in \<open>simp_all add: R dprf_def\<close>)
qed

lemma prfs_lift_rule:
  assumes D: "cterm_ok ct" "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "ct_T (cd_rep ct) = propT" "cd_sign ct = th_sign th"
  shows "dprf (with_cons (th_constraints th)
      (mk_thm (lift_rule (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th)) (th_shyps th \<union> cd_sorts ct)
        (th_hyps th) (th_sign th)
        (bindW (th_proof th) (\<lambda>p. returnW (lift_rule_proof (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th) p)))
        (bindM (th_zproof th) (lift_rule_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))
          (ct_maxidx (cd_rep ct)) (rp th)))))"
proof -
  let ?th = "Abs_thm th :: 'u pure_thm" and ?ct = "Abs_cterm ct"
  have R: "rep_thm ?th = th" "rep_cterm ?ct = ct" using D by (simp_all add: rep_Abs rep_Abs_cterm)
  have "is_prf_sig (th_sign (lift_rule_data ?ct ?th)) \<Longrightarrow> proofs_ok (lift_rule_data ?ct ?th)"
    by (rule proofs_ok_lift_rule) (use H P in \<open>simp_all add: R dprf_def\<close>)
  then show ?thesis by (simp add: dprf_def lift_rule_data_def Let_def R)
qed

lemma prfs_axiom:
  assumes H: "sg_axioms c a = Some A" "sign_axioms invent c"
  shows "dprf (axiom_data invent c a A)"
  unfolding dprf_def by (rule impI, rule proofs_ok_axiom) (use H in simp_all)

lemma prfs_strip_shyps:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> finite (th_shyps th)"
      "sign_closed (th_sign th)"
      "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> \<forall>S\<in>th_shyps th. sort_ok (sg_alg (th_sign th)) S"
      "d = strip_shyps_rep (sg_alg (th_sign th)) gts (shyps_list (th_shyps th)) (th_hyps th) (rp th)"
  shows "dprf (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (strip_shyps_proof (sg_alg (th_sign th)) d))
      (bindM (th_zproof th) (zstrip_shyps_proof (sg_alg (th_sign th)) d)))"
proof (cases "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))")
  case False
  then show ?thesis by (simp add: dprf_nosig)
next
  case True
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  show ?thesis
    using proofs_ok_strip_shyps[of ?th gts] H(1)[OF True] H(2) H(3)[OF True] H(4) P
    by (simp add: R dprf_def mk_thm_def cong: option.case_cong)
qed

lemma prfs_unconstrainT:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> finite (th_shyps th)"
      "okT (unconstrainT_rep invent (shyps_list (th_shyps th)) (th_hyps th) (rp th)) r"
      "unc_sig_ok box zn invent (th_sign th) (shyps_list (th_shyps th)) (th_prop th) r"
      "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> \<forall>S\<in>th_shyps th. sort_ok (sg_alg (th_sign th)) S"
  shows "dprf (mk_thm r {[]} [] (th_sign th)
      (bindW (th_proof th) (\<lambda>_. liftMP (unconstrain_thm_proof box invent (shyps_list (th_shyps th)) (th_prop th))))
      (bindM (th_zproof th) (\<lambda>_. zunconstrain_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) zn invent
        (shyps_list (th_shyps th)) (th_prop th))))"
proof (cases "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))")
  case False
  then show ?thesis by (simp add: dprf_nosig)
next
  case True
  let ?th = "Abs_thm th :: 'u pure_thm"
  have R: "rep_thm ?th = th" using D by (simp add: rep_Abs)
  have "unc_ok box zn invent (th_sign th) (shyps_list (th_shyps th)) (th_prop th) r"
    using H(3) H(4)[OF True] set_shyps_list[OF H(1)[OF True]] by (simp add: unc_ok_iff)
  then show ?thesis
    using proofs_ok_unconstrainT[of invent ?th r box zn] H(1)[OF True] H(2)
    by (simp add: R dprf_def unconstrainT_data_def mk_thm_def)
qed

lemma prfs_transfer:
  assumes D: "dsem TYPE('u) th" and P: "dprf th" and H: "sign_le (th_sign th) c'"
  shows "dprf (th\<lparr>th_sign := c'\<rparr>)"
  using proofs_ok_transfer[OF conjunct1[OF D[unfolded dsem_def]] _ H] P by (simp add: dprf_def)

lemma prfs_solve_constraints:
  assumes D: "dsem TYPE('u) th" and P: "dprf th"
  shows "dprf (solve_data th)"
  using proofs_ok_solve_data[OF conjunct1[OF D[unfolded dsem_def]]] P by (auto simp: dprf_def)

lemma prfs_instantiate:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "\<forall>(v, cT)\<in>set cTs. ctyp_ok cT \<and> cty_sign cT = th_sign th"
      "\<forall>(v, ct)\<in>set cts. cterm_ok ct \<and> cd_sign ct = th_sign th"
      "\<not> (cTs = [] \<and> cts = [])"
      "okT (instantiate (sg_alg (th_sign th)) bt (map (\<lambda>(v, cT). (v, (cty_T cT, cty_maxidx cT))) cTs)
        (map (\<lambda>(v, ct). (v, (ct_t (cd_rep ct), ct_T (cd_rep ct), ct_maxidx (cd_rep ct)))) cts) (rp th)) r"
  shows "dprf (solve_data (mk_thm r
      (th_shyps th \<union> ((\<Union>(v, cT)\<in>set cTs. cty_sorts cT) \<union> (\<Union>(v, ct)\<in>set cts. cd_sorts ct)))
      (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (instantiate_proof (map (\<lambda>(v, cT). (v, cty_T cT)) cTs)
        (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts) p)))
      (bindM (th_zproof th) (zinstantiate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
        (map (\<lambda>(v, cT). (v, cty_T cT)) cTs) (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts)))))" (is "dprf (solve_data ?X)")
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
  have S: "thm_sem TYPE('u) ?X" using sound_instantiate[OF D H] by (simp add: dsem_def)
  have "proofs_ok ?X" if "is_prf_sig (th_sign ?X)"
    using that by - (rule proofs_ok_instantiate[where th = ?th and cTs = ?cTs and cts = ?cts, unfolded R I],
      use H(4) P g ne in \<open>simp_all add: R I dprf_def\<close>)
  then show ?thesis using proofs_ok_solve_data[OF S] by (auto simp: dprf_def)
qed

lemma prfs_assumption_gen:
  assumes D: "dsem TYPE('u) st"
    and P: "dprf st"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "data_scons st" "okT (assumption i (rp st)) s0"
      "aresult (unify_ops cfg vl) s0 r"
  shows "dprf (ares_data st (aseq_ctx s0) r)"
proof (cases "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))")
  case False
  then show ?thesis by (simp add: dprf_nosig ares_data_def)
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
    using proofs_ok_thm_of_ares_gen[OF ps cfg sc a H(4)] P
    by (simp add: dprf_def thm_of_ares_raw R ares_data_def)
qed

lemma prfs_flexflex_rule_gen:
  assumes D: "dsem TYPE('u) th"
    and P: "dprf th"
    and H: "cfg_alg cfg = sg_alg (th_sign th)" "data_scons th"
      "okT (flexflex_rule (unify_ops cfg vl) (rp th)) s0"
      "fresult (unify_ops cfg vl) smashT (rp th) s0 (env, r)"
  shows "dprf (fres_data (solve_data th) env r)"
proof (cases "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th))")
  case False
  then show ?thesis by (auto simp: dprf_nosig fres_data_def)
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
  have PS: "dprf (solve_data th)" by (rule prfs_solve_constraints[OF D P])
  show ?thesis
    using proofs_ok_thm_of_fres_gen[OF ps cfg sc a res] P PS
    by (simp add: dprf_def thm_of_fres_raw R)
qed

lemma prfs_bicompose_gen:
  assumes D: "dsem TYPE('u) st" "dsem TYPE('u) rule"
    and P: "dprf st" "dprf rule"
    and H: "cfg_alg cfg = sg_alg (th_sign st)" "\<forall>xs. length (vl xs) = length xs" "th_sign rule = th_sign st"
      "data_scons2 st rule"
      "okT (dest_state (rp st) i) (stpairs, Bs, Bi, C)"
      "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (th_sign st)) flatten match_flg incremented (pthm_of (rp st))
        (stpairs, Bs, Bi, C) False e (pthm_of (rp rule)) nsubgoal) xq"
      "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
  shows "dprf (bc_data (th_sign st) i st flatten e rule x)"
proof (cases "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))")
  case False
  then show ?thesis by (simp add: dprf_nosig bc_data_def)
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
    using proofs_ok_thm_of_bc_gen[OF ps cfg vl sr sc d ok H(7)] P
    by (simp add: dprf_def thm_of_bc_raw R bc_data_def)
qed

lemma prfs_biresolution_gen:
  assumes D: "dsem TYPE('u) st" "\<forall>r\<in>set brules. dsem TYPE('u) (snd r)"
    and P: "dprf st" "\<forall>r\<in>set brules. dprf (snd r)"
    and cfg: "cfg_alg cfg = sg_alg (th_sign st)" and vl: "\<forall>xs. length (vl xs) = length xs"
    and sg: "\<forall>r\<in>set brules. th_sign (snd r) = th_sign st"
    and cs: "data_scons st" "\<forall>r\<in>set brules. data_scons (snd r)"
    and br: "okT (biresolution trace match_flg rp brules i (rp st)) s0"
    and res: "pure_sig_gen.brresult (sg_alg (th_sign st)) (unify_ops cfg vl) rp s0 (x, (e, rule))"
  shows "dprf (bres_data (th_sign st) i st e rule x)"
proof (cases "pure_sig (sg_alg (th_sign st)) (sg_ar (th_sign st))")
  case False
  then show ?thesis by (simp add: dprf_nosig bres_data_def)
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
  have po: "proofs_ok (bres_data ?c i st e rule x)" if psig: "is_prf_sig ?c"
  proof -
    interpret prf_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "sg_close ?c" "sg_tyargs ?c"
      using psig by (simp add: is_prf_sig_def prf_sig_gen_of)
    have ps: "proofs_ok st" using P(1) psig by (simp add: dprf_def)
    have pr: "proofs_ok rule" using P(2) r sr psig by (fastforce simp: dprf_def)
    have sg_eq: "th_sign (bres_data ?c i st e rule x) = ?c" by (simp add: bres_data_def)
    show ?thesis unfolding proofs_ok_def Let_def sg_eq
    proof (rule conjI; intro allI impI)
      fix p assume "th_proof (bres_data ?c i st e rule x) = returnW p"
      then obtain rp' sp where rp: "th_proof rule = returnW rp'" and sp: "th_proof st = returnW sp"
        and p: "bires_proof (rp st) i e (rp rule) x rp' sp = returnW p"
        by (auto simp: bres_data_def bindP_eq_returnP)
      have "prf_valid (sg_ax ?c) (set (th_hyps st @ th_hyps rule)) (br_tpairs x) p (br_prop x) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) p"
        by (rule biresolution_proof_valid[OF br res cfg vl' st ru nm(1) _ _ _ _ p])
          (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def thm_rep.truncate_def\<close>)
      moreover have "prf_nolb 0 p"
        by (rule biresolution_proof_closed[OF br res cfg vl' st ru nm(1) _ _ p])
          (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
      ultimately show "prf_valid (sg_ax ?c)
          (set (th_hyps (bres_data ?c i st e rule x))) (th_tpairs (bres_data ?c i st e rule x)) p
          (th_prop (bres_data ?c i st e rule x)) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
        by (simp add: bres_data_def)
    next
      fix z assume "th_zproof (bres_data ?c i st e rule x) = return z"
      then obtain rp' sp where rp: "th_zproof rule = return rp'" and sp: "th_zproof st = return sp"
        and z: "bires_zproof ztargs (rp st) i e (rp rule) x rp' sp = return z"
        by (auto simp: bres_data_def bindZ_eq_returnZ)
      have "zvalid (sg_ax ?c) (set (th_hyps st @ th_hyps rule)) (br_tpairs x) z (br_prop x) \<and> zinv z"
        by (rule biresolution_zproof_valid[OF br res cfg vl' st ru nm(1) _ _ _ _ z])
          (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def thm_rep.truncate_def\<close>)
      moreover have zs: "zinv sp" "znolb 0 sp" "zhyps_ok sp" "zinv rp'" "znolb 0 rp'" "zhyps_ok rp'"
        using ps sp pr rp sr by (simp_all add: proofs_ok_def Let_def)
      note zc = biresolution_zproof_closed[OF br res cfg vl' st ru nm(1) zs(1) zs(4) zs(2) zs(5) z]
      have "znolb 0 z" by (rule zc(1))
      moreover have "zhyps z \<subseteq> zhyps sp \<union> zhyps rp'" by (rule zc(2))
      then have "zhyps_ok z" using zs(3,6) by (auto simp: zhyps_ok_def)
      ultimately show "zvalid (sg_ax ?c)
          (set (th_hyps (bres_data ?c i st e rule x))) (th_tpairs (bres_data ?c i st e rule x)) z
          (th_prop (bres_data ?c i st e rule x)) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
        by (simp add: bres_data_def)
    qed
  qed
  show ?thesis using po by (simp add: dprf_def bres_data_def)
qed

subsection \<open>Derivable theorems with their proofs\<close>

text \<open>
  The rules of \<^const>\<open>derivable\<close> with the classic and the tight proof that each rule constructs,
  and with the conditions on the signature that the proofs need: the equality axioms
  (\<^const>\<open>sign_eq\<close>), closed axioms (\<^const>\<open>sign_closed\<close>), the proof boxes of \<open>unconstrainT\<close>
  (\<^const>\<open>unc_sig_ok\<close>) and the axioms as proof constants (\<^const>\<open>sign_axioms\<close>).
\<close>

inductive pderivable :: "thm_data \<Rightarrow> bool" where
  assumeI: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> okT (assume_rule (cd_rep ct)) r \<Longrightarrow>
    pderivable
     (mk_thm r (cd_sorts ct) [ct_t (cd_rep ct)] (cd_sign ct) (returnW (Hyp (ct_t (cd_rep ct))))
      (zassume_proof (pure_sig_gen.ztargs (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
| implies_intr: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> pderivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> okT (implies_intr (cd_rep ct) (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (filter (\<lambda>h.
      \<not> aconv_term (ct_t (cd_rep ct)) h) (th_hyps th)) (th_sign th) (bindW (th_proof th)
      (\<lambda>p. returnW (implies_intr_proof (ct_t (cd_rep ct)) p))) (bindM (th_zproof th)
      (zimplies_intr_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))))))"
| implies_elim: "pderivable thAB \<Longrightarrow> pderivable thA \<Longrightarrow> th_sign thAB = th_sign thA
    \<Longrightarrow> okT (implies_elim (rp thAB) (rp thA)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints thA \<union> th_constraints thAB) (mk_thm r (th_shyps thAB \<union>
      th_shyps thA) (th_hyps thA @ th_hyps thAB) (th_sign thAB) (bindW (th_proof thAB)
      (\<lambda>p. bindW (th_proof thA) (\<lambda>q. returnW (PAppp p q)))) (bindM (th_zproof
      thAB) (\<lambda>p. bindM (th_zproof thA) (\<lambda>q. return (ZAppp p q))))))"
| forall_intr: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> pderivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow> okT (forall_intr (th_hyps th)
    (cd_rep ct) (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (cd_rep
      ct))) (ct_t (cd_rep ct)) p))) (bindM (th_zproof th) (zforall_intr_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) (ct_T (cd_rep ct)) (var_name (ct_t (cd_rep ct))) (ct_t (cd_rep
      ct))))))"
| forall_elim: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> pderivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> okT (forall_elim (cd_rep ct) (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (PAppt p (Some (ct_t (cd_rep ct)))))) (bindM
      (th_zproof th) (\<lambda>p. zforall_elim_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
      (ct_t (cd_rep ct)) p))))"
| symmetric: "pderivable th \<Longrightarrow> sign_eq (th_sign th) \<Longrightarrow> okT (symmetric (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (symmetric_proof p))) (bindM (th_zproof th) (\<lambda>p. case
      eq_args (th_prop (rp th)) of Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th))) T t u p | None \<Rightarrow> raise undefined))))"
| transitive: "pderivable th1 \<Longrightarrow> pderivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (transitive (rp th1) (rp th2)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (bindW (th_proof th1) (\<lambda>p.
      bindW (th_proof th2) (\<lambda>q. case eq_args (th_prop (rp th1)) of Some (T, t1, u)
      \<Rightarrow> returnW (transitive_proof T u p q) | None \<Rightarrow> raiseW undefined)))
      (bindM (th_zproof th1) (\<lambda>p. bindM (th_zproof th2) (\<lambda>q. case (eq_args
      (th_prop (rp th1)), eq_args (th_prop (rp th2))) of (Some (T, t1, u), Some (_, _, t2))
      \<Rightarrow> ztransitive_proof (pure_sig_gen.ztargs (sg_consts (th_sign th1))) T t1 u t2 p q |
      _ \<Rightarrow> raise undefined)))))"
| abstract_rule: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> pderivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> sign_eq (th_sign th) \<Longrightarrow> sign_closed (th_sign th)
    \<Longrightarrow> okT (abstract_rule_res b (th_hyps th) (cd_rep ct) (rp th)) (r, U, f, g) \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (th_hyps th) (th_sign
      th) (bindW (th_proof th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (cd_rep ct)) p)))
      (bindM (th_zproof th) (zabstract_rule_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_T
      (cd_rep ct)) U b (ct_t (cd_rep ct)) f g))))"
| combination: "pderivable th1 \<Longrightarrow> pderivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (combination_res (rp th1) (rp
    th2)) (r, T1, U, f, g, t, u) \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (bindW (th_proof th1) (\<lambda>p.
      bindW (th_proof th2) (\<lambda>q. combination_proof f g t u p q))) (bindM (th_zproof th1)
      (\<lambda>p. bindM (th_zproof th2) (\<lambda>q. zcombination_proof (pure_sig_gen.ztargs
      (sg_consts (th_sign th1))) T1 U f g t u p q)))))"
| equal_intr: "pderivable th1 \<Longrightarrow> pderivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (equal_intr (rp th1) (rp th2)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_intr_proof th1 th2)
      (zprf2r zequal_intr_proof th1 th2)))"
| equal_elim: "pderivable th1 \<Longrightarrow> pderivable th2 \<Longrightarrow> th_sign th1 = th_sign th2
    \<Longrightarrow> sign_eq (th_sign th1) \<Longrightarrow> okT (equal_elim (rp th1) (rp th2)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th1 \<union> th_constraints th2) (mk_thm r (th_shyps th1 \<union>
      th_shyps th2) (th_hyps th1 @ th_hyps th2) (th_sign th1) (prf2r equal_elim_proof th1 th2)
      (zprf2r zequal_elim_proof th1 th2)))"
| trivial: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> okT (trivial (cd_rep ct)) r \<Longrightarrow>
    pderivable
     (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW trivial_proof) (ztrivial_proof (pure_sig_gen.ztargs
      (sg_consts (cd_sign ct))) (ct_t (cd_rep ct))))"
| weaken: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> pderivable th \<Longrightarrow> cd_sign ct = th_sign th
    \<Longrightarrow> okT (weaken (cd_rep ct) (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (cd_sorts ct \<union> th_shyps th) (ct_t (cd_rep ct) #
      th_hyps th) (th_sign th) (th_proof th) (th_zproof th)))"
| renamed_prop: "pderivable th \<Longrightarrow> okT (renamed_prop P (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (th_proof th)
      (th_zproof th)))"
| incr_indexes: "pderivable th \<Longrightarrow> okT (incr_indexes_thm i (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (incr_indexes_prf
      i (th_proof th)) (incr_indexes_zprf i (th_zproof th))))"
| permute_prems: "pderivable th \<Longrightarrow> okT (permute_data j k (rp th)) (r, prems', m) \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (permute_prems_proof prems' j m p))) (bindM (th_zproof th)
      (zpermute_prems_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) prems' j m))))"
| rotate_rule: "pderivable th \<Longrightarrow> okT (rotate_data k i (rp th)) (r, Bs, Bi', params, asms, m) \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p))) (bindM (th_zproof th)
      (zrotate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi' params asms m))))"
| varifyT_global: "pderivable th \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow> okT (varifyT_global vl
    fixed (th_hyps th) (rp th)) (names, r) \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th) (bindW (th_proof
      th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (th_zproof th) (zvarifyT_proof
      names))))"
| adjust_maxidx: "pderivable th \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm (adjust_maxidx_thm i (rp th)) (th_shyps th) (th_hyps th)
      (th_sign th) (th_proof th) (th_zproof th)))"
| reflexive: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow> okT (reflexive (cd_rep ct)) r \<Longrightarrow>
    pderivable (conv_datar ct r)"
| beta_conversion: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow> okT (beta_conversion full (cd_rep ct)) r \<Longrightarrow>
    pderivable (conv_datar ct r)"
| eta_conversion: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow> okT (eta_conversion (cd_rep ct)) r \<Longrightarrow>
    pderivable (conv_datar ct r)"
| eta_long_conversion: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> sign_eq (cd_sign ct) \<Longrightarrow>
    okT (eta_long_conversion (cd_rep ct)) r \<Longrightarrow> pderivable (conv_datar ct r)"
| generalize: "pderivable th \<Longrightarrow> \<not> (tfrees = [] \<and> frees = []) \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow>
    okT (generalize tfrees frees gi (th_hyps th) (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs th) (th_prop th) p)))
      (bindM (th_zproof th) (zgeneralize_proof tfrees frees gi))))"
| legacy_freezeT: "pderivable th \<Longrightarrow> ok (full_prop_of (th_tpairs th) (th_prop th)) P1 \<Longrightarrow>
    okT (legacy_freezeT vl (rp th)) r \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p)))
      (bindM (th_zproof th) (zlegacy_freezeT_proof vl P1))))"
| of_class: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> ct_t (cd_rep ct) = mk_of_class T c \<Longrightarrow>
    tm_sorts (mk_of_class T c) \<subseteq> cd_sorts ct \<Longrightarrow>
    pure_sig_gen.class_const (sg_alg (cd_sign ct)) (sg_consts (cd_sign ct)) (c + STR ''_class'') c \<Longrightarrow>
    sign_eq (cd_sign ct) \<Longrightarrow> okT (Pure_Subst_Rules.of_class (sg_alg (cd_sign ct)) T c) r \<Longrightarrow>
    pderivable
     (solve_data (mk_thm r (cd_sorts ct) [] (cd_sign ct) (returnW (PClass T c))
      (return (OFCLASSp (ztyp_of T) c))))"
| eq_assumption: "pderivable th \<Longrightarrow> okT (eq_assumption i (rp th)) (n, r) \<Longrightarrow>
    okT (dest_state (rp th) i) (tpairs, Bs, Bi, C) \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th) (mk_thm r (th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
      (bindM (th_zproof th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) Bs Bi n))))"
| lift_rule: "cterm_ok ct \<Longrightarrow> csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow> pderivable th \<Longrightarrow> ct_T (cd_rep ct) = propT \<Longrightarrow> cd_sign ct = th_sign th \<Longrightarrow>
    pderivable
     (with_cons (th_constraints th)
      (mk_thm (lift_rule (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th)) (th_shyps th \<union> cd_sorts ct)
        (th_hyps th) (th_sign th)
        (bindW (th_proof th) (\<lambda>p. returnW (lift_rule_proof (ct_t (cd_rep ct)) (ct_maxidx (cd_rep ct)) (rp th) p)))
        (bindM (th_zproof th) (lift_rule_zproof (pure_sig_gen.ztargs (sg_consts (th_sign th))) (ct_t (cd_rep ct))
          (ct_maxidx (cd_rep ct)) (rp th)))))"
| axiom: "sg_axioms c a = Some A \<Longrightarrow> sign_axioms invent c \<Longrightarrow> pderivable (axiom_data invent c a A)"
| strip_shyps: "pderivable th \<Longrightarrow> sign_closed (th_sign th) \<Longrightarrow>
    d = strip_shyps_rep (sg_alg (th_sign th)) gts (shyps_list (th_shyps th)) (th_hyps th) (rp th) \<Longrightarrow>
    pderivable
     (mk_thm (rp th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> th_shyps th) (th_hyps th) (th_sign th)
      (bindW (th_proof th) (strip_shyps_proof (sg_alg (th_sign th)) d))
      (bindM (th_zproof th) (zstrip_shyps_proof (sg_alg (th_sign th)) d)))"
| unconstrainT: "pderivable th \<Longrightarrow>
    okT (unconstrainT_rep invent (shyps_list (th_shyps th)) (th_hyps th) (rp th)) r \<Longrightarrow>
    unc_sig_ok box zn invent (th_sign th) (shyps_list (th_shyps th)) (th_prop th) r \<Longrightarrow>
    pderivable
     (mk_thm r {[]} [] (th_sign th)
      (bindW (th_proof th) (\<lambda>_. liftMP (unconstrain_thm_proof box invent (shyps_list (th_shyps th)) (th_prop th))))
      (bindM (th_zproof th) (\<lambda>_. zunconstrain_proof (pure_sig_gen.ztargs (sg_consts (th_sign th))) zn invent
        (shyps_list (th_shyps th)) (th_prop th))))"
| transfer: "pderivable th \<Longrightarrow> sign_le (th_sign th) c' \<Longrightarrow> pderivable (th\<lparr>th_sign := c'\<rparr>)"
| solve_constraints: "pderivable th \<Longrightarrow> pderivable (solve_data th)"
| instantiate: "pderivable th \<Longrightarrow>
    \<forall>(v, cT)\<in>set cTs. ctyp_ok cT \<and> cty_sign cT = th_sign th \<Longrightarrow>
    \<forall>(v, ct)\<in>set cts. cterm_ok ct \<and> cd_sign ct = th_sign th \<Longrightarrow>
    \<forall>(v, cT)\<in>set cTs. csorts_ok (cty_sign cT) (cty_sorts cT) \<Longrightarrow>
    \<forall>(v, ct)\<in>set cts. csorts_ok (cd_sign ct) (cd_sorts ct) \<Longrightarrow>
    \<not> (cTs = [] \<and> cts = []) \<Longrightarrow>
    okT (instantiate (sg_alg (th_sign th)) bt (map (\<lambda>(v, cT). (v, (cty_T cT, cty_maxidx cT))) cTs)
      (map (\<lambda>(v, ct). (v, (ct_t (cd_rep ct), ct_T (cd_rep ct), ct_maxidx (cd_rep ct)))) cts) (rp th)) r \<Longrightarrow>
    pderivable
     (solve_data (mk_thm r
      (th_shyps th \<union> ((\<Union>(v, cT)\<in>set cTs. cty_sorts cT) \<union> (\<Union>(v, ct)\<in>set cts. cd_sorts ct)))
      (th_hyps th) (th_sign th)
      (bindW (th_proof th) (\<lambda>p. returnW (instantiate_proof (map (\<lambda>(v, cT). (v, cty_T cT)) cTs)
        (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts) p)))
      (bindM (th_zproof th) (zinstantiate_proof (pure_sig_gen.ztargs (sg_consts (th_sign th)))
        (map (\<lambda>(v, cT). (v, cty_T cT)) cTs) (map (\<lambda>(v, ct). (v, ct_t (cd_rep ct))) cts)))))"
| assumption: "pderivable st \<Longrightarrow> cfg_alg cfg = sg_alg (th_sign st) \<Longrightarrow> data_scons st \<Longrightarrow>
    okT (assumption i (rp st)) s0 \<Longrightarrow> aresult (unify_ops cfg vl) s0 r \<Longrightarrow>
    pderivable (ares_data st (aseq_ctx s0) r)"
| flexflex_rule: "pderivable th \<Longrightarrow> cfg_alg cfg = sg_alg (th_sign th) \<Longrightarrow> data_scons th \<Longrightarrow>
    okT (flexflex_rule (unify_ops cfg vl) (rp th)) s0 \<Longrightarrow>
    fresult (unify_ops cfg vl) smashT (rp th) s0 (env, r) \<Longrightarrow>
    pderivable (fres_data (solve_data th) env r)"
| bicompose: "pderivable st \<Longrightarrow> pderivable rule \<Longrightarrow> cfg_alg cfg = sg_alg (th_sign st) \<Longrightarrow>
    \<forall>xs. length (vl xs) = length xs \<Longrightarrow> th_sign rule = th_sign st \<Longrightarrow>
    data_scons2 st rule \<Longrightarrow>
    okT (dest_state (rp st) i) (stpairs, Bs, Bi, C) \<Longrightarrow>
    okT (bicompose_aux (unify_ops cfg vl) (sg_alg (th_sign st)) flatten match_flg incremented (pthm_of (rp st))
      (stpairs, Bs, Bi, C) False e (pthm_of (rp rule)) nsubgoal) xq \<Longrightarrow>
    pure_sig_gen.bresult (unify_ops cfg vl) xq x \<Longrightarrow>
    pderivable (bc_data (th_sign st) i st flatten e rule x)"
| biresolution: "pderivable st \<Longrightarrow> \<forall>r\<in>set brules. pderivable (snd r) \<Longrightarrow>
    cfg_alg cfg = sg_alg (th_sign st) \<Longrightarrow> \<forall>xs. length (vl xs) = length xs \<Longrightarrow>
    \<forall>r\<in>set brules. th_sign (snd r) = th_sign st \<Longrightarrow>
    data_scons st \<Longrightarrow> \<forall>r\<in>set brules. data_scons (snd r) \<Longrightarrow>
    okT (biresolution trace match_flg rp brules i (rp st)) s0 \<Longrightarrow>
    pure_sig_gen.brresult (sg_alg (th_sign st)) (unify_ops cfg vl) rp s0 (x, (e, rule)) \<Longrightarrow>
    pderivable (bres_data (th_sign st) i st e rule x)"

text \<open>Without the proofs, these are derivable theorems:\<close>

lemma solve_data_mk_thm: "solve_data (mk_thm r Sh hs c p z) = mk_thm r Sh hs c p (zsolve z)"
  by (simp add: solve_data_def mk_thm_def)

lemma solve_data_core:
  "solve_data th = mk_thm (rp th) (th_shyps th) (th_hyps th) (th_sign th) (th_proof th) (zsolve (th_zproof th))"
  by (cases th) (simp add: solve_data_def mk_thm_def thm_rep.truncate_def)

lemma fres_data_core:
  "fres_data (solve_data th) env r = fres_core th env r (th_proof (fres_data (solve_data th) env r))
    (th_zproof (fres_data (solve_data th) env r))"
  by (simp add: fres_data_def fres_core_def solve_data_core mk_thm_def with_cons_def)

lemma bc_data_core:
  "bc_data (th_sign st) i st flatten e rule x = comp_core st rule x (th_proof (bc_data (th_sign st) i st flatten e rule x))
    (th_zproof (bc_data (th_sign st) i st flatten e rule x))"
  by (simp add: bc_data_def comp_core_def Un_commute)

lemma bres_data_core:
  "bres_data (th_sign st) i st e rule x = comp_core st rule x (th_proof (bres_data (th_sign st) i st e rule x))
    (th_zproof (bres_data (th_sign st) i st e rule x))"
  by (simp add: bres_data_def comp_core_def)

theorem pderivable_derivable: "pderivable d \<Longrightarrow> derivable d"
proof (induction rule: pderivable.induct)
  case (flexflex_rule th cfg vl s0 env r)
  then show ?case by (subst fres_data_core) (rule derivable.flexflex_rule)
next
  case (bicompose st rule cfg vl i stpairs Bs Bi C flatten match_flg incremented e nsubgoal xq x)
  then show ?case by (subst bc_data_core) (rule derivable.bicompose)
next
  case (biresolution st brules cfg vl trace match_flg i s0 x e rule)
  then show ?case by (subst bres_data_core) (rule derivable.biresolution; blast)
next
  case (solve_constraints th)
  then show ?case by (subst solve_data_core) (rule derivable.solve_constraints)
next
  case (transfer th c')
  show ?case by (rule derivable.transfer[OF transfer.IH transfer.hyps(2)])
qed (unfold conv_datar_def axiom_data_def ares_data_def solve_data_mk_thm,
  (rule derivable.intros; (assumption | erule sign_eq_eqs | erule unc_sig_sem | erule sign_axioms_sem)+)+)

lemmas pderivable_sem = derivable_sem[OF pderivable_derivable]
  and pderivable_shyps = derivable_shyps[OF pderivable_derivable]

subsection \<open>Soundness\<close>

lemmas prfs_rules =
  prfs_assumeI prfs_implies_intr prfs_implies_elim prfs_forall_intr prfs_forall_elim
  prfs_symmetric prfs_transitive prfs_abstract_rule prfs_combination prfs_equal_intr
  prfs_equal_elim prfs_trivial prfs_weaken prfs_renamed_prop prfs_incr_indexes
  prfs_permute_prems prfs_rotate_rule prfs_varifyT_global prfs_adjust_maxidx prfs_reflexive
  prfs_beta_conversion prfs_eta_conversion prfs_eta_long_conversion prfs_generalize prfs_legacy_freezeT
  prfs_of_class prfs_eq_assumption prfs_lift_rule prfs_axiom prfs_solve_constraints prfs_instantiate

text \<open>The proofs of derivable data are valid, by induction over the rules:\<close>

lemma pderivable_prf: "pderivable d \<Longrightarrow> dprf d"
proof (induction rule: pderivable.induct)
  case (biresolution st brules cfg vl trace match_flg i s0 x e rule)
  then show ?case by (intro prfs_biresolution_gen[where 'u = unit]) (auto intro: pderivable_sem)
next
  case (bicompose st rule cfg vl i stpairs Bs Bi C flatten match_flg incremented e nsubgoal xq x)
  then show ?case by (intro prfs_bicompose_gen[where 'u = unit]) (auto intro: pderivable_sem)
next
  case (assumption st cfg i s0 vl r)
  then show ?case by (intro prfs_assumption_gen[where 'u = unit]) (auto intro: pderivable_sem)
next
  case (flexflex_rule th cfg vl s0 env r)
  then show ?case by (intro prfs_flexflex_rule_gen[where 'u = unit]) (auto intro: pderivable_sem)
next
  case (strip_shyps th d gts)
  note D = pderivable_sem[OF strip_shyps.hyps(1), where 'u = unit]
  show ?case
    by (rule prfs_strip_shyps[OF D strip_shyps.IH])
      (use strip_shyps.hyps pderivable_shyps[OF strip_shyps.hyps(1)] in auto)
next
  case (unconstrainT th invent r box zn)
  note D = pderivable_sem[OF unconstrainT.hyps(1), where 'u = unit]
  show ?case
    by (rule prfs_unconstrainT[OF D unconstrainT.IH])
      (use unconstrainT.hyps pderivable_shyps[OF unconstrainT.hyps(1)] in auto)
next
  case (transfer th c')
  then show ?case by (intro prfs_transfer[where 'u = unit]) (auto intro: pderivable_sem)
qed (rule prfs_rules; (assumption | rule pderivable_sem[where 'u = unit])+)+

theorem derivable_proofs:
  assumes "pderivable d" "is_prf_sig (th_sign d)"
  shows "proofs_ok d"
  using pderivable_prf[OF assms(1)] assms(2) by (simp add: dprf_def)

text \<open>
  The data that the rules construct with their proofs satisfy the invariant of theorems: they
  are well formed, valid in every model of their signature, and their proofs are valid.
\<close>

theorem derivable_sound: "pderivable d \<Longrightarrow> dok TYPE('u) d"
  by (simp add: dok_iff pderivable_sem pderivable_prf)

end
