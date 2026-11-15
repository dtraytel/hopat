section \<open>Proofs: Thm_Rules3\<close>

theory Thm_Rules3_Proofs
  imports Thm_Rules3 Thm_Rules2_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Rules3\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

lemma proofs_ok_eq_assumption:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (eq_assumption i (rep_of th)) (n, r)" and d: "okT (dest_state (rep_of th) i) (tpairs, Bs, Bi, C)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
    (bindM (zproof_of th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) Bs Bi n)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
    (bindM (zproof_of th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) Bs Bi n)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  have P: "th_prop (rep_of th) = list_implies (Bs @ [Bi]) C"
    if w: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (th_prop (rep_of th))" and ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    show ?thesis using list_implies_strip_prems[OF okT_dest_state(2)[OF d] wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
  note P' = P[OF w ps]
  have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
  have pA: "pnn A" if "A \<in> set (Bs @ [Bi])" for A
    using pP that P' typs_list_implies_sub(1)[OF that, of C] by (auto simp: pnn_def vars_list_implies)
  have cA: "closed A" if "A \<in> set (Bs @ [Bi])" for A
    using wtpD(1)[OF w] that P' by (auto simp: closed_def loose_bvar_list_implies)
  have H: "\<forall>h\<in>set (hyps_of th). closed h" using w0 by (auto simp: thm_wf_def wt_thm_def wtp_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = assumption_proof Bs Bi n q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule eq_assumption_proof_valid[OF ok d vq(1) w])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using vq(2,3) by (auto simp: pf assumption_proof_def prf_idx_mk_AbsP prf_idx_proof_combP prf_idx_mk_asm_prf
        prf_nolb_proof_combP prf_nolb_mk_asm_prf)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (eq_assumption_zproof ztargs Bs Bi n) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "eq_assumption_zproof ztargs Bs Bi n q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zeq_assumption_proof_valid[OF ok d vq(1) w _ H z]) (use pA pnn_noneg in blast)
    moreover have "zinv z \<and> znolb 0 z \<and> zhyps z \<subseteq> zhyps q"
    proof -
      let ?env = "empty_env (-1) :: env"
      from z obtain Ns Z0 N where Ns: "list_all2 (\<lambda>B N. \<exists>Z. zterm_of ztargs B = return Z \<and>
          znorm_term ztargs ?env Z = return N) Bs Ns"
        and Z0: "zterm_of ztargs Bi = return Z0" and N: "znorm_term ztargs ?env Z0 = return N"
        and bn: "beta_norm_prooft (ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
          [zmk_asm_prf N n (zasm_count (-1) Bi)]))) = Some z"
        by (auto simp: eq_assumption_zproof_def zassumption_proof_def znorm_proof_def Let_def bindZ_eq_returnZ
          mapZ_eq_returnZ liftOZ_eq_returnZ)
      have nt: "zterm_ok N' \<and> \<not> zloose N' 0" if "zterm_of ztargs A = return Z" "znorm_term ztargs ?env Z = return N'"
        "A \<in> set (Bs @ [Bi])" for A Z N'
      proof -
        have bt: "beta_norm_term Z = Some N'" using that(2) by (simp add: znorm_term_def liftOZ_eq_returnZ env_is_empty_def empty_env_def)
        show ?thesis using zterm_ok_beta_norm_term[OF bt zterm_ok_zterm_of_pnn[OF that(1) pA[OF that(3)]]]
          zloose_beta_norm_term[OF bt, of 0] zloose_zterm_of[OF that(1)] cA[OF that(3)] by (simp add: closed_def)
      qed
      have Nsz: "zterm_ok N' \<and> \<not> zloose N' 0" if "N' \<in> set Ns" for N'
      proof -
        from that obtain j where j: "j < length Ns" "N' = Ns ! j" by (auto simp: in_set_conv_nth)
        have jl: "j < length Bs" using j(1) list_all2_lengthD[OF Ns] by simp
        from list_all2_nthD[OF Ns jl] j(2) obtain Z where "zterm_of ztargs (Bs ! j) = return Z"
          "znorm_term ztargs ?env Z = return N'" by blast
        with nt nth_mem[OF jl] show ?thesis by simp
      qed
      have Nz: "zterm_ok N \<and> \<not> zloose N 0" by (rule nt[OF Z0 N]) simp
      have arg: "zinv (ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
          [zmk_asm_prf N n (zasm_count (-1) Bi)])))"
        using vq(2) Nsz Nz zinv_zmk_asm_prf by (auto simp: zinv_ZAbsps zinv_ZAppps)
      have arg2: "znolb 0 (ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
          [zmk_asm_prf N n (zasm_count (-1) Bi)])))"
        using vq(3) Nsz Nz zmk_asm_prf_closed by (auto simp: znolb_ZAbsps znolb_ZAppps)
      from zinv_beta_norm_prooft[OF bn arg] beta_norm_prooft_closed[OF bn, of 0] arg2
      show ?thesis using zmk_asm_prf_closed[of N 0] Nz by (auto simp: zhyps_ZAppps)
    qed
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" using vq(4) by (auto simp: zhyps_ok_def)
  qed
qed

lemma proofs_ok_thm_of_ares:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and cs: "thm_cons state"
    and a: "okT (assumption i (rep_of state)) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
  shows "proofs_ok (thm_of_ares (state :: 'u pure_thm) (aseq_ctx s0) r)"
proof -
  let ?c = "sign_of state" and ?th = "thm_of_ares state (aseq_ctx s0) r"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv[OF ps cs] by simp
  note ti = assumption_thm_inv[OF a res cfg st]
  obtain tpairs Bs Bi C params asms concl l env tps where
    "okT (dest_state (rep_of state) i) (tpairs, Bs, Bi, C)" "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) asms 1" "l < length asms"
    "ures (empty_env (th_maxidx (rep_of state))) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and nt: "okT (newth (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    "sinv (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))
      (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (empty_env (th_maxidx (rep_of state)))
      (tdps ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs))"
    by (rule assumption_result[OF a res cfg st])
  have mx: "th_maxidx (ar_thm r) = maxidx (ar_env r)" using okT_newth[OF nt(1)] by simp
  have ws: "wt_thm (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using st by (simp add: thm_inv_def)
  interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def)
  have po: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have sg: "th_sign ?th = ?c" by (simp add: thm_of_ares_def)
  show ?thesis unfolding proofs_ok_def Let_def sg
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof ?th = returnW p"
    then obtain pf where pf: "proof_of state = returnW pf" and pr: "ares_proof (aseq_ctx s0) r pf = returnW p"
      by (auto simp: thm_of_ares_def bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of state)) (th_tpairs (rep_of state)) pf (th_prop (rep_of state))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    from assumption_proof_ok[OF a res cfg st pr vq]
    show "prf_valid (sg_ax ?c) (set (th_hyps ?th)) (th_tpairs ?th) p (th_prop ?th) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_ares_def)
  next
    fix z assume "th_zproof ?th = return z"
    then obtain pf where pf: "zproof_of state = return pf"
      and z: "ares_zproof ztargs (rep_of state) (aseq_ctx s0) r pf = return z"
      by (auto simp: thm_of_ares_def bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of state)) (th_tpairs (rep_of state)) pf (th_prop (rep_of state))"
      "zinv pf" "znolb 0 pf" "zhyps_ok pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    have H: "\<forall>h\<in>set (hyps_of state). closed h" using ws by (auto simp: wt_thm_def dest: wtpD(1))
    note zr = assumption_zproof_ok[OF a res cfg st z vq(1-3) H]
    have "zhyps_ok z" using zhyps_ok_mono[OF vq(4)] zr by blast
    with zr show "zvalid (sg_ax ?c) (set (th_hyps ?th)) (th_tpairs ?th) z (th_prop ?th) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z"
      by (simp add: thm_of_ares_def)
  qed
qed

lemma proofs_ok_thm_of_ares_gen:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    and a: "okT (assumption i (rep_of state)) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and nb: "binds_none (ar_env r) (ares_clash state)"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
  shows "proofs_ok (thm_of_ares (state :: 'u pure_thm) (aseq_ctx s0) r)"
proof -
  let ?c = "sign_of state" and ?th = "thm_of_ares state (aseq_ctx s0) r"
  let ?L = "ares_clash state"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps] sc by simp
  have nfL: "nfree (ar_env r)" using nb by (rule nfree_binds_none)
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  note ti = assumption_thm_inv[OF a res cfg st nfL l0]
  obtain tpairs Bs Bi C params asms concl l env tps where
    "okT (dest_state (rep_of state) i) (tpairs, Bs, Bi, C)" "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) asms 1" "l < length asms"
    "ures (empty_env (th_maxidx (rep_of state))) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and nt: "okT (newth (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    "sinv (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))
      (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (empty_env (th_maxidx (rep_of state)))
      (tdps ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs))"
    by (rule assumption_result[OF a res cfg st])
  have mx: "th_maxidx (ar_thm r) = maxidx (ar_env r)" using okT_newth[OF nt(1)] by simp
  have ws: "wt_thm (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using st by (simp add: thm_inv_def)
  interpret prf_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def prf_sig_gen_of)
  have po: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have sg: "th_sign ?th = ?c" by (simp add: thm_of_ares_def)
  show ?thesis unfolding proofs_ok_def Let_def sg
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof ?th = returnW p"
    then obtain pf where pf: "proof_of state = returnW pf" and pr: "ares_proof (aseq_ctx s0) r pf = returnW p"
      by (auto simp: thm_of_ares_def bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of state)) (th_tpairs (rep_of state)) pf (th_prop (rep_of state))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    from assumption_proof_ok[OF a res cfg st pr vq nfL l0]
    show "prf_valid (sg_ax ?c) (set (th_hyps ?th)) (th_tpairs ?th) p (th_prop ?th) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_ares_def)
  next
    fix z assume "th_zproof ?th = return z"
    then obtain pf where pf: "zproof_of state = return pf"
      and z: "ares_zproof ztargs (rep_of state) (aseq_ctx s0) r pf = return z"
      by (auto simp: thm_of_ares_def bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of state)) (th_tpairs (rep_of state)) pf (th_prop (rep_of state))"
      "zinv pf" "znolb 0 pf" "zhyps_ok pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    have H: "\<forall>h\<in>set (hyps_of state). closed h" using ws by (auto simp: wt_thm_def dest: wtpD(1))
    note zr = assumption_zproof_ok[OF a res cfg st z vq(1-3) H nfL l0]
    have "zhyps_ok z" using zhyps_ok_mono[OF vq(4)] zr by blast
    with zr show "zvalid (sg_ax ?c) (set (th_hyps ?th)) (th_tpairs ?th) z (th_prop ?th) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z"
      by (simp add: thm_of_ares_def)
  qed
qed

lemma proofs_ok_thm_of_fres:
  assumes ps: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of th)" and cs: "thm_cons th"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of th) s0 (env, r)"
    and psig: "is_prf_sig (sign_of th)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "proofs_ok (thm_of_fres (th :: 'u pure_thm) env r)"
proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs (rep_of th)). aconv_term t u)")
  case True
  then show ?thesis using po_th psig by (simp add: thm_of_fres_def)
next
  case False
  let ?c = "sign_of th" and ?th = "thm_of_fres th env r"
  have eq: "?th = with_cons (env_constraints env) (mk_thm r (shyps_of th \<union> env_sorts env) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (norm_proof_remove_types env))
      (bindM (zproof_of th) (flexflex_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (rep_of th) env)))"
    unfolding thm_of_fres_def if_not_P[OF False] ..
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have st: "thm_inv (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_inv[OF ps cs] by simp
  note ti = flexflex_thm_inv[OF a res cfg st]
  have ws: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using st by (simp add: thm_inv_def)
  interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def)
  have po: "proofs_ok (rep_thm th)" by (rule po_th[OF psig])
  show ?thesis unfolding proofs_ok_def Let_def eq with_cons_sel mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix p assume "bindW (proof_of th) (norm_proof_remove_types env) = returnW p"
    then obtain pf where pf: "proof_of th = returnW pf" and nq: "norm_proof_remove_types env pf = returnW p"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    from flexflex_proof_ok[OF a res cfg st False nq vq]
    show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) p (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" .
  next
    fix z assume "bindM (zproof_of th) (flexflex_zproof ztargs (rep_of th) env) = return z"
    then obtain pf where pf: "zproof_of th = return pf" and z: "flexflex_zproof ztargs (rep_of th) env pf = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "zinv pf" "znolb 0 pf" "zhyps_ok pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    have H: "\<forall>h\<in>set (hyps_of th). closed h" using ws by (auto simp: wt_thm_def dest: wtpD(1))
    note zr = flexflex_zproof_ok[OF a res cfg st False z vq(1-3) H]
    have "zhyps_ok z" using zhyps_ok_mono[OF vq(4)] zr by blast
    with zr show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by blast
  qed
qed

lemma proofs_ok_thm_of_fres_gen:
  assumes ps: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of th)" and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of th) s0 (env, r)"
    and nb: "binds_none env (ares_clash th)"
    and psig: "is_prf_sig (sign_of th)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "proofs_ok (thm_of_fres (th :: 'u pure_thm) env r)"
proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs (rep_of th)). aconv_term t u)")
  case True
  then show ?thesis using po_th psig by (simp add: thm_of_fres_def)
next
  case False
  let ?c = "sign_of th" and ?th = "thm_of_fres th env r"
  have eq: "?th = with_cons (env_constraints env) (mk_thm r (shyps_of th \<union> env_sorts env) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (norm_proof_remove_types env))
      (bindM (zproof_of th) (flexflex_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (rep_of th) env)))"
    unfolding thm_of_fres_def if_not_P[OF False] ..
  let ?L = "ares_clash th"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_inv0[OF ps] sc by simp
  have nfL: "nfree env" using nb by (rule nfree_binds_none)
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  note ti = flexflex_thm_inv[OF a res cfg st nfL l0]
  have ws: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using st by (simp add: thm_inv_def)
  interpret prf_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def prf_sig_gen_of)
  have po: "proofs_ok (rep_thm th)" by (rule po_th[OF psig])
  show ?thesis unfolding proofs_ok_def Let_def eq with_cons_sel mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix p assume "bindW (proof_of th) (norm_proof_remove_types env) = returnW p"
    then obtain pf where pf: "proof_of th = returnW pf" and nq: "norm_proof_remove_types env pf = returnW p"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    from flexflex_proof_ok[OF a res cfg st False nq vq nfL l0]
    show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) p (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" .
  next
    fix z assume "bindM (zproof_of th) (flexflex_zproof ztargs (rep_of th) env) = return z"
    then obtain pf where pf: "zproof_of th = return pf" and z: "flexflex_zproof ztargs (rep_of th) env pf = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "zinv pf" "znolb 0 pf" "zhyps_ok pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    have H: "\<forall>h\<in>set (hyps_of th). closed h" using ws by (auto simp: wt_thm_def dest: wtpD(1))
    note zr = flexflex_zproof_ok[OF a res cfg st False z vq(1-3) H nfL l0]
    have "zhyps_ok z" using zhyps_ok_mono[OF vq(4)] zr by blast
    with zr show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by blast
  qed
qed

end
