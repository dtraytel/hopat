section \<open>Proofs: Thm_Strip_Shyps\<close>

theory Thm_Strip_Shyps_Proofs
  imports Thm_Strip_Shyps Thm_Bicompose_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Strip_Shyps\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

theorem proofs_ok_strip_shyps:
  fixes th :: "'u pure_thm" and gts :: "name list"
  defines "d \<equiv> strip_shyps_rep (sg_alg (sign_of th)) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)"
  assumes fin: "finite (shyps_of th)" and sc: "sign_closed (sign_of th)"
    and so: "\<forall>S\<in>shyps_of th. sort_ok (sg_alg (sign_of th)) S"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm (rep_of th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)
    (hyps_of th) (sign_of th) (bindW (proof_of th) (strip_shyps_proof (sg_alg (sign_of th)) d))
    (bindM (zproof_of th) (zstrip_shyps_proof (sg_alg (sign_of th)) d)))) \<Longrightarrow>
    proofs_ok (mk_thm (rep_of th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)
    (hyps_of th) (sign_of th) (bindW (proof_of th) (strip_shyps_proof (sg_alg (sign_of th)) d))
    (bindM (zproof_of th) (zstrip_shyps_proof (sg_alg (sign_of th)) d)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  let ?Ts = "thm_atyps (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using w0 by (simp add: thm_wf_def)
  have na: "TFree a S \<notin> tatoms (sg_close ?c X)" for X a S using sc by (simp add: sign_closed_def)
  have sl: "set (shyps_list (shyps_of th)) = shyps_of th" by (rule set_shyps_list[OF fin])
  have so': "\<forall>S\<in>set (shyps_list (shyps_of th)). sort_ok (sg_alg ?c) S" using so sl by simp
  note sd = strip_data_ok[OF w0 so']
  have dS: "d' = strip_shyps_data (sg_alg ?c) gts (shyps_list (shyps_of th)) ?Ts" if "d = Some d'" for d'
    using strip_shyps_rep_Some[OF that[unfolded d_def]] by simp
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  have hc: "\<forall>h\<in>set (hyps_of th). closed h" using wt wtpD(1) by (auto simp: wt_thm_def)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (strip_shyps_proof (sg_alg ?c) d) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "strip_shyps_proof (sg_alg ?c) d q = returnW pf"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th)) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
    proof (cases d)
      case None
      with pf vq show ?thesis by (simp add: strip_shyps_proof_def returnW_def)
    next
      case (Some d')
      note d' = dS[OF Some]
      let ?\<phi> = "\<lambda>T. case strip_atyp (sg_alg ?c) d' T of Some T' \<Rightarrow> T' | None \<Rightarrow> T"
      from pf Some have pf': "pf = map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) q"
        by (simp add: strip_shyps_proof_def strip_proof_def returnW_def raiseW_def strip_typ_tmap
          split: if_splits) (simp add: strip_typ_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
        unfolding pf'
      proof (rule prf_valid_strip_atyps[where \<psi> = "strip_repl (sg_alg ?c) d'", OF vq(1) wt _ vq(3)])
        show "TFree a S \<notin> tatoms (sg_close ?c X)" if "X \<in> prf_atoms q" for X a S by (rule na)
        show "tatoms X \<subseteq> set ?Ts" if "X \<in> insert (th_prop (rep_of th)) (set (hyps_of th) \<union>
            fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
          by (rule sd(1)[OF that])
        show "has_sort (sg_alg ?c) T' S \<and> cert_typ (sg_alg ?c) (sg_ar ?c) T'"
          if "strip_repl (sg_alg ?c) d' S = Some T'" for S T'
          using sd(3)[OF that[unfolded d']] by (simp add: d')
        show "?\<phi> T = (if T \<in> set ?Ts then T else case strip_repl (sg_alg ?c) d' (atyp_sort T) of
            Some T' \<Rightarrow> T' | None \<Rightarrow> T)" for T
          unfolding d' by (subst sd(4)) simp
      qed
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using prf_idx_map_types[OF vq(2)] prf_nolb_map_types[OF vq(3)] by (simp_all add: pf')
      ultimately show ?thesis by simp
    qed
  next
    fix z assume "bindM (zproof_of th) (zstrip_shyps_proof (sg_alg ?c) d) = return z"
    then obtain q z1 where q: "zproof_of th = return q"
      and z1: "(case d of Some d \<Rightarrow> zstrip_proof (sg_alg ?c) d q | None \<Rightarrow> return q) = return z1"
      and bn: "beta_norm_prooft z1 = Some z"
      by (auto simp: bindZ_eq_returnZ zstrip_shyps_proof_def liftOZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have v1: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z1 (th_prop (rep_of th)) \<and> zinv z1 \<and>
        znolb 0 z1 \<and> zhyps z1 = zhyps q"
    proof (cases d)
      case None
      with z1 vq show ?thesis by simp
    next
      case (Some d')
      note d' = dS[OF Some]
      from z1 Some have zs: "zstrip_proof (sg_alg ?c) d' q = return z1" by simp
      show ?thesis
      proof (rule zstrip_proof_valid[where \<psi> = "strip_repl (sg_alg ?c) d'", OF vq(1) wt _ vq(3,2,4) _ _ _ _ zs])
        show "TFree a S \<notin> tatoms (sg_close ?c X)" for X a S by (rule na)
        show "tatoms X \<subseteq> set ?Ts" if "X \<in> insert (th_prop (rep_of th)) (set (hyps_of th) \<union>
            fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
          by (rule sd(1)[OF that])
        show "tnn T" if "T \<in> set ?Ts" for T by (rule sd(2)[OF that])
        show "has_sort (sg_alg ?c) T' S \<and> cert_typ (sg_alg ?c) (sg_ar ?c) T' \<and> tnn T'"
          if "strip_repl (sg_alg ?c) d' S = Some T'" for S T'
          using sd(3)[OF that[unfolded d']] by (simp add: d')
        show "strip_atyp (sg_alg ?c) d' T = (if T \<in> set ?Ts then Some T else strip_repl (sg_alg ?c) d' (atyp_sort T))"
          for T unfolding d' by (rule sd(4))
      qed
    qed
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z (th_prop (rep_of th))"
      by (rule zvalid_beta_norm[OF conjunct1[OF v1] bn hc])
    moreover have "zinv z" by (rule zinv_beta_norm_prooft[OF bn]) (use v1 in blast)
    moreover have "znolb 0 z" "zhyps z \<subseteq> zhyps z1" using beta_norm_prooft_closed[OF bn, of 0] v1 by simp_all
    moreover have "zhyps_ok z" by (rule zhyps_ok_mono[OF vq(4)]) (use v1 \<open>zhyps z \<subseteq> zhyps z1\<close> in simp)
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z (th_prop (rep_of th)) \<and>
        zinv z \<and> znolb 0 z \<and> zhyps_ok z" by blast
  qed
qed

end
