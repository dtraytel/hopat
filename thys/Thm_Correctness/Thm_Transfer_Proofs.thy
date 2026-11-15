section \<open>Proofs: Thm_Transfer\<close>

theory Thm_Transfer_Proofs
  imports Thm_Transfer Thm_Unconstrain_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Transfer\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

text \<open>The proofs of a theorem of a signature are valid in its extensions:\<close>

theorem proofs_ok_transfer:
  assumes sem: "thm_sem TYPE('u) th" and prfs: "is_prf_sig (th_sign th) \<Longrightarrow> proofs_ok th"
    and sl: "sign_le (th_sign th) c'"
  shows "is_prf_sig (th_sign (th\<lparr>th_sign := c'\<rparr>)) \<Longrightarrow> proofs_ok (th\<lparr>th_sign := c'\<rparr>)"
proof -
  let ?c = "th_sign th"
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" and ar: "sg_ar c' = sg_ar ?c"
    and ax: "\<And>A. sg_ax ?c A \<Longrightarrow> sg_ax c' A" and cl: "sg_close c' = sg_close ?c" and ty: "sg_tyargs c' = sg_tyargs ?c"
    and axs: "\<And>a A. sg_axioms ?c a = Some A \<Longrightarrow> sg_axioms c' a = Some A \<and> pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) A"
    using sl by (auto simp: sign_le_def)
  have axd: "\<And>A n. sg_ax ?c A \<Longrightarrow> n \<in> term_consts A \<Longrightarrow> const_decl (sg_consts ?c) n"
    using sl by (auto simp: sign_le_def)
  from sem ps have wf: "pure_sig.thm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (th_maxidx th) (th_hyps th) (th_tpairs th) (th_prop th)"
    and val: "\<And>M :: 'u model. is_model ?c M \<Longrightarrow> valid_in ?c M (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)"
    by (auto simp: thm_sem_def)
  assume ip: "is_prf_sig (th_sign (th\<lparr>th_sign := c'\<rparr>))"
  then have ip': "prf_sig (sg_alg c') (sg_ar c') (sg_close c') (sg_tyargs c')" by (simp add: is_prf_sig_def)
  then have ps'': "pure_sig (sg_alg c') (sg_ar c')" by (simp add: prf_sig_def)
  have ipc: "prf_sig (sg_alg ?c) (sg_ar ?c) (sg_close ?c) (sg_tyargs ?c)"
    using ip' ps ar cl ty by (simp add: prf_sig_def)
  interpret PE: prf_ext "sg_alg ?c" "sg_alg c'" "sg_ar ?c" "sg_consts ?c" "sg_consts c'" "sg_close ?c" "sg_tyargs ?c"
    using sig_ext_sign_le[OF sl ps''] ipc ip' ar cl ty by (simp add: prf_ext_def)
  have po: "proofs_ok th" using prfs ipc by (simp add: is_prf_sig_def)
  have H: "h \<in> set (th_hyps th) \<Longrightarrow> vars h = {} \<and> ttvars h = {}" for h
    using wf by (simp add: PE.S.thm_wf_def PE.S.wt_thm_def)
  have Hd: "const_decl (sg_consts ?c) n" if "h \<in> set (th_hyps th)" "n \<in> term_consts h" for h n
  proof -
    from wf that(1) have "PE.S.wtp h" by (simp add: PE.S.thm_wf_def PE.S.wt_thm_def)
    from PE.S.typing_consts_decl[OF PE.S.wtpD(2)[OF this] that(2)] show ?thesis .
  qed
  have A: "PE.P'.prf_valid (sg_ax c') (set (th_hyps th)) (th_tpairs th) p (th_prop th) \<and>
      prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" if "th_proof th = returnW p" for p
    using po that PE.prf_valid_ext[OF H ax] by (simp add: proofs_ok_def Let_def)
  have B: "PE.P'.zvalid (sg_ax c') (set (th_hyps th)) (th_tpairs th) z (th_prop th) \<and> zinv z \<and> znolb 0 z \<and>
      PE.S'.zhyps_ok z" if "th_zproof th = return z" for z
  proof -
    from po that have v: "PE.P.zvalid (sg_ax ?c) (set (th_hyps th)) (th_tpairs th) z (th_prop th)"
      and i: "zinv z" "znolb 0 z" "PE.S.zhyps_ok z"
      by (simp_all add: proofs_ok_def Let_def)
    have zv1: "PE.P'.zvalid (sg_ax c') (set (th_hyps th)) (th_tpairs th) z (th_prop th)"
      by (rule PE.zvalid_ext(1)[OF _ _ _ _ v]) (use H ax Hd axd in blast)+
    have zv2: "\<forall>h\<in>zhyps z. zt_decl (sg_consts ?c) h"
      by (rule PE.zvalid_ext(2)[where ax' = "sg_ax c'", OF _ _ _ _ v]) (use H ax Hd axd in blast)+
    from zv1 PE.zhyps_ok_ext[OF zv2 i(3)] i(1,2) show ?thesis by simp
  qed
  show "proofs_ok (th\<lparr>th_sign := c'\<rparr>)"
    unfolding proofs_ok_def Let_def using A B by (simp add: ar cl ty)
qed

theorem thm_ok_transfer:
  assumes ok: "thm_ok TYPE('u) th" and sl: "sign_le (th_sign th) c'"
  shows "thm_ok TYPE('u) (th\<lparr>th_sign := c'\<rparr>)"
proof -
  from ok have s: "thm_sem TYPE('u) th" and p: "is_prf_sig (th_sign th) \<Longrightarrow> proofs_ok th"
    by (simp_all add: thm_ok_def)
  show ?thesis using thm_sem_transfer[OF s sl] proofs_ok_transfer[OF s p sl] by (simp add: thm_ok_def)
qed

end
