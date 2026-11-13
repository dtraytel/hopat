section \<open>Further inference rules on the abstract type of theorems\<close>

theory Thm_Rules2
  imports Thm_Rules
begin

text \<open>
  The structural and substitution rules of \<open>thm.ML\<close> as operations on \<^typ>\<open>'u pure_thm\<close>, in the
  style of \<^theory>\<open>Thm_Correctness.Thm_Rules\<close>. The rules that abstract over or generalize free
  variables need closed axioms (\<open>sign_closed\<close>); the equality rules and \<open>of_class\<close> need
  the signature of \<open>Pure\<close> (\<open>sign_eq\<close>).
\<close>

subsection \<open>Maximal index, renaming of bound variables and incrementing indices\<close>

lemma maxidx_tpairs_ge: "i \<le> maxidx_tpairs tps i"
  unfolding maxidx_tpairs_def by (rule fold_infl) (auto intro: order_trans[OF maxidx_term_ge maxidx_term_ge])

context pure_sig
begin

lemma maxidx_tpairs_mem:
  assumes "(t, u) \<in> set tps"
  shows "ibelow (maxidx_tpairs tps i) t \<and> ibelow (maxidx_tpairs tps i) u"
proof -
  have ge: "\<And>x j. x \<in> set tps \<Longrightarrow> j \<le> (\<lambda>(t, u) i. maxidx_term u (maxidx_term t i)) x j"
    by (auto intro: order_trans[OF maxidx_term_ge maxidx_term_ge])
  have "snd (fst v) \<le> maxidx_tpairs tps i" if "v \<in> vars t \<or> v \<in> vars u" for v
    unfolding maxidx_tpairs_def
  proof (rule fold_mem_ge[OF ge assms])
    fix j
    show "snd (fst v) \<le> (\<lambda>(t, u) i. maxidx_term u (maxidx_term t i)) (t, u) j"
      using that by (auto intro: order_trans[OF _ maxidx_term_ge] maxidx_term_vars)
  qed
  moreover have "snd (fst v) \<le> maxidx_tpairs tps i" if "v \<in> ttvars t \<or> v \<in> ttvars u" for v
    unfolding maxidx_tpairs_def
  proof (rule fold_mem_ge[OF ge assms])
    fix j
    show "snd (fst v) \<le> (\<lambda>(t, u) i. maxidx_term u (maxidx_term t i)) (t, u) j"
      using that by (auto intro: order_trans[OF _ maxidx_term_ge] maxidx_term_ttvars)
  qed
  ultimately show ?thesis by (simp add: ibelow_def)
qed

lemma thm_wf_reidx:
  assumes w: "thm_wf m hs tps P" and ib: "ibelow m' P" and tp: "\<forall>(t, u)\<in>set tps. ibelow m' t \<and> ibelow m' u"
    and m': "-1 \<le> m'"
  shows "thm_wf m' hs tps P"
  using w ib tp m' unfolding thm_wf_def wt_thm_def by (fast)

lemma thm_wf_adjust_maxidx:
  assumes w: "thm_wf (th_maxidx th) hs (th_tpairs th) (th_prop th)"
  shows "thm_wf (th_maxidx (adjust_maxidx_thm i th)) hs (th_tpairs (adjust_maxidx_thm i th))
    (th_prop (adjust_maxidx_thm i th))"
proof -
  let ?m = "th_maxidx th"
  have ib: "ibelow ?m (th_prop th)" "\<forall>(t, u)\<in>set (th_tpairs th). ibelow ?m t \<and> ibelow ?m u" "-1 \<le> ?m"
    using w unfolding thm_wf_def wt_thm_def by (fast+)
  consider "?m = i" | "?m < i" | "i < ?m" by (fastforce)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using w by (simp add: adjust_maxidx_thm_def)
  next
    case 2
    have "thm_wf i hs (th_tpairs th) (th_prop th)"
      by (rule thm_wf_reidx[OF w]) (use ib 2 ibelow_mono in \<open>fastforce+\<close>)
    then show ?thesis using 2 by (simp add: adjust_maxidx_thm_def mk_rep_def)
  next
    case 3
    let ?k = "max (maxidx_tpairs (th_tpairs th) (maxidx_of_term (th_prop th))) i"
    have k1: "maxidx_of_term (th_prop th) \<le> ?k"
      using maxidx_tpairs_ge[of "maxidx_of_term (th_prop th)" "th_tpairs th"] by simp
    have "thm_wf ?k hs (th_tpairs th) (th_prop th)"
    proof (rule thm_wf_reidx[OF w])
      show "ibelow ?k (th_prop th)" by (rule ibelow_mono[OF maxidx_of_term_ibelow k1])
      show "\<forall>(t, u)\<in>set (th_tpairs th). ibelow ?k t \<and> ibelow ?k u"
      proof (intro ballI, clarify)
        fix t u assume "(t, u) \<in> set (th_tpairs th)"
        from maxidx_tpairs_mem[OF this, of "maxidx_of_term (th_prop th)"]
        show "ibelow ?k t \<and> ibelow ?k u" by (meson ibelow_mono max.cobounded1)
      qed
      show "-1 \<le> ?k" using k1 maxidx_term_ge[of "-1" "th_prop th"] by (simp add: maxidx_of_term_def)
    qed
    then show ?thesis using 3 by (simp add: adjust_maxidx_thm_def mk_rep_def)
  qed
qed

end

definition adjust_maxidx_thm_thm :: "integer \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm" where
  "adjust_maxidx_thm_thm i th = Abs_thm (with_cons (cons_of th) (mk_thm (adjust_maxidx_thm i (rep_of th)) (shyps_of th) (hyps_of th)
    (sign_of th) (proof_of th) (zproof_of th)))"

lemma adjust_maxidx_thm_sel [simp]:
  "th_tpairs (adjust_maxidx_thm i th) = th_tpairs th" "th_prop (adjust_maxidx_thm i th) = th_prop th"
  by (simp_all add: adjust_maxidx_thm_def mk_rep_def)

lemma thm_ok_adjust_maxidx:
  fixes th :: "'u pure_thm"
  shows "thm_ok TYPE('u) (mk_thm (adjust_maxidx_thm i (rep_of th)) (shyps_of th) (hyps_of th)
    (sign_of th) (proof_of th) (zproof_of th))" (is "thm_ok _ ?th")
proof (rule thm_okI)
  let ?c = "sign_of th"
  assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
  then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
      (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
    using thm_wf_adjust_maxidx[OF w0, of i] by simp
next
  fix M :: "'u model"
  assume M: "is_model (th_sign ?th) M"
  then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
    using pure_thm_valid_in[of th M] by (simp add: valid_in_def)
next
  assume "is_prf_sig (th_sign ?th)"
  then have "proofs_ok (rep_thm th)" by (intro pure_thm_proofs_ok) simp
  then show "proofs_ok ?th" by (simp add: proofs_ok_def)
qed

theorem adjust_maxidx_thm_thm:
  "rep_thm (adjust_maxidx_thm_thm i th) = with_cons (cons_of th) (mk_thm (adjust_maxidx_thm i (rep_of th)) (shyps_of th) (hyps_of th)
    (sign_of th) (proof_of th) (zproof_of th))"
  using thm_ok_adjust_maxidx[of i th] by (simp add: adjust_maxidx_thm_thm_def Abs_thm_inverse)

context pure_sig
begin

lemma wtp_aconv: "aconv_term s t \<Longrightarrow> wtp s \<Longrightarrow> wtp t"
  using loose_bvar1_aconv[of s t] typing_aconv[of s t] by (auto simp: wtp_def closed_iff_loose_bvar1)

end

definition renamed_prop_thm :: "pterm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "renamed_prop_thm P th = map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (proof_of th) (zproof_of th)))) (resT (renamed_prop P (rep_of th)))"

lemma thm_ok_renamed_prop:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (renamed_prop P (rep_of th)) r"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  from ok have a: "aconv_term (th_prop (rep_of th)) P"
    and r: "r = mk_rep (th_maxidx (rep_of th)) (th_tpairs (rep_of th)) P"
    by (auto simp: renamed_prop_def returnW_def raiseW_def split: if_splits)
  have u: "unname P = unname (th_prop (rep_of th))" using a by (simp add: aconv_term_unname)
  have vt: "vars P = vars (th_prop (rep_of th))" "ttvars P = ttvars (th_prop (rep_of th))"
    by (metis u vars_unname, metis u ttvars_unname)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) P"
      using w0 wtp_aconv[OF a] vt unfolding thm_wf_def wt_thm_def vars_thm_def tvars_thm_def ibelow_def by (auto)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by simp
    then have w: "wtp (th_prop (rep_of th))" "\<forall>h\<in>set (hyps_of th). wtp h" by (simp_all add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule renamed_prop_valid[OF ok _ w]) (use pure_thm_valid_in[of th M] M in simp)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps by (simp add: thm_wf_def wt_thm_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume q: "proof_of th = returnW pf"
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using p q by (simp_all add: proofs_ok_def Let_def)
      then show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and>
          prf_nolb 0 pf"
        using renamed_prop_proof_valid[OF ok vq(1) w] by simp
    next
      fix z assume q: "zproof_of th = return z"
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z (th_prop (rep_of th))" "zinv z"
        "znolb 0 z" "zhyps_ok z"
        using p q by (simp_all add: proofs_ok_def Let_def)
      then show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z"
        using zrenamed_prop_proof_valid[OF ok vq(1) w] by simp
    qed
  qed
qed

theorem renamed_prop_thm:
  assumes "renamed_prop_thm P th = Some th'"
  obtains r where "okT (renamed_prop P (rep_of th)) r"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th))"
proof -
  from assms obtain r where ok: "okT (renamed_prop P (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th)))"
    by (auto simp: renamed_prop_thm_def resT_Some)
  show thesis
    by (rule that[OF ok]) (use thm_ok_renamed_prop[OF ok] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed

text \<open>
  \<open>Thm.incr_indexes\<close> applies \<open>Proofterm.incr_indexes\<close> and \<open>ZTerm.incr_indexes_proof\<close> to the
  proofs if the increment is positive.
\<close>

lemma zterm_ok_zsubst_term':
  "zterm_ok t \<Longrightarrow> (\<And>T. ztyp_ok T \<Longrightarrow> ztyp_ok (tf T)) \<Longrightarrow>
    (\<And>x T u. vf (x, T) = Some u \<Longrightarrow> ztyp_ok T \<Longrightarrow> zterm_ok u) \<Longrightarrow> zterm_ok (zsubst_term tf vf t)"
  by (induction tf vf t rule: zsubst_term.induct) (auto split: option.splits)

lemma loose_bvar_incr_idx_Nil: "loose_bvar (incr_idx [] inc lev t) k \<longleftrightarrow> loose_bvar t k"
  by (induction "[] :: ptyp list" inc lev t arbitrary: k rule: incr_idx.induct) simp_all

definition incr_indexes_prf :: "integer \<Rightarrow> prf P \<Rightarrow> prf P" where
  "incr_indexes_prf i p = (if i = 0 then p else bindW p (\<lambda>q. returnW (incr_indexes_proof i q)))"

definition incr_indexes_zprf :: "integer \<Rightarrow> zproof Z \<Rightarrow> zproof Z" where
  "incr_indexes_zprf i p = (if i = 0 then p else bindM p (zincr_indexes_proof i))"

definition incr_indexes_thm' :: "integer \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "incr_indexes_thm' i th = map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (incr_indexes_prf i (proof_of th)) (incr_indexes_zprf i (zproof_of th))))) (resT (incr_indexes_thm i (rep_of th)))"

context pure_sig
begin

lemma incr_indexes_vars:
  "v \<in> vars (incr_indexes [] i t) \<Longrightarrow> \<exists>w\<in>vars t. snd (fst v) = snd (fst w) + i"
  by (force simp: incr_indexes_idx vars_incr_idx)

lemma incr_indexes_ttvars:
  "v \<in> ttvars (incr_indexes [] i t) \<Longrightarrow> \<exists>w\<in>ttvars t. snd (fst v) = snd (fst w) + i"
  using ttvars_incr_idx[of "fst (fst v)" "snd (fst v)" "snd v" "[]" i 0 t]
  by (cases v) (force simp: incr_indexes_idx)

lemma incr_indexes_typed:
  assumes "e \<turnstile> t : T" "closed t"
  shows "e' \<turnstile> incr_indexes [] i t : incr_tvar i T" "closed (incr_indexes [] i t)"
  using typing_incr_idx0[OF assms, of "[]" e' i] closed_incr_idx0[OF assms(2), of "[]" i]
  by (simp_all add: incr_indexes_idx closed_def)

lemma wtp_incr_indexes0': "wtp P \<Longrightarrow> wtp (incr_indexes [] inc P)"
  using typing_incr_idx0[OF wtpD(2) wtpD(1), of P "[]" "\<lambda>_. propT" inc] closed_incr_idx0[OF wtpD(1), of P "[]" inc]
  by (intro wtpI) (simp_all add: incr_indexes_idx closed_def incr_tvar_tren)

lemma thm_wf_incr_indexes:
  assumes w: "thm_wf m hs tps P" and i: "0 \<le> i"
  shows "thm_wf (m + i) hs (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) (incr_indexes [] i P)"
proof -
  from w have wP: "wtp P" and ib: "ibelow m P" and h: "\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tp: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> ibelow m t \<and> ibelow m u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and m: "-1 \<le> m" and vn: "\<forall>v\<in>vars_thm tps P. 0 \<le> snd (fst v)"
    and tn: "\<forall>v\<in>tvars_thm tps P. 0 \<le> snd (fst v)"
    unfolding thm_wf_def wt_thm_def by (blast+)
  have ibi: "ibelow (m + i) (incr_indexes [] i t)" if "ibelow m t" for t
    using that incr_indexes_vars[of _ i t] incr_indexes_ttvars[of _ i t] unfolding ibelow_def by (fastforce)
  have nn: "\<forall>v\<in>vars (incr_indexes [] i t). 0 \<le> snd (fst v)" if "\<forall>v\<in>vars t. 0 \<le> snd (fst v)" for t
    using that incr_indexes_vars[of _ i t] i by (fastforce)
  have tnn: "\<forall>v\<in>ttvars (incr_indexes [] i t). 0 \<le> snd (fst v)" if "\<forall>v\<in>ttvars t. 0 \<le> snd (fst v)" for t
    using that incr_indexes_ttvars[of _ i t] i by (fastforce)
  have tp': "\<forall>(t, u)\<in>set (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps).
      closed t \<and> closed u \<and> ibelow (m + i) t \<and> ibelow (m + i) u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  proof clarsimp
    fix t u assume "(t, u) \<in> set tps"
    with tp obtain T where c: "closed t" "closed u" "ibelow m t" "ibelow m u" "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T"
      by (blast)
    show "closed (incr_indexes [] i t) \<and> closed (incr_indexes [] i u) \<and> ibelow (m + i) (incr_indexes [] i t) \<and>
        ibelow (m + i) (incr_indexes [] i u) \<and>
        (\<exists>T. \<forall>e. e \<turnstile> incr_indexes [] i t : T \<and> e \<turnstile> incr_indexes [] i u : T)"
      using incr_indexes_typed[OF c(5) c(1)] incr_indexes_typed[OF c(6) c(2)] ibi[OF c(3)] ibi[OF c(4)] by (blast)
  qed
  have vn': "\<forall>v\<in>vars_thm (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) (incr_indexes [] i P).
      0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> vars_thm (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) (incr_indexes [] i P)"
    then obtain x where x: "v \<in> vars (incr_indexes [] i x)" "vars x \<subseteq> vars_thm tps P"
      unfolding vars_thm_def by (fastforce)
    from incr_indexes_vars[OF x(1)] obtain w where "w \<in> vars x" "snd (fst v) = snd (fst w) + i" by blast
    with x(2) vn i show "0 \<le> snd (fst v)" by (fastforce)
  qed
  have tn': "\<forall>v\<in>tvars_thm (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) (incr_indexes [] i P).
      0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> tvars_thm (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) (incr_indexes [] i P)"
    then obtain x where x: "v \<in> ttvars (incr_indexes [] i x)" "ttvars x \<subseteq> tvars_thm tps P"
      unfolding tvars_thm_def by (fastforce)
    from incr_indexes_ttvars[OF x(1)] obtain w where "w \<in> ttvars x" "snd (fst v) = snd (fst w) + i" by blast
    with x(2) tn i show "0 \<le> snd (fst v)" by (fastforce)
  qed
  show ?thesis unfolding thm_wf_def wt_thm_def
    using wtp_incr_indexes0'[OF wP] ibi[OF ib] h tp' m i vn' tn' by simp
qed

end

lemma thm_ok_incr_indexes:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (incr_indexes_thm i (rep_of th)) r"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (incr_indexes_prf i (proof_of th)) (incr_indexes_zprf i (zproof_of th)))" (is "thm_ok _ ?th")
proof (cases "i = 0")
  case True
  with ok have r: "r = rep_of th" by (auto simp: incr_indexes_thm_def returnW_def raiseW_def)
  have e: "rep_thm th = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th))"
    by (simp add: r mk_thm_def with_cons_def)
  have "thm_ok TYPE('u) (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th)))"
    using thm_ok_rep[of th] e by metis
  then show ?thesis using True by (simp add: incr_indexes_prf_def incr_indexes_zprf_def)
next
  case False
  let ?c = "sign_of th" and ?inc = "\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)"
  from ok False have i: "0 \<le> i"
    and r: "r = mk_rep (th_maxidx (rep_of th) + i) (map ?inc (th_tpairs (rep_of th)))
      (incr_indexes [] i (th_prop (rep_of th)))"
    by (auto simp: incr_indexes_thm_def returnW_def raiseW_def split: if_splits)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using thm_wf_incr_indexes[OF w0 i] by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by simp
    then have c: "closed (th_prop (rep_of th))" "\<forall>(t, u)\<in>set (th_tpairs (rep_of th)). closed t \<and> closed u"
      "\<forall>h\<in>set (hyps_of th). vars h = {} \<and> ttvars h = {}"
      by (auto simp: thm_wf_def wt_thm_def wtp_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule incr_indexes_thm_valid[OF ok _ c]) (use pure_thm_valid_in[of th M] M in simp)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "incr_indexes_prf i (proof_of th) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = incr_indexes_proof i q"
        using False by (auto simp: incr_indexes_prf_def bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        using incr_indexes_proof_valid[OF vq(1), of i] by (simp add: r mk_rep_def pf)
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
        using vq(2) i incr_indexes_vars[of _ i]
        by (fastforce simp: pf incr_indexes_proof_def prf_idx_def prf_terms_map_proof_terms)
      moreover have "prf_nolb 0 pf" unfolding pf incr_indexes_proof_def
        by (rule prf_nolb_map[OF _ _ vq(3)])
          (simp_all add: incr_indexes_idx loose_bvar_incr_idx_Nil)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "incr_indexes_zprf i (zproof_of th) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zincr_indexes_proof i q = return z"
        using False by (auto simp: incr_indexes_zprf_def bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      define var where "var = (\<lambda>((x, j), T). if 0 \<le> j then Some (ZVar (x, j + i) T) else None)"
      have m: "map_zproof (zincr_tvar i) (\<lambda>t. return (zsubst_term (zincr_tvar i) var t)) q = return z"
        using z by (simp add: zincr_indexes_proof_def Let_def var_def)
      have var: "\<And>v u. var v = Some u \<Longrightarrow> \<not> zloose u 0"
        by (auto simp: var_def split: if_splits)
      have var': "\<And>x T u. var (x, T) = Some u \<Longrightarrow> ztyp_ok T \<Longrightarrow> zterm_ok u"
        using i by (auto simp: var_def split: if_splits)
      have zc: "zconsts_ok q" and zo: "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp_all add: zinv_def)
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        using zincr_indexes_proof_valid[OF vq(1) z i zo zc] by (simp add: r mk_rep_def)
      moreover have "zinv z"
        by (rule zinv_map_zproof[OF m vq(2)])
          (use ztyp_ok_zincr_tvar[OF _ i] var' in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
      moreover have "znolb 0 z"
      proof -
        have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term (zincr_tvar i) var t) k"
          using zloose_zsubst_term var by blast
        show ?thesis by (rule znolb_map_zproof[OF m zc _ _ vq(3)]) (use zl in auto)
      qed
      moreover have "zhyps_ok z" using vq(4) zhyps_map_zproof[OF m] by (simp add: zhyps_ok_def)
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" by simp
    qed
  qed
qed

theorem incr_indexes_thm':
  assumes "incr_indexes_thm' i th = Some th'"
  obtains r where "okT (incr_indexes_thm i (rep_of th)) r"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (incr_indexes_prf i (proof_of th)) (incr_indexes_zprf i (zproof_of th)))"
proof -
  from assms obtain r where ok: "okT (incr_indexes_thm i (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (incr_indexes_prf i (proof_of th)) (incr_indexes_zprf i (zproof_of th))))"
    by (auto simp: incr_indexes_thm'_def resT_Some)
  show thesis
    by (rule that[OF ok]) (use thm_ok_incr_indexes[OF ok] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed


subsection \<open>Implication introduction\<close>

lemma prf_idx_abshyp: "prf_idx P p \<Longrightarrow> prf_idx P (abshyp h i p)"
  by (induction h i p rule: abshyp.induct) auto

lemma prf_nolb_abshyp: "prf_nolb k p \<Longrightarrow> prf_nolb k (abshyp h i p)"
  by (induction h i p arbitrary: k rule: abshyp.induct) auto

lemma zinv_zabshyp: "zinv p \<Longrightarrow> zinv (zabshyp h l p)"
  by (induction h l p rule: zabshyp.induct) auto

lemma znolb_zabshyp: "znolb k p \<Longrightarrow> znolb k (zabshyp h l p)"
  by (induction h l p arbitrary: k rule: zabshyp.induct) auto

lemma zhyps_zabshyp: "zhyps (zabshyp h l p) \<subseteq> zhyps p"
  by (induction h l p rule: zabshyp.induct) auto

definition implies_intr_thm :: "pure_cterm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "implies_intr_thm ct th =
    (if csign_of ct = sign_of th then
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th)
          (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)))
          (bindM (zproof_of th) (zimplies_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)))))))
        (resT (implies_intr (crep_of ct) (rep_of th)))
     else None)"

lemma thm_ok_implies_intr:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (implies_intr (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct \<union> shyps_of th)
    (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zimplies_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  obtain A U m where cr: "crep_of ct = CTerm A U m" by (cases "crep_of ct")
  let ?hs = "filter (\<lambda>h. \<not> aconv_term A h) (hyps_of th)"
  have ok': "okT (implies_intr (CTerm A U m) (rep_of th)) r" using ok by (simp add: cr)
  from ok' have U: "U = propT"
    and r: "r = mk_rep (max m (th_maxidx (rep_of th))) (th_tpairs (rep_of th)) (mk_implies A (th_prop (rep_of th)))"
    by (auto simp: implies_intr_def returnW_def raiseW_def split: if_splits)
  have wfc: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm A U m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
    using pure_cterm_wf[of ct] ps c by (simp add: cr)
  have wA: "pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) A" if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    show ?thesis using wfc[OF ps] U by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
  qed
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm A U m)" by (rule wfc[OF ps])
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    have "thm_wf (max m (th_maxidx (rep_of th))) (hyps_of th) (th_tpairs (rep_of th)) (mk_implies A (th_prop (rep_of th)))"
    proof (rule thm_wf_extend[OF w0, where V = "vars A" and TV = "ttvars A"])
      show "wtp (mk_implies A (th_prop (rep_of th)))" unfolding mk_implies_def by (rule wtp_implies[OF wA[OF ps] w])
    qed (use wf in \<open>auto simp: cterm_wf_def ibelow_def mk_implies_def ttvars_def implies_def propT_def\<close>)
    then have "thm_wf (max m (th_maxidx (rep_of th))) ?hs (th_tpairs (rep_of th)) (mk_implies A (th_prop (rep_of th)))"
      unfolding thm_wf_def wt_thm_def by simp
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r mk_rep_def cr)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by simp
    then have w: "wtp (th_prop (rep_of th))" "\<forall>h\<in>set (hyps_of th). wtp h" by (simp_all add: thm_wf_def wt_thm_def)
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid_in[of th M] M by simp
    have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      by (rule valid_mono[OF v]) simp
    then have "valid (csorts_of ct \<union> shyps_of th) ?hs (th_tpairs r) (th_prop r)"
      by (rule implies_intr_valid[OF ok' _ wA[OF ps'] w(1) w(2)])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def cr)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have wf: "cterm_wf (CTerm A U m)" by (rule wfc[OF ps])
    have wA': "wtp A" by (rule wA[OF ps])
    have pA: "pnn A" using wf by (simp add: cterm_wf_def pnn_iff)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have H: "\<And>t. t \<in> set (hyps_of th) \<Longrightarrow> vars t = {} \<and> ttvars t = {}"
      using w0 by (simp add: thm_wf_def wt_thm_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = implies_intr_proof A q"
        by (auto simp: bindP_eq_returnP cr)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set ?hs) (th_tpairs r) pf (th_prop r)"
        using implies_intr_rule_proof_valid[OF ok' vq(1) wA' H] by (simp add: pf)
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using prf_idx_abshyp[OF vq(2)] prf_nolb_abshyp[OF vq(3)] by (simp_all add: pf implies_intr_proof_def)
      ultimately show "prf_valid (sg_ax ?c) (set (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)))
          (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
        by (simp add: cr)
    next
      fix z assume "bindM (zproof_of th) (zimplies_intr_proof ztargs (ct_t (crep_of ct))) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zimplies_intr_proof ztargs A q = return z"
        by (auto simp: bindZ_eq_returnZ cr)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      from z obtain h where h: "zterm_of ztargs A = return h" and zh: "z = ZAbsp STR ''H'' h (zabshyp h 0 q)"
        by (auto simp: zimplies_intr_proof_def bindZ_eq_returnZ)
      have "zvalid (sg_ax ?c) (set ?hs) (th_tpairs r) z (th_prop r)"
        using zimplies_intr_rule_proof_valid[OF ok' vq(1) wA' pnn_noneg[OF pA] H _ z] vq(4)
        by (simp add: zhyps_ok_def)
      moreover have "zinv z"
        using zterm_ok_zterm_of_pnn[OF h pA] zinv_zabshyp[OF vq(2)] by (simp add: zh)
      moreover have "znolb 0 z"
        using zloose_zterm_of[OF h] wtpD(1)[OF wA'] znolb_zabshyp[OF vq(3)] by (simp add: zh closed_def)
      moreover have "zhyps_ok z" using vq(4) zhyps_zabshyp by (fastforce simp: zh zhyps_ok_def)
      ultimately show "zvalid (sg_ax ?c) (set (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)))
          (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
        by (simp add: cr)
    qed
  qed
qed

theorem implies_intr_thm:
  assumes "implies_intr_thm ct th = Some th'"
  obtains r where "okT (implies_intr (crep_of ct) (rep_of th)) r" "csign_of ct = sign_of th"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th)
      (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)))
      (bindM (zproof_of th) (zimplies_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)))))"
proof -
  from assms obtain r where c: "csign_of ct = sign_of th" and ok: "okT (implies_intr (crep_of ct) (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th)
      (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)))
      (bindM (zproof_of th) (zimplies_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct))))))"
    by (auto simp: implies_intr_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c]) (use thm_ok_implies_intr[OF ok c] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed


subsection \<open>Eta-long conversion\<close>

lemma fastype_of_bound_mem: "ok (fastype_of_bound Ts i) T \<Longrightarrow> T \<in> set Ts"
  by (induction Ts i rule: fastype_of_bound.induct) (auto split: if_splits)

lemma range_type_ofT_tvars: "ok (range_type_ofT t U) T \<Longrightarrow> tvars T \<subseteq> tvars U"
  by (cases "(t, U)" rule: range_type_ofT.cases) (auto split: if_splits)

lemma fastype_of_atom_tvars:
  "ok (fastype_of_atom Ts a) T \<Longrightarrow> tvars T \<subseteq> ttvars a \<union> (\<Union>U\<in>set Ts. tvars U)"
  by (cases "(Ts, a)" rule: fastype_of_atom.cases) (auto dest: fastype_of_bound_mem)

lemma fastype_of_term_tvars_aux:
  "(ok (fastype_of_term Ts t) T \<longrightarrow> tvars T \<subseteq> ttvars t \<union> (\<Union>U\<in>set Ts. tvars U)) \<and>
    (ok (range_type_of Ts t) T \<longrightarrow> tvars T \<subseteq> ttvars t \<union> (\<Union>U\<in>set Ts. tvars U))"
proof (induction t arbitrary: Ts T)
  case (Abs a T0 b)
  show ?case
  proof (intro conjI impI)
    assume "ok (fastype_of_term Ts (Abs a T0 b)) T"
    then obtain U where U: "ok (fastype_of_term (T0 # Ts) b) U" and T: "T = T0 \<rightarrow>\<^sub>T U" by (auto)
    show "tvars T \<subseteq> ttvars (Abs a T0 b) \<union> (\<Union>U\<in>set Ts. tvars U)"
      using Abs.IH[of "T0 # Ts" U] U T by (auto)
  next
    assume "ok (range_type_of Ts (Abs a T0 b)) T"
    then show "tvars T \<subseteq> ttvars (Abs a T0 b) \<union> (\<Union>U\<in>set Ts. tvars U)"
      using Abs.IH[of "T0 # Ts" T] by (auto)
  qed
next
  case (App s u)
  show ?case
  proof (intro conjI impI)
    assume "ok (fastype_of_term Ts (s $ u)) T"
    then show "tvars T \<subseteq> ttvars (s $ u) \<union> (\<Union>U\<in>set Ts. tvars U)"
      using App.IH(1)[of Ts T] by (auto)
  next
    assume "ok (range_type_of Ts (s $ u)) T"
    then obtain U where U: "ok (range_type_of Ts s) U" and r: "ok (range_type_ofT (s $ u) U) T" by (auto)
    show "tvars T \<subseteq> ttvars (s $ u) \<union> (\<Union>U\<in>set Ts. tvars U)"
      using App.IH(1)[of Ts U] U range_type_ofT_tvars[OF r] by (auto)
  qed
qed (auto dest!: fastype_of_atom_tvars range_type_ofT_tvars fastype_of_bound_mem)+

lemma fastype_of_term_tvars:
  "ok (fastype_of_term Ts t) T \<Longrightarrow> tvars T \<subseteq> ttvars t \<union> (\<Union>U\<in>set Ts. tvars U)"
  using fastype_of_term_tvars_aux by blast

lemma pr_binder_types_tvars: "U \<in> set (Pure_Rules.binder_types T) \<Longrightarrow> tvars U \<subseteq> tvars T"
  by (induction T rule: Pure_Rules.binder_types.induct) (auto split: if_splits)

context pure_sig
begin

lemma eta_long_vars:
  "Pure_Rules.eta_long Ts t = Some y \<Longrightarrow> y = Ok t' \<Longrightarrow>
    vars t' \<subseteq> vars t \<and> ttvars t' \<subseteq> ttvars t \<union> (\<Union>U\<in>set Ts. tvars U)"
proof (induction Ts t y arbitrary: t' rule: Pure_Rules.eta_long.raw_induct[rotated, consumes 1])
  case (1 f Ts t y)
  have IH: "vars s' \<subseteq> vars s \<and> ttvars s' \<subseteq> ttvars s \<union> (\<Union>U\<in>set Ts'. tvars U)" if "ok (f Ts' s) s'" for Ts' s s'
    using "1.IH"[OF that(1) HOL.refl] .
  from "1.hyps" "1.prems"(1) have hyps: "ok (case dest_Abs t of
     None \<Rightarrow>
       case strip_comb t of
       (u, ts) \<Rightarrow>
         if is_Abs u then beta_norm t \<bind> f Ts
         else fastype_of_term Ts t \<bind>
              (\<lambda>T. mapM (\<lambda>s. f (rev (Pure_Rules.binder_types T) @ Ts)
                    (incr_boundvars (integer_of_nat (length (Pure_Rules.binder_types T))) s)) ts \<bind>
                   (\<lambda>ts'. mapM (\<lambda>j. f (rev (Pure_Rules.binder_types T) @ Ts) (Bound j))
                           (downto (integer_of_nat (length (Pure_Rules.binder_types T)) - 1) 0) \<bind>
                          (\<lambda>bs. return (abss (Pure_Rules.binder_types T)
                            (list_comb (incr_boundvars (integer_of_nat (length (Pure_Rules.binder_types T))) u)
                              (ts' @ bs))))))
     | Some (s, T, b) \<Rightarrow> f (T # Ts) b \<bind> (\<lambda>b'. return (Abs s T b'))) t'"
    by simp
  show ?case
  proof (cases "dest_Abs t")
    case (Some x)
    then obtain a T0 b where t: "t = Abs a T0 b" by (cases t) auto
    from hyps t obtain b' where b': "ok (f (T0 # Ts) b) b'" and t': "t' = Abs a T0 b'" by (auto)
    from IH[OF b'] show ?thesis by (auto simp: t t')
  next
    case None
    obtain u ts where sc: "strip_comb t = (u, ts)" by (cases "strip_comb t")
    have t: "t = u \<degree>\<degree> ts" by (rule strip_comb_apps[OF sc])
    show ?thesis
    proof (cases "is_Abs u")
      case True
      with hyps None sc obtain t2 where n: "ok (beta_norm t) t2" and r: "ok (f Ts t2) t'" by (auto)
      note red = beta_norm_reds[OF n]
      from IH[OF r] beta_reds_vars[OF red] ttvars_mono[OF beta_reds_typs[OF red]] show ?thesis by (blast)
    next
      case False
      from hyps None sc False obtain T where ft: "ok (fastype_of_term Ts t) T" by (auto)
      let ?Bt = "Pure_Rules.binder_types T"
      let ?n = "integer_of_nat (length ?Bt)"
      let ?Ts' = "rev ?Bt @ Ts"
      let ?X = "ttvars t \<union> (\<Union>U\<in>set Ts. tvars U)"
      from hyps None sc False ft obtain ts' bs where
        mts: "ok (mapM (\<lambda>s. f ?Ts' (incr_boundvars ?n s)) ts) ts'"
        and mbs: "ok (mapM (\<lambda>j. f ?Ts' (Bound j)) (downto (?n - 1) 0)) bs"
        and t': "t' = abss ?Bt (list_comb (incr_boundvars ?n u) (ts' @ bs))"
        by (auto simp: return_def)
      have tT: "tvars T \<subseteq> ?X" by (rule fastype_of_term_tvars(1)[OF ft])
      have tBt: "tvars U \<subseteq> ?X" if "U \<in> set ?Bt" for U using pr_binder_types_tvars[OF that] tT by (blast)
      have tTs': "(\<Union>U\<in>set ?Ts'. tvars U) \<subseteq> ?X" using tBt by (auto)
      have l1: "list_all2 (\<lambda>s s'. ok (f ?Ts' (incr_boundvars ?n s)) s') ts ts'" using mts by (simp add: ok_mapM)
      have l2: "list_all2 (\<lambda>j b. ok (f ?Ts' (Bound j)) b) (downto (?n - 1) 0) bs" using mbs by (simp add: ok_mapM)
      have ibv: "vars (incr_boundvars n s) = vars s" "ttvars (incr_boundvars n s) = ttvars s" for n s
        by (simp_all add: incr_boundvars_def ttvars_def)
      have vts: "vars s' \<subseteq> vars t \<and> ttvars s' \<subseteq> ?X" if "s' \<in> set ts'" for s'
      proof -
        from that obtain i where i: "i < length ts'" "s' = ts' ! i" by (auto simp: in_set_conv_nth)
        have il: "i < length ts" using i(1) list_all2_lengthD[OF l1] by simp
        have "ok (f ?Ts' (incr_boundvars ?n (ts ! i))) s'" using list_all2_nthD[OF l1 il] i(2) by simp
        from IH[OF this] have "vars s' \<subseteq> vars (ts ! i)" "ttvars s' \<subseteq> ttvars (ts ! i) \<union> ?X"
          using tTs' unfolding ibv by blast+
        moreover have "vars (ts ! i) \<subseteq> vars t" "ttvars (ts ! i) \<subseteq> ttvars t"
          using nth_mem[OF il] by (auto simp: t vars_apps typs_apps ttvars_def)
        ultimately show ?thesis by (blast)
      qed
      have vbs: "vars b \<subseteq> vars t \<and> ttvars b \<subseteq> ?X" if "b \<in> set bs" for b
      proof -
        from that obtain i where i: "i < length bs" "b = bs ! i" by (auto simp: in_set_conv_nth)
        have il: "i < length (downto (?n - 1) 0)" using i(1) list_all2_lengthD[OF l2] by simp
        have "ok (f ?Ts' (Bound (downto (?n - 1) 0 ! i))) b" using list_all2_nthD[OF l2 il] i(2) by simp
        from IH[OF this] have "vars b = {}" "ttvars b \<subseteq> (\<Union>U\<in>set ?Ts'. tvars U)" by (simp_all add: ttvars_def)
        then show ?thesis using subset_trans[OF _ tTs', of "ttvars b"] by simp
      qed
      have vu: "vars u \<subseteq> vars t" "ttvars u \<subseteq> ttvars t" by (auto simp: t vars_apps typs_apps ttvars_def)
      have tabss: "ttvars (abss Bs s) = (\<Union>U\<in>set Bs. tvars U) \<union> ttvars s" for Bs s
        by (induction Bs) auto
      have vabss: "vars (abss Bs s) = vars s" for Bs s by (induction Bs) auto
      have va: "vars s \<subseteq> vars t \<and> ttvars s \<subseteq> ?X" if "s \<in> set (ts' @ bs)" for s
        using that vts[of s] vbs[of s] by auto
      have "vars t' \<subseteq> vars t"
        unfolding t' vabss list_comb_apps vars_apps ibv
      proof (intro Un_least UN_least)
        show "vars u \<subseteq> vars t" by (rule vu(1))
        show "vars s \<subseteq> vars t" if "s \<in> set (ts' @ bs)" for s using va[OF that] by simp
      qed
      moreover have "ttvars t' \<subseteq> ?X"
        unfolding t' tabss list_comb_apps ttvars_apps ibv
      proof (intro Un_least UN_least)
        show "tvars U \<subseteq> ?X" if "U \<in> set ?Bt" for U by (rule tBt[OF that])
        show "ttvars u \<subseteq> ?X" using vu(2) by blast
        show "ttvars s \<subseteq> ?X" if "s \<in> set (ts' @ bs)" for s using va[OF that] by simp
      qed
      ultimately show ?thesis by (blast)
    qed
  qed
qed

lemma conv_ok_eta_long_conversion: "conv_ok eta_long_conversion"
  unfolding conv_ok_def
proof (intro allI impI)
  fix t T m r assume ok: "okT (eta_long_conversion (CTerm t T m)) r" and c: "closed t" and ty: "\<forall>e. e \<turnstile> t : T"
  from ok obtain t' P where el: "ok (Pure_Rules.eta_long [] t) t'" and mk: "ok (mk_equals (t, t')) P"
    and r: "r = mk_rep m [] P"
    by (auto simp: eta_long_conversion_def)
  have bv: "bvok e [] t" for e using c by (simp add: bvok_def closed_iff_loose_bvar1)
  have elc: "e \<turnstile> t' : T \<and> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and> lbsub t' t" for e
    using eta_long_correct[OF el HOL.refl ty[rule_format, of e] bv[of e]] .
  have ty': "e \<turnstile> t' : T" for e using elc by blast
  have cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" and lb: "lbsub t' t" using elc by blast+
  have c': "closed t'" using c lb by (auto simp: lbsub_def closed_iff_loose_bvar1)
  have v: "vars t' \<subseteq> vars t" "ttvars t' \<subseteq> ttvars t" using eta_long_vars[OF el HOL.refl] by simp_all
  have "P = eq_const T $ t $ t'" using mk_equals_ok[OF mk c] ty by (blast)
  with r c' ty' cv v
  show "\<exists>t'. r = mk_rep m [] (eq_const T $ t $ t') \<and> closed t' \<and> (\<forall>e. e \<turnstile> t' : T) \<and> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and>
      vars t' \<subseteq> vars t \<and> ttvars t' \<subseteq> ttvars t"
    by (blast)
qed

end

definition eta_long_conversion_thm :: "pure_cterm \<Rightarrow> 'u pure_thm option" where
  "eta_long_conversion_thm ct = conversion_thm ct eta_long_conversion"

theorem eta_long_conversion_thm:
  assumes "eta_long_conversion_thm ct = Some th"
  obtains r where "okT (eta_long_conversion (crep_of ct)) r" "sign_eq (csign_of ct)" "rep_thm th = conv_data ct r"
  using conversion_thm[OF assms[unfolded eta_long_conversion_thm_def] pure_sig.conv_ok_eta_long_conversion] by (blast)


subsection \<open>Permutation of premises\<close>

lemma ttvars_list_implies_eq: "ttvars (list_implies As B) = (\<Union>A\<in>set As. ttvars A) \<union> ttvars B"
  by (induction As) (auto simp: implies_def propT_def ttvars_def)


context pure_sig
begin

lemma permute_data_wf:
  assumes ok: "okT (permute_data j k th0) (th, prems', m)" and w: "wtp (th_prop th0)"
  shows "wtp (th_prop th)" "vars (th_prop th) = vars (th_prop th0)" "ttvars (th_prop th) = ttvars (th_prop th0)"
    "th_tpairs th = th_tpairs th0" "th_maxidx th = th_maxidx th0"
    "set prems' = set (strip_imp_prems (th_prop th0))"
proof -
  let ?ps = "strip_imp_prems (th_prop th0)" and ?C = "strip_imp_concl (th_prop th0)"
  have P: "th_prop th0 = list_implies ?ps ?C"
    by (rule list_implies_strip_imp[OF wtpD(2)[OF w, of "\<lambda>_. propT"]])
  obtain J M where JM: "J \<le> length ?ps" "M \<le> length ?ps - J"
    and p': "prems' = take J ?ps @ drop M (drop J ?ps) @ take M (drop J ?ps)"
    and th: "th = mk_rep (th_maxidx th0) (th_tpairs th0) (list_implies prems' ?C)"
    by (rule permute_data_precise[OF ok P])
  have s: "set prems' = set ?ps"
    unfolding p' by (metis append_take_drop_id set_append set_rotate_take_drop)
  have l: "length prems' = length ?ps" unfolding p' using JM by simp
  have wps: "(\<forall>A\<in>set ?ps. wtp A) \<and> wtp ?C"
    using w wtp_list_implies[where As = ?ps and As' = ?ps and B = ?C and B' = ?C] P by (auto)
  have "wtp (list_implies prems' ?C)"
    using w wps wtp_list_implies[where As = ?ps and As' = prems' and B = ?C and B' = ?C] P l s by (auto)
  then show "wtp (th_prop th)" by (simp add: th mk_rep_def)
  have "vars (th_prop th) = vars (list_implies ?ps ?C)"
    by (simp add: th mk_rep_def vars_list_implies s)
  then show "vars (th_prop th) = vars (th_prop th0)" by (subst P)
  have "ttvars (th_prop th) = ttvars (list_implies ?ps ?C)"
    by (simp add: th mk_rep_def ttvars_list_implies_eq s)
  then show "ttvars (th_prop th) = ttvars (th_prop th0)" by (subst P)
  show "th_tpairs th = th_tpairs th0" "th_maxidx th = th_maxidx th0" by (simp_all add: th mk_rep_def)
  show "set prems' = set ?ps" by (rule s)
qed

lemma thm_wf_same_vars:
  assumes "thm_wf m hs tps P" "wtp Q" "vars Q = vars P" "ttvars Q = ttvars P"
  shows "thm_wf m hs tps Q"
  using assms unfolding thm_wf_def wt_thm_def ibelow_def vars_thm_def tvars_thm_def by simp

lemma strip_imp_prems_sub:
  "A \<in> set (strip_imp_prems t) \<Longrightarrow> vars A \<subseteq> vars t \<and> typs A \<subseteq> typs t \<and> (\<forall>k. loose_bvar A k \<longrightarrow> loose_bvar t k)"
proof (induction t rule: strip_imp_prems.induct)
  case (1 t)
  show ?case
  proof (cases "dest_imp t")
    case None
    then show ?thesis using "1.prems" by (subst (asm) strip_imp_prems.simps) simp
  next
    case (Some p)
    then obtain H B where d: "dest_imp t = Some (H, B)" by (cases p) auto
    then obtain U where t: "t = Const STR ''Pure.imp'' U $ H $ B" by (auto simp: dest_imp_Some)
    from "1.prems" d have "A = H \<or> A \<in> set (strip_imp_prems B)" by (subst (asm) strip_imp_prems.simps) simp
    then show ?thesis using "1.IH"[OF d HOL.refl] t by (auto)
  qed
qed

end

definition permute_prems_thm :: "integer \<Rightarrow> integer \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "permute_prems_thm j k th =
    map_option (\<lambda>(r, prems', m). Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
        (bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)))
        (bindM (zproof_of th) (zpermute_prems_proof (pure_sig.ztargs (sg_consts (sign_of th))) prems' j m)))))
      (resT (permute_data j k (rep_of th)))"

lemma thm_ok_permute_prems:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (permute_data j k (rep_of th)) (r, prems', m)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)))
    (bindM (zproof_of th) (zpermute_prems_proof (pure_sig.ztargs (sg_consts (sign_of th))) prems' j m)))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  have okp: "okT (permute_prems j k (rep_of th)) r" using ok by (simp add: permute_prems_def returnW_def, blast)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    note pw = permute_data_wf[OF ok w]
    have "thm_wf (th_maxidx r) (hyps_of th) (th_tpairs r) (th_prop r)"
      unfolding pw(4,5) by (rule thm_wf_same_vars[OF w0 pw(1-3)])
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by simp
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps' by (simp add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule permute_prems_valid(1)[OF okp _ w]) (use pure_thm_valid_in[of th M] M in simp)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    note pw = permute_data_wf[OF ok w]
    have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
    have pA: "pnn A" "\<not> loose_bvar A 0" if "A \<in> set prems'" for A
    proof -
      have "A \<in> set (strip_imp_prems (th_prop (rep_of th)))" using that pw(6) by simp
      note sub = strip_imp_prems_sub[OF this]
      show "pnn A" using pP sub by (auto simp: pnn_def)
      show "\<not> loose_bvar A 0" using sub wtpD(1)[OF w] by (auto simp: closed_def)
    qed
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = permute_prems_proof prems' j m q"
        by (auto simp: bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        unfolding pf by (rule permute_prems_proof_valid[OF ok vq(1) w])
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using vq(2,3) by (simp_all add: pf permute_prems_proof_def Let_def prf_idx_mk_AbsP prf_idx_proof_combP
          prf_nolb_proof_combP, auto)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zpermute_prems_proof ztargs prems' j m) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zpermute_prems_proof ztargs prems' j m q = return z"
        by (auto simp: bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zpermute_prems_proof_valid[OF ok vq(1) w _ z]) (use pA pnn_noneg in blast)
      moreover from z obtain Ps where Ps: "list_all2 (\<lambda>A t. zterm_of ztargs A = return t) prems' Ps"
        and zq: "z = ZAbsps Ps (ZAppps q (map ZBoundp (downto (integer_of_nat (length prems') - 1)
          (integer_of_nat (length prems') - j) @ downto (m - 1) 0 @ downto (integer_of_nat (length prems') - j - 1) m)))"
        by (auto simp: zpermute_prems_proof_def Let_def bindZ_eq_returnZ mapZ_eq_returnZ)
      have Pz: "zterm_ok t \<and> \<not> zloose t 0" if "t \<in> set Ps" for t
      proof -
        from that obtain i where i: "i < length Ps" "t = Ps ! i" by (auto simp: in_set_conv_nth)
        have il: "i < length prems'" using i(1) list_all2_lengthD[OF Ps] by simp
        have zt: "zterm_of ztargs (prems' ! i) = return t" using list_all2_nthD[OF Ps il] i(2) by simp
        show ?thesis using zterm_ok_zterm_of_pnn[OF zt pA(1)] zloose_zterm_of[OF zt] pA(2) nth_mem[OF il]
          by simp
      qed
      have "zinv z" using vq(2) Pz by (auto simp: zq zinv_ZAbsps zinv_ZAppps)
      moreover have "znolb 0 z" using vq(3) Pz by (auto simp: zq znolb_ZAbsps znolb_ZAppps)
      moreover have "zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def zhyps_ZAppps)
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" by simp
    qed
  qed
qed

theorem permute_prems_thm:
  assumes "permute_prems_thm j k th = Some th'"
  obtains r prems' m where "okT (permute_data j k (rep_of th)) (r, prems', m)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)))
      (bindM (zproof_of th) (zpermute_prems_proof (pure_sig.ztargs (sg_consts (sign_of th))) prems' j m)))"
proof -
  from assms obtain r prems' m where ok: "okT (permute_data j k (rep_of th)) (r, prems', m)"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)))
      (bindM (zproof_of th) (zpermute_prems_proof (pure_sig.ztargs (sg_consts (sign_of th))) prems' j m))))"
    by (auto simp: permute_prems_thm_def resT_Some)
  show thesis
    by (rule that[OF ok]) (use thm_ok_permute_prems[OF ok] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed

subsection \<open>Rotation of the premises of a subgoal\<close>

lemma zinv_ZAbsts: "zinv (ZAbsts xs p) \<longleftrightarrow> (\<forall>(a, T)\<in>set xs. ztyp_ok T) \<and> zinv p"
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases x) (simp add: ZAbsts_def)
qed (simp add: ZAbsts_def)

lemma znolb_ZAbsts: "znolb k (ZAbsts xs p) \<longleftrightarrow> znolb (k + integer_of_nat (length xs)) p"
proof (induction xs arbitrary: k)
  case (Cons x xs)
  obtain a T where x: "x = (a, T)" by (cases x)
  have "k + 1 + integer_of_nat (length xs) = k + integer_of_nat (length (x # xs))"
    by (simp add: integer_of_nat_eq_of_nat)
  moreover have "znolb k (ZAbsts (x # xs) p) = znolb (k + 1) (ZAbsts xs p)" by (simp add: ZAbsts_def x)
  ultimately show ?case by (simp only: Cons.IH)
qed (simp add: ZAbsts_def)

lemma zhyps_ZAbsts [simp]: "zhyps (ZAbsts xs p) = zhyps p"
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases x) (simp add: ZAbsts_def)
qed (simp add: ZAbsts_def)

lemma prf_idx_mk_Abst: "prf_idx P (mk_Abst ps p) \<longleftrightarrow> prf_idx P p"
  by (induction ps) (auto simp: mk_Abst_def)

lemma prf_nolb_mk_Abst: "prf_nolb k (mk_Abst ps p) \<longleftrightarrow> prf_nolb (k + integer_of_nat (length ps)) p"
  by (induction ps arbitrary: k) (auto simp: mk_Abst_def algebra_simps integer_of_nat_eq_of_nat)

lemma loose_bvar_list_forall:
  "loose_bvar (list_forall ps X) k \<longleftrightarrow> loose_bvar X (k + integer_of_nat (length ps))"
  by (induction ps X arbitrary: k rule: list_forall.induct)
    (auto simp: all_const_def algebra_simps integer_of_nat_eq_of_nat)

context pure_sig
begin

lemma rotate_data_wf:
  assumes ok: "okT (rotate_data k i state) (th, Bs, Bi', params, asms, m)" and w: "wtp (th_prop state)"
  shows "wtp (th_prop th)" "vars (th_prop th) = vars (th_prop state)" "ttvars (th_prop th) = ttvars (th_prop state)"
    "th_tpairs th = th_tpairs state" "th_maxidx th = th_maxidx state"
    "\<forall>A\<in>set (Bs @ [Bi']). vars A \<subseteq> vars (th_prop state) \<and> ttvars A \<subseteq> ttvars (th_prop state) \<and> \<not> loose_bvar A 0"
    "\<forall>A\<in>set asms. vars A \<subseteq> vars (th_prop state) \<and> ttvars A \<subseteq> ttvars (th_prop state) \<and>
      \<not> loose_bvar A (integer_of_nat (length params))"
    "\<forall>(a, T)\<in>set params. tvars T \<subseteq> ttvars (th_prop state)"
proof -
  obtain tpairs Bi C M where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and th: "th = mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C)"
    and ps: "params = strip_all_vars Bi" "asms = strip_imp_prems (strip_all_body Bi)"
    and Bi'0: "Bi' = Bi \<and> (M = 0 \<or> M = length asms) \<or>
      Bi' = list_forall params (list_implies (drop M asms @ take M asms) (strip_imp_concl (strip_all_body Bi)))"
    by (rule rotate_data_precise[OF ok])
  note ds = okT_dest_state[OF d]
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  define c where "c = strip_imp_concl (strip_all_body Bi)"
  have tP: "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi]) C : propT" using wtpD(2)[OF w] P by simp
  note tD = typing_list_impliesD[OF tP]
  have tBi: "(\<lambda>_. propT) \<turnstile> Bi : propT" using tD by simp
  have Bi: "Bi = list_forall params (list_implies asms c)"
  proof -
    have "pushes (\<lambda>_. propT) (map snd params) \<turnstile> strip_all_body Bi : propT"
      using tBi list_forall_strip_all[OF tBi] unfolding ps(1) by (metis typing_list_forall)
    from list_implies_strip_imp[OF this] list_forall_strip_all[OF tBi] show ?thesis
      by (simp add: ps c_def)
  qed
  define As' where "As' = drop M asms @ take M asms"
  have s: "set As' = set asms" unfolding As'_def by (rule set_rotate_take_drop)
  have Bi'': "Bi' = Bi \<or> Bi' = list_forall params (list_implies As' c)" using Bi'0 by (auto simp: As'_def c_def)
  have tBi0: "(\<lambda>_. propT) \<turnstile> list_forall params (list_implies asms c) : propT" using tBi Bi by simp
  note pm = list_forall_implies_perm[OF tBi0 s]
  have tBi': "(\<lambda>_. propT) \<turnstile> Bi' : propT" using Bi'' pm(1) tBi by (blast)
  have lb: "loose_bvar Bi' k \<longleftrightarrow> loose_bvar Bi k" for k using Bi'' pm(2)[of k] Bi by metis
  have vB: "vars Bi' = vars Bi" "ttvars Bi' = ttvars Bi"
    using Bi'' unfolding Bi by (auto simp: vars_list_implies ttvars_list_forall_eq ttvars_list_implies_eq s)
  have cP: "\<not> loose_bvar (th_prop state) 0" using wtpD(1)[OF w] by (simp add: closed_def)
  show "wtp (th_prop th)"
  proof (rule wtpI)
    show "closed (th_prop th)"
      using cP P lb by (simp add: th mk_rep_def closed_def loose_bvar_list_implies)
    have "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi']) C : propT"
      using tD tBi' typing_list_implies_imp[OF tP] by (intro typing_list_impliesI) auto
    then show "(\<lambda>_. propT) \<turnstile> th_prop th : propT" by (simp add: th mk_rep_def)
  qed
  show "vars (th_prop th) = vars (th_prop state)"
    using vB by (simp add: th P mk_rep_def vars_list_implies)
  show "ttvars (th_prop th) = ttvars (th_prop state)"
    using vB by (simp add: th P mk_rep_def ttvars_list_implies_eq)
  show "th_tpairs th = th_tpairs state" "th_maxidx th = th_maxidx state"
    using ds(1) by (simp_all add: th mk_rep_def)
  show "\<forall>A\<in>set (Bs @ [Bi']). vars A \<subseteq> vars (th_prop state) \<and> ttvars A \<subseteq> ttvars (th_prop state) \<and>
      \<not> loose_bvar A 0"
    using cP vB lb unfolding P by (auto simp: vars_list_implies ttvars_list_implies_eq loose_bvar_list_implies)
  have aB: "vars A \<subseteq> vars Bi \<and> ttvars A \<subseteq> ttvars Bi \<and> \<not> loose_bvar A (integer_of_nat (length params))"
    if "A \<in> set asms" for A
  proof -
    have "\<not> loose_bvar Bi 0" using cP P by (simp add: loose_bvar_list_implies)
    then have "\<not> loose_bvar (list_implies asms c) (integer_of_nat (length params))"
      unfolding Bi loose_bvar_list_forall by simp
    then show ?thesis using that unfolding Bi
      by (auto simp: vars_list_implies ttvars_list_forall_eq ttvars_list_implies_eq loose_bvar_list_implies)
  qed
  have BP: "vars Bi \<subseteq> vars (th_prop state)" "ttvars Bi \<subseteq> ttvars (th_prop state)"
    unfolding P by (auto simp: vars_list_implies ttvars_list_implies_eq)
  show "\<forall>A\<in>set asms. vars A \<subseteq> vars (th_prop state) \<and> ttvars A \<subseteq> ttvars (th_prop state) \<and>
      \<not> loose_bvar A (integer_of_nat (length params))"
    using aB BP by (blast)
  show "\<forall>(a, T)\<in>set params. tvars T \<subseteq> ttvars (th_prop state)"
    using BP(2) unfolding Bi by (auto simp: ttvars_list_forall_eq btvars_def)
qed

end

definition rotate_rule_thm :: "integer \<Rightarrow> integer \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "rotate_rule_thm k i th =
    map_option (\<lambda>(r, Bs, Bi', params, asms, m). Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
        (bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)))
        (bindM (zproof_of th) (zrotate_proof (pure_sig.ztargs (sg_consts (sign_of th))) Bs Bi' params asms m)))))
      (resT (rotate_data k i (rep_of th)))"

lemma thm_ok_rotate_rule:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (rotate_data k i (rep_of th)) (r, Bs, Bi', params, asms, m)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)))
    (bindM (zproof_of th) (zrotate_proof (pure_sig.ztargs (sg_consts (sign_of th))) Bs Bi' params asms m)))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  have okr: "okT (rotate_rule k i (rep_of th)) r" using ok by (simp add: rotate_rule_def returnW_def, blast)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    note rw = rotate_data_wf[OF ok w]
    have "thm_wf (th_maxidx r) (hyps_of th) (th_tpairs r) (th_prop r)"
      unfolding rw(4,5) by (rule thm_wf_same_vars[OF w0 rw(1-3)])
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by simp
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps' by (simp add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule rotate_rule_valid(1)[OF okr _ w]) (use pure_thm_valid_in[of th M] M in simp)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    note rw = rotate_data_wf[OF ok w]
    have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
    have sub_pnn: "pnn A" if "vars A \<subseteq> vars (th_prop (rep_of th))" "ttvars A \<subseteq> ttvars (th_prop (rep_of th))" for A
      using pP that by (auto simp: pnn_iff)
    have pB: "pnn A" "\<not> loose_bvar A 0" if "A \<in> set (Bs @ [Bi'])" for A
      using rw(6) that sub_pnn by (blast+)
    have pA: "pnn A" "\<not> loose_bvar A (integer_of_nat (length params))" if "A \<in> set asms" for A
      using rw(7) that sub_pnn by (blast+)
    have pT: "tnn T" if "(a, T) \<in> set params" for a T
      using rw(8) that pP by (fastforce simp: pnn_iff tnn_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    have dl: "\<not> loose_bvar (Bound j) (integer_of_nat (length params))"
      if "j \<in> set (downto (integer_of_nat (length params) - 1) 0)" for j
      using downto_le[OF that] by simp
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = rotate_proof Bs Bi' params asms m q"
        by (auto simp: bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        unfolding pf by (rule rotate_proof_valid[OF ok vq(1) w])
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
        using vq(2) by (simp add: pf rotate_proof_def Let_def prf_idx_mk_AbsP prf_idx_proof_combP prf_idx_mk_Abst
          prf_idx_proof_combt, auto)
      moreover have "prf_nolb 0 pf"
        using vq(3) dl by (simp add: pf rotate_proof_def Let_def prf_nolb_proof_combP prf_nolb_mk_Abst
          prf_nolb_proof_combt, auto)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zrotate_proof ztargs Bs Bi' params asms m) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zrotate_proof ztargs Bs Bi' params asms m q = return z"
        by (auto simp: bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zrotate_proof_valid[OF ok vq(1) w _ _ _ z])
          (use pB pA pT pnn_noneg tnn_tnoneg in \<open>blast+\<close>)
      moreover from z obtain Bs' asms' where B: "list_all2 (\<lambda>A t. zterm_of ztargs A = return t) (Bs @ [Bi']) Bs'"
        and A: "list_all2 (\<lambda>A t. zterm_of ztargs A = return t) asms asms'"
        and zq: "z = ZAbsps Bs' (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs)) 1) @
          [ZAbsts (map (\<lambda>(a, T). (a, ztyp_of T)) params) (ZAbsps asms'
            (ZAppps (ZAppts (ZBoundp (integer_of_nat (length asms))) (map ZBound (downto (integer_of_nat (length params) - 1) 0)))
              (map ZBoundp (downto (integer_of_nat (length asms) - m - 1) 0 @
                downto (integer_of_nat (length asms) - 1) (integer_of_nat (length asms) - m)))))]))"
        by (auto simp: zrotate_proof_def bindZ_eq_returnZ mapZ_eq_returnZ Let_def)
      have Bz: "zterm_ok t \<and> \<not> zloose t 0" if "t \<in> set Bs'" for t
      proof -
        from that obtain j where j: "j < length Bs'" "t = Bs' ! j" by (auto simp: in_set_conv_nth)
        have jl: "j < length (Bs @ [Bi'])" using j(1) list_all2_lengthD[OF B] by simp
        have zt: "zterm_of ztargs ((Bs @ [Bi']) ! j) = return t" using list_all2_nthD[OF B jl] j(2) by simp
        show ?thesis using zterm_ok_zterm_of_pnn[OF zt pB(1)] zloose_zterm_of[OF zt] pB(2) nth_mem[OF jl] by simp
      qed
      have Az: "zterm_ok t \<and> \<not> zloose t (integer_of_nat (length params))" if "t \<in> set asms'" for t
      proof -
        from that obtain j where j: "j < length asms'" "t = asms' ! j" by (auto simp: in_set_conv_nth)
        have jl: "j < length asms" using j(1) list_all2_lengthD[OF A] by simp
        have zt: "zterm_of ztargs (asms ! j) = return t" using list_all2_nthD[OF A jl] j(2) by simp
        show ?thesis using zterm_ok_zterm_of_pnn[OF zt pA(1)] zloose_zterm_of[OF zt] pA(2) nth_mem[OF jl] by simp
      qed
      have Tz: "\<forall>(a, T)\<in>set (map (\<lambda>(a, T). (a, ztyp_of T)) params). ztyp_ok T"
        using pT ztyp_ok_ztyp_of by (auto)
      have dz: "\<not> zloose (ZBound j) (integer_of_nat (length params))"
        if "j \<in> set (downto (integer_of_nat (length params) - 1) 0)" for j
        using downto_le[OF that] by simp
      have "zinv z" using vq(2) Bz Az Tz
        by (auto simp: zq zinv_ZAbsps zinv_ZAppps zinv_ZAbsts zinv_ZAppts)
      moreover have "znolb 0 z" using vq(3) Bz Az dz
        by (auto simp: zq znolb_ZAbsps znolb_ZAppps znolb_ZAbsts znolb_ZAppts)
      moreover have "zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def zhyps_ZAppps)
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" by simp
    qed
  qed
qed

theorem rotate_rule_thm:
  assumes "rotate_rule_thm k i th = Some th'"
  obtains r Bs Bi' params asms m where "okT (rotate_data k i (rep_of th)) (r, Bs, Bi', params, asms, m)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)))
      (bindM (zproof_of th) (zrotate_proof (pure_sig.ztargs (sg_consts (sign_of th))) Bs Bi' params asms m)))"
proof -
  from assms obtain r Bs Bi' params asms m where ok: "okT (rotate_data k i (rep_of th)) (r, Bs, Bi', params, asms, m)"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)))
      (bindM (zproof_of th) (zrotate_proof (pure_sig.ztargs (sg_consts (sign_of th))) Bs Bi' params asms m))))"
    by (auto simp: rotate_rule_thm_def resT_Some)
  show thesis
    by (rule that[OF ok]) (use thm_ok_rotate_rule[OF ok] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed


subsection \<open>Universal introduction\<close>

text \<open>
  The axioms of the proofs are closed (\<open>Theory.add_axiom\<close> uses \<open>Logic.varify_global\<close>, the
  propositions of theorems are closed by \<open>Logic.unconstrainT\<close> and \<open>prop_args\<close>): their closures
  contain no free variables.
\<close>

definition sign_closed :: "sign \<Rightarrow> bool" where
  "sign_closed c \<longleftrightarrow> (\<forall>A. fnames (sg_close c A) = {} \<and> (\<forall>b S. TFree b S \<notin> tatoms (sg_close c A)))"

definition var_name :: "pterm \<Rightarrow> name" where
  "var_name x = (case x of Free a _ \<Rightarrow> a | Var (a, _) _ \<Rightarrow> a | _ \<Rightarrow> STR '''')"

lemma abstract_over_aux_sub:
  "vars (abstract_over_aux x lev t) \<subseteq> vars t \<and> typs (abstract_over_aux x lev t) \<subseteq> typs t"
  by (induction x lev t rule: abstract_over_aux.induct) auto

lemma loose_bvar_abstract_over_aux':
  "\<not> loose_bvar t k \<Longrightarrow> lev \<le> k \<Longrightarrow> \<not> loose_bvar (abstract_over_aux x lev t) (k + 1)"
  using loose_bvar_abstract_over_aux[of t "k + 1" lev x] loose_bvar_mono[of t "k + 1" k] by (force)

lemma prf_idx_prf_abstract_over_aux: "prf_idx P p \<Longrightarrow> prf_idx P (prf_abstract_over_aux v lev p)"
  unfolding prf_idx_def using abstract_over_aux_sub by (fastforce dest: prf_terms_prf_abstract_over_aux)

lemma prf_nolb_prf_abstract_over_aux:
  "prf_nolb k p \<Longrightarrow> lev \<le> k \<Longrightarrow> prf_nolb (k + 1) (prf_abstract_over_aux v lev p)"
proof (induction v lev p arbitrary: k rule: prf_abstract_over_aux.induct)
  case (2 v lev a T p)
  from "2.prems" have "prf_nolb (k + 1) p" "lev + 1 \<le> k + 1" by simp_all
  from "2.IH"[OF this] show ?case by simp
qed (auto simp: prf_abstract_term_eq loose_bvar_abstract_over_aux')

lemma zterm_ok_zabstract_term: "zterm_ok t \<Longrightarrow> zterm_ok (zabstract_term z i t)"
  by (induction z i t rule: zabstract_term.induct) auto

lemma zloose_zabstract_term:
  "\<not> zloose t k \<Longrightarrow> lev \<le> k \<Longrightarrow> \<not> zloose (zabstract_term z lev t) (k + 1)"
proof (induction z lev t arbitrary: k rule: zabstract_term.induct)
  case (1 z i x T t)
  show ?case
  proof (cases "aconv_zterm (ZAbs x T t) z")
    case False
    from "1.prems" have "\<not> zloose t (k + 1)" "i + 1 \<le> k + 1" by simp_all
    from "1.IH"[OF False this] False show ?thesis by simp
  qed (use "1.prems" in simp)
qed (auto simp: zloose_le)

lemma zinv_zabstract_proof: "zinv p \<Longrightarrow> zinv (zabstract_proof z i p)"
proof (induction z i p rule: zabstract_proof.induct)
  case (4 z i c instT inst)
  then show ?case by (auto simp: zterm_ok_zabstract_term)
qed (auto simp: zterm_ok_zabstract_term)

lemma znolb_zabstract_proof: "znolb k p \<Longrightarrow> lev \<le> k \<Longrightarrow> znolb (k + 1) (zabstract_proof z lev p)"
proof (induction z lev p arbitrary: k rule: zabstract_proof.induct)
  case (1 z i x T p)
  from "1.prems" have "znolb (k + 1) p" "i + 1 \<le> k + 1" by simp_all
  from "1.IH"[OF this] show ?case by simp
qed (auto simp: zloose_zabstract_term)

lemma zhyps_zabstract_proof [simp]: "zhyps (zabstract_proof z i p) = zhyps p"
  by (induction z i p rule: zabstract_proof.induct) auto

lemma zterm_ok_zvars: "zterm_ok t \<Longrightarrow> (x, U) \<in> zvars t \<Longrightarrow> ztyp_ok U"
  by (induction t) auto

context pure_sig
begin

lemma forall_intr_shape:
  assumes ok: "okT (forall_intr hs (CTerm x T m) th0) th" and tx: "\<And>e. e \<turnstile> x : T"
  obtains b z where "th = mk_rep (max m (th_maxidx th0)) (th_tpairs th0) (all_const T $ Abs b T (abstract_over x (th_prop th0)))"
    "x = Free b T \<or> x = Var z T" "var_name x = b"
proof (cases x)
  case (Free a U)
  with tx[of "\<lambda>_. propT"] have "U = T" by (auto)
  with ok Free that[of a] show ?thesis
    by (auto simp: forall_intr_def returnW_def raiseW_def Let_def var_name_def split: if_splits)
next
  case (Var zi U)
  obtain a j where zi: "zi = (a, j)" by (cases zi)
  with Var tx[of "\<lambda>_. propT"] have "U = T" by (auto)
  with ok Var zi that[of a] show ?thesis
    by (auto simp: forall_intr_def returnW_def raiseW_def Let_def var_name_def split: if_splits)
qed (use ok in \<open>auto simp: forall_intr_def raiseW_def Let_def\<close>)

lemma wtp_forall_abstract:
  assumes x: "x = Free a T \<or> x = Var z T" and w: "wtp P" and tx: "\<And>e. e \<turnstile> x : T"
  shows "wtp (all_const T $ Abs b T (abstract_over x P))"
proof (rule wtpI)
  have "\<not> loose_bvar P 0" using wtpD(1)[OF w] by (simp add: closed_def)
  from loose_bvar_abstract_over_aux'[OF this, of 0 x]
  show "closed (all_const T $ Abs b T (abstract_over x P))" by (simp add: closed_def abstract_over_def all_const_def)
  have cT: "cert_typ alg ar T" using tx[of "\<lambda>_. propT"] x by (auto)
  have cP: "cert_typ alg ar propT" by (rule typing_cert_closed[OF wtpD(2)[OF w] wtpD(1)[OF w]])
  have tQ: "(\<lambda>_. propT)\<langle>0:T\<rangle> \<turnstile> abstract_over x P : propT"
    unfolding abstract_over_def
    by (rule typing_abstract_over_aux[OF x wtpD(2)[OF w]]) (use wtpD(1)[OF w] in \<open>simp_all add: closed_def\<close>)
  show "(\<lambda>_. propT) \<turnstile> all_const T $ Abs b T (abstract_over x P) : propT"
    unfolding typing_all_const using cT cP tQ by (simp add: all_type_def cert_typ_fun)
qed

end

definition forall_intr_thm :: "pure_cterm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "forall_intr_thm ct th =
    (if csign_of ct = sign_of th \<and> sign_closed (sign_of th) then
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p)))
          (bindM (zproof_of th) (zforall_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct))
            (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)))))))
        (resT (forall_intr (hyps_of th) (crep_of ct) (rep_of th)))
     else None)"

lemma thm_ok_forall_intr:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (forall_intr (hyps_of th) (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
    and sc: "sign_closed (sign_of th)"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zforall_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct))
      (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  obtain x T m where cr: "crep_of ct = CTerm x T m" by (cases "crep_of ct")
  have ok': "okT (forall_intr (hyps_of th) (CTerm x T m) (rep_of th)) r" using ok by (simp add: cr)
  have wfc: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm x T m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
    using pure_cterm_wf[of ct] ps c by (simp add: cr)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps])
    have tx: "\<And>e. e \<turnstile> x : T" and cx: "closed x" using wf by (simp_all add: cterm_wf_def)
    obtain b z where r: "r = mk_rep (max m (th_maxidx (rep_of th))) (th_tpairs (rep_of th))
        (all_const T $ Abs b T (abstract_over x (th_prop (rep_of th))))"
      and x: "x = Free b T \<or> x = Var z T"
      by (rule forall_intr_shape[OF ok' tx])
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    have tT: "tvars T \<subseteq> ttvars x" by (rule typing_tvars_closed[OF tx cx])
    note ao = abstract_over_aux_sub[of x 0 "th_prop (rep_of th)"]
    have "thm_wf (max m (th_maxidx (rep_of th))) (hyps_of th) (th_tpairs (rep_of th))
        (all_const T $ Abs b T (abstract_over x (th_prop (rep_of th))))"
    proof (rule thm_wf_extend[OF w0 wtp_forall_abstract[OF x w tx], where V = "vars x" and TV = "ttvars x"])
      show "vars (all_const T $ Abs b T (abstract_over x (th_prop (rep_of th)))) \<subseteq> vars (th_prop (rep_of th)) \<union> vars x"
        using ao by (auto simp: all_const_def abstract_over_def)
      show "ttvars (all_const T $ Abs b T (abstract_over x (th_prop (rep_of th)))) \<subseteq> ttvars (th_prop (rep_of th)) \<union> ttvars x"
        using ao tT by (auto simp: all_const_def abstract_over_def ttvars_def propT_def)
    qed (use wf in \<open>auto simp: cterm_wf_def ibelow_def\<close>)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps'])
    have tx: "\<And>e. e \<turnstile> x : T" using wf by (simp add: cterm_wf_def)
    have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by (simp add: thm_wf_def)
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid_in[of th M] M by simp
    have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      by (rule valid_mono[OF v]) simp
    then have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule forall_intr_valid[OF ok' _ wt tx])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps])
    have tx: "\<And>e. e \<turnstile> x : T" and cx: "closed x" using wf by (simp_all add: cterm_wf_def)
    have px: "pnn x" using wf by (simp add: cterm_wf_def pnn_iff)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using w0 by (simp add: thm_wf_def)
    have tT: "tnn T" using typing_tvars_closed[OF tx cx] px unfolding tnn_def pnn_iff by (force)
    have scl: "fnames (sg_close ?c A) = {}" "TFree b S \<notin> tatoms (sg_close ?c A)" for A b S
      using sc by (simp_all add: sign_closed_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p))
          = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = forall_intr_proof (var_name x) x q"
        by (auto simp: bindP_eq_returnP cr)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        unfolding pf by (rule forall_intr_rule_proof_valid[OF ok' vq(1) wt tx]) (simp add: scl)
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using prf_idx_prf_abstract_over_aux[OF vq(2)] prf_nolb_prf_abstract_over_aux[OF vq(3), of 0]
        by (simp_all add: pf forall_intr_proof_def prf_abstract_over_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zforall_intr_proof ztargs (ct_T (crep_of ct)) (var_name (ct_t (crep_of ct)))
          (ct_t (crep_of ct))) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zforall_intr_proof ztargs T (var_name x) x q = return z"
        by (auto simp: bindZ_eq_returnZ cr)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have eqc: "zeq_close_ok" using scl by (simp add: zeq_close_ok_def)
      have cz: "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) q"
      proof (rule zprf_all_mono[of zterm_ok ztyp_ok])
        show "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp add: zinv_def)
        fix t assume "zterm_ok t"
        then show "\<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T"
          using zterm_ok_zvars by (fastforce simp: ztyp_ok_def zcanon_def)
      qed simp
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zforall_intr_rule_proof_valid[OF ok' vq(1) wt tx pnn_noneg[OF px] eqc cz z])
      moreover from z obtain zx where zx: "zterm_of ztargs x = return zx"
        and zq: "z = ZAbst (var_name x) (ztyp_of T) (zabstract_proof zx 0 q)"
        by (auto simp: zforall_intr_proof_def bindZ_eq_returnZ)
      have "zinv z" using zinv_zabstract_proof[OF vq(2)] ztyp_ok_ztyp_of[OF tT] by (simp add: zq)
      moreover have "znolb 0 z" using znolb_zabstract_proof[OF vq(3), of 0] by (simp add: zq)
      moreover have "zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def)
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" by simp
    qed
  qed
qed

theorem forall_intr_thm:
  assumes "forall_intr_thm ct th = Some th'"
  obtains r where "okT (forall_intr (hyps_of th) (crep_of ct) (rep_of th)) r" "csign_of ct = sign_of th"
    "sign_closed (sign_of th)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p)))
      (bindM (zproof_of th) (zforall_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct))
        (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)))))"
proof -
  from assms obtain r where c: "csign_of ct = sign_of th" and sc: "sign_closed (sign_of th)"
    and ok: "okT (forall_intr (hyps_of th) (crep_of ct) (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p)))
      (bindM (zproof_of th) (zforall_intr_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct))
        (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct))))))"
    by (auto simp: forall_intr_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c sc]) (use thm_ok_forall_intr[OF ok c sc] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed

subsection \<open>Abstraction\<close>

lemma abstract_rule_res_ok:
  assumes "okT (abstract_rule_res b hs ct th0) (r, U, f, g)"
  shows "okT (abstract_rule b hs ct th0) r" "okT (abstract_rule_data b hs ct th0) (U, f, g)"
  using assms by (auto simp: abstract_rule_res_def abstract_rule_def)

context pure_sig
begin

lemma abstract_rule_shape:
  assumes ok: "okT (abstract_rule b hs (CTerm x T m) th0) th"
    and ad: "okT (abstract_rule_data b hs (CTerm x T m) th0) (U, f, g)"
    and eq: "eq_ok" and w: "wtp (th_prop th0)" and tx: "\<And>e. e \<turnstile> x : T" and cx: "closed x"
  shows "wtp (th_prop th)" "th_maxidx th = maxidx_typ T (th_maxidx th0)" "th_tpairs th = th_tpairs th0"
    "vars (th_prop th) \<subseteq> vars (th_prop th0)" "ttvars (th_prop th) \<subseteq> ttvars (th_prop th0) \<union> tvars T"
    "vars f \<subseteq> vars (th_prop th0)" "ttvars f \<subseteq> ttvars (th_prop th0) \<union> tvars T"
    "vars g \<subseteq> vars (th_prop th0)" "ttvars g \<subseteq> ttvars (th_prop th0) \<union> tvars T"
    "closed f" "closed g"
proof -
  let ?P = "th_prop th0"
  from ok obtain U' f' g' P where ad': "okT (abstract_rule_data b hs (CTerm x T m) th0) (U', f', g')"
    and mk: "ok (mk_equals (f', g')) P" and th: "th = mk_rep (maxidx_typ T (th_maxidx th0)) (th_tpairs th0) P"
    by (auto simp: abstract_rule_def)
  have same: "U' = U" "f' = f" "g' = g" using ad ad' by (auto)
  obtain t u a z where d: "dest_eq_fun ?P = Some (U, t, u)"
    and f: "f = Abs b T (abstract_over x t)" and g: "g = Abs b T (abstract_over x u)"
    and xc: "(x = Free a T \<and> \<not> occs_hyps x hs (th_tpairs th0)) \<or> (x = Var z T \<and> \<not> occs_hyps x [] (th_tpairs th0))"
    by (rule abstract_rule_data_ok[OF ad tx])
  have x: "x = Free a T \<or> x = Var z T" using xc by (blast)
  note d' = dest_eq_any_dest_eq_fun[OF d]
  obtain A where P0: "?P = eq_const A $ t $ u" and c: "closed t" "closed u"
    and ty: "\<And>e. e \<turnstile> t : A" "\<And>e. e \<turnstile> u : A"
    using dest_eq_any_wtp[OF eq d' w] by (blast)
  have tQ: "e\<langle>0:T\<rangle> \<turnstile> abstract_over x s : A" if "closed s" "\<And>e. e \<turnstile> s : A" for s e
    unfolding abstract_over_def
    by (rule typing_abstract_over_aux[OF x that(2)]) (use that(1) in \<open>simp_all add: closed_def\<close>)
  have cT: "cert_typ alg ar T" using tx[of "\<lambda>_. propT"] x by (auto)
  have tf: "e \<turnstile> f : T \<rightarrow>\<^sub>T A" "e \<turnstile> g : T \<rightarrow>\<^sub>T A" for e
    using tQ[OF c(1) ty(1)] tQ[OF c(2) ty(2)] cT by (auto simp: f g)
  show cf: "closed f" "closed g"
    using loose_bvar_abstract_over_aux[OF loose_bvar_mono[of t 0 1], of 0 x]
      loose_bvar_abstract_over_aux[OF loose_bvar_mono[of u 0 1], of 0 x] c
    by (simp_all add: f g closed_def abstract_over_def)
  have P: "P = eq_const (T \<rightarrow>\<^sub>T A) $ f $ g" by (rule mk_equals_ok[OF mk[unfolded same] cf(1) tf(1)])
  have "wtp (eq_const (T \<rightarrow>\<^sub>T A) $ f $ g)"
  proof (rule wtpI)
    show "closed (eq_const (T \<rightarrow>\<^sub>T A) $ f $ g)" using cf by (simp add: closed_def)
    from eq obtain v S where cc: "ctab STR ''Pure.eq'' = Some (TVar v S \<rightarrow>\<^sub>T TVar v S \<rightarrow>\<^sub>T propT)"
      by (auto simp: eq_ok_def)
    have ct: "const_typ_ok ctab STR ''Pure.eq'' ((T \<rightarrow>\<^sub>T A) \<rightarrow>\<^sub>T (T \<rightarrow>\<^sub>T A) \<rightarrow>\<^sub>T propT)"
      unfolding const_typ_ok_def using cc by (auto intro!: exI[of _ "\<lambda>_ _. T \<rightarrow>\<^sub>T A"] simp: propT_def)
    have cA: "cert_typ alg ar (T \<rightarrow>\<^sub>T A)" by (rule typing_cert_closed[OF tf(1) cf(1)])
    have cP: "cert_typ alg ar propT" using typing_cert_closed[OF wtpD(2)[OF w] wtpD(1)[OF w]] .
    have tc: "(\<lambda>_. propT) \<turnstile> eq_const (T \<rightarrow>\<^sub>T A) : (T \<rightarrow>\<^sub>T A) \<rightarrow>\<^sub>T (T \<rightarrow>\<^sub>T A) \<rightarrow>\<^sub>T propT"
      using ct cA cP by (intro typing.Const) (simp_all add: cert_typ_fun)
    show "(\<lambda>_. propT) \<turnstile> eq_const (T \<rightarrow>\<^sub>T A) $ f $ g : propT"
      by (rule typing.App[OF typing.App[OF tc tf(1)] tf(2)])
  qed
  then show "wtp (th_prop th)" by (simp add: th P mk_rep_def)
  show "th_maxidx th = maxidx_typ T (th_maxidx th0)" "th_tpairs th = th_tpairs th0" by (simp_all add: th mk_rep_def)
  have tA: "tvars A \<subseteq> ttvars t" by (rule typing_tvars_closed[OF ty(1) c(1)])
  note at = abstract_over_aux_sub[of x 0 t] and au = abstract_over_aux_sub[of x 0 u]
  show vf: "vars f \<subseteq> vars ?P" "vars g \<subseteq> vars ?P"
    using at au by (auto simp: P0 f g abstract_over_def)
  show tvf: "ttvars f \<subseteq> ttvars ?P \<union> tvars T" "ttvars g \<subseteq> ttvars ?P \<union> tvars T"
    using at au by (auto simp: P0 f g abstract_over_def ttvars_def)
  show "vars (th_prop th) \<subseteq> vars ?P" using vf by (simp add: th P mk_rep_def)
  show "ttvars (th_prop th) \<subseteq> ttvars ?P \<union> tvars T"
    using tvf tA by (auto simp: th P P0 mk_rep_def ttvars_def propT_def)
qed

end

definition abstract_rule_thm :: "name \<Rightarrow> pure_cterm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "abstract_rule_thm b ct th =
    (if csign_of ct = sign_of th \<and> sign_eq (sign_of th) \<and> sign_closed (sign_of th) then
      map_option (\<lambda>(r, U, f, g). Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)))
          (bindM (zproof_of th) (zabstract_rule_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct)) U b
            (ct_t (crep_of ct)) f g)))))
        (resT (abstract_rule_res b (hyps_of th) (crep_of ct) (rep_of th)))
     else None)"

lemma thm_ok_abstract_rule:
  fixes th :: "'u pure_thm"
  assumes res: "okT (abstract_rule_res b (hyps_of th) (crep_of ct) (rep_of th)) (r, U, f, g)"
    and c: "csign_of ct = sign_of th" and se: "sign_eq (sign_of th)" and sc: "sign_closed (sign_of th)"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zabstract_rule_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct)) U b
      (ct_t (crep_of ct)) f g)))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  obtain x T m where cr: "crep_of ct = CTerm x T m" by (cases "crep_of ct")
  have ok': "okT (abstract_rule b (hyps_of th) (CTerm x T m) (rep_of th)) r"
    and ad: "okT (abstract_rule_data b (hyps_of th) (CTerm x T m) (rep_of th)) (U, f, g)"
    using abstract_rule_res_ok[OF res] by (simp_all add: cr)
  have eq: "pure_sig.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  have wfc: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm x T m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
    using pure_cterm_wf[of ct] ps c by (simp add: cr)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps])
    have tx: "\<And>e. e \<turnstile> x : T" and cx: "closed x" using wf by (simp_all add: cterm_wf_def)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    note sh = abstract_rule_shape[OF ok' ad eq w tx cx]
    have tT: "tvars T \<subseteq> ttvars x" by (rule typing_tvars_closed[OF tx cx])
    have m0: "th_maxidx (rep_of th) \<le> maxidx_typ T (th_maxidx (rep_of th))" by (rule maxidx_typ_ge)
    have "thm_wf (max (maxidx_typ T (th_maxidx (rep_of th))) (th_maxidx (rep_of th))) (hyps_of th)
        (th_tpairs (rep_of th)) (th_prop r)"
    proof (rule thm_wf_extend[OF w0 sh(1), where V = "{}" and TV = "tvars T"])
      show "vars (th_prop r) \<subseteq> vars (th_prop (rep_of th)) \<union> {}" using sh(4) by simp
      show "ttvars (th_prop r) \<subseteq> ttvars (th_prop (rep_of th)) \<union> tvars T" by (rule sh(5))
      show "\<forall>v\<in>tvars T. 0 \<le> snd (fst v) \<and> snd (fst v) \<le> maxidx_typ T (th_maxidx (rep_of th))"
        using wf tT maxidx_typ_tvars by (fastforce simp: cterm_wf_def)
    qed simp
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using m0 sh(2,3) by (simp add: max_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps'])
    have tx: "\<And>e. e \<turnstile> x : T" using wf by (simp add: cterm_wf_def)
    have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by (simp add: thm_wf_def)
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid_in[of th M] M by simp
    have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      by (rule valid_mono[OF v]) simp
    then have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule abstract_rule_valid[OF ok' _ wt eq tx])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
      using se by (simp add: sign_eq_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps])
    have tx: "\<And>e. e \<turnstile> x : T" and cx: "closed x" using wf by (simp_all add: cterm_wf_def)
    have px: "pnn x" using wf by (simp add: cterm_wf_def pnn_iff)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using w0 by (simp add: thm_wf_def)
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    note sh = abstract_rule_shape[OF ok' ad eq w tx cx]
    have tT: "tvars T \<subseteq> ttvars x" by (rule typing_tvars_closed[OF tx cx])
    have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
    have tnT: "tnn T" using tT px unfolding tnn_def pnn_iff by (force)
    have pf: "pnn f" "pnn g" using sh(6-9) pP tT px unfolding pnn_iff by (blast)+
    have scl: "fnames (sg_close ?c A) = {}" "TFree b' S \<notin> tatoms (sg_close ?c A)" for A b' S
      using sc by (simp_all add: sign_closed_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = abstract_rule_proof b x q"
        by (auto simp: bindP_eq_returnP cr)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        unfolding pf by (rule abstract_rule_proof_valid[OF ok' vq(1) wt tx]) (simp add: scl)
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using prf_idx_prf_abstract_over_aux[OF vq(2)] prf_nolb_prf_abstract_over_aux[OF vq(3), of 0]
        by (simp_all add: pf abstract_rule_proof_def forall_intr_proof_def prf_abstract_over_def equality_axm_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zabstract_rule_proof ztargs (ct_T (crep_of ct)) U b (ct_t (crep_of ct)) f g)
          = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zabstract_rule_proof ztargs T U b x f g q = return z"
        by (auto simp: bindZ_eq_returnZ cr)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
      have cz: "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) q"
      proof (rule zprf_all_mono[of zterm_ok ztyp_ok])
        show "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp add: zinv_def)
        fix t assume "zterm_ok t"
        then show "\<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T"
          using zterm_ok_zvars by (fastforce simp: ztyp_ok_def zcanon_def)
      qed simp
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zabstract_rule_proof_valid(1)[OF ok' vq(1) wt tx ad pnn_noneg[OF px] pnn_noneg[OF pf(1)]
          pnn_noneg[OF pf(2)] zc cz _ z]) (use sc in \<open>simp add: zeq_close_ok_def sign_closed_def\<close>)
      moreover from z obtain f' g' ax0 zx where f': "zterm_of ztargs f = return f'" and g': "zterm_of ztargs g = return g'"
        and ax0: "zaxiom_proof STR ''abstract_rule'' [(tvar_a, ztyp_of T), (tvar_b, ztyp_of U)]
          [(STR ''f'', f'), (STR ''g'', g')] = return ax0"
        and zx: "zterm_of ztargs x = return zx" and zq: "z = ZAppp ax0 (ZAbst b (ztyp_of T) (zabstract_proof zx 0 q))"
        by (auto simp: zabstract_rule_proof_def zforall_intr_proof_def bindZ_eq_returnZ)
      have "zinv ax0 \<and> znolb 0 ax0 \<and> zhyps ax0 = {}"
        by (rule zaxiom_proof_ok[OF ax0])
          (use zterm_ok_zterm_of_pnn[OF f' pf(1)] zterm_ok_zterm_of_pnn[OF g' pf(2)]
            zloose_zterm_of[OF f'] zloose_zterm_of[OF g'] sh(10,11) in \<open>auto simp: zeq_vars_def closed_def\<close>)
      moreover have "zinv (ZAbst b (ztyp_of T) (zabstract_proof zx 0 q))"
        using zinv_zabstract_proof[OF vq(2)] ztyp_ok_ztyp_of[OF tnT] by simp
      moreover have "znolb 0 (ZAbst b (ztyp_of T) (zabstract_proof zx 0 q))"
        using znolb_zabstract_proof[OF vq(3), of 0] by simp
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def)
    qed
  qed
qed

theorem abstract_rule_thm:
  assumes "abstract_rule_thm b ct th = Some th'"
  obtains r U f g where "okT (abstract_rule_res b (hyps_of th) (crep_of ct) (rep_of th)) (r, U, f, g)"
    "csign_of ct = sign_of th" "sign_eq (sign_of th)" "sign_closed (sign_of th)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)))
      (bindM (zproof_of th) (zabstract_rule_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct)) U b
        (ct_t (crep_of ct)) f g)))"
proof -
  from assms obtain r U f g where c: "csign_of ct = sign_of th" and se: "sign_eq (sign_of th)"
    and sc: "sign_closed (sign_of th)"
    and res: "okT (abstract_rule_res b (hyps_of th) (crep_of ct) (rep_of th)) (r, U, f, g)"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)))
      (bindM (zproof_of th) (zabstract_rule_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct)) U b
        (ct_t (crep_of ct)) f g))))"
    by (auto simp: abstract_rule_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF res c se sc]) (use thm_ok_abstract_rule[OF res c se sc] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed

subsection \<open>Generalization\<close>

lemma tvars_generalizeT: "(v, S) \<in> tvars (generalizeT tfrees gi T) \<Longrightarrow> (v, S) \<in> tvars T \<or> snd v = gi"
  by (induction tfrees gi T rule: generalizeT.induct) (auto split: if_splits)

lemma vars_generalize_term:
  "(v, U) \<in> vars (generalize_term tfrees frees gi t) \<Longrightarrow> (\<exists>U'. (v, U') \<in> vars t) \<or> gi \<le> snd v"
  by (induction tfrees frees gi t rule: generalize_term.induct) (auto split: if_splits simp: clean_index_ge)

lemma ttvars_generalize_term:
  "(v, S) \<in> ttvars (generalize_term tfrees frees gi t) \<Longrightarrow> (v, S) \<in> ttvars t \<or> snd v = gi"
  by (induction tfrees frees gi t rule: generalize_term.induct)
    (auto split: if_splits dest: tvars_generalizeT simp: ttvars_def)

lemma loose_bvar_generalize_term': "loose_bvar (generalize_term tfrees frees i t) k \<longleftrightarrow> loose_bvar t k"
  by (induction tfrees frees i t arbitrary: k rule: generalize_term.induct) auto

lemma prf_nolb_prf_abstract_over_free:
  "prf_nolb 0 p \<Longrightarrow> prf_nolb 0 (forall_intr_proof x (Free x T) p)"
  using prf_nolb_prf_abstract_over_aux[of 0 p 0] by (simp add: forall_intr_proof_def prf_abstract_over_def)

context pure_sig
begin

lemma typing_generalize_term': "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> generalize_term [] frees i t : T"
  by (induction rule: typing.induct) auto

lemma typing_generalize_term_gen:
  assumes "e \<turnstile> t : T"
  shows "(\<lambda>j. map_atyps (gen_atom (tf_set tfrees) (\<lambda>a S. (a, i))) (e j)) \<turnstile> generalize_term tfrees frees i t :
    map_atyps (gen_atom (tf_set tfrees) (\<lambda>a S. (a, i))) T"
  unfolding generalize_term_split[of tfrees]
  by (rule typing_generalize_term'[OF typing_tmap[OF assms tmap_ok_gen_atom]])

lemma wtp_generalize_term: "wtp t \<Longrightarrow> wtp (generalize_term tfrees frees i t)"
  unfolding generalize_term_split[of tfrees]
  using wtp_tmap[OF _ tmap_ok_gen_atom, of t] typing_generalize_term'
  by (auto simp: wtp_def closed_def)

lemma thm_wf_generalize:
  assumes ok: "okT (generalize tfrees frees gi hs th0) th"
    and w: "thm_wf (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)"
  shows "thm_wf (th_maxidx th) hs (th_tpairs th) (th_prop th)"
proof (cases "tfrees = [] \<and> frees = []")
  case True
  with ok w show ?thesis by (auto simp: generalize_def returnW_def)
next
  case False
  let ?gen = "generalize_term tfrees frees gi"
  let ?P = "?gen (th_prop th0)" and ?tps = "map (\<lambda>(t, u). (?gen t, ?gen u)) (th_tpairs th0)"
  from ok False have gi: "th_maxidx th0 < gi"
    and th: "th = mk_rep (maxidx_tpairs ?tps (maxidx_of_term ?P)) ?tps ?P"
    by (auto simp: generalize_def returnW_def raiseW_def Let_def split: if_splits)
  from w have wP: "wtp (th_prop th0)" and h: "\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tp: "\<forall>(t, u)\<in>set (th_tpairs th0). closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and m: "-1 \<le> th_maxidx th0" and vn: "\<forall>v\<in>vars_thm (th_tpairs th0) (th_prop th0). 0 \<le> snd (fst v)"
    and tn: "\<forall>v\<in>tvars_thm (th_tpairs th0) (th_prop th0). 0 \<le> snd (fst v)"
    unfolding thm_wf_def wt_thm_def by (blast+)
  have gi0: "0 \<le> gi" using gi m by (simp add: integer_arith)
  let ?k = "maxidx_tpairs ?tps (maxidx_of_term ?P)"
  have ibP: "ibelow ?k ?P"
    by (rule ibelow_mono[OF maxidx_of_term_ibelow maxidx_tpairs_ge])
  have tp0: "closed (?gen t) \<and> closed (?gen u) \<and> ibelow ?k (?gen t) \<and> ibelow ?k (?gen u) \<and>
      (\<exists>T. \<forall>e. e \<turnstile> ?gen t : T \<and> e \<turnstile> ?gen u : T)" if tu: "(t, u) \<in> set (th_tpairs th0)" for t u
  proof -
    from tp tu obtain T where c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by (blast)
    have "(?gen t, ?gen u) \<in> set ?tps" using tu by (force)
    from maxidx_tpairs_mem[OF this, of "maxidx_of_term ?P"]
    have "ibelow ?k (?gen t) \<and> ibelow ?k (?gen u)" .
    moreover have "closed (?gen t)" "closed (?gen u)" using c by (simp_all add: closed_def loose_bvar_generalize_term')
    moreover have "\<forall>e. e \<turnstile> ?gen t : map_atyps (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))) T \<and>
        e \<turnstile> ?gen u : map_atyps (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))) T"
    proof
      fix e
      let ?\<phi> = "gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))"
      have "(\<lambda>j. map_atyps ?\<phi> ((\<lambda>_. propT) j)) \<turnstile> ?gen t : map_atyps ?\<phi> T"
        "(\<lambda>j. map_atyps ?\<phi> ((\<lambda>_. propT) j)) \<turnstile> ?gen u : map_atyps ?\<phi> T"
        by (rule typing_generalize_term_gen[OF ty(1)], rule typing_generalize_term_gen[OF ty(2)])
      then show "e \<turnstile> ?gen t : map_atyps ?\<phi> T \<and> e \<turnstile> ?gen u : map_atyps ?\<phi> T"
        using typing_closed \<open>closed (?gen t)\<close> \<open>closed (?gen u)\<close> by (blast)
    qed
    ultimately show ?thesis by (blast)
  qed
  have tp': "\<forall>(t, u)\<in>set ?tps. closed t \<and> closed u \<and> ibelow ?k t \<and> ibelow ?k u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    using tp0 by (fastforce)
  have mk: "-1 \<le> ?k"
    using maxidx_tpairs_ge[of "maxidx_of_term ?P" ?tps] maxidx_term_ge[of "-1" ?P] by (simp add: maxidx_of_term_def)
  have vn': "\<forall>v\<in>vars_thm ?tps ?P. 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> vars_thm ?tps ?P"
    then obtain x where x: "v \<in> vars (?gen x)" "vars x \<subseteq> vars_thm (th_tpairs th0) (th_prop th0)"
      unfolding vars_thm_def by (force)
    obtain y U where v: "v = (y, U)" by (cases v)
    from vars_generalize_term[of y U tfrees frees gi x] x(1) v
    have "(\<exists>U'. (y, U') \<in> vars x) \<or> gi \<le> snd y" by simp
    then show "0 \<le> snd (fst v)" using x(2) vn gi0 v by (force)
  qed
  have tn': "\<forall>v\<in>tvars_thm ?tps ?P. 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> tvars_thm ?tps ?P"
    then obtain x where x: "v \<in> ttvars (?gen x)" "ttvars x \<subseteq> tvars_thm (th_tpairs th0) (th_prop th0)"
      unfolding tvars_thm_def by (force)
    obtain y S where v: "v = (y, S)" by (cases v)
    from ttvars_generalize_term[of y S tfrees frees gi x] x(1) v
    have "(y, S) \<in> ttvars x \<or> snd y = gi" by simp
    then show "0 \<le> snd (fst v)" using x(2) tn gi0 v by (force)
  qed
  show ?thesis unfolding th thm_wf_def wt_thm_def
    using wtp_generalize_term[OF wP] ibP h tp' mk vn' tn' by (simp add: mk_rep_def)
qed

end

definition generalize_thm :: "name list \<Rightarrow> name list \<Rightarrow> integer \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "generalize_thm tfrees frees gi th =
    (if tfrees = [] \<and> frees = [] then Some th
     else if sign_closed (sign_of th) then
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th))
            (th_prop (rep_of th)) p)))
          (bindM (zproof_of th) (zgeneralize_proof tfrees frees gi)))))
        (resT (generalize tfrees frees gi (hyps_of th) (rep_of th)))
     else None)"

lemma vars_prf_generalize:
  assumes "\<forall>t\<in>prf_terms p. \<forall>v\<in>vars t. 0 \<le> snd (fst v)" "0 \<le> gi"
  shows "\<forall>t\<in>prf_terms (map_proof_terms (generalize_term tf fr gi) g p). \<forall>v\<in>vars t. 0 \<le> snd (fst v)"
proof (intro ballI)
  fix t v assume "t \<in> prf_terms (map_proof_terms (generalize_term tf fr gi) g p)" "v \<in> vars t"
  then obtain s where s: "s \<in> prf_terms p" "v \<in> vars (generalize_term tf fr gi s)"
    by (auto simp: prf_terms_map_proof_terms)
  obtain y U where v: "v = (y, U)" by (cases v)
  from vars_generalize_term[of y U tf fr gi s] s(2) v
  have "(\<exists>U'. (y, U') \<in> vars s) \<or> gi \<le> snd y" by simp
  then show "0 \<le> snd (fst v)" using assms s(1) v by (force)
qed

lemma prf_terms_forall_intr_proof:
  "t \<in> prf_terms (forall_intr_proof a x p) \<Longrightarrow> \<exists>s\<in>prf_terms p. \<exists>l. t = abstract_over_aux x l s"
  using prf_terms_prf_abstract_over_aux by (simp add: forall_intr_proof_def prf_abstract_over_def)

lemma prf_idx_generalize_thm_proof:
  assumes p: "prf_idx (\<lambda>i. 0 \<le> i) pf" and gi: "0 \<le> gi"
  shows "prf_idx (\<lambda>i. 0 \<le> i) (generalize_thm_proof tfrees frees gi tps P pf)"
proof -
  let ?P = "\<lambda>p. \<forall>t\<in>prf_terms p. \<forall>v\<in>vars t. 0 \<le> snd (fst v)"
  have p1: "?P (map_proof_terms (generalize_term tfrees [] gi) (generalizeT tfrees gi) pf)"
    by (rule vars_prf_generalize[OF p[unfolded prf_idx_def] gi])
  have fi: "?P (forall_intr_proof a x q)" if "?P q" for a x q
    using that abstract_over_aux_sub by (fastforce dest: prf_terms_forall_intr_proof)
  have p2: "?P (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) xs q)" if "?P q" for xs q
    using that
  proof (induction xs arbitrary: q)
    case (Cons x xs)
    obtain a T where x: "x = (a, T)" by (cases x)
    show ?case using Cons.IH[OF fi[OF Cons.prems]] by (simp add: x)
  qed simp
  have p3: "?P (foldr (\<lambda>(x, T) p. PAppt p (Some (Var (clean_index (x, gi)) T))) xs q)" if "?P q" for xs q
    using that
  proof (induction xs)
    case (Cons x xs)
    obtain a T where x: "x = (a, T)" by (cases x)
    have "0 \<le> snd (clean_index (a, gi))" using clean_index_ge[of gi a] gi by simp
    with Cons show ?case by (simp add: x)
  qed simp
  have g: "?P (generalize_proof tfrees fr gi P pf)" for fr
    unfolding generalize_proof_def Let_def by (rule p3, rule p2, rule p1)
  show ?thesis
    unfolding generalize_thm_proof_def Let_def prf_idx_def
    using g vars_prf_generalize[OF g gi] by simp
qed

lemma prf_nolb_generalize_thm_proof:
  assumes p: "prf_nolb 0 pf"
  shows "prf_nolb 0 (generalize_thm_proof tfrees frees gi tps P pf)"
proof -
  have p1: "prf_nolb 0 (map_proof_terms (generalize_term tf fr gi) g q)" if "prf_nolb 0 q" for tf fr g q
    by (rule prf_nolb_map[OF _ _ that]) (simp_all add: loose_bvar_generalize_term')
  have p2: "prf_nolb 0 (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) xs q)" if "prf_nolb 0 q" for xs q
    using that
  proof (induction xs arbitrary: q)
    case (Cons x xs)
    obtain a T where x: "x = (a, T)" by (cases x)
    show ?case using Cons.IH[OF prf_nolb_prf_abstract_over_free[OF Cons.prems]] by (simp add: x)
  qed simp
  have p3: "prf_nolb 0 (foldr (\<lambda>(x, T) p. PAppt p (Some (Var (clean_index (x, gi)) T))) xs q)" if "prf_nolb 0 q" for xs q
    using that
  proof (induction xs)
    case (Cons x xs)
    then show ?case by (cases x) simp
  qed simp
  have g: "prf_nolb 0 (generalize_proof tfrees fr gi P pf)" for fr
    unfolding generalize_proof_def Let_def by (rule p3, rule p2, rule p1[OF p])
  show ?thesis unfolding generalize_thm_proof_def Let_def using g p1[OF g] by simp
qed

lemma zinv_zgeneralize_proof:
  assumes z: "zgeneralize_proof tfrees frees gi p = return q" and p: "zinv p" and gi: "0 \<le> gi"
  shows "zinv q" "znolb 0 p \<Longrightarrow> znolb 0 q" "zhyps q = zhyps p"
proof -
  define tf :: "indexname \<times> psort \<Rightarrow> ztyp option"
    where "tf = (\<lambda>((a, i), S). if i = -1 \<and> a \<in> set tfrees then Some (ZTVar (a, gi) S) else None)"
  define var :: "indexname \<times> ztyp \<Rightarrow> zterm option"
    where "var = (\<lambda>((x, i), T). if i = -1 \<and> x \<in> set frees then Some (ZVar (clean_index (x, gi)) T) else None)"
  have m: "map_zproof (zsubst_type tf) (\<lambda>t. return (zsubst_term (zsubst_type tf) var t)) p = return q"
    using z by (simp add: zgeneralize_proof_def Let_def tf_def var_def)
  have tf: "ztyp_ok U" if "tf (v, S) = Some U" for v S U
    using that gi by (cases v) (auto simp: tf_def split: if_splits)
  have tok: "ztyp_ok (zsubst_type tf T)" if "ztyp_ok T" for T
    by (rule ztyp_ok_zsubst_type[OF that tf])
  have vok: "zterm_ok u" if "var (x, T) = Some u" "ztyp_ok T" for x T u
  proof -
    obtain a i where x: "x = (a, i)" by (cases x)
    show ?thesis using that gi clean_index_ge[of gi a] by (auto simp: var_def x split: if_splits)
  qed
  have vcl: "\<not> zloose u 0" if "var v = Some u" for v u
    using that by (auto simp: var_def split: if_splits prod.splits)
  show "zinv q"
    by (rule zinv_map_zproof[OF m p tok]) (use tok vok in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
  have zc: "zconsts_ok p" using p by (simp add: zinv_def)
  have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term (zsubst_type tf) var t) k"
    using zloose_zsubst_term vcl by blast
  show "znolb 0 p \<Longrightarrow> znolb 0 q" by (rule znolb_map_zproof[OF m zc]) (use zl in auto)
  show "zhyps q = zhyps p" by (rule zhyps_map_zproof[OF m])
qed

lemma thm_ok_generalize:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (generalize tfrees frees gi (hyps_of th) (rep_of th)) r" and sc: "sign_closed (sign_of th)"
    and ne: "\<not> (tfrees = [] \<and> frees = [])"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th)) (th_prop (rep_of th)) p)))
    (bindM (zproof_of th) (zgeneralize_proof tfrees frees gi)))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  from ok ne have gi: "th_maxidx (rep_of th) < gi"
    by (auto simp: generalize_def returnW_def raiseW_def Let_def split: if_splits)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using thm_wf_generalize[OF ok w0] by simp
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by (simp add: thm_wf_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule generalize_tfrees_valid[OF ok _ wt]) (use pure_thm_valid_in[of th M] M in simp)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      and mx: "-1 \<le> th_maxidx (rep_of th)"
      using w0 by (simp_all add: thm_wf_def)
    have gi0: "0 \<le> gi" using gi mx by (simp add: integer_arith)
    have scl: "fnames (sg_close ?c A) = {}" "TFree b S \<notin> tatoms (sg_close ?c A)" for A b S
      using sc by (simp_all add: sign_closed_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th))
          (th_prop (rep_of th)) p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q"
        and pf: "pf = generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th)) (th_prop (rep_of th)) q"
        by (auto simp: bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        unfolding pf by (rule generalize_tfrees_proof_valid[OF ok vq(1) wt _ _ vq(3)])
          (simp_all add: scl tf_in_def)
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" unfolding pf by (rule prf_idx_generalize_thm_proof[OF vq(2) gi0])
      moreover have "prf_nolb 0 pf" unfolding pf by (rule prf_nolb_generalize_thm_proof[OF vq(3)])
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zgeneralize_proof tfrees frees gi) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zgeneralize_proof tfrees frees gi q = return z"
        by (auto simp: bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
      have eqc: "zeq_close_ok" using scl by (simp add: zeq_close_ok_def)
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zgeneralize_proof_valid[OF ok vq(1) wt mx prf_nolb_zprf_tr[OF vq(3)] zc eqc z])
      moreover note zg = zinv_zgeneralize_proof[OF z vq(2) gi0]
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" using vq(3,4) by (simp add: zhyps_ok_def)
    qed
  qed
qed

theorem generalize_thm:
  assumes "generalize_thm tfrees frees gi th = Some th'" and "\<not> (tfrees = [] \<and> frees = [])"
  obtains r where "okT (generalize tfrees frees gi (hyps_of th) (rep_of th)) r" "sign_closed (sign_of th)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th))
        (th_prop (rep_of th)) p)))
      (bindM (zproof_of th) (zgeneralize_proof tfrees frees gi)))"
proof -
  from assms obtain r where sc: "sign_closed (sign_of th)"
    and ok: "okT (generalize tfrees frees gi (hyps_of th) (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th))
        (th_prop (rep_of th)) p)))
      (bindM (zproof_of th) (zgeneralize_proof tfrees frees gi))))"
    by (auto simp: generalize_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok sc]) (use thm_ok_generalize[OF ok sc assms(2)] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed


subsection \<open>Type variables: varification and freezing\<close>

lemma typs_list_implies_sub: "A \<in> set As \<Longrightarrow> typs A \<subseteq> typs (list_implies As B)" "typs B \<subseteq> typs (list_implies As B)"
  by (induction As) (auto simp: implies_def)

context pure_sig
begin

lemma vars_typs_sub_ibelow:
  "ibelow m t \<Longrightarrow> vars s \<subseteq> vars t \<Longrightarrow> typs s \<subseteq> typs t \<Longrightarrow> ibelow m s"
  unfolding ibelow_def ttvars_def by (blast)

end

lemma tmap_sub:
  assumes "vars s \<subseteq> vars t" "typs s \<subseteq> typs t"
  shows "vars (tmap \<phi> s) \<subseteq> vars (tmap \<phi> t)" "typs (tmap \<phi> s) \<subseteq> typs (tmap \<phi> t)"
  using assms by (auto simp: vars_map_types typs_map_types)

definition resM :: "'a M \<Rightarrow> 'a option" where
  "resM m = (case m of Some (Ok x) \<Rightarrow> Some x | _ \<Rightarrow> None)"

lemma resM_Some: "resM m = Some x \<longleftrightarrow> ok m x"
  by (auto simp: resM_def split: option.splits xres.splits)

lemma full_prop_of_sub:
  assumes f: "ok (full_prop_of tps P) P1" and X: "X \<in> insert P (fst ` set tps \<union> snd ` set tps)"
  shows "vars X \<subseteq> vars P1" "typs X \<subseteq> typs P1"
proof -
  obtain eqs where eqs: "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) tps eqs"
    and P1: "P1 = list_implies eqs P"
    by (rule ok_full_prop_of[OF f])
  have "\<exists>q\<in>set eqs. vars X \<subseteq> vars q \<and> typs X \<subseteq> typs q" if "X \<in> fst ` set tps \<union> snd ` set tps"
  proof -
    from that obtain t u where tu: "(t, u) \<in> set tps" "X = t \<or> X = u" by (force)
    then obtain i where i: "i < length tps" "tps ! i = (t, u)" by (auto simp: in_set_conv_nth)
    have il: "i < length eqs" using i(1) list_all2_lengthD[OF eqs] by simp
    from list_all2_nthD[OF eqs i(1)] i(2) obtain T where "eqs ! i = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u"
      by (auto)
    then show ?thesis using nth_mem[OF il] tu(2) by (intro bexI[of _ "eqs ! i"]) auto
  qed
  with X have "X = P \<or> (\<exists>q\<in>set eqs. vars X \<subseteq> vars q \<and> typs X \<subseteq> typs q)" by blast
  then have "vars X \<subseteq> vars P1 \<and> typs X \<subseteq> typs P1"
  proof (elim disjE bexE conjE)
    assume "X = P"
    then show ?thesis using typs_list_implies_sub(2)[of P eqs] by (auto simp: P1 vars_list_implies)
  next
    fix q assume q: "q \<in> set eqs" "vars X \<subseteq> vars q" "typs X \<subseteq> typs q"
    then show ?thesis using typs_list_implies_sub(1)[OF q(1), of P] by (auto simp: P1 vars_list_implies)
  qed
  then show "vars X \<subseteq> vars P1" "typs X \<subseteq> typs P1" by simp_all
qed

lemma (in pure_sig) full_prop_of_vars:
  assumes f: "ok (full_prop_of tps P) P1"
  shows "vars P1 \<subseteq> vars_thm tps P \<and> ttvars P1 \<subseteq> tvars_thm tps P"
proof -
  from f obtain eqs where m: "ok (mapM mk_equals tps) eqs" and P1: "P1 = list_implies eqs P"
    by (auto simp: full_prop_of_def)
  have l: "list_all2 (\<lambda>x y. ok (mk_equals x) y) tps eqs" using m by (simp add: ok_mapM)
  have q: "vars q \<subseteq> vars_thm tps P \<and> ttvars q \<subseteq> tvars_thm tps P" if "q \<in> set eqs" for q
  proof -
    from that obtain i where i: "i < length eqs" "q = eqs ! i" by (auto simp: in_set_conv_nth)
    have il: "i < length tps" using i(1) list_all2_lengthD[OF l] by simp
    obtain t u where tu: "tps ! i = (t, u)" by (cases "tps ! i")
    have "ok (mk_equals (t, u)) q" using list_all2_nthD[OF l il] tu i(2) by simp
    then obtain T where T: "ok (fastype_of t) T" and q: "q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u"
      by (auto simp: mk_equals_def)
    have tT: "tvars T \<subseteq> ttvars t" using fastype_of_term_tvars[of "[]" t T] T by (simp add: fastype_of_def)
    have mem: "(t, u) \<in> set tps" using tu nth_mem[OF il] by simp
    show ?thesis using tT mem by (auto simp: q vars_thm_def tvars_thm_def ttvars_def propT_def)
  qed
  then show ?thesis
    by (auto simp: P1 vars_list_implies ttvars_list_implies_eq vars_thm_def tvars_thm_def)
qed

lemma tvars_varify_tfree:
  assumes "\<And>a S v S'. map_of names (a, S) = Some (v, S') \<Longrightarrow> snd v = 0"
  shows "(w, S) \<in> tvars (map_atyps (varify_tfree names) T) \<Longrightarrow> (w, S) \<in> tvars T \<or> snd w = 0"
  using assms by (induction T) (auto simp: varify_tfree_def split: option.splits)

lemma tvars_freeze_tvar: "(w, S) \<in> tvars (map_atyps (freeze_tvar alist) T) \<Longrightarrow> (w, S) \<in> tvars T"
  by (induction T) (auto simp: freeze_tvar_def split: option.splits)

lemma varify_names_idx:
  assumes "map_of (varify_global_names vl fixed t) (a, S) = Some (v, S')"
  shows "snd v = 0"
proof -
  from map_of_SomeD[OF assms] obtain x y where
    "((a, S), (v, S')) = (case x of (a, S) \<Rightarrow> \<lambda>b. ((a, S), ((b, 0), S))) y"
    by (auto simp: varify_global_names_def Let_def dest!: set_zip_leftD)
  then show ?thesis by (auto split: prod.splits)
qed

lemma varifyT_global_shape:
  assumes ok: "okT (varifyT_global vl fixed hs th0) (names, th)"
  shows "th_tpairs th = map (\<lambda>(t, u). (tmap (varify_tfree names) t, tmap (varify_tfree names) u)) (th_tpairs th0)"
    "th_prop th = tmap (varify_tfree names) (th_prop th0)" "th_maxidx th = max 0 (th_maxidx th0)"
    "\<And>a S v S'. map_of names (a, S) = Some (v, S') \<Longrightarrow> snd v = 0 \<and> S' = S"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0" and ?tf = "fold add_tfrees hs fixed"
  let ?\<phi> = "varify_tfree names"
  from ok obtain P1 ts P3 tps0 where f: "ok (full_prop_of ?tps ?P) P1"
    and nm: "names = varify_global_names vl ?tf P1"
    and sp: "ok (strip_prems (integer_of_nat (length ?tps)) [] (tmap ?\<phi> P1)) (ts, P3)"
    and d: "ok (mapM dest_equals ts) tps0"
    and th: "th_tpairs th = rev tps0" "th_prop th = P3" "th_maxidx th = max 0 (th_maxidx th0)"
    by (auto simp: varifyT_global_def Let_def mk_rep_def split: prod.splits)
  obtain eqs where eqs: "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) ?tps eqs"
    and P1: "P1 = list_implies eqs ?P"
    by (rule ok_full_prop_of[OF f])
  have l: "integer_of_nat (length ?tps) = ilength (map (tmap ?\<phi>) eqs)"
    using list_all2_lengthD[OF eqs] by (simp add: ilength_eq)
  from sp[unfolded P1 tmap_list_implies l strip_prems_list_implies]
  have ts: "ts = rev (map (tmap ?\<phi>) eqs)" and P3: "P3 = tmap ?\<phi> ?P"
    by (simp_all add: return_def)
  have "rev tps0 = map (\<lambda>(t, u). (tmap ?\<phi> t, tmap ?\<phi> u)) ?tps"
    by (rule ok_dest_equals_map_types[OF eqs d ts])
  then show "th_tpairs th = map (\<lambda>(t, u). (tmap ?\<phi> t, tmap ?\<phi> u)) ?tps" by (simp add: th)
  show "th_prop th = tmap ?\<phi> ?P" "th_maxidx th = max 0 (th_maxidx th0)" by (simp_all add: th P3)
  show "\<And>a S v S'. map_of names (a, S) = Some (v, S') \<Longrightarrow> snd v = 0 \<and> S' = S"
    using varify_names_idx map_of_varify_global_names nm by (blast)
qed

lemma legacy_freezeT_shape:
  assumes ok: "okT (legacy_freezeT vl th0) th" and f: "ok (full_prop_of (th_tpairs th0) (th_prop th0)) P1"
  defines "\<phi> \<equiv> freeze_tvar (legacy_freeze_names vl P1)"
  shows "th_tpairs th = map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) (th_tpairs th0)"
    "th_prop th = tmap \<phi> (th_prop th0)" "th_maxidx th = maxidx_of_term (tmap \<phi> P1)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  have id: "(if legacy_freeze_names vl P1 = [] then P1 else tmap \<phi> P1) = tmap \<phi> P1"
  proof -
    have fid: "freeze_tvar [] A = A" for A by (simp add: freeze_tvar_def split: ptyp.splits)
    have "tmap (freeze_tvar []) t = t" for t by (rule map_types_id) (simp add: fid map_atyps_id)
    then show ?thesis by (simp add: \<phi>_def)
  qed
  from ok obtain P1' ts P3 tps0 where f': "ok (full_prop_of ?tps ?P) P1'"
    and sp: "ok (strip_prems (integer_of_nat (length ?tps)) []
      (if legacy_freeze_names vl P1' = [] then P1' else tmap (freeze_tvar (legacy_freeze_names vl P1')) P1'))
      (ts, P3)"
    and d: "ok (mapM dest_equals ts) tps0"
    and th: "th_tpairs th = rev tps0" "th_prop th = P3"
      "th_maxidx th = maxidx_of_term (if legacy_freeze_names vl P1' = [] then P1'
        else tmap (freeze_tvar (legacy_freeze_names vl P1')) P1')"
    by (auto simp: legacy_freezeT_def Let_def mk_rep_def split: prod.splits)
  have P1': "P1' = P1" using f f' by simp
  obtain eqs where eqs: "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) ?tps eqs"
    and P1: "P1 = list_implies eqs ?P"
    by (rule ok_full_prop_of[OF f])
  have l: "integer_of_nat (length ?tps) = ilength (map (tmap \<phi>) eqs)"
    using list_all2_lengthD[OF eqs] by (simp add: ilength_eq)
  from sp[unfolded P1' \<phi>_def[symmetric] id, unfolded P1 tmap_list_implies l strip_prems_list_implies]
  have ts: "ts = rev (map (tmap \<phi>) eqs)" and P3: "P3 = tmap \<phi> ?P"
    by (simp_all add: return_def)
  have "rev tps0 = map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) ?tps"
    by (rule ok_dest_equals_map_types[OF eqs d ts])
  then show "th_tpairs th = map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) ?tps" by (simp add: th)
  show "th_prop th = tmap \<phi> ?P" by (simp add: th P3)
  show "th_maxidx th = maxidx_of_term (tmap \<phi> P1)" using th(3) unfolding P1' \<phi>_def[symmetric] id .
qed

context pure_sig
begin

lemma thm_wf_tmap:
  assumes w: "thm_wf m hs tps P" and \<phi>: "tmap_ok \<phi>" and m': "-1 \<le> m'"
    and ib: "\<And>X. X \<in> insert P (fst ` set tps \<union> snd ` set tps) \<Longrightarrow>
      ibelow m' (tmap \<phi> X) \<and> (\<forall>v\<in>ttvars (tmap \<phi> X). 0 \<le> snd (fst v))"
  shows "thm_wf m' hs (map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) tps) (tmap \<phi> P)"
proof -
  from w have wP: "wtp P" and h: "\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tp: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and vn: "\<forall>v\<in>vars_thm tps P. 0 \<le> snd (fst v)"
    unfolding thm_wf_def wt_thm_def by (blast+)
  have tp0: "closed (tmap \<phi> t) \<and> closed (tmap \<phi> u) \<and> ibelow m' (tmap \<phi> t) \<and> ibelow m' (tmap \<phi> u) \<and>
      (\<exists>T. \<forall>e. e \<turnstile> tmap \<phi> t : T \<and> e \<turnstile> tmap \<phi> u : T)" if tu: "(t, u) \<in> set tps" for t u
  proof -
    from tp tu obtain T where c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by (blast)
    have c': "closed (tmap \<phi> t)" "closed (tmap \<phi> u)" using c by (simp_all add: closed_def)
    have "\<forall>e. e \<turnstile> tmap \<phi> t : map_atyps \<phi> T \<and> e \<turnstile> tmap \<phi> u : map_atyps \<phi> T"
      using typing_tmap[OF ty(1) \<phi>] typing_tmap[OF ty(2) \<phi>] typing_closed c' by (blast)
    moreover have "t \<in> fst ` set tps" "u \<in> snd ` set tps" using tu by force+
    then have "ibelow m' (tmap \<phi> t)" "ibelow m' (tmap \<phi> u)" using ib by blast+
    ultimately show ?thesis using c' by (blast)
  qed
  have tp': "\<forall>(t, u)\<in>set (map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) tps). closed t \<and> closed u \<and> ibelow m' t \<and>
      ibelow m' u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    using tp0 by (fastforce)
  have vn': "\<forall>v\<in>vars_thm (map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) tps) (tmap \<phi> P). 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> vars_thm (map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) tps) (tmap \<phi> P)"
    then have "v \<in> vars (tmap \<phi> P) \<or> (\<exists>(t, u)\<in>set tps. v \<in> vars (tmap \<phi> t) \<or> v \<in> vars (tmap \<phi> u))"
      unfolding vars_thm_def by auto
    then obtain X where "vars X \<subseteq> vars_thm tps P" "v \<in> vars (tmap \<phi> X)" unfolding vars_thm_def by blast
    with vn show "0 \<le> snd (fst v)" by (fastforce simp: vars_map_types)
  qed
  have tn': "\<forall>v\<in>tvars_thm (map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) tps) (tmap \<phi> P). 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> tvars_thm (map (\<lambda>(t, u). (tmap \<phi> t, tmap \<phi> u)) tps) (tmap \<phi> P)"
    then have "v \<in> ttvars (tmap \<phi> P) \<or> (\<exists>(t, u)\<in>set tps. v \<in> ttvars (tmap \<phi> t) \<or> v \<in> ttvars (tmap \<phi> u))"
      unfolding tvars_thm_def by auto
    then show "0 \<le> snd (fst v)"
    proof
      assume "v \<in> ttvars (tmap \<phi> P)"
      with ib[of P] show ?thesis by blast
    next
      assume "\<exists>(t, u)\<in>set tps. v \<in> ttvars (tmap \<phi> t) \<or> v \<in> ttvars (tmap \<phi> u)"
      then obtain t u where tu: "(t, u) \<in> set tps" and v: "v \<in> ttvars (tmap \<phi> t) \<or> v \<in> ttvars (tmap \<phi> u)" by blast
      have "t \<in> fst ` set tps" "u \<in> snd ` set tps" using tu by force+
      with v ib show ?thesis by blast
    qed
  qed
  show ?thesis unfolding thm_wf_def wt_thm_def
    using wtp_tmap[OF wP \<phi>] ib[of P] h tp' m' vn' tn' by simp
qed

lemma tmap_ok_freeze: "tmap_ok (freeze_tvar alist)"
  by (rule tmap_okI) (auto simp: freeze_tvar_def cert_typ_def split: option.splits)

end

definition varifyT_global_thm :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> (name \<times> psort) list \<Rightarrow>
    'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "varifyT_global_thm vl fixed th =
    (if sign_closed (sign_of th) then
      map_option (\<lambda>(names, r). Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names)))))
        (resT (varifyT_global vl fixed (hyps_of th) (rep_of th)))
     else None)"

lemma zinv_map_zsubst_type:
  assumes m: "map_zproof (zsubst_type f) (\<lambda>t. return (zsubst_term (zsubst_type f) (\<lambda>_. None) t)) p = return q"
    and p: "zinv p" and f: "\<And>v S U. f (v, S) = Some U \<Longrightarrow> ztyp_ok U"
  shows "zinv q" "znolb 0 p \<Longrightarrow> znolb 0 q" "zhyps q = zhyps p"
proof -
  have tok: "ztyp_ok (zsubst_type f T)" if "ztyp_ok T" for T by (rule ztyp_ok_zsubst_type[OF that f])
  show "zinv q" by (rule zinv_map_zproof[OF m p tok]) (use tok in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
  have zc: "zconsts_ok p" using p by (simp add: zinv_def)
  have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term (zsubst_type f) (\<lambda>_. None) t) k"
    using zloose_zsubst_term[of _ _ "\<lambda>_. None"] by simp
  show "znolb 0 p \<Longrightarrow> znolb 0 q" by (rule znolb_map_zproof[OF m zc]) (use zl in auto)
  show "zhyps q = zhyps p" by (rule zhyps_map_zproof[OF m])
qed

lemma prf_idx_map_types: "prf_idx P p \<Longrightarrow> prf_idx P (map_proof_terms (map_types f) g p)"
  by (fastforce simp: prf_idx_def prf_terms_map_proof_terms vars_map_types)

lemma prf_nolb_map_types: "prf_nolb 0 p \<Longrightarrow> prf_nolb 0 (map_proof_terms (map_types f) g p)"
  by (rule prf_nolb_map) simp_all

lemma thm_ok_varifyT_global:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (varifyT_global vl fixed (hyps_of th) (rep_of th)) (names, r)" and sc: "sign_closed (sign_of th)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names)))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th" and ?\<phi> = "varify_tfree names"
  note sh = varifyT_global_shape[OF ok]
  have gen: "?\<phi> = gen_atom (varA names) (varg names)" by (rule varify_tfree_gen_atom) (use sh(4) in blast)
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have ib0: "ibelow (th_maxidx (rep_of th)) X" and nn: "\<forall>v\<in>ttvars X. 0 \<le> snd (fst v)"
      if "X \<in> insert (th_prop (rep_of th)) (fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
    proof -
      let ?m = "th_maxidx (rep_of th)" and ?tps = "th_tpairs (rep_of th)" and ?P = "th_prop (rep_of th)"
      from w0 have ibP: "ibelow ?m ?P" and ibT: "\<And>t u. (t, u) \<in> set ?tps \<Longrightarrow> ibelow ?m t \<and> ibelow ?m u"
        and tn: "\<forall>v\<in>tvars_thm ?tps ?P. 0 \<le> snd (fst v)"
        unfolding thm_wf_def wt_thm_def by fast+
      from that have "X = ?P \<or> (\<exists>(t, u)\<in>set ?tps. X = t \<or> X = u)" by force
      then have "ibelow ?m X \<and> ttvars X \<subseteq> tvars_thm ?tps ?P"
      proof
        assume "X = ?P"
        then show ?thesis using ibP by (auto simp: tvars_thm_def)
      next
        assume "\<exists>(t, u)\<in>set ?tps. X = t \<or> X = u"
        then obtain t u where tu: "(t, u) \<in> set ?tps" "X = t \<or> X = u" by blast
        then show ?thesis using ibT[OF tu(1)] by (auto simp: tvars_thm_def)
      qed
      then show "ibelow ?m X" "\<forall>v\<in>ttvars X. 0 \<le> snd (fst v)" using tn by blast+
    qed
    have "thm_wf (max 0 (th_maxidx (rep_of th))) (hyps_of th)
        (map (\<lambda>(t, u). (tmap ?\<phi> t, tmap ?\<phi> u)) (th_tpairs (rep_of th))) (tmap ?\<phi> (th_prop (rep_of th)))"
    proof (rule thm_wf_tmap[OF w0])
      show "tmap_ok ?\<phi>" unfolding gen by (rule tmap_ok_gen_atom)
      fix X assume X: "X \<in> insert (th_prop (rep_of th)) (fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))"
      have tv: "v \<in> ttvars (tmap ?\<phi> X) \<Longrightarrow> v \<in> ttvars X \<or> snd (fst v) = 0" for v
        using tvars_varify_tfree[of names "fst v" "snd v"] sh(4) by (cases v) (fastforce simp: ttvars_def typs_map_types)
      show "ibelow (max 0 (th_maxidx (rep_of th))) (tmap ?\<phi> X) \<and> (\<forall>v\<in>ttvars (tmap ?\<phi> X). 0 \<le> snd (fst v))"
        using ib0[OF X] nn[OF X] tv by (fastforce simp: ibelow_def vars_map_types)
    qed simp
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: sh(1-3))
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by simp
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule varifyT_global_valid[OF ok]) (use pure_thm_valid_in[of th M] M w0 in \<open>auto simp: thm_wf_def wt_thm_def\<close>)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have wP: "wtp (th_prop (rep_of th))" and wh: "\<And>h. h \<in> set (hyps_of th) \<Longrightarrow> wtp h \<and> vars h = {} \<and> ttvars h = {}"
      using w0 by (auto simp: thm_wf_def wt_thm_def)
    have scl: "fnames (sg_close ?c A) = {}" "TFree b S \<notin> tatoms (sg_close ?c A)" for A b S
      using sc by (simp_all add: sign_closed_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = varifyT_proof names q"
        by (auto simp: bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        unfolding pf by (rule varifyT_global_proof_valid[OF ok vq(1) wP wh _ vq(3)]) (use sc in \<open>auto simp: sign_closed_def\<close>)
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using prf_idx_map_types[OF vq(2)] prf_nolb_map_types[OF vq(3)] vq(2,3)
        by (simp_all add: pf varifyT_proof_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zvarifyT_proof names) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zvarifyT_proof names q = return z"
        by (auto simp: bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
      have eqc: "zeq_close_ok" using scl by (simp add: zeq_close_ok_def)
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zvarifyT_global_proof_valid[OF ok vq(1) wP wh prf_nolb_zprf_tr[OF vq(3)] zc eqc z])
      moreover have "zinv z \<and> znolb 0 z \<and> zhyps z = zhyps q"
      proof (cases "names = []")
        case True
        then show ?thesis using z vq(2,3) by (simp add: zvarifyT_proof_def)
      next
        case False
        define fv :: "indexname \<times> psort \<Rightarrow> ztyp option" where "fv = (\<lambda>((a, i), S). if i = -1
          then map_option (\<lambda>(v, S'). ZTVar v S') (map_of names (a, S)) else None)"
        have m: "map_zproof (zsubst_type fv) (\<lambda>t. return (zsubst_term (zsubst_type fv) (\<lambda>_. None) t)) q = return z"
          using z False by (simp add: zvarifyT_proof_def Let_def fv_def)
        have f: "ztyp_ok U" if "fv (v, S) = Some U" for v S U
        proof -
          obtain a i where v: "v = (a, i)" by (cases v)
          from that obtain w S' where "map_of names (a, S) = Some (w, S')" "U = ZTVar w S'"
            by (auto simp: v fv_def split: if_splits)
          with sh(4)[of a S w S'] show ?thesis by simp
        qed
        from zinv_map_zsubst_type[OF m vq(2) f] vq(3) show ?thesis by simp
      qed
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" using vq(4) by (simp add: zhyps_ok_def)
    qed
  qed
qed

theorem varifyT_global_thm:
  assumes "varifyT_global_thm vl fixed th = Some th'"
  obtains names r where "okT (varifyT_global vl fixed (hyps_of th) (rep_of th)) (names, r)" "sign_closed (sign_of th)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names)))"
proof -
  from assms obtain names r where sc: "sign_closed (sign_of th)"
    and ok: "okT (varifyT_global vl fixed (hyps_of th) (rep_of th)) (names, r)"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names))))"
    by (auto simp: varifyT_global_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok sc]) (use thm_ok_varifyT_global[OF ok sc] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed

definition legacy_freezeT_thm :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "legacy_freezeT_thm vl th =
    (case (resM (full_prop_of (th_tpairs (rep_of th)) (th_prop (rep_of th))), resT (legacy_freezeT vl (rep_of th))) of
      (Some P1, Some r) \<Rightarrow> Some (Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
        (bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p))) (bindM (zproof_of th) (zlegacy_freezeT_proof vl P1)))))
    | _ \<Rightarrow> None)"

lemma thm_ok_legacy_freezeT:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (legacy_freezeT vl (rep_of th)) r" and f: "ok (full_prop_of (th_tpairs (rep_of th)) (th_prop (rep_of th))) P1"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p))) (bindM (zproof_of th) (zlegacy_freezeT_proof vl P1)))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th" and ?\<phi> = "freeze_tvar (legacy_freeze_names vl P1)"
  note sh = legacy_freezeT_shape[OF ok f]
  have sub: "vars X \<subseteq> vars P1" "typs X \<subseteq> typs P1"
    if "X \<in> insert (th_prop (rep_of th)) (fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
    using full_prop_of_sub[OF f that] by simp_all
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have nn: "\<forall>v\<in>ttvars X. 0 \<le> snd (fst v)"
      if "X \<in> insert (th_prop (rep_of th)) (fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
      using that w0 by (force simp: thm_wf_def tvars_thm_def)
    have "thm_wf (maxidx_of_term (tmap ?\<phi> P1)) (hyps_of th)
        (map (\<lambda>(t, u). (tmap ?\<phi> t, tmap ?\<phi> u)) (th_tpairs (rep_of th))) (tmap ?\<phi> (th_prop (rep_of th)))"
    proof (rule thm_wf_tmap[OF w0 tmap_ok_freeze])
      show "-1 \<le> maxidx_of_term (tmap ?\<phi> P1)" using maxidx_term_ge by (simp add: maxidx_of_term_def)
      fix X assume X: "X \<in> insert (th_prop (rep_of th)) (fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))"
      have "ibelow (maxidx_of_term (tmap ?\<phi> P1)) (tmap ?\<phi> X)"
        using vars_typs_sub_ibelow[OF maxidx_of_term_ibelow tmap_sub[OF sub[OF X]]] .
      moreover have "\<forall>v\<in>ttvars (tmap ?\<phi> X). 0 \<le> snd (fst v)"
        using nn[OF X] tvars_freeze_tvar by (fastforce simp: ttvars_def typs_map_types)
      ultimately show "ibelow (maxidx_of_term (tmap ?\<phi> P1)) (tmap ?\<phi> X) \<and> (\<forall>v\<in>ttvars (tmap ?\<phi> X). 0 \<le> snd (fst v))"
        by simp
    qed
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: sh)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by simp
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule legacy_freezeT_valid[OF ok]) (use pure_thm_valid_in[of th M] M w0 in \<open>auto simp: thm_wf_def wt_thm_def\<close>)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have fv: "vars P1 \<subseteq> vars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)) \<and>
        ttvars P1 \<subseteq> tvars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      by (rule full_prop_of_vars[OF f])
    have nP: "noneg P1" using fv w0 by (intro pnn_noneg) (auto simp: thm_wf_def pnn_iff)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = legacy_freezeT_proof vl P1 q"
        by (auto simp: bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        unfolding pf by (rule legacy_freezeT_proof_valid[OF ok f vq(1)])
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using prf_idx_map_types[OF vq(2)] prf_nolb_map_types[OF vq(3)] vq(2,3)
        by (simp_all add: pf legacy_freezeT_proof_def Let_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zlegacy_freezeT_proof vl P1) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zlegacy_freezeT_proof vl P1 q = return z"
        by (auto simp: bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zlegacy_freezeT_proof_valid[OF ok f vq(1) nP zc z])
      moreover have "zinv z \<and> znolb 0 z \<and> zhyps z = zhyps q"
      proof (cases "legacy_freeze_names vl P1 = []")
        case True
        then show ?thesis using z vq(2,3) by (simp add: zlegacy_freezeT_proof_def)
      next
        case False
        define fv :: "indexname \<times> psort \<Rightarrow> ztyp option"
          where "fv = (\<lambda>(ix, S). map_option (\<lambda>a. ZTVar (a, -1) S) (map_of (legacy_freeze_names vl P1) ix))"
        have m: "map_zproof (zsubst_type fv) (\<lambda>t. return (zsubst_term (zsubst_type fv) (\<lambda>_. None) t)) q = return z"
          using z False by (simp add: zlegacy_freezeT_proof_def Let_def fv_def)
        have f: "ztyp_ok U" if "fv (v, S) = Some U" for v S U
          using that by (auto simp: fv_def)
        from zinv_map_zsubst_type[OF m vq(2) f] vq(3) show ?thesis by simp
      qed
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" using vq(4) by (simp add: zhyps_ok_def)
    qed
  qed
qed

theorem legacy_freezeT_thm:
  assumes "legacy_freezeT_thm vl th = Some th'"
  obtains P1 r where "ok (full_prop_of (th_tpairs (rep_of th)) (th_prop (rep_of th))) P1"
    "okT (legacy_freezeT vl (rep_of th)) r"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p))) (bindM (zproof_of th) (zlegacy_freezeT_proof vl P1)))"
proof -
  from assms obtain P1 r where f: "ok (full_prop_of (th_tpairs (rep_of th)) (th_prop (rep_of th))) P1"
    and ok: "okT (legacy_freezeT vl (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p))) (bindM (zproof_of th) (zlegacy_freezeT_proof vl P1))))"
    by (auto simp: legacy_freezeT_thm_def resT_Some resM_Some split: option.splits)
  show thesis
    by (rule that[OF f ok]) (use thm_ok_legacy_freezeT[OF ok f] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed


subsection \<open>Class membership\<close>

text \<open>
  \<open>Thm.of_class (T, c)\<close>: the proposition \<open>OFCLASS(T, c)\<close> is certified (\<open>global_cterm_of\<close>), its
  sorts are the sort hypotheses, and \<open>c\<close> is a declared class with its constant
  (\<open>Sign.certify_class\<close>).
\<close>

definition of_class_thm :: "pure_cterm \<Rightarrow> ptyp \<Rightarrow> pclass \<Rightarrow> 'u pure_thm option" where
  "of_class_thm ct T c =
    (if ct_t (crep_of ct) = mk_of_class T c \<and> tm_sorts (mk_of_class T c) \<subseteq> csorts_of ct \<and>
        pure_sig.class_const (sg_alg (csign_of ct)) (sg_consts (csign_of ct)) (c + STR ''_class'') c \<and>
        sign_eq (csign_of ct) then
      map_option (\<lambda>r. Abs_thm (solve_data (mk_thm r (csorts_of ct) [] (csign_of ct) (returnW (PClass T c))
        (return (OFCLASSp (ztyp_of T) c))))) (resT (Pure_Subst_Rules.of_class (sg_alg (csign_of ct)) T c))
     else None)"

context pure_sig
begin

lemma of_class_cterm:
  assumes wf: "cterm_wf (CTerm (mk_of_class T c) U m)"
  shows "wtp (mk_of_class T c)" "cert_typ alg ar T" "tnn T"
    "\<forall>v\<in>vars (mk_of_class T c). 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars (mk_of_class T c). 0 \<le> snd (fst v)"
proof -
  from wf have c: "closed (mk_of_class T c)" and ty: "\<And>e. e \<turnstile> mk_of_class T c : U"
    and nv: "\<forall>v\<in>vars (mk_of_class T c). 0 \<le> snd (fst v)" and nt: "\<forall>v\<in>ttvars (mk_of_class T c). 0 \<le> snd (fst v)"
    by (simp_all add: cterm_wf_def)
  from ty[of "\<lambda>_. propT"] have U: "U = propT" and cI: "cert_typ alg ar (Type STR ''itself'' [T])"
    by (auto simp: mk_of_class_def propT_def)
  show "wtp (mk_of_class T c)" using c ty U by (auto intro: wtpI)
  show "cert_typ alg ar T" using cI by (auto simp: cert_typ_def tarity_def)
  show "tnn T" using nt by (auto simp: tnn_def mk_of_class_def ttvars_def)
  show "\<forall>v\<in>vars (mk_of_class T c). 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars (mk_of_class T c). 0 \<le> snd (fst v)"
    by (rule nv, rule nt)
qed

end

lemma tsorts_tm_sorts_of_class: "tsorts T \<subseteq> tm_sorts (mk_of_class T c)"
  by (auto simp: mk_of_class_def)

lemma thm_ok_of_class:
  fixes ct :: pure_cterm
  assumes ok: "okT (Pure_Subst_Rules.of_class (sg_alg (csign_of ct)) T c) r"
    and P: "ct_t (crep_of ct) = mk_of_class T c" and so: "tm_sorts (mk_of_class T c) \<subseteq> csorts_of ct"
    and cc: "pure_sig.class_const (sg_alg (csign_of ct)) (sg_consts (csign_of ct)) (c + STR ''_class'') c"
    and se: "sign_eq (csign_of ct)"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct) [] (csign_of ct) (returnW (PClass T c))
    (return (OFCLASSp (ztyp_of T) c)))" (is "thm_ok _ ?th")
proof -
  let ?c = "csign_of ct" and ?P = "mk_of_class T c"
  obtain U m where cr: "crep_of ct = CTerm ?P U m" using P by (cases "crep_of ct") simp
  from ok have r: "r = mk_rep (maxidx_of_term ?P) [] ?P"
    by (auto simp: Pure_Subst_Rules.of_class_def returnW_def raiseW_def Let_def split: if_splits)
  have common: "pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) ?P \<and> cert_typ (sg_alg ?c) (sg_ar ?c) T \<and> tnn T \<and>
      (\<forall>v\<in>vars ?P. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>ttvars ?P. 0 \<le> snd (fst v))"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm ?P U m)" using pure_cterm_wf[OF ps] by (simp add: cr)
    from of_class_cterm[OF wf] show ?thesis by simp
  qed
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    from common[OF ps] have w: "wtp ?P" and nv: "\<forall>v\<in>vars ?P. 0 \<le> snd (fst v)" and nt: "\<forall>v\<in>ttvars ?P. 0 \<le> snd (fst v)"
      by simp_all
    have "thm_wf (maxidx_of_term ?P) [] [] ?P"
      unfolding thm_wf_def wt_thm_def using w nv nt maxidx_of_term_ibelow[of ?P] maxidx_term_ge[of "-1" ?P]
      by (simp add: vars_thm_def tvars_thm_def maxidx_of_term_def)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    from common[OF ps'] have w: "wtp ?P" and cT: "cert_typ (sg_alg ?c) (sg_ar ?c) T" by simp_all
    have "valid (csorts_of ct) [] (th_tpairs r) (th_prop r)"
      by (rule of_class_valid[OF ok cT cc _ w]) (use so tsorts_tm_sorts_of_class in blast)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
      using se by (simp add: sign_eq_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    from common[OF ps] have w: "wtp ?P" and cT: "cert_typ (sg_alg ?c) (sg_ar ?c) T" and tT: "tnn T" by simp_all
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "returnW (PClass T c) = returnW pf"
      then have pf: "pf = PClass T c" by (simp add: returnW_def)
      have "prf_valid (sg_ax ?c) (set []) (th_tpairs r) (PClass T c) (th_prop r)"
        by (rule of_class_proof_valid[OF ok cT w])
      then show "prf_valid (sg_ax ?c) (set []) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
        by (simp add: pf)
    next
      fix z assume "(return (OFCLASSp (ztyp_of T) c) :: zproof Z) = return z"
      then have z: "z = OFCLASSp (ztyp_of T) c" by (simp add: return_def)
      have "zvalid (sg_ax ?c) (set []) (th_tpairs r) z (th_prop r)"
        unfolding z by (rule zof_class_proof_valid[OF ok cT w])
      moreover have "zinv z" using ztyp_ok_ztyp_of[OF tT] by (simp add: z)
      ultimately show "zvalid (sg_ax ?c) (set []) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
        by (simp add: z zhyps_ok_def)
    qed
  qed
qed

theorem of_class_thm:
  assumes "of_class_thm ct T c = Some th"
  obtains r where "okT (Pure_Subst_Rules.of_class (sg_alg (csign_of ct)) T c) r" "ct_t (crep_of ct) = mk_of_class T c"
    "rep_thm th = solve_data (mk_thm r (csorts_of ct) [] (csign_of ct) (returnW (PClass T c)) (return (OFCLASSp (ztyp_of T) c)))"
proof -
  from assms obtain r where P: "ct_t (crep_of ct) = mk_of_class T c" and so: "tm_sorts (mk_of_class T c) \<subseteq> csorts_of ct"
    and cc: "pure_sig.class_const (sg_alg (csign_of ct)) (sg_consts (csign_of ct)) (c + STR ''_class'') c"
    and se: "sign_eq (csign_of ct)" and ok: "okT (Pure_Subst_Rules.of_class (sg_alg (csign_of ct)) T c) r"
    and th: "th = Abs_thm (solve_data (mk_thm r (csorts_of ct) [] (csign_of ct) (returnW (PClass T c)) (return (OFCLASSp (ztyp_of T) c))))"
    by (auto simp: of_class_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok P]) (unfold th, rule rep_Abs_thm, rule thm_ok_solve_data, rule thm_ok_of_class[OF ok P so cc se], simp)
qed


subsection \<open>Instantiation\<close>

text \<open>Bounds of the maximal index computed by \<open>Term_Subst.instantiate_maxidx\<close>:\<close>

lemma instT_m_bound:
  assumes bT: "\<forall>x\<in>set tab. \<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x)"
  shows "m \<le> snd (instT_m tab T m) \<and> (\<forall>w\<in>tvars (tsubst (tab_inst tab) T). snd (fst w) \<le> snd (instT_m tab T m))"
    "m \<le> snd (instTs_m tab Ts m) \<and>
      (\<forall>U\<in>set (map (tsubst (tab_inst tab)) Ts). \<forall>w\<in>tvars U. snd (fst w) \<le> snd (instTs_m tab Ts m))"
  using bT
proof (induction tab T m and tab Ts m rule: instT_m_instTs_m.induct)
  case (1 tab a Ts m)
  note bT = "1.prems"(1)
  obtain Ts' m' where e: "instTs_m tab Ts m = (Ts', m')" by (cases "instTs_m tab Ts m")
  from "1.IH"[OF bT] e show ?case by auto
next
  case (2 tab a i S m)
  note bT = "2.prems"(1)
  show ?case
  proof (cases "map_of tab ((a, i), S)")
    case (Some r)
    obtain U j where r: "r = (U, j)" by (cases r)
    from Some r have m: "(((a, i), S), (U, j)) \<in> set tab" by (auto dest: map_of_SomeD)
    have "\<forall>w\<in>tvars U. snd (fst w) \<le> j" using bT m by force
    with Some r show ?thesis by (auto simp: tab_inst_def)
  qed (auto simp: tab_inst_def)
next
  case (5 tab T Ts m)
  note bT = "5.prems"(1)
  obtain T' m1 where e1: "instT_m tab T m = (T', m1)" by (cases "instT_m tab T m")
  obtain Ts' m2 where e2: "instTs_m tab Ts m1 = (Ts', m2)" by (cases "instTs_m tab Ts m1")
  from "5.IH"(1)[OF bT] e1 have h1: "m \<le> m1" "\<forall>w\<in>tvars (tsubst (tab_inst tab) T). snd (fst w) \<le> m1" by simp_all
  from "5.IH"(2)[OF e1[symmetric] bT] e2
  have h2: "m1 \<le> m2" "\<forall>U\<in>set (map (tsubst (tab_inst tab)) Ts). \<forall>w\<in>tvars U. snd (fst w) \<le> m2" by simp_all
  have "\<forall>w\<in>tvars (tsubst (tab_inst tab) T). snd (fst w) \<le> m2" using h1(2) h2(1) by fastforce
  with h1 h2 show ?case using e1 e2 by simp
qed simp_all

context pure_sig
begin

lemma inst_m_bound:
  assumes bT: "\<forall>x\<in>set tT. \<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x)"
    and bt: "\<forall>x\<in>set tt. ibelow (snd (snd x)) (fst (snd x))"
  shows "m \<le> snd (inst_m tT tt t m) \<and> ibelow (snd (inst_m tT tt t m)) (vsubst (tab_subst tt) (inst (tab_inst tT) t))"
  using bT bt
proof (induction tT tt t m rule: inst_m.induct)
  case (1 tT tt c T m)
  note bT = "1.prems"(1) and bt = "1.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e instT_m_eq[OF e] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  then show ?case using e instT_m_eq[OF e] by (auto simp: ibelow_def)
next
  case (2 tT tt x T m)
  note bT = "2.prems"(1) and bt = "2.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e instT_m_eq[OF e] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  then show ?case using e instT_m_eq[OF e] by (auto simp: ibelow_def)
next
  case (3 tT tt x i T m)
  note bT = "3.prems"(1) and bt = "3.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have T': "T' = tsubst (tab_inst tT) T" using instT_m_eq[OF e] .
  have b: "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e T' instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  show ?case
  proof (cases "lookup_var tt ((x, i), T')")
    case (Some r)
    obtain u j where r: "r = (u, j)" by (cases r)
    from Some r have m: "(((x, i), T'), (u, j)) \<in> set tt" using lookup_var_SomeD by fastforce
    have "ibelow j u" using bt m by force
    then show ?thesis using Some r e b T'
      by (auto simp: tab_subst_def ibelow_def)
  next
    case None
    then show ?thesis using e b T' by (auto simp: tab_subst_def ibelow_def)
  qed
next
  case (5 tT tt x T b m)
  note bT = "5.prems"(1) and bt = "5.prems"(2)
  obtain T' m1 where e1: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  obtain b' m2 where e2: "inst_m tT tt b m1 = (b', m2)" by (cases "inst_m tT tt b m1")
  have bb: "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e1 instT_m_eq[OF e1] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  from "5.IH"[OF e1[symmetric] bT bt] e2 have "m1 \<le> m2" "ibelow m2 (vsubst (tab_subst tt) (inst (tab_inst tT) b))"
    by simp_all
  then show ?case using e1 e2 bb instT_m_eq[OF e1] by (auto simp: ibelow_def)
next
  case (6 tT tt t u m)
  note bT = "6.prems"(1) and bt = "6.prems"(2)
  obtain t' m1 where e1: "inst_m tT tt t m = (t', m1)" by (cases "inst_m tT tt t m")
  obtain u' m2 where e2: "inst_m tT tt u m1 = (u', m2)" by (cases "inst_m tT tt u m1")
  from "6.IH"(1)[OF bT bt] e1 have h1: "m \<le> m1" "ibelow m1 (vsubst (tab_subst tt) (inst (tab_inst tT) t))" by simp_all
  from "6.IH"(2)[OF e1[symmetric] bT bt] e2 have h2: "m1 \<le> m2" "ibelow m2 (vsubst (tab_subst tt) (inst (tab_inst tT) u))"
    by simp_all
  from h1(2) h2(1) have "ibelow m2 (vsubst (tab_subst tt) (inst (tab_inst tT) t))" by (rule ibelow_mono)
  with h1 h2 show ?case using e1 e2 by (auto simp: ibelow_def)
qed (simp add: ibelow_def)

lemma inst_beta_m_bound:
  assumes bT: "\<forall>x\<in>set tT. \<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x)"
    and bt: "\<forall>x\<in>set tt. ibelow (snd (snd x)) (fst (snd x))"
  shows "m \<le> snd (inst_beta_m tT tt t m) \<and>
      ibelow (snd (inst_beta_m tT tt t m)) (vsubst (tab_subst tt) (inst (tab_inst tT) t))"
    "m \<le> snd (inst_beta_spine tT tt t args m) \<and>
      ibelow (snd (inst_beta_spine tT tt t args m)) (vsubst (tab_subst tt) (inst (tab_inst tT) t))"
  using bT bt
proof (induction tT tt t m and tT tt t args m rule: inst_beta_m_inst_beta_spine.induct)
  case (1 tT tt c T m)
  note bT = "1.prems"(1) and bt = "1.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e instT_m_eq[OF e] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  then show ?case using e instT_m_eq[OF e] by (auto simp: ibelow_def)
next
  case (2 tT tt x T m)
  note bT = "2.prems"(1) and bt = "2.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e instT_m_eq[OF e] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  then show ?case using e instT_m_eq[OF e] by (auto simp: ibelow_def)
next
  case (5 tT tt x T b m)
  note bT = "5.prems"(1) and bt = "5.prems"(2)
  obtain T' m1 where e1: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  obtain b' m2 where e2: "inst_beta_m tT tt b m1 = (b', m2)" by (cases "inst_beta_m tT tt b m1")
  have bb: "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e1 instT_m_eq[OF e1] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  from "5.IH"[OF e1[symmetric] bT bt] e2 have "m1 \<le> m2" "ibelow m2 (vsubst (tab_subst tt) (inst (tab_inst tT) b))"
    by simp_all
  then show ?case using e1 e2 bb instT_m_eq[OF e1] by (auto simp: ibelow_def)
next
  case (6 tT tt t u m)
  note bT = "6.prems"(1) and bt = "6.prems"(2)
  obtain u' m1 where e1: "inst_beta_m tT tt u m = (u', m1)" by (cases "inst_beta_m tT tt u m")
  from "6.IH"(1)[OF bT bt] e1 have h1: "m \<le> m1" "ibelow m1 (vsubst (tab_subst tt) (inst (tab_inst tT) u))" by simp_all
  from "6.IH"(2)[OF e1[symmetric] bT bt]
  have h2: "m1 \<le> snd (inst_beta_spine tT tt t [u'] m1)"
    "ibelow (snd (inst_beta_spine tT tt t [u'] m1)) (vsubst (tab_subst tt) (inst (tab_inst tT) t))" by simp_all
  from h1(2) h2(1) have "ibelow (snd (inst_beta_spine tT tt t [u'] m1)) (vsubst (tab_subst tt) (inst (tab_inst tT) u))"
    by (rule ibelow_mono)
  with h1 h2 show ?case using e1 by (auto simp: ibelow_def)
next
  case (7 tT tt t u args m)
  note bT = "7.prems"(1) and bt = "7.prems"(2)
  obtain u' m1 where e1: "inst_beta_m tT tt u m = (u', m1)" by (cases "inst_beta_m tT tt u m")
  from "7.IH"(1)[OF bT bt] e1 have h1: "m \<le> m1" "ibelow m1 (vsubst (tab_subst tt) (inst (tab_inst tT) u))" by simp_all
  from "7.IH"(2)[OF e1[symmetric] bT bt]
  have h2: "m1 \<le> snd (inst_beta_spine tT tt t (u' # args) m1)"
    "ibelow (snd (inst_beta_spine tT tt t (u' # args) m1)) (vsubst (tab_subst tt) (inst (tab_inst tT) t))" by simp_all
  from h1(2) h2(1) have "ibelow (snd (inst_beta_spine tT tt t (u' # args) m1)) (vsubst (tab_subst tt) (inst (tab_inst tT) u))"
    by (rule ibelow_mono)
  with h1 h2 show ?case using e1 by (auto simp: ibelow_def)
next
  case (8 tT tt x i T args m)
  note bT = "8.prems"(1) and bt = "8.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have T': "T' = tsubst (tab_inst tT) T" using instT_m_eq[OF e] .
  have b: "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e T' instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  show ?case
  proof (cases "lookup_var tt ((x, i), T')")
    case (Some r)
    obtain u j where r: "r = (u, j)" by (cases r)
    from Some r have m: "(((x, i), T'), (u, j)) \<in> set tt" using lookup_var_SomeD by fastforce
    have "ibelow j u" using bt m by force
    then show ?thesis using Some r e b T' by (auto simp: tab_subst_def ibelow_def)
  next
    case None
    then show ?thesis using e b T' by (auto simp: tab_subst_def ibelow_def)
  qed
next
  case (9 tT tt c T args m)
  note bT = "9.prems"(1) and bt = "9.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e instT_m_eq[OF e] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  then show ?case using e instT_m_eq[OF e] by (auto simp: ibelow_def)
next
  case (10 tT tt x T args m)
  note bT = "10.prems"(1) and bt = "10.prems"(2)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e instT_m_eq[OF e] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  then show ?case using e instT_m_eq[OF e] by (auto simp: ibelow_def)
next
  case (12 tT tt x T b args m)
  note bT = "12.prems"(1) and bt = "12.prems"(2)
  obtain T' m1 where e1: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  obtain b' m2 where e2: "inst_beta_m tT tt b m1 = (b', m2)" by (cases "inst_beta_m tT tt b m1")
  have bb: "m \<le> m1" "\<forall>w\<in>tvars T'. snd (fst w) \<le> m1"
    using e1 instT_m_eq[OF e1] instT_m_bound(1)[OF bT, where T = T and m = m] by simp_all
  from "12.IH"[OF e1[symmetric] bT bt] e2 have "m1 \<le> m2" "ibelow m2 (vsubst (tab_subst tt) (inst (tab_inst tT) b))"
    by simp_all
  then show ?case using e1 e2 bb instT_m_eq[OF e1] by (auto simp: ibelow_def)
qed (simp_all add: ibelow_def)

end


lemma pnn_iff': "pnn t \<longleftrightarrow> (\<forall>v\<in>vars t. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>ttvars t. 0 \<le> snd (fst v))"
  by (fastforce simp: pnn_def tnn_def ttvars_def)

lemma tnn_tsubst_tab: "tnn T \<Longrightarrow> \<forall>x\<in>set tT. tnn (fst (snd x)) \<Longrightarrow> tnn (tsubst (tab_inst tT) T)"
proof (induction T)
  case (TVar v S)
  show ?case
  proof (cases "map_of tT (v, S)")
    case (Some r)
    then have "((v, S), r) \<in> set tT" by (rule map_of_SomeD)
    with TVar.prems(2) Some show ?thesis by (cases r) (force simp: tab_inst_def)
  qed (use TVar.prems in \<open>simp add: tab_inst_def\<close>)
qed auto

lemma pnn_ap_tab:
  assumes "pnn t" "\<forall>x\<in>set tT. tnn (fst (snd x))" "\<forall>x\<in>set tt. pnn (fst (snd x))"
  shows "pnn (vsubst (tab_subst tt) (inst (tab_inst tT) t))"
  using assms(1)
proof (induction t)
  case (Var x T)
  show ?case
  proof (cases "lookup_var tt (x, tsubst (tab_inst tT) T)")
    case (Some r)
    then have "((x, tsubst (tab_inst tT) T), r) \<in> set tt" by (rule lookup_var_SomeD)
    with assms(3) Some show ?thesis by (cases r) (force simp: tab_subst_def)
  next
    case None
    have "tnn (tsubst (tab_inst tT) T)" using Var.prems tnn_tsubst_tab[OF _ assms(2)] by (simp add: pnn_def)
    with None Var.prems show ?thesis by (simp add: tab_subst_def pnn_def)
  qed
next
  case (Const c T)
  then show ?case using tnn_tsubst_tab[OF _ assms(2)] by (simp add: pnn_def)
next
  case (Free x T)
  then show ?case using tnn_tsubst_tab[OF _ assms(2)] by (simp add: pnn_def)
next
  case (Abs a T t)
  then show ?case using tnn_tsubst_tab[OF _ assms(2)] by simp
next
  case (Bound i)
  then show ?case by (simp add: pnn_def)
next
  case (App s t)
  then show ?case by simp
qed

lemma instantiate_shape:
  assumes ok: "okT (instantiate alg bt instT insts th0) th" and ne: "\<not> (instT = [] \<and> insts = [])"
  defines "tt \<equiv> map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts"
  defines "f \<equiv> (if bt then inst_beta_m instT tt else inst_m instT tt)"
  defines "F \<equiv> (\<lambda>(t, u) (acc, i). case f t i of (t', i1) \<Rightarrow> case f u i1 of (u', i2) \<Rightarrow>
    (acc @ [(t' :: pterm, u')], i2))"
  shows "okT (check_instT alg instT) ()" "okT (check_inst insts) ()"
    "th_prop th = fst (f (th_prop th0) (-1))"
    "th_tpairs th = fst (fold F (th_tpairs th0) ([], snd (f (th_prop th0) (-1))))"
    "th_maxidx th = snd (fold F (th_tpairs th0) ([], snd (f (th_prop th0) (-1))))"
    "list_all (\<lambda>x. 0 \<le> snd (fst (fst x))) instT" "list_all (\<lambda>x. 0 \<le> snd (fst (fst x))) insts"
  using ok ne unfolding instantiate_def f_def F_def tt_def check_inst_idx_def
  by (auto simp: returnW_def raiseW_def Let_def mk_rep_def split: prod.splits if_splits)

lemma fold_tpairs_bound:
  fixes f :: "pterm \<Rightarrow> integer \<Rightarrow> pterm \<times> integer" and Q :: "integer \<Rightarrow> pterm \<Rightarrow> bool"
  assumes f: "\<And>t i. i \<le> snd (f t i) \<and> Q (snd (f t i)) (fst (f t i))"
    and mono: "\<And>m m' x. Q m x \<Longrightarrow> m \<le> m' \<Longrightarrow> Q m' x"
  defines "F \<equiv> (\<lambda>(t, u) (acc, i). case f t i of (t', i1) \<Rightarrow> case f u i1 of (u', i2) \<Rightarrow>
    (acc @ [(t', u')], i2))"
  shows "m \<le> snd (fold F tps (acc, m)) \<and>
    (\<forall>p\<in>set (fst (fold F tps (acc, m))). p \<in> set acc \<or> (Q (snd (fold F tps (acc, m))) (fst p) \<and>
      Q (snd (fold F tps (acc, m))) (snd p)))"
proof (induction tps arbitrary: acc m)
  case (Cons p tps)
  obtain t u where p: "p = (t, u)" by (cases p)
  obtain t' i1 where e1: "f t m = (t', i1)" by (cases "f t m")
  obtain u' i2 where e2: "f u i1 = (u', i2)" by (cases "f u i1")
  have F: "F p (acc, m) = (acc @ [(t', u')], i2)" by (simp add: F_def p e1 e2)
  have b: "m \<le> i1" "Q i1 t'" "i1 \<le> i2" "Q i2 u'" using f[where t = t and i = m] f[where t = u and i = i1] by (simp_all add: e1 e2)
  let ?r = "fold F tps (acc @ [(t', u')], i2)"
  have IH: "i2 \<le> snd ?r" "\<forall>q\<in>set (fst ?r). q \<in> set (acc @ [(t', u')]) \<or> (Q (snd ?r) (fst q) \<and> Q (snd ?r) (snd q))"
    using Cons.IH[where acc = "acc @ [(t', u')]" and m = i2] by simp_all
  have q: "Q (snd ?r) t'" "Q (snd ?r) u'"
    using mono[OF b(2) order_trans[OF b(3) IH(1)]] mono[OF b(4) IH(1)] by simp_all
  have "m \<le> snd ?r" using b(1,3) IH(1) by simp
  then show ?case using IH(2) q by (auto simp: F)
qed simp

context pure_sig
begin

lemma pnn_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> pnn s \<Longrightarrow> pnn t"
  using beta_reds_vars[of s t] beta_reds_typs[of s t] by (auto simp: pnn_def)

lemma has_sort_check_instT':
  "okT (check_instT alg tab) () \<Longrightarrow> ((v, S), (U, j)) \<in> set tab \<Longrightarrow> wft ar U \<Longrightarrow> has_sort alg U S"
proof (induction tab)
  case (Cons e xs)
  obtain a i S' U' j' where e: "e = (((a, i), S'), (U', j'))" by (metis prod.collapse)
  from Cons.prems(1) e obtain b where b: "ok (of_sort alg U' S') b"
    and r: "okT (if b then check_instT alg xs else raiseW (NOT_OF_SORT U' S')) ()"
    by auto
  from r have b': "b" "okT (check_instT alg xs) ()" by (auto simp: raiseW_def split: if_splits)
  show ?case
  proof (cases "((v, S), (U, j)) = (((a, i), S'), (U', j'))")
    case True
    then have eq: "U = U'" "S = S'" by auto
    with Cons.prems(3) have "of_sort alg U' S' = return (has_sort alg U' S')" by (simp add: of_sort_sem)
    with b b'(1) eq show ?thesis by simp
  next
    case False
    with Cons.prems(2) e have "((v, S), (U, j)) \<in> set xs" by auto
    from Cons.IH[OF b'(2) this Cons.prems(3)] show ?thesis .
  qed
qed simp

lemma check_inst_eq': "okT (check_inst insts) () \<Longrightarrow> ((v, T), (u, U, j)) \<in> set insts \<Longrightarrow> T = U"
  by (induction insts rule: check_inst.induct) (auto simp: raiseW_def split: if_splits)

lemma instantiate_inst_ok:
  assumes ci: "okT (check_instT alg instT) ()" and cs: "okT (check_inst insts) ()"
    and cT: "\<forall>x\<in>set instT. cert_typ alg ar (fst (snd x))"
    and ct: "\<forall>x\<in>set insts. closed (fst (snd x)) \<and> (\<forall>e. e \<turnstile> fst (snd x) : fst (snd (snd x)))"
  shows "cinst (tab_inst instT)" "wt_subst (tab_subst (map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts))"
proof -
  let ?tt = "map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts"
  show "cinst (tab_inst instT)" unfolding cinst_def
  proof
    show "wsinst alg (tab_inst instT)" unfolding wsinst_def
    proof (intro allI)
      fix v S show "has_sort alg (tab_inst instT v S) S"
      proof (cases "map_of instT (v, S)")
        case (Some r)
        obtain U j where r: "r = (U, j)" by (cases r)
        with Some have m: "((v, S), (U, j)) \<in> set instT" by (auto dest: map_of_SomeD)
        moreover from m cT have "wft ar U" by (force simp: cert_typ_def)
        ultimately show ?thesis using has_sort_check_instT'[OF ci] Some r by (simp add: tab_inst_def)
      qed (simp add: tab_inst_def, use class_le_refl in blast)
    qed
    show "cert_inst (tab_inst instT)" unfolding cert_inst_def
    proof (intro allI impI)
      fix v S assume "sort_ok alg S"
      then show "cert_typ alg ar (tab_inst instT v S)" using cT
        by (force simp: tab_inst_def cert_typ_def split: option.splits dest!: map_of_SomeD)
    qed
  qed
  show "wt_subst (tab_subst ?tt)" unfolding wt_subst_def closed_subst_def
  proof (intro conjI allI impI)
    fix x T
    show "closed (tab_subst ?tt x T)" using ct
      by (force simp: tab_subst_def closed_def split: option.splits dest!: lookup_var_SomeD)
    assume "cert_typ alg ar T"
    then show "\<exists>e. e \<turnstile> tab_subst ?tt x T : T"
    proof (cases "lookup_var ?tt (x, T)")
      case (Some r)
      obtain u j where r: "r = (u, j)" by (cases r)
      with Some obtain U where m: "((x, T), (u, U, j)) \<in> set insts" by (force dest!: lookup_var_SomeD)
      with ct check_inst_eq'[OF cs m] Some r show ?thesis by (force simp: tab_subst_def)
    qed (auto simp: tab_subst_def)
  qed
qed

lemma wtp_ap: "wtp X \<Longrightarrow> cinst \<rho> \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> wtp (ap \<rho> \<sigma> X)"
proof (rule wtpI)
  assume X: "wtp X" and \<rho>: "cinst \<rho>" and \<sigma>: "wt_subst \<sigma>"
  show "closed (ap \<rho> \<sigma> X)" using wtpD(1)[OF X] \<sigma> by (simp add: closed_def ap_def wt_subst_def)
  have "(\<lambda>i. tsubst \<rho> propT) \<turnstile> ap \<rho> \<sigma> X : tsubst \<rho> propT"
    by (rule typing_ap_inst[OF wtpD(2)[OF X] cinstD(2)[OF \<rho>] \<sigma>])
  then show "(\<lambda>_. propT) \<turnstile> ap \<rho> \<sigma> X : propT"
    using \<open>closed (ap \<rho> \<sigma> X)\<close> typing_closed by (simp add: propT_def)
qed

end


context pure_sig
begin

lemma instantiate_step:
  fixes bt' :: bool
  assumes bT: "\<forall>x\<in>set instT. \<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x)"
    and bt: "\<forall>x\<in>set tt. ibelow (snd (snd x)) (fst (snd x))"
  defines "f \<equiv> (if bt' then inst_beta_m instT tt else inst_m instT tt)"
  shows "i \<le> snd (f t i) \<and> ibelow (snd (f t i)) (fst (f t i)) \<and>
    ap (tab_inst instT) (tab_subst tt) t \<rightarrow>\<^sub>\<beta>\<^sup>* fst (f t i)"
proof (cases bt')
  case True
  note b = inst_beta_m_bound(1)[OF bT bt, where t = t and m = i]
  note r = inst_beta_m_reds(1)[where tt = tt and tT = instT and t = t and m = i]
  have "ibelow (snd (inst_beta_m instT tt t i)) (fst (inst_beta_m instT tt t i))"
    by (rule vars_typs_sub_ibelow[OF conjunct2[OF b] beta_reds_vars[OF r] beta_reds_typs[OF r]])
  then show ?thesis using True b r by (simp add: f_def ap_def)
next
  case False
  note b = inst_m_bound[OF bT bt, where t = t and m = i]
  then show ?thesis using False by (simp add: f_def ap_def inst_m_fst)
qed

lemma thm_wf_instantiate:
  assumes ok: "okT (instantiate alg bt instT insts th0) th" and ne: "\<not> (instT = [] \<and> insts = [])"
    and w: "thm_wf (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)"
    and cT: "\<forall>x\<in>set instT. cert_typ alg ar (fst (snd x)) \<and> tnn (fst (snd x)) \<and>
      (\<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x))"
    and ct: "\<forall>x\<in>set insts. cterm_wf (CTerm (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x))))"
  shows "thm_wf (th_maxidx th) hs (th_tpairs th) (th_prop th)"
proof -
  define tt where "tt = map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts"
  define f where "f = (if bt then inst_beta_m instT tt else inst_m instT tt)"
  define F where "F = (\<lambda>(t, u) (acc, i). case f t i of (t', i1) \<Rightarrow> case f u i1 of (u', i2) \<Rightarrow>
    (acc @ [(t' :: pterm, u')], i2))"
  note sh = instantiate_shape[OF ok ne, folded tt_def f_def F_def]
  let ?\<rho> = "tab_inst instT" and ?\<sigma> = "tab_subst tt"
  have ctw: "closed u \<and> (\<forall>e. e \<turnstile> u : U) \<and> ibelow j u \<and> pnn u" if "((v, T), (u, U, j)) \<in> set insts" for v T u U j
    using ct that by (force simp: cterm_wf_def pnn_iff')
  have bT: "\<forall>x\<in>set instT. \<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x)" using cT by blast
  have bt: "\<forall>x\<in>set tt. ibelow (snd (snd x)) (fst (snd x))" using ctw by (force simp: tt_def)
  have ptt: "\<forall>x\<in>set tt. pnn (fst (snd x))" using ctw by (force simp: tt_def)
  have tnT: "\<forall>x\<in>set instT. tnn (fst (snd x))" using cT by blast
  have io: "cinst ?\<rho>" "wt_subst ?\<sigma>"
    using instantiate_inst_ok[OF sh(1) sh(2)] cT ct unfolding tt_def by (force simp: cterm_wf_def)+
  note stp = instantiate_step[OF bT bt, where bt' = bt, folded f_def]
  from w have wP: "wtp (th_prop th0)" and h: "\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tp: "\<forall>(t, u)\<in>set (th_tpairs th0). closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and m0: "-1 \<le> th_maxidx th0"
    and pP: "pnn (th_prop th0)" and pT: "\<forall>(t, u)\<in>set (th_tpairs th0). pnn t \<and> pnn u"
    unfolding thm_wf_def wt_thm_def by (auto simp: pnn_iff' vars_thm_def tvars_thm_def)
  let ?P = "th_prop th0"
  let ?r = "fold F (th_tpairs th0) ([], snd (f ?P (-1)))"
  have fb: "snd (f ?P (-1)) \<le> snd ?r \<and> (\<forall>p\<in>set (fst ?r). p \<in> set [] \<or> (ibelow (snd ?r) (fst p) \<and> ibelow (snd ?r) (snd p)))"
    unfolding F_def by (rule fold_tpairs_bound[where Q = ibelow]) (use stp ibelow_mono in auto)
  obtain ps where ps: "fst ?r = [] @ ps"
    and l: "list_all2 (\<lambda>(t, u) (t', u'). ap ?\<rho> ?\<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> ap ?\<rho> ?\<sigma> u \<rightarrow>\<^sub>\<beta>\<^sup>* u') (th_tpairs th0) ps"
    using fold_tpairs[of "\<lambda>t t'. ap ?\<rho> ?\<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" f "th_tpairs th0" "[]" "snd (f ?P (-1))"] stp
    unfolding F_def by blast
  have stP: "-1 \<le> snd (f ?P (-1))" "ibelow (snd (f ?P (-1))) (fst (f ?P (-1)))" "ap ?\<rho> ?\<sigma> ?P \<rightarrow>\<^sub>\<beta>\<^sup>* fst (f ?P (-1))"
    using stp[where i = "-1" and t = ?P] by simp_all
  \<comment> \<open>the proposition\<close>
  have wP': "wtp (fst (f ?P (-1)))"
  proof (rule wtpI)
    note wa = wtp_ap[OF wP io]
    show "closed (fst (f ?P (-1)))" by (rule beta_reds_closed[OF stP(3) wtpD(1)[OF wa]])
    show "(\<lambda>_. propT) \<turnstile> fst (f ?P (-1)) : propT" by (rule subject_reduction_beta'[OF stP(3) wtpD(2)[OF wa]])
  qed
  have pP': "pnn (fst (f ?P (-1)))"
    using pnn_beta_reds[OF stP(3)] pnn_ap_tab[OF pP tnT ptt] by (simp add: ap_def)
  \<comment> \<open>the flex-flex pairs\<close>
  have tp': "closed t' \<and> closed u' \<and> ibelow (snd ?r) t' \<and> ibelow (snd ?r) u' \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t' : T \<and> e \<turnstile> u' : T) \<and> pnn t' \<and> pnn u'" if tu': "(t', u') \<in> set ps" for t' u'
  proof -
    from tu' obtain i where i: "i < length ps" "ps ! i = (t', u')" by (auto simp: in_set_conv_nth)
    have il: "i < length (th_tpairs th0)" using i(1) list_all2_lengthD[OF l] by simp
    obtain t u where tu: "th_tpairs th0 ! i = (t, u)" by (cases "th_tpairs th0 ! i")
    have m: "(t, u) \<in> set (th_tpairs th0)" using nth_mem[OF il] tu by simp
    from list_all2_nthD[OF l il] tu i(2) have red: "ap ?\<rho> ?\<sigma> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" "ap ?\<rho> ?\<sigma> u \<rightarrow>\<^sub>\<beta>\<^sup>* u'" by simp_all
    from tp m obtain T where c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
    have ca: "closed (ap ?\<rho> ?\<sigma> t)" "closed (ap ?\<rho> ?\<sigma> u)"
      using c io(2) by (simp_all add: closed_def ap_def wt_subst_def)
    have ta: "e \<turnstile> ap ?\<rho> ?\<sigma> t : tsubst ?\<rho> T" "e \<turnstile> ap ?\<rho> ?\<sigma> u : tsubst ?\<rho> T" for e
      using typing_ap_inst[OF ty(1) cinstD(2)[OF io(1)] io(2)] typing_ap_inst[OF ty(2) cinstD(2)[OF io(1)] io(2)]
        ca typing_closed by blast+
    have "closed t'" "closed u'" using beta_reds_closed[OF red(1) ca(1)] beta_reds_closed[OF red(2) ca(2)] .
    moreover have "\<forall>e. e \<turnstile> t' : tsubst ?\<rho> T \<and> e \<turnstile> u' : tsubst ?\<rho> T"
      using subject_reduction_beta'[OF red(1) ta(1)] subject_reduction_beta'[OF red(2) ta(2)] by blast
    moreover have "ibelow (snd ?r) t'" "ibelow (snd ?r) u'" using fb tu' ps by auto
    moreover have "pnn t'" "pnn u'"
      using pnn_beta_reds[OF red(1)] pnn_beta_reds[OF red(2)] pnn_ap_tab[OF _ tnT ptt] pT m by (auto simp: ap_def)
    ultimately show ?thesis by blast
  qed
  have ibP': "ibelow (snd ?r) (fst (f ?P (-1)))" using ibelow_mono[OF stP(2) conjunct1[OF fb]] .
  have mr: "-1 \<le> snd ?r" using stP(1) fb by simp
  have vn: "\<forall>v\<in>vars_thm ps (fst (f ?P (-1))). 0 \<le> snd (fst v)"
    using pP' tp' unfolding vars_thm_def pnn_def by fastforce
  have tn: "\<forall>v\<in>tvars_thm ps (fst (f ?P (-1))). 0 \<le> snd (fst v)"
    using pP' tp' unfolding tvars_thm_def pnn_iff' by fastforce
  have "thm_wf (snd ?r) hs ps (fst (f ?P (-1)))"
    unfolding thm_wf_def wt_thm_def using wP' ibP' h tp' mr vn tn by fast
  then show ?thesis using sh(3-5) ps by (simp add: F_def)
qed

end

context prf_sig
begin

lemma prf_valid_beta_reds:
  assumes p: "prf_valid ax H tps pf \<phi>" and l: "list_all2 (\<lambda>(t, u) (t', u'). t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> u \<rightarrow>\<^sub>\<beta>\<^sup>* u') tps tps'"
    and red: "\<phi> \<rightarrow>\<^sub>\<beta>\<^sup>* \<phi>'" and w: "wtp \<phi>"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  shows "prf_valid ax H tps' pf \<phi>'"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  have ws: "wt_subst \<sigma>" using \<sigma> by (simp add: gsubst_def)
  have p0: "prf_ok ax H (ieqs \<rho> \<sigma> tps) e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> \<phi>)" by (rule prf_validD[OF p \<rho> \<sigma>])
  have p1: "prf_ok ax H (ieqs \<rho> \<sigma> tps') e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> \<phi>)"
  proof (rule prf_ok_eqs[OF _ p0])
    fix l r e' T assume lr: "(l, r) \<in> ieqs \<rho> \<sigma> tps" and c: "closed l" "closed r"
      and tl: "e' \<turnstile> l : T" "e' \<turnstile> r : T"
    from lr obtain t u where tu: "(t, u) \<in> set tps" and lt: "l = ap \<rho> \<sigma> t" and ru: "r = ap \<rho> \<sigma> u" by auto
    from tu obtain i where i: "i < length tps" "tps ! i = (t, u)" by (auto simp: in_set_conv_nth)
    have il: "i < length tps'" using i(1) list_all2_lengthD[OF l] by simp
    obtain t' u' where tu': "tps' ! i = (t', u')" by (cases "tps' ! i")
    from list_all2_nthD[OF l i(1)] i(2) tu' have red': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" "u \<rightarrow>\<^sub>\<beta>\<^sup>* u'" by simp_all
    have m': "(t', u') \<in> set tps'" using nth_mem[OF il] tu' by simp
    have ra: "l \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> t'" "r \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> u'"
      unfolding lt ru by (rule beta_reds_ap[OF red'(1) ws], rule beta_reds_ap[OF red'(2) ws])
    have c': "closed (ap \<rho> \<sigma> t')" "closed (ap \<rho> \<sigma> u')" using beta_reds_closed[OF ra(1) c(1)] beta_reds_closed[OF ra(2) c(2)] .
    have t': "e' \<turnstile> ap \<rho> \<sigma> t' : T" "e' \<turnstile> ap \<rho> \<sigma> u' : T"
      using subject_reduction_beta'[OF ra(1) tl(1)] subject_reduction_beta'[OF ra(2) tl(2)] .
    have "(ap \<rho> \<sigma> t', ap \<rho> \<sigma> u') \<in> ceqs (ieqs \<rho> \<sigma> tps')" using pmapI[OF m', of "ap \<rho> \<sigma>"] c' by simp
    from eqv.eqv_ax[OF this t'] have m: "eqv (ceqs (ieqs \<rho> \<sigma> tps')) e' (ap \<rho> \<sigma> t') (ap \<rho> \<sigma> u')" .
    have cl: "l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" "r \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
      using conv_beta_eta[OF _ ra(1)] conv_beta_eta[OF _ ra(2)] tl by (auto simp: wt_def)
    show "eqv (ceqs (ieqs \<rho> \<sigma> tps')) e' l r"
      by (rule eqv.eqv_trans[OF eqv.eqv_trans[OF eqv.eqv_conv[OF cl(1) tl(1) t'(1)] m]
        eqv.eqv_sym[OF eqv.eqv_conv[OF cl(2) tl(2) t'(2)]]])
  qed
  have ra: "ap \<rho> \<sigma> \<phi> \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> \<phi>'" by (rule beta_reds_ap[OF red ws])
  have ta: "e \<turnstile> ap \<rho> \<sigma> \<phi> : propT" by (rule typing_ap_wtp[OF w \<rho> \<sigma>])
  show "prf_ok ax H (ieqs \<rho> \<sigma> tps') e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> \<phi>')"
    by (rule prf_ok.conv[OF p1 conv_beta_eta[OF _ ra] subject_reduction_beta'[OF ra ta]]) (use ta in \<open>auto simp: wt_def\<close>)
qed

lemma zvalid_beta_reds:
  assumes p: "zvalid ax H tps pf \<phi>" and l: "list_all2 (\<lambda>(t, u) (t', u'). t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> u \<rightarrow>\<^sub>\<beta>\<^sup>* u') tps tps'"
    and red: "\<phi> \<rightarrow>\<^sub>\<beta>\<^sup>* \<phi>'" and w: "wtp \<phi>"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  shows "zvalid ax H tps' pf \<phi>'"
proof -
  obtain w0 where w0: "pcerase w0 = pcerase (zprf_tr pf)" "prf_valid ax H tps w0 \<phi>" using p by (rule zvalidE)
  from zvalidI[OF w0(1) prf_valid_beta_reds[OF w0(2) l red w tw]] show ?thesis .
qed

end


text \<open>
  Certified types (\<open>Thm.ctyp\<close>): a certified type with its maximal index and its sorts; its
  type variables have non-negative indices bounded by the maximal index.
\<close>

record ctyp_data =
  cty_T :: ptyp
  cty_maxidx :: integer
  cty_sorts :: "psort set"
  cty_sign :: sign

definition ctyp_ok :: "ctyp_data \<Rightarrow> bool" where
  "ctyp_ok c \<longleftrightarrow> (pure_sig (sg_alg (cty_sign c)) (sg_ar (cty_sign c)) \<longrightarrow>
      cert_typ (sg_alg (cty_sign c)) (sg_ar (cty_sign c)) (cty_T c) \<and> -1 \<le> cty_maxidx c \<and>
      (\<forall>w\<in>tvars (cty_T c). 0 \<le> snd (fst w) \<and> snd (fst w) \<le> cty_maxidx c)) \<and>
    tsorts (cty_T c) \<subseteq> cty_sorts c"

lemma ctyp_ok_prop: "ctyp_ok \<lparr>cty_T = propT, cty_maxidx = -1, cty_sorts = {}, cty_sign = sign0\<rparr>"
  by (simp add: ctyp_ok_def cert_typ_def propT_def tarity_def sign0_def)

typedef (overloaded) pure_ctyp = "{c. ctyp_ok c}"
  morphisms rep_ctyp Abs_ctyp
  using ctyp_ok_prop by blast

lemma pure_ctyp_ok: "ctyp_ok (rep_ctyp cT)"
  using rep_ctyp[of cT] by simp

definition instT_of :: "((indexname \<times> psort) \<times> pure_ctyp) list \<Rightarrow> instT_m" where
  "instT_of cTs = map (\<lambda>(v, cT). (v, (cty_T (rep_ctyp cT), cty_maxidx (rep_ctyp cT)))) cTs"

definition insts_of :: "((indexname \<times> ptyp) \<times> pure_cterm) list \<Rightarrow>
    ((indexname \<times> ptyp) \<times> pterm \<times> ptyp \<times> integer) list" where
  "insts_of cts = map (\<lambda>(v, ct). (v, (ct_t (crep_of ct), ct_T (crep_of ct), ct_maxidx (crep_of ct)))) cts"

definition inst_Ts :: "((indexname \<times> psort) \<times> pure_ctyp) list \<Rightarrow> instT" where
  "inst_Ts cTs = map (\<lambda>(v, cT). (v, cty_T (rep_ctyp cT))) cTs"

definition inst_ts :: "((indexname \<times> ptyp) \<times> pure_cterm) list \<Rightarrow> inst" where
  "inst_ts cts = map (\<lambda>(v, ct). (v, ct_t (crep_of ct))) cts"

definition inst_sorts :: "((indexname \<times> psort) \<times> pure_ctyp) list \<Rightarrow> ((indexname \<times> ptyp) \<times> pure_cterm) list \<Rightarrow>
    psort set" where
  "inst_sorts cTs cts = (\<Union>(v, cT)\<in>set cTs. cty_sorts (rep_ctyp cT)) \<union> (\<Union>(v, ct)\<in>set cts. csorts_of ct)"

text \<open>
  \<open>Thm.instantiate\<close> (\<open>beta = False\<close>) and \<open>Thm.instantiate_beta\<close> (\<open>beta = True\<close>). The
  rule checks that the instantiated variables have indices from \<open>0\<close> (fix
  \<open>thm-instantiate-index\<close>): the tight proofs reserve the index \<open>-1\<close> for free variables.
\<close>

definition instantiate_thm :: "bool \<Rightarrow> ((indexname \<times> psort) \<times> pure_ctyp) list \<Rightarrow>
    ((indexname \<times> ptyp) \<times> pure_cterm) list \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "instantiate_thm bt cTs cts th =
    (if cTs = [] \<and> cts = [] then Some th
     else if (\<forall>(v, cT)\<in>set cTs. cty_sign (rep_ctyp cT) = sign_of th) \<and>
        (\<forall>(v, ct)\<in>set cts. csign_of ct = sign_of th) then
      map_option (\<lambda>r. Abs_thm (solve_data (mk_thm r (shyps_of th \<union> inst_sorts cTs cts) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)))
          (bindM (zproof_of th) (zinstantiate_proof (pure_sig.ztargs (sg_consts (sign_of th))) (inst_Ts cTs) (inst_ts cts))))))
        (resT (instantiate (sg_alg (sign_of th)) bt (instT_of cTs) (insts_of cts) (rep_of th)))
     else None)"

lemma tab_inst_Ts: "tab_inst (map (\<lambda>(v, T). (v, (T, -1))) (inst_Ts cTs)) = tab_inst (instT_of cTs)"
proof -
  have "tab_inst (map (\<lambda>(v, T). (v, (T, -1))) (inst_Ts cTs)) v S = tab_inst (instT_of cTs) v S" for v S
    by (induction cTs) (auto simp: tab_inst_def inst_Ts_def instT_of_def split: option.splits)
  then show ?thesis by (intro ext)
qed

lemma tab_subst_ts:
  "tab_subst (map (\<lambda>(v, t). (v, (t, -1))) (inst_ts cts)) = tab_subst (map (\<lambda>(v, (u, U, j)). (v, (u, j))) (insts_of cts))"
proof -
  have "tab_subst (map (\<lambda>(v, t). (v, (t, -1))) (inst_ts cts)) x T =
      tab_subst (map (\<lambda>(v, (u, U, j)). (v, (u, j))) (insts_of cts)) x T" for x T
    by (induction cts) (auto simp: tab_subst_def inst_ts_def insts_of_def split: option.splits if_splits)
  then show ?thesis by (intro ext)
qed

lemma vars_remove_types [simp]: "vars (remove_types t) = vars t"
  by (induction t rule: remove_types.induct) auto

lemma loose_bvar_remove_types [simp]: "loose_bvar (remove_types t) k \<longleftrightarrow> loose_bvar t k"
  by (induction t arbitrary: k rule: remove_types.induct) auto

lemma vars_vsubst_inst_nonneg:
  assumes "\<forall>w\<in>vars t. 0 \<le> snd (fst w)" "\<And>x T w. w \<in> vars (\<sigma> x T) \<Longrightarrow> w = (x, T) \<or> 0 \<le> snd (fst w)"
  shows "\<forall>w\<in>vars (vsubst \<sigma> (inst \<rho> t)). 0 \<le> snd (fst w)"
  using assms(1) by (induction t) (auto dest: assms(2))

lemma lookup_zvar_SomeD: "lookup_zvar xs v = Some u \<Longrightarrow> (v, u) \<in> set xs"
  by (induction xs v rule: lookup_zvar.induct) (auto split: if_splits)

lemma lookup_var_map_Some:
  "lookup_var (map (\<lambda>(v, t). (v, (g t, -1))) xs) w = Some r \<Longrightarrow> \<exists>t. (w, t) \<in> set xs \<and> r = (g t, -1)"
  by (induction xs) (auto split: if_splits)


context pure_sig
begin

lemma instantiate_reds:
  assumes ok: "okT (instantiate alg bt instT insts th0) th" and ne: "\<not> (instT = [] \<and> insts = [])"
    and cT: "\<forall>x\<in>set instT. cert_typ alg ar (fst (snd x)) \<and> tnn (fst (snd x)) \<and>
      (\<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x))"
    and ct: "\<forall>x\<in>set insts. cterm_wf (CTerm (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x))))"
  defines "tt \<equiv> map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts"
  shows "cinst (tab_inst instT)" "wt_subst (tab_subst tt)" "okT (check_inst insts) ()"
    "ap (tab_inst instT) (tab_subst tt) (th_prop th0) \<rightarrow>\<^sub>\<beta>\<^sup>* th_prop th"
    "list_all2 (\<lambda>(t, u) (t', u'). ap (tab_inst instT) (tab_subst tt) t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and>
      ap (tab_inst instT) (tab_subst tt) u \<rightarrow>\<^sub>\<beta>\<^sup>* u') (th_tpairs th0) (th_tpairs th)"
proof -
  define f where "f = (if bt then inst_beta_m instT tt else inst_m instT tt)"
  define F where "F = (\<lambda>(t, u) (acc, i). case f t i of (t', i1) \<Rightarrow> case f u i1 of (u', i2) \<Rightarrow>
    (acc @ [(t' :: pterm, u')], i2))"
  note sh = instantiate_shape[OF ok ne, folded tt_def f_def F_def]
  have bT: "\<forall>x\<in>set instT. \<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x)" using cT by blast
  have bt: "\<forall>x\<in>set tt. ibelow (snd (snd x)) (fst (snd x))" using ct by (force simp: tt_def cterm_wf_def)
  show io: "cinst (tab_inst instT)" "wt_subst (tab_subst tt)"
    using instantiate_inst_ok[OF sh(1) sh(2)] cT ct unfolding tt_def by (force simp: cterm_wf_def)+
  show "okT (check_inst insts) ()" by (rule sh(2))
  note stp = instantiate_step[OF bT bt, where bt' = bt, folded f_def]
  show "ap (tab_inst instT) (tab_subst tt) (th_prop th0) \<rightarrow>\<^sub>\<beta>\<^sup>* th_prop th"
    using sh(3) stp[where i = "-1" and t = "th_prop th0"] by simp
  obtain ps where ps: "fst (fold F (th_tpairs th0) ([], snd (f (th_prop th0) (-1)))) = [] @ ps"
    and l: "list_all2 (\<lambda>(t, u) (t', u'). ap (tab_inst instT) (tab_subst tt) t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and>
      ap (tab_inst instT) (tab_subst tt) u \<rightarrow>\<^sub>\<beta>\<^sup>* u') (th_tpairs th0) ps"
    using fold_tpairs[of "\<lambda>t t'. ap (tab_inst instT) (tab_subst tt) t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" f "th_tpairs th0" "[]"
      "snd (f (th_prop th0) (-1))"] stp
    unfolding F_def by blast
  then show "list_all2 (\<lambda>(t, u) (t', u'). ap (tab_inst instT) (tab_subst tt) t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and>
      ap (tab_inst instT) (tab_subst tt) u \<rightarrow>\<^sub>\<beta>\<^sup>* u') (th_tpairs th0) (th_tpairs th)"
    using sh(4) by (simp add: F_def)
qed

lemma tpairs_ap:
  assumes "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and \<rho>: "cinst \<rho>" and \<sigma>: "wt_subst \<sigma>"
  shows "\<forall>(t, u)\<in>set (map (\<lambda>(t, u). (ap \<rho> \<sigma> t, ap \<rho> \<sigma> u)) tps). closed t \<and> closed u \<and>
    (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
proof (clarsimp)
  fix t u assume "(t, u) \<in> set tps"
  with assms(1) obtain T where c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
  have ca: "closed (ap \<rho> \<sigma> t)" "closed (ap \<rho> \<sigma> u)" using c \<sigma> by (simp_all add: closed_def ap_def wt_subst_def)
  have "e \<turnstile> ap \<rho> \<sigma> t : tsubst \<rho> T" "e \<turnstile> ap \<rho> \<sigma> u : tsubst \<rho> T" for e
    using typing_ap_inst[OF ty(1) cinstD(2)[OF \<rho>] \<sigma>] typing_ap_inst[OF ty(2) cinstD(2)[OF \<rho>] \<sigma>] ca typing_closed
    by blast+
  with ca show "closed (ap \<rho> \<sigma> t) \<and> closed (ap \<rho> \<sigma> u) \<and> (\<exists>T. \<forall>e. e \<turnstile> ap \<rho> \<sigma> t : T \<and> e \<turnstile> ap \<rho> \<sigma> u : T)"
    by blast
qed

end

lemma list_all2_map_beta:
  "list_all2 (\<lambda>(t, u) (t', u'). S t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> S u \<rightarrow>\<^sub>\<beta>\<^sup>* u') tps tps' \<Longrightarrow>
    list_all2 (\<lambda>(t, u) (t', u'). t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> u \<rightarrow>\<^sub>\<beta>\<^sup>* u') (map (\<lambda>(t, u). (S t, S u)) tps) tps'"
  unfolding list_all2_map1 by (erule list_all2_mono) (auto split: prod.splits)

lemma thm_ok_instantiate:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (instantiate (sg_alg (sign_of th)) bt (instT_of cTs) (insts_of cts) (rep_of th)) r"
    and ne: "\<not> (cTs = [] \<and> cts = [])"
    and sT0: "\<forall>(v, cT)\<in>set cTs. cty_sign (rep_ctyp cT) = sign_of th"
    and st0: "\<forall>(v, ct)\<in>set cts. csign_of ct = sign_of th"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th \<union> inst_sorts cTs cts) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)))
    (bindM (zproof_of th) (zinstantiate_proof (pure_sig.ztargs (sg_consts (sign_of th))) (inst_Ts cTs) (inst_ts cts))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th" and ?iT = "instT_of cTs" and ?is = "insts_of cts"
  have ne': "\<not> (?iT = [] \<and> ?is = [])" using ne by (simp add: instT_of_def insts_of_def)
  have ix: "list_all (\<lambda>x. 0 \<le> snd (fst (fst x))) ?iT" "list_all (\<lambda>x. 0 \<le> snd (fst (fst x))) ?is"
    using instantiate_shape(6,7)[OF ok ne'] .
  have sT: "\<forall>(v, cT)\<in>set cTs. cty_sign (rep_ctyp cT) = sign_of th \<and> snd (fst v) \<noteq> -1"
  proof (clarify, rule conjI)
    fix x i S cT assume m: "(((x, i), S), cT) \<in> set cTs"
    with sT0 show "cty_sign (rep_ctyp cT) = sign_of th" by auto
    from m have "(((x, i), S), (cty_T (rep_ctyp cT), cty_maxidx (rep_ctyp cT))) \<in> set ?iT"
      by (force simp: instT_of_def)
    with ix(1) have "0 \<le> i" by (auto simp: list_all_iff)
    then show "snd (fst ((x, i), S)) \<noteq> -1" by auto
  qed
  have st: "\<forall>(v, ct)\<in>set cts. csign_of ct = sign_of th \<and> snd (fst v) \<noteq> -1"
  proof (clarify, rule conjI)
    fix x i T ct assume m: "(((x, i), T), ct) \<in> set cts"
    with st0 show "csign_of ct = sign_of th" by auto
    from m have "(((x, i), T), (ct_t (crep_of ct), ct_T (crep_of ct), ct_maxidx (crep_of ct))) \<in> set ?is"
      by (force simp: insts_of_def)
    with ix(2) have "0 \<le> i" by (auto simp: list_all_iff)
    then show "snd (fst ((x, i), T)) \<noteq> -1" by auto
  qed
  have cTok: "\<forall>x\<in>set ?iT. cert_typ (sg_alg ?c) (sg_ar ?c) (fst (snd x)) \<and> tnn (fst (snd x)) \<and>
      (\<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x))" if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof
    fix x assume "x \<in> set ?iT"
    then obtain v cT where v: "(v, cT) \<in> set cTs" and x: "x = (v, (cty_T (rep_ctyp cT), cty_maxidx (rep_ctyp cT)))"
      by (auto simp: instT_of_def)
    with sT have s: "cty_sign (rep_ctyp cT) = ?c" by auto
    from pure_ctyp_ok[of cT] ps s show "cert_typ (sg_alg ?c) (sg_ar ?c) (fst (snd x)) \<and> tnn (fst (snd x)) \<and>
        (\<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x))"
      by (auto simp: x ctyp_ok_def tnn_def)
  qed
  have ctok: "\<forall>x\<in>set ?is. pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c)
      (CTerm (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x))))" if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof
    fix x assume "x \<in> set ?is"
    then obtain v ct where v: "(v, ct) \<in> set cts"
      and x: "x = (v, (ct_t (crep_of ct), ct_T (crep_of ct), ct_maxidx (crep_of ct)))"
      by (auto simp: insts_of_def)
    with st have s: "csign_of ct = ?c" by auto
    from pure_cterm_wf[of ct] ps s show "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c)
        (CTerm (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x))))"
      by (simp add: x)
  qed
  have sorts: "tsorts (fst (snd x)) \<subseteq> inst_sorts cTs cts" if "x \<in> set ?iT" for x
  proof -
    from that obtain v cT where v: "(v, cT) \<in> set cTs" and x: "x = (v, (cty_T (rep_ctyp cT), cty_maxidx (rep_ctyp cT)))"
      by (auto simp: instT_of_def)
    from pure_ctyp_ok[of cT] have "tsorts (cty_T (rep_ctyp cT)) \<subseteq> cty_sorts (rep_ctyp cT)" by (simp add: ctyp_ok_def)
    with v show ?thesis by (auto simp: x inst_sorts_def)
  qed
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using thm_wf_instantiate[OF ok ne' w0 cTok[OF ps] ctok[OF ps]] by simp
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps' by (simp add: thm_wf_def)
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid_in[of th M] M by simp
    have "valid (shyps_of th \<union> inst_sorts cTs cts) (hyps_of th) (th_tpairs r) (th_prop r)"
    proof (rule instantiate_valid[OF ok v wt])
      show "\<forall>((v, S), U, j)\<in>set ?iT. cert_typ (sg_alg ?c) (sg_ar ?c) U \<and> tsorts U \<subseteq> shyps_of th \<union> inst_sorts cTs cts"
        using cTok[OF ps'] sorts by fastforce
      show "\<forall>((v, T), u, U, j)\<in>set ?is. closed u \<and> (\<forall>e. e \<turnstile> u : U)"
        using ctok[OF ps'] by (fastforce simp: cterm_wf_def)
    qed simp
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have wP: "wtp (th_prop (rep_of th))" and H: "\<And>h. h \<in> set (hyps_of th) \<Longrightarrow> vars h = {} \<and> ttvars h = {}"
      and tw: "\<forall>(t, u)\<in>set (th_tpairs (rep_of th)). closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
      using w0 by (auto simp: thm_wf_def wt_thm_def)
    define tt where "tt = map (\<lambda>(v, (u, U, j)). (v, (u, j))) ?is"
    note rd = instantiate_reds[OF ok ne' cTok[OF ps] ctok[OF ps], folded tt_def]
    let ?\<rho> = "tab_inst ?iT" and ?\<sigma> = "tab_subst tt"
    have \<rho>0: "cinst (tab_inst (map (\<lambda>(v, T). (v, (T, -1))) (inst_Ts cTs)))" using rd(1) by (simp add: tab_inst_Ts)
    have \<sigma>0: "wt_subst (tab_subst (map (\<lambda>(v, t). (v, (t, -1))) (inst_ts cts)))"
      using rd(2) by (simp add: tab_subst_ts tt_def)
    have eqs: "tab_inst (map (\<lambda>(v, T). (v, (T, -1))) (inst_Ts cTs)) = ?\<rho>"
      "tab_subst (map (\<lambda>(v, t). (v, (t, -1))) (inst_ts cts)) = ?\<sigma>"
      by (simp_all add: tab_inst_Ts tab_subst_ts tt_def)
    have wS: "wtp (ap ?\<rho> ?\<sigma> (th_prop (rep_of th)))" by (rule wtp_ap[OF wP rd(1) rd(2)[folded gsubst_def]])
    note twS = tpairs_ap[OF tw rd(1) rd(2)]
    note lS = list_all2_map_beta[OF rd(5)]
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    have nn_ct: "pnn (ct_t (crep_of ct))" if "(v, ct) \<in> set cts" for v ct
      using ctok[OF ps] that by (force simp: insts_of_def cterm_wf_def pnn_iff')
    have cl_ct: "closed (ct_t (crep_of ct))" if "(v, ct) \<in> set cts" for v ct
      using ctok[OF ps] that by (force simp: insts_of_def cterm_wf_def)
    \<comment> \<open>the substitution of the classic proofs\<close>
    let ?\<sigma>r = "tab_subst (map (\<lambda>(v, t). (v, (remove_types t, -1))) (inst_ts cts))"
    have ip: "instantiate_proof (inst_Ts cTs) (inst_ts cts) w = map_proof_terms (\<lambda>t. vsubst ?\<sigma>r (inst ?\<rho> t)) (tsubst ?\<rho>) w"
      for w by (simp add: instantiate_proof_def inst_m_fst instT_m_fst Let_def flip: eqs(1))
    have \<sigma>r_cases: "?\<sigma>r x T = Var x T \<or> (\<exists>v ct. (v, ct) \<in> set cts \<and> ?\<sigma>r x T = remove_types (ct_t (crep_of ct)))"
      for x T
    proof (cases "lookup_var (map (\<lambda>(v, t). (v, (remove_types t, -1 :: integer))) (inst_ts cts)) (x, T)")
      case (Some r')
      then obtain t where t: "((x, T), t) \<in> set (inst_ts cts)" "r' = (remove_types t, -1)"
        by (auto dest: lookup_var_map_Some)
      then obtain v ct where "(v, ct) \<in> set cts" "t = ct_t (crep_of ct)" by (auto simp: inst_ts_def)
      moreover have "?\<sigma>r x T = remove_types t" using Some t(2) unfolding tab_subst_def by simp
      ultimately show ?thesis by blast
    next
      case None
      then have "?\<sigma>r x T = Var x T" unfolding tab_subst_def by simp
      then show ?thesis by blast
    qed
    have \<sigma>r: "w \<in> vars (?\<sigma>r x T) \<Longrightarrow> w = (x, T) \<or> 0 \<le> snd (fst w)" for w x T
      using \<sigma>r_cases[of x T] nn_ct by (auto simp: pnn_def)
    have \<sigma>rc: "closed_subst ?\<sigma>r"
      unfolding closed_subst_def
    proof (intro allI)
      fix x T show "closed (?\<sigma>r x T)" using \<sigma>r_cases[of x T] cl_ct by (auto simp: closed_def)
    qed
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)) = returnW pf"
      then obtain q where q: "proof_of th = returnW q" and pf: "pf = instantiate_proof (inst_Ts cTs) (inst_ts cts) q"
        by (auto simp: bindP_eq_returnP)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th))
          (map (\<lambda>(t, u). (ap ?\<rho> ?\<sigma> t, ap ?\<rho> ?\<sigma> u)) (th_tpairs (rep_of th))) pf (ap ?\<rho> ?\<sigma> (th_prop (rep_of th)))"
        using instantiate_proof_valid[OF vq(1) \<rho>0 \<sigma>0 H] unfolding pf eqs by (simp add: ap_def)
      then have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
        by (rule prf_valid_beta_reds[OF _ lS rd(4) wS twS])
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
        using vq(2) vars_vsubst_inst_nonneg[OF _ \<sigma>r]
        by (fastforce simp: pf ip prf_idx_def prf_terms_map_proof_terms)
      moreover have "prf_nolb 0 pf" unfolding pf ip
        by (rule prf_nolb_map[OF _ _ vq(3)]) (simp_all add: \<sigma>rc)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
    next
      fix z assume "bindM (zproof_of th) (zinstantiate_proof ztargs (inst_Ts cTs) (inst_ts cts)) = return z"
      then obtain q where q: "zproof_of th = return q" and z: "zinstantiate_proof ztargs (inst_Ts cTs) (inst_ts cts) q = return z"
        by (auto simp: bindZ_eq_returnZ)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
        using p q by (simp_all add: proofs_ok_def Let_def)
      have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
      have cz: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. zcanon T) (\<lambda>_. True) q"
      proof (rule zprf_all_mono[of zterm_ok ztyp_ok])
        show "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp add: zinv_def)
        fix t assume "zterm_ok t"
        then show "\<forall>(x, T)\<in>zvars t. zcanon T" using zterm_ok_zvars by (fastforce simp: ztyp_ok_def)
      qed simp
      have kT: "\<forall>((v, S), T)\<in>set (inst_Ts cTs). snd v \<noteq> -1 \<and> tnoneg T"
        using sT cTok[OF ps] by (fastforce simp: inst_Ts_def instT_of_def intro: tnn_tnoneg)
      have kt: "\<forall>((v, T), t)\<in>set (inst_ts cts). snd v \<noteq> -1 \<and> tnoneg T \<and> noneg t"
      proof (clarsimp simp: inst_ts_def)
        fix x i T ct assume m: "(((x, i), T), ct) \<in> set cts"
        with st have i: "i \<noteq> -1" by auto
        from m have mi: "(((x, i), T), (ct_t (crep_of ct), ct_T (crep_of ct), ct_maxidx (crep_of ct))) \<in> set ?is"
          by (force simp: insts_of_def)
        have TU: "T = ct_T (crep_of ct)" by (rule check_inst_eq'[OF rd(3) mi])
        from ctok[OF ps] mi have wf: "cterm_wf (CTerm (ct_t (crep_of ct)) (ct_T (crep_of ct)) (ct_maxidx (crep_of ct)))"
          by force
        then have "tvars (ct_T (crep_of ct)) \<subseteq> ttvars (ct_t (crep_of ct))"
          by (intro typing_tvars_closed) (auto simp: cterm_wf_def)
        with wf have "tnn T" by (force simp: TU cterm_wf_def tnn_def)
        moreover have "pnn (ct_t (crep_of ct))" using nn_ct m by blast
        ultimately show "i \<noteq> -1 \<and> tnoneg T \<and> noneg (ct_t (crep_of ct))" using i tnn_tnoneg pnn_noneg by blast
      qed
      have "zvalid (sg_ax ?c) (set (hyps_of th)) (map (\<lambda>(t, u). (ap ?\<rho> ?\<sigma> t, ap ?\<rho> ?\<sigma> u)) (th_tpairs (rep_of th))) z
          (ap ?\<rho> ?\<sigma> (th_prop (rep_of th)))"
        using zinstantiate_proof_valid[OF vq(1) \<rho>0 \<sigma>0 H kT kt cz zc z] unfolding eqs by (simp add: ap_def)
      then have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
        by (rule zvalid_beta_reds[OF _ lS rd(4) wS twS])
      moreover have "zinv z \<and> znolb 0 z \<and> zhyps z = zhyps q"
      proof -
        let ?ty = "zsubst_type (map_of (map (\<lambda>(v, T). (v, ztyp_of T)) (inst_Ts cTs)))"
        from z obtain zinst where zi0: "mapM (\<lambda>((v, T), t). do {t' \<leftarrow> zterm_of ztargs t; return ((v, ztyp_of T), t')})
            (inst_ts cts) = return zinst"
          and m: "map_zproof ?ty (\<lambda>t. return (zsubst_term ?ty (lookup_zvar zinst) t)) q = return z"
          by (auto simp: zinstantiate_proof_def bindZ_eq_returnZ Let_def)
        have zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ztargs t = return t' \<and> e = ((v, ztyp_of T), t'))
            (inst_ts cts) zinst"
          using zi0[unfolded mapZ_eq_returnZ] by (rule list_all2_mono) (auto simp: bindZ_eq_returnZ split: prod.splits)
        have zv: "zterm_ok u \<and> \<not> zloose u 0" if "lookup_zvar zinst w = Some u" for w u
        proof -
          from lookup_zvar_SomeD[OF that] have "(w, u) \<in> set zinst" .
          then obtain i where i: "i < length zinst" "zinst ! i = (w, u)" by (auto simp: in_set_conv_nth)
          have il: "i < length (inst_ts cts)" using i(1) list_all2_lengthD[OF zi] by simp
          obtain vT t where vt: "inst_ts cts ! i = (vT, t)" by (cases "inst_ts cts ! i")
          from list_all2_nthD[OF zi il] vt i(2) have zt: "zterm_of ztargs t = return u" by (cases vT) auto
          from nth_mem[OF il] vt obtain v ct where "(v, ct) \<in> set cts" "t = ct_t (crep_of ct)"
            by (auto simp: inst_ts_def)
          with nn_ct cl_ct have "pnn t" "closed t" by blast+
          then show ?thesis using zterm_ok_zterm_of_pnn[OF zt] zloose_zterm_of[OF zt] by (simp add: closed_def)
        qed
        have ft: "ztyp_ok U" if "map_of (map (\<lambda>(v, T). (v, ztyp_of T)) (inst_Ts cTs)) vS = Some U" for vS U
        proof -
          from map_of_SomeD[OF that] obtain T where "(vS, T) \<in> set (inst_Ts cTs)" "U = ztyp_of T" by auto
          with cTok[OF ps] show ?thesis by (force simp: inst_Ts_def instT_of_def intro: ztyp_ok_ztyp_of)
        qed
        have tok: "ztyp_ok (?ty T)" if "ztyp_ok T" for T by (rule ztyp_ok_zsubst_type[OF that ft])
        have "zinv z" by (rule zinv_map_zproof[OF m vq(2) tok]) (use tok zv in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
        moreover have "znolb 0 z"
        proof -
          have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term ?ty (lookup_zvar zinst) t) k"
            using zloose_zsubst_term zv by blast
          show ?thesis by (rule znolb_map_zproof[OF m zc _ _ vq(3)]) (use zl in auto)
        qed
        ultimately show ?thesis using zhyps_map_zproof[OF m] by simp
      qed
      ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
          zhyps_ok z" using vq(4) by (simp add: zhyps_ok_def)
    qed
  qed
qed

theorem instantiate_thm:
  assumes "instantiate_thm bt cTs cts th = Some th'" and "\<not> (cTs = [] \<and> cts = [])"
  obtains r where "okT (instantiate (sg_alg (sign_of th)) bt (instT_of cTs) (insts_of cts) (rep_of th)) r"
    "rep_thm th' = solve_data (mk_thm r (shyps_of th \<union> inst_sorts cTs cts) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)))
      (bindM (zproof_of th) (zinstantiate_proof (pure_sig.ztargs (sg_consts (sign_of th))) (inst_Ts cTs) (inst_ts cts))))"
proof -
  from assms obtain r where sT: "\<forall>(v, cT)\<in>set cTs. cty_sign (rep_ctyp cT) = sign_of th"
    and st: "\<forall>(v, ct)\<in>set cts. csign_of ct = sign_of th"
    and ok: "okT (instantiate (sg_alg (sign_of th)) bt (instT_of cTs) (insts_of cts) (rep_of th)) r"
    and th': "th' = Abs_thm (solve_data (mk_thm r (shyps_of th \<union> inst_sorts cTs cts) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)))
      (bindM (zproof_of th) (zinstantiate_proof (pure_sig.ztargs (sg_consts (sign_of th))) (inst_Ts cTs) (inst_ts cts)))))"
    by (auto simp: instantiate_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok]) (unfold th', rule rep_Abs_thm, rule thm_ok_solve_data, rule thm_ok_instantiate[OF ok assms(2) sT st], simp)
qed

end
