section \<open>Proofs: Thm_Bicompose\<close>

theory Thm_Bicompose_Proofs
  imports "Thm_Soundness.Thm_Bicompose" Thm_Axiom_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Bicompose\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

context prf_sig_gen
begin

theorem bicompose_thm_proof_valid:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (pthm_of state)
      (stpairs, Bs, Bi, C) False eres_flg (pthm_of rule) nsubgoal) xq"
    and rx: "bresult (unify_ops cfg vl) xq x" and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv0 (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and ru: "thm_inv0 (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and tv: "scons (tvars_thm (th_tpairs state) (th_prop state) \<union> tvars_thm (th_tpairs rule) (th_prop rule))"
    and nm: "bc_names incremented (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule)) x"
    and sp: "prf_valid ax (set hs) (th_tpairs state) sprf (th_prop state)" "prf_idx (\<lambda>i. 0 \<le> i) sprf"
      "prf_nolb 0 sprf"
    and rp: "prf_valid ax (set hr) (th_tpairs rule) rprf (th_prop rule)" "prf_idx (\<lambda>i. 0 \<le> i) rprf"
      "prf_nolb 0 rprf"
    and p: "bc_proof state i eres_flg flatten x rprf sprf = returnW p"
  shows "prf_valid ax (set (hs @ hr)) (br_tpairs x) p (br_prop x) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
proof -
  obtain rAs B env where tp: "stpairs = th_tpairs state" and SP: "th_prop state = list_implies (Bs @ [Bi]) C"
    and P: "th_prop rule = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B)"
    and rc: "rchar (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B) x"
    and bi: "bres_inv x"
    by (rule bicompose_setup[OF d ok rx cfg vl st ru tv nm]) blast
  let ?smax = "th_maxidx state"
  have some: "(SOME d. okT (dest_state state i) d) = (stpairs, Bs, Bi, C)" using d by (blast intro: okT_det)
  have ws: "wt_thm ?smax hs stpairs (list_implies (Bs @ [Bi]) C)" using st tp SP by (simp add: thm_inv0_def)
  have wr: "wt_thm (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)" using ru by (simp add: thm_inv0_def)
  have p': "bicompose_proof (br_env x) ?smax flatten Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
      (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1)
      (ren_prf (na_ren (br_newas x)) rprf) sprf = returnW p"
    using p by (simp add: bc_proof_def some bres_proof_sel bres_nlift_def)
  note bp = bres_inv_props[OF bi]
  have "prf_valid ax (set (hs @ hr)) (br_tpairs x) p (br_prop x)"
  proof (rule bicompose_proof_valid[OF HOL.refl rc pa _ _ _ _ _ _ _ _ vl p'])
    show "prf_valid ax (set hs) stpairs sprf (list_implies (Bs @ [Bi]) C)" using sp(1) tp SP by simp
    show "wtp (list_implies (Bs @ [Bi]) C)" "ibelow ?smax (list_implies (Bs @ [Bi]) C)"
      "\<forall>(t, u)\<in>set stpairs. ibelow ?smax t \<and> ibelow ?smax u"
      using ws by (auto simp: wt_thm_def)
    show "prf_valid ax (set hr) (th_tpairs rule) rprf (list_implies (rev rAs) B)" using rp(1) P by simp
    show "wtp (list_implies (rev rAs) B)" using wr P by (simp add: wt_thm_def)
  qed simp_all
  moreover have "prf_idx (\<lambda>i. 0 \<le> i) p"
    by (rule prf_idx_bicompose_proof[OF p' _ sp(2)]) (use rp(2) bp in \<open>simp_all add: prf_idx_ren_prf\<close>)
  moreover have "prf_nolb 0 p"
  proof -
    have "prf_nolb 0 (ren_prf (na_ren (br_newas x)) rprf)"
      using rp(3) by (auto simp: ren_prf_def split: option.splits intro: prf_nolb_map)
    then show ?thesis by (rule prf_nolb_bicompose_proof[OF p' _ sp(3) bp(4) bp(5) bp(3)])
  qed
  ultimately show ?thesis by blast
qed

theorem bicompose_thm_zproof_valid:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (pthm_of state)
      (stpairs, Bs, Bi, C) False eres_flg (pthm_of rule) nsubgoal) xq"
    and rx: "bresult (unify_ops cfg vl) xq x" and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv0 (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and ru: "thm_inv0 (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and tv: "scons (tvars_thm (th_tpairs state) (th_prop state) \<union> tvars_thm (th_tpairs rule) (th_prop rule))"
    and nm: "bc_names incremented (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule)) x"
    and sp: "zvalid ax (set hs) (th_tpairs state) sprf (th_prop state)" "zinv sprf" "znolb 0 sprf"
    and rp: "zvalid ax (set hr) (th_tpairs rule) rprf (th_prop rule)" "zinv rprf" "znolb 0 rprf"
    and p: "bc_zproof ztargs state i eres_flg flatten rule x rprf sprf = return p"
  shows "zvalid ax (set (hs @ hr)) (br_tpairs x) p (br_prop x) \<and> zinv p \<and> znolb 0 p \<and>
    zhyps p \<subseteq> zhyps sprf \<union> zhyps rprf"
proof -
  obtain rAs B env where tp: "stpairs = th_tpairs state" and SP: "th_prop state = list_implies (Bs @ [Bi]) C"
    and P: "th_prop rule = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B)"
    and rc: "rchar (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B) x"
    and bi: "bres_inv x" and bA: "\<forall>C'. br_A x = Some C' \<longrightarrow> C' \<in> set (rev rAs)"
    by (rule bicompose_setup[OF d ok rx cfg vl st ru tv nm]) blast
  let ?smax = "th_maxidx state"
  have some: "(SOME d. okT (dest_state state i) d) = (stpairs, Bs, Bi, C)" using d by (blast intro: okT_det)
  note bp = bres_inv_props[OF bi]
  have ws: "wt_thm ?smax hs stpairs (list_implies (Bs @ [Bi]) C)" using st tp SP by (simp add: thm_inv0_def)
  have wr: "wt_thm (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)" using ru by (simp add: thm_inv0_def)
  have sm: "-1 \<le> ?smax" using st by (simp add: thm_inv0_def)
  from p obtain rprf' vis
    where rr: "(case na_ren (br_newas x) of None \<Rightarrow> return rprf | Some r \<Rightarrow> zren_proof r ?smax rprf) = return rprf'"
    and vz: "liftMZ (mapM (\<lambda>th. full_prop_of (th_tpairs th) (th_prop th)) [state, rule]) = return vis"
    and zb: "zbicompose_proof ztargs (br_env x) ?smax flatten Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
      (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) vis rprf' sprf = return p"
    by (auto simp: bc_zproof_def some bres_zproof_sel bindZ_eq_returnZ bres_nlift_def)
  have rren: "case na_ren (br_newas x) of None \<Rightarrow> rprf' = rprf | Some rn \<Rightarrow> zren_proof rn ?smax rprf = return rprf'"
    using rr by (cases "na_ren (br_newas x)") auto
  have zri: "zinv rprf'" using rren rp(2) by (cases "na_ren (br_newas x)") (auto intro: zinv_zren_proof)
  have zrc: "zconsts_ok rprf" using rp(2) by (simp add: zinv_def)
  have rren2: "(znolb 0 rprf \<longrightarrow> znolb 0 rprf') \<and> zhyps rprf' = zhyps rprf \<and> zconsts_ok rprf'"
  proof (cases "na_ren (br_newas x)")
    case None
    with rr zrc show ?thesis by simp
  next
    case (Some rn)
    with rr have zr: "zren_proof rn ?smax rprf = return rprf'" by simp
    have "znolb 0 rprf'" if "znolb 0 rprf"
      by (rule znolb_map_zproof[OF zr[unfolded zren_proof_def] zrc _ _ that]) auto
    with zhyps_map_zproof[OF zr[unfolded zren_proof_def]] map_zproof_zconsts_ok[OF zr[unfolded zren_proof_def] zrc]
    show ?thesis by blast
  qed
  text \<open>The visible propositions:\<close>
  from vz obtain fs fl where vis: "vis = [fs, fl]" and fs: "ok (full_prop_of (th_tpairs state) (th_prop state)) fs"
    and fl: "ok (full_prop_of (th_tpairs rule) (th_prop rule)) fl"
    by (auto simp: liftMZ_eq_returnZ ok_mapM list_all2_Cons1)
  note fS = thm_inv0_full_prop_of[OF st fs] and fL = thm_inv0_full_prop_of[OF ru fl]
  have pv: "\<forall>t\<in>set vis. pnn t" using fS(1) fL(1) by (simp add: vis)
  note vp = visible_pnn[OF pv]
  have tvis: "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm (th_tpairs rule) (list_implies (rev rAs) B)
      \<subseteq> set (visible_tvars vis)"
  proof -
    have "set (visible_tvars vis) = ttvars fs \<union> ttvars fl" using vp(3) by (simp add: vis)
    with fS(2) fL(2) tp SP P show ?thesis by auto
  qed
  have pS: "pnn (list_implies (Bs @ [Bi]) C)" using thm_inv0_pnn(1)[OF st] SP by simp
  have pP: "pnn (th_prop rule)" by (rule thm_inv0_pnn(1)[OF ru])
  have "zvalid ax (set (hs @ hr)) (br_tpairs x) p (br_prop x)"
  proof (rule zbicompose_proof_valid[OF HOL.refl rc pa _ _ _ _ _ _ _ _ _ _ vl _ rren _ _ _ _ bp(2) _ _ _ zb])
    show "zvalid ax (set hs) stpairs sprf (list_implies (Bs @ [Bi]) C)" using sp(1) tp SP by simp
    show "wtp (list_implies (Bs @ [Bi]) C)" "ibelow ?smax (list_implies (Bs @ [Bi]) C)"
      "\<forall>(t, u)\<in>set stpairs. ibelow ?smax t \<and> ibelow ?smax u"
      using ws by (auto simp: wt_thm_def)
    show "zvalid ax (set hr) (th_tpairs rule) rprf (list_implies (rev rAs) B)" using rp(1) P by simp
    show "wtp (list_implies (rev rAs) B)" using wr P by (simp add: wt_thm_def)
    show "False \<Longrightarrow> lifted_rule ?smax Bi (rev rAs) B" by simp
    show "noneg (list_implies (rev rAs) B)" using pP P by (simp add: pnn_noneg)
    show "noneg (list_implies (Bs @ [Bi]) C)" using pS by (simp add: pnn_noneg)
    show "\<forall>A\<in>set (na_As (br_newas x) @ na_oldAs (br_newas x)). noneg A" using bp(7) by (simp add: pnn_noneg)
    show "-1 \<le> ?smax" by (rule sm)
    show "vis \<noteq> []" by (simp add: vis)
    show "\<forall>(x, T)\<in>set (visible_vars vis). snd x \<noteq> -1" using vp(1) by (fastforce simp: integer_nonneg_ne_m1)
    show "\<forall>(v, S)\<in>set (visible_tvars vis). snd v \<noteq> -1" using vp(2) by (fastforce simp: integer_nonneg_ne_m1)
    show "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm (th_tpairs rule) (list_implies (rev rAs) B)
        \<subseteq> set (visible_tvars vis)" by (rule tvis)
    show "\<forall>h\<in>set (hs @ hr). closed h" using ws wr by (auto simp: wt_thm_def dest: wtpD(1))
    show "zconsts_ok sprf" using sp(2) by (simp add: zinv_def)
    show "zconsts_ok rprf" by (rule zrc)
  qed
  moreover have "zinv p"
  proof (rule zinv_zbicompose_proof[OF zb zri sp(2) bp(3) bp(1) vp(1,2)])
    show "\<forall>t\<in>set (Bs @ na_As (br_newas x) @ na_oldAs (br_newas x)). pnn t"
      using bp(7) pS by (auto simp: pnn_list_implies)
    show "\<forall>C'. br_A x = Some C' \<longrightarrow> pnn C'" using bA pP P by (auto simp: pnn_list_implies)
  qed
  moreover have "znolb 0 p \<and> zhyps p \<subseteq> zhyps sprf \<union> zhyps rprf"
  proof -
    have wS: "wtp (list_implies (Bs @ [Bi]) C)" using ws by (simp add: wt_thm_def)
    have wP: "wtp (list_implies (rev rAs) B)" using wr P by (simp add: wt_thm_def)
    have cl: "\<forall>t\<in>set (Bs @ na_As (br_newas x) @ na_oldAs (br_newas x)). closed t"
      using bp(8) wtp_list_implies_mem[OF wS] by (auto dest: wtpD(1))
    have clA: "\<forall>C'. br_A x = Some C' \<longrightarrow> closed C'"
      using bA wtp_list_implies_mem[OF wP] by (auto dest: wtpD(1))
    note zbc = zbicompose_proof_closed[OF zb conjunct2[OF conjunct2[OF rren2]] _ bp(3) bp(5) cl clA]
    have "zconsts_ok sprf" using sp(2) by (simp add: zinv_def)
    with zbc rren2 rp(3) sp(3) show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed

end

context prf_sig
begin

text \<open>Without loose names:\<close>

theorem bicompose_thm_proof_valid:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (pthm_of state)
      (stpairs, Bs, Bi, C) False eres_flg (pthm_of rule) nsubgoal) xq"
    and rx: "bresult (unify_ops cfg vl) xq x" and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv0 (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and ru: "thm_inv0 (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and tv: "scons (tvars_thm (th_tpairs state) (th_prop state) \<union> tvars_thm (th_tpairs rule) (th_prop rule))"
    and vc: "incremented \<Longrightarrow>
      vtcons (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule))"
    and sp: "prf_valid ax (set hs) (th_tpairs state) sprf (th_prop state)" "prf_idx (\<lambda>i. 0 \<le> i) sprf"
      "prf_nolb 0 sprf"
    and rp: "prf_valid ax (set hr) (th_tpairs rule) rprf (th_prop rule)" "prf_idx (\<lambda>i. 0 \<le> i) rprf"
      "prf_nolb 0 rprf"
    and p: "bc_proof state i eres_flg flatten x rprf sprf = returnW p"
  shows "prf_valid ax (set (hs @ hr)) (br_tpairs x) p (br_prop x) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
proof -
  have nm: "bc_names incremented (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule)) x"
    using vc by (simp add: bc_names_iff)
  show ?thesis by (rule bicompose_thm_proof_valid[OF d ok rx cfg vl st ru tv nm sp rp p])
qed

theorem bicompose_thm_zproof_valid:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (pthm_of state)
      (stpairs, Bs, Bi, C) False eres_flg (pthm_of rule) nsubgoal) xq"
    and rx: "bresult (unify_ops cfg vl) xq x" and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv0 (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and ru: "thm_inv0 (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and tv: "scons (tvars_thm (th_tpairs state) (th_prop state) \<union> tvars_thm (th_tpairs rule) (th_prop rule))"
    and vc: "incremented \<Longrightarrow>
      vtcons (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule))"
    and sp: "zvalid ax (set hs) (th_tpairs state) sprf (th_prop state)" "zinv sprf" "znolb 0 sprf"
    and rp: "zvalid ax (set hr) (th_tpairs rule) rprf (th_prop rule)" "zinv rprf" "znolb 0 rprf"
    and p: "bc_zproof ztargs state i eres_flg flatten rule x rprf sprf = return p"
  shows "zvalid ax (set (hs @ hr)) (br_tpairs x) p (br_prop x) \<and> zinv p \<and> znolb 0 p \<and>
    zhyps p \<subseteq> zhyps sprf \<union> zhyps rprf"
proof -
  have nm: "bc_names incremented (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule)) x"
    using vc by (simp add: bc_names_iff)
  show ?thesis by (rule bicompose_thm_zproof_valid[OF d ok rx cfg vl st ru tv nm sp rp p])
qed

end


lemma proofs_ok_thm_of_bc:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and vc: "incremented \<Longrightarrow> bc_vcons state rule"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and rx: "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
    and po_rule: "is_prf_sig (sign_of rule) \<Longrightarrow> proofs_ok (rep_thm rule)"
  shows "proofs_ok (thm_of_bc (sign_of state) i (state :: 'u pure_thm) flatten e rule x)"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  note a = bc_args[OF ps sr sc vc]
  note st = a(1) and ru = a(2) and tv = a(3) and vc' = a(4)
  obtain rAs B env where tp: "stpairs = th_tpairs (rep_of state)"
    and SP: "th_prop (rep_of state) = list_implies (Bs @ [Bi]) C"
    and ti: "thm_inv (maxidx (br_env x)) (hyps_of state @ hyps_of rule) (br_tpairs x) (br_prop x)"
    by (rule bicompose_setup[OF d ok rx cfg vl a]) blast
  interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def)
  have ps: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have pr: "proofs_ok (rep_thm rule)" by (rule po_rule) (simp add: sr psig)
  have sg_eq: "th_sign (thm_of_bc ?c i state flatten e rule x) = ?c" by (simp add: thm_of_bc_def)
  show ?thesis unfolding proofs_ok_def Let_def sg_eq
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof (thm_of_bc ?c i state flatten e rule x) = returnW p"
    then obtain rp sp where rp: "proof_of rule = returnW rp" and sp: "proof_of state = returnW sp"
      and p: "bc_proof (rep_of state) i e flatten x rp sp = returnW p"
      by (auto simp: thm_of_bc_def bindP_eq_returnP)
    have "prf_valid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) p (br_prop x) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (rule bicompose_thm_proof_valid[OF d ok rx cfg vl st ru tv vc' _ _ _ _ _ _ p])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    then show "prf_valid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) p
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_bc_def)
  next
    fix z assume "th_zproof (thm_of_bc ?c i state flatten e rule x) = return z"
    then obtain rp sp where rp: "zproof_of rule = return rp" and sp: "zproof_of state = return sp"
      and z: "bc_zproof ztargs (rep_of state) i e flatten (rep_of rule) x rp sp = return z"
      by (auto simp: thm_of_bc_def bindZ_eq_returnZ)
    have zs: "zinv sp" "znolb 0 sp" "zhyps_ok sp" "zinv rp" "znolb 0 rp" "zhyps_ok rp"
      using ps sp pr rp sr by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) z (br_prop x) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      by (rule bicompose_thm_zproof_valid[OF d ok rx cfg vl st ru tv vc' _ zs(1,2) _ zs(4,5) z])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    moreover have "zhyps_ok z" if "zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      using that zs(3,6) by (auto simp: zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) z
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: thm_of_bc_def)
  qed
qed

lemma proofs_ok_thm_of_bc_gen:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and rx: "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
    and po_rule: "is_prf_sig (sign_of rule) \<Longrightarrow> proofs_ok (rep_thm rule)"
  shows "proofs_ok (thm_of_bc (sign_of state) i (state :: 'u pure_thm) flatten e rule x)"
proof -
  let ?c = "sign_of state"
  let ?X = "pure_sig_gen.vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
    pure_sig_gen.vars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
  let ?V = "\<Union>A\<in>set (na_As (br_newas x)). vars A"
  let ?L = "bc_clash state rule x"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have tv: "scons (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      tvars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"
    using sc by (simp add: bc_scons_def)
  then have s1: "scons (tvars_thm (th_tpairs (rep_thm state)) (th_prop (rep_thm state)))"
    and s2: "scons (tvars_thm (th_tpairs (rep_thm rule)) (th_prop (rep_thm rule)))"
    by (auto simp: scons_def)
  have st: "thm_inv0 (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps s1] by simp
  have ru: "thm_inv0 (th_maxidx (rep_of rule)) (hyps_of rule) (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
    using pure_thm_inv0[of rule] ps s2 sr by simp
  have h1: "?L = {} \<Longrightarrow> vtcons ?X" by (fastforce simp: bc_clash_def vclash_def vtcons_def)
  have h3: "lvtcons (?X \<union> ?V)" by (rule lvtcons_vclash) (simp add: bc_clash_def)
  have h4: "?L \<subseteq> fst ` (?X \<union> ?V)" by (force simp: bc_clash_def vclash_def)
  have nm: "bc_names incremented ?X x" unfolding bc_names_def using h1 h3 h4 by blast
  have vc': "incremented \<Longrightarrow> lvtcons ?X" using bc_names_inc[OF nm] .
  obtain rAs B env where tp: "stpairs = th_tpairs (rep_of state)"
    and SP: "th_prop (rep_of state) = list_implies (Bs @ [Bi]) C"
    and ti: "thm_inv (maxidx (br_env x)) (hyps_of state @ hyps_of rule) (br_tpairs x) (br_prop x)"
    by (rule bicompose_setup[OF d ok rx cfg vl st ru tv nm]) blast
  interpret prf_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def prf_sig_gen_of)
  have ps: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have pr: "proofs_ok (rep_thm rule)" by (rule po_rule) (simp add: sr psig)
  have sg_eq: "th_sign (thm_of_bc ?c i state flatten e rule x) = ?c" by (simp add: thm_of_bc_def)
  show ?thesis unfolding proofs_ok_def Let_def sg_eq
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof (thm_of_bc ?c i state flatten e rule x) = returnW p"
    then obtain rp sp where rp: "proof_of rule = returnW rp" and sp: "proof_of state = returnW sp"
      and p: "bc_proof (rep_of state) i e flatten x rp sp = returnW p"
      by (auto simp: thm_of_bc_def bindP_eq_returnP)
    have "prf_valid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) p (br_prop x) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (rule bicompose_thm_proof_valid[OF d ok rx cfg vl st ru tv nm _ _ _ _ _ _ p])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    then show "prf_valid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) p
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_bc_def)
  next
    fix z assume "th_zproof (thm_of_bc ?c i state flatten e rule x) = return z"
    then obtain rp sp where rp: "zproof_of rule = return rp" and sp: "zproof_of state = return sp"
      and z: "bc_zproof ztargs (rep_of state) i e flatten (rep_of rule) x rp sp = return z"
      by (auto simp: thm_of_bc_def bindZ_eq_returnZ)
    have zs: "zinv sp" "znolb 0 sp" "zhyps_ok sp" "zinv rp" "znolb 0 rp" "zhyps_ok rp"
      using ps sp pr rp sr by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) z (br_prop x) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      by (rule bicompose_thm_zproof_valid[OF d ok rx cfg vl st ru tv nm _ zs(1,2) _ zs(4,5) z])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    moreover have "zhyps_ok z" if "zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      using that zs(3,6) by (auto simp: zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) z
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: thm_of_bc_def)
  qed
qed

end
