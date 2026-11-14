section \<open>Composition of theorems with arbitrary flags\<close>

theory Thm_Bicompose
  imports Thm_Cterm
begin

text \<open>
  \<open>Thm.bicompose flags (eres_flg, orule, nsubgoal) i state\<close> composes the rule with subgoal \<open>i\<close>
  of the proof state without lifting the rule (\<open>bicompose_aux\<close> with \<open>lifted = false\<close>), for
  arbitrary \<open>flatten\<close>, \<open>match\<close>, \<open>incremented\<close>, \<open>eres_flg\<close> and \<open>nsubgoal\<close>. The type variables
  of the two theorems are required to have one sort for each name. If \<open>incremented\<close> is true,
  their variables are required to have one type for each name as well; if it is false,
  \<open>Thm.bicompose\<close> unifies the types of the variables of the same name (\<open>unify_var_types\<close>),
  and no condition on the names of the variables is needed.
\<close>

context pure_sig
begin

lemma full_prop_of_ex:
  assumes "\<forall>(t, u)\<in>set tps. closed t \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T)"
  shows "\<exists>p. ok (full_prop_of tps P) p"
proof -
  have "\<exists>eqs. mapM mk_equals tps = return eqs" using assms
  proof (induction tps)
    case (Cons tu tps)
    obtain t u where tu: "tu = (t, u)" by (cases tu)
    from Cons.prems obtain T where t: "closed t" "\<And>e. e \<turnstile> t : T" by (auto simp: tu)
    have "fastype_of t = return T" using fastype_closed[OF t(2) t(1)] by (simp add: fastype_of_def)
    then have "mk_equals tu = return (Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u)"
      by (simp add: mk_equals_def tu)
    with Cons.IH Cons.prems show ?case by auto
  qed (simp add: return_def)
  then show ?thesis by (auto simp: full_prop_of_def return_def)
qed

lemma thm_wf_full_prop_of_ex: "thm_wf m hs tps P \<Longrightarrow> \<exists>p. ok (full_prop_of tps P) p"
  by (rule full_prop_of_ex) (fastforce simp: thm_wf_def wt_thm_def)


subsection \<open>The setting of a result\<close>

lemma bicompose_setup:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (pthm_of state)
      (stpairs, Bs, Bi, C) False eres_flg (pthm_of rule) nsubgoal) xq"
    and rx: "bresult (unify_ops cfg vl) xq x" and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv0 (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and ru: "thm_inv0 (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and tv: "scons (tvars_thm (th_tpairs state) (th_prop state) \<union> tvars_thm (th_tpairs rule) (th_prop rule))"
    and vc: "incremented \<Longrightarrow>
      vtcons (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule))"
  obtains rAs B env where "stpairs = th_tpairs state" "th_prop state = list_implies (Bs @ [Bi]) C"
    "th_prop rule = list_implies (rev rAs) B"
    "pinv_all (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B)"
    "rchar (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B) x"
    "thm_inv (maxidx (br_env x)) (hs @ hr) (br_tpairs x) (br_prop x)" "bres_inv x"
    "\<forall>C'. br_A x = Some C' \<longrightarrow> C' \<in> set (rev rAs)"
proof -
  let ?smax = "th_maxidx state" and ?S = "list_implies (Bs @ [Bi]) C"
  note ds = okT_dest_state[OF d]
  have ws0: "wt_thm ?smax hs (th_tpairs state) (th_prop state)" using st by (simp add: thm_inv0_def)
  have SP: "th_prop state = ?S"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF conjunct1[OF ws0[unfolded wt_thm_def]], of "\<lambda>_. propT"]]
    by simp
  have tp: "stpairs = th_tpairs state" by (rule ds(1))
  have sS: "thm_inv0 ?smax hs stpairs ?S" using st tp SP by simp
  have ws: "wt_thm ?smax hs stpairs ?S" using sS by (simp add: thm_inv0_def)
  have wr: "wt_thm (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)" using ru by (simp add: thm_inv0_def)
  have tv': "scons (tvars_thm stpairs ?S \<union> tvars_thm (th_tpairs rule) (th_prop rule))" using tv tp SP by simp
  have vc': "incremented \<Longrightarrow> vtcons (vars_thm stpairs ?S \<union> vars_thm (th_tpairs rule) (th_prop rule))"
    using vc tp SP by simp
  have ok1: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (?smax, stpairs, ?S)
      (stpairs, Bs, Bi, C) False eres_flg (th_maxidx rule, th_tpairs rule, th_prop rule) nsubgoal) xq"
    using ok tp SP by (simp add: pthm_of_def)
  have lo: "False \<Longrightarrow> lifted_over ?smax Bi (th_prop rule) nsubgoal" by simp
  obtain rAs B env where P: "th_prop rule = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env flatten match_flg ?smax stpairs Bs Bi C False eres_flg (th_tpairs rule) rAs B)"
    and rc: "rchar (call_spec cfg vl env flatten match_flg ?smax stpairs Bs Bi C False eres_flg (th_tpairs rule) rAs B) x"
    by (rule bicompose_aux_rchar[OF ok1 rx cfg ws wr lo tv' vc']) blast
  have ti: "thm_inv (maxidx (br_env x)) (hs @ hr) (br_tpairs x) (br_prop x) \<and> bres_inv x"
    by (rule bicompose_aux_thm_inv_gen[OF ok1 rx cfg sS ru lo tv' vc' vl])
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (B, Bi)"
  define ctx where "ctx = BCtx flatten match_flg False ?smax Bs Bi C (th_tpairs rule) nlift BBi
    (BBi # th_tpairs rule @ stpairs)"
  have sp': "call_spec cfg vl env flatten match_flg ?smax stpairs Bs Bi C False eres_flg (th_tpairs rule) rAs B =
      BSpec cfg vl env ctx rAs eres_flg"
    by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have bA: "\<forall>C'. br_A x = Some C' \<longrightarrow> C' \<in> set (rev rAs)"
  proof (rule rchar_data[OF sp' ctx_def nlift_def rc])
    fix A1o na tus env' tps Pre As0 dps tps1 and n :: integer
    assume ad: "okT (addth ctx A1o na (env', tps)) x" and rAs: "rev rAs = Pre @ As0"
      and A1o: "Pre = [] \<and> A1o = None \<and> n = 0 \<or> (\<exists>A1. Pre = [A1] \<and> A1o = Some A1 \<and> 1 \<le> n)"
    have "br_A x = A1o" using ad by (cases rule: addth_cases) auto
    with A1o rAs show ?thesis by auto
  qed
  show thesis by (rule that[OF tp SP P pa rc conjunct1[OF ti] conjunct2[OF ti] bA])
qed

end


subsection \<open>The proofs\<close>

definition bc_proof :: "thm_rep \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bres \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf P" where
  "bc_proof st i e flatten x rp sp = (case SOME d. okT (dest_state st i) d of (stpairs, Bs, Bi, C) \<Rightarrow>
    bres_proof st Bs (bres_nlift Bi e) flatten x rp sp)"

definition bc_zproof :: "ztypargs \<Rightarrow> thm_rep \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> thm_rep \<Rightarrow> bres \<Rightarrow> zproof \<Rightarrow>
    zproof \<Rightarrow> zproof Z" where
  "bc_zproof ta st i e flatten ru x rp sp = (case SOME d. okT (dest_state st i) d of (stpairs, Bs, Bi, C) \<Rightarrow>
    bres_zproof ta st Bs (bres_nlift Bi e) flatten ru x rp sp)"

context prf_sig
begin

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
  obtain rAs B env where tp: "stpairs = th_tpairs state" and SP: "th_prop state = list_implies (Bs @ [Bi]) C"
    and P: "th_prop rule = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B)"
    and rc: "rchar (call_spec cfg vl env flatten match_flg (th_maxidx state) stpairs Bs Bi C False eres_flg
      (th_tpairs rule) rAs B) x"
    and bi: "bres_inv x"
    by (rule bicompose_setup[OF d ok rx cfg vl st ru tv vc]) blast
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
    and vc: "incremented \<Longrightarrow>
      vtcons (vars_thm (th_tpairs state) (th_prop state) \<union> vars_thm (th_tpairs rule) (th_prop rule))"
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
    by (rule bicompose_setup[OF d ok rx cfg vl st ru tv vc]) blast
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


subsection \<open>Theorems\<close>

definition thm_of_bc :: "sign \<Rightarrow> integer \<Rightarrow> 'u pure_thm \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'u pure_thm \<Rightarrow> bres \<Rightarrow> thm_data" where
  "thm_of_bc c i state flatten e rule x = \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x,
    th_prop = br_prop x, th_shyps = shyps_of state \<union> shyps_of rule \<union> env_sorts (br_env x),
    th_hyps = hyps_of state @ hyps_of rule, th_sign = c,
    th_proof = bindW (proof_of rule) (\<lambda>rp. bindW (proof_of state) (\<lambda>sp.
      bc_proof (rep_of state) i e flatten x rp sp)),
    th_zproof = bindM (zproof_of rule) (\<lambda>rp. bindM (zproof_of state) (\<lambda>sp.
      bc_zproof (pure_sig.ztargs (sg_consts c)) (rep_of state) i e flatten (rep_of rule) x rp sp)),
    th_constraints = cons_of rule \<union> cons_of state \<union> env_constraints (br_env x)\<rparr>"

definition bc_cons :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> bool" where
  "bc_cons state rule \<longleftrightarrow>
    scons (pure_sig.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.tvars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule))) \<and>
    pure_sig.vtcons (pure_sig.vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.vars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"

text \<open>Its two parts: one sort for each name of a type variable, one type for each name of a
  variable.\<close>

definition bc_scons :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> bool" where
  "bc_scons state rule \<longleftrightarrow>
    scons (pure_sig.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.tvars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"

definition bc_vcons :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> bool" where
  "bc_vcons state rule \<longleftrightarrow>
    pure_sig.vtcons (pure_sig.vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.vars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"

lemma bc_cons_iff: "bc_cons state rule \<longleftrightarrow> bc_scons state rule \<and> bc_vcons state rule"
  by (simp add: bc_cons_def bc_scons_def bc_vcons_def)

text \<open>The arguments of a composition satisfy the assumptions of the theorems above:\<close>

lemma bc_args:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and vc: "incremented \<Longrightarrow> bc_vcons state rule"
  shows "pure_sig.thm_inv0 (sg_alg (sign_of state)) (sg_ar (sign_of state)) (sg_consts (sign_of state))
      (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    and "pure_sig.thm_inv0 (sg_alg (sign_of state)) (sg_ar (sign_of state)) (sg_consts (sign_of state))
      (th_maxidx (rep_of rule)) (hyps_of rule) (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
    and "scons (pure_sig.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.tvars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"
    and "incremented \<Longrightarrow> pure_sig.vtcons (pure_sig.vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.vars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"
proof -
  show tv: "scons (pure_sig.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.tvars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"
    using sc by (simp add: bc_scons_def)
  then have s1: "scons (pure_sig.tvars_thm (th_tpairs (rep_thm state)) (th_prop (rep_thm state)))"
    and s2: "scons (pure_sig.tvars_thm (th_tpairs (rep_thm rule)) (th_prop (rep_thm rule)))"
    by (auto simp: scons_def)
  show "pure_sig.thm_inv0 (sg_alg (sign_of state)) (sg_ar (sign_of state)) (sg_consts (sign_of state))
      (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps s1] by simp
  show "pure_sig.thm_inv0 (sg_alg (sign_of state)) (sg_ar (sign_of state)) (sg_consts (sign_of state))
      (th_maxidx (rep_of rule)) (hyps_of rule) (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
    using pure_thm_inv0[of rule] ps s2 sr by simp
  show "incremented \<Longrightarrow> pure_sig.vtcons (pure_sig.vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      pure_sig.vars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"
    using vc by (simp add: bc_vcons_def)
qed

text \<open>The sort constraints of the environment of a result hold (\<open>Thm.insert_constraints_env\<close>):\<close>

lemma cons_ok_thm_of_bc:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and vc: "incremented \<Longrightarrow> bc_vcons state rule"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and rx: "pure_sig.bresult (unify_ops cfg vl) xq x"
  shows "cons_ok (sign_of state) (cons_of rule \<union> cons_of (state :: 'u pure_thm) \<union> env_constraints (br_env x))"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  note a = bc_args[OF ps sr sc vc]
  have "bres_inv x" by (rule bicompose_setup[OF d ok rx cfg vl a]) blast
  then have "tsorted (sg_alg ?c) (tyenv (br_env x))" by (simp add: bres_inv_def)
  then show ?thesis using sr by (simp add: cons_ok_env)
qed

lemma sorts_ok_thm_of_bc:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and vc: "incremented \<Longrightarrow> bc_vcons state rule"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and rx: "pure_sig.bresult (unify_ops cfg vl) xq x"
  shows "\<forall>S\<in>env_sorts (br_env x). sort_ok (sg_alg (sign_of (state :: 'u pure_thm))) S"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  note a = bc_args[OF ps sr sc vc]
  have "bres_inv x" by (rule bicompose_setup[OF d ok rx cfg vl a]) blast
  then have "scert (sg_alg ?c) (tyenv (br_env x))" by (simp add: bres_inv_def)
  then show ?thesis using scert_env_sorts by blast
qed

lemma thm_ok_thm_of_bc:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and vc: "incremented \<Longrightarrow> bc_vcons state rule"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and rx: "pure_sig.bresult (unify_ops cfg vl) xq x"
  shows "thm_ok TYPE('u) (thm_of_bc (sign_of state) i (state :: 'u pure_thm) flatten e rule x)"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  note a = bc_args[OF ps sr sc vc]
  note st = a(1) and ru = a(2) and tv = a(3) and vc' = a(4)
  obtain rAs B env where tp: "stpairs = th_tpairs (rep_of state)"
    and SP: "th_prop (rep_of state) = list_implies (Bs @ [Bi]) C"
    and ti: "thm_inv (maxidx (br_env x)) (hyps_of state @ hyps_of rule) (br_tpairs x) (br_prop x)"
    by (rule bicompose_setup[OF d ok rx cfg vl a]) blast
  have "valid_in ?c M (shyps_of state \<union> shyps_of rule \<union> env_sorts (br_env x)) (hyps_of state @ hyps_of rule)
      (br_tpairs x) (br_prop x)" if M: "is_model ?c M" for M :: "'u model"
  proof -
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD[OF M])
    have vs: "valid (shyps_of state) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
      using pure_thm_valid[OF M] by (simp add: valid_in_def)
    have vr: "valid (shyps_of rule) (hyps_of rule) (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
      using pure_thm_valid[of rule M] M sr by (simp add: valid_in_def)
    let ?S = "list_implies (Bs @ [Bi]) C"
    have ws: "wt_thm (th_maxidx (rep_of state)) (hyps_of state) stpairs ?S" using st tp SP by (simp add: thm_inv0_def)
    have wr: "wt_thm (th_maxidx (rep_of rule)) (hyps_of rule) (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
      using ru by (simp add: thm_inv0_def)
    have ok1: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg ?c) flatten match_flg incremented
        (th_maxidx (rep_of state), stpairs, ?S) (stpairs, Bs, Bi, C) False e
        (th_maxidx (rep_of rule), th_tpairs (rep_of rule), th_prop (rep_of rule)) nsubgoal) xq"
      using ok tp SP by (simp add: pthm_of_def)
    have vS: "valid (shyps_of state) (hyps_of state) stpairs ?S" using vs tp SP by simp
    interpret bc: bicompose_call_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      cfg vl flatten match_flg incremented "th_maxidx (rep_of state)" stpairs Bs Bi C False e "th_maxidx (rep_of rule)"
      "th_tpairs (rep_of rule)" "th_prop (rep_of rule)" nsubgoal "hyps_of state" "hyps_of rule"
      by unfold_locales (use cfg ws wr tv vc' tp SP vl in simp_all)
    have "valid (shyps_of state \<union> shyps_of rule \<union> tyenv_sorts (tyenv (br_env x))) (hyps_of state @ hyps_of rule)
        (br_tpairs x) (br_prop x)"
      by (rule bc.bicompose_aux_valid[OF ok1 rx vS vr])
    then show ?thesis unfolding valid_in_def by (rule valid_mono) (auto simp: env_sorts_def)
  qed
  moreover have "proofs_ok (thm_of_bc ?c i state flatten e rule x)" if psig: "is_prf_sig ?c"
  proof -
    interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      using psig by (simp add: is_prf_sig_def)
    have ps: "proofs_ok (rep_thm state)" by (rule pure_thm_proofs_ok[OF psig])
    have pr: "proofs_ok (rep_thm rule)" by (rule pure_thm_proofs_ok) (simp add: sr psig)
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
  ultimately show ?thesis using ti by (simp add: thm_ok_def thm_of_bc_def thm_inv_wf)
qed

text \<open>
  \<open>bicompose_thms cfg vl flatten match incremented eres_flg rule nsubgoal i state\<close>: the results of
  \<open>Thm.bicompose\<close> on theorems; \<open>None\<close> if an exception is raised, if the signatures do not agree,
  if the configuration does not belong to the signature, or if the theorems are not consistent
  (\<^const>\<open>bc_scons\<close>; with \<open>incremented\<close> also \<^const>\<open>bc_vcons\<close>).
\<close>

definition bicompose_thms :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    'u pure_thm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm list option" where
  "bicompose_thms cfg vl flatten match_flg incremented e rule nsubgoal i state =
    (let c = sign_of state;
      R = (\<lambda>xs. \<exists>dst xq. okT (dest_state (rep_of state) i) dst \<and>
        okT (bicompose_aux (unify_ops cfg vl) (sg_alg c) flatten match_flg incremented (pthm_of (rep_of state))
          dst False e (pthm_of (rep_of rule)) nsubgoal) xq \<and> pure_sig.bevals (unify_ops cfg vl) xq xs)
     in if pure_sig (sg_alg c) (sg_ar c) \<and> cfg_alg cfg = sg_alg c \<and> (\<forall>xs. length (vl xs) = length xs) \<and>
          sign_of rule = c \<and> bc_scons state rule \<and> (incremented \<longrightarrow> bc_vcons state rule) \<and> (\<exists>xs. R xs)
       then Some (map (\<lambda>x. Abs_thm (thm_of_bc c i state flatten e rule x)) (THE xs. R xs))
       else None)"

theorem bicompose_thms_results:
  assumes bt: "bicompose_thms cfg vl flatten match_flg incremented e rule nsubgoal i state = Some ths"
    and th: "th \<in> set ths"
  shows "\<exists>stpairs Bs Bi C xq x. okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C) \<and>
    okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq \<and>
    pure_sig.bresult (unify_ops cfg vl) xq x \<and> rep_thm th = thm_of_bc (sign_of state) i state flatten e rule x"
proof -
  let ?c = "sign_of state"
  let ?R = "\<lambda>xs. \<exists>dst xq. okT (dest_state (rep_of state) i) dst \<and>
    okT (bicompose_aux (unify_ops cfg vl) (sg_alg ?c) flatten match_flg incremented (pthm_of (rep_of state))
      dst False e (pthm_of (rep_of rule)) nsubgoal) xq \<and> pure_sig.bevals (unify_ops cfg vl) xq xs"
  from bt have g: "pure_sig (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "sign_of rule = ?c" "bc_scons state rule" "incremented \<longrightarrow> bc_vcons state rule" "\<exists>xs. ?R xs"
    and ths: "ths = map (\<lambda>x. Abs_thm (thm_of_bc ?c i state flatten e rule x)) (THE xs. ?R xs)"
    unfolding bicompose_thms_def Let_def by (auto split: if_splits)
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule g(1))
  from g(7) obtain ys dst xq where d: "okT (dest_state (rep_of state) i) dst"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg ?c) flatten match_flg incremented (pthm_of (rep_of state))
      dst False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and ev: "bevals (unify_ops cfg vl) xq ys" by blast
  have the: "(THE xs. ?R xs) = ys"
  proof (rule the_equality)
    show "?R ys" using d ok ev by blast
    fix zs assume "?R zs"
    then obtain dst' xq' where "okT (dest_state (rep_of state) i) dst'"
      "okT (bicompose_aux (unify_ops cfg vl) (sg_alg ?c) flatten match_flg incremented (pthm_of (rep_of state))
        dst' False e (pthm_of (rep_of rule)) nsubgoal) xq'" "bevals (unify_ops cfg vl) xq' zs" by blast
    with d ok ev show "zs = ys" using okT_det bevals_det by metis
  qed
  from th obtain x where x: "x \<in> set ys" and thx: "th = Abs_thm (thm_of_bc ?c i state flatten e rule x)"
    unfolding ths the by auto
  have rx: "bresult (unify_ops cfg vl) xq x" by (rule bevals_results[OF ev x])
  obtain stpairs Bs Bi C where dst: "dst = (stpairs, Bs, Bi, C)" by (cases dst) auto
  have okx: "thm_ok TYPE('a) (thm_of_bc ?c i state flatten e rule x)"
    by (rule thm_ok_thm_of_bc[OF g(1,2) _ g(4,5) _ d[unfolded dst] ok[unfolded dst] rx]) (use g(3,6) in blast)+
  have cox: "cons_ok ?c (cons_of rule \<union> cons_of state \<union> env_constraints (br_env x))"
    by (rule cons_ok_thm_of_bc[OF g(1,2) _ g(4,5) _ d[unfolded dst] ok[unfolded dst] rx]) (use g(3,6) in blast)+
  have "rep_thm th = thm_of_bc ?c i state flatten e rule x"
    unfolding thx by (rule rep_Abs_thm[OF okx]) (use cox in \<open>simp add: thm_of_bc_def\<close>)
  with d ok rx dst show ?thesis by blast
qed

end
