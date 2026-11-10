section \<open>Closed classic proofs\<close>

theory Proof_Closed
  imports ZEq_Proofs
begin

text \<open>
  The terms of a classic proof refer only to bound variables of abstractions of the proof
  (\<^const>\<open>prf_nolb\<close>). Lifting, normalisation and composition keep this, and so does the
  translation of tight proofs.
\<close>

subsection \<open>Auxiliary facts\<close>

lemma prf_nolb_proof_combP: "prf_nolb k (proof_combP p qs) \<longleftrightarrow> prf_nolb k p \<and> (\<forall>q\<in>set qs. prf_nolb k q)"
  unfolding proof_combP_def by (induction qs arbitrary: p) auto

lemma prf_nolb_proof_combt:
  "prf_nolb k (proof_combt p ts) \<longleftrightarrow> prf_nolb k p \<and> (\<forall>t\<in>set ts. \<not> loose_bvar t k)"
  unfolding proof_combt_def by (induction ts arbitrary: p) auto

lemma prf_nolb_mk_AbsP [simp]: "prf_nolb k (mk_AbsP xs p) = prf_nolb k p"
  unfolding mk_AbsP_def by (induction xs) auto

lemma prf_nolb_foldl_PAppt:
  "prf_nolb k (foldl (\<lambda>p t. PAppt p (Some t)) p ts) \<longleftrightarrow> prf_nolb k p \<and> (\<forall>t\<in>set ts. \<not> loose_bvar t k)"
  by (induction ts arbitrary: p) auto

lemma (in pure_sig) beta_reds_loose_bvar: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar s k \<Longrightarrow> \<not> loose_bvar t k"
  by (induction rule: rtranclp_induct) (auto dest: loose_bvar_beta)


subsection \<open>Lifting\<close>

lemma prf_nolb_lift_prf: "prf_nolb lev p \<Longrightarrow> prf_nolb (lev + ilength Ts) (lift_prf inc Ts lev p)"
proof (induction inc Ts lev p rule: lift_prf.induct)
  case (1 inc Ts lev a T p)
  then show ?case by (simp add: algebra_simps)
qed (auto simp: loose_bvar_incr_idx)

lemma prf_nolb_spine:
  "b < k \<Longrightarrow> prf_nolb k p \<Longrightarrow> fst (snd (foldr mk_app bs (a, b, p))) \<le> b \<and>
    prf_nolb k (snd (snd (foldr mk_app bs (a, b, p))))"
  by (induction bs) (auto simp: mk_app_def split: prod.splits)

lemma prf_nolb_lift_leaf:
  "prf_nolb 0 pf \<Longrightarrow> j = ilength Ts \<Longrightarrow>
    prf_nolb j (proof_combP (lift_prf inc (rev Ts) 0 pf) (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) ks))"
  using prf_nolb_lift_prf[of 0 pf "rev Ts" inc] prf_nolb_spine[of "j - 1" j "PBound _" bs "i - 1"]
  by (auto simp: prf_nolb_proof_combP ilength_eq)

lemma prf_nolb_lift_prems:
  "prf_nolb 0 pf \<Longrightarrow> j = ilength Ts \<Longrightarrow> prf_nolb j (lift_prems inc k pf Ts bs i j G)"
proof (induction inc k pf Ts bs i j G rule: lift_prems.induct)
  case (2 inc k pf Ts bs i j c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    have "prf_nolb (j + 1) (lift_prems inc k pf (T # Ts) (False # bs) i (j + 1) t)"
      by (rule "2.IH"[OF True "2.prems"(1)]) (use "2.prems"(2) in \<open>simp add: algebra_simps\<close>)
    with True show ?thesis by simp
  next
    case False
    with "2.prems" show ?thesis by (simp add: prf_nolb_lift_leaf)
  qed
qed (simp_all add: prf_nolb_lift_leaf)

lemma prf_nolb_lift_proof: "prf_nolb 0 pf \<Longrightarrow> prf_nolb 0 (lift_proof gprop inc prems pf)"
  using prf_nolb_lift_prems[of pf 0 "[]"] by (simp add: lift_proof_def ilength_eq)


subsection \<open>Composition and normalisation\<close>

lemma prf_nolb_mk_asm_prf: "prf_nolb k (mk_asm_prf A i m)"
proof -
  have "prf_nolb k (imp_prf A i m)" for k A i m by (induction A i m arbitrary: k rule: imp_prf.induct) auto
  then have "prf_nolb k (all_prf i m A)" for k by (induction i m A arbitrary: k rule: all_prf.induct) auto
  then show ?thesis by (simp add: mk_asm_prf_def)
qed

lemma prf_nolb_flatten_params_proof: "j \<le> k \<Longrightarrow> prf_nolb k (flatten_params_proof i j n x)"
proof (induction i j n x arbitrary: k rule: flatten_params_proof.induct)
  case (2 i j n c U a T t k')
  then show ?case
    by (auto simp: prf_nolb_proof_combP prf_nolb_proof_combt integer_arith dest!: downto_le)
qed (auto simp: prf_nolb_proof_combP prf_nolb_proof_combt integer_arith dest!: downto_le)

lemma prf_nolb_core_prf:
  "prf_nolb 0 sprf \<Longrightarrow> prf_nolb 0 p \<Longrightarrow> prf_nolb 0 (core_prf flatten lb oldAs A n m sprf p)"
  by (auto simp: core_prf_def prf_nolb_proof_combP prf_nolb_mk_asm_prf prf_nolb_flatten_params_proof)

lemma prf_nolb_norm_proof:
  "norm_proof E q = returnW q' \<Longrightarrow>
    (\<And>t t' k. ok (norm_term E t) t' \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar t k \<Longrightarrow> \<not> loose_bvar t' k) \<Longrightarrow>
    0 \<le> k \<Longrightarrow> prf_nolb k q \<Longrightarrow> prf_nolb k q'"
proof (induction q arbitrary: q' k)
  case (Abst a T p)
  then show ?case by (auto simp: bindP_eq_returnP)
next
  case (PThm x)
  then show ?case by (cases x) (auto simp: bindP_eq_returnP)
qed (fastforce simp: bindP_eq_returnP map_optionP_eq_returnP dest!: norm_term_P_returnP)+

context prf_sig
begin

lemma loose_bvar_norm_term:
  assumes nt: "ok (norm_term E t) t'" and ac: "acyc E" "closed_env E" "tacyc (tyenv E)"
    and k: "0 \<le> k" and l: "\<not> loose_bvar t k"
  shows "\<not> loose_bvar t' k"
proof -
  have "\<not> loose_bvar (env_apply E t) k"
    using l k closed_usubst[OF ac(1,2)] by (simp add: env_apply_def unf_def)
  from beta_reds_loose_bvar[OF norm_term_env_apply(1)[OF nt ac] k this] show ?thesis .
qed

theorem prf_nolb_bicompose_proof:
  assumes res: "bicompose_proof env smax flatten Bs As A oldAs n m rprf sprf = returnW p"
    and r: "prf_nolb 0 rprf" and s: "prf_nolb 0 sprf"
    and ac: "acyc env" "closed_env env" "tacyc (tyenv env)"
  shows "prf_nolb 0 p"
proof -
  let ?E = "remove_types_env env"
  have ac': "acyc ?E" "closed_env ?E" "tacyc (tyenv ?E)" using ac by (simp_all add: remove_types_env_props)
  have np: "prf_nolb 0 q'" if nq: "norm_proof ?E q = returnW q'" and q: "prf_nolb 0 q" for q q'
    by (rule prf_nolb_norm_proof[OF nq _ _ q]) (use loose_bvar_norm_term[OF _ ac'] in auto)
  have core: "prf_nolb 0 x" if c: "bicompose_core env flatten Bs As A oldAs n m sprf q = returnW x"
    and q: "prf_nolb 0 q" for q x
    using bicompose_core_returnP[OF c] q s by (simp add: prf_nolb_core_prf)
  consider "bicompose_core env flatten Bs As A oldAs n m sprf rprf = returnW p"
    | r' where "norm_proof ?E rprf = returnW r'" "bicompose_core env flatten Bs As A oldAs n m sprf r' = returnW p"
    | q where "bicompose_core env flatten Bs As A oldAs n m sprf rprf = returnW q" "norm_proof ?E q = returnW p"
    using res unfolding bicompose_proof_def norm_proof_remove_types_def
    by (auto simp: bindP_eq_returnP split: if_splits)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (rule core[OF _ r])
  next
    case (2 r')
    show ?thesis by (rule core[OF 2(2) np[OF 2(1) r]])
  next
    case (3 q)
    show ?thesis by (rule np[OF 3(2) core[OF 3(1) r]])
  qed
qed

theorem biresolution_proof_closed:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r))"
    and sp: "prf_nolb 0 sprf" and rp: "prf_nolb 0 rprf"
    and p: "bires_proof state i eres_flg (rep rule) x rprf sprf = returnW p"
  shows "prf_nolb 0 p"
proof -
  obtain stpairs Bs Bi C rAs B env where some: "(SOME d. okT (dest_state state i) d) = (stpairs, Bs, Bi, C)"
    and r: "(eres_flg, rule) \<in> set brules" and tp: "stpairs = th_tpairs state"
    and SP: "th_prop state = list_implies (Bs @ [Bi]) C"
    and ws: "wt_thm (th_maxidx state) hs stpairs (list_implies (Bs @ [Bi]) C)" and pB: "pnn Bi"
    and lri: "thm_inv (th_maxidx (lift_rule Bi (th_maxidx state) (rep rule))) (hyps rule)
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) (th_prop (lift_rule Bi (th_maxidx state) (rep rule)))"
    and P: "th_prop (lift_rule Bi (th_maxidx state) (rep rule)) = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B)"
    and rc: "rchar (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B) x"
    and lrl: "lifted_rule (th_maxidx state) Bi (rev rAs) B" and bi: "bres_inv x"
    and bA: "\<forall>C'. br_A x = Some C' \<longrightarrow> C' \<in> set (rev rAs)"
    by (rule biresolution_setup[OF br res cfg vl st rules])
  let ?smax = "th_maxidx state" and ?rprf = "lift_rule_proof Bi (th_maxidx state) (rep rule) rprf"
  have p': "bicompose_proof (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
      (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1)
      (ren_prf (na_ren (br_newas x)) ?rprf) sprf = returnW p"
    using p by (simp add: bires_proof_def some bres_proof_sel bres_nlift_def)
  have "prf_nolb 0 ?rprf" unfolding lift_rule_proof_def by (rule prf_nolb_lift_proof[OF rp])
  then have rn: "prf_nolb 0 (ren_prf (na_ren (br_newas x)) ?rprf)"
    by (auto simp: ren_prf_def split: option.splits intro: prf_nolb_map)
  note bp = bres_inv_props[OF bi]
  show ?thesis by (rule prf_nolb_bicompose_proof[OF p' rn sp bp(4) bp(5) bp(3)])
qed

end


subsection \<open>Tight proofs\<close>

lemma (in pure_sig) prf_nolb_zprf_tr: "znolb k p \<Longrightarrow> prf_nolb k (zprf_tr p)"
proof (induction p arbitrary: k)
  case (ZConstp c)
  obtain c0 instT tab where c: "c = (c0, instT, tab)" by (cases c)
  have look: "\<not> loose_bvar t k" if "map_option zdec (zv_lookup_name tab (x, -1)) = Some t" for x t
  proof -
    from that obtain u where u: "zv_lookup_name tab (x, -1) = Some u" "t = zdec u" by auto
    then obtain T where "zv_lookup tab ((x, -1), T) = Some u"
      unfolding zv_lookup_name_def by (auto split: if_splits)
    with ZConstp.prems c u(2) show ?thesis by auto
  qed
  have "prf_nolb k (zeq_tr n (\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1))))" for n
  proof -
    have "\<not> loose_bvar t k" if "those (map (\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1))) xs) = Some ts"
      "t \<in> set ts" for xs ts t
      using list_all2_ex2[OF those_Some_list_all2[OF that(1)] that(2)] look by auto
    then show ?thesis
      by (auto simp: zeq_tr_def prf_nolb_foldl_PAppt equality_axm_def split: option.splits prod.splits)
  qed
  then show ?case by (auto simp: c zconst_tr_def split: zproof_name.splits prod.splits)
qed simp_all


text \<open>The hypotheses of a tight proof are the encodings of their decodings:\<close>

definition (in pure_sig) zhyps_ok :: "zproof \<Rightarrow> bool" where
  "zhyps_ok p \<longleftrightarrow> (\<forall>h\<in>zhyps p. zterm_of ztargs (zdec h) = return h)"

lemma (in pure_sig) zhyps_ok_mono: "zhyps_ok p \<Longrightarrow> zhyps q \<subseteq> zhyps p \<Longrightarrow> zhyps_ok q"
  by (auto simp: zhyps_ok_def)


lemma (in prf_sig) zhyps_ok_zterm_of:
  "zterm_of ztargs t = return z \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> pnn t \<Longrightarrow> zterm_of ztargs (zdec z) = return z"
  using zterm_of_zdec_pnn[of e t T] by auto

text \<open>The proof constants of the equality axioms:\<close>

lemma zaxiom_proof_closed:
  assumes z: "zaxiom_proof a Ts ts = return p" and a: "a \<in> fst ` set zeq_vars"
    and xs: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>t. map_of ts x = Some t \<and> \<not> zloose t 0"
  shows "znolb 0 p" "zhyps p = {}"
proof -
  let ?vs = "snd (snd (zequality_axiom a))"
  let ?tab = "fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) ?vs zv_empty"
  let ?instT = "fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) (fst (snd (zequality_axiom a))) zt_empty"
  have e: "zequality_axm a = ((ZAxiom (STR ''Pure.'' + a), fst (zequality_axiom a)), (?instT, ?tab))"
    by (simp add: zequality_axm_def split: prod.splits)
  have l: "zv_lookup ?tab k = (if k \<in> set ?vs then Some (ZVar (fst k) (snd k)) else None)" for k
    by (simp add: zv_lookup_fold_update)
  from a have "a \<in> {STR ''reflexive'', STR ''symmetric'', STR ''transitive'', STR ''equal_intr'',
      STR ''equal_elim'', STR ''abstract_rule'', STR ''combination''}"
    by (simp add: zeq_vars_def)
  then have d: "distinct (map fst ?vs)"
    and w: "\<forall>k\<in>set ?vs. fst (fst k) \<in> set (the (map_of zeq_vars a))"
    by (auto simp: zeq_vars_def zequality_axiom_def Let_def)
  have nok: "ztab_names_ok ?tab"
    unfolding ztab_names_ok_def
  proof (intro allI impI)
    fix k1 k2 assume "zv_lookup ?tab k1 \<noteq> None" "zv_lookup ?tab k2 \<noteq> None" "fst k1 = fst k2"
    then have "k1 \<in> set ?vs" "k2 \<in> set ?vs" "fst k1 = fst k2" by (simp_all add: l split: if_splits)
    with d show "k1 = k2" by (metis distinct_map inj_onD)
  qed
  let ?term = "\<lambda>t. (return :: zterm \<Rightarrow> zterm Z) (case t of ZVar (x, _) _ \<Rightarrow> (case map_of ts x of Some u \<Rightarrow> u | None \<Rightarrow> t) | _ \<Rightarrow> t)"
  from z obtain instT' tab' where mi: "map_insts (zsubst_tvar_names (map_of Ts)) ?term (?instT, ?tab) = return (instT', tab')"
    and p: "p = ZConstp ((ZAxiom (STR ''Pure.'' + a), fst (zequality_axiom a)), (instT', tab'))"
    by (auto simp: zaxiom_proof_def make_const_proof_def e bindZ_eq_returnZ)
  have "\<not> zloose t' 0" if "zv_lookup tab' k = Some t'" for k t'
  proof -
    have "\<exists>k0 t0. zv_lookup ?tab k0 = Some t0 \<and> ?term t0 = return t'" by (rule map_insts_values[OF mi nok that])
    then obtain k0 t0 where k0: "zv_lookup ?tab k0 = Some t0" "?term t0 = return t'" by blast
    obtain x i T where kk: "k0 = ((x, i), T)" by (cases k0) auto
    from k0(1) have k0': "k0 \<in> set ?vs" "t0 = ZVar (fst k0) (snd k0)" by (simp_all add: l split: if_splits)
    from xs w k0'(1) kk obtain u where u: "map_of ts x = Some u" "\<not> zloose u 0" by fastforce
    from k0(2) k0'(2) kk u(1) have "t' = u" by (simp add: return_def)
    with u(2) show ?thesis by simp
  qed
  then show "znolb 0 p" by (simp add: p)
  show "zhyps p = {}" by (simp add: p)
qed

end
