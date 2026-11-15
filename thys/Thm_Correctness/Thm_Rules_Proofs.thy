section \<open>Proofs: Thm_Rules\<close>

theory Thm_Rules_Proofs
  imports "Thm_Soundness.Thm_Rules" Thm_Type_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Rules\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

lemma proofs_ok_implies_elim:
  fixes thAB thA :: "'u pure_thm"
  assumes ok: "okT (implies_elim (rep_of thAB) (rep_of thA)) r" and c: "sign_of thA = sign_of thAB"
    and po_thAB: "is_prf_sig (sign_of thAB) \<Longrightarrow> proofs_ok (rep_thm thAB)"
    and po_thA: "is_prf_sig (sign_of thA) \<Longrightarrow> proofs_ok (rep_thm thA)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
    (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
    (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q)))))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
    (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
    (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q)))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of thAB"
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have pAB: "proofs_ok (rep_thm thAB)" by (rule po_thAB) (use psig in simp)
  have pA: "proofs_ok (rep_thm thA)" by (rule po_thA) (use psig c in simp)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w1: "wtp (th_prop (rep_of thAB))" and w2: "wtp (th_prop (rep_of thA))"
    using pure_thm_wf[of thAB] pure_thm_wf[of thA] c ps by (simp_all add: thm_wf_def wt_thm_def)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pr assume "bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))) = returnW pr"
    then obtain p q where p: "proof_of thAB = returnW p" and q: "proof_of thA = returnW q" and pr: "pr = PAppp p q"
      by (auto simp: bindP_eq_returnP)
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of thAB)) (th_tpairs (rep_of thAB)) p (th_prop (rep_of thAB))"
      "prf_idx (\<lambda>i. 0 \<le> i) p" "prf_nolb 0 p"
      using pAB p by (simp_all add: proofs_ok_def Let_def)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of thA)) (th_tpairs (rep_of thA)) q (th_prop (rep_of thA))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using pA q c by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of thAB) \<union> set (hyps_of thA)) (th_tpairs r) (PAppp p q) (th_prop r)"
      by (rule implies_elim_rule_proof_valid[OF ok vp(1) vq(1) w1 w2])
    then show "prf_valid (sg_ax ?c) (set (hyps_of thA @ hyps_of thAB)) (th_tpairs r) pr (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pr \<and> prf_nolb 0 pr"
      using vp(2,3) vq(2,3) by (simp add: pr Un_commute)
  next
    fix z assume "bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q))) = return z"
    then obtain p q where p: "zproof_of thAB = return p" and q: "zproof_of thA = return q" and z: "z = ZAppp p q"
      by (auto simp: bindZ_eq_returnZ)
    have vp: "zvalid (sg_ax ?c) (set (hyps_of thAB)) (th_tpairs (rep_of thAB)) p (th_prop (rep_of thAB))" "zinv p"
        "znolb 0 p" "zhyps_ok p"
      using pAB p by (simp_all add: proofs_ok_def Let_def)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of thA)) (th_tpairs (rep_of thA)) q (th_prop (rep_of thA))" "zinv q"
        "znolb 0 q" "zhyps_ok q"
      using pA q c by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of thAB) \<union> set (hyps_of thA)) (th_tpairs r) (ZAppp p q) (th_prop r)"
      by (rule zimplies_elim_rule_proof_valid[OF ok vp(1) vq(1) w1 w2])
    then show "zvalid (sg_ax ?c) (set (hyps_of thA @ hyps_of thAB)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps_ok z"
      using vp(2-4) vq(2-4) by (auto simp: z Un_commute zhyps_ok_def)
  qed
qed

context prf_sig
begin

lemma thm_wf_pnn:
  assumes "thm_wf m hs tps P"
  shows "pnn P" "\<forall>(t, u)\<in>set tps. pnn t \<and> pnn u"
  using assms by (auto simp: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)

end

lemma zinv_zaxiom_proof:
  assumes z: "zaxiom_proof a Ts ts = return p" and a: "a \<in> fst ` set zeq_vars"
    and xs: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>t. map_of ts x = Some t \<and> zterm_ok t"
    and tys: "\<And>n T. (n, T) \<in> set Ts \<Longrightarrow> ztyp_ok T"
  shows "zinv p"
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
  have "zterm_ok t'" if "zv_lookup tab' k = Some t'" for k t'
  proof -
    have "\<exists>k0 t0. zv_lookup ?tab k0 = Some t0 \<and> ?term t0 = return t'" by (rule map_insts_values[OF mi nok that])
    then obtain k0 t0 where k0: "zv_lookup ?tab k0 = Some t0" "?term t0 = return t'" by blast
    obtain x i T where kk: "k0 = ((x, i), T)" by (cases k0) auto
    from k0(1) have k0': "k0 \<in> set ?vs" "t0 = ZVar (fst k0) (snd k0)" by (simp_all add: l split: if_splits)
    from xs w k0'(1) kk obtain u where u: "map_of ts x = Some u" "zterm_ok u" by fastforce
    from k0(2) k0'(2) kk u(1) have "t' = u" by (simp add: return_def)
    with u(2) show ?thesis by simp
  qed
  moreover have "ztyp_ok T'" if "zt_lookup instT' k = Some T'" for k T'
  proof -
    have iT: "instT' = zt_map (zsubst_tvar_names (map_of Ts)) ?instT"
      using mi by (auto simp: map_insts_def bindZ_eq_returnZ)
    from that obtain T0 where T0: "zt_lookup ?instT k = Some T0" "T' = zsubst_tvar_names (map_of Ts) T0"
      by (auto simp: iT)
    from T0(1) have T0': "T0 = ZTVar (fst k) (snd k)" by (simp add: zt_lookup_fold_update split: if_splits)
    from a T0(1) have m1: "snd (fst k) = -1"
      by (auto simp: zt_lookup_fold_update zeq_vars_def zequality_axiom_def Let_def split: if_splits)
    obtain x S where k: "k = ((x, -1), S)" using m1 by (cases k; cases "fst k") auto
    show ?thesis
    proof (cases "map_of Ts x")
      case None
      then show ?thesis using T0(2) T0' k by (simp add: ztyp_ok_def)
    next
      case (Some T1)
      then have "(x, T1) \<in> set Ts" by (rule map_of_SomeD)
      then have "ztyp_ok T1" by (rule tys)
      then show ?thesis using T0(2) T0' k Some by simp
    qed
  qed
  ultimately show ?thesis using map_insts_names(1)[OF mi nok] by (simp add: p)
qed

lemma zaxiom_proof_ok:
  assumes z: "zaxiom_proof a Ts ts = return p" and a: "a \<in> fst ` set zeq_vars"
    and xs: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>t. map_of ts x = Some t \<and> zterm_ok t \<and> \<not> zloose t 0"
    and tys: "\<And>n T. (n, T) \<in> set Ts \<Longrightarrow> ztyp_ok T"
  shows "zinv p \<and> znolb 0 p \<and> zhyps p = {}"
  using zinv_zaxiom_proof[OF z a] zaxiom_proof_closed[OF z a] xs tys by blast

lemma proofs_ok_symmetric:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (symmetric (rep_of th)) r" and se: "sign_eq (sign_of th)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
    (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
        Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) T t u p
      | None \<Rightarrow> raise undefined)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
    (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
        Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) T t u p
      | None \<Rightarrow> raise undefined)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  have eq: "pure_sig_gen.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain e t u where P: "th_prop (rep_of th) = e $ t $ u" and d: "dest_eq_fun (th_prop (rep_of th)) \<noteq> None"
    and r: "r = mk_rep (th_maxidx (rep_of th)) (th_tpairs (rep_of th)) (e $ u $ t)"
    by (auto simp: symmetric_def returnW_def raiseW_def split: pterm.splits option.splits)
  then obtain T' where "dest_eq_fun (th_prop (rep_of th)) = Some (T', t, u)"
    by (cases "th_prop (rep_of th)" rule: dest_eq_fun.cases) (auto split: if_splits)
  then have d': "dest_eq_any (th_prop (rep_of th)) = Some (t, u)" by (rule dest_eq_any_dest_eq_fun)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def)
  have pth: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have wf: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  then have w: "wtp (th_prop (rep_of th))" by (simp add: thm_wf_def wt_thm_def)
  obtain T where P': "th_prop (rep_of th) = eq_const T $ t $ u" using dest_eq_any_wtp[OF eq d' w] by blast
  have pt: "pnn t" "pnn u" using thm_wf_pnn(1)[OF wf] unfolding P' by simp_all
  have tT: "tnn T" using thm_wf_pnn(1)[OF wf] unfolding P' by (simp add: pnn_def)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pr assume "bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)) = returnW pr"
    then obtain p where p: "proof_of th = returnW p" and pr: "pr = symmetric_proof p"
      by (auto simp: bindP_eq_returnP)
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) p (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) p" "prf_nolb 0 p"
      using pth p by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) (symmetric_proof p) (th_prop r)"
      by (rule symmetric_proof_valid[OF ok vp(1) w prf_valid_refl_ok[OF vp(1)]])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) (symmetric_proof p)" "prf_nolb 0 (symmetric_proof p)"
      using vp(2,3) by (auto simp: symmetric_proof_def equality_axm_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pr (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pr \<and> prf_nolb 0 pr"
      by (simp add: pr)
  next
    fix z assume "bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
        Some (T, t, u) \<Rightarrow> zsymmetric_proof ztargs T t u p | None \<Rightarrow> raise undefined) = return z"
    then obtain p where p: "zproof_of th = return p" and z: "zsymmetric_proof ztargs T t u p = return z"
      using P' by (auto simp: bindZ_eq_returnZ propT_def)
    have vp: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) p (th_prop (rep_of th))" "zinv p"
      "znolb 0 p" "zhyps_ok p"
      using pth p by (simp_all add: proofs_ok_def Let_def)
    have zc: "zconsts_ok p" using vp(2) by (simp add: zinv_def)
    note zs = zsymmetric_proof_valid[OF ok vp(1) w P' pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)] zc z]
    have cl: "\<not> loose_bvar t 0" "\<not> loose_bvar u 0" using wtpD(1)[OF w] unfolding P' by (simp_all add: closed_def)
    have "zinv z \<and> znolb 0 z \<and> zhyps_ok z"
    proof (cases "zis_reflexive_proof p")
      case True
      with z have "z = p" by (simp add: zsymmetric_proof_def)
      with vp(2-4) show ?thesis by simp
    next
      case False
      with z obtain x y ax where x: "zterm_of ztargs t = return x" and y: "zterm_of ztargs u = return y"
        and ax: "zaxiom_proof STR ''symmetric'' [(tvar_a, ztyp_of T)] [(STR ''x'', x), (STR ''y'', y)] = return ax"
        and zz: "z = ZAppp ax p"
        by (auto simp: zsymmetric_proof_def bindZ_eq_returnZ)
      have "zinv ax \<and> znolb 0 ax \<and> zhyps ax = {}"
        by (rule zaxiom_proof_ok[OF ax])
          (use zterm_ok_zterm_of_pnn[OF x pt(1)] zterm_ok_zterm_of_pnn[OF y pt(2)]
            zloose_zterm_of[OF x] zloose_zterm_of[OF y] cl ztyp_ok_ztyp_of[OF tT] in \<open>auto simp: zeq_vars_def\<close>)
      with vp(2-4) show ?thesis by (auto simp: zz zhyps_ok_def)
    qed
    with zs(1) show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps_ok z" by simp
  qed
qed

lemma proofs_ok_transitive:
  fixes th1 th2 :: "'u pure_thm"
  assumes ok: "okT (transitive (rep_of th1) (rep_of th2)) r" and c: "sign_of th2 = sign_of th1"
    and se: "sign_eq (sign_of th1)"
    and po_th1: "is_prf_sig (sign_of th1) \<Longrightarrow> proofs_ok (rep_thm th1)"
    and po_th2: "is_prf_sig (sign_of th2) \<Longrightarrow> proofs_ok (rep_thm th2)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
      case eq_args (th_prop (rep_of th1)) of
        Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
      | None \<Rightarrow> raiseW undefined)))
    (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
      case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
        (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
          ztransitive_proof (pure_sig_gen.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
      | _ \<Rightarrow> raise undefined))))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
      case eq_args (th_prop (rep_of th1)) of
        Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
      | None \<Rightarrow> raiseW undefined)))
    (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
      case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
        (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
          ztransitive_proof (pure_sig_gen.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
      | _ \<Rightarrow> raise undefined))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig_gen.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain e x y T t1 u u' t2 where P1: "th_prop (rep_of th1) = e $ x $ y"
    and d1: "dest_eq (th_prop (rep_of th1)) = Some (T, t1, u)"
    and d2: "dest_eq_any (th_prop (rep_of th2)) = Some (u', t2)" and a: "aconv_term u u'"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) (e $ t1 $ t2)"
    by (auto simp: transitive_def returnW_def raiseW_def split: pterm.splits option.splits prod.splits if_splits)
  have d1': "dest_eq_any (th_prop (rep_of th1)) = Some (t1, u)" by (rule dest_eq_any_dest_eq[OF d1])
  have common: "\<exists>A. th_prop (rep_of th1) = eq_const A $ t1 $ u \<and> th_prop (rep_of th2) = eq_const A $ u' $ t2 \<and>
      e = eq_const A \<and> pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (eq_const A $ t1 $ t2)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w1: "wtp (th_prop (rep_of th1))" and w2: "wtp (th_prop (rep_of th2))"
      using pure_thm_wf[of th1] pure_thm_wf[of th2] ps c by (simp_all add: thm_wf_def wt_thm_def)
    obtain A where P1': "th_prop (rep_of th1) = eq_const A $ t1 $ u" and c1: "closed t1" "closed u"
      and ty1: "\<And>e. e \<turnstile> t1 : A" "\<And>e. e \<turnstile> u : A"
      using dest_eq_any_wtp[OF eq d1' w1] by blast
    obtain B where P2': "th_prop (rep_of th2) = eq_const B $ u' $ t2" and c2: "closed u'" "closed t2"
      and ty2: "\<And>e. e \<turnstile> u' : B" "\<And>e. e \<turnstile> t2 : B"
      using dest_eq_any_wtp[OF eq d2 w2] by blast
    have AB: "A = B" using typing_aconv[OF a ty1(2)] ty2(1) typing_unique by metis
    have "wtp (eq_const A $ t1 $ t2)"
    proof (rule wtpI)
      show "closed (eq_const A $ t1 $ t2)" using c1 c2 by (simp add: closed_def)
      have "(\<lambda>_. propT) \<turnstile> eq_const A $ t1 $ u : propT" using wtpD(2)[OF w1] P1' by simp
      then show "(\<lambda>_. propT) \<turnstile> eq_const A $ t1 $ t2 : propT" using ty1 ty2 AB by auto
    qed
    with P1' P2' P1 AB show ?thesis by auto
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def)
  have p1: "proofs_ok (rep_thm th1)" by (rule po_th1) (use psig in simp)
  have p2: "proofs_ok (rep_thm th2)" by (rule po_th2) (use psig c in simp)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  from common ps obtain A where P1': "th_prop (rep_of th1) = eq_const A $ t1 $ u"
    and P2': "th_prop (rep_of th2) = eq_const A $ u' $ t2" by auto
  have wf1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
    using pure_thm_wf[of th1] ps by simp
  have wf2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
    using pure_thm_wf[of th2] ps c by simp
  have w1: "wtp (th_prop (rep_of th1))" and w2: "wtp (th_prop (rep_of th2))"
    using wf1 wf2 by (simp_all add: thm_wf_def wt_thm_def)
  have pt: "pnn t1" "pnn u" using thm_wf_pnn(1)[OF wf1] unfolding P1' by simp_all
  have pt2: "pnn t2" using thm_wf_pnn(1)[OF wf2] unfolding P2' by simp_all
  have tA: "tnn A" using thm_wf_pnn(1)[OF wf1] unfolding P1' by (simp add: pnn_def)
  have ea1: "eq_args (th_prop (rep_of th1)) = Some (A, t1, u)" unfolding P1' by (simp add: propT_def)
  have ea2: "eq_args (th_prop (rep_of th2)) = Some (A, u', t2)" unfolding P2' by (simp add: propT_def)
  have H: "set (hyps_of th1 @ hyps_of th2) = set (hyps_of th1) \<union> set (hyps_of th2)" by simp
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pr assume "bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
        case eq_args (th_prop (rep_of th1)) of Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
        | None \<Rightarrow> raiseW undefined)) = returnW pr"
    then obtain p q where p: "proof_of th1 = returnW p" and q: "proof_of th2 = returnW q"
      and pr: "pr = transitive_proof A u p q"
      using ea1 by (auto simp: bindP_eq_returnP)
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      "prf_idx (\<lambda>i. 0 \<le> i) p" "prf_nolb 0 p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) (transitive_proof A u p q) (th_prop r)"
      unfolding H
      by (rule transitive_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2
        prf_valid_refl_ok[OF vp(1)] prf_valid_refl_ok[OF vq(1)] d1']) simp_all
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) (transitive_proof A u p q)"
      using vp(2) vq(2) pt(2) by (auto simp: transitive_proof_def equality_axm_def pnn_def)
    moreover have "prf_nolb 0 (transitive_proof A u p q)"
      using vp(3) vq(3) wtpD(1)[OF w1, unfolded P1'] by (auto simp: transitive_proof_def equality_axm_def closed_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pr (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pr \<and> prf_nolb 0 pr"
      by (simp add: pr)
  next
    fix z assume "bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
          (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow> ztransitive_proof ztargs T t1 u t2 p q
        | _ \<Rightarrow> raise undefined)) = return z"
    then obtain p q where p: "zproof_of th1 = return p" and q: "zproof_of th2 = return q"
      and z: "ztransitive_proof ztargs A t1 u t2 p q = return z"
      using ea1 ea2 by (auto simp: bindZ_eq_returnZ)
    have vp: "zvalid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))" "zinv p"
      "znolb 0 p" "zhyps_ok p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have zv1: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      and zv2: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      using vp(1) vq(1) by (auto simp: zvalid_def intro: prf_valid_mono)
    note zs = ztransitive_proof_valid[OF ok zv1 zv2 w1 w2 P1' d2 pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)]
      pnn_noneg[OF pt2] _ _ z]
    have zc: "zconsts_ok p" "zconsts_ok q" using vp(2) vq(2) by (simp_all add: zinv_def)
    have cl: "\<not> loose_bvar t1 0" "\<not> loose_bvar u 0" "\<not> loose_bvar t2 0"
      using wtpD(1)[OF w1] wtpD(1)[OF w2] unfolding P1' P2' by (simp_all add: closed_def)
    have "zinv z \<and> znolb 0 z \<and> zhyps_ok z"
    proof (cases "zis_reflexive_proof p \<or> zis_reflexive_proof q")
      case True
      with z have "z = p \<or> z = q" by (auto simp: ztransitive_proof_def split: if_splits)
      with vp(2-4) vq(2-4) show ?thesis by auto
    next
      case False
      with z obtain x y w ax where x: "zterm_of ztargs t1 = return x" and y: "zterm_of ztargs u = return y"
        and w: "zterm_of ztargs t2 = return w"
        and ax: "zaxiom_proof STR ''transitive'' [(tvar_a, ztyp_of A)] [(STR ''x'', x), (STR ''y'', y), (STR ''z'', w)] = return ax"
        and zz: "z = ZAppp (ZAppp ax p) q"
        by (auto simp: ztransitive_proof_def bindZ_eq_returnZ)
      have "zinv ax \<and> znolb 0 ax \<and> zhyps ax = {}"
        by (rule zaxiom_proof_ok[OF ax])
          (use zterm_ok_zterm_of_pnn[OF x pt(1)] zterm_ok_zterm_of_pnn[OF y pt(2)] zterm_ok_zterm_of_pnn[OF w pt2]
            zloose_zterm_of[OF x] zloose_zterm_of[OF y] zloose_zterm_of[OF w] cl ztyp_ok_ztyp_of[OF tA]
            in \<open>auto simp: zeq_vars_def\<close>)
      with vp(2-4) vq(2-4) show ?thesis by (auto simp: zz zhyps_ok_def)
    qed
    with zs(1)[OF zc] show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and>
        zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by simp
  qed
qed

lemma prf2_returnW:
  assumes "prf2 f th1 th2 = returnW pf" and "app2_args (th_prop (rep_of th1)) = Some (A, B)"
  obtains p q where "proof_of th1 = returnW p" "proof_of th2 = returnW q" "pf = f A B p q"
  using assms by (auto simp: prf2_def bindP_eq_returnP)

lemma proofs_ok_equal_intr:
  fixes th1 th2 :: "'u pure_thm"
  assumes ok: "okT (equal_intr (rep_of th1) (rep_of th2)) r" and c: "sign_of th2 = sign_of th1"
    and se: "sign_eq (sign_of th1)"
    and po_th1: "is_prf_sig (sign_of th1) \<Longrightarrow> proofs_ok (rep_thm th1)"
    and po_th2: "is_prf_sig (sign_of th2) \<Longrightarrow> proofs_ok (rep_thm th2)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig_gen.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain A B B' A' P where d1: "dest_imp (th_prop (rep_of th1)) = Some (A, B)"
    and mk: "ok (mk_equals (A, B)) P"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) P"
    by (auto simp: equal_intr_def returnW_def raiseW_def split: option.splits if_splits prod.splits)
  have common: "\<exists>A B. th_prop (rep_of th1) = implies $ A $ B \<and> th_prop r = eq_const propT $ A $ B \<and>
      pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (eq_const propT $ A $ B)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w1: "wtp (th_prop (rep_of th1))"
      using pure_thm_wf[of th1] ps by (simp add: thm_wf_def wt_thm_def)
    note dw1 = dest_imp_wtp[OF d1 w1]
    have P: "P = eq_const propT $ A $ B" by (rule mk_equals_ok[OF mk wtpD(1)[OF dw1(2)] wtpD(2)[OF dw1(2)]])
    have "wtp (eq_const propT $ A $ B)"
    proof (rule wtpI)
      show "closed (eq_const propT $ A $ B)" using wtpD(1)[OF dw1(2)] wtpD(1)[OF dw1(3)] by (simp add: closed_def)
      from eq obtain v S where cc: "sg_consts ?c STR ''Pure.eq'' = Some (TVar v S \<rightarrow>\<^sub>T TVar v S \<rightarrow>\<^sub>T propT)"
        by (auto simp: eq_ok_def)
      have ct: "const_typ_ok (sg_consts ?c) STR ''Pure.eq'' (propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT)"
        unfolding const_typ_ok_def using cc by (auto intro!: exI[of _ "\<lambda>_ _. propT"] simp: propT_def)
      show "(\<lambda>_. propT) \<turnstile> eq_const propT $ A $ B : propT"
        using wtpD(2)[OF dw1(2)] wtpD(2)[OF dw1(3)] ct typing_cert_closed[OF wtpD(2)[OF dw1(2)] wtpD(1)[OF dw1(2)]]
        by (auto simp: cert_typ_fun)
    qed
    with dw1(1) P show ?thesis by (auto simp: r mk_rep_def)
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def)
  have p1: "proofs_ok (rep_thm th1)" by (rule po_th1) (use psig in simp)
  have p2: "proofs_ok (rep_thm th2)" by (rule po_th2) (use psig c in simp)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  from common ps obtain A B where P1': "th_prop (rep_of th1) = implies $ A $ B" by blast
  have wf1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
    using pure_thm_wf[of th1] ps by simp
  have wf2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
    using pure_thm_wf[of th2] ps c by simp
  have w1: "wtp (th_prop (rep_of th1))" and w2: "wtp (th_prop (rep_of th2))"
    using wf1 wf2 by (simp_all add: thm_wf_def wt_thm_def)
  have pt: "pnn A" "pnn B" using thm_wf_pnn(1)[OF wf1] unfolding P1' by (simp_all add: implies_def)
  have ea: "app2_args (th_prop (rep_of th1)) = Some (A, B)" unfolding P1' by (simp add: implies_def)
  have H: "set (hyps_of th1 @ hyps_of th2) = set (hyps_of th1) \<union> set (hyps_of th2)" by simp
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pr assume "prf2 equal_intr_proof th1 th2 = returnW pr"
    then obtain p q where p: "proof_of th1 = returnW p" and q: "proof_of th2 = returnW q"
      and pr: "pr = equal_intr_proof A B p q"
      using ea by (rule prf2_returnW)
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      "prf_idx (\<lambda>i. 0 \<le> i) p" "prf_nolb 0 p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) (equal_intr_proof A B p q) (th_prop r)"
      unfolding H
      by (rule equal_intr_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2 P1']) simp_all
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) (equal_intr_proof A B p q)"
      using vp(2) vq(2) pt by (auto simp: equal_intr_proof_def equality_axm_def pnn_def)
    moreover have "prf_nolb 0 (equal_intr_proof A B p q)"
      using vp(3) vq(3) wtpD(1)[OF w1, unfolded P1'] by (auto simp: equal_intr_proof_def equality_axm_def closed_def implies_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pr (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pr \<and> prf_nolb 0 pr"
      by (simp add: pr)
  next
    fix z assume "zprf2 zequal_intr_proof th1 th2 = return z"
    then obtain p q where p: "zproof_of th1 = return p" and q: "zproof_of th2 = return q"
      and z: "zequal_intr_proof ztargs A B p q = return z"
      using ea by (rule zprf2_return)
    have vp: "zvalid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))" "zinv p"
      "znolb 0 p" "zhyps_ok p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have zv1: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      and zv2: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      using vp(1) vq(1) by (auto simp: zvalid_def intro: prf_valid_mono)
    have zc: "zconsts_ok p" "zconsts_ok q" using vp(2) vq(2) by (simp_all add: zinv_def)
    note zs = zequal_intr_proof_valid[OF ok zv1 zv2 w1 w2 P1' pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)] zc z]
    from z obtain a b ax where a: "zterm_of ztargs A = return a" and b: "zterm_of ztargs B = return b"
      and ax: "zaxiom_proof STR ''equal_intr'' [] [(STR ''A'', a), (STR ''B'', b)] = return ax"
      and zz: "z = ZAppp (ZAppp ax p) q"
      by (auto simp: zequal_intr_proof_def bindZ_eq_returnZ)
    have cl: "\<not> loose_bvar A 0" "\<not> loose_bvar B 0"
      using wtpD(1)[OF w1] unfolding P1' by (simp_all add: closed_def implies_def)
    have "zinv ax \<and> znolb 0 ax \<and> zhyps ax = {}"
      by (rule zaxiom_proof_ok[OF ax])
        (use zterm_ok_zterm_of_pnn[OF a pt(1)] zterm_ok_zterm_of_pnn[OF b pt(2)]
          zloose_zterm_of[OF a] zloose_zterm_of[OF b] cl in \<open>auto simp: zeq_vars_def\<close>)
    with vp(2-4) vq(2-4) have "zinv z \<and> znolb 0 z \<and> zhyps_ok z" by (auto simp: zz zhyps_ok_def)
    with zs show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps_ok z"
      by simp
  qed
qed

lemma proofs_ok_equal_elim:
  fixes th1 th2 :: "'u pure_thm"
  assumes ok: "okT (equal_elim (rep_of th1) (rep_of th2)) r" and c: "sign_of th2 = sign_of th1"
    and se: "sign_eq (sign_of th1)"
    and po_th1: "is_prf_sig (sign_of th1) \<Longrightarrow> proofs_ok (rep_thm th1)"
    and po_th2: "is_prf_sig (sign_of th2) \<Longrightarrow> proofs_ok (rep_thm th2)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig_gen.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain A B where d: "dest_eq_any (th_prop (rep_of th1)) = Some (A, B)"
    and a: "aconv_term (th_prop (rep_of th2)) A"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) B"
    by (auto simp: equal_elim_def returnW_def raiseW_def split: option.splits if_splits)
  have common: "\<exists>A B. th_prop (rep_of th1) = eq_const propT $ A $ B \<and> th_prop r = B \<and>
      pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) B"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w1: "wtp (th_prop (rep_of th1))" and w2: "wtp (th_prop (rep_of th2))"
      using pure_thm_wf[of th1] pure_thm_wf[of th2] ps c by (simp_all add: thm_wf_def wt_thm_def)
    obtain T where P: "th_prop (rep_of th1) = eq_const T $ A $ B" and cB: "closed B"
      and ty: "\<And>e. e \<turnstile> A : T" "\<And>e. e \<turnstile> B : T"
      using dest_eq_any_wtp[OF eq d w1] by blast
    have T: "T = propT" using typing_aconv[OF a wtpD(2)[OF w2]] ty(1) typing_unique by metis
    have "wtp B" using cB ty(2) T by (auto intro: wtpI)
    with P T show ?thesis by (auto simp: r mk_rep_def)
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def)
  have p1: "proofs_ok (rep_thm th1)" by (rule po_th1) (use psig in simp)
  have p2: "proofs_ok (rep_thm th2)" by (rule po_th2) (use psig c in simp)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  from common ps obtain A B where P1': "th_prop (rep_of th1) = eq_const propT $ A $ B" by blast
  have wf1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
    using pure_thm_wf[of th1] ps by simp
  have wf2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
    using pure_thm_wf[of th2] ps c by simp
  have w1: "wtp (th_prop (rep_of th1))" and w2: "wtp (th_prop (rep_of th2))"
    using wf1 wf2 by (simp_all add: thm_wf_def wt_thm_def)
  have pt: "pnn A" "pnn B" using thm_wf_pnn(1)[OF wf1] unfolding P1' by (simp_all add: propT_def)
  have ea: "app2_args (th_prop (rep_of th1)) = Some (A, B)" unfolding P1' by (simp add: propT_def)
  have H: "set (hyps_of th1 @ hyps_of th2) = set (hyps_of th1) \<union> set (hyps_of th2)" by simp
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pr assume "prf2 equal_elim_proof th1 th2 = returnW pr"
    then obtain p q where p: "proof_of th1 = returnW p" and q: "proof_of th2 = returnW q"
      and pr: "pr = equal_elim_proof A B p q"
      using ea by (rule prf2_returnW)
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      "prf_idx (\<lambda>i. 0 \<le> i) p" "prf_nolb 0 p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) (equal_elim_proof A B p q) (th_prop r)"
      unfolding H
      by (rule equal_elim_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2 P1']) simp_all
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) (equal_elim_proof A B p q)"
      using vp(2) vq(2) pt by (auto simp: equal_elim_proof_def equality_axm_def pnn_def)
    moreover have "prf_nolb 0 (equal_elim_proof A B p q)"
      using vp(3) vq(3) wtpD(1)[OF w1, unfolded P1'] by (auto simp: equal_elim_proof_def equality_axm_def closed_def propT_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pr (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pr \<and> prf_nolb 0 pr"
      by (simp add: pr)
  next
    fix z assume "zprf2 zequal_elim_proof th1 th2 = return z"
    then obtain p q where p: "zproof_of th1 = return p" and q: "zproof_of th2 = return q"
      and z: "zequal_elim_proof ztargs A B p q = return z"
      using ea by (rule zprf2_return)
    have vp: "zvalid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))" "zinv p"
      "znolb 0 p" "zhyps_ok p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have zv1: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      and zv2: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      using vp(1) vq(1) by (auto simp: zvalid_def intro: prf_valid_mono)
    have zc: "zconsts_ok p" "zconsts_ok q" using vp(2) vq(2) by (simp_all add: zinv_def)
    note zs = zequal_elim_proof_valid[OF ok zv1 zv2 w1 w2 P1' pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)] zc z]
    from z obtain a b ax where a: "zterm_of ztargs A = return a" and b: "zterm_of ztargs B = return b"
      and ax: "zaxiom_proof STR ''equal_elim'' [] [(STR ''A'', a), (STR ''B'', b)] = return ax"
      and zz: "z = ZAppp (ZAppp ax p) q"
      by (auto simp: zequal_elim_proof_def bindZ_eq_returnZ)
    have cl: "\<not> loose_bvar A 0" "\<not> loose_bvar B 0"
      using wtpD(1)[OF w1] unfolding P1' by (simp_all add: closed_def propT_def)
    have "zinv ax \<and> znolb 0 ax \<and> zhyps ax = {}"
      by (rule zaxiom_proof_ok[OF ax])
        (use zterm_ok_zterm_of_pnn[OF a pt(1)] zterm_ok_zterm_of_pnn[OF b pt(2)]
          zloose_zterm_of[OF a] zloose_zterm_of[OF b] cl in \<open>auto simp: zeq_vars_def\<close>)
    with vp(2-4) vq(2-4) have "zinv z \<and> znolb 0 z \<and> zhyps_ok z" by (auto simp: zz zhyps_ok_def)
    with zs show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps_ok z"
      by simp
  qed
qed

context prf_sig
begin

lemma vars_comb_arg: "x \<in> set_option (comb_arg f t) \<Longrightarrow> vars x = vars t"
  by (auto simp: comb_arg_def split: pterm.splits)

lemma prf_idx_combination_proof:
  assumes cp: "combination_proof f g t u p q = returnW pf" and p: "prf_idx P p" and q: "prf_idx P q"
    and v: "\<forall>v\<in>vars f \<union> vars g \<union> vars t \<union> vars u. P (snd (fst v))"
  shows "prf_idx P pf"
proof -
  have lr: "ok m x" if "liftMP m = returnW x" for m :: "prf M" and x
    using that by (cases m) (auto simp: liftMP_def returnW_def)
  from lr[OF cp[unfolded combination_proof_def]] obtain fn gn where fn: "ok (beta_norm f) fn" and gn: "ok (beta_norm g) gn"
    and pf: "pf = PAppp (PAppp (PAppt (PAppt
      (if check_comb p then PAppt (PAppt (equality_axm STR ''combination'') None) None
       else if is_reflexive_proof p then PAppt (equality_axm STR ''combination'' %> remove_types fn) None
       else equality_axm STR ''combination'' %> remove_types fn %> remove_types gn)
      (comb_arg fn t)) (comb_arg gn u)) p) q"
    by (auto simp: Let_def)
  have "vars fn \<subseteq> vars f" "vars gn \<subseteq> vars g"
    by (rule beta_reds_vars[OF beta_norm_reds[OF fn]], rule beta_reds_vars[OF beta_norm_reds[OF gn]])
  then show ?thesis using p q v vars_comb_arg[of _ fn t] vars_comb_arg[of _ gn u]
    by (auto simp: pf equality_axm_def)
qed

lemma prf_nolb_combination_proof:
  assumes cp: "combination_proof f g t u p q = returnW pf" and p: "prf_nolb 0 p" and q: "prf_nolb 0 q"
    and c: "\<not> loose_bvar f 0" "\<not> loose_bvar g 0" "\<not> loose_bvar t 0" "\<not> loose_bvar u 0"
  shows "prf_nolb 0 pf"
proof -
  have lr: "ok m x" if "liftMP m = returnW x" for m :: "prf M" and x
    using that by (cases m) (auto simp: liftMP_def returnW_def)
  from lr[OF cp[unfolded combination_proof_def]] obtain fn gn where fn: "ok (beta_norm f) fn" and gn: "ok (beta_norm g) gn"
    and pf: "pf = PAppp (PAppp (PAppt (PAppt
      (if check_comb p then PAppt (PAppt (equality_axm STR ''combination'') None) None
       else if is_reflexive_proof p then PAppt (equality_axm STR ''combination'' %> remove_types fn) None
       else equality_axm STR ''combination'' %> remove_types fn %> remove_types gn)
      (comb_arg fn t)) (comb_arg gn u)) p) q"
    by (auto simp: Let_def)
  have "\<not> loose_bvar fn 0" "\<not> loose_bvar gn 0"
    using beta_reds_loose_bvar[OF beta_norm_reds[OF fn] _ c(1)] beta_reds_loose_bvar[OF beta_norm_reds[OF gn] _ c(2)]
    by simp_all
  moreover have "\<not> loose_bvar x 0" if "x \<in> set_option (comb_arg h v)" "\<not> loose_bvar v 0" for x h v
    using that by (auto simp: comb_arg_def split: pterm.splits)
  ultimately show ?thesis using p q c by (auto simp: pf equality_axm_def)
qed

end

lemma proofs_ok_combination:
  fixes th1 th2 :: "'u pure_thm"
  assumes res: "okT (combination_res (rep_of th1) (rep_of th2)) (r, T1, U, f, g, t, u)"
    and c: "sign_of th2 = sign_of th1" and se: "sign_eq (sign_of th1)"
    and po_th1: "is_prf_sig (sign_of th1) \<Longrightarrow> proofs_ok (rep_thm th1)"
    and po_th2: "is_prf_sig (sign_of th2) \<Longrightarrow> proofs_ok (rep_thm th2)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
    (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
      zcombination_proof (pure_sig_gen.ztargs (sg_consts (sign_of th1))) T1 U f g t u p q))))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
    (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
      zcombination_proof (pure_sig_gen.ztargs (sg_consts (sign_of th1))) T1 U f g t u p q))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig_gen.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  note ok = combination_res_ok(1)[OF res] and cd = combination_res_ok(2)[OF res]
  define fT where "fT = T1 \<rightarrow>\<^sub>T U"
  have d1: "dest_eq_fun (th_prop (rep_of th1)) = Some (fT, f, g)"
    and d2: "dest_eq_fun (th_prop (rep_of th2)) = Some (T1, t, u)" and fT: "fT = T1 \<rightarrow>\<^sub>T U"
    using combination_data_okE[OF cd] by (simp_all add: fT_def)
  from ok obtain fT' U' f' g' t' u' P where cd': "okT (combination_data (rep_of th1) (rep_of th2)) (fT', U', f', g', t', u')"
    and mk: "ok (mk_equals (f' $ t', g' $ u')) P"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) P"
    by (auto simp: combination_def)
  have same: "fT' = T1" "U' = U" "f' = f" "g' = g" "t' = t" "u' = u" using cd cd' by auto
  have common: "th_prop (rep_of th1) = eq_const fT $ f $ g \<and> th_prop (rep_of th2) = eq_const T1 $ t $ u \<and>
      th_prop r = eq_const U $ (f $ t) $ (g $ u) \<and>
      pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (eq_const U $ (f $ t) $ (g $ u))"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have w1: "wtp (th_prop (rep_of th1))" and w2: "wtp (th_prop (rep_of th2))"
      using pure_thm_wf[of th1] pure_thm_wf[of th2] ps c by (simp_all add: thm_wf_def wt_thm_def)
    note d1' = dest_eq_any_dest_eq_fun[OF d1] and d2' = dest_eq_any_dest_eq_fun[OF d2]
    obtain A where P1: "th_prop (rep_of th1) = eq_const A $ f $ g" and c1: "closed f" "closed g"
      and ty1: "\<And>e. e \<turnstile> f : A" "\<And>e. e \<turnstile> g : A"
      using dest_eq_any_wtp[OF eq d1' w1] by blast
    obtain B where P2: "th_prop (rep_of th2) = eq_const B $ t $ u" and c2: "closed t" "closed u"
      and ty2: "\<And>e. e \<turnstile> t : B" "\<And>e. e \<turnstile> u : B"
      using dest_eq_any_wtp[OF eq d2' w2] by blast
    from d1 P1 have A: "A = fT" by (simp add: propT_def)
    from d2 P2 have B: "B = T1" by (simp add: propT_def)
    have tft: "e \<turnstile> f $ t : U" "e \<turnstile> g $ u : U" for e using ty1 ty2 A B fT by auto
    have cft: "closed (f $ t)" "closed (g $ u)" using c1 c2 by (simp_all add: closed_def)
    have P: "P = eq_const U $ (f $ t) $ (g $ u)" using mk_equals_ok[OF mk[unfolded same] cft(1) tft(1)] .
    have "wtp (eq_const U $ (f $ t) $ (g $ u))"
    proof (rule wtpI)
      show "closed (eq_const U $ (f $ t) $ (g $ u))" using cft by (simp add: closed_def)
      from eq obtain v S where cc: "sg_consts ?c STR ''Pure.eq'' = Some (TVar v S \<rightarrow>\<^sub>T TVar v S \<rightarrow>\<^sub>T propT)"
        by (auto simp: eq_ok_def)
      have ct: "const_typ_ok (sg_consts ?c) STR ''Pure.eq'' (U \<rightarrow>\<^sub>T U \<rightarrow>\<^sub>T propT)"
        unfolding const_typ_ok_def using cc by (auto intro!: exI[of _ "\<lambda>_ _. U"] simp: propT_def)
      have cU: "cert_typ (sg_alg ?c) (sg_ar ?c) U" by (rule typing_cert_closed[OF tft(1) cft(1)])
      have cP: "cert_typ (sg_alg ?c) (sg_ar ?c) propT"
        using typing_cert_closed[OF wtpD(2)[OF w1] wtpD(1)[OF w1]] .
      show "(\<lambda>_. propT) \<turnstile> eq_const U $ (f $ t) $ (g $ u) : propT"
      proof -
        have tc: "(\<lambda>_. propT) \<turnstile> eq_const U : U \<rightarrow>\<^sub>T U \<rightarrow>\<^sub>T propT"
          using ct cU cP by (intro typing.Const) (simp_all add: cert_typ_fun)
        show ?thesis by (rule typing.App[OF typing.App[OF tc tft(1)] tft(2)])
      qed
    qed
    with P1 P2 A B P show ?thesis by (simp add: r mk_rep_def)
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def)
  have p1: "proofs_ok (rep_thm th1)" by (rule po_th1) (use psig in simp)
  have p2: "proofs_ok (rep_thm th2)" by (rule po_th2) (use psig c in simp)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  from common ps have P1': "th_prop (rep_of th1) = eq_const fT $ f $ g"
    and P2': "th_prop (rep_of th2) = eq_const T1 $ t $ u" by auto
  have wf1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
    using pure_thm_wf[of th1] ps by simp
  have wf2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
    using pure_thm_wf[of th2] ps c by simp
  have w1: "wtp (th_prop (rep_of th1))" and w2: "wtp (th_prop (rep_of th2))"
    using wf1 wf2 by (simp_all add: thm_wf_def wt_thm_def)
  have pt: "pnn f" "pnn g" using thm_wf_pnn(1)[OF wf1] unfolding P1' by simp_all
  have pt2: "pnn t" "pnn u" using thm_wf_pnn(1)[OF wf2] unfolding P2' by simp_all
  have tTU: "tnn T1" "tnn U" using thm_wf_pnn(1)[OF wf1] unfolding P1' fT_def by (simp_all add: pnn_def)
  have H: "set (hyps_of th1 @ hyps_of th2) = set (hyps_of th1) \<union> set (hyps_of th2)" by simp
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)) = returnW pf"
    then obtain p q where p: "proof_of th1 = returnW p" and q: "proof_of th2 = returnW q"
      and cp: "combination_proof f g t u p q = returnW pf"
      by (auto simp: bindP_eq_returnP)
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      "prf_idx (\<lambda>i. 0 \<le> i) p" "prf_nolb 0 p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pf (th_prop r)"
      unfolding H by (rule combination_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2 cd cp])
        simp_all
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
      by (rule prf_idx_combination_proof[OF cp vp(2) vq(2)]) (use pt pt2 in \<open>auto simp: pnn_def\<close>)
    moreover have "prf_nolb 0 pf"
      by (rule prf_nolb_combination_proof[OF cp vp(3) vq(3)])
        (use wtpD(1)[OF w1, unfolded P1'] wtpD(1)[OF w2, unfolded P2'] in \<open>auto simp: closed_def\<close>)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
      by simp
  next
    fix z assume "bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        zcombination_proof ztargs T1 U f g t u p q)) = return z"
    then obtain p q where p: "zproof_of th1 = return p" and q: "zproof_of th2 = return q"
      and z: "zcombination_proof ztargs T1 U f g t u p q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vp: "zvalid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))" "zinv p"
      "znolb 0 p" "zhyps_ok p"
      using p1 p by (simp_all add: proofs_ok_def Let_def)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p2 q c by (simp_all add: proofs_ok_def Let_def)
    have zv1: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
      and zv2: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
      using vp(1) vq(1) by (auto simp: zvalid_def intro: prf_valid_mono)
    have zc: "zconsts_ok p" "zconsts_ok q" using vp(2) vq(2) by (simp_all add: zinv_def)
    note zs = zcombination_proof_valid[OF ok zv1 zv2 w1 w2 cd pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)]
      pnn_noneg[OF pt2(1)] pnn_noneg[OF pt2(2)] zc z]
    from z obtain f' g' x y ax where f': "zterm_of ztargs f = return f'" and g': "zterm_of ztargs g = return g'"
      and x: "zterm_of ztargs t = return x" and y: "zterm_of ztargs u = return y"
      and ax: "zaxiom_proof STR ''combination'' [(tvar_a, ztyp_of T1), (tvar_b, ztyp_of U)]
        [(STR ''f'', f'), (STR ''g'', g'), (STR ''x'', x), (STR ''y'', y)] = return ax"
      and zz: "z = ZAppp (ZAppp ax p) q"
      by (auto simp: zcombination_proof_def bindZ_eq_returnZ)
    have cl: "\<not> loose_bvar f 0" "\<not> loose_bvar g 0" "\<not> loose_bvar t 0" "\<not> loose_bvar u 0"
      using wtpD(1)[OF w1] wtpD(1)[OF w2] unfolding P1' P2' by (simp_all add: closed_def)
    have "zinv ax \<and> znolb 0 ax \<and> zhyps ax = {}"
      by (rule zaxiom_proof_ok[OF ax])
        (use zterm_ok_zterm_of_pnn[OF f' pt(1)] zterm_ok_zterm_of_pnn[OF g' pt(2)]
          zterm_ok_zterm_of_pnn[OF x pt2(1)] zterm_ok_zterm_of_pnn[OF y pt2(2)]
          zloose_zterm_of[OF f'] zloose_zterm_of[OF g'] zloose_zterm_of[OF x] zloose_zterm_of[OF y] cl
          ztyp_ok_ztyp_of[OF tTU(1)] ztyp_ok_ztyp_of[OF tTU(2)]
          in \<open>auto simp: zeq_vars_def\<close>)
    with vp(2-4) vq(2-4) have "zinv z \<and> znolb 0 z \<and> zhyps_ok z" by (auto simp: zz zhyps_ok_def)
    with zs show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps_ok z"
      by simp
  qed
qed

lemma proofs_ok_assume:
  fixes ct :: pure_cterm
  assumes ok: "okT (assume_rule (crep_of ct)) r"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct) [ct_t (crep_of ct)] (csign_of ct)
    (returnW (Hyp (ct_t (crep_of ct)))) (zassume_proof (pure_sig_gen.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct) [ct_t (crep_of ct)] (csign_of ct)
    (returnW (Hyp (ct_t (crep_of ct)))) (zassume_proof (pure_sig_gen.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "csign_of ct" and ?t = "ct_t (crep_of ct)"
  note a = assume_rule_ok[OF ok]
  have common: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) ?t \<and> vars ?t = {} \<and> ttvars ?t = {}"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (crep_of ct)" by (rule pure_cterm_wf) (rule ps)
    have "wtp ?t" using wf a(1) by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
    with cterm_wf_novars[OF wf a(3)] show ?thesis by simp
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  from common[OF ps] have w: "wtp ?t" and v: "vars ?t = {}" "ttvars ?t = {}" by simp_all
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "returnW (Hyp ?t) = returnW pf"
    then have pf: "pf = Hyp ?t" by (simp add: returnW_def)
    have "prf_valid (sg_ax ?c) (set [?t]) [] (Hyp ?t) ?t" by (rule assume_proof_valid) (use w v in simp_all)
    then show "prf_valid (sg_ax ?c) (set [?t]) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and>
        prf_nolb 0 pf"
      by (simp add: pf a(2) mk_rep_def)
  next
    fix z assume z: "zassume_proof ztargs ?t = return z"
    have "zvalid (sg_ax ?c) (set [?t]) [] z ?t" by (rule zassume_proof_valid[OF z]) (use w v in simp_all)
    moreover from z obtain A' where A': "zterm_of ztargs ?t = return A'" and zA: "z = ZHyp A'"
      by (auto simp: zassume_proof_def bindZ_eq_returnZ)
    moreover have "pnn ?t" using v by (simp add: pnn_iff)
    then have "zterm_of ztargs (zdec A') = return A'" by (rule zhyps_ok_zterm_of[OF A' wtpD(2)[OF w]])
    ultimately show "zvalid (sg_ax ?c) (set [?t]) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: a(2) mk_rep_def zhyps_ok_def)
  qed
qed

lemma proofs_ok_conversion:
  fixes ct :: pure_cterm
  assumes ok: "okT (f (crep_of ct)) r" and se: "sign_eq (csign_of ct)"
    and cf: "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) \<Longrightarrow>
      pure_sig.conv_ok (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) f"
  shows "is_prf_sig (th_sign (conv_data ct r)) \<Longrightarrow>
    proofs_ok (conv_data ct r)"
proof -
  let ?c = "csign_of ct"
  obtain t T m where cr: "crep_of ct = CTerm t T m" by (cases "crep_of ct")
  have ok': "okT (f (CTerm t T m)) r" using ok by (simp add: cr)
  have eq: "pure_sig_gen.eq_ok (sg_consts ?c)" and pr: "sg_ar ?c STR ''prop'' = 0" using se by (simp_all add: sign_eq_def)
  have th: "th_sign (conv_data ct r) = ?c" "th_shyps (conv_data ct r) = csorts_of ct" "th_hyps (conv_data ct r) = []"
    "th_maxidx (conv_data ct r) = th_maxidx r" "th_tpairs (conv_data ct r) = th_tpairs r" "th_prop (conv_data ct r) = th_prop r"
    by (simp_all add: conv_data_def)
  assume psig: "is_prf_sig (th_sign (conv_data ct r))"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def th)
  have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def th)
  have wf: "cterm_wf (CTerm t T m)" using pure_cterm_wf[OF ps'] by (simp add: cr)
  obtain t' where r: "r = mk_rep m [] (eq_const T $ t $ t')" and c: "closed t" "closed t'"
    and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T" and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
    and v: "vars t' \<subseteq> vars t" and tv: "ttvars t' \<subseteq> ttvars t"
    by (rule conv_ok_result[OF cf[OF ps'] ok' wf]) blast
  have pt: "pnn t" using wf by (simp add: cterm_wf_def pnn_iff)
  have tT: "tnn T" by (rule tnn_typing[OF ty(1)[of "\<lambda>_. propT"]]) (use pt in \<open>simp_all add: pnn_def tnn_def propT_def\<close>)
  show "proofs_ok (conv_data ct r)"
    unfolding proofs_ok_def Let_def th
  proof (rule conjI; intro allI impI)
    fix pf assume "th_proof (conv_data ct r) = returnW pf"
    then have pf: "pf = reflexive_proof" by (simp add: conv_data_def returnW_def)
    have "prf_valid (sg_ax ?c) {} [] reflexive_proof (eq_const T $ t $ t')"
      by (rule reflexive_proof_conv_valid[OF c ty cv])
    then show "prf_valid (sg_ax ?c) (set []) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and>
        prf_nolb 0 pf"
      by (simp add: r pf mk_rep_def reflexive_proof_def equality_axm_def)
  next
    fix z assume "th_zproof (conv_data ct r) = return z"
    then have z: "zreflexive_proof ztargs T t = return z" by (simp add: conv_data_def cr)
    note v = zreflexive_conv_proof_valid[OF z c ty cv pnn_noneg[OF pt]]
    from z obtain x where x: "zterm_of ztargs t = return x"
      and ax: "zaxiom_proof STR ''reflexive'' [(tvar_a, ztyp_of T)] [(STR ''x'', x)] = return z"
      by (auto simp: zreflexive_proof_def bindZ_eq_returnZ)
    have "zinv z \<and> znolb 0 z \<and> zhyps z = {}"
      by (rule zaxiom_proof_ok[OF ax])
        (use zterm_ok_zterm_of_pnn[OF x pt] zloose_zterm_of[OF x] c(1) ztyp_ok_ztyp_of[OF tT]
          in \<open>auto simp: zeq_vars_def closed_def\<close>)
    with v(1) show "zvalid (sg_ax ?c) (set []) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: r mk_rep_def zhyps_ok_def)
  qed
qed

lemma proofs_ok_trivial:
  fixes ct :: pure_cterm
  assumes ok: "okT (trivial (crep_of ct)) r"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct) [] (csign_of ct)
    (returnW trivial_proof) (ztrivial_proof (pure_sig_gen.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct) [] (csign_of ct)
    (returnW trivial_proof) (ztrivial_proof (pure_sig_gen.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "csign_of ct"
  obtain t T m where cr: "crep_of ct = CTerm t T m" by (cases "crep_of ct")
  from ok have T: "T = propT" and r: "r = mk_rep m [] (implies $ t $ t)"
    by (auto simp: trivial_def cr returnW_def raiseW_def mk_implies_def split: if_splits)
  have common: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) t \<and>
      pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm t T m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm t T m)" using pure_cterm_wf[OF ps] by (simp add: cr)
    then have "wtp t" using T by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
    with wf show ?thesis by simp
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  from common[OF ps] have w: "wtp t" and wf: "cterm_wf (CTerm t T m)" by simp_all
  have pt: "pnn t" using wf by (simp add: cterm_wf_def pnn_iff)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "returnW trivial_proof = returnW pf"
    then have pf: "pf = trivial_proof" by (simp add: returnW_def)
    have "prf_valid (sg_ax ?c) (set []) [] trivial_proof (implies $ t $ t)" by (rule trivial_proof_valid[OF w])
    then show "prf_valid (sg_ax ?c) (set []) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and>
        prf_nolb 0 pf"
      by (simp add: pf r mk_rep_def trivial_proof_def)
  next
    fix z assume z: "ztrivial_proof ztargs (ct_t (crep_of ct)) = return z"
    then have z': "ztrivial_proof ztargs t = return z" by (simp add: cr)
    have "zvalid (sg_ax ?c) (set []) [] z (implies $ t $ t)"
      by (rule ztrivial_proof_valid[OF z' w pnn_noneg[OF pt]])
    moreover have "zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      using z' zterm_ok_zterm_of_pnn[OF _ pt] zloose_zterm_of wtpD(1)[OF w]
      by (auto simp: ztrivial_proof_def bindZ_eq_returnZ zhyps_ok_def closed_def)
    ultimately show "zvalid (sg_ax ?c) (set []) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: r mk_rep_def)
  qed
qed

lemma proofs_ok_weaken:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (weaken (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct \<union> shyps_of th) (ct_t (crep_of ct) # hyps_of th) (sign_of th)
    (proof_of th) (zproof_of th))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct \<union> shyps_of th) (ct_t (crep_of ct) # hyps_of th) (sign_of th)
    (proof_of th) (zproof_of th))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th" and ?t = "ct_t (crep_of ct)"
  note a = weaken_ok[OF ok]
  have common: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) ?t \<and> vars ?t = {} \<and> ttvars ?t = {}"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (crep_of ct)" using pure_cterm_wf[of ct] ps c by simp
    have "wtp ?t" using wf a(1) by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
    with cterm_wf_novars[OF wf a(3)] show ?thesis by simp
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume pf: "proof_of th = returnW pf"
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using p pf by (simp_all add: proofs_ok_def Let_def)
    show "prf_valid (sg_ax ?c) (set (?t # hyps_of th)) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and>
        prf_nolb 0 pf"
      using weaken_proof_valid[OF ok vp(1)] vp(2,3) by simp
  next
    fix z assume z: "zproof_of th = return z"
    have vz: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z (th_prop (rep_of th))" "zinv z"
      "znolb 0 z" "zhyps_ok z"
      using p z by (simp_all add: proofs_ok_def Let_def)
    show "zvalid (sg_ax ?c) (set (?t # hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      using zweaken_proof_valid[OF ok vz(1)] vz(2-4) by simp
  qed
qed

lemma proofs_ok_forall_elim:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (forall_elim (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (PAppt p (Some (ct_t (crep_of ct))))))
    (bindM (zproof_of th) (\<lambda>p. zforall_elim_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)) p)))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (PAppt p (Some (ct_t (crep_of ct))))))
    (bindM (zproof_of th) (\<lambda>p. zforall_elim_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)) p)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  obtain t T m where cr: "crep_of ct = CTerm t T m" by (cases "crep_of ct")
  have ok': "okT (forall_elim (CTerm t T m) (rep_of th)) r" using ok by (simp add: cr)
  from ok' obtain A where d: "dest_all_app (th_prop (rep_of th)) = Some (T, A)"
    and r: "r = mk_rep (max m (th_maxidx (rep_of th))) (th_tpairs (rep_of th)) (betapply A t)"
    by (auto simp: forall_elim_def returnW_def raiseW_def split: option.splits if_splits)
  have wfc: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm t T m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" for ps
    using pure_cterm_wf[of ct] ps c by (simp add: cr)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have wf: "cterm_wf (CTerm t T m)" by (rule wfc[OF ps])
  have ct: "closed t" "\<And>e. e \<turnstile> t : T" using wf by (simp_all add: cterm_wf_def)
  have pt: "pnn t" using wf by (simp add: cterm_wf_def pnn_iff)
  have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps by (simp add: thm_wf_def wt_thm_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (PAppt p (Some (ct_t (crep_of ct))))) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = PAppt q (Some t)"
      by (auto simp: bindP_eq_returnP cr)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) (PAppt q (Some t)) (th_prop r)"
      by (rule forall_elim_rule_proof_valid[OF ok' vq(1) w ct])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) (PAppt q (Some t))" using vq(2) wf by (simp add: cterm_wf_def)
    moreover have "prf_nolb 0 (PAppt q (Some t))" using vq(3) ct(1) by (simp add: closed_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and>
        prf_nolb 0 pf"
      by (simp add: pf)
  next
    fix z assume "bindM (zproof_of th) (\<lambda>p. zforall_elim_proof ztargs (ct_t (crep_of ct)) p) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zforall_elim_proof ztargs t q = return z"
      by (auto simp: bindZ_eq_returnZ cr)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zforall_elim_rule_proof_valid[OF ok' vq(1) w ct pnn_noneg[OF pt] z])
    moreover have "zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      using z vq(2-4) zterm_ok_zterm_of_pnn[OF _ pt] zloose_zterm_of ct(1)
      by (auto simp: zforall_elim_proof_def bindZ_eq_returnZ zhyps_ok_def closed_def)
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" by simp
  qed
qed

end
