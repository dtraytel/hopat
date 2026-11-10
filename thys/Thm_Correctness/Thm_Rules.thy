section \<open>Inference rules on the abstract type of theorems\<close>

theory Thm_Rules
  imports Thm_Type
begin

text \<open>
  The primitive inference rules of \<open>thm.ML\<close> as operations on \<^typ>\<open>'u pure_thm\<close>: the logical part
  of the result is computed by the model of the rule, the proofs by the proof constructors of
  \<open>Proofterm\<close> and \<open>ZTerm\<close> from the proofs of the premises. An operation returns \<open>None\<close> if the
  rule raises an exception or if the signatures of its arguments differ
  (\<open>Thm.join_certificate\<close>).
\<close>

definition resT :: "'a T \<Rightarrow> 'a option" where
  "resT m = (case m of Some (_, Ok x) \<Rightarrow> Some x | _ \<Rightarrow> None)"

lemma resT_Some: "resT m = Some x \<longleftrightarrow> okT m x"
  by (auto simp: resT_def split: option.splits xres.splits)

definition mk_thm :: "thm_rep \<Rightarrow> psort set \<Rightarrow> pterm list \<Rightarrow> sign \<Rightarrow> prf P \<Rightarrow> zproof Z \<Rightarrow> thm_data" where
  "mk_thm r Sh hs c p z = \<lparr>th_maxidx = th_maxidx r, th_tpairs = th_tpairs r, th_prop = th_prop r,
    th_shyps = Sh, th_hyps = hs, th_sign = c, th_proof = p, th_zproof = z\<rparr>"

lemma mk_thm_sel [simp]:
  "th_maxidx (mk_thm r Sh hs c p z) = th_maxidx r" "th_tpairs (mk_thm r Sh hs c p z) = th_tpairs r"
  "th_prop (mk_thm r Sh hs c p z) = th_prop r" "th_shyps (mk_thm r Sh hs c p z) = Sh"
  "th_hyps (mk_thm r Sh hs c p z) = hs" "th_sign (mk_thm r Sh hs c p z) = c"
  "th_proof (mk_thm r Sh hs c p z) = p" "th_zproof (mk_thm r Sh hs c p z) = z"
  by (simp_all add: mk_thm_def)

lemma thm_okI:
  assumes "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow>
      pure_sig.thm_wf (sg_alg (th_sign th)) (sg_ar (th_sign th)) (sg_consts (th_sign th))
        (th_maxidx th) (th_hyps th) (th_tpairs th) (th_prop th)"
    and "\<And>M :: 'u model. pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> is_model (th_sign th) M \<Longrightarrow>
      valid_in (th_sign th) M (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)"
    and "is_prf_sig (th_sign th) \<Longrightarrow> proofs_ok th"
  shows "thm_ok TYPE('u) th"
  using assms by (auto simp: thm_ok_def)

lemma pure_thm_valid_in:
  fixes th :: "'u pure_thm" and M :: "'u model"
  shows "is_model (sign_of th) M \<Longrightarrow> pure_model.valid (sg_alg (sign_of th)) (sg_ar (sign_of th)) (sg_consts (sign_of th))
    (m_mem M) (m_fun M) (m_app M) (m_lam M) (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)
    (shyps_of th) (hyps_of th) (th_tpairs (rep_thm th)) (th_prop (rep_thm th))"
  using pure_thm_valid[of th M] by (simp add: valid_in_def)


subsection \<open>Implication elimination\<close>

context pure_sig
begin

lemma thm_wf_implies_elim:
  assumes ok: "okT (implies_elim thAB thA) th"
    and w1: "thm_wf (th_maxidx thAB) hs1 (th_tpairs thAB) (th_prop thAB)"
    and w2: "thm_wf (th_maxidx thA) hs2 (th_tpairs thA) (th_prop thA)"
  shows "thm_wf (th_maxidx th) (hs2 @ hs1) (th_tpairs th) (th_prop th)"
proof -
  from ok obtain A B where d: "dest_imp (th_prop thAB) = Some (A, B)"
    and th: "th = mk_rep (max (th_maxidx thA) (th_maxidx thAB)) (union_tpairs (th_tpairs thA) (th_tpairs thAB)) B"
    by (auto simp: implies_elim_def returnW_def raiseW_def split: option.splits if_splits)
  let ?m = "max (th_maxidx thA) (th_maxidx thAB)"
  have wP: "wtp (th_prop thAB)" using w1 by (simp add: thm_wf_def wt_thm_def)
  note dw = dest_imp_wtp[OF d wP]
  have vB: "vars B \<subseteq> vars (th_prop thAB)" "ttvars B \<subseteq> ttvars (th_prop thAB)"
    by (subst dw(1); auto simp: implies_def)+
  have tps: "set (th_tpairs th) \<subseteq> set (th_tpairs thA) \<union> set (th_tpairs thAB)"
    using union_tpairs_set(1) by (simp add: th mk_rep_def)
  have ib: "ibelow ?m B" using w1 vB by (force simp: thm_wf_def wt_thm_def ibelow_def)
  have hs: "\<forall>h\<in>set (hs2 @ hs1). wtp h \<and> vars h = {} \<and> ttvars h = {}" using w1 w2 by (auto simp: thm_wf_def wt_thm_def)
  have tp: "\<forall>(t, u)\<in>set (th_tpairs th). closed t \<and> closed u \<and> ibelow ?m t \<and> ibelow ?m u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  proof (intro ballI, clarify)
    fix t u assume "(t, u) \<in> set (th_tpairs th)"
    with tps have "(t, u) \<in> set (th_tpairs thA) \<or> (t, u) \<in> set (th_tpairs thAB)" by blast
    then show "closed t \<and> closed u \<and> ibelow ?m t \<and> ibelow ?m u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    proof
      assume "(t, u) \<in> set (th_tpairs thA)"
      with w2 show ?thesis by (fastforce simp: thm_wf_def wt_thm_def intro: ibelow_mono)
    next
      assume "(t, u) \<in> set (th_tpairs thAB)"
      with w1 show ?thesis by (fastforce simp: thm_wf_def wt_thm_def intro: ibelow_mono)
    qed
  qed
  have mm: "-1 \<le> ?m" using w1 by (simp add: thm_wf_def le_max_iff_disj)
  have vn: "0 \<le> snd (fst v)" if "v \<in> vars_thm (th_tpairs th) B" for v
  proof -
    have "v \<in> vars_thm (th_tpairs thA) (th_prop thA) \<or> v \<in> vars_thm (th_tpairs thAB) (th_prop thAB)"
      using that tps vB by (fastforce simp: vars_thm_def)
    with w1 w2 show ?thesis by (auto simp: thm_wf_def)
  qed
  have tn: "0 \<le> snd (fst v)" if "v \<in> tvars_thm (th_tpairs th) B" for v
  proof -
    have "v \<in> tvars_thm (th_tpairs thA) (th_prop thA) \<or> v \<in> tvars_thm (th_tpairs thAB) (th_prop thAB)"
      using that tps vB by (fastforce simp: tvars_thm_def)
    with w1 w2 show ?thesis by (auto simp: thm_wf_def)
  qed
  show ?thesis using dw(3) ib hs tp mm vn tn by (simp add: thm_wf_def wt_thm_def th mk_rep_def)
qed

end

definition implies_elim_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "implies_elim_thm thAB thA =
    (if sign_of thAB = sign_of thA then
      map_option (\<lambda>r. Abs_thm (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
          (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
          (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q))))))
        (resT (implies_elim (rep_of thAB) (rep_of thA)))
     else None)"

lemma thm_ok_implies_elim:
  fixes thAB thA :: "'u pure_thm"
  assumes ok: "okT (implies_elim (rep_of thAB) (rep_of thA)) r" and c: "sign_of thA = sign_of thAB"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
    (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
    (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q)))))"
    (is "thm_ok _ ?th")
proof (rule thm_okI)
  let ?c = "sign_of thAB"
  assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
  then interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by simp
  have w1: "thm_wf (th_maxidx (rep_of thAB)) (hyps_of thAB) (th_tpairs (rep_of thAB)) (th_prop (rep_of thAB))"
    using pure_thm_wf[of thAB] ps by simp
  have w2: "thm_wf (th_maxidx (rep_of thA)) (hyps_of thA) (th_tpairs (rep_of thA)) (th_prop (rep_of thA))"
    using pure_thm_wf[of thA] ps c by simp
  show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
      (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
    using thm_wf_implies_elim[OF ok w1 w2] by simp
  fix M :: "'u model" assume M: "is_model (th_sign ?th) M"
  interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
    "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
    by (rule is_modelD) (use M in simp)
  have v1: "valid (shyps_of thAB) (hyps_of thAB) (th_tpairs (rep_of thAB)) (th_prop (rep_of thAB))"
    using pure_thm_valid_in[of thAB M] M by simp
  have v2: "valid (shyps_of thA) (hyps_of thA) (th_tpairs (rep_of thA)) (th_prop (rep_of thA))"
    using pure_thm_valid_in[of thA M] M c by simp
  have "valid (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (th_tpairs r) (th_prop r)"
    by (rule implies_elim_valid[OF ok v1 v2]) (use w1 w2 in \<open>simp_all add: thm_wf_def wt_thm_def\<close>)
  then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
    by (simp add: valid_in_def)
next
  let ?c = "sign_of thAB"
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have pAB: "proofs_ok (rep_thm thAB)" by (rule pure_thm_proofs_ok) (use psig in simp)
  have pA: "proofs_ok (rep_thm thA)" by (rule pure_thm_proofs_ok) (use psig c in simp)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w1: "wtp (th_prop (rep_of thAB))" and w2: "wtp (th_prop (rep_of thA))"
    using pure_thm_wf[of thAB] pure_thm_wf[of thA] c ps by (simp_all add: thm_wf_def wt_thm_def)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pr assume "bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))) = returnW pr"
    then obtain p q where p: "proof_of thAB = returnW p" and q: "proof_of thA = returnW q" and pr: "pr = PAppp p q"
      by (auto simp: bindP_eq_returnP)
    have vp: "prf_valid (sg_ax ?c) (set (hyps_of thAB)) (th_tpairs (rep_of thAB)) p (th_prop (rep_of thAB))"
      "prf_idx (\<lambda>i. 0 \<le> i) p"
      using pAB p by (simp_all add: proofs_ok_def Let_def)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of thA)) (th_tpairs (rep_of thA)) q (th_prop (rep_of thA))"
      "prf_idx (\<lambda>i. 0 \<le> i) q"
      using pA q c by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of thAB) \<union> set (hyps_of thA)) (th_tpairs r) (PAppp p q) (th_prop r)"
      by (rule implies_elim_rule_proof_valid[OF ok vp(1) vq(1) w1 w2])
    then show "prf_valid (sg_ax ?c) (set (hyps_of thA @ hyps_of thAB)) (th_tpairs r) pr (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pr"
      using vp(2) vq(2) by (simp add: pr Un_commute)
  next
    fix z assume "bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q))) = return z"
    then obtain p q where p: "zproof_of thAB = return p" and q: "zproof_of thA = return q" and z: "z = ZAppp p q"
      by (auto simp: bindZ_eq_returnZ)
    have vp: "zvalid (sg_ax ?c) (set (hyps_of thAB)) (th_tpairs (rep_of thAB)) p (th_prop (rep_of thAB))" "zinv p"
      using pAB p by (simp_all add: proofs_ok_def Let_def)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of thA)) (th_tpairs (rep_of thA)) q (th_prop (rep_of thA))" "zinv q"
      using pA q c by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of thAB) \<union> set (hyps_of thA)) (th_tpairs r) (ZAppp p q) (th_prop r)"
      by (rule zimplies_elim_rule_proof_valid[OF ok vp(1) vq(1) w1 w2])
    then show "zvalid (sg_ax ?c) (set (hyps_of thA @ hyps_of thAB)) (th_tpairs r) z (th_prop r) \<and> zinv z"
      using vp(2) vq(2) by (simp add: z Un_commute)
  qed
qed

theorem implies_elim_thm:
  assumes "implies_elim_thm thAB thA = Some th"
  obtains r where "okT (implies_elim (rep_of thAB) (rep_of thA)) r" "sign_of thA = sign_of thAB"
    "rep_thm th = mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
      (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
      (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q))))"
proof -
  from assms obtain r where c: "sign_of thAB = sign_of thA" and ok: "okT (implies_elim (rep_of thAB) (rep_of thA)) r"
    and th: "th = Abs_thm (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
      (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
      (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q)))))"
    by (auto simp: implies_elim_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric]]) (use thm_ok_implies_elim[OF ok c[symmetric]] in \<open>simp add: th Abs_thm_inverse\<close>)
qed


subsection \<open>Auxiliary facts\<close>

context pure_sig
begin

lemma thm_wf_cong:
  "thm_wf m hs tps P \<Longrightarrow> wtp Q \<Longrightarrow> vars Q = vars P \<Longrightarrow> ttvars Q = ttvars P \<Longrightarrow> thm_wf m hs tps Q"
  by (simp add: thm_wf_def wt_thm_def ibelow_def vars_thm_def tvars_thm_def)

end

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
  then show ?thesis using map_insts_names(1)[OF mi nok] by (simp add: p)
qed

text \<open>
  The signature condition of the equality rules: \<open>Pure.eq\<close> is declared with its polymorphic type,
  and the equality axioms of \<open>Pure\<close> are axioms with their closures (as in every theory).
\<close>

definition sign_eq :: "sign \<Rightarrow> bool" where
  "sign_eq c \<longleftrightarrow> pure_sig.eq_ok (sg_consts c) \<and>
    (is_prf_sig c \<longrightarrow> prf_eq (sg_alg c) (sg_ar c) (sg_consts c) (sg_close c) (sg_tyargs c) (sg_ax c))"

fun eq_args :: "pterm \<Rightarrow> (ptyp \<times> pterm \<times> pterm) option" where
  "eq_args (Const c (Type a [T, U]) $ t $ u) = Some (T, t, u)"
| "eq_args _ = None"


subsection \<open>Symmetry\<close>

definition symmetric_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "symmetric_thm th =
    (if sign_eq (sign_of th) then
      map_option (\<lambda>r. Abs_thm (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
          (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
              Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig.ztargs (sg_consts (sign_of th))) T t u p
            | None \<Rightarrow> raise undefined))))
        (resT (symmetric (rep_of th)))
     else None)"

lemma thm_ok_symmetric:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (symmetric (rep_of th)) r" and se: "sign_eq (sign_of th)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
    (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
        Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig.ztargs (sg_consts (sign_of th))) T t u p
      | None \<Rightarrow> raise undefined)))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th"
  have eq: "pure_sig.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain e t u where P: "th_prop (rep_of th) = e $ t $ u" and d: "dest_eq_fun (th_prop (rep_of th)) \<noteq> None"
    and r: "r = mk_rep (th_maxidx (rep_of th)) (th_tpairs (rep_of th)) (e $ u $ t)"
    by (auto simp: symmetric_def returnW_def raiseW_def split: pterm.splits option.splits)
  then obtain T' where "dest_eq_fun (th_prop (rep_of th)) = Some (T', t, u)"
    by (cases "th_prop (rep_of th)" rule: dest_eq_fun.cases) (auto split: if_splits)
  then have d': "dest_eq_any (th_prop (rep_of th)) = Some (t, u)" by (rule dest_eq_any_dest_eq_fun)
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by simp
    have w: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    obtain T where P': "th_prop (rep_of th) = eq_const T $ t $ u" and c: "closed t" "closed u"
      and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T"
      using dest_eq_any_wtp[OF eq d'] w by (auto simp: thm_wf_def wt_thm_def)
    have wP: "wtp (eq_const T $ t $ u)" using w P' by (simp add: thm_wf_def wt_thm_def)
    have e: "e = eq_const T" using P P' by simp
    have "wtp (eq_const T $ u $ t)"
    proof (rule wtpI)
      show "closed (eq_const T $ u $ t)" using c by (simp add: closed_def)
      have "(\<lambda>_. propT) \<turnstile> eq_const T $ t $ u : propT" by (rule wtpD(2)[OF wP])
      then show "(\<lambda>_. propT) \<turnstile> eq_const T $ u $ t : propT" using ty by auto
    qed
    moreover have "vars (e $ u $ t) = vars (th_prop (rep_of th))" "ttvars (e $ u $ t) = ttvars (th_prop (rep_of th))"
      using P by auto
    ultimately have "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (e $ u $ t)"
      using thm_wf_cong[OF w] e by simp
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid_in[of th M] M by simp
    have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps by (simp add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule symmetric_valid[OF ok v eq w])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
      using se by (simp add: sign_eq_def)
    have pth: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have wf: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    then have w: "wtp (th_prop (rep_of th))" by (simp add: thm_wf_def wt_thm_def)
    obtain T where P': "th_prop (rep_of th) = eq_const T $ t $ u" using dest_eq_any_wtp[OF eq d' w] by blast
    have pt: "pnn t" "pnn u" using thm_wf_pnn(1)[OF wf] unfolding P' by simp_all
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pr assume "bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)) = returnW pr"
      then obtain p where p: "proof_of th = returnW p" and pr: "pr = symmetric_proof p"
        by (auto simp: bindP_eq_returnP)
      have vp: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) p (th_prop (rep_of th))"
        "prf_idx (\<lambda>i. 0 \<le> i) p"
        using pth p by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) (symmetric_proof p) (th_prop r)"
        by (rule symmetric_proof_valid[OF ok vp(1) w prf_valid_refl_ok[OF vp(1)]])
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) (symmetric_proof p)"
        using vp(2) by (auto simp: symmetric_proof_def equality_axm_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pr (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pr"
        by (simp add: pr)
    next
      fix z assume "bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
          Some (T, t, u) \<Rightarrow> zsymmetric_proof ztargs T t u p | None \<Rightarrow> raise undefined) = return z"
      then obtain p where p: "zproof_of th = return p" and z: "zsymmetric_proof ztargs T t u p = return z"
        using P' by (auto simp: bindZ_eq_returnZ propT_def)
      have vp: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) p (th_prop (rep_of th))" "zinv p"
        using pth p by (simp_all add: proofs_ok_def Let_def)
      have zc: "zconsts_ok p" using vp(2) by (simp add: zinv_def)
      note zs = zsymmetric_proof_valid[OF ok vp(1) w P' pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)] zc z]
      have "zinv z"
      proof (cases "zis_reflexive_proof p")
        case True
        with z have "z = p" by (simp add: zsymmetric_proof_def)
        with vp(2) show ?thesis by simp
      next
        case False
        with z obtain x y ax where x: "zterm_of ztargs t = return x" and y: "zterm_of ztargs u = return y"
          and ax: "zaxiom_proof STR ''symmetric'' [(tvar_a, ztyp_of T)] [(STR ''x'', x), (STR ''y'', y)] = return ax"
          and zz: "z = ZAppp ax p"
          by (auto simp: zsymmetric_proof_def bindZ_eq_returnZ)
        have "zinv ax"
          by (rule zinv_zaxiom_proof[OF ax])
            (use zterm_ok_zterm_of_pnn[OF x pt(1)] zterm_ok_zterm_of_pnn[OF y pt(2)] in \<open>auto simp: zeq_vars_def\<close>)
        with vp(2) show ?thesis by (simp add: zz)
      qed
      with zs(1) show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z" by simp
    qed
  qed
qed

theorem symmetric_thm:
  assumes "symmetric_thm th = Some th'"
  obtains r where "okT (symmetric (rep_of th)) r" "sign_eq (sign_of th)"
    "rep_thm th' = mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
      (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
          Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig.ztargs (sg_consts (sign_of th))) T t u p
        | None \<Rightarrow> raise undefined))"
proof -
  from assms obtain r where se: "sign_eq (sign_of th)" and ok: "okT (symmetric (rep_of th)) r"
    and th': "th' = Abs_thm (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
      (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
          Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig.ztargs (sg_consts (sign_of th))) T t u p
        | None \<Rightarrow> raise undefined)))"
    by (auto simp: symmetric_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok se]) (use thm_ok_symmetric[OF ok se] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed


subsection \<open>Transitivity\<close>

context pure_sig
begin

lemma thm_wf_union:
  assumes w1: "thm_wf m1 hs1 tps1 P1" and w2: "thm_wf m2 hs2 tps2 P2" and wQ: "wtp Q"
    and vQ: "vars Q \<subseteq> vars P1 \<union> vars P2" "ttvars Q \<subseteq> ttvars P1 \<union> ttvars P2"
    and tps: "set tps \<subseteq> set tps1 \<union> set tps2" and hs: "set hs = set hs1 \<union> set hs2"
  shows "thm_wf (max m1 m2) hs tps Q"
proof -
  let ?m = "max m1 m2"
  from w1 obtain ib1: "ibelow m1 P1" and h1: "\<forall>h\<in>set hs1. wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tp1: "\<forall>(t, u)\<in>set tps1. closed t \<and> closed u \<and> ibelow m1 t \<and> ibelow m1 u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and m1: "-1 \<le> m1" and vn1: "\<forall>v\<in>vars_thm tps1 P1. 0 \<le> snd (fst v)"
    and tn1: "\<forall>v\<in>tvars_thm tps1 P1. 0 \<le> snd (fst v)"
    unfolding thm_wf_def wt_thm_def by blast
  from w2 obtain ib2: "ibelow m2 P2" and h2: "\<forall>h\<in>set hs2. wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tp2: "\<forall>(t, u)\<in>set tps2. closed t \<and> closed u \<and> ibelow m2 t \<and> ibelow m2 u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and vn2: "\<forall>v\<in>vars_thm tps2 P2. 0 \<le> snd (fst v)"
    and tn2: "\<forall>v\<in>tvars_thm tps2 P2. 0 \<le> snd (fst v)"
    unfolding thm_wf_def wt_thm_def by blast
  have mx: "m1 \<le> ?m" "m2 \<le> ?m" by simp_all
  have ib: "ibelow ?m Q"
    unfolding ibelow_def
  proof (intro conjI ballI)
    fix v assume "v \<in> vars Q"
    with vQ(1) have "v \<in> vars P1 \<or> v \<in> vars P2" by blast
    then show "snd (fst v) \<le> ?m"
      using ib1 ib2 unfolding ibelow_def by (meson order_trans mx)
  next
    fix v assume "v \<in> ttvars Q"
    with vQ(2) have "v \<in> ttvars P1 \<or> v \<in> ttvars P2" by blast
    then show "snd (fst v) \<le> ?m"
      using ib1 ib2 unfolding ibelow_def by (meson order_trans mx)
  qed
  have h: "\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}" using h1 h2 hs by blast
  have tp: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> ibelow ?m t \<and> ibelow ?m u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  proof (intro ballI, clarify)
    fix t u assume "(t, u) \<in> set tps"
    with tps have "(t, u) \<in> set tps1 \<or> (t, u) \<in> set tps2" by blast
    then show "closed t \<and> closed u \<and> ibelow ?m t \<and> ibelow ?m u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    proof
      assume "(t, u) \<in> set tps1"
      with tp1 have "closed t \<and> closed u \<and> ibelow m1 t \<and> ibelow m1 u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
        by blast
      then show ?thesis using ibelow_mono[OF _ mx(1)] by blast
    next
      assume "(t, u) \<in> set tps2"
      with tp2 have "closed t \<and> closed u \<and> ibelow m2 t \<and> ibelow m2 u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
        by blast
      then show ?thesis using ibelow_mono[OF _ mx(2)] by blast
    qed
  qed
  have mm: "-1 \<le> ?m" using m1 by simp
  have sub: "vars_thm tps Q \<subseteq> vars_thm tps1 P1 \<union> vars_thm tps2 P2"
    using tps vQ(1) unfolding vars_thm_def by blast
  have tsub: "tvars_thm tps Q \<subseteq> tvars_thm tps1 P1 \<union> tvars_thm tps2 P2"
    using tps vQ(2) unfolding tvars_thm_def by blast
  have vn: "\<forall>v\<in>vars_thm tps Q. 0 \<le> snd (fst v)" using sub vn1 vn2 by blast
  have tn: "\<forall>v\<in>tvars_thm tps Q. 0 \<le> snd (fst v)" using tsub tn1 tn2 by blast
  show ?thesis unfolding thm_wf_def wt_thm_def using wQ ib h tp mm vn tn by blast
qed

end

definition transitive_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "transitive_thm th1 th2 =
    (if sign_of th1 = sign_of th2 \<and> sign_eq (sign_of th1) then
      map_option (\<lambda>r. Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
          (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
            case eq_args (th_prop (rep_of th1)) of
              Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
            | None \<Rightarrow> raiseW undefined)))
          (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
            case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
              (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
                ztransitive_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
            | _ \<Rightarrow> raise undefined)))))
        (resT (transitive (rep_of th1) (rep_of th2)))
     else None)"

lemma thm_ok_transitive:
  fixes th1 th2 :: "'u pure_thm"
  assumes ok: "okT (transitive (rep_of th1) (rep_of th2)) r" and c: "sign_of th2 = sign_of th1"
    and se: "sign_eq (sign_of th1)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
      case eq_args (th_prop (rep_of th1)) of
        Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
      | None \<Rightarrow> raiseW undefined)))
    (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
      case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
        (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
          ztransitive_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
      | _ \<Rightarrow> raise undefined))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain e x y T t1 u u' t2 where P1: "th_prop (rep_of th1) = e $ x $ y"
    and d1: "dest_eq (th_prop (rep_of th1)) = Some (T, t1, u)"
    and d2: "dest_eq_any (th_prop (rep_of th2)) = Some (u', t2)" and a: "aconv_term u u'"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) (e $ t1 $ t2)"
    by (auto simp: transitive_def returnW_def raiseW_def split: pterm.splits option.splits prod.splits if_splits)
  have d1': "dest_eq_any (th_prop (rep_of th1)) = Some (t1, u)" by (rule dest_eq_any_dest_eq[OF d1])
  have common: "\<exists>A. th_prop (rep_of th1) = eq_const A $ t1 $ u \<and> th_prop (rep_of th2) = eq_const A $ u' $ t2 \<and>
      e = eq_const A \<and> pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (eq_const A $ t1 $ t2)"
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
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by simp
    from common ps obtain A where P1': "th_prop (rep_of th1) = eq_const A $ t1 $ u"
      and P2': "th_prop (rep_of th2) = eq_const A $ u' $ t2" and e: "e = eq_const A"
      and wQ: "wtp (eq_const A $ t1 $ t2)" by auto
    have w1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_wf[of th1] ps by simp
    have w2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_wf[of th2] ps c by simp
    have "thm_wf (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2))) (hyps_of th1 @ hyps_of th2)
        (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) (eq_const A $ t1 $ t2)"
      by (rule thm_wf_union[OF w1 w2 wQ]) (use union_tpairs_set(1) P1' P2' in auto)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r e mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have v1: "valid (shyps_of th1) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_valid_in[of th1 M] M by simp
    have v2: "valid (shyps_of th2) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_valid_in[of th2 M] M c by simp
    have w: "wtp (th_prop (rep_of th1))" "wtp (th_prop (rep_of th2))"
      using pure_thm_wf[of th1] pure_thm_wf[of th2] ps c by (simp_all add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (th_tpairs r) (th_prop r)"
      by (rule transitive_valid[OF ok v1 v2 eq w])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
      using se by (simp add: sign_eq_def)
    have p1: "proofs_ok (rep_thm th1)" by (rule pure_thm_proofs_ok) (use psig in simp)
    have p2: "proofs_ok (rep_thm th2)" by (rule pure_thm_proofs_ok) (use psig c in simp)
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
        "prf_idx (\<lambda>i. 0 \<le> i) p"
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
        "prf_idx (\<lambda>i. 0 \<le> i) q"
        using p2 q c by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) (transitive_proof A u p q) (th_prop r)"
        unfolding H
        by (rule transitive_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2
          prf_valid_refl_ok[OF vp(1)] prf_valid_refl_ok[OF vq(1)] d1']) simp_all
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) (transitive_proof A u p q)"
        using vp(2) vq(2) pt(2) by (auto simp: transitive_proof_def equality_axm_def pnn_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pr (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pr"
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
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
        using p2 q c by (simp_all add: proofs_ok_def Let_def)
      have zv1: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
        and zv2: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
        using vp(1) vq(1) by (auto simp: zvalid_def intro: prf_valid_mono)
      note zs = ztransitive_proof_valid[OF ok zv1 zv2 w1 w2 P1' d2 pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)]
        pnn_noneg[OF pt2] _ _ z]
      have zc: "zconsts_ok p" "zconsts_ok q" using vp(2) vq(2) by (simp_all add: zinv_def)
      have "zinv z"
      proof (cases "zis_reflexive_proof p \<or> zis_reflexive_proof q")
        case True
        with z have "z = p \<or> z = q" by (auto simp: ztransitive_proof_def split: if_splits)
        with vp(2) vq(2) show ?thesis by auto
      next
        case False
        with z obtain x y w ax where x: "zterm_of ztargs t1 = return x" and y: "zterm_of ztargs u = return y"
          and w: "zterm_of ztargs t2 = return w"
          and ax: "zaxiom_proof STR ''transitive'' [(tvar_a, ztyp_of A)] [(STR ''x'', x), (STR ''y'', y), (STR ''z'', w)] = return ax"
          and zz: "z = ZAppp (ZAppp ax p) q"
          by (auto simp: ztransitive_proof_def bindZ_eq_returnZ)
        have "zinv ax"
          by (rule zinv_zaxiom_proof[OF ax])
            (use zterm_ok_zterm_of_pnn[OF x pt(1)] zterm_ok_zterm_of_pnn[OF y pt(2)] zterm_ok_zterm_of_pnn[OF w pt2]
              in \<open>auto simp: zeq_vars_def\<close>)
        with vp(2) vq(2) show ?thesis by (simp add: zz)
      qed
      with zs(1)[OF zc] show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z"
        by simp
    qed
  qed
qed

theorem transitive_thm:
  assumes "transitive_thm th1 th2 = Some th"
  obtains r where "okT (transitive (rep_of th1) (rep_of th2)) r" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
        case eq_args (th_prop (rep_of th1)) of
          Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
        | None \<Rightarrow> raiseW undefined)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
          (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
            ztransitive_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
        | _ \<Rightarrow> raise undefined)))"
proof -
  from assms obtain r where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (transitive (rep_of th1) (rep_of th2)) r"
    and th: "th = Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
        case eq_args (th_prop (rep_of th1)) of
          Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
        | None \<Rightarrow> raiseW undefined)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
          (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
            ztransitive_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
        | _ \<Rightarrow> raise undefined))))"
    by (auto simp: transitive_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_transitive[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse\<close>)
qed


subsection \<open>Equality of propositions\<close>

text \<open>The wrapper takes the arguments of the proof constructors from the first premise.\<close>

fun app2_args :: "pterm \<Rightarrow> (pterm \<times> pterm) option" where
  "app2_args (f $ A $ B) = Some (A, B)"
| "app2_args _ = None"

definition prf2 :: "(pterm \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf) \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> prf P" where
  "prf2 f th1 th2 = bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
    case app2_args (th_prop (rep_of th1)) of Some (A, B) \<Rightarrow> returnW (f A B p q) | None \<Rightarrow> raiseW undefined))"

definition zprf2 :: "(ztypargs \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow> zproof Z) \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> zproof Z" where
  "zprf2 f th1 th2 = bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
    case app2_args (th_prop (rep_of th1)) of
      Some (A, B) \<Rightarrow> f (pure_sig.ztargs (sg_consts (sign_of th1))) A B p q
    | None \<Rightarrow> raise undefined))"

lemma prf2_returnW:
  assumes "prf2 f th1 th2 = returnW pf" and "app2_args (th_prop (rep_of th1)) = Some (A, B)"
  obtains p q where "proof_of th1 = returnW p" "proof_of th2 = returnW q" "pf = f A B p q"
  using assms by (auto simp: prf2_def bindP_eq_returnP)

lemma zprf2_return:
  assumes "zprf2 f th1 th2 = return z" and "app2_args (th_prop (rep_of th1)) = Some (A, B)"
  obtains p q where "zproof_of th1 = return p" "zproof_of th2 = return q"
    "f (pure_sig.ztargs (sg_consts (sign_of th1))) A B p q = return z"
  using assms by (auto simp: zprf2_def bindZ_eq_returnZ)

definition equal_intr_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "equal_intr_thm th1 th2 =
    (if sign_of th1 = sign_of th2 \<and> sign_eq (sign_of th1) then
      map_option (\<lambda>r. Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
          (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2)))
        (resT (equal_intr (rep_of th1) (rep_of th2)))
     else None)"

lemma thm_ok_equal_intr:
  fixes th1 th2 :: "'u pure_thm"
  assumes ok: "okT (equal_intr (rep_of th1) (rep_of th2)) r" and c: "sign_of th2 = sign_of th1"
    and se: "sign_eq (sign_of th1)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain A B B' A' P where d1: "dest_imp (th_prop (rep_of th1)) = Some (A, B)"
    and mk: "ok (mk_equals (A, B)) P"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) P"
    by (auto simp: equal_intr_def returnW_def raiseW_def split: option.splits if_splits prod.splits)
  have common: "\<exists>A B. th_prop (rep_of th1) = implies $ A $ B \<and> th_prop r = eq_const propT $ A $ B \<and>
      pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (eq_const propT $ A $ B)"
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
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by simp
    from common ps obtain A B where P1': "th_prop (rep_of th1) = implies $ A $ B"
      and Q: "th_prop r = eq_const propT $ A $ B" and wQ: "wtp (eq_const propT $ A $ B)" by auto
    have w1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_wf[of th1] ps by simp
    have w2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_wf[of th2] ps c by simp
    have "thm_wf (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2))) (hyps_of th1 @ hyps_of th2)
        (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) (eq_const propT $ A $ B)"
      by (rule thm_wf_union[OF w1 w2 wQ]) (use union_tpairs_set(1) P1' in \<open>auto simp: propT_def implies_def\<close>)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using Q by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have v1: "valid (shyps_of th1) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_valid_in[of th1 M] M by simp
    have v2: "valid (shyps_of th2) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_valid_in[of th2 M] M c by simp
    have w: "wtp (th_prop (rep_of th1))" "wtp (th_prop (rep_of th2))"
      using pure_thm_wf[of th1] pure_thm_wf[of th2] ps c by (simp_all add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (th_tpairs r) (th_prop r)"
      by (rule equal_intr_valid[OF ok v1 v2 eq w])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
      using se by (simp add: sign_eq_def)
    have p1: "proofs_ok (rep_thm th1)" by (rule pure_thm_proofs_ok) (use psig in simp)
    have p2: "proofs_ok (rep_thm th2)" by (rule pure_thm_proofs_ok) (use psig c in simp)
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
        "prf_idx (\<lambda>i. 0 \<le> i) p"
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
        "prf_idx (\<lambda>i. 0 \<le> i) q"
        using p2 q c by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) (equal_intr_proof A B p q) (th_prop r)"
        unfolding H
        by (rule equal_intr_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2 P1']) simp_all
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) (equal_intr_proof A B p q)"
        using vp(2) vq(2) pt by (auto simp: equal_intr_proof_def equality_axm_def pnn_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pr (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pr"
        by (simp add: pr)
    next
      fix z assume "zprf2 zequal_intr_proof th1 th2 = return z"
      then obtain p q where p: "zproof_of th1 = return p" and q: "zproof_of th2 = return q"
        and z: "zequal_intr_proof ztargs A B p q = return z"
        using ea by (rule zprf2_return)
      have vp: "zvalid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))" "zinv p"
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
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
      have "zinv ax"
        by (rule zinv_zaxiom_proof[OF ax])
          (use zterm_ok_zterm_of_pnn[OF a pt(1)] zterm_ok_zterm_of_pnn[OF b pt(2)] in \<open>auto simp: zeq_vars_def\<close>)
      with vp(2) vq(2) have "zinv z" by (simp add: zz)
      with zs show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z"
        by simp
    qed
  qed
qed

theorem equal_intr_thm:
  assumes "equal_intr_thm th1 th2 = Some th"
  obtains r where "okT (equal_intr (rep_of th1) (rep_of th2)) r" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2)"
proof -
  from assms obtain r where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (equal_intr (rep_of th1) (rep_of th2)) r"
    and th: "th = Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2))"
    by (auto simp: equal_intr_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_equal_intr[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse\<close>)
qed

definition equal_elim_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "equal_elim_thm th1 th2 =
    (if sign_of th1 = sign_of th2 \<and> sign_eq (sign_of th1) then
      map_option (\<lambda>r. Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
          (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2)))
        (resT (equal_elim (rep_of th1) (rep_of th2)))
     else None)"

lemma thm_ok_equal_elim:
  fixes th1 th2 :: "'u pure_thm"
  assumes ok: "okT (equal_elim (rep_of th1) (rep_of th2)) r" and c: "sign_of th2 = sign_of th1"
    and se: "sign_eq (sign_of th1)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  from ok obtain A B where d: "dest_eq_any (th_prop (rep_of th1)) = Some (A, B)"
    and a: "aconv_term (th_prop (rep_of th2)) A"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) B"
    by (auto simp: equal_elim_def returnW_def raiseW_def split: option.splits if_splits)
  have common: "\<exists>A B. th_prop (rep_of th1) = eq_const propT $ A $ B \<and> th_prop r = B \<and>
      pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) B"
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
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by simp
    from common ps obtain A B where P1': "th_prop (rep_of th1) = eq_const propT $ A $ B"
      and Q: "th_prop r = B" and wQ: "wtp (B)" by auto
    have w1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_wf[of th1] ps by simp
    have w2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_wf[of th2] ps c by simp
    have "thm_wf (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2))) (hyps_of th1 @ hyps_of th2)
        (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) (B)"
      by (rule thm_wf_union[OF w1 w2 wQ]) (use union_tpairs_set(1) P1' in \<open>auto simp: propT_def implies_def\<close>)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using Q by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have v1: "valid (shyps_of th1) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_valid_in[of th1 M] M by simp
    have v2: "valid (shyps_of th2) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_valid_in[of th2 M] M c by simp
    have w: "wtp (th_prop (rep_of th1))" "wtp (th_prop (rep_of th2))"
      using pure_thm_wf[of th1] pure_thm_wf[of th2] ps c by (simp_all add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (th_tpairs r) (th_prop r)"
      by (rule equal_elim_valid[OF ok v1 v2 eq w])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
      using se by (simp add: sign_eq_def)
    have p1: "proofs_ok (rep_thm th1)" by (rule pure_thm_proofs_ok) (use psig in simp)
    have p2: "proofs_ok (rep_thm th2)" by (rule pure_thm_proofs_ok) (use psig c in simp)
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
        "prf_idx (\<lambda>i. 0 \<le> i) p"
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
        "prf_idx (\<lambda>i. 0 \<le> i) q"
        using p2 q c by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) (equal_elim_proof A B p q) (th_prop r)"
        unfolding H
        by (rule equal_elim_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2 P1']) simp_all
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) (equal_elim_proof A B p q)"
        using vp(2) vq(2) pt by (auto simp: equal_elim_proof_def equality_axm_def pnn_def)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pr (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pr"
        by (simp add: pr)
    next
      fix z assume "zprf2 zequal_elim_proof th1 th2 = return z"
      then obtain p q where p: "zproof_of th1 = return p" and q: "zproof_of th2 = return q"
        and z: "zequal_elim_proof ztargs A B p q = return z"
        using ea by (rule zprf2_return)
      have vp: "zvalid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))" "zinv p"
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
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
      have "zinv ax"
        by (rule zinv_zaxiom_proof[OF ax])
          (use zterm_ok_zterm_of_pnn[OF a pt(1)] zterm_ok_zterm_of_pnn[OF b pt(2)] in \<open>auto simp: zeq_vars_def\<close>)
      with vp(2) vq(2) have "zinv z" by (simp add: zz)
      with zs show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z"
        by simp
    qed
  qed
qed

theorem equal_elim_thm:
  assumes "equal_elim_thm th1 th2 = Some th"
  obtains r where "okT (equal_elim (rep_of th1) (rep_of th2)) r" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2)"
proof -
  from assms obtain r where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (equal_elim (rep_of th1) (rep_of th2)) r"
    and th: "th = Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2))"
    by (auto simp: equal_elim_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_equal_elim[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse\<close>)
qed


subsection \<open>Combination\<close>

lemma combination_res_ok:
  assumes "okT (combination_res th1 th2) (r, fT, U, f, g, t, u)"
  shows "okT (combination th1 th2) r" "okT (combination_data th1 th2) (fT, U, f, g, t, u)"
  using assms by (auto simp: combination_res_def combination_def okW_bindW)

lemma combination_data_okE:
  assumes "okT (combination_data th1 th2) (fT, U, f, g, t, u)"
  obtains T1 where "dest_eq_fun (th_prop th1) = Some (fT, f, g)" "dest_eq_fun (th_prop th2) = Some (T1, t, u)"
    "fT = T1 \<rightarrow>\<^sub>T U"
  using assms
  by (auto simp: combination_data_def returnW_def raiseW_def split: option.splits ptyp.splits list.splits if_splits)

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

end

definition combination_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "combination_thm th1 th2 =
    (if sign_of th1 = sign_of th2 \<and> sign_eq (sign_of th1) then
      map_option (\<lambda>(r, fT, U, f, g, t, u). Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2)
          (sign_of th1)
          (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
          (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
            zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) fT U f g t u p q)))))
        (resT (combination_res (rep_of th1) (rep_of th2)))
     else None)"

lemma thm_ok_combination:
  fixes th1 th2 :: "'u pure_thm"
  assumes res: "okT (combination_res (rep_of th1) (rep_of th2)) (r, fT, U, f, g, t, u)"
    and c: "sign_of th2 = sign_of th1" and se: "sign_eq (sign_of th1)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
    (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
      zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) fT U f g t u p q))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  note ok = combination_res_ok(1)[OF res] and cd = combination_res_ok(2)[OF res]
  obtain T1 where d1: "dest_eq_fun (th_prop (rep_of th1)) = Some (fT, f, g)"
    and d2: "dest_eq_fun (th_prop (rep_of th2)) = Some (T1, t, u)" and fT: "fT = T1 \<rightarrow>\<^sub>T U"
    by (rule combination_data_okE[OF cd])
  from ok obtain fT' U' f' g' t' u' P where cd': "okT (combination_data (rep_of th1) (rep_of th2)) (fT', U', f', g', t', u')"
    and mk: "ok (mk_equals (f' $ t', g' $ u')) P"
    and r: "r = mk_rep (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2)))
      (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) P"
    by (auto simp: combination_def)
  have same: "fT' = fT" "U' = U" "f' = f" "g' = g" "t' = t" "u' = u" using cd cd' by auto
  have common: "th_prop (rep_of th1) = eq_const fT $ f $ g \<and> th_prop (rep_of th2) = eq_const T1 $ t $ u \<and>
      th_prop r = eq_const U $ (f $ t) $ (g $ u) \<and>
      pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (eq_const U $ (f $ t) $ (g $ u))"
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
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by simp
    from common ps have P1': "th_prop (rep_of th1) = eq_const fT $ f $ g"
      and P2': "th_prop (rep_of th2) = eq_const T1 $ t $ u"
      and Q: "th_prop r = eq_const U $ (f $ t) $ (g $ u)" and wQ: "wtp (eq_const U $ (f $ t) $ (g $ u))" by auto
    have w1: "thm_wf (th_maxidx (rep_of th1)) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_wf[of th1] ps by simp
    have w2: "thm_wf (th_maxidx (rep_of th2)) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_wf[of th2] ps c by simp
    have "thm_wf (max (th_maxidx (rep_of th1)) (th_maxidx (rep_of th2))) (hyps_of th1 @ hyps_of th2)
        (union_tpairs (th_tpairs (rep_of th1)) (th_tpairs (rep_of th2))) (eq_const U $ (f $ t) $ (g $ u))"
      by (rule thm_wf_union[OF w1 w2 wQ]) (use union_tpairs_set(1) P1' P2' fT in \<open>auto simp: propT_def\<close>)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using Q by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have v1: "valid (shyps_of th1) (hyps_of th1) (th_tpairs (rep_of th1)) (th_prop (rep_of th1))"
      using pure_thm_valid_in[of th1 M] M by simp
    have v2: "valid (shyps_of th2) (hyps_of th2) (th_tpairs (rep_of th2)) (th_prop (rep_of th2))"
      using pure_thm_valid_in[of th2 M] M c by simp
    have w: "wtp (th_prop (rep_of th1))" "wtp (th_prop (rep_of th2))"
      using pure_thm_wf[of th1] pure_thm_wf[of th2] ps c by (simp_all add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (th_tpairs r) (th_prop r)"
      by (rule combination_valid[OF ok v1 v2 eq w])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
      using se by (simp add: sign_eq_def)
    have p1: "proofs_ok (rep_thm th1)" by (rule pure_thm_proofs_ok) (use psig in simp)
    have p2: "proofs_ok (rep_thm th2)" by (rule pure_thm_proofs_ok) (use psig c in simp)
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
    have H: "set (hyps_of th1 @ hyps_of th2) = set (hyps_of th1) \<union> set (hyps_of th2)" by simp
    show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
    proof (rule conjI; intro allI impI)
      fix pf assume "bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)) = returnW pf"
      then obtain p q where p: "proof_of th1 = returnW p" and q: "proof_of th2 = returnW q"
        and cp: "combination_proof f g t u p q = returnW pf"
        by (auto simp: bindP_eq_returnP)
      have vp: "prf_valid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
        "prf_idx (\<lambda>i. 0 \<le> i) p"
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "prf_valid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
        "prf_idx (\<lambda>i. 0 \<le> i) q"
        using p2 q c by (simp_all add: proofs_ok_def Let_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pf (th_prop r)"
        unfolding H by (rule combination_proof_valid[OF ok prf_valid_mono[OF vp(1)] prf_valid_mono[OF vq(1)] w1 w2 cd cp])
          simp_all
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
        by (rule prf_idx_combination_proof[OF cp vp(2) vq(2)]) (use pt pt2 in \<open>auto simp: pnn_def\<close>)
      ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) pf (th_prop r) \<and>
          prf_idx (\<lambda>i. 0 \<le> i) pf"
        by simp
    next
      fix z assume "bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
          zcombination_proof ztargs fT U f g t u p q)) = return z"
      then obtain p q where p: "zproof_of th1 = return p" and q: "zproof_of th2 = return q"
        and z: "zcombination_proof ztargs fT U f g t u p q = return z"
        by (auto simp: bindZ_eq_returnZ)
      have vp: "zvalid (sg_ax ?c) (set (hyps_of th1)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))" "zinv p"
        using p1 p by (simp_all add: proofs_ok_def Let_def)
      have vq: "zvalid (sg_ax ?c) (set (hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))" "zinv q"
        using p2 q c by (simp_all add: proofs_ok_def Let_def)
      have zv1: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th1)) p (th_prop (rep_of th1))"
        and zv2: "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs (rep_of th2)) q (th_prop (rep_of th2))"
        using vp(1) vq(1) by (auto simp: zvalid_def intro: prf_valid_mono)
      have zc: "zconsts_ok p" "zconsts_ok q" using vp(2) vq(2) by (simp_all add: zinv_def)
      note zs = zcombination_proof_valid[OF ok zv1 zv2 w1 w2 cd pnn_noneg[OF pt(1)] pnn_noneg[OF pt(2)]
        pnn_noneg[OF pt2(1)] pnn_noneg[OF pt2(2)] zc z]
      from z obtain f' g' x y ax where f': "zterm_of ztargs f = return f'" and g': "zterm_of ztargs g = return g'"
        and x: "zterm_of ztargs t = return x" and y: "zterm_of ztargs u = return y"
        and ax: "zaxiom_proof STR ''combination'' [(tvar_a, ztyp_of fT), (tvar_b, ztyp_of U)]
          [(STR ''f'', f'), (STR ''g'', g'), (STR ''x'', x), (STR ''y'', y)] = return ax"
        and zz: "z = ZAppp (ZAppp ax p) q"
        by (auto simp: zcombination_proof_def bindZ_eq_returnZ)
      have "zinv ax"
        by (rule zinv_zaxiom_proof[OF ax])
          (use zterm_ok_zterm_of_pnn[OF f' pt(1)] zterm_ok_zterm_of_pnn[OF g' pt(2)]
            zterm_ok_zterm_of_pnn[OF x pt2(1)] zterm_ok_zterm_of_pnn[OF y pt2(2)] in \<open>auto simp: zeq_vars_def\<close>)
      with vp(2) vq(2) have "zinv z" by (simp add: zz)
      with zs show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z"
        by simp
    qed
  qed
qed

theorem combination_thm:
  assumes "combination_thm th1 th2 = Some th"
  obtains r fT U f g t u where "okT (combination_res (rep_of th1) (rep_of th2)) (r, fT, U, f, g, t, u)" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) fT U f g t u p q)))"
proof -
  from assms obtain r fT U f g t u where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (combination_res (rep_of th1) (rep_of th2)) (r, fT, U, f, g, t, u)"
    and th: "th = Abs_thm (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) fT U f g t u p q))))"
    by (auto simp: combination_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_combination[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse\<close>)
qed

end
