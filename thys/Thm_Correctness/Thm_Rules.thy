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
    th_shyps = Sh, th_hyps = hs, th_sign = c, th_proof = p, th_zproof = z, th_constraints = {}\<rparr>"

lemma mk_thm_sel [simp]:
  "th_maxidx (mk_thm r Sh hs c p z) = th_maxidx r" "th_tpairs (mk_thm r Sh hs c p z) = th_tpairs r"
  "th_prop (mk_thm r Sh hs c p z) = th_prop r" "th_shyps (mk_thm r Sh hs c p z) = Sh"
  "th_hyps (mk_thm r Sh hs c p z) = hs" "th_sign (mk_thm r Sh hs c p z) = c"
  "th_proof (mk_thm r Sh hs c p z) = p" "th_zproof (mk_thm r Sh hs c p z) = z"
  "th_constraints (mk_thm r Sh hs c p z) = {}"
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
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of thA \<union> cons_of thAB) (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
          (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
          (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q)))))))
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

theorem implies_elim_thm:
  assumes "implies_elim_thm thAB thA = Some th"
  obtains r where "okT (implies_elim (rep_of thAB) (rep_of thA)) r" "sign_of thA = sign_of thAB"
    "rep_thm th = with_cons (cons_of thA \<union> cons_of thAB) (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
      (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
      (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q)))))"
proof -
  from assms obtain r where c: "sign_of thAB = sign_of thA" and ok: "okT (implies_elim (rep_of thAB) (rep_of thA)) r"
    and th: "th = Abs_thm (with_cons (cons_of thA \<union> cons_of thAB) (mk_thm r (shyps_of thAB \<union> shyps_of thA) (hyps_of thA @ hyps_of thAB) (sign_of thAB)
      (bindW (proof_of thAB) (\<lambda>p. bindW (proof_of thA) (\<lambda>q. returnW (PAppp p q))))
      (bindM (zproof_of thAB) (\<lambda>p. bindM (zproof_of thA) (\<lambda>q. return (ZAppp p q))))))"
    by (auto simp: implies_elim_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric]]) (use thm_ok_implies_elim[OF ok c[symmetric]] in \<open>simp add: th Abs_thm_inverse c\<close>)
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

lemma zaxiom_proof_ok:
  assumes z: "zaxiom_proof a Ts ts = return p" and a: "a \<in> fst ` set zeq_vars"
    and xs: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>t. map_of ts x = Some t \<and> zterm_ok t \<and> \<not> zloose t 0"
  shows "zinv p \<and> znolb 0 p \<and> zhyps p = {}"
  using zinv_zaxiom_proof[OF z a] zaxiom_proof_closed[OF z a] xs by blast

text \<open>
  The signature condition of the equality rules: \<open>Pure.eq\<close> is declared with its polymorphic type,
  the type \<open>prop\<close> has no arguments, and the equality axioms of \<open>Pure\<close> are axioms with their closures (as in every theory).
\<close>

definition sign_eq :: "sign \<Rightarrow> bool" where
  "sign_eq c \<longleftrightarrow> pure_sig.eq_ok (sg_consts c) \<and> sg_ar c STR ''prop'' = 0 \<and>
    (is_prf_sig c \<longrightarrow> prf_eq (sg_alg c) (sg_ar c) (sg_consts c) (sg_close c) (sg_tyargs c) (sg_ax c))"

fun eq_args :: "pterm \<Rightarrow> (ptyp \<times> pterm \<times> pterm) option" where
  "eq_args (Const c (Type a [T, U]) $ t $ u) = Some (T, t, u)"
| "eq_args _ = None"


subsection \<open>Symmetry\<close>

definition symmetric_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "symmetric_thm th =
    (if sign_eq (sign_of th) then
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
          (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
              Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig.ztargs (sg_consts (sign_of th))) T t u p
            | None \<Rightarrow> raise undefined)))))
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
              zloose_zterm_of[OF x] zloose_zterm_of[OF y] cl in \<open>auto simp: zeq_vars_def\<close>)
        with vp(2-4) show ?thesis by (auto simp: zz zhyps_ok_def)
      qed
      with zs(1) show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and>
          znolb 0 z \<and> zhyps_ok z" by simp
    qed
  qed
qed

theorem symmetric_thm:
  assumes "symmetric_thm th = Some th'"
  obtains r where "okT (symmetric (rep_of th)) r" "sign_eq (sign_of th)"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
      (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
          Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig.ztargs (sg_consts (sign_of th))) T t u p
        | None \<Rightarrow> raise undefined)))"
proof -
  from assms obtain r where se: "sign_eq (sign_of th)" and ok: "okT (symmetric (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (symmetric_proof p)))
      (bindM (zproof_of th) (\<lambda>p. case eq_args (th_prop (rep_of th)) of
          Some (T, t, u) \<Rightarrow> zsymmetric_proof (pure_sig.ztargs (sg_consts (sign_of th))) T t u p
        | None \<Rightarrow> raise undefined))))"
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
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
          (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
            case eq_args (th_prop (rep_of th1)) of
              Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
            | None \<Rightarrow> raiseW undefined)))
          (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
            case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
              (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
                ztransitive_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
            | _ \<Rightarrow> raise undefined))))))
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
              zloose_zterm_of[OF x] zloose_zterm_of[OF y] zloose_zterm_of[OF w] cl in \<open>auto simp: zeq_vars_def\<close>)
        with vp(2-4) vq(2-4) show ?thesis by (auto simp: zz zhyps_ok_def)
      qed
      with zs(1)[OF zc] show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and>
          zinv z \<and> znolb 0 z \<and> zhyps_ok z"
        by simp
    qed
  qed
qed

theorem transitive_thm:
  assumes "transitive_thm th1 th2 = Some th"
  obtains r where "okT (transitive (rep_of th1) (rep_of th2)) r" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
        case eq_args (th_prop (rep_of th1)) of
          Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
        | None \<Rightarrow> raiseW undefined)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
          (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
            ztransitive_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
        | _ \<Rightarrow> raise undefined))))"
proof -
  from assms obtain r where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (transitive (rep_of th1) (rep_of th2)) r"
    and th: "th = Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q.
        case eq_args (th_prop (rep_of th1)) of
          Some (T, t1, u) \<Rightarrow> returnW (transitive_proof T u p q)
        | None \<Rightarrow> raiseW undefined)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        case (eq_args (th_prop (rep_of th1)), eq_args (th_prop (rep_of th2))) of
          (Some (T, t1, u), Some (_, _, t2)) \<Rightarrow>
            ztransitive_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T t1 u t2 p q
        | _ \<Rightarrow> raise undefined)))))"
    by (auto simp: transitive_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_transitive[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse c\<close>)
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
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
          (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2))))
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
qed

theorem equal_intr_thm:
  assumes "equal_intr_thm th1 th2 = Some th"
  obtains r where "okT (equal_intr (rep_of th1) (rep_of th2)) r" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2))"
proof -
  from assms obtain r where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (equal_intr (rep_of th1) (rep_of th2)) r"
    and th: "th = Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_intr_proof th1 th2) (zprf2 zequal_intr_proof th1 th2)))"
    by (auto simp: equal_intr_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_equal_intr[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse c\<close>)
qed

definition equal_elim_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "equal_elim_thm th1 th2 =
    (if sign_of th1 = sign_of th2 \<and> sign_eq (sign_of th1) then
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
          (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2))))
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
qed

theorem equal_elim_thm:
  assumes "equal_elim_thm th1 th2 = Some th"
  obtains r where "okT (equal_elim (rep_of th1) (rep_of th2)) r" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2))"
proof -
  from assms obtain r where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (equal_elim (rep_of th1) (rep_of th2)) r"
    and th: "th = Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (prf2 equal_elim_proof th1 th2) (zprf2 zequal_elim_proof th1 th2)))"
    by (auto simp: equal_elim_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_equal_elim[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse c\<close>)
qed


subsection \<open>Combination\<close>

lemma combination_res_ok:
  assumes "okT (combination_res th1 th2) (r, T1, U, f, g, t, u)"
  shows "okT (combination th1 th2) r" "okT (combination_data th1 th2) (T1, U, f, g, t, u)"
  using assms by (auto simp: combination_res_def combination_def okW_bindW)

lemma combination_data_okE:
  assumes "okT (combination_data th1 th2) (T1, U, f, g, t, u)"
  shows "dest_eq_fun (th_prop th1) = Some (T1 \<rightarrow>\<^sub>T U, f, g)" "dest_eq_fun (th_prop th2) = Some (T1, t, u)"
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

definition combination_thm :: "'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "combination_thm th1 th2 =
    (if sign_of th1 = sign_of th2 \<and> sign_eq (sign_of th1) then
      map_option (\<lambda>(r, T1, U, f, g, t, u). Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2)
          (sign_of th1)
          (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
          (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
            zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T1 U f g t u p q))))))
        (resT (combination_res (rep_of th1) (rep_of th2)))
     else None)"

lemma thm_ok_combination:
  fixes th1 th2 :: "'u pure_thm"
  assumes res: "okT (combination_res (rep_of th1) (rep_of th2)) (r, T1, U, f, g, t, u)"
    and c: "sign_of th2 = sign_of th1" and se: "sign_eq (sign_of th1)"
  shows "thm_ok TYPE('u) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
    (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
    (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
      zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T1 U f g t u p q))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th1"
  have eq: "pure_sig.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
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
            in \<open>auto simp: zeq_vars_def\<close>)
      with vp(2-4) vq(2-4) have "zinv z \<and> znolb 0 z \<and> zhyps_ok z" by (auto simp: zz zhyps_ok_def)
      with zs show "zvalid (sg_ax ?c) (set (hyps_of th1 @ hyps_of th2)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and>
          znolb 0 z \<and> zhyps_ok z"
        by simp
    qed
  qed
qed

theorem combination_thm:
  assumes "combination_thm th1 th2 = Some th"
  obtains r T1 U f g t u where "okT (combination_res (rep_of th1) (rep_of th2)) (r, T1, U, f, g, t, u)" "sign_of th2 = sign_of th1" "sign_eq (sign_of th1)"
    "rep_thm th = with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T1 U f g t u p q))))"
proof -
  from assms obtain r T1 U f g t u where c: "sign_of th1 = sign_of th2" and se: "sign_eq (sign_of th1)"
    and ok: "okT (combination_res (rep_of th1) (rep_of th2)) (r, T1, U, f, g, t, u)"
    and th: "th = Abs_thm (with_cons (cons_of th1 \<union> cons_of th2) (mk_thm r (shyps_of th1 \<union> shyps_of th2) (hyps_of th1 @ hyps_of th2) (sign_of th1)
      (bindW (proof_of th1) (\<lambda>p. bindW (proof_of th2) (\<lambda>q. combination_proof f g t u p q)))
      (bindM (zproof_of th1) (\<lambda>p. bindM (zproof_of th2) (\<lambda>q.
        zcombination_proof (pure_sig.ztargs (sg_consts (sign_of th1))) T1 U f g t u p q)))))"
    by (auto simp: combination_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c[symmetric] se]) (use thm_ok_combination[OF ok c[symmetric] se] in \<open>simp add: th Abs_thm_inverse c\<close>)
qed


subsection \<open>Maximal indices\<close>

lemma fold_infl: "(\<And>x j. x \<in> set xs \<Longrightarrow> (j :: integer) \<le> f x j) \<Longrightarrow> i \<le> fold f xs i"
proof (induction xs arbitrary: i)
  case (Cons a xs)
  have "i \<le> f a i" by (rule Cons.prems) simp
  also have "f a i \<le> fold f xs (f a i)" by (rule Cons.IH) (use Cons.prems in simp)
  finally show ?case by simp
qed simp

lemma fold_mem_ge:
  assumes "\<And>x j. x \<in> set xs \<Longrightarrow> (j :: integer) \<le> f x j" and "x \<in> set xs" and "\<And>j. c \<le> f x j"
  shows "c \<le> fold f xs i"
  using assms
proof (induction xs arbitrary: i)
  case (Cons a xs)
  show ?case
  proof (cases "x = a")
    case True
    have "c \<le> f a i" using Cons.prems(3) True by simp
    also have "f a i \<le> fold f xs (f a i)" by (rule fold_infl) (use Cons.prems(1) in simp)
    finally show ?thesis by simp
  next
    case False
    then have "c \<le> fold f xs (f a i)" by (intro Cons.IH) (use Cons.prems in auto)
    then show ?thesis by simp
  qed
qed simp

lemma maxidx_typ_ge: "i \<le> maxidx_typ T i"
  by (induction T i rule: maxidx_typ.induct) (auto intro: fold_infl)

lemma maxidx_typ_tvars: "v \<in> tvars T \<Longrightarrow> snd (fst v) \<le> maxidx_typ T i"
proof (induction T i rule: maxidx_typ.induct)
  case (2 a Ts i)
  then obtain U where U: "U \<in> set Ts" "v \<in> tvars U" by auto
  show ?case unfolding maxidx_typ.simps by (rule fold_mem_ge[OF maxidx_typ_ge U(1)]) (rule "2.IH"[OF U])
qed auto

lemma maxidx_term_ge: "i \<le> maxidx_term t i"
proof (induction t i rule: maxidx_term.induct)
  case (1 uu j T i)
  have "i \<le> max i j" by simp
  also have "max i j \<le> maxidx_typ T (max i j)" by (rule maxidx_typ_ge)
  finally show ?case by simp
next
  case (5 uv T t i)
  show ?case unfolding maxidx_term.simps by (rule order_trans[OF maxidx_typ_ge "5.IH"])
next
  case (6 t u i)
  show ?case unfolding maxidx_term.simps by (rule order_trans[OF "6.IH"(1) "6.IH"(2)])
qed (simp_all add: maxidx_typ_ge)

lemma maxidx_term_vars: "v \<in> vars t \<Longrightarrow> snd (fst v) \<le> maxidx_term t i"
proof (induction t i rule: maxidx_term.induct)
  case (1 uu j T i)
  then have "snd (fst v) = j" by auto
  moreover have "j \<le> max i j" by simp
  moreover have "max i j \<le> maxidx_typ T (max i j)" by (rule maxidx_typ_ge)
  ultimately show ?case by simp
next
  case (6 t u i)
  show ?case
  proof (cases "v \<in> vars t")
    case True
    show ?thesis unfolding maxidx_term.simps by (rule order_trans[OF "6.IH"(1)[OF True] maxidx_term_ge])
  next
    case False
    with "6.prems" have "v \<in> vars u" by simp
    then show ?thesis unfolding maxidx_term.simps by (rule "6.IH"(2))
  qed
qed simp_all

lemma maxidx_term_ttvars: "v \<in> ttvars t \<Longrightarrow> snd (fst v) \<le> maxidx_term t i"
proof (induction t i rule: maxidx_term.induct)
  case (5 uv T t i)
  show ?case
  proof (cases "v \<in> tvars T")
    case True
    show ?thesis unfolding maxidx_term.simps by (rule order_trans[OF maxidx_typ_tvars[OF True] maxidx_term_ge])
  next
    case False
    with "5.prems" have "v \<in> ttvars t" by simp
    then show ?thesis unfolding maxidx_term.simps by (rule "5.IH")
  qed
next
  case (6 t u i)
  show ?case
  proof (cases "v \<in> ttvars t")
    case True
    show ?thesis unfolding maxidx_term.simps by (rule order_trans[OF "6.IH"(1)[OF True] maxidx_term_ge])
  next
    case False
    with "6.prems" have "v \<in> ttvars u" by simp
    then show ?thesis unfolding maxidx_term.simps by (rule "6.IH"(2))
  qed
qed (auto intro: maxidx_typ_tvars)

context pure_sig
begin

lemma maxidx_of_term_ibelow: "ibelow (maxidx_of_term t) t"
  by (auto simp: ibelow_def maxidx_of_term_def intro: maxidx_term_vars maxidx_term_ttvars)

end


subsection \<open>Auxiliary facts on terms\<close>

lemma subst_not_loose_vars: "\<not> loose_bvar1 s k \<Longrightarrow> vars (s[u/k]) \<subseteq> vars s"
proof (induction s arbitrary: k u)
  case (App s1 s2)
  have "vars (s1[u/k]) \<subseteq> vars s1" "vars (s2[u/k]) \<subseteq> vars s2"
    by (rule App.IH(1), use App.prems in simp, rule App.IH(2), use App.prems in simp)
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma subst_not_loose_typs: "\<not> loose_bvar1 s k \<Longrightarrow> typs (s[u/k]) \<subseteq> typs s"
proof (induction s arbitrary: k u)
  case (App s1 s2)
  have "typs (s1[u/k]) \<subseteq> typs s1" "typs (s2[u/k]) \<subseteq> typs s2"
    by (rule App.IH(1), use App.prems in simp, rule App.IH(2), use App.prems in simp)
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma eta_vars_typs: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> vars t \<subseteq> vars s \<and> typs t \<subseteq> typs s"
proof (induction rule: eta.induct)
  case (eta s a T u)
  then show ?case using subst_not_loose_vars[OF eta] subst_not_loose_typs[OF eta] by auto
qed auto

lemma eta_reds_vars_typs: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> vars t \<subseteq> vars s \<and> typs t \<subseteq> typs s"
  by (induction rule: rtranclp_induct) (use eta_vars_typs in blast)+

lemma ttvars_mono: "typs t \<subseteq> typs s \<Longrightarrow> ttvars t \<subseteq> ttvars s"
  by (auto simp: ttvars_def)

context pure_sig
begin

lemma typing_tvars:
  "e \<turnstile> t : T \<Longrightarrow> (\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 t i \<longrightarrow> tvars (e i) \<subseteq> X) \<Longrightarrow> ttvars t \<subseteq> X \<Longrightarrow> tvars T \<subseteq> X"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  have "\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 t i \<longrightarrow> tvars ((e\<langle>0:T\<rangle>) i) \<subseteq> X"
  proof (intro allI impI)
    fix i assume i: "0 \<le> i" "loose_bvar1 t i"
    show "tvars ((e\<langle>0:T\<rangle>) i) \<subseteq> X"
    proof (cases "i = 0")
      case False
      with i have "0 \<le> i - 1" "loose_bvar1 (Abs a T t) (i - 1)" by (simp_all add: integer_arith)
      with Abs.prems(1) False i(1) show ?thesis by (simp add: integer_arith)
    qed (use Abs.prems(2) in simp)
  qed
  with Abs show ?case by simp
next
  case (App e s T U t)
  then show ?case by auto
qed auto

lemma typing_tvars_closed: "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> tvars T \<subseteq> ttvars t"
  by (erule typing_tvars) (simp_all add: closed_iff_loose_bvar1)

end


subsection \<open>Certified terms\<close>

text \<open>
  A certified term (\<open>Thm.cterm\<close>) carries its certificate, the term, its type, its maximal index
  and its sorts. The term is closed and has the type; its schematic variables and type
  variables have non-negative indices (\<open>Sign.certify_term\<close> rejects others) bounded by the
  maximal index.
\<close>

record cterm_data =
  cd_rep :: cterm_rep
  cd_sorts :: "psort set"
  cd_sign :: sign

context pure_sig
begin

definition cterm_wf :: "cterm_rep \<Rightarrow> bool" where
  "cterm_wf ct \<longleftrightarrow> closed (ct_t ct) \<and> (\<forall>e. e \<turnstile> ct_t ct : ct_T ct) \<and> ibelow (ct_maxidx ct) (ct_t ct) \<and>
    -1 \<le> ct_maxidx ct \<and> (\<forall>v\<in>vars (ct_t ct). 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>ttvars (ct_t ct). 0 \<le> snd (fst v))"

end

definition cterm_ok :: "cterm_data \<Rightarrow> bool" where
  "cterm_ok c \<longleftrightarrow> (pure_sig (sg_alg (cd_sign c)) (sg_ar (cd_sign c)) \<longrightarrow>
    pure_sig.cterm_wf (sg_alg (cd_sign c)) (sg_ar (cd_sign c)) (sg_consts (cd_sign c)) (cd_rep c))"

definition cterm0 :: cterm_data where
  "cterm0 = \<lparr>cd_rep = CTerm (Var (STR ''A'', 0) propT) propT 0, cd_sorts = {}, cd_sign = sign0\<rparr>"

lemma cterm_ok_cterm0: "cterm_ok cterm0"
proof -
  let ?alg = "sg_alg sign0" and ?ar = "sg_ar sign0" and ?ct = "sg_consts sign0"
  have "pure_sig.cterm_wf ?alg ?ar ?ct (CTerm (Var (STR ''A'', 0) propT) propT 0)" if ps: "pure_sig ?alg ?ar"
  proof -
    interpret pure_sig ?alg ?ar ?ct by (rule ps)
    have c: "cert_typ ?alg ?ar propT" by (simp add: cert_typ_def propT_def tarity_def sign0_def)
    then show ?thesis by (auto simp: cterm_wf_def closed_def ibelow_def propT_def)
  qed
  then show ?thesis by (simp add: cterm_ok_def cterm0_def)
qed

typedef (overloaded) pure_cterm = "{c. cterm_ok c}"
  morphisms rep_cterm Abs_cterm
  using cterm_ok_cterm0 by blast

abbreviation crep_of :: "pure_cterm \<Rightarrow> cterm_rep" where
  "crep_of ct \<equiv> cd_rep (rep_cterm ct)"

abbreviation csign_of :: "pure_cterm \<Rightarrow> sign" where
  "csign_of ct \<equiv> cd_sign (rep_cterm ct)"

abbreviation csorts_of :: "pure_cterm \<Rightarrow> psort set" where
  "csorts_of ct \<equiv> cd_sorts (rep_cterm ct)"

lemma pure_cterm_wf:
  "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) \<Longrightarrow>
    pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
  using rep_cterm[of ct] by (simp add: cterm_ok_def)


subsection \<open>Assumption\<close>

lemma assume_rule_ok:
  assumes "okT (assume_rule ct) r"
  shows "ct_T ct = propT" "r = mk_rep (-1) [] (ct_t ct)"
    "ct_maxidx ct = -1 \<or> ct_maxidx ct < -1 \<or> maxidx_of_term (ct_t ct) \<le> -1"
  using assms by (auto simp: assume_rule_def adjust_maxidx_cterm_def Let_def returnW_def raiseW_def max_def
    split: if_splits)

context pure_sig
begin

lemma cterm_wf_novars:
  assumes wf: "cterm_wf ct" and m: "ct_maxidx ct = -1 \<or> ct_maxidx ct < -1 \<or> maxidx_of_term (ct_t ct) \<le> -1"
  shows "vars (ct_t ct) = {}" "ttvars (ct_t ct) = {}"
proof -
  have ib: "ibelow (-1) (ct_t ct)"
  proof -
    consider "ct_maxidx ct = -1" | "ct_maxidx ct < -1" | "maxidx_of_term (ct_t ct) \<le> -1" using m by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using wf by (simp add: cterm_wf_def)
    next
      case 2
      then show ?thesis using wf by (simp add: cterm_wf_def integer_arith)
    next
      case 3
      then show ?thesis by (rule ibelow_mono[OF maxidx_of_term_ibelow])
    qed
  qed
  have nn: "\<forall>v\<in>vars (ct_t ct). 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars (ct_t ct). 0 \<le> snd (fst v)"
    using wf by (simp_all add: cterm_wf_def)
  show "vars (ct_t ct) = {}" "ttvars (ct_t ct) = {}"
    using ib nn unfolding ibelow_def by (fastforce simp: integer_arith)+
qed

end

definition assume_thm :: "pure_cterm \<Rightarrow> 'u pure_thm option" where
  "assume_thm ct = map_option (\<lambda>r. Abs_thm (mk_thm r (csorts_of ct) [ct_t (crep_of ct)] (csign_of ct)
      (returnW (Hyp (ct_t (crep_of ct)))) (zassume_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct)))))
    (resT (assume_rule (crep_of ct)))"

lemma thm_ok_assume:
  fixes ct :: pure_cterm
  assumes ok: "okT (assume_rule (crep_of ct)) r"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct) [ct_t (crep_of ct)] (csign_of ct)
    (returnW (Hyp (ct_t (crep_of ct)))) (zassume_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "csign_of ct" and ?t = "ct_t (crep_of ct)"
  note a = assume_rule_ok[OF ok]
  have common: "pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) ?t \<and> vars ?t = {} \<and> ttvars ?t = {}"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (crep_of ct)" by (rule pure_cterm_wf) (rule ps)
    have "wtp ?t" using wf a(1) by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
    with cterm_wf_novars[OF wf a(3)] show ?thesis by simp
  qed
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps')
    from common[OF ps'] have w: "wtp ?t" and v: "vars ?t = {}" "ttvars ?t = {}" by simp_all
    show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      using w v by (simp add: a(2) mk_rep_def thm_wf_def wt_thm_def ibelow_def vars_thm_def tvars_thm_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have "valid (csorts_of ct) [th_prop r] (th_tpairs r) (th_prop r)" by (rule assume_valid[OF ok])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def a(2) mk_rep_def)
  next
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
qed

theorem assume_thm:
  assumes "assume_thm ct = Some th"
  obtains r where "okT (assume_rule (crep_of ct)) r"
    "rep_thm th = mk_thm r (csorts_of ct) [ct_t (crep_of ct)] (csign_of ct)
      (returnW (Hyp (ct_t (crep_of ct)))) (zassume_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct)))"
proof -
  from assms obtain r where ok: "okT (assume_rule (crep_of ct)) r"
    and th: "th = Abs_thm (mk_thm r (csorts_of ct) [ct_t (crep_of ct)] (csign_of ct)
      (returnW (Hyp (ct_t (crep_of ct)))) (zassume_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))"
    by (auto simp: assume_thm_def resT_Some)
  show thesis
    by (rule that[OF ok]) (unfold th, rule rep_Abs_thm, rule thm_ok_assume[OF ok], simp)
qed


subsection \<open>Reflexivity and the conversions\<close>

text \<open>
  \<open>reflexive\<close> and the conversions derive \<open>t \<equiv> t'\<close> for a term \<open>t'\<close> convertible to the certified
  term \<open>t\<close>; their proofs are those of reflexivity (\<open>Thm.conversion_thm\<close> of the wrapper).
\<close>

context pure_sig
begin

definition conv_ok :: "(cterm_rep \<Rightarrow> thm_rep T) \<Rightarrow> bool" where
  "conv_ok f \<longleftrightarrow> (\<forall>t T m r. okT (f (CTerm t T m)) r \<longrightarrow> closed t \<longrightarrow> (\<forall>e. e \<turnstile> t : T) \<longrightarrow>
    (\<exists>t'. r = mk_rep m [] (eq_const T $ t $ t') \<and> closed t' \<and> (\<forall>e. e \<turnstile> t' : T) \<and> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and>
      vars t' \<subseteq> vars t \<and> ttvars t' \<subseteq> ttvars t))"

lemma conv_ok_result:
  assumes cf: "conv_ok f" and ok: "okT (f (CTerm t T m)) r" and wf: "cterm_wf (CTerm t T m)"
  obtains t' where "r = mk_rep m [] (eq_const T $ t $ t')" "closed t" "closed t'" "\<And>e. e \<turnstile> t : T"
    "\<And>e. e \<turnstile> t' : T" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" "vars t' \<subseteq> vars t" "ttvars t' \<subseteq> ttvars t"
proof -
  from wf have c: "closed t" and ty: "\<And>e. e \<turnstile> t : T" by (simp_all add: cterm_wf_def)
  from cf[unfolded conv_ok_def, rule_format, OF ok c] ty obtain t' where
    "r = mk_rep m [] (eq_const T $ t $ t')" "closed t'" "\<And>e. e \<turnstile> t' : T" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
    "vars t' \<subseteq> vars t" "ttvars t' \<subseteq> ttvars t"
    by blast
  with c ty show thesis by (intro that) simp_all
qed

lemma conv_thm_wf:
  assumes wf: "cterm_wf (CTerm t T m)" and eq: "eq_ok" and pr: "ar STR ''prop'' = 0"
    and c': "closed t'" and ty': "\<And>e. e \<turnstile> t' : T" and v: "vars t' \<subseteq> vars t" and tv: "ttvars t' \<subseteq> ttvars t"
  shows "thm_wf m [] [] (eq_const T $ t $ t')"
proof -
  from wf have c: "closed t" and ty: "\<And>e. e \<turnstile> t : T" and ib: "ibelow m t" and mm: "-1 \<le> m"
    and nn: "\<forall>v\<in>vars t. 0 \<le> snd (fst v)" and tn: "\<forall>v\<in>ttvars t. 0 \<le> snd (fst v)"
    by (simp_all add: cterm_wf_def)
  have tT: "tvars T \<subseteq> ttvars t" by (rule typing_tvars_closed[OF ty c])
  have cT: "cert_typ alg ar T" by (rule typing_cert_closed[OF ty c])
  have cP: "cert_typ alg ar propT" using pr by (simp add: cert_typ_def propT_def tarity_def)
  from eq obtain v S where cc: "ctab STR ''Pure.eq'' = Some (TVar v S \<rightarrow>\<^sub>T TVar v S \<rightarrow>\<^sub>T propT)"
    by (auto simp: eq_ok_def)
  have ct: "const_typ_ok ctab STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT)"
    unfolding const_typ_ok_def using cc by (auto intro!: exI[of _ "\<lambda>_ _. T"] simp: propT_def)
  have tc: "e \<turnstile> eq_const T : T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT" for e
    using ct cT cP by (intro typing.Const) (simp_all add: cert_typ_fun)
  have w: "wtp (eq_const T $ t $ t')"
  proof (rule wtpI)
    show "closed (eq_const T $ t $ t')" using c c' by (simp add: closed_def)
    show "(\<lambda>_. propT) \<turnstile> eq_const T $ t $ t' : propT" by (rule typing.App[OF typing.App[OF tc ty] ty'])
  qed
  have tP: "tvars propT = {}" by (simp add: propT_def)
  have ib': "ibelow m (eq_const T $ t $ t')" using ib tT v tv tP by (auto simp: ibelow_def)
  have vt: "vars_thm [] (eq_const T $ t $ t') = vars t \<union> vars t'"
    and tvt: "tvars_thm [] (eq_const T $ t $ t') \<subseteq> ttvars t"
    using tT tv tP by (auto simp: vars_thm_def tvars_thm_def)
  show ?thesis unfolding thm_wf_def wt_thm_def using w ib' mm nn tn vt tvt v by auto
qed

lemma conv_ok_reflexive: "conv_ok reflexive"
  unfolding conv_ok_def
proof (intro allI impI)
  fix t T m r assume ok: "okT (reflexive (CTerm t T m)) r" and c: "closed t" and ty: "\<forall>e. e \<turnstile> t : T"
  from ok obtain P where P: "ok (mk_equals (t, t)) P" and r: "r = mk_rep m [] P" by (auto simp: reflexive_def)
  have "P = eq_const T $ t $ t" using mk_equals_ok[OF P c] ty by blast
  with r c ty show "\<exists>t'. r = mk_rep m [] (eq_const T $ t $ t') \<and> closed t' \<and> (\<forall>e. e \<turnstile> t' : T) \<and> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and>
      vars t' \<subseteq> vars t \<and> ttvars t' \<subseteq> ttvars t"
    by (intro exI[of _ t]) (simp add: conv_refl)
qed

lemma conv_ok_beta_conversion: "conv_ok (beta_conversion full)"
  unfolding conv_ok_def
proof (intro allI impI)
  fix t T m r assume ok: "okT (beta_conversion full (CTerm t T m)) r" and c: "closed t" and ty: "\<forall>e. e \<turnstile> t : T"
  from ok obtain t' P where red: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and mk: "ok (mk_equals (t, t')) P" and r: "r = mk_rep m [] P"
    by (auto simp: beta_conversion_def returnW_def raiseW_def subst_bound_subst
      dest: beta_norm_reds split: if_splits pterm.splits)
  have c': "closed t'" by (rule beta_reds_closed[OF red c])
  have ty': "e \<turnstile> t' : T" for e using subject_reduction_beta'[OF red] ty by blast
  have cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" by (rule beta_eta_conv[OF beta_reds_sup[OF red]]) (use ty in \<open>auto simp: wt_def\<close>)
  have "P = eq_const T $ t $ t'" using mk_equals_ok[OF mk c] ty by blast
  with r c' ty' cv beta_reds_vars[OF red] ttvars_mono[OF beta_reds_typs[OF red]]
  show "\<exists>t'. r = mk_rep m [] (eq_const T $ t $ t') \<and> closed t' \<and> (\<forall>e. e \<turnstile> t' : T) \<and> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and>
      vars t' \<subseteq> vars t \<and> ttvars t' \<subseteq> ttvars t"
    by blast
qed

lemma conv_ok_eta_conversion: "conv_ok eta_conversion"
  unfolding conv_ok_def
proof (intro allI impI)
  fix t T m r assume ok: "okT (eta_conversion (CTerm t T m)) r" and c: "closed t" and ty: "\<forall>e. e \<turnstile> t : T"
  from ok obtain P where mk: "ok (mk_equals (t, eta_contract t)) P" and r: "r = mk_rep m [] P"
    by (auto simp: eta_conversion_def)
  note red = eta_contract_reds[of t]
  have c': "closed (eta_contract t)" by (rule eta_reds_closed[OF red c])
  have ty': "e \<turnstile> eta_contract t : T" for e using eta_reds_typing[OF red] ty by blast
  have cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract t" by (rule beta_eta_conv[OF eta_reds_sup[OF red]]) (use ty in \<open>auto simp: wt_def\<close>)
  have "P = eq_const T $ t $ eta_contract t" using mk_equals_ok[OF mk c] ty by blast
  with r c' ty' cv eta_reds_vars_typs[OF red] ttvars_mono[of "eta_contract t" t]
  show "\<exists>t'. r = mk_rep m [] (eq_const T $ t $ t') \<and> closed t' \<and> (\<forall>e. e \<turnstile> t' : T) \<and> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and>
      vars t' \<subseteq> vars t \<and> ttvars t' \<subseteq> ttvars t"
    by blast
qed

end

definition conv_data :: "pure_cterm \<Rightarrow> thm_rep \<Rightarrow> thm_data" where
  "conv_data ct r = mk_thm r (csorts_of ct) [] (csign_of ct) (returnW reflexive_proof)
    (zreflexive_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_T (crep_of ct)) (ct_t (crep_of ct)))"

definition conversion_thm :: "pure_cterm \<Rightarrow> (cterm_rep \<Rightarrow> thm_rep T) \<Rightarrow> 'u pure_thm option" where
  "conversion_thm ct f =
    (if sign_eq (csign_of ct) then map_option (\<lambda>r. Abs_thm (conv_data ct r)) (resT (f (crep_of ct))) else None)"

lemma thm_ok_conversion:
  fixes ct :: pure_cterm
  assumes ok: "okT (f (crep_of ct)) r" and se: "sign_eq (csign_of ct)"
    and cf: "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) \<Longrightarrow>
      pure_sig.conv_ok (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) f"
  shows "thm_ok TYPE('u) (conv_data ct r)"
proof -
  let ?c = "csign_of ct"
  obtain t T m where cr: "crep_of ct = CTerm t T m" by (cases "crep_of ct")
  have ok': "okT (f (CTerm t T m)) r" using ok by (simp add: cr)
  have eq: "pure_sig.eq_ok (sg_consts ?c)" and pr: "sg_ar ?c STR ''prop'' = 0" using se by (simp_all add: sign_eq_def)
  have th: "th_sign (conv_data ct r) = ?c" "th_shyps (conv_data ct r) = csorts_of ct" "th_hyps (conv_data ct r) = []"
    "th_maxidx (conv_data ct r) = th_maxidx r" "th_tpairs (conv_data ct r) = th_tpairs r" "th_prop (conv_data ct r) = th_prop r"
    by (simp_all add: conv_data_def)
  show ?thesis
  proof (rule thm_okI)
    assume ps: "pure_sig (sg_alg (th_sign (conv_data ct r))) (sg_ar (th_sign (conv_data ct r)))"
    then have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" by (simp add: th)
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps')
    have wf: "cterm_wf (CTerm t T m)" using pure_cterm_wf[OF ps'] by (simp add: cr)
    obtain t' where r: "r = mk_rep m [] (eq_const T $ t $ t')" and c: "closed t" "closed t'"
      and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T" and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
      and v: "vars t' \<subseteq> vars t" and tv: "ttvars t' \<subseteq> ttvars t"
      by (rule conv_ok_result[OF cf[OF ps'] ok' wf]) blast
    have "thm_wf m [] [] (eq_const T $ t $ t')" by (rule conv_thm_wf[OF wf eq pr c(2) ty(2) v tv])
    then show "pure_sig.thm_wf (sg_alg (th_sign (conv_data ct r))) (sg_ar (th_sign (conv_data ct r)))
        (sg_consts (th_sign (conv_data ct r))) (th_maxidx (conv_data ct r)) (th_hyps (conv_data ct r))
        (th_tpairs (conv_data ct r)) (th_prop (conv_data ct r))"
      by (simp only: th) (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign (conv_data ct r))) (sg_ar (th_sign (conv_data ct r)))"
      and M: "is_model (th_sign (conv_data ct r)) M"
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by (simp add: th)
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in \<open>simp add: th\<close>)
    have wf: "cterm_wf (CTerm t T m)" using pure_cterm_wf[OF ps'] by (simp add: cr)
    obtain t' where r: "r = mk_rep m [] (eq_const T $ t $ t')" and c: "closed t" "closed t'"
      and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T" and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
      and v: "vars t' \<subseteq> vars t" and tv: "ttvars t' \<subseteq> ttvars t"
      by (rule conv_ok_result[OF cf[OF ps'] ok' wf]) blast
    have "valid (csorts_of ct) [] [] (eq_const T $ t $ t')" by (rule valid_conv_eq[OF eq c ty cv])
    then show "valid_in (th_sign (conv_data ct r)) M (th_shyps (conv_data ct r)) (th_hyps (conv_data ct r))
        (th_tpairs (conv_data ct r)) (th_prop (conv_data ct r))"
      by (simp only: th) (simp add: r mk_rep_def valid_in_def)
  next
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
          (use zterm_ok_zterm_of_pnn[OF x pt] zloose_zterm_of[OF x] c(1) in \<open>auto simp: zeq_vars_def closed_def\<close>)
      with v(1) show "zvalid (sg_ax ?c) (set []) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
        by (simp add: r mk_rep_def zhyps_ok_def)
    qed
  qed
qed

theorem conversion_thm:
  assumes "conversion_thm ct f = Some th"
    and cf: "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) \<Longrightarrow>
      pure_sig.conv_ok (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) f"
  obtains r where "okT (f (crep_of ct)) r" "sign_eq (csign_of ct)" "rep_thm th = conv_data ct r"
proof -
  from assms(1) obtain r where se: "sign_eq (csign_of ct)" and ok: "okT (f (crep_of ct)) r"
    and th: "th = Abs_thm (conv_data ct r)"
    by (auto simp: conversion_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok se]) (unfold th, rule rep_Abs_thm, rule thm_ok_conversion[OF ok se cf], simp_all add: conv_data_def)
qed

definition reflexive_thm :: "pure_cterm \<Rightarrow> 'u pure_thm option" where
  "reflexive_thm ct = conversion_thm ct reflexive"

definition beta_conversion_thm :: "bool \<Rightarrow> pure_cterm \<Rightarrow> 'u pure_thm option" where
  "beta_conversion_thm full ct = conversion_thm ct (beta_conversion full)"

definition eta_conversion_thm :: "pure_cterm \<Rightarrow> 'u pure_thm option" where
  "eta_conversion_thm ct = conversion_thm ct eta_conversion"

theorem reflexive_thm:
  assumes "reflexive_thm ct = Some th"
  obtains r where "okT (reflexive (crep_of ct)) r" "sign_eq (csign_of ct)" "rep_thm th = conv_data ct r"
  using conversion_thm[OF assms[unfolded reflexive_thm_def] pure_sig.conv_ok_reflexive] by blast

theorem beta_conversion_thm:
  assumes "beta_conversion_thm full ct = Some th"
  obtains r where "okT (beta_conversion full (crep_of ct)) r" "sign_eq (csign_of ct)" "rep_thm th = conv_data ct r"
  using conversion_thm[OF assms[unfolded beta_conversion_thm_def] pure_sig.conv_ok_beta_conversion] by blast

theorem eta_conversion_thm:
  assumes "eta_conversion_thm ct = Some th"
  obtains r where "okT (eta_conversion (crep_of ct)) r" "sign_eq (csign_of ct)" "rep_thm th = conv_data ct r"
  using conversion_thm[OF assms[unfolded eta_conversion_thm_def] pure_sig.conv_ok_eta_conversion] by blast


subsection \<open>The trivial implication\<close>

context pure_sig
begin

lemma wtp_implies:
  assumes wA: "wtp A" and wB: "wtp B"
  shows "wtp (implies $ A $ B)"
proof (rule wtpI)
  show "closed (implies $ A $ B)" using wtpD(1)[OF wA] wtpD(1)[OF wB] by (simp add: closed_def implies_def)
  have cP: "cert_typ alg ar propT" by (rule typing_cert_closed[OF wtpD(2)[OF wA] wtpD(1)[OF wA]])
  have "(\<lambda>_. propT) \<turnstile> implies : propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT"
    unfolding implies_def using cP by (intro typing.Const) (simp_all add: const_typ_ok_def propT_def cert_typ_fun)
  then show "(\<lambda>_. propT) \<turnstile> implies $ A $ B : propT"
    by (rule typing.App[OF typing.App[OF _ wtpD(2)[OF wA]] wtpD(2)[OF wB]])
qed

lemma vars_implies [simp]: "vars implies = {}" and ttvars_implies [simp]: "ttvars implies = {}"
  by (simp_all add: implies_def propT_def)

end

definition trivial_thm :: "pure_cterm \<Rightarrow> 'u pure_thm option" where
  "trivial_thm ct = map_option (\<lambda>r. Abs_thm (mk_thm r (csorts_of ct) [] (csign_of ct)
      (returnW trivial_proof) (ztrivial_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct)))))
    (resT (trivial (crep_of ct)))"

lemma thm_ok_trivial:
  fixes ct :: pure_cterm
  assumes ok: "okT (trivial (crep_of ct)) r"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct) [] (csign_of ct)
    (returnW trivial_proof) (ztrivial_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "csign_of ct"
  obtain t T m where cr: "crep_of ct = CTerm t T m" by (cases "crep_of ct")
  from ok have T: "T = propT" and r: "r = mk_rep m [] (implies $ t $ t)"
    by (auto simp: trivial_def cr returnW_def raiseW_def mk_implies_def split: if_splits)
  have common: "pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) t \<and>
      pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm t T m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm t T m)" using pure_cterm_wf[OF ps] by (simp add: cr)
    then have "wtp t" using T by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
    with wf show ?thesis by simp
  qed
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    from common[OF ps] have w: "wtp t" and wf: "cterm_wf (CTerm t T m)" by simp_all
    have "thm_wf m [] [] (implies $ t $ t)"
      using wtp_implies[OF w w] wf by (auto simp: thm_wf_def wt_thm_def cterm_wf_def ibelow_def vars_thm_def tvars_thm_def)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r mk_rep_def)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    from common ps have w: "wtp t" by simp
    have "valid (csorts_of ct) [] (th_tpairs r) (th_prop r)" by (rule trivial_valid[OF ok[unfolded cr] w])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
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
qed

theorem trivial_thm:
  assumes "trivial_thm ct = Some th"
  obtains r where "okT (trivial (crep_of ct)) r"
    "rep_thm th = mk_thm r (csorts_of ct) [] (csign_of ct)
      (returnW trivial_proof) (ztrivial_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct)))"
proof -
  from assms obtain r where ok: "okT (trivial (crep_of ct)) r"
    and th: "th = Abs_thm (mk_thm r (csorts_of ct) [] (csign_of ct)
      (returnW trivial_proof) (ztrivial_proof (pure_sig.ztargs (sg_consts (csign_of ct))) (ct_t (crep_of ct))))"
    by (auto simp: trivial_thm_def resT_Some)
  show thesis
    by (rule that[OF ok]) (unfold th, rule rep_Abs_thm, rule thm_ok_trivial[OF ok], simp)
qed


subsection \<open>Weakening\<close>

lemma weaken_ok:
  assumes "okT (weaken ct th) r"
  shows "ct_T ct = propT" "r = th" "ct_maxidx ct = -1 \<or> ct_maxidx ct < -1 \<or> maxidx_of_term (ct_t ct) \<le> -1"
  using assms by (auto simp: weaken_def adjust_maxidx_cterm_def Let_def returnW_def raiseW_def max_def
    split: if_splits)

definition weaken_thm :: "pure_cterm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "weaken_thm ct th =
    (if csign_of ct = sign_of th then
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (ct_t (crep_of ct) # hyps_of th) (sign_of th)
          (proof_of th) (zproof_of th))))
        (resT (weaken (crep_of ct) (rep_of th)))
     else None)"

lemma thm_ok_weaken:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (weaken (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct \<union> shyps_of th) (ct_t (crep_of ct) # hyps_of th) (sign_of th)
    (proof_of th) (zproof_of th))"
    (is "thm_ok _ ?th")
proof -
  let ?c = "sign_of th" and ?t = "ct_t (crep_of ct)"
  note a = weaken_ok[OF ok]
  have common: "pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) ?t \<and> vars ?t = {} \<and> ttvars ?t = {}"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (crep_of ct)" using pure_cterm_wf[of ct] ps c by simp
    have "wtp ?t" using wf a(1) by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
    with cterm_wf_novars[OF wf a(3)] show ?thesis by simp
  qed
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    from common[OF ps] have w: "wtp ?t" and v: "vars ?t = {}" "ttvars ?t = {}" by simp_all
    have "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    then have "thm_wf (th_maxidx (rep_of th)) (?t # hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using w v by (simp add: thm_wf_def wt_thm_def)
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: a(2))
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid_in[of th M] M by simp
    have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      by (rule valid_mono[OF v]) simp
    then have "valid (csorts_of ct \<union> shyps_of th) (?t # hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule weaken_valid[OF ok])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
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
qed

theorem weaken_thm:
  assumes "weaken_thm ct th = Some th'"
  obtains r where "okT (weaken (crep_of ct) (rep_of th)) r" "csign_of ct = sign_of th"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (ct_t (crep_of ct) # hyps_of th) (sign_of th)
      (proof_of th) (zproof_of th))"
proof -
  from assms obtain r where c: "csign_of ct = sign_of th" and ok: "okT (weaken (crep_of ct) (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (ct_t (crep_of ct) # hyps_of th) (sign_of th)
      (proof_of th) (zproof_of th)))"
    by (auto simp: weaken_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c]) (use thm_ok_weaken[OF ok c] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed


subsection \<open>Universal elimination\<close>

context pure_sig
begin

lemma thm_wf_extend:
  assumes w: "thm_wf m0 hs tps P" and wQ: "wtp Q"
    and vQ: "vars Q \<subseteq> vars P \<union> V" and tQ: "ttvars Q \<subseteq> ttvars P \<union> TV"
    and V: "\<forall>v\<in>V. 0 \<le> snd (fst v) \<and> snd (fst v) \<le> m" and TV: "\<forall>v\<in>TV. 0 \<le> snd (fst v) \<and> snd (fst v) \<le> m"
  shows "thm_wf (max m m0) hs tps Q"
proof -
  let ?m = "max m m0"
  from w obtain ib: "ibelow m0 P" and h: "\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tp: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> ibelow m0 t \<and> ibelow m0 u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and m0: "-1 \<le> m0" and vn: "\<forall>v\<in>vars_thm tps P. 0 \<le> snd (fst v)"
    and tn: "\<forall>v\<in>tvars_thm tps P. 0 \<le> snd (fst v)"
    unfolding thm_wf_def wt_thm_def by blast
  have mx: "m \<le> ?m" "m0 \<le> ?m" by simp_all
  have ib': "ibelow ?m Q"
    unfolding ibelow_def
  proof (intro conjI ballI)
    fix v assume "v \<in> vars Q"
    with vQ have "v \<in> vars P \<or> v \<in> V" by blast
    then show "snd (fst v) \<le> ?m" using ib V unfolding ibelow_def by (meson order_trans mx)
  next
    fix v assume "v \<in> ttvars Q"
    with tQ have "v \<in> ttvars P \<or> v \<in> TV" by blast
    then show "snd (fst v) \<le> ?m" using ib TV unfolding ibelow_def by (meson order_trans mx)
  qed
  have tp': "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> ibelow ?m t \<and> ibelow ?m u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  proof (intro ballI, clarify)
    fix t u assume "(t, u) \<in> set tps"
    with tp have "closed t \<and> closed u \<and> ibelow m0 t \<and> ibelow m0 u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
      by blast
    then show "closed t \<and> closed u \<and> ibelow ?m t \<and> ibelow ?m u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
      using ibelow_mono[OF _ mx(2)] by blast
  qed
  have mm: "-1 \<le> ?m" using m0 by simp
  have vn': "\<forall>v\<in>vars_thm tps Q. 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> vars_thm tps Q"
    then have "v \<in> vars_thm tps P \<or> v \<in> V" using vQ unfolding vars_thm_def by blast
    then show "0 \<le> snd (fst v)" using vn V by blast
  qed
  have tn': "\<forall>v\<in>tvars_thm tps Q. 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> tvars_thm tps Q"
    then have "v \<in> tvars_thm tps P \<or> v \<in> TV" using tQ unfolding tvars_thm_def by blast
    then show "0 \<le> snd (fst v)" using tn TV by blast
  qed
  show ?thesis unfolding thm_wf_def wt_thm_def using wQ ib' h tp' mm vn' tn' by blast
qed

lemma betapply_vars_typs: "vars (betapply A t) \<subseteq> vars A \<union> vars t \<and> typs (betapply A t) \<subseteq> typs A \<union> typs t"
proof (cases A)
  case (Abs a U b)
  then show ?thesis using vars_subst[of b t 0] typs_subst[of b t 0] by (auto simp: subst_bound_subst)
qed simp_all

lemma forall_elim_result:
  assumes d: "dest_all_app P = Some (T, A)" and w: "wtp P" and ct: "closed t" "\<And>e. e \<turnstile> t : T"
  shows "wtp (betapply A t)" "vars (betapply A t) \<subseteq> vars P \<union> vars t" "ttvars (betapply A t) \<subseteq> ttvars P \<union> ttvars t"
proof -
  note dw = dest_all_app_wtp[OF d w]
  have wAt: "wtp (A $ t)" using dw(2,3) ct by (intro wtpI) (auto simp: closed_def)
  show "wtp (betapply A t)"
  proof (cases A)
    case (Abs a U b)
    then have red: "A $ t \<rightarrow>\<^sub>\<beta> betapply A t" by (simp add: subst_bound_subst)
    show ?thesis
    proof (rule wtpI)
      show "closed (betapply A t)"
        using wtpD(1)[OF wAt] free_beta[OF red] by (auto simp: closed_iff_loose_bvar1)
      show "(\<lambda>_. propT) \<turnstile> betapply A t : propT" by (rule subject_reduction_beta[OF wtpD(2)[OF wAt] red])
    qed
  qed (use wAt in simp_all)
  have vP: "vars P = vars A" and tP: "ttvars A \<subseteq> ttvars P" using dw(1) by (simp_all add: all_const_def)
  show "vars (betapply A t) \<subseteq> vars P \<union> vars t" using betapply_vars_typs[of A t] vP by blast
  have "ttvars (betapply A t) \<subseteq> ttvars A \<union> ttvars t"
    using betapply_vars_typs[of A t] unfolding ttvars_def by blast
  with tP show "ttvars (betapply A t) \<subseteq> ttvars P \<union> ttvars t" by blast
qed

end

definition forall_elim_thm :: "pure_cterm \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "forall_elim_thm ct th =
    (if csign_of ct = sign_of th then
      map_option (\<lambda>r. Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
          (bindW (proof_of th) (\<lambda>p. returnW (PAppt p (Some (ct_t (crep_of ct))))))
          (bindM (zproof_of th) (\<lambda>p. zforall_elim_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)) p)))))
        (resT (forall_elim (crep_of ct) (rep_of th)))
     else None)"

lemma thm_ok_forall_elim:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (forall_elim (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
  shows "thm_ok TYPE('u) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (PAppt p (Some (ct_t (crep_of ct))))))
    (bindM (zproof_of th) (\<lambda>p. zforall_elim_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)) p)))"
    (is "thm_ok _ ?th")
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
  show ?thesis
  proof (rule thm_okI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm t T m)" by (rule wfc[OF ps])
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    have ct: "closed t" "\<And>e. e \<turnstile> t : T" using wf by (simp_all add: cterm_wf_def)
    note fr = forall_elim_result[OF d w ct]
    have "thm_wf (max m (th_maxidx (rep_of th))) (hyps_of th) (th_tpairs (rep_of th)) (betapply A t)"
      by (rule thm_wf_extend[OF w0 fr(1) fr(2) fr(3)]) (use wf in \<open>auto simp: cterm_wf_def ibelow_def\<close>)
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
    have wf: "cterm_wf (CTerm t T m)" by (rule wfc[OF ps'])
    have ct: "closed t" "\<And>e. e \<turnstile> t : T" using wf by (simp_all add: cterm_wf_def)
    have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps' by (simp add: thm_wf_def wt_thm_def)
    have v: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid_in[of th M] M by simp
    have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      by (rule valid_mono[OF v]) simp
    then have "valid (csorts_of ct \<union> shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule forall_elim_valid[OF ok' _ w ct])
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  next
    assume psig: "is_prf_sig (th_sign ?th)"
    then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
      by (simp add: is_prf_sig_def)
    have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
    have wf: "cterm_wf (CTerm t T m)" by (rule wfc[OF ps])
    have ct: "closed t" "\<And>e. e \<turnstile> t : T" using wf by (simp_all add: cterm_wf_def)
    have pt: "pnn t" using wf by (simp add: cterm_wf_def pnn_iff)
    have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps by (simp add: thm_wf_def wt_thm_def)
    have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
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
qed

theorem forall_elim_thm:
  assumes "forall_elim_thm ct th = Some th'"
  obtains r where "okT (forall_elim (crep_of ct) (rep_of th)) r" "csign_of ct = sign_of th"
    "rep_thm th' = with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (PAppt p (Some (ct_t (crep_of ct))))))
      (bindM (zproof_of th) (\<lambda>p. zforall_elim_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)) p)))"
proof -
  from assms obtain r where c: "csign_of ct = sign_of th" and ok: "okT (forall_elim (crep_of ct) (rep_of th)) r"
    and th': "th' = Abs_thm (with_cons (cons_of th) (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (\<lambda>p. returnW (PAppt p (Some (ct_t (crep_of ct))))))
      (bindM (zproof_of th) (\<lambda>p. zforall_elim_proof (pure_sig.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)) p))))"
    by (auto simp: forall_elim_thm_def resT_Some split: if_splits)
  show thesis
    by (rule that[OF ok c]) (use thm_ok_forall_elim[OF ok c] in \<open>simp add: th' Abs_thm_inverse\<close>)
qed

end
