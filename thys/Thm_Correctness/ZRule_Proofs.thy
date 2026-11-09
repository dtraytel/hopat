section \<open>Validity of the tight proofs of the inference rules\<close>

theory ZRule_Proofs
  imports Rule_Proofs
begin

context prf_model
begin

lemma zvalidI: "pcerase w = pcerase (zprf_tr p) \<Longrightarrow> prf_valid ax H tps w \<phi> \<Longrightarrow> zvalid ax H tps p \<phi>"
  unfolding zvalid_def by blast

lemma zvalidE:
  assumes "zvalid ax H tps p \<phi>"
  obtains w where "pcerase w = pcerase (zprf_tr p)" "prf_valid ax H tps w \<phi>"
  using assms unfolding zvalid_def by blast

text \<open>Proofs that agree up to the convertibility of their annotations in every instance:\<close>

lemma prf_valid_aeq:
  "prf_valid ax H tps p \<phi> \<Longrightarrow> (\<And>\<rho> \<sigma>. cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> prf_aeq (prf_ap \<rho> \<sigma> p) (prf_ap \<rho> \<sigma> q)) \<Longrightarrow>
    prf_valid ax H tps q \<phi>"
  unfolding prf_valid_def by (blast intro: prf_ok_aeq)

lemma zterm_of_ground:
  assumes "zterm_of ztargs A = return z" "wtp A" "vars A = {}" "ttvars A = {}"
  shows "zdec z = A"
proof -
  have "\<exists>z. zterm_of ztargs A = return z \<and> zdec z = A"
    by (rule zterm_of_zdec[OF wtpD(2)[OF assms(2)]]) (use assms(3,4) in \<open>auto simp: ttvars_def\<close>)
  with assms(1) show ?thesis by auto
qed

lemma ueq_zdec_zterm_of: "zterm_of ta t = return z \<Longrightarrow> noneg t \<Longrightarrow> ap \<rho> \<sigma> (zdec z) \<approx> ap \<rho> \<sigma> t"
  using erase_ap_zdec_zterm_of[of ta t z \<rho> \<sigma>] by simp


subsection \<open>Hypotheses, implication and universal quantification\<close>

theorem zassume_proof_valid:
  assumes z: "zassume_proof ztargs A = return p" and A: "A \<in> H" "wtp A" "vars A = {}" "ttvars A = {}"
  shows "zvalid ax H [] p A"
proof -
  from z obtain A' where A': "zterm_of ztargs A = return A'" "p = ZHyp A'"
    by (auto simp: zassume_proof_def bindZ_eq_returnZ)
  have "zdec A' = A" by (rule zterm_of_ground[OF A'(1) A(2-4)])
  then have "zprf_tr p = Hyp A" by (simp add: A'(2))
  then show ?thesis by (intro zvalidI[of "Hyp A"]) (simp_all add: assume_proof_valid[OF A])
qed

theorem ztrivial_proof_valid:
  assumes z: "ztrivial_proof ztargs A = return p" and wA: "wtp A" and nA: "noneg A"
  shows "zvalid ax H [] p (implies $ A $ A)"
proof -
  from z obtain A' where A': "zterm_of ztargs A = return A'" "p = ZAbsp STR ''H'' A' (ZBoundp 0)"
    by (auto simp: ztrivial_proof_def bindZ_eq_returnZ)
  let ?w = "AbsP STR ''H'' (Some (zdec A')) (PBound 0)"
  have "prf_valid ax H [] ?w (implies $ A $ A)"
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    have t: "e \<turnstile> ap \<rho> \<sigma> A : propT" by (rule typing_ap_wtp[OF wA \<rho> \<sigma>])
    have a: "ap \<rho> \<sigma> (zdec A') \<approx> ap \<rho> \<sigma> A" by (rule ueq_zdec_zterm_of[OF A'(1) nA])
    have "prf_ok ax H e [ap \<rho> \<sigma> A] (PBound 0) (ap \<rho> \<sigma> A)"
      using prf_ok.PBound[of 0 "[ap \<rho> \<sigma> A]" e] t by simp
    then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> ?w) (ap \<rho> \<sigma> (implies $ A $ A))"
      using t a by (simp add: prf_ap_def ap_def[symmetric] prf_ok.AbsP)
  qed
  then show ?thesis by (intro zvalidI[of ?w]) (simp_all add: A'(2))
qed

theorem zimplies_elim_rule_proof_valid:
  assumes ok: "okT (implies_elim thAB thA) th"
    and p: "zvalid ax H1 (th_tpairs thAB) p (th_prop thAB)"
    and q: "zvalid ax H2 (th_tpairs thA) q (th_prop thA)"
    and w1: "wtp (th_prop thAB)" and w2: "wtp (th_prop thA)"
  shows "zvalid ax (H1 \<union> H2) (th_tpairs th) (ZAppp p q) (th_prop th)"
proof -
  obtain wp where wp: "pcerase wp = pcerase (zprf_tr p)" "prf_valid ax H1 (th_tpairs thAB) wp (th_prop thAB)"
    using p by (rule zvalidE)
  obtain wq where wq: "pcerase wq = pcerase (zprf_tr q)" "prf_valid ax H2 (th_tpairs thA) wq (th_prop thA)"
    using q by (rule zvalidE)
  show ?thesis
    by (rule zvalidI[OF _ implies_elim_rule_proof_valid[OF ok wp(2) wq(2) w1 w2]]) (simp add: wp(1) wq(1))
qed

theorem zforall_elim_rule_proof_valid:
  assumes ok: "okT (forall_elim (CTerm t T m) th0) th"
    and p: "zvalid ax H (th_tpairs th0) prf (th_prop th0)"
    and w: "wtp (th_prop th0)" and ct: "closed t" "\<And>e. e \<turnstile> t : T" and nt: "noneg t"
    and z: "zforall_elim_proof ztargs t prf = return q"
  shows "zvalid ax H (th_tpairs th) q (th_prop th)"
proof -
  from z obtain t' where t': "zterm_of ztargs t = return t'" "q = ZAppt prf t'"
    by (auto simp: zforall_elim_proof_def bindZ_eq_returnZ)
  obtain w0 where w0: "pcerase w0 = pcerase (zprf_tr prf)" "prf_valid ax H (th_tpairs th0) w0 (th_prop th0)"
    using p by (rule zvalidE)
  have "prf_valid ax H (th_tpairs th) (PAppt w0 (Some t)) (th_prop th)"
    by (rule forall_elim_rule_proof_valid[OF ok w0(2) w ct])
  then have "prf_valid ax H (th_tpairs th) (PAppt w0 (Some (zdec t'))) (th_prop th)"
  proof (rule prf_valid_aeq)
    fix \<rho> \<sigma> show "prf_aeq (prf_ap \<rho> \<sigma> (PAppt w0 (Some t))) (prf_ap \<rho> \<sigma> (PAppt w0 (Some (zdec t'))))"
      using ueq_zdec_zterm_of[OF t'(1) nt, of \<rho> \<sigma>]
      by (simp add: prf_ap_def prf_aeq.PAppt prf_aeq.refl ann_eq_def ueq_sym)
  qed
  then show ?thesis by (rule zvalidI[rotated]) (simp add: t'(2) w0(1))
qed

end

text \<open>The hypotheses of a tight proof:\<close>

fun zhyps :: "zproof \<Rightarrow> zterm set" where
  "zhyps (ZHyp t) = {t}"
| "zhyps (ZAbst a T p) = zhyps p"
| "zhyps (ZAbsp a t p) = zhyps p"
| "zhyps (ZAppt p t) = zhyps p"
| "zhyps (ZAppp p q) = zhyps p \<union> zhyps q"
| "zhyps _ = {}"

lemma aconv_zterm_refl [simp]: "aconv_zterm t t"
  by (induction t) simp_all

text \<open>Converting \<open>\<alpha>\<close>-convertible terms gives \<open>\<alpha>\<close>-convertible tight terms:\<close>

lemma zterm_of_aconv:
  "aconv_term A B \<Longrightarrow> zterm_of ta A = return h \<Longrightarrow> zterm_of ta B = return t \<Longrightarrow> aconv_zterm h t"
proof (induction A arbitrary: B h t)
  case (Const c T)
  then have "B = Const c T" by (cases B) auto
  with Const.prems show ?case by simp
next
  case (Free x T)
  then have "B = Free x T" by (cases B) auto
  with Free.prems show ?case by simp
next
  case (Var x T)
  then have "B = Var x T" by (cases B) auto
  with Var.prems show ?case by simp
next
  case (Bound i)
  then have "B = Bound i" by (cases B) auto
  with Bound.prems show ?case by simp
next
  case (Abs a T b)
  then obtain a' b' where B: "B = Abs a' T b'" "aconv_term b b'" by (cases B) auto
  from Abs.prems(2) obtain hb where hb: "zterm_of ta b = return hb" "h = ZAbs a (ztyp_of T) hb"
    by (auto simp: bindZ_eq_returnZ)
  from Abs.prems(3) B obtain tb where tb: "zterm_of ta b' = return tb" "t = ZAbs a' (ztyp_of T) tb"
    by (auto simp: bindZ_eq_returnZ)
  show ?case using Abs.IH[OF B(2) hb(1) tb(1)] by (simp add: hb(2) tb(2))
next
  case (App t1 u1)
  then obtain t2 u2 where B: "B = t2 $ u2" "aconv_term t1 t2" "aconv_term u1 u2" by (cases B) auto
  show ?case
  proof (cases "\<exists>c T d U. t1 = Const c T \<and> u1 = Const d U")
    case True
    with B have "B = t1 $ u1" by auto
    with App.prems show ?thesis by simp
  next
    case False
    have F2: "\<not> (\<exists>c T d U. t2 = Const c T \<and> u2 = Const d U)"
    proof
      assume "\<exists>c T d U. t2 = Const c T \<and> u2 = Const d U"
      then obtain c T d U where "t2 = Const c T" "u2 = Const d U" by blast
      with B(2,3) have "t1 = Const c T" "u1 = Const d U" by (cases t1; simp; cases u1; simp)+
      with False show False by blast
    qed
    have m: "match_of_class (t1 $ u1) = None" "match_of_class (t2 $ u2) = None"
      using False F2 by (auto simp: match_of_class_def split: pterm.splits)
    from App.prems(2) m(1) obtain h1 h2 where h: "zterm_of ta t1 = return h1" "zterm_of ta u1 = return h2"
      "h = ZApp h1 h2"
      by (auto simp: bindZ_eq_returnZ)
    from App.prems(3) m(2) B(1) obtain k1 k2 where k: "zterm_of ta t2 = return k1" "zterm_of ta u2 = return k2"
      "t = ZApp k1 k2"
      by (auto simp: bindZ_eq_returnZ)
    show ?thesis using App.IH(1)[OF B(2) h(1) k(1)] App.IH(2)[OF B(3) h(2) k(2)] by (simp add: h(3) k(3))
  qed
qed

lemma pcerase_abshyp: "pcerase (abshyp h i p) = abshyp h i (pcerase p)"
  by (induction p arbitrary: i) simp_all

context prf_model
begin

lemma aconv_zterm_zdec: "aconv_zterm h t \<Longrightarrow> aconv_term (zdec h) (zdec t)"
  by (induction h t rule: aconv_zterm.induct) auto

lemma zprf_tr_zabshyp:
  "(\<And>t. t \<in> zhyps p \<Longrightarrow> aconv_zterm h t \<longleftrightarrow> aconv_term A (zdec t)) \<Longrightarrow>
    zprf_tr (zabshyp h i p) = abshyp A i (zprf_tr p)"
  by (induction p arbitrary: i) auto

lemma implies_intr_proof_valid_ann:
  assumes p: "prf_valid ax H tps prf B" and wh: "wtp h"
    and H: "\<And>t. t \<in> H \<Longrightarrow> vars t = {} \<and> ttvars t = {}"
    and a: "\<And>\<rho> \<sigma>. cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> ann_ok (map_option (ap \<rho> \<sigma>) t) (ap \<rho> \<sigma> h)"
  shows "prf_valid ax {t \<in> H. \<not> aconv_term h t} tps (AbsP STR ''H'' t (abshyp h 0 prf)) (implies $ h $ B)"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  let ?h = "ap \<rho> \<sigma> h"
  have th: "e \<turnstile> ?h : propT" for e by (rule typing_ap_wtp[OF wh \<rho> \<sigma>])
  have ch: "closed ?h" using wtpD(1)[OF wh] \<sigma> by (simp add: closed_def)
  have c: "?h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" if "t \<in> H" "aconv_term h t" for t
  proof -
    from that(2) have u: "unname h = unname t" by (simp add: aconv_term_unname)
    have "vars h = {}" "ttvars h = {}"
      using arg_cong[OF u, of vars] arg_cong[OF u, of ttvars] H[OF that(1)] by simp_all
    then have "?h = h" by (rule ap_ground)
    moreover have "wt h" using wtpD(2)[OF wh] by (auto simp: wt_def)
    ultimately show ?thesis using aconv_term_conv[OF that(2)] by simp
  qed
  have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> prf) (ap \<rho> \<sigma> B)" by (rule prf_validD[OF p \<rho> \<sigma> sol])
  from prf_ok_abshyp[OF this ch th c]
  have "prf_ok ax {t \<in> H. \<not> aconv_term h t} e [?h] (abshyp h 0 (prf_ap \<rho> \<sigma> prf)) (ap \<rho> \<sigma> B)" by simp
  from prf_ok.AbsP[OF th a[OF \<rho> \<sigma>] this]
  show "prf_ok ax {t \<in> H. \<not> aconv_term h t} e [] (prf_ap \<rho> \<sigma> (AbsP STR ''H'' t (abshyp h 0 prf)))
      (ap \<rho> \<sigma> (implies $ h $ B))"
    by (simp add: prf_ap_def map_proof_terms_abshyp ap_def[symmetric])
qed

theorem zimplies_intr_rule_proof_valid:
  assumes ok: "okT (implies_intr (CTerm A U m) th0) th"
    and p: "zvalid ax H (th_tpairs th0) prf (th_prop th0)" and wA: "wtp A" and nA: "noneg A"
    and H: "\<And>t. t \<in> H \<Longrightarrow> vars t = {} \<and> ttvars t = {}"
    and hy: "\<And>t. t \<in> zhyps prf \<Longrightarrow> zterm_of ztargs (zdec t) = return t"
    and z: "zimplies_intr_proof ztargs A prf = return q"
  shows "zvalid ax {t \<in> H. \<not> aconv_term A t} (th_tpairs th) q (th_prop th)"
proof -
  from ok have th: "th = mk_rep (max m (th_maxidx th0)) (th_tpairs th0) (mk_implies A (th_prop th0))"
    by (auto simp: implies_intr_def returnW_def raiseW_def split: if_splits)
  from z obtain h where h: "zterm_of ztargs A = return h" "q = ZAbsp STR ''H'' h (zabshyp h 0 prf)"
    by (auto simp: zimplies_intr_proof_def bindZ_eq_returnZ)
  have "\<exists>z. zterm_of ztargs A = return z \<and> zdec z = A"
    by (rule zterm_of_zdec[OF wtpD(2)[OF wA]]) (use nA in \<open>auto simp: noneg_def tnoneg_def\<close>)
  with h(1) have hA: "zdec h = A" by auto
  have C: "aconv_zterm h t \<longleftrightarrow> aconv_term A (zdec t)" if "t \<in> zhyps prf" for t
  proof
    assume "aconv_zterm h t"
    from aconv_zterm_zdec[OF this] show "aconv_term A (zdec t)" by (simp add: hA)
  next
    assume "aconv_term A (zdec t)"
    from zterm_of_aconv[OF this h(1) hy[OF that]] show "aconv_zterm h t" .
  qed
  obtain w where w: "pcerase w = pcerase (zprf_tr prf)" "prf_valid ax H (th_tpairs th0) w (th_prop th0)"
    using p by (rule zvalidE)
  have v: "prf_valid ax {t \<in> H. \<not> aconv_term A t} (th_tpairs th0) (AbsP STR ''H'' (Some A) (abshyp A 0 w))
      (implies $ A $ th_prop th0)"
  proof (rule implies_intr_proof_valid_ann[OF w(2) wA H])
    fix \<rho> \<sigma> show "ann_ok (map_option (ap \<rho> \<sigma>) (Some A)) (ap \<rho> \<sigma> A)"
      by (simp only: option.map ann_ok_simps) (rule ueq_refl)
  qed
  have "pcerase (AbsP STR ''H'' (Some A) (abshyp A 0 w)) = pcerase (zprf_tr q)"
    by (simp add: h(2) hA zprf_tr_zabshyp[OF C] pcerase_abshyp w(1))
  from zvalidI[OF this v] show ?thesis by (simp add: th mk_rep_def mk_implies_def)
qed

end

end
