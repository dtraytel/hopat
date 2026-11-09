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

lemma prf_terms_pcerase [simp]: "prf_terms (pcerase p) = prf_terms p"
  by (induction p) simp_all

lemma pcerase_prf_abstract_over_aux:
  "pcerase (prf_abstract_over_aux v i p) = prf_abstract_over_aux v i (pcerase p)"
  by (induction p arbitrary: i) simp_all

context prf_model
begin

text \<open>
  Abstracting a tight variable agrees with abstracting its decoding if the variables of the
  same decoding are the same tight variable:
\<close>

lemma zdec_zabstract_term:
  assumes z: "z = ZVar xi Z" and c: "\<And>yi U. (yi, U) \<in> zvars t \<Longrightarrow> typ_of U = typ_of Z \<Longrightarrow> U = Z"
  shows "zdec (zabstract_term z i t) = prf_abstract_term (zdec z) i (zdec t)"
proof -
  have nA: "\<not> aconv_term (zdec z) (s $ u)" "\<not> aconv_term (zdec z) (Abs a T s)" for s u a T
    by (cases xi; simp add: z)+
  show ?thesis
    using c
  proof (induction t arbitrary: i)
    case (ZVar yi U)
    have "zdec (ZVar yi U) = zdec (ZVar xi Z) \<longleftrightarrow> yi = xi \<and> typ_of U = typ_of Z"
      by (cases yi; cases xi) auto
    with ZVar.prems show ?case by (auto simp: z)
  next
    case (ZApp t1 t2)
    have "zdec (zabstract_term z i t1) = prf_abstract_term (zdec z) i (zdec t1)"
      "zdec (zabstract_term z i t2) = prf_abstract_term (zdec z) i (zdec t2)"
      by (rule ZApp.IH(1), use ZApp.prems in auto, rule ZApp.IH(2), use ZApp.prems in auto)
    then show ?case using nA by (simp add: z)
  next
    case (ZAbs a T t)
    have "zdec (zabstract_term z (i + 1) t) = prf_abstract_term (zdec z) (i + 1) (zdec t)"
      by (rule ZAbs.IH) (use ZAbs.prems in auto)
    then show ?case using nA by (simp add: z)
  next
    case (ZOfclass T c)
    then show ?case using nA by (simp add: z Proof_Judgment.of_class_def)
  qed (auto simp: z)
qed

lemma zprf_tr_zabstract_proof:
  assumes z: "z = ZVar xi Z"
    and c: "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = typ_of Z \<longrightarrow> U = Z) (\<lambda>_. True) p"
  shows "zprf_tr (zabstract_proof z i p) = prf_abstract_over_aux (zdec z) i (zprf_tr p)"
  using c
proof (induction p arbitrary: i)
  case (ZAbsp a t q)
  have "zdec (zabstract_term z i t) = prf_abstract_term (zdec z) i (zdec t)"
    by (rule zdec_zabstract_term[OF z]) (use ZAbsp.prems in auto)
  with ZAbsp show ?case by simp
next
  case (ZAppt q t)
  have "zdec (zabstract_term z i t) = prf_abstract_term (zdec z) i (zdec t)"
    by (rule zdec_zabstract_term[OF z]) (use ZAppt.prems in auto)
  with ZAppt show ?case by simp
qed simp_all

theorem zforall_intr_rule_proof_valid:
  assumes ok: "okT (forall_intr hs (CTerm x T m) th0) th"
    and p: "zvalid ax (set hs) (th_tpairs th0) prf (th_prop th0)"
    and wt: "wt_thm (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)" and tx: "\<And>e. e \<turnstile> x : T"
    and nx: "noneg x"
    and uF: "\<And>t a U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms (zprf_tr prf) \<Longrightarrow>
      x = Free a T \<Longrightarrow> (a, U) \<in> pfrees t \<Longrightarrow> U = T"
    and uV: "\<And>t z U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms (zprf_tr prf) \<Longrightarrow>
      x = Var z T \<Longrightarrow> (z, U) \<in> vars t \<Longrightarrow> U = T"
    and cz: "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) prf"
    and z: "zforall_intr_proof ztargs T c x prf = return q"
  shows "zvalid ax (set hs) (th_tpairs th) q (th_prop th)"
proof -
  from z obtain zx where zx: "zterm_of ztargs x = return zx" "q = ZAbst c (ztyp_of T) (zabstract_proof zx 0 prf)"
    by (auto simp: zforall_intr_proof_def bindZ_eq_returnZ)
  have "\<exists>z. zterm_of ztargs x = return z \<and> zdec z = x"
    by (rule zterm_of_zdec[OF tx[of "\<lambda>_. propT"]]) (use nx in \<open>auto simp: noneg_def tnoneg_def\<close>)
  with zx(1) have dx: "zdec zx = x" by auto
  have "\<exists>a v. x = Free a T \<or> x = Var v T"
  proof (cases x)
    case (Free a U)
    with tx[of "\<lambda>_. propT"] show ?thesis by auto
  next
    case (Var v U)
    with tx[of "\<lambda>_. propT"] show ?thesis by auto
  qed (use ok in \<open>auto simp: forall_intr_def raiseW_def Let_def\<close>)
  then obtain a v where xa: "x = Free a T \<or> x = Var v T" by blast
  have tT: "typ_of (ztyp_of T) = T" using nx xa by (auto simp: noneg_def typ_of_ztyp_of_tnoneg)
  have "\<exists>xi. zx = ZVar xi (ztyp_of T)" using xa zx(1) by (auto simp: return_def)
  then obtain xi where xv: "zx = ZVar xi (ztyp_of T)" by blast
  obtain w where w: "pcerase w = pcerase (zprf_tr prf)" "prf_valid ax (set hs) (th_tpairs th0) w (th_prop th0)"
    using p by (rule zvalidE)
  have tw: "prf_terms w = prf_terms (zprf_tr prf)" using arg_cong[OF w(1), of prf_terms] by simp
  have aw: "prf_atoms w = {}" using arg_cong[OF w(1), of prf_atoms] by simp
  have v: "prf_valid ax (set hs) (th_tpairs th) (Abst c (Some T) (prf_abstract_over x w)) (th_prop th)"
    by (rule forall_intr_rule_proof_valid_ann[OF ok w(2) wt tx]) (use uF uV aw tw in auto)
  have cz': "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = typ_of (ztyp_of T) \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) prf"
    using cz by (simp only: tT)
  have "pcerase (Abst c (Some T) (prf_abstract_over x w)) = pcerase (zprf_tr q)"
    using zprf_tr_zabstract_proof[OF xv cz', of 0]
    by (simp add: zx(2) tT dx prf_abstract_over_def pcerase_prf_abstract_over_aux w(1))
  from zvalidI[OF this v] show ?thesis .
qed

end

context prf_sig
begin

subsection \<open>Tight proofs by maps of their terms and types\<close>

text \<open>A generalization of @{thm [source] map_zproof_aeq} to maps of the classic proof:\<close>

lemma map_zproof_aeq_gen:
  assumes "map_zproof ityp tf q = return m"
    and tf: "zprf_all (\<lambda>t. \<forall>t'. tf t = return t' \<longrightarrow> ap \<rho> \<sigma> (zdec t') \<approx> F (zdec t))
      (\<lambda>Z. tsubst \<rho> (typ_of (ityp Z)) = G (typ_of Z)) q"
    and tc: "\<And>T. tsubst \<rho> (f T) = G T"
    and w: "pcerase w = pcerase (zprf_tr q)"
  shows "prf_aeq (map_proof_terms F G w) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m) (pclass_map f w)))"
  using assms(1,2,4)
proof (induction q arbitrary: m w)
  case (ZAbst a T q)
  from ZAbst.prems(1) obtain m1 where m1: "map_zproof ityp tf q = return m1" and m: "m = ZAbst a (ityp T) m1"
    by (auto simp: bindZ_eq_returnZ)
  from ZAbst.prems(3) obtain w1 where w: "w = Abst a (Some (typ_of T)) w1" "pcerase w1 = pcerase (zprf_tr q)"
    by (cases w) auto
  have "prf_aeq (map_proof_terms F G w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    using ZAbst.IH[OF m1 _ w(2)] ZAbst.prems(2) by simp
  moreover have "tsubst \<rho> (typ_of (ityp T)) = G (typ_of T)" using ZAbst.prems(2) by simp
  ultimately show ?case by (simp add: m w prf_ap_def prf_aeq.Abst)
next
  case (ZAbsp a t q)
  from ZAbsp.prems(1) obtain t' m1 where t': "tf t = return t'" and m1: "map_zproof ityp tf q = return m1"
    and m: "m = ZAbsp a t' m1"
    by (auto simp: bindZ_eq_returnZ)
  from ZAbsp.prems(3) obtain w1 where w: "w = AbsP a (Some (zdec t)) w1" "pcerase w1 = pcerase (zprf_tr q)"
    by (cases w) auto
  have "prf_aeq (map_proof_terms F G w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    using ZAbsp.IH[OF m1 _ w(2)] ZAbsp.prems(2) by simp
  moreover have "ap \<rho> \<sigma> (zdec t') \<approx> F (zdec t)"
    using ZAbsp.prems(2) t' by (simp only: zprf_all.simps)
  ultimately show ?case by (simp add: m w prf_ap_def prf_aeq.AbsP ann_eq_def ueq_sym)
next
  case (ZAppt q t)
  from ZAppt.prems(1) obtain t' m1 where t': "tf t = return t'" and m1: "map_zproof ityp tf q = return m1"
    and m: "m = ZAppt m1 t'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppt.prems(3) obtain w1 where w: "w = PAppt w1 (Some (zdec t))" "pcerase w1 = pcerase (zprf_tr q)"
    by (cases w) auto
  have "prf_aeq (map_proof_terms F G w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    using ZAppt.IH[OF m1 _ w(2)] ZAppt.prems(2) by simp
  moreover have "ap \<rho> \<sigma> (zdec t') \<approx> F (zdec t)"
    using ZAppt.prems(2) t' by (simp only: zprf_all.simps)
  ultimately show ?case by (simp add: m w prf_ap_def prf_aeq.PAppt ann_eq_def ueq_sym)
next
  case (ZAppp q1 q2)
  from ZAppp.prems(1) obtain m1 m2 where m1: "map_zproof ityp tf q1 = return m1"
    and m2: "map_zproof ityp tf q2 = return m2" and m: "m = ZAppp m1 m2"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppp.prems(3) obtain w1 w2 where w: "w = PAppp w1 w2" "pcerase w1 = pcerase (zprf_tr q1)"
    "pcerase w2 = pcerase (zprf_tr q2)"
    by (cases w) auto
  have "prf_aeq (map_proof_terms F G w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    "prf_aeq (map_proof_terms F G w2) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m2) (pclass_map f w2)))"
    using ZAppp.IH(1)[OF m1 _ w(2)] ZAppp.IH(2)[OF m2 _ w(3)] ZAppp.prems(2) by simp_all
  then show ?case by (simp add: m w prf_ap_def prf_aeq.PAppp)
next
  case (OFCLASSp T c)
  from OFCLASSp.prems(3) obtain T' where w: "w = PClass T' c" by (cases w) auto
  from OFCLASSp.prems(1) have "m = OFCLASSp T c" by (simp add: return_def)
  then show ?case by (simp add: w tc prf_ap_def prf_aeq.refl)
next
  case (ZConstp c)
  from ZConstp.prems(3) have "w = MinProof" by (cases w) auto
  moreover from ZConstp.prems(1) obtain c' where "m = ZConstp c'"
    by (cases c) (auto simp: bindZ_eq_returnZ)
  ultimately show ?case by (simp add: prf_ap_def prf_aeq.refl)
qed (auto simp: return_def prf_ap_def prf_aeq.refl elim: pcerase.elims)

end

lemma zprf_all_mono: "zprf_all P Q p \<Longrightarrow> (\<And>t. P t \<Longrightarrow> P' t) \<Longrightarrow> (\<And>T. Q T \<Longrightarrow> Q' T) \<Longrightarrow> zprf_all P' Q' p"
  by (induction p) auto

context prf_sig
begin

lemma zdec_zincr_subst:
  assumes var: "var = (\<lambda>((x, j), T). if 0 \<le> j then Some (ZVar (x, j + inc) T) else None)"
    and "zterm_ok t" "0 \<le> inc"
  shows "zdec (zsubst_term (zincr_tvar inc) var t) = incr_idx [] inc lev (zdec t)"
  using assms(2)
proof (induction t arbitrary: lev)
  case (ZVar xi T)
  obtain x i where xi: "xi = (x, i)" by (cases xi)
  have T: "typ_of (zincr_tvar inc T) = incr_tvar inc (typ_of T)"
    using ZVar assms(3) by (intro typ_of_zincr_tvar) simp_all
  show ?case
  proof (cases "0 \<le> i")
    case True
    have "i + inc \<noteq> -1" using True assms(3) by (intro integer_nonneg_ne_m1 add_nonneg_nonneg)
    moreover have "i \<noteq> -1" using True by (rule integer_nonneg_ne_m1)
    ultimately show ?thesis using True T by (simp add: xi var)
  next
    case False
    with ZVar have "i = -1" by (simp add: xi)
    then show ?thesis using T by (simp add: xi var)
  qed
next
  case (ZConst1 c T)
  then have "typ_of (zincr_tvar inc T) = incr_tvar inc (typ_of T)" using assms(3) by (intro typ_of_zincr_tvar) simp_all
  then show ?case using zconst_typ_incr[of c inc "[typ_of T]"] by simp
next
  case (ZConst c Us)
  then have e: "map (\<lambda>x. typ_of (zincr_tvar inc x)) Us = map (\<lambda>x. incr_tvar inc (typ_of x)) Us"
    using assms(3) by (auto simp: map_eq_conv intro: typ_of_zincr_tvar)
  have "zconst_typ c (map typ_of (map (zincr_tvar inc) Us)) = incr_tvar inc (zconst_typ c (map typ_of Us))"
    using zconst_typ_incr[of c inc "map typ_of Us"] by (simp only: map_map comp_def e)
  then show ?case by simp
next
  case (ZAbs a T t)
  then show ?case using assms(3) by (simp add: typ_of_zincr_tvar)
next
  case (ZOfclass T c)
  then show ?case using assms(3) by (simp add: typ_of_zincr_tvar Proof_Judgment.of_class_def propT_def)
qed (simp_all add: zconst_typ_incr[of _ _ "[]", simplified])

end

context prf_model
begin

theorem zincr_indexes_proof_valid:
  assumes p: "zvalid ax H tps prf \<phi>" and z: "zincr_indexes_proof i prf = return q" and i: "0 \<le> i"
    and ok: "zprf_all zterm_ok ztyp_ok prf"
  shows "zvalid ax H (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) q (incr_indexes [] i \<phi>)"
proof -
  obtain w where w: "pcerase w = pcerase (zprf_tr prf)" "prf_valid ax H tps w \<phi>" using p by (rule zvalidE)
  define var where "var = (\<lambda>((x, j), T). if 0 \<le> j then Some (ZVar (x, j + i) T) else None)"
  have m: "map_zproof (zincr_tvar i) (\<lambda>t. return (zsubst_term (zincr_tvar i) var t)) prf = return q"
    using z by (simp add: zincr_indexes_proof_def Let_def var_def)
  let ?w = "prf_reclass (zprf_tr q) (pclass_map (incr_tvar i) w)"
  have "prf_valid ax H (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) ?w (incr_indexes [] i \<phi>)"
  proof (rule prf_valid_aeq[OF incr_indexes_proof_valid[OF w(2)]])
    fix \<rho> \<sigma>
    have "prf_aeq (map_proof_terms (\<lambda>t. ap \<rho> \<sigma> (incr_indexes [] i t)) (\<lambda>T. tsubst \<rho> (incr_tvar i T)) w)
        (prf_ap \<rho> \<sigma> ?w)"
    proof (rule map_zproof_aeq_gen[OF m _ _ w(1)])
      show "zprf_all (\<lambda>t. \<forall>t'. return (zsubst_term (zincr_tvar i) var t) = return t' \<longrightarrow>
          ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (incr_indexes [] i (zdec t)))
        (\<lambda>Z. tsubst \<rho> (typ_of (zincr_tvar i Z)) = tsubst \<rho> (incr_tvar i (typ_of Z))) prf"
      proof (rule zprf_all_mono[OF ok])
        fix t assume t: "zterm_ok t"
        have "zdec (zsubst_term (zincr_tvar i) var t) = incr_indexes [] i (zdec t)"
          using zdec_zincr_subst[OF var_def t i, of 0] by (cases "i = 0") (simp_all add: incr_indexes_def incr_idx_id)
        then show "\<forall>t'. return (zsubst_term (zincr_tvar i) var t) = return t' \<longrightarrow>
            ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (incr_indexes [] i (zdec t))"
          by (simp add: ueq_refl)
      next
        fix Z assume "ztyp_ok Z"
        then show "tsubst \<rho> (typ_of (zincr_tvar i Z)) = tsubst \<rho> (incr_tvar i (typ_of Z))"
          by (simp add: typ_of_zincr_tvar i)
      qed
    qed simp
    then show "prf_aeq (prf_ap \<rho> \<sigma> (incr_indexes_proof i w)) (prf_ap \<rho> \<sigma> ?w)"
      by (simp add: prf_ap_def incr_indexes_proof_def map_proof_terms_comp comp_def)
  qed
  then show ?thesis by (rule zvalidI[rotated]) simp
qed

end

end
