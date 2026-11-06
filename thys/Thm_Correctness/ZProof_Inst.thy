section \<open>Instantiating the visible variables of tight proofs\<close>

theory ZProof_Inst
  imports ZProof_Norm
begin

text \<open>
  The normalisation of a tight proof (\<open>ZTerm.norm_proof\<close>) instantiates the type variables and
  variables of the visible propositions by their normal forms. It does not instantiate the types
  of the proofs of class membership (\<open>OFCLASSp\<close>), which are treated like hypotheses: the
  normalised proof is correct up to these types. A proof is compared with another one up to
  the types of its class proofs by erasing them:
\<close>

fun pcerase :: "prf \<Rightarrow> prf" where
  "pcerase (Abst a T p) = Abst a T (pcerase p)"
| "pcerase (AbsP a t p) = AbsP a t (pcerase p)"
| "pcerase (PAppt p t) = PAppt (pcerase p) t"
| "pcerase (PAppp p q) = PAppp (pcerase p) (pcerase q)"
| "pcerase (PClass T c) = PClass dummyT c"
| "pcerase p = p"

text \<open>The proof \<open>a\<close> with the types of the class proofs of \<open>b\<close>:\<close>

fun prf_reclass :: "prf \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_reclass (Abst a T p) (Abst a' T' p') = Abst a T (prf_reclass p p')"
| "prf_reclass (AbsP a t p) (AbsP a' t' p') = AbsP a t (prf_reclass p p')"
| "prf_reclass (PAppt p t) (PAppt p' t') = PAppt (prf_reclass p p') t"
| "prf_reclass (PAppp p q) (PAppp p' q') = PAppp (prf_reclass p p') (prf_reclass q q')"
| "prf_reclass (PClass T c) (PClass T' c') = PClass T' c"
| "prf_reclass p p' = p"

fun pclass_map :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> prf \<Rightarrow> prf" where
  "pclass_map f (Abst a T p) = Abst a T (pclass_map f p)"
| "pclass_map f (AbsP a t p) = AbsP a t (pclass_map f p)"
| "pclass_map f (PAppt p t) = PAppt (pclass_map f p) t"
| "pclass_map f (PAppp p q) = PAppp (pclass_map f p) (pclass_map f q)"
| "pclass_map f (PClass T c) = PClass (f T) c"
| "pclass_map f p = p"

lemma pcerase_prf_reclass [simp]: "pcerase (prf_reclass a b) = pcerase a"
  by (induction a b rule: prf_reclass.induct) simp_all

lemma pcerase_pclass_map [simp]: "pcerase (pclass_map f p) = pcerase p"
  by (induction p) simp_all

lemma pcerase_prf_subst: "pcerase (prf_subst u k p) = prf_subst u k (pcerase p)"
  by (induction u k p rule: prf_subst.induct) simp_all

lemma prf_atoms_pcerase [simp]: "prf_atoms (pcerase p) = prf_atoms p"
  by (induction p) simp_all

text \<open>The variables of a tight term:\<close>

fun zvars :: "zterm \<Rightarrow> (indexname \<times> ztyp) set" where
  "zvars (ZVar x T) = {(x, T)}"
| "zvars (ZAbs a T t) = zvars t"
| "zvars (ZApp t u) = zvars t \<union> zvars u"
| "zvars _ = {}"

lemma typ_of_zsubst_type:
  assumes "\<And>v S U. f (v, S) = Some U \<Longrightarrow> snd v \<noteq> -1"
  shows "typ_of (zsubst_type f Z) = tsubst (\<lambda>v S. case f (v, S) of Some U \<Rightarrow> typ_of U | None \<Rightarrow> TVar v S) (typ_of Z)"
proof (induction Z)
  case (ZTVar v S)
  show ?case
  proof (cases "snd v = -1")
    case True
    then have "f (v, S) = None" using assms by (cases "f (v, S)") auto
    with True show ?thesis by simp
  qed (auto split: option.splits)
qed simp_all

lemma tvars_typ_of_ztyp_of: "tvars (typ_of (ztyp_of T)) \<subseteq> tvars T"
  by (induction T rule: ztyp_of.induct) (auto simp: propT_def)

context prf_sig
begin

lemma prf_ap_PClass [simp]: "prf_ap \<rho> \<sigma> (PClass T c) = PClass (tsubst \<rho> T) c"
  by (simp add: prf_ap_def)


subsection \<open>Terms\<close>

lemma ap_zsubst_term:
  assumes ty: "\<And>Z. typ_of (ityp Z) = tsubst \<iota> (typ_of Z)"
    and vn: "\<forall>(x, Z)\<in>X. snd x = -1 \<longrightarrow> look (x, ityp Z) = None"
    and vv: "\<forall>(x, Z)\<in>X. snd x \<noteq> -1 \<longrightarrow> (case look (x, ityp Z) of
        None \<Rightarrow> \<sigma> x (tsubst \<rho> (typ_of (ityp Z))) = \<sigma>' x (tsubst \<rho> (typ_of (ityp Z)))
      | Some u \<Rightarrow> ap \<rho> \<sigma> (zdec u) \<approx> \<sigma>' x (tsubst \<rho> (typ_of (ityp Z))))"
    and X: "zvars t \<subseteq> X"
  shows "ap \<rho> \<sigma> (zdec (zsubst_term ityp look t)) \<approx> ap (\<lambda>v S. tsubst \<rho> (\<iota> v S)) \<sigma>' (zdec t)"
  using X
proof (induction t)
  case (ZVar x Z)
  then have xZ: "(x, Z) \<in> X" by simp
  have tz: "tsubst (\<lambda>v S. tsubst \<rho> (\<iota> v S)) (typ_of Z) = tsubst \<rho> (typ_of (ityp Z))"
    by (simp add: ty tsubst_tsubst)
  show ?case
  proof (cases "snd x = -1")
    case True
    with vn xZ have "look (x, ityp Z) = None" by auto
    with True tz show ?thesis by (simp add: ueq_refl)
  next
    case False
    show ?thesis
    proof (cases "look (x, ityp Z)")
      case None
      with vv xZ False have "\<sigma> x (tsubst \<rho> (typ_of (ityp Z))) = \<sigma>' x (tsubst \<rho> (typ_of (ityp Z)))" by auto
      with None False tz show ?thesis by (simp add: ueq_refl)
    next
      case (Some u)
      with vv xZ False have h: "ap \<rho> \<sigma> (zdec u) \<approx> \<sigma>' x (tsubst \<rho> (typ_of (ityp Z)))" by fastforce
      have e1: "ap \<rho> \<sigma> (zdec (zsubst_term ityp look (ZVar x Z))) = ap \<rho> \<sigma> (zdec u)" using Some by simp
      have e2: "ap (\<lambda>v S. tsubst \<rho> (\<iota> v S)) \<sigma>' (zdec (ZVar x Z)) = \<sigma>' x (tsubst \<rho> (typ_of (ityp Z)))"
        using False tz by simp
      show ?thesis unfolding e1 e2 by (rule h)
    qed
  qed
next
  case (ZAbs a T t)
  have "zvars t \<subseteq> X" using ZAbs.prems by simp
  from ZAbs.IH[OF this] show ?case unfolding zsubst_term.simps zdec.simps ap_simps by (rule ueq_Abs)
next
  case (ZApp t u)
  have "zvars t \<subseteq> X" "zvars u \<subseteq> X" using ZApp.prems by simp_all
  from ZApp.IH(1)[OF this(1)] ZApp.IH(2)[OF this(2)] show ?case unfolding zsubst_term.simps zdec.simps ap_simps by (rule ueq_App)
qed (simp_all add: of_class_def ueq_refl)


subsection \<open>Proofs\<close>

lemma map_zproof_aeq:
  assumes "map_zproof ityp tf q = returnZ m"
    and tf: "zprf_all (\<lambda>t. \<forall>t'. tf t = returnZ t' \<longrightarrow> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>1 \<sigma>' (zdec t)) (\<lambda>_. True) q"
    and ty: "\<And>Z. tsubst \<rho> (typ_of (ityp Z)) = tsubst \<rho>1 (typ_of Z)"
    and tc: "\<And>T. tsubst \<rho> (f T) = tsubst \<rho>1 T"
    and w: "pcerase w = pcerase (zprf_tr q)"
  shows "prf_aeq (prf_ap \<rho>1 \<sigma>' w) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m) (pclass_map f w)))"
  using assms(1,2,5)
proof (induction q arbitrary: m w)
  case (ZAbst a T q)
  from ZAbst.prems(1) obtain m1 where m1: "map_zproof ityp tf q = returnZ m1" and m: "m = ZAbst a (ityp T) m1"
    by (auto simp: bindZ_eq_returnZ)
  from ZAbst.prems(3) obtain w1 where w: "w = Abst a (Some (typ_of T)) w1" "pcerase w1 = pcerase (zprf_tr q)"
    by (cases w) auto
  have "prf_aeq (prf_ap \<rho>1 \<sigma>' w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    using ZAbst.IH[OF m1 _ w(2)] ZAbst.prems(2) by simp
  then show ?case by (simp add: m w ty prf_aeq.Abst)
next
  case (ZAbsp a t q)
  from ZAbsp.prems(1) obtain t' m1 where t': "tf t = returnZ t'" and m1: "map_zproof ityp tf q = returnZ m1"
    and m: "m = ZAbsp a t' m1"
    by (auto simp: bindZ_eq_returnZ)
  from ZAbsp.prems(3) obtain w1 where w: "w = AbsP a (Some (zdec t)) w1" "pcerase w1 = pcerase (zprf_tr q)"
    by (cases w) auto
  have "prf_aeq (prf_ap \<rho>1 \<sigma>' w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    using ZAbsp.IH[OF m1 _ w(2)] ZAbsp.prems(2) by simp
  moreover have "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>1 \<sigma>' (zdec t)"
    using ZAbsp.prems(2) t' by (simp only: zprf_all.simps)
  ultimately show ?case by (simp add: m w prf_aeq.AbsP ann_eq_def ueq_sym)
next
  case (ZAppt q t)
  from ZAppt.prems(1) obtain t' m1 where t': "tf t = returnZ t'" and m1: "map_zproof ityp tf q = returnZ m1"
    and m: "m = ZAppt m1 t'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppt.prems(3) obtain w1 where w: "w = PAppt w1 (Some (zdec t))" "pcerase w1 = pcerase (zprf_tr q)"
    by (cases w) auto
  have "prf_aeq (prf_ap \<rho>1 \<sigma>' w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    using ZAppt.IH[OF m1 _ w(2)] ZAppt.prems(2) by simp
  moreover have "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>1 \<sigma>' (zdec t)"
    using ZAppt.prems(2) t' by (simp only: zprf_all.simps)
  ultimately show ?case by (simp add: m w prf_aeq.PAppt ann_eq_def ueq_sym)
next
  case (ZAppp q1 q2)
  from ZAppp.prems(1) obtain m1 m2 where m1: "map_zproof ityp tf q1 = returnZ m1"
    and m2: "map_zproof ityp tf q2 = returnZ m2" and m: "m = ZAppp m1 m2"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppp.prems(3) obtain w1 w2 where w: "w = PAppp w1 w2" "pcerase w1 = pcerase (zprf_tr q1)"
    "pcerase w2 = pcerase (zprf_tr q2)"
    by (cases w) auto
  have "prf_aeq (prf_ap \<rho>1 \<sigma>' w1) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m1) (pclass_map f w1)))"
    "prf_aeq (prf_ap \<rho>1 \<sigma>' w2) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr m2) (pclass_map f w2)))"
    using ZAppp.IH(1)[OF m1 _ w(2)] ZAppp.IH(2)[OF m2 _ w(3)] ZAppp.prems(2) by simp_all
  then show ?case by (simp add: m w prf_aeq.PAppp)
next
  case (OFCLASSp T c)
  from OFCLASSp.prems(3) obtain T' where w: "w = PClass T' c" by (cases w) auto
  from OFCLASSp.prems(1) have "m = OFCLASSp T c" by (simp add: returnZ_def)
  then show ?case by (simp add: w tc prf_aeq.refl)
next
  case (ZConstp c)
  from ZConstp.prems(3) have "w = MinProof" by (cases w) auto
  moreover from ZConstp.prems(1) obtain c' where "m = ZConstp c'"
    by (cases c) (auto simp: bindZ_eq_returnZ)
  ultimately show ?case by (simp add: prf_aeq.refl)
qed (auto simp: returnZ_def prf_aeq.refl elim: pcerase.elims)

end

end
