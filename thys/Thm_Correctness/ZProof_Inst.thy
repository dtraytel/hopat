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

subsection \<open>Contraction of proof redexes\<close>

lemma prf_atoms_prf_ap_empty: "prf_atoms p = {} \<Longrightarrow> prf_atoms (prf_ap \<rho> \<sigma> p) = {}"
  by (induction p) (simp_all add: prf_ap_def)

lemma prf_atoms_zprf_tr [simp]: "prf_atoms (zprf_tr p) = {}"
  by (induction p) simp_all

text \<open>
  The contraction of the proof redexes of a tight proof preserves the correctness of every proof
  that agrees with it up to the types of its class proofs:
\<close>

abbreviation prf_transfer :: "(pterm \<Rightarrow> bool) \<Rightarrow> pterm set \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> bool" where
  "prf_transfer ax H w w' \<equiv> \<forall>\<rho> \<sigma> e Hs \<phi>. gsubst \<sigma> \<longrightarrow>
    prf_ok ax H e Hs (prf_ap \<rho> \<sigma> w) \<phi> \<longrightarrow> prf_ok ax H e Hs (prf_ap \<rho> \<sigma> w') \<phi>"

theorem beta_norm_prooft_wit:
  assumes "beta_norm_prooft p = Some p'" and H: "\<forall>h\<in>H. closed h"
  shows "pcerase w = pcerase (zprf_tr p) \<Longrightarrow> \<exists>w'. pcerase w' = pcerase (zprf_tr p') \<and> prf_transfer ax H w w'"
  using assms(1)
proof (induction p p' arbitrary: w rule: beta_norm_prooft.raw_induct[rotated, consumes 1])
  case (1 bn p p')
  note h = "1.hyps" and IH = "1.IH" and wp = "1.prems"
  have redex: "\<exists>w'. pcerase w' = pcerase (zprf_tr p') \<and> prf_transfer ax H (PAppt (Abst a T' wb) (Some (zdec u))) w'"
    if wb: "pcerase wb = pcerase (zprf_tr body)" and b: "bn (subst_proof_bound u body) = Some p'" for a T' wb body u
  proof -
    let ?ws = "prf_subst (zdec u) 0 wb"
    have "pcerase ?ws = pcerase (zprf_tr (subst_proof_bound u body))"
      by (simp add: pcerase_prf_subst wb zprf_tr_subst_proof_bound)
    from IH[OF b this] obtain w' where w': "pcerase w' = pcerase (zprf_tr p')" "prf_transfer ax H ?ws w'" by blast
    have at: "prf_atoms wb = {}" using arg_cong[OF wb, of prf_atoms] by simp
    have "prf_transfer ax H (PAppt (Abst a T' wb) (Some (zdec u))) ?ws"
    proof (intro allI impI)
      fix \<rho> \<sigma> e Hs \<phi> assume gs: "gsubst \<sigma>"
        and ok: "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> (PAppt (Abst a T' wb) (Some (zdec u)))) \<phi>"
      from prf_ok_beta[OF ok[simplified] H prf_atoms_prf_ap_empty[OF at]]
      show "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> ?ws) \<phi>" by (simp add: prf_ap_prf_subst[OF gs])
    qed
    with w' show ?thesis by blast
  qed
  show ?case
  proof (cases p)
    case (ZAbst a T q)
    with h obtain q' where q': "bn q = Some q'" and p': "p' = ZAbst a T q'" by (auto simp: bind_eq_Some_conv)
    from wp ZAbst obtain w1 where w: "w = Abst a (Some (typ_of T)) w1" "pcerase w1 = pcerase (zprf_tr q)"
      by (cases w) auto
    from IH[OF q' w(2)] obtain w1' where w1': "pcerase w1' = pcerase (zprf_tr q')" "prf_transfer ax H w1 w1'"
      by blast
    have "prf_transfer ax H w (Abst a (Some (typ_of T)) w1')"
    proof (intro allI impI)
      fix \<rho> \<sigma> e Hs \<phi> assume gs: "gsubst \<sigma>" and ok: "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> w) \<phi>"
      have ok': "prf_ok ax H e Hs (Abst a (Some (tsubst \<rho> (typ_of T))) (prf_ap \<rho> \<sigma> w1)) \<phi>" using ok w by simp
      from prf_ok_Abst_inv[OF ok' HOL.refl]
      obtain U b B where A: "tann_ok (Some (tsubst \<rho> (typ_of T))) U" "cert_typ alg ar U"
        "prf_ok ax H (e\<langle>0:U\<rangle>) (map (incr_bv 1 0) Hs) (prf_ap \<rho> \<sigma> w1) B"
        "all_const U $ Abs b U B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi>"
        by blast
      have "prf_ok ax H (e\<langle>0:U\<rangle>) (map (incr_bv 1 0) Hs) (prf_ap \<rho> \<sigma> w1') B" using w1'(2) gs A(3) by blast
      from prf_ok.conv[OF prf_ok.Abst[OF A(1,2) this] A(4) prf_ok_typing[OF ok]]
      show "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> (Abst a (Some (typ_of T)) w1')) \<phi>" by simp
    qed
    with w1'(1) show ?thesis by (intro exI[of _ "Abst a (Some (typ_of T)) w1'"]) (simp add: p')
  next
    case (ZAppt f u)
    from wp ZAppt obtain wf where w: "w = PAppt wf (Some (zdec u))" "pcerase wf = pcerase (zprf_tr f)"
      by (cases w) auto
    have appt: "prf_transfer ax H w (PAppt wf' (Some (zdec u')))"
      if tr: "prf_transfer ax H wf wf'" and uu: "\<And>\<rho> \<sigma>. gsubst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> (zdec u') \<approx> ap \<rho> \<sigma> (zdec u)"
      for wf' u'
    proof (intro allI impI)
      fix \<rho> \<sigma> e Hs \<phi> assume gs: "gsubst \<sigma>" and ok: "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> w) \<phi>"
      have ok': "prf_ok ax H e Hs (PAppt (prf_ap \<rho> \<sigma> wf) (Some (ap \<rho> \<sigma> (zdec u)))) \<phi>" using ok w by simp
      from prf_ok_PAppt_inv[OF ok' HOL.refl]
      obtain U g t where P: "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> wf) (all_const U $ g)" "e \<turnstile> t : U"
        "ann_ok (Some (ap \<rho> \<sigma> (zdec u))) t" "g $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi>"
        by blast
      have Pf: "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> wf') (all_const U $ g)" using tr gs P(1) by blast
      have "ap \<rho> \<sigma> (zdec u) \<approx> t" using P(3) by (simp add: ann_ok_def)
      with uu[OF gs] have "ann_ok (Some (ap \<rho> \<sigma> (zdec u'))) t" unfolding ann_ok_def option.case by (rule ueq_trans)
      from prf_ok.conv[OF prf_ok.PAppt[OF Pf P(2) this] P(4) prf_ok_typing[OF ok]]
      show "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> (PAppt wf' (Some (zdec u')))) \<phi>" by simp
    qed
    have trans: "prf_transfer ax H x z" if "prf_transfer ax H x y" "prf_transfer ax H y z" for x y z
      using that by blast
    show ?thesis
    proof (cases "\<exists>a T body. f = ZAbst a T body")
      case True
      then obtain a T body where f: "f = ZAbst a T body" by blast
      from w(2) f obtain wb where wf: "wf = Abst a (Some (typ_of T)) wb" "pcerase wb = pcerase (zprf_tr body)"
        by (cases wf) auto
      have "bn (subst_proof_bound u body) = Some p'" using h ZAppt f by simp
      from redex[OF wf(2) this, of a "Some (typ_of T)"] show ?thesis by (simp only: w wf)
    next
      case False
      with h ZAppt obtain nf where hf: "bn f = Some nf"
        and rest: "(case nf of ZAbst _ _ body \<Rightarrow> bn (subst_proof_bound u body)
          | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZAppt nf nu))) = Some p'"
        by (cases f) (auto simp: bind_eq_Some_conv)
      from IH[OF hf w(2)] obtain wf' where wf': "pcerase wf' = pcerase (zprf_tr nf)" "prf_transfer ax H wf wf'"
        by blast
      show ?thesis
      proof (cases "\<exists>a T body. nf = ZAbst a T body")
        case True
        then obtain a T body where nfb: "nf = ZAbst a T body" by blast
        from wf'(1) nfb obtain wb where wb: "wf' = Abst a (Some (typ_of T)) wb" "pcerase wb = pcerase (zprf_tr body)"
          by (cases wf') auto
        have "bn (subst_proof_bound u body) = Some p'" using rest nfb by simp
        from redex[OF wb(2) this] obtain w' where w': "pcerase w' = pcerase (zprf_tr p')"
          "prf_transfer ax H (PAppt (Abst a (Some (typ_of T)) wb) (Some (zdec u))) w'" by blast
        have "prf_transfer ax H w (PAppt wf' (Some (zdec u)))" by (rule appt[OF wf'(2)]) (simp add: ueq_refl)
        with w' wb show ?thesis by (blast intro: trans)
      next
        case False
        with rest obtain nu where nu: "beta_norm_term u = Some nu" and p': "p' = ZAppt nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        have "prf_transfer ax H w (PAppt wf' (Some (zdec nu)))"
          by (rule appt[OF wf'(2)]) (rule beta_norm_term_ok[OF nu])
        with wf'(1) show ?thesis by (intro exI[of _ "PAppt wf' (Some (zdec nu))"]) (simp add: p')
      qed
    qed
  qed (use h wp in \<open>auto\<close>)
qed

end


subsection \<open>Normalisation\<close>

lemma set_zdedup_vars [simp]: "set (zdedup_vars xs) = set xs"
  by (induction xs rule: zdedup_vars.induct) auto

lemma zlookup_var_zip_Some:
  "list_all2 R vs us \<Longrightarrow> zlookup_var (zip vs us) v = Some u \<Longrightarrow> v \<in> set vs \<and> R v u"
  by (induction vs us rule: list_all2_induct) (auto split: if_splits)

lemma zlookup_var_zip_None:
  "list_all2 R vs us \<Longrightarrow> zlookup_var (zip vs us) v = None \<Longrightarrow> v \<notin> set vs"
  by (induction vs us rule: list_all2_induct) (auto split: if_splits)

lemma map_of_zip_Some: "list_all2 R xs ys \<Longrightarrow> map_of (zip xs ys) x = Some y \<Longrightarrow> R x y"
  by (induction xs ys rule: list_all2_induct) (auto split: if_splits)

lemma map_of_zip_None: "list_all2 R xs ys \<Longrightarrow> x \<notin> set xs \<Longrightarrow> map_of (zip xs ys) x = None"
  by (induction xs ys rule: list_all2_induct) auto

lemma term_vars_types: "(x, T) \<in> set (term_vars t) \<Longrightarrow> T \<in> set (term_types t)"
  by (induction t) auto

lemma zprf_all_mono:
  "zprf_all P Q p \<Longrightarrow> (\<And>t. P t \<Longrightarrow> P' t) \<Longrightarrow> (\<And>T. Q T \<Longrightarrow> Q' T) \<Longrightarrow> zprf_all P' Q' p"
  by (induction p) auto

context prf_sig
begin

text \<open>
  The normalisation of a tight proof \<open>q\<close> that agrees with \<open>w\<close> up to the types of class proofs.
  The variables of \<open>q\<close> are visible or not bound by the environment; the instance of \<open>w\<close> where the
  visible type variables are instantiated as by the extension \<open>\<rho>'\<close>, and the variables as by
  \<open>\<sigma>'\<close>, is transferred to the instance of the normalised proof by \<open>\<rho>\<close> and \<open>\<sigma>\<close>.
\<close>

theorem znorm_proof_ok:
  assumes nz: "znorm_proof ta env vis q = returnZ r" and vis: "vis \<noteq> []"
    and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and en: "eneg env"
    and vv: "\<forall>(x, T)\<in>set (visible_vars vis). snd x \<noteq> -1"
    and vt: "\<forall>(v, S)\<in>set (visible_tvars vis). snd v \<noteq> -1"
    and hid: "zprf_all (\<lambda>t. \<forall>(x, Z)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
      (x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set (visible_vars vis) \<or> vt_lookup (tenv env) x = None) (\<lambda>_. True) q"
    and w: "pcerase w = pcerase (zprf_tr q)" and H: "\<forall>h\<in>H. closed h"
  shows "\<exists>w'. pcerase w' = pcerase (zprf_tr r) \<and> (\<forall>\<rho> \<sigma> \<rho>' \<sigma>' e Hs \<phi>. iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> gsubst \<sigma> \<longrightarrow>
    prf_ok ax H e Hs (prf_ap (\<lambda>v S. if (v, S) \<in> set (visible_tvars vis) then \<rho>' v S else \<rho> v S) \<sigma>' w) \<phi> \<longrightarrow>
    prf_ok ax H e Hs (prf_ap \<rho> \<sigma> w') \<phi>)"
proof (cases "env_is_empty env")
  case True
  with nz vis have bn: "beta_norm_prooft q = Some r" by (simp add: znorm_proof_def liftOZ_eq_returnZ)
  from beta_norm_prooft_wit[OF bn H w] obtain w' where w': "pcerase w' = pcerase (zprf_tr r)"
    "prf_transfer ax H w w'" by blast
  have l: "vt_lookup (tyenv env) v = None" "vt_lookup (tenv env) x = None" for v x
    using True by (simp_all add: env_is_empty_def vt_is_empty_lookup)
  have "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> w') \<phi>"
    if ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and gs: "gsubst \<sigma>"
      and ok: "prf_ok ax H e Hs (prf_ap (\<lambda>v S. if (v, S) \<in> set (visible_tvars vis) then \<rho>' v S else \<rho> v S) \<sigma>' w) \<phi>"
    for \<rho> \<sigma> \<rho>' \<sigma>' e Hs \<phi>
  proof -
    have "(\<lambda>v S. if (v, S) \<in> set (visible_tvars vis) then \<rho>' v S else \<rho> v S) = \<rho>" "\<sigma>' = \<sigma>"
      by (intro ext; simp add: iextD(6,7)[OF ie] l)+
    with ok w'(2) gs show ?thesis by simp
  qed
  with w'(1) show ?thesis by blast
next
  case False
  let ?\<theta> = "tyenv env" and ?VT = "visible_tvars vis" and ?VV = "visible_vars vis"
  define ityp where "ityp instT = (case instT of None \<Rightarrow> id
    | Some xs \<Rightarrow> if List.null xs then id else zsubst_type (map_of xs))" for instT :: "((indexname \<times> psort) \<times> ztyp) list option"
  obtain instT us m where
    iT: "(if vt_is_empty ?\<theta> then returnZ None
      else bindZ (mapZ (\<lambda>(v, S). znorm_type ?\<theta> (ZTVar v S)) ?VT) (\<lambda>Us. returnZ (Some (zip ?VT Us)))) = returnZ instT"
    and us: "mapZ (\<lambda>(a, T). znorm_term ta env (ZVar a T))
      (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) = returnZ us"
    and m: "map_zproof (ityp instT) (\<lambda>t. liftOZ (beta_norm_term (zsubst_term (ityp instT)
      (zlookup_var (zip (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) us)) t))) q = returnZ m"
    and bn: "beta_norm_prooft m = Some r"
    using nz False vis unfolding znorm_proof_def Let_def ityp_def
    by (auto simp: bindZ_eq_returnZ liftOZ_eq_returnZ)
  define vs where "vs = zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)"
  define look where "look = zlookup_var (zip vs us)"
  define \<iota> where "\<iota> v S = (case instT of None \<Rightarrow> TVar v S
    | Some xs \<Rightarrow> (case map_of xs (v, S) of Some U \<Rightarrow> typ_of U | None \<Rightarrow> TVar v S))" for v S
  have us': "list_all2 (\<lambda>(a, T) u. znorm_term ta env (ZVar a T) = returnZ u) vs us"
    using us unfolding vs_def mapZ_eq_returnZ by (simp add: list_all2_conv_all_nth split_def)
  text \<open>The instantiation of the visible type variables.\<close>
  have iT': "instT = None \<and> vt_is_empty ?\<theta> \<or> (\<exists>Us. instT = Some (zip ?VT Us) \<and> \<not> vt_is_empty ?\<theta> \<and>
      list_all2 (\<lambda>x U. znorm_type ?\<theta> (ZTVar (fst x) (snd x)) = returnZ U) ?VT Us)"
  proof (cases "vt_is_empty ?\<theta>")
    case True
    with iT show ?thesis by (simp add: returnZ_inj)
  next
    case False
    with iT obtain Us where "mapZ (\<lambda>(v, S). znorm_type ?\<theta> (ZTVar v S)) ?VT = returnZ Us"
      "instT = Some (zip ?VT Us)"
      by (auto simp: bindZ_eq_returnZ returnZ_inj)
    with False show ?thesis by (auto simp: mapZ_eq_returnZ split_def)
  qed
  have ty: "typ_of (ityp instT Z) = tsubst \<iota> (typ_of Z)" for Z
    using iT'
  proof (elim disjE exE conjE)
    assume i: "instT = None"
    have "\<iota> = TVar" by (intro ext) (simp add: \<iota>_def i)
    then show ?thesis by (simp add: ityp_def i)
  next
    fix Us assume i: "instT = Some (zip ?VT Us)"
    have k: "map_of (zip ?VT Us) (v, S) = Some U \<Longrightarrow> snd v \<noteq> -1" for v S U
      using map_of_SomeD[of "zip ?VT Us"] vt by (fastforce dest: set_zip_leftD)
    have ie: "\<iota> = (\<lambda>v S. case map_of (zip ?VT Us) (v, S) of Some U \<Rightarrow> typ_of U | None \<Rightarrow> TVar v S)"
      by (intro ext) (simp add: \<iota>_def i)
    show ?thesis
    proof (cases "List.null (zip ?VT Us)")
      case True
      then have "map_of (zip ?VT Us) = Map.empty" by (cases "zip ?VT Us") simp_all
      then have "\<iota> = TVar" by (intro ext) (simp only: ie option.simps)
      with True show ?thesis by (simp add: ityp_def i)
    next
      case False
      have "typ_of (zsubst_type (map_of (zip ?VT Us)) Z) =
          tsubst (\<lambda>v S. case map_of (zip ?VT Us) (v, S) of Some U \<Rightarrow> typ_of U | None \<Rightarrow> TVar v S) (typ_of Z)"
        by (rule typ_of_zsubst_type) (rule k)
      with False show ?thesis by (simp add: ityp_def i ie)
    qed
  qed
  have \<iota>_out: "\<iota> v S = TVar v S" if "(v, S) \<notin> set ?VT" for v S
    using iT' that by (auto simp: \<iota>_def map_of_zip_None[of _ ?VT] split: option.splits)
  have \<iota>_in: "tcons ?\<theta> (TVar v S) \<and> \<iota> v S = tnorm ?\<theta> (TVar v S)" if "(v, S) \<in> set ?VT" "\<not> vt_is_empty ?\<theta>" for v S
  proof -
    from iT' that(2) obtain Us where i: "instT = Some (zip ?VT Us)"
      and l: "list_all2 (\<lambda>x U. znorm_type ?\<theta> (ZTVar (fst x) (snd x)) = returnZ U) ?VT Us" by blast
    have "length ?VT = length Us" using list_all2_lengthD[OF l] .
    note vin = that(1)
    then obtain U where U: "map_of (zip ?VT Us) (v, S) = Some U"
      using vin map_of_zip_is_None[OF \<open>length ?VT = length Us\<close>, of "(v, S)"]
      by (cases "map_of (zip ?VT Us) (v, S)") auto
    have "znorm_type ?\<theta> (ZTVar v S) = returnZ U" using map_of_zip_Some[OF l U] by simp
    from znorm_type_success[OF this tac(1) enegD(1)[OF en]] that(1) vt
    show ?thesis by (auto simp: \<iota>_def i U)
  qed
  have \<iota>_unb: "vt_lookup ?\<theta> w = None" if "(v, S) \<in> set ?VT" "(w, S') \<in> tvars (\<iota> v S)" for v S w S'
  proof (cases "vt_is_empty ?\<theta>")
    case True then show ?thesis by (simp add: vt_is_empty_lookup)
  next
    case False
    with \<iota>_in[OF that(1)] that(2) tnorm_unbound[OF tac(1)] show ?thesis by metis
  qed
  have \<iota>_inst: "tsubst \<rho> (\<iota> v S) = (if (v, S) \<in> set ?VT then \<rho>' v S else \<rho> v S)"
    if ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" for \<rho> \<sigma> \<rho>' \<sigma>' v S
  proof (cases "(v, S) \<in> set ?VT")
    case True
    show ?thesis
    proof (cases "vt_is_empty ?\<theta>")
      case True
      then have "instT = None" using iT by (simp add: returnZ_def)
      with True \<open>(v, S) \<in> set ?VT\<close> show ?thesis
        by (simp add: \<iota>_def iextD(6)[OF ie] vt_is_empty_lookup)
    next
      case False
      with \<iota>_in[OF \<open>(v, S) \<in> set ?VT\<close>] iext_tnorm[OF ie tac] True show ?thesis by simp
    qed
  qed (simp add: \<iota>_out)
  text \<open>The variables of the visible propositions and their instances.\<close>
  have vsI: "(x, ityp instT Z) \<in> set vs" if "(x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set ?VV" for x Z
    using that by (force simp: vs_def)
  have vsD: "\<exists>T0. (x, T0) \<in> set ?VV \<and> Z' = ityp instT (ztyp_of T0)" if "(x, Z') \<in> set vs" for x Z'
    using that by (auto simp: vs_def)
  have VT: "tvars T0 \<subseteq> set ?VT" if "(x, T0) \<in> set ?VV" for x T0
    using that term_vars_types by (fastforce simp: visible_vars_def visible_tvars_def)
  text \<open>The witness of the instantiated proof.\<close>
  define wm where "wm = prf_reclass (zprf_tr m) (pclass_map (tsubst \<iota>) w)"
  from beta_norm_prooft_wit[OF bn H, where w=wm and ax=ax] obtain w' where w': "pcerase w' = pcerase (zprf_tr r)"
    "prf_transfer ax H wm w'" by (auto simp: wm_def)
  have "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> w') \<phi>"
    if ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and gs: "gsubst \<sigma>"
      and ok: "prf_ok ax H e Hs (prf_ap (\<lambda>v S. if (v, S) \<in> set ?VT then \<rho>' v S else \<rho> v S) \<sigma>' w) \<phi>"
    for \<rho> \<sigma> \<rho>' \<sigma>' e Hs \<phi>
  proof -
    note i = iextD[OF ie]
    define \<rho>1 where "\<rho>1 = (\<lambda>v S. tsubst \<rho> (\<iota> v S))"
    have r1: "\<rho>1 = (\<lambda>v S. if (v, S) \<in> set ?VT then \<rho>' v S else \<rho> v S)"
      by (intro ext) (simp add: \<rho>1_def \<iota>_inst[OF ie])
    have tz: "tsubst \<rho> (typ_of (ityp instT Z)) = tsubst \<rho>1 (typ_of Z)" for Z
      by (simp add: ty tsubst_tsubst \<rho>1_def)
    have tc: "tsubst \<rho> (tsubst \<iota> T) = tsubst \<rho>1 T" for T
      by (simp add: tsubst_tsubst \<rho>1_def)
    have tf: "zprf_all (\<lambda>t. \<forall>t'. liftOZ (beta_norm_term (zsubst_term (ityp instT) look t)) = returnZ t' \<longrightarrow>
        ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>1 \<sigma>' (zdec t)) (\<lambda>_. True) q"
    proof (rule zprf_all_mono[OF hid], intro allI impI)
      fix t t'
      assume ht: "\<forall>(x, Z)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
        (x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set ?VV \<or> vt_lookup (tenv env) x = None"
        and t': "liftOZ (beta_norm_term (zsubst_term (ityp instT) look t)) = returnZ t'"
      have b: "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (zdec (zsubst_term (ityp instT) look t))"
        using beta_norm_term_ok[OF t'[unfolded liftOZ_eq_returnZ] gs] .
      have "ap \<rho> \<sigma> (zdec (zsubst_term (ityp instT) look t)) \<approx> ap \<rho>1 \<sigma>' (zdec t)"
        unfolding \<rho>1_def
      proof (rule ap_zsubst_term[OF ty _ _ order_refl])
        have "look (x, ityp instT Z) = None" if "snd x = -1" for x :: indexname and Z
        proof -
          have "(x, ityp instT Z) \<notin> set vs" using that vsD vv by fastforce
          then show "look (x, ityp instT Z) = None"
            unfolding look_def by (meson option.exhaust zlookup_var_zip_Some[OF us'])
        qed
        then show "\<forall>(x, Z)\<in>zvars t. snd x = -1 \<longrightarrow> look (x, ityp instT Z) = None" by blast
        show "\<forall>(x, Z)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (case look (x, ityp instT Z) of
            None \<Rightarrow> \<sigma> x (tsubst \<rho> (typ_of (ityp instT Z))) = \<sigma>' x (tsubst \<rho> (typ_of (ityp instT Z)))
          | Some u \<Rightarrow> ap \<rho> \<sigma> (zdec u) \<approx> \<sigma>' x (tsubst \<rho> (typ_of (ityp instT Z))))"
        proof -
          have "case look (x, ityp instT Z) of
              None \<Rightarrow> \<sigma> x (tsubst \<rho> (typ_of (ityp instT Z))) = \<sigma>' x (tsubst \<rho> (typ_of (ityp instT Z)))
            | Some u \<Rightarrow> ap \<rho> \<sigma> (zdec u) \<approx> \<sigma>' x (tsubst \<rho> (typ_of (ityp instT Z)))"
            if xZ: "(x, Z) \<in> zvars t" and x: "snd x \<noteq> -1" for x :: indexname and Z
          proof (cases "look (x, ityp instT Z)")
            case None
            then have "(x, ityp instT Z) \<notin> set vs" unfolding look_def by (rule zlookup_var_zip_None[OF us'])
            then have "vt_lookup (tenv env) x = None" using ht xZ x vsI by blast
            with None show ?thesis by (simp add: i(7))
          next
            case (Some u)
            from zlookup_var_zip_Some[OF us' Some[unfolded look_def]]
            have inv: "(x, ityp instT Z) \<in> set vs" and nu: "znorm_term ta env (ZVar x (ityp instT Z)) = returnZ u"
              by auto
            from vsD[OF inv] obtain T0 where T0: "(x, T0) \<in> set ?VV" "ityp instT Z = ityp instT (ztyp_of T0)" by blast
            have "tsubst \<rho>' (typ_of (ityp instT Z)) = tsubst \<rho> (typ_of (ityp instT Z))"
            proof (rule tsubst_cong)
              fix v S assume "(v, S) \<in> tvars (typ_of (ityp instT Z))"
              then obtain v0 S0 where "(v0, S0) \<in> tvars (typ_of (ztyp_of T0))" "(v, S) \<in> tvars (\<iota> v0 S0)"
                by (auto simp: T0(2) ty tvars_tsubst)
              moreover have "(v0, S0) \<in> set ?VT" using calculation(1) tvars_typ_of_ztyp_of VT[OF T0(1)] by blast
              ultimately have "vt_lookup ?\<theta> v = None" by (blast intro: \<iota>_unb)
              then show "\<rho>' v S = \<rho> v S" by (rule i(6))
            qed
            moreover have "ap \<rho> \<sigma> (zdec u) \<approx> ap \<rho>' \<sigma>' (zdec (ZVar x (ityp instT Z)))"
              using conjunct2[OF znorm_term_ok[OF nu ie tac en]] .
            ultimately show ?thesis using Some x by simp
          qed
          then show ?thesis by blast
        qed
      qed
      from ueq_trans[OF b this] show "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>1 \<sigma>' (zdec t)" .
    qed simp
    have "prf_aeq (prf_ap \<rho>1 \<sigma>' w) (prf_ap \<rho> \<sigma> wm)"
      unfolding wm_def by (rule map_zproof_aeq[OF m[folded vs_def look_def] tf tz tc w])
    from w'(2) gs prf_ok_aeq[OF ok[folded r1] this] show ?thesis by blast
  qed
  with w'(1) show ?thesis by blast
qed

end

end
