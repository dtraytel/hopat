section \<open>Validity of the proofs of the inference rules\<close>

theory Rule_Proofs
  imports Varify_Correct Equality_Correct Assumption_Correct Eta_Long_Correct
begin

lemma map_proof_terms_abshyp:
  "map_proof_terms f g (abshyp h i p) = abshyp h i (map_proof_terms f g p)"
proof (induction p arbitrary: i)
  case (PThm x)
  then show ?case by (cases x) simp
qed simp_all

lemma vars_unname [simp]: "vars (unname t) = vars t"
  by (induction t) auto

lemma ttvars_unname [simp]: "ttvars (unname t) = ttvars t"
  by (induction t) auto

context prf_sig
begin

subsection \<open>Introduction and elimination of implications\<close>

lemma prf_ok_abshyp:
  assumes "prf_ok ax H e Hs p \<phi>" and h': "closed h'" "\<And>e. e \<turnstile> h' : propT"
    and c: "\<And>t. t \<in> H \<Longrightarrow> aconv_term h t \<Longrightarrow> h' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "prf_ok ax {t \<in> H. \<not> aconv_term h t} e (Hs @ [h']) (abshyp h (ilength Hs) p) \<phi>"
  using assms(1)
proof (induction rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  then show ?case by (blast intro: prf_ok.conv)
next
  case (PBound i Hs e)
  then show ?case using prf_ok.PBound[of i "Hs @ [h']"] by (simp add: nth_append)
next
  case (AbsP e A t Hs p B a)
  then show ?case by (simp add: prf_ok.AbsP ilength_eq integer_of_nat_Suc)
next
  case (Abst T U e Hs p B a b)
  have "incr_bv 1 0 h' = h'" using h'(1) by (simp add: closed_def incr_bv_closed)
  with Abst show ?case by (simp add: prf_ok.Abst ilength_eq)
next
  case (Hyp t e Hs)
  show ?case
  proof (cases "aconv_term h t")
    case True
    have "prf_ok ax {t \<in> H. \<not> aconv_term h t} e (Hs @ [h']) (PBound (ilength Hs)) h'"
      using prf_ok.PBound[of "ilength Hs" "Hs @ [h']" e] h'(2)
      by (simp add: ilength_eq nth_append integer_of_nat_ge0)
    from prf_ok.conv[OF this c[OF Hyp(1) True] Hyp(2)] True show ?thesis by simp
  next
    case False
    with Hyp show ?thesis by (simp add: prf_ok.Hyp)
  qed
qed (auto intro: prf_ok.intros)

theorem trivial_proof_valid:
  assumes "wtp A"
  shows "prf_valid ax H [] trivial_proof (implies $ A $ A)"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  have t: "e \<turnstile> ap \<rho> \<sigma> A : propT" by (rule typing_ap_wtp[OF assms \<rho> \<sigma>])
  have "prf_ok ax H e [ap \<rho> \<sigma> A] (PBound 0) (ap \<rho> \<sigma> A)"
    using prf_ok.PBound[of 0 "[ap \<rho> \<sigma> A]" e] t by simp
  then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> trivial_proof) (ap \<rho> \<sigma> (implies $ A $ A))"
    using t by (simp add: trivial_proof_def prf_ap_def ap_def[symmetric] prf_ok.AbsP)
qed

theorem implies_intr_proof_valid:
  assumes p: "prf_valid ax H tps prf B" and wh: "wtp h"
    and H: "\<And>t. t \<in> H \<Longrightarrow> vars t = {} \<and> ttvars t = {}"
  shows "prf_valid ax {t \<in> H. \<not> aconv_term h t} tps (implies_intr_proof h prf) (implies $ h $ B)"
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
  then show "prf_ok ax {t \<in> H. \<not> aconv_term h t} e [] (prf_ap \<rho> \<sigma> (implies_intr_proof h prf))
      (ap \<rho> \<sigma> (implies $ h $ B))"
    using th by (simp add: implies_intr_proof_def prf_ap_def map_proof_terms_abshyp ap_def[symmetric]
      prf_ok.AbsP)
qed

theorem implies_elim_proof_valid:
  assumes p: "prf_valid ax H tps p (implies $ A $ B)" and q: "prf_valid ax H tps' q A"
  shows "prf_valid ax H (tps @ tps') (PAppp p q) B"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (tps @ tps') \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> p) (ap \<rho> \<sigma> (implies $ A $ B))"
    by (rule prf_validD[OF p \<rho> \<sigma>]) (use sol in auto)
  moreover have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> q) (ap \<rho> \<sigma> A)"
    by (rule prf_validD[OF q \<rho> \<sigma>]) (use sol in auto)
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (PAppp p q)) (ap \<rho> \<sigma> B)"
    by (simp add: prf_ap_def ap_def[symmetric] prf_ok.PAppp)
qed

lemma prf_ok_mono: "prf_ok ax H e Hs p \<phi> \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> prf_ok ax H' e Hs p \<phi>"
  by (induction rule: prf_ok.induct) (auto intro: prf_ok.intros)

lemma prf_valid_mono: "prf_valid ax H tps p \<phi> \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> prf_valid ax H' tps p \<phi>"
  unfolding prf_valid_def by (blast intro: prf_ok_mono)

end

context prf_model
begin

subsection \<open>The primitive rules of implication and universal quantification\<close>

theorem assume_proof_valid:
  assumes "A \<in> H" "wtp A" "vars A = {}" "ttvars A = {}"
  shows "prf_valid ax H [] (Hyp A) A"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (Hyp A)) (ap \<rho> \<sigma> A)"
    using assms wtpD(2)[OF assms(2)] by (simp add: prf_ap_def ap_ground prf_ok.Hyp)
qed

theorem implies_intr_rule_proof_valid:
  assumes ok: "okT (implies_intr (CTerm A U m) th0) th"
    and p: "prf_valid ax H (th_tpairs th0) prf (th_prop th0)" and wA: "wtp A"
    and H: "\<And>t. t \<in> H \<Longrightarrow> vars t = {} \<and> ttvars t = {}"
  shows "prf_valid ax {t \<in> H. \<not> aconv_term A t} (th_tpairs th) (implies_intr_proof A prf) (th_prop th)"
proof -
  from ok have th: "th = mk_rep (max m (th_maxidx th0)) (th_tpairs th0) (mk_implies A (th_prop th0))"
    by (auto simp: implies_intr_def returnW_def raiseW_def split: if_splits)
  from implies_intr_proof_valid[OF p wA H] show ?thesis by (simp add: th mk_rep_def mk_implies_def)
qed

theorem implies_elim_rule_proof_valid:
  assumes ok: "okT (implies_elim thAB thA) th"
    and p: "prf_valid ax H1 (th_tpairs thAB) p (th_prop thAB)"
    and q: "prf_valid ax H2 (th_tpairs thA) q (th_prop thA)"
    and w1: "wtp (th_prop thAB)" and w2: "wtp (th_prop thA)"
  shows "prf_valid ax (H1 \<union> H2) (th_tpairs th) (PAppp p q) (th_prop th)"
proof -
  from ok obtain A B where d: "dest_imp (th_prop thAB) = Some (A, B)" and a: "aconv_term A (th_prop thA)"
    and th: "th = mk_rep (max (th_maxidx thA) (th_maxidx thAB)) (union_tpairs (th_tpairs thA) (th_tpairs thAB)) B"
    by (auto simp: implies_elim_def returnW_def raiseW_def split: option.splits if_splits)
  note dw = dest_imp_wtp[OF d w1]
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have sol': "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "(t, u) \<in> set (th_tpairs thA) \<union> set (th_tpairs thAB)" for t u
      by (rule sol_union_tpairs[OF _ that]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    have "prf_ok ax H1 e [] (prf_ap \<rho> \<sigma> p) (ap \<rho> \<sigma> (th_prop thAB))"
      by (rule prf_validD[OF p \<rho> \<sigma>]) (use sol' in auto)
    then have "prf_ok ax (H1 \<union> H2) e [] (prf_ap \<rho> \<sigma> p) (ap \<rho> \<sigma> (th_prop thAB))"
      by (rule prf_ok_mono) simp
    then have pp: "prf_ok ax (H1 \<union> H2) e [] (prf_ap \<rho> \<sigma> p) (implies $ ap \<rho> \<sigma> A $ ap \<rho> \<sigma> B)"
      by (simp add: dw(1) ap_def)
    have "prf_ok ax H2 e [] (prf_ap \<rho> \<sigma> q) (ap \<rho> \<sigma> (th_prop thA))"
      by (rule prf_validD[OF q \<rho> \<sigma>]) (use sol' in auto)
    then have "prf_ok ax (H1 \<union> H2) e [] (prf_ap \<rho> \<sigma> q) (ap \<rho> \<sigma> (th_prop thA))" by (rule prf_ok_mono) simp
    moreover have "ap \<rho> \<sigma> (th_prop thA) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> A"
      using a by (blast intro: aconv_term_conv aconv_term_ap conv_sym)
    ultimately have "prf_ok ax (H1 \<union> H2) e [] (prf_ap \<rho> \<sigma> q) (ap \<rho> \<sigma> A)"
      by (rule prf_ok.conv) (rule typing_ap_wtp[OF dw(2) \<rho> \<sigma>])
    with pp show "prf_ok ax (H1 \<union> H2) e [] (prf_ap \<rho> \<sigma> (PAppp p q)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: th mk_rep_def prf_ap_def ap_def[symmetric] prf_ok.PAppp)
  qed
qed

theorem forall_elim_rule_proof_valid:
  assumes ok: "okT (forall_elim (CTerm t T m) th0) th"
    and p: "prf_valid ax H (th_tpairs th0) prf (th_prop th0)"
    and w: "wtp (th_prop th0)" and ct: "closed t" "\<And>e. e \<turnstile> t : T"
  shows "prf_valid ax H (th_tpairs th) (PAppt prf (Some t)) (th_prop th)"
proof -
  from ok obtain A where d: "dest_all_app (th_prop th0) = Some (T, A)"
    and th: "th = mk_rep (max m (th_maxidx th0)) (th_tpairs th0) (betapply A t)"
    by (auto simp: forall_elim_def returnW_def raiseW_def split: option.splits if_splits)
  note dw = dest_all_app_wtp[OF d w]
  have wAt: "wtp (A $ t)" using dw(2,3) ct by (intro wtpI) (auto simp: closed_def)
  have wt: "wt (A $ t)" unfolding wt_def using wtpD(2)[OF wAt, of "\<lambda>_. propT"] by blast
  have wB: "wtp (betapply A t)"
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
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> prf) (ap \<rho> \<sigma> (th_prop th0))"
      by (rule prf_validD[OF p \<rho> \<sigma>]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    then have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> prf) (all_const (tsubst \<rho> T) $ ap \<rho> \<sigma> A)"
      by (simp add: dw(1) ap_def[symmetric])
    moreover have "e \<turnstile> ap \<rho> \<sigma> t : tsubst \<rho> T"
    proof -
      have "closed (ap \<rho> \<sigma> t)" using ct(1) \<sigma> by (simp add: closed_def)
      with typing_ap_inst[OF ct(2) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] show ?thesis by (rule typing_closed)
    qed
    ultimately have "prf_ok ax H e [] (PAppt (prf_ap \<rho> \<sigma> prf) (Some (ap \<rho> \<sigma> t))) (ap \<rho> \<sigma> (A $ t))"
      by (simp add: ap_def[symmetric] prf_ok.PAppt)
    moreover have "ap \<rho> \<sigma> (A $ t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (betapply A t)"
      by (rule conv_ap[OF betapply_conv[OF wt] cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
    ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (PAppt prf (Some t))) (ap \<rho> \<sigma> (th_prop th))"
      using typing_ap_wtp[OF wB \<rho> \<sigma>] by (simp add: th mk_rep_def prf_ap_def ap_def[symmetric] prf_ok.conv)
  qed
qed

end

subsection \<open>Universal introduction\<close>

definition tauV :: "name \<Rightarrow> ptyp \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> ptyp \<Rightarrow> pterm" where
  "tauV G U lev y V = (if y = G \<and> V = U then Bound lev else Free y V)"

definition tauF :: "name \<Rightarrow> name \<Rightarrow> ptyp \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> ptyp \<Rightarrow> pterm" where
  "tauF a G U lev y V = (if y = a \<and> V = U then Bound lev else if y = G \<and> V = U then Free a U else Free y V)"

lemma lift_tauV: "0 \<le> lev \<Longrightarrow> (\<lambda>y V. lift (tauV G U lev y V) 0) = tauV G U (lev + 1)"
  by (auto simp: fun_eq_iff tauV_def)

lemma lift_tauF: "0 \<le> lev \<Longrightarrow> (\<lambda>y V. lift (tauF a G U lev y V) 0) = tauF a G U (lev + 1)"
  by (auto simp: fun_eq_iff tauF_def)

lemma prf_abstract_term_atom:
  "x = Free a T \<or> x = Var z T \<Longrightarrow> prf_abstract_term x lev t = abstract_over_aux x lev t"
  by (induction t arbitrary: lev) (auto simp: aconv_term_atom)

lemma fsubst_tauF_frename:
  assumes "G \<notin> fnames s" "G \<noteq> a" "0 \<le> lev"
  shows "fsubst (tauF a G U lev) (frename (\<lambda>b V. if b = a \<and> V = U then G else b) s) = s"
  using assms
proof (induction s arbitrary: lev)
  case (Free y V)
  then show ?case by (auto simp: tauF_def)
next
  case (Abs c V t)
  then show ?case by (simp add: lift_tauF)
qed simp_all

lemma prf_atoms_map_proof_terms [simp]: "prf_atoms (map_proof_terms f g p) = prf_atoms p"
proof (induction p)
  case (PThm x)
  then show ?case by (cases x) simp
qed simp_all

lemma finite_prf_terms [simp]: "finite (prf_terms p)"
  by (induction p rule: prf_terms.induct) auto

context prf_sig
begin

lemma fsubst_ap_Var:
  assumes "0 \<le> lev" and u: "\<And>U. (z, U) \<in> vars t \<Longrightarrow> U = T"
    and G: "G \<notin> fnames t" "\<And>v U. (v, U) \<in> vars t \<Longrightarrow> G \<notin> fnames (\<sigma> v (tsubst \<rho> U))"
  shows "fsubst (tauV G (tsubst \<rho> T) lev) (ap \<rho> (\<sigma>(z := (\<sigma> z)(tsubst \<rho> T := Free G (tsubst \<rho> T)))) t) =
    ap \<rho> \<sigma> (abstract_over_aux (Var z T) lev t)"
  using assms
proof (induction t arbitrary: lev)
  case (Var v U)
  show ?case
  proof (cases "v = z")
    case True
    with Var.prems(2) have "U = T" by simp
    with True show ?thesis by (simp add: ap_def tauV_def)
  next
    case False
    have "fsubst (tauV G (tsubst \<rho> T) lev) (\<sigma> v (tsubst \<rho> U)) = \<sigma> v (tsubst \<rho> U)"
      by (rule fsubst_id) (use Var.prems(4) in \<open>auto simp: tauV_def\<close>)
    with False show ?thesis by (simp add: ap_def)
  qed
next
  case (Free y U)
  then show ?case by (auto simp: ap_def tauV_def)
next
  case (Abs b U s)
  then show ?case by (simp add: ap_def lift_tauV)
next
  case (App s1 s2)
  then show ?case by (simp add: ap_def)
qed (simp_all add: ap_def)

lemma fsubst_ap_Free:
  assumes "0 \<le> lev" and u: "\<And>U. (a, U) \<in> pfrees t \<Longrightarrow> U = T" and Ga: "G \<noteq> a"
    and G: "G \<notin> fnames t" "\<And>v U. (v, U) \<in> vars t \<Longrightarrow> G \<notin> fnames (\<sigma> v (tsubst \<rho> U))"
  shows "fsubst (tauF a G (tsubst \<rho> T) lev)
      (ap \<rho> (\<lambda>v U. frename (\<lambda>b V. if b = a \<and> V = tsubst \<rho> T then G else b) (\<sigma> v U)) t) =
    ap \<rho> \<sigma> (abstract_over_aux (Free a T) lev t)"
  using assms
proof (induction t arbitrary: lev)
  case (Var v U)
  then show ?case by (simp add: ap_def fsubst_tauF_frename)
next
  case (Free y U)
  then show ?case by (auto simp: ap_def tauF_def)
next
  case (Abs b U s)
  then show ?case by (simp add: ap_def lift_tauF)
next
  case (App s1 s2)
  then show ?case by (simp add: ap_def)
qed (simp_all add: ap_def)

lemma prf_fsubst_prf_ap_abstract:
  assumes x: "x = Free a T \<or> x = Var z T" and lt: "\<And>lev. 0 \<le> lev \<Longrightarrow> (\<lambda>y V. lift (\<tau> lev y V) 0) = \<tau> (lev + 1)"
    and tm: "\<And>t lev. t \<in> prf_terms p \<Longrightarrow> 0 \<le> lev \<Longrightarrow> fsubst (\<tau> lev) (ap \<rho> \<sigma>' t) = ap \<rho> \<sigma> (abstract_over_aux x lev t)"
    and "0 \<le> lev"
  shows "prf_fsubst (\<tau> lev) (prf_ap \<rho> \<sigma>' p) = prf_ap \<rho> \<sigma> (prf_abstract_over_aux x lev p)"
  using tm assms(4)
proof (induction p arbitrary: lev)
  case (Abst b U q)
  have "prf_fsubst (\<tau> (lev + 1)) (prf_ap \<rho> \<sigma>' q) = prf_ap \<rho> \<sigma> (prf_abstract_over_aux x (lev + 1) q)"
    by (rule Abst.IH) (use Abst.prems in auto)
  with Abst.prems(2) lt show ?case by (simp add: prf_ap_def)
next
  case (AbsP b t q)
  then show ?case by (cases t) (auto simp: prf_ap_def prf_abstract_term_atom[OF x])
next
  case (PAppt q t)
  then show ?case by (cases t) (auto simp: prf_ap_def prf_abstract_term_atom[OF x])
next
  case (PAppp q1 q2)
  then show ?case by (simp add: prf_ap_def)
next
  case (PThm h)
  then show ?case by (cases h) (simp add: prf_ap_def)
qed (simp_all add: prf_ap_def)

end

context prf_model
begin

lemma prf_ok_Abst_fsubst:
  assumes p: "prf_ok ax H (e\<langle>0:U\<rangle>) [] q \<phi>" and cU: "cert_typ alg ar U"
    and N: "\<And>h. h \<in> H \<Longrightarrow> fnames h \<inter> N = {}" "\<forall>A\<in>prf_atoms q. fnames (close A) \<inter> N = {}"
    and \<tau>: "\<And>y V. cert_typ alg ar V \<Longrightarrow> e\<langle>0:U\<rangle> \<turnstile> \<tau> y V : V" "\<And>y V. y \<notin> N \<Longrightarrow> \<tau> y V = Free y V"
  shows "prf_ok ax H e [] (Abst c None (prf_fsubst \<tau> q)) (all_const U $ Abs b U (fsubst \<tau> \<phi>))"
proof -
  have "prf_ok ax H (e\<langle>0:U\<rangle>) (map (fsubst \<tau>) []) (prf_fsubst \<tau> q) (fsubst \<tau> \<phi>)"
    by (rule prf_ok_fsubst[OF N(1) p \<tau> N(2)])
  then show ?thesis using cU by (simp add: prf_ok.Abst)
qed

lemma forall_intr_proof_valid:
  assumes p: "prf_valid ax (set hs) tps prf P"
    and wt: "wt_thm m hs tps P" and tx: "\<And>e. e \<turnstile> x : T"
    and cases: "(x = Free b T \<and> \<not> occs_hyps x hs tps) \<or> (\<exists>j. x = Var (b, j) T \<and> \<not> occs_hyps x [] tps)"
    and uF: "\<And>t a U. t \<in> thm_terms hs tps P \<union> prf_terms prf \<Longrightarrow> x = Free a T \<Longrightarrow>
      (a, U) \<in> pfrees t \<Longrightarrow> U = T"
    and uV: "\<And>t z U. t \<in> thm_terms hs tps P \<union> prf_terms prf \<Longrightarrow> x = Var z T \<Longrightarrow>
      (z, U) \<in> vars t \<Longrightarrow> U = T"
    and axF: "\<And>A a. A \<in> prf_atoms prf \<Longrightarrow> x = Free a T \<Longrightarrow> a \<notin> fnames (close A)"
  shows "prf_valid ax (set hs) tps (forall_intr_proof c x prf) (all_const T $ Abs b' T (abstract_over x P))"
proof -
  let ?tps = "tps" and ?P = "P"
  let ?Ts = "thm_terms hs ?tps ?P \<union> prf_terms prf"
  have hv: "\<And>h. h \<in> set hs \<Longrightarrow> vars h = {}" using wt by (simp add: wt_thm_def)
  have cT: "cert_typ alg ar T" using cases tx[of "\<lambda>_. propT"] by auto
  have fTs: "finite ?Ts" by simp
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    let ?\<rho>T = "tsubst \<rho> T"
    have c\<rho>T: "cert_typ alg ar ?\<rho>T" by (rule cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]])
    define N0 where "N0 = (\<Union>t\<in>?Ts. fnames t) \<union> (\<Union>t\<in>?Ts. \<Union>(v, U)\<in>vars t. fnames (\<sigma> v (tsubst \<rho> U))) \<union>
      (\<Union>A\<in>prf_atoms prf. fnames (close A)) \<union> {b}"
    have "finite N0" using fTs by (auto simp: N0_def)
    then obtain G where G: "G \<notin> N0" using ex_new_if_finite[OF infinite_literal] by blast
    have Gt: "G \<notin> fnames t" if "t \<in> ?Ts" for t using G that by (auto simp: N0_def)
    have G\<sigma>: "G \<notin> fnames (\<sigma> v (tsubst \<rho> U))" if "t \<in> ?Ts" "(v, U) \<in> vars t" for t v U
      using G that by (auto simp: N0_def)
    have GA: "G \<notin> fnames (close A)" if "A \<in> prf_atoms prf" for A using G that by (auto simp: N0_def)
    have Gb: "G \<noteq> b" using G by (simp add: N0_def)
    have PTs: "?P \<in> ?Ts" by (simp add: thm_terms_def)
    have hTs: "h \<in> ?Ts" if "h \<in> set hs" for h using that by (simp add: thm_terms_def)
    have tTs: "t \<in> ?Ts \<and> u \<in> ?Ts" if "(t, u) \<in> set ?tps" for t u using that by (force simp: thm_terms_def)
    have pTs: "t \<in> ?Ts" if "t \<in> prf_terms prf" for t using that by simp
    note \<sigma>c = closed_substD[OF gsubstD(2)[OF \<sigma>]]
    have \<sigma>t: "cert_typ alg ar U \<Longrightarrow> \<exists>e. e \<turnstile> \<sigma> v U : U" for v U
      using wt_subst_typing[OF gsubstD(1)[OF \<sigma>]] by blast
    have tw: "closed t \<and> (\<exists>U. \<forall>e. e \<turnstile> t : U)" if "(t, u) \<in> set ?tps" for t u
      using wt that by (fastforce simp: wt_thm_def)
    from cases show "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> (forall_intr_proof c x prf))
        (ap \<rho> \<sigma> (all_const T $ Abs b' T (abstract_over x P)))"
    proof (elim disjE exE conjE)
      assume xF: "x = Free b T" and noc: "\<not> occs_hyps x hs ?tps"
      define f where "f = (\<lambda>a V. if a = b \<and> V = ?\<rho>T then G else a)"
      define \<sigma>' where "\<sigma>' = (\<lambda>v U. frename f (\<sigma> v U))"
      have \<sigma>': "gsubst \<sigma>'"
        using \<sigma>c \<sigma>t by (fastforce simp: gsubst_def wt_subst_def closed_subst_def closed_def \<sigma>'_def intro: typing_frename)
      have fr: "f a (tsubst \<rho> U) = a" if "s \<in> ?Ts" "\<not> occs x s" "(a, U) \<in> pfrees s" for s a U
      proof -
        have "a \<noteq> b" using that uF[OF that(1) xF, of U] xF by (auto simp: occs_Free)
        then show ?thesis by (simp add: f_def)
      qed
      have sol': "ap \<rho> \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u" if tu: "(t, u) \<in> set ?tps" for t u
      proof -
        have no: "\<not> occs x t" "\<not> occs x u" using noc tu by (auto simp: occs_hyps_def)
        have e: "ap \<rho> \<sigma>' s = frename f (ap \<rho> \<sigma> s)" if "s \<in> ?Ts" "\<not> occs x s" for s
          using ap_frename[of s f \<rho> \<sigma>] fr[OF that] by (simp add: \<sigma>'_def)
        from tw[OF tu] obtain U where ct: "closed t" and tt: "\<And>e. e \<turnstile> t : U" by blast
        have "gterm (ap \<rho> \<sigma> t) (tsubst \<rho> U)" by (rule gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma> ct tt])
        then have "wt (ap \<rho> \<sigma> t)" unfolding gterm_def wt_def by blast
        from conv_frename[OF this sol[of t u]] tu e[OF conjunct1[OF tTs[OF tu]] no(1)]
          e[OF conjunct2[OF tTs[OF tu]] no(2)]
        show ?thesis by simp
      qed
      have pr: "prf_ok ax (set hs) (e\<langle>0:?\<rho>T\<rangle>) [] (prf_ap \<rho> \<sigma>' prf) (ap \<rho> \<sigma>' ?P)"
        by (rule prf_validD[OF p \<rho> \<sigma>' sol'])
      have tm: "fsubst (tauF b G ?\<rho>T lev) (ap \<rho> \<sigma>' t) = ap \<rho> \<sigma> (abstract_over_aux x lev t)"
        if "t \<in> ?Ts" "0 \<le> lev" for t lev
        unfolding \<sigma>'_def f_def xF
        by (rule fsubst_ap_Free[OF that(2) _ Gb Gt[OF that(1)]]) (use uF[OF that(1) xF] G\<sigma>[OF that(1)] in auto)
      have nh: "fnames h \<inter> {b, G} = {}" if "h \<in> set hs" for h
      proof -
        have "\<not> occs x h" using noc that by (auto simp: occs_hyps_def)
        then have "b \<notin> fnames h" using uF[OF hTs[OF that] xF] xF by (force simp: occs_Free fnames_pfrees)
        then show ?thesis using Gt[OF hTs[OF that]] by auto
      qed
      have "prf_ok ax (set hs) e [] (Abst c None (prf_fsubst (tauF b G ?\<rho>T 0) (prf_ap \<rho> \<sigma>' prf)))
          (all_const ?\<rho>T $ Abs b' ?\<rho>T (fsubst (tauF b G ?\<rho>T 0) (ap \<rho> \<sigma>' ?P)))"
      proof (rule prf_ok_Abst_fsubst[OF pr c\<rho>T nh])
        show "\<forall>A\<in>prf_atoms (prf_ap \<rho> \<sigma>' prf). fnames (close A) \<inter> {b, G} = {}"
          using axF xF GA by (auto simp: prf_ap_def)
        show "e\<langle>0:?\<rho>T\<rangle> \<turnstile> tauF b G ?\<rho>T 0 y V : V" if "cert_typ alg ar V" for y V
          using that c\<rho>T by (auto simp: tauF_def shift_def)
      qed (auto simp: tauF_def)
      moreover have "prf_fsubst (tauF b G ?\<rho>T 0) (prf_ap \<rho> \<sigma>' prf) = prf_ap \<rho> \<sigma> (prf_abstract_over x prf)"
        unfolding prf_abstract_over_def
        by (rule prf_fsubst_prf_ap_abstract[where \<tau> = "tauF b G ?\<rho>T" and lev = 0, OF disjI1[OF xF] lift_tauF])
          (use tm pTs in auto)
      ultimately show ?thesis
        using tm[OF PTs, of 0] by (simp add: forall_intr_proof_def prf_ap_def abstract_over_def)
    next
      fix j assume xV: "x = Var (b, j) T" and noc: "\<not> occs_hyps x [] ?tps"
      let ?z = "(b, j)"
      define \<sigma>' where "\<sigma>' = \<sigma>(?z := (\<sigma> ?z)(?\<rho>T := Free G ?\<rho>T))"
      have \<sigma>': "gsubst \<sigma>'"
        using \<sigma>c \<sigma>t c\<rho>T by (fastforce simp: gsubst_def wt_subst_def closed_subst_def closed_def \<sigma>'_def)
      have sol': "ap \<rho> \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u" if tu: "(t, u) \<in> set ?tps" for t u
      proof -
        have no: "\<not> occs x t" "\<not> occs x u" using noc tu by (auto simp: occs_hyps_def)
        have "ap \<rho> \<sigma>' s = ap \<rho> \<sigma> s" if "s \<in> ?Ts" "\<not> occs x s" for s
        proof (rule ap_cong_vars)
          fix v U assume "(v, U) \<in> vars s"
          with that uV[OF that(1) xV, of U] xV show "\<sigma>' v (tsubst \<rho> U) = \<sigma> v (tsubst \<rho> U)"
            by (auto simp: \<sigma>'_def occs_Var)
        qed
        with tTs[OF tu] no sol[of t u] tu show ?thesis by simp
      qed
      have pr: "prf_ok ax (set hs) (e\<langle>0:?\<rho>T\<rangle>) [] (prf_ap \<rho> \<sigma>' prf) (ap \<rho> \<sigma>' ?P)"
        by (rule prf_validD[OF p \<rho> \<sigma>' sol'])
      have tm: "fsubst (tauV G ?\<rho>T lev) (ap \<rho> \<sigma>' t) = ap \<rho> \<sigma> (abstract_over_aux x lev t)"
        if "t \<in> ?Ts" "0 \<le> lev" for t lev
        unfolding \<sigma>'_def xV
        by (rule fsubst_ap_Var[OF that(2) _ Gt[OF that(1)]]) (use uV[OF that(1) xV] G\<sigma>[OF that(1)] in auto)
      have nh: "fnames h \<inter> {G} = {}" if "h \<in> set hs" for h using Gt[OF hTs[OF that]] by auto
      have "prf_ok ax (set hs) e [] (Abst c None (prf_fsubst (tauV G ?\<rho>T 0) (prf_ap \<rho> \<sigma>' prf)))
          (all_const ?\<rho>T $ Abs b' ?\<rho>T (fsubst (tauV G ?\<rho>T 0) (ap \<rho> \<sigma>' ?P)))"
      proof (rule prf_ok_Abst_fsubst[OF pr c\<rho>T nh])
        show "\<forall>A\<in>prf_atoms (prf_ap \<rho> \<sigma>' prf). fnames (close A) \<inter> {G} = {}"
          using GA by (auto simp: prf_ap_def)
        show "e\<langle>0:?\<rho>T\<rangle> \<turnstile> tauV G ?\<rho>T 0 y V : V" if "cert_typ alg ar V" for y V
          using that by (auto simp: tauV_def shift_def)
      qed (auto simp: tauV_def)
      moreover have "prf_fsubst (tauV G ?\<rho>T 0) (prf_ap \<rho> \<sigma>' prf) = prf_ap \<rho> \<sigma> (prf_abstract_over x prf)"
        unfolding prf_abstract_over_def
        by (rule prf_fsubst_prf_ap_abstract[where \<tau> = "tauV G ?\<rho>T" and lev = 0, OF disjI2[OF xV] lift_tauV])
          (use tm pTs in auto)
      ultimately show ?thesis
        using tm[OF PTs, of 0] by (simp add: forall_intr_proof_def prf_ap_def abstract_over_def)
    qed
  qed
qed


theorem forall_intr_rule_proof_valid:
  assumes ok: "okT (forall_intr hs (CTerm x T m) th0) th"
    and p: "prf_valid ax (set hs) (th_tpairs th0) prf (th_prop th0)"
    and wt: "wt_thm (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)" and tx: "\<And>e. e \<turnstile> x : T"
    and uF: "\<And>t a U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms prf \<Longrightarrow> x = Free a T \<Longrightarrow>
      (a, U) \<in> pfrees t \<Longrightarrow> U = T"
    and uV: "\<And>t z U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms prf \<Longrightarrow> x = Var z T \<Longrightarrow>
      (z, U) \<in> vars t \<Longrightarrow> U = T"
    and axF: "\<And>A a. A \<in> prf_atoms prf \<Longrightarrow> x = Free a T \<Longrightarrow> a \<notin> fnames (close A)"
  shows "prf_valid ax (set hs) (th_tpairs th) (forall_intr_proof c x prf) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  obtain b where th: "th = mk_rep (max m (th_maxidx th0)) ?tps (all_const T $ Abs b T (abstract_over x ?P))"
    and cases: "(x = Free b T \<and> \<not> occs_hyps x hs ?tps) \<or> (\<exists>j. x = Var (b, j) T \<and> \<not> occs_hyps x [] ?tps)"
  proof (cases x)
    case (Free a U)
    with tx[of "\<lambda>_. propT"] have "U = T" by auto
    with ok Free that[of a] show ?thesis
      by (auto simp: forall_intr_def returnW_def raiseW_def Let_def split: if_splits)
  next
    case (Var zi U)
    obtain a j where zi: "zi = (a, j)" by (cases zi)
    with Var tx[of "\<lambda>_. propT"] have "U = T" by auto
    with ok Var zi that[of a] show ?thesis
      by (auto simp: forall_intr_def returnW_def raiseW_def Let_def split: if_splits)
  qed (use ok in \<open>auto simp: forall_intr_def raiseW_def Let_def\<close>)
  from forall_intr_proof_valid[OF p wt tx cases uF uV axF] show ?thesis by (simp add: th mk_rep_def)
qed
end

subsection \<open>Instances of proofs\<close>

lemma map_proof_terms_comp:
  "map_proof_terms f g (map_proof_terms f' g' p) = map_proof_terms (f \<circ> f') (g \<circ> g') p"
proof (induction p)
  case (PThm x)
  then show ?case by (cases x) (simp add: option.map_comp comp_def)
qed (simp_all add: option.map_comp comp_def)

lemma map_proof_terms_cong:
  "(\<And>t. t \<in> prf_terms p \<Longrightarrow> f t = f' t) \<Longrightarrow> map_proof_terms f g p = map_proof_terms f' g p"
proof (induction p)
  case (AbsP a t q)
  then show ?case by (cases t) simp_all
next
  case (PAppt q t)
  then show ?case by (cases t) simp_all
next
  case (PThm x)
  then show ?case by (cases x) simp
qed simp_all

lemma prf_terms_map_proof_terms: "prf_terms (map_proof_terms f g p) = f ` prf_terms p"
proof (induction p)
  case (AbsP a t q)
  then show ?case by (cases t) simp_all
next
  case (PAppt q t)
  then show ?case by (cases t) auto
next
  case (PThm x)
  then show ?case by (cases x) simp
qed auto

lemma prf_aeq_map_proof_terms:
  "(\<And>t. t \<in> prf_terms p \<Longrightarrow> erase (f t) = erase (f' t)) \<Longrightarrow>
    prf_aeq (map_proof_terms f g p) (map_proof_terms f' g p)"
proof (induction p)
  case (Abst a T q)
  then show ?case by (simp add: prf_aeq.Abst)
next
  case (AbsP a t q)
  then show ?case by (cases t) (simp_all add: prf_aeq.AbsP ann_eq_def)
next
  case (PAppt q t)
  then show ?case by (cases t) (simp_all add: prf_aeq.PAppt ann_eq_def)
next
  case (PAppp q1 q2)
  then show ?case by (simp add: prf_aeq.PAppp)
next
  case (PThm x)
  then show ?case by (cases x) (simp add: prf_aeq.refl)
qed (simp_all add: prf_aeq.refl)

lemma erase_vsubst_cong:
  "(\<And>x U. erase (\<sigma> x U) = erase (\<sigma>' x U)) \<Longrightarrow> erase (vsubst \<sigma> t) = erase (vsubst \<sigma>' t)"
  by (induction t) simp_all

context prf_sig
begin

lemma erase_ap_cong: "erase s = erase t \<Longrightarrow> erase (ap \<rho> \<sigma> s) = erase (ap \<rho> \<sigma> t)"
  by (metis erase_ap_erase)

lemma ap_vsubst0:
  "(\<And>x T. (x, T) \<in> vars t \<Longrightarrow> \<sigma>1 x (tsubst \<rho> T) = ap \<rho> \<sigma> (\<sigma>0 x T)) \<Longrightarrow>
    ap \<rho> \<sigma>1 t = ap \<rho> \<sigma> (vsubst \<sigma>0 t)"
  by (induction t) (auto simp: ap_def)

lemma prf_valid_erase_terms:
  assumes "prf_valid ax H tps (map_proof_terms f g p) \<phi>"
    and "\<And>t. t \<in> prf_terms p \<Longrightarrow> erase (f t) = erase (f' t)"
  shows "prf_valid ax H tps (map_proof_terms f' g p) \<phi>"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (map_proof_terms f g p)) (ap \<rho> \<sigma> \<phi>)" by (rule prf_validD[OF assms(1) \<rho> \<sigma> sol])
  moreover have "prf_aeq (prf_ap \<rho> \<sigma> (map_proof_terms f g p)) (prf_ap \<rho> \<sigma> (map_proof_terms f' g p))"
    unfolding prf_ap_def map_proof_terms_comp
    by (rule prf_aeq_map_proof_terms) (simp only: comp_def, rule erase_ap_cong, rule assms(2))
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (map_proof_terms f' g p)) (ap \<rho> \<sigma> \<phi>)"
    by (rule prf_ok_aeq)
qed

theorem prf_valid_tinst:
  assumes p: "prf_valid ax H tps p \<phi>" and \<rho>0: "cinst \<rho>0"
  shows "prf_valid ax H (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps) (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) p)
    (inst \<rho>0 \<phi>)"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  let ?\<rho> = "\<lambda>v S. tsubst \<rho> (\<rho>0 v S)"
  have a: "ap \<rho> \<sigma> (inst \<rho>0 t) = ap ?\<rho> \<sigma> t" for t by (simp add: ap_def inst_inst)
  have "prf_ok ax H e [] (prf_ap ?\<rho> \<sigma> p) (ap ?\<rho> \<sigma> \<phi>)"
    by (rule prf_validD[OF p cinst_comp[OF \<rho> \<rho>0] \<sigma>]) (use sol in \<open>force simp: a[symmetric]\<close>)
  moreover have "prf_ap \<rho> \<sigma> (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) p) = prf_ap ?\<rho> \<sigma> p"
    unfolding prf_ap_def map_proof_terms_comp by (simp add: comp_def a tsubst_tsubst)
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) p)) (ap \<rho> \<sigma> (inst \<rho>0 \<phi>))"
    by (simp add: a)
qed

definition prf_vars :: "(pterm \<times> pterm) list \<Rightarrow> prf \<Rightarrow> pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "prf_vars tps p \<phi> = vars \<phi> \<union> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u) \<union> (\<Union>t\<in>prf_terms p. vars t)"

theorem prf_valid_vsubst:
  assumes p: "prf_valid ax H tps p \<phi>" and \<sigma>0: "wt_subst \<sigma>0"
    and uniq: "\<And>x T U. (x, T) \<in> prf_vars tps p \<phi> \<Longrightarrow> (x, U) \<in> prf_vars tps p \<phi> \<Longrightarrow> T = U"
    and cert: "\<And>x T. (x, T) \<in> prf_vars tps p \<phi> \<Longrightarrow> cert_typ alg ar T"
  shows "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) tps) (map_proof_terms (vsubst \<sigma>0) id p)
    (vsubst \<sigma>0 \<phi>)"
proof (rule prf_validI)
  let ?V = "prf_vars tps p \<phi>"
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) tps) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  define \<sigma>1 where "\<sigma>1 x T' = (if \<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T
    then ap \<rho> \<sigma> (\<sigma>0 x (SOME T. (x, T) \<in> ?V)) else \<sigma> x T')" for x T'
  have s1: "\<sigma>1 x (tsubst \<rho> T) = ap \<rho> \<sigma> (\<sigma>0 x T)" if "(x, T) \<in> ?V" for x T
  proof -
    have "(SOME T. (x, T) \<in> ?V) = T" using that uniq by (metis (mono_tags, lifting) someI)
    with that show ?thesis by (auto simp: \<sigma>1_def)
  qed
  have g1: "gsubst \<sigma>1"
  proof -
    have cv: "closed (\<sigma>1 x T')" for x T'
    proof (cases "\<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T")
      case True
      then obtain T where T: "(x, T) \<in> ?V" "T' = tsubst \<rho> T" by blast
      have "closed (\<sigma>0 x T)" using \<sigma>0 by (simp add: wt_subst_def closed_substD)
      then show ?thesis using s1[OF T(1)] T(2) \<sigma> by (simp add: closed_def gsubstD)
    next
      case False
      then have "\<sigma>1 x T' = \<sigma> x T'" unfolding \<sigma>1_def by (rule if_not_P)
      then show ?thesis using \<sigma> by (simp add: gsubstD closed_substD)
    qed
    moreover have "e \<turnstile> \<sigma>1 x T' : T'" if "cert_typ alg ar T'" for e x T'
    proof (cases "\<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T")
      case True
      then obtain T where T: "(x, T) \<in> ?V" "T' = tsubst \<rho> T" by blast
      have "(\<lambda>i. tsubst \<rho> (e i)) \<turnstile> ap \<rho> \<sigma> (\<sigma>0 x T) : tsubst \<rho> T"
        by (rule typing_ap_inst[OF wt_subst_typing[OF \<sigma>0 cert[OF T(1)]] cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
      with cv[of x T'] s1[OF T(1)] T(2) show ?thesis by (metis typing_closed)
    next
      case False
      then have "\<sigma>1 x T' = \<sigma> x T'" unfolding \<sigma>1_def by (rule if_not_P)
      then show ?thesis using wt_subst_typing[OF gsubstD(1)[OF \<sigma>] that] by simp
    qed
    ultimately show ?thesis by (auto simp: gsubst_def wt_subst_def closed_subst_def)
  qed
  have a: "ap \<rho> \<sigma>1 t = ap \<rho> \<sigma> (vsubst \<sigma>0 t)" if "vars t \<subseteq> ?V" for t
    by (rule ap_vsubst0) (use s1 that in blast)
  have "prf_ok ax H e [] (prf_ap \<rho> \<sigma>1 p) (ap \<rho> \<sigma>1 \<phi>)"
  proof (rule prf_validD[OF p \<rho> g1])
    fix t u assume tu: "(t, u) \<in> set tps"
    then have "vars t \<subseteq> ?V" "vars u \<subseteq> ?V" by (auto simp: prf_vars_def)
    with tu sol show "ap \<rho> \<sigma>1 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>1 u" by (force simp: a)
  qed
  moreover have "prf_ap \<rho> \<sigma> (map_proof_terms (vsubst \<sigma>0) id p) = prf_ap \<rho> \<sigma>1 p"
    unfolding prf_ap_def map_proof_terms_comp comp_id
    by (rule map_proof_terms_cong) (use a in \<open>fastforce simp: prf_vars_def\<close>)
  moreover have "vars \<phi> \<subseteq> ?V" by (auto simp: prf_vars_def)
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (map_proof_terms (vsubst \<sigma>0) id p)) (ap \<rho> \<sigma> (vsubst \<sigma>0 \<phi>))"
    by (simp add: a)
qed

lemma ap_incr_idx_Nil:
  "ap \<rho> \<sigma> (incr_idx [] inc lev t) = ap (tinc inc \<rho>) (\<lambda>(x, i) U. \<sigma> (x, i + inc) U) t"
  by (induction "[] :: ptyp list" inc lev t rule: incr_idx.induct)
    (simp_all add: ap_def tsubst_incr_tvar)

lemma gsubst_incr: "gsubst \<sigma> \<Longrightarrow> gsubst (\<lambda>(x, i) U. \<sigma> (x, i + inc) U)"
  by (auto simp: gsubst_def wt_subst_def closed_subst_def split: prod.splits)

theorem incr_indexes_proof_valid:
  assumes p: "prf_valid ax H tps p \<phi>"
  shows "prf_valid ax H (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) (incr_indexes_proof i p)
    (incr_indexes [] i \<phi>)"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) tps) \<Longrightarrow>
      ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  let ?\<rho> = "tinc i \<rho>" and ?\<sigma> = "\<lambda>(x, j) U. \<sigma> (x, j + i) U"
  have a: "ap \<rho> \<sigma> (incr_indexes [] i t) = ap ?\<rho> ?\<sigma> t" for t
    by (simp add: incr_indexes_idx ap_incr_idx_Nil)
  have "prf_ok ax H e [] (prf_ap ?\<rho> ?\<sigma> p) (ap ?\<rho> ?\<sigma> \<phi>)"
    by (rule prf_validD[OF p cinst_tinc[OF \<rho>] gsubst_incr[OF \<sigma>]]) (use sol in \<open>force simp: a[symmetric]\<close>)
  moreover have "prf_ap \<rho> \<sigma> (incr_indexes_proof i p) = prf_ap ?\<rho> ?\<sigma> p"
    unfolding prf_ap_def incr_indexes_proof_def map_proof_terms_comp
    by (simp add: comp_def a tsubst_incr_tvar)
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (incr_indexes_proof i p)) (ap \<rho> \<sigma> (incr_indexes [] i \<phi>))"
    by (simp add: a)
qed

theorem instantiate_proof_valid:
  fixes instT :: instT and insts :: inst
  defines "\<rho>0 \<equiv> tab_inst (map (\<lambda>(v, T). (v, (T, -1))) instT)"
    and "\<sigma>0 \<equiv> tab_subst (map (\<lambda>(v, t). (v, (t, -1))) insts)"
  assumes p: "prf_valid ax H tps pf \<phi>" and \<rho>0: "cinst \<rho>0" and \<sigma>0: "wt_subst \<sigma>0"
    and uniq: "\<And>x T U. (x, T) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) pf) (inst \<rho>0 \<phi>) \<Longrightarrow>
      (x, U) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) pf) (inst \<rho>0 \<phi>) \<Longrightarrow> T = U"
    and cert: "\<And>x T. (x, T) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) pf) (inst \<rho>0 \<phi>) \<Longrightarrow> cert_typ alg ar T"
  shows "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps)
    (instantiate_proof instT insts pf) (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
proof -
  define \<sigma>r where "\<sigma>r = tab_subst (map (\<lambda>(v, t). (v, (remove_types t, -1))) insts)"
  have lk: "tab_subst (map (\<lambda>(v, t). (v, (h t, -1))) xs) x U =
      (case map_of xs (x, U) of None \<Rightarrow> Var x U | Some t \<Rightarrow> h t)" for h :: "pterm \<Rightarrow> pterm" and xs :: inst and x U
    by (induction xs) (auto simp: tab_subst_def split: option.splits)
  have er: "erase (\<sigma>0 x U) = erase (\<sigma>r x U)" for x U
    using lk[of "\<lambda>t. t" insts x U] lk[of remove_types insts x U]
    by (simp add: \<sigma>0_def \<sigma>r_def split: option.splits)
  have ip: "instantiate_proof instT insts pf = map_proof_terms (\<lambda>t. vsubst \<sigma>r (inst \<rho>0 t)) (tsubst \<rho>0) pf"
    by (simp add: instantiate_proof_def inst_m_fst instT_m_fst \<rho>0_def \<sigma>r_def Let_def)
  have v1: "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps))
      (map_proof_terms (vsubst \<sigma>0) id (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) pf)) (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
    by (rule prf_valid_vsubst[OF prf_valid_tinst[OF p \<rho>0] \<sigma>0 uniq cert])
  have "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps)
      (map_proof_terms (\<lambda>t. vsubst \<sigma>0 (inst \<rho>0 t)) (tsubst \<rho>0) pf) (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
    using v1 by (simp add: map_proof_terms_comp comp_def case_prod_beta')
  then show ?thesis unfolding ip
    by (rule prf_valid_erase_terms) (rule erase_vsubst_cong, rule er)
qed

end


subsection \<open>Freezing schematic type variables\<close>

context prf_model
begin

theorem legacy_freezeT_proof_valid:
  assumes ok: "okT (legacy_freezeT vl th0) th" and f: "ok (full_prop_of (th_tpairs th0) (th_prop th0)) P1"
    and p: "prf_valid ax H (th_tpairs th0) pf (th_prop th0)"
  shows "prf_valid ax H (th_tpairs th) (legacy_freezeT_proof vl P1 pf) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  from ok obtain P1' ts P3 tps0 where f': "ok (full_prop_of ?tps ?P) P1'"
    and sp: "ok (strip_prems (integer_of_nat (length ?tps)) []
      (if legacy_freeze_names vl P1' = [] then P1' else map_types (map_atyps (freeze_tvar (legacy_freeze_names vl P1'))) P1'))
      (ts, P3)"
    and d: "ok (mapM dest_equals ts) tps0"
    and th: "th_tpairs th = rev tps0" "th_prop th = P3"
    by (auto simp: legacy_freezeT_def Let_def mk_rep_def split: prod.splits)
  have P1': "P1' = P1" using f f' by simp
  define \<rho>0 where "\<rho>0 = freeze_inst (legacy_freeze_names vl P1)"
  have mt: "map_types (map_atyps (freeze_tvar (legacy_freeze_names vl P1))) = inst \<rho>0"
    by (simp add: fun_eq_iff \<rho>0_def map_atyps_freeze_tvar[abs_def] map_types_tsubst[symmetric] comp_def)
  have ma: "map_atyps (freeze_tvar (legacy_freeze_names vl P1)) = tsubst \<rho>0"
    by (simp add: fun_eq_iff \<rho>0_def map_atyps_freeze_tvar)
  have nil: "\<rho>0 = TVar" if "legacy_freeze_names vl P1 = []"
    using that by (auto simp: \<rho>0_def freeze_inst_def fun_eq_iff)
  have P2: "(if legacy_freeze_names vl P1 = [] then P1 else map_types (map_atyps (freeze_tvar (legacy_freeze_names vl P1))) P1)
      = inst \<rho>0 P1"
    by (cases "legacy_freeze_names vl P1 = []") (simp_all add: nil mt)
  have pf: "legacy_freezeT_proof vl P1 pf = map_proof_terms (inst \<rho>0) (tsubst \<rho>0) pf"
  proof (cases "legacy_freeze_names vl P1 = []")
    case True
    have "map_proof_terms (\<lambda>t. t) (\<lambda>T. T) q = q" for q
    proof (induction q)
      case (AbsP a t q) then show ?case by (cases t) simp_all
    next
      case (PAppt q t) then show ?case by (cases t) simp_all
    next
      case (PThm x) then show ?case by (cases x) (simp add: option.map_ident hd_set_types_def)
    qed (simp_all add: option.map_ident)
    moreover have "inst TVar = (\<lambda>t. t)" "tsubst TVar = (\<lambda>T. T)" by (simp_all add: fun_eq_iff)
    ultimately show ?thesis using True by (simp add: legacy_freezeT_proof_def nil)
  next
    case False
    have "map_types (tsubst \<rho>0) = inst \<rho>0" by (simp add: fun_eq_iff map_types_tsubst)
    with False show ?thesis by (simp add: legacy_freezeT_proof_def Let_def ma)
  qed
  obtain eqs where eqs: "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) ?tps eqs"
    and P1: "P1 = list_implies eqs ?P"
    by (rule ok_full_prop_of[OF f])
  have l: "integer_of_nat (length ?tps) = ilength (map (inst \<rho>0) eqs)"
    using list_all2_lengthD[OF eqs] by (simp add: ilength_eq)
  from sp[unfolded P1' P2, unfolded P1 inst_list_implies l strip_prems_list_implies]
  have "ts = rev (map (inst \<rho>0) eqs)" "P3 = inst \<rho>0 ?P" by (simp_all add: return_def)
  with ok_dest_equals_inst[OF eqs d] th
  have th': "th_tpairs th = map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) ?tps" "th_prop th = inst \<rho>0 ?P" by simp_all
  have c0: "cinst \<rho>0"
    unfolding cinst_def wsinst_def cert_inst_def
    by (auto simp: \<rho>0_def freeze_inst_def cert_typ_def has_sort_TFree_iff split: option.splits)
      (use class_le_refl in blast)+
  from prf_valid_tinst[OF p c0] show ?thesis by (simp add: th' pf)
qed

end


subsection \<open>Permutations of premises\<close>

lemma downto_nat:
  assumes "b \<le> a + 1" "0 \<le> b"
  shows "downto a b = map (\<lambda>l. integer_of_nat (nat_of_integer a - l)) [0..<nat_of_integer (a - b + 1)]"
proof -
  have "a - integer_of_nat l = integer_of_nat (nat_of_integer a - l)" if "l < nat_of_integer (a - b + 1)" for l
    using that assms by (simp add: integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq of_nat_diff
      less_eq_integer.rep_eq)
  then show ?thesis by (simp add: downto_map)
qed

context prf_sig
begin

lemma prf_ok_mk_AbsP:
  "(\<And>A. A \<in> set As \<Longrightarrow> e \<turnstile> A : propT) \<Longrightarrow> prf_ok ax H e (rev As @ Hs) q C \<Longrightarrow>
    prf_ok ax H e Hs (mk_AbsP As q) (list_implies As C)"
proof (induction As arbitrary: Hs)
  case (Cons A As)
  have "prf_ok ax H e (A # Hs) (mk_AbsP As q) (list_implies As C)"
    by (rule Cons.IH) (use Cons.prems in auto)
  with Cons.prems(1) show ?case by (simp add: mk_AbsP_def prf_ok.AbsP)
qed (simp add: mk_AbsP_def)

lemma prf_ok_proof_combP:
  "prf_ok ax H e Hs p (list_implies As C) \<Longrightarrow> list_all2 (\<lambda>q A. prf_ok ax H e Hs q A) qs As \<Longrightarrow>
    prf_ok ax H e Hs (proof_combP p qs) C"
proof (induction qs arbitrary: As p)
  case (Cons q qs)
  then obtain A As' where As: "As = A # As'" by (cases As) auto
  with Cons.prems have "prf_ok ax H e Hs (PAppp p q) (list_implies As' C)"
    by (auto intro: prf_ok.PAppp)
  with Cons.IH[of "PAppp p q" As'] Cons.prems(2) As show ?case by (simp add: proof_combP_def)
qed (simp add: proof_combP_def)

lemma prf_ok_PBound_nth:
  "i < length Hs \<Longrightarrow> e \<turnstile> Hs ! i : propT \<Longrightarrow> prf_ok ax H e Hs (PBound (integer_of_nat i)) (Hs ! i)"
  using prf_ok.PBound[of "integer_of_nat i" Hs e] by simp

lemma prf_ok_PBounds:
  assumes "length is = length As" "\<And>k. k < length As \<Longrightarrow> f k < length Hs \<and> Hs ! f k = As ! k"
    and "is = map (\<lambda>k. integer_of_nat (f k)) [0..<length As]" "\<And>A. A \<in> set Hs \<Longrightarrow> e \<turnstile> A : propT"
  shows "list_all2 (\<lambda>q A. prf_ok ax H e Hs q A) (map PBound is) As"
  unfolding assms(3) list_all2_conv_all_nth
proof (intro conjI allI impI)
  show "length (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<length As])) = length As" by simp
  fix k assume "k < length (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<length As]))"
  then have k: "k < length As" by simp
  from assms(2)[OF k] have fk: "f k < length Hs" "Hs ! f k = As ! k" by auto
  then have "e \<turnstile> Hs ! f k : propT" using assms(4) nth_mem by blast
  with prf_ok_PBound_nth[OF fk(1), of e ax H] fk k
  show "prf_ok ax H e Hs (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<length As]) ! k) (As ! k)" by simp
qed

end


lemma permute_index:
  fixes ps :: "'a list"
  assumes J: "J \<le> length ps" and M: "M \<le> length ps - J" and k: "k < length ps"
  defines "ps' \<equiv> take J ps @ drop M (drop J ps) @ take M (drop J ps)"
    and "f \<equiv> \<lambda>k. if k < J then length ps - 1 - k else if k < J + M then M - 1 - (k - J)
      else length ps - J - 1 - (k - J - M)"
  shows "f k < length ps' \<and> rev ps' ! f k = ps ! k"
proof -
  let ?n = "length ps"
  have l: "length ps' = ?n" using J M by (simp add: ps'_def)
  have fk: "f k < ?n" using k J M by (auto simp: f_def)
  have r: "rev ps' ! f k = ps' ! (?n - 1 - f k)" using fk l by (simp add: rev_nth)
  have "ps' ! (?n - 1 - f k) = ps ! k"
  proof (cases "k < J")
    case True
    then show ?thesis using k J by (simp add: ps'_def f_def nth_append)
  next
    case nJ: False
    show ?thesis
    proof (cases "k < J + M")
      case True
      then have i: "?n - 1 - f k = length (take J ps) + (length (drop M (drop J ps)) + (k - J))"
        using nJ k J M by (simp add: f_def)
      have "ps' ! (?n - 1 - f k) = take M (drop J ps) ! (k - J)"
        unfolding i ps'_def by (simp only: nth_append_length_plus)
      then show ?thesis using True nJ J M k by simp
    next
      case False
      then have i: "?n - 1 - f k = length (take J ps) + (k - J - M)" using nJ k J M by (simp add: f_def)
      have "ps' ! (?n - 1 - f k) = (drop M (drop J ps) @ take M (drop J ps)) ! (k - J - M)"
        unfolding i ps'_def by (simp only: nth_append_length_plus append.assoc)
      moreover have "k - (J + M) < length ps - (M + J)" using False k by linarith
      ultimately show ?thesis using False nJ J M k by (simp add: nth_append)
    qed
  qed
  with fk l r show ?thesis by simp
qed

lemma int_nat_minus: "integer_of_nat a - integer_of_nat b = integer_of_nat (a - b)" if "b \<le> a"
  using that by (simp add: integer_eq_iff integer_of_nat.rep_eq of_nat_diff)

lemma nat_int_minus1: "nat_of_integer (integer_of_nat a - 1) = a - 1"
  by (cases a) (simp_all add: nat_of_integer.rep_eq integer_of_nat.rep_eq)

lemma permute_downto:
  assumes J: "J \<le> n" and M: "M \<le> n - J"
  defines "f \<equiv> \<lambda>k. if k < J then n - 1 - k else if k < J + M then M - 1 - (k - J) else n - J - 1 - (k - J - M)"
  shows "downto (integer_of_nat n - 1) (integer_of_nat n - integer_of_nat J) @
      downto (integer_of_nat M - 1) 0 @ downto (integer_of_nat n - integer_of_nat J - 1) (integer_of_nat M) =
    map (\<lambda>k. integer_of_nat (f k)) [0..<n]"
proof -
  have u1: "[0..<n] = [0..<J] @ [J..<n]" using upt_add_eq_append[of 0 J "n - J"] J by simp
  have u2: "[J..<n] = [J..<J + M] @ [J + M..<n]" using upt_add_eq_append[of J "J + M" "n - J - M"] J M by simp
  have u: "[0..<n] = [0..<J] @ [J..<J + M] @ [J + M..<n]" by (simp add: u1 u2)
  have nj: "integer_of_nat n - integer_of_nat J = integer_of_nat (n - J)" by (rule int_nat_minus[OF J])
  have p1: "downto (integer_of_nat n - 1) (integer_of_nat n - integer_of_nat J) = map (\<lambda>k. integer_of_nat (f k)) [0..<J]"
  proof -
    have "downto (integer_of_nat n - 1) (integer_of_nat (n - J)) =
        map (\<lambda>l. integer_of_nat (nat_of_integer (integer_of_nat n - 1) - l))
          [0..<nat_of_integer (integer_of_nat n - 1 - integer_of_nat (n - J) + 1)]"
      by (rule downto_nat) (use J in \<open>simp_all add: less_eq_integer.rep_eq integer_of_nat.rep_eq of_nat_diff\<close>)
    moreover have "nat_of_integer (integer_of_nat n - 1 - integer_of_nat (n - J) + 1) = J"
      using J by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq of_nat_diff)
    ultimately show ?thesis using J by (simp add: nj nat_int_minus1 f_def)
  qed
  have p2: "downto (integer_of_nat M - 1) 0 = map (\<lambda>k. integer_of_nat (f k)) [J..<J + M]"
  proof -
    have "downto (integer_of_nat M - 1) 0 =
        map (\<lambda>l. integer_of_nat (nat_of_integer (integer_of_nat M - 1) - l)) [0..<nat_of_integer (integer_of_nat M - 1 - 0 + 1)]"
      by (rule downto_nat) (simp_all add: less_eq_integer.rep_eq integer_of_nat.rep_eq)
    moreover have "nat_of_integer (integer_of_nat M - 1 - 0 + 1) = M"
      by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq)
    moreover have "[J..<J + M] = map (\<lambda>l. J + l) [0..<M]" by (induction M) auto
    ultimately show ?thesis by (simp add: nat_int_minus1 f_def)
  qed
  have p3: "downto (integer_of_nat n - integer_of_nat J - 1) (integer_of_nat M) =
      map (\<lambda>k. integer_of_nat (f k)) [J + M..<n]"
  proof -
    have "downto (integer_of_nat (n - J) - 1) (integer_of_nat M) =
        map (\<lambda>l. integer_of_nat (nat_of_integer (integer_of_nat (n - J) - 1) - l))
          [0..<nat_of_integer (integer_of_nat (n - J) - 1 - integer_of_nat M + 1)]"
      by (rule downto_nat) (use M in \<open>simp_all add: less_eq_integer.rep_eq integer_of_nat.rep_eq of_nat_diff\<close>)
    moreover have "nat_of_integer (integer_of_nat (n - J) - 1 - integer_of_nat M + 1) = n - J - M"
      using M by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq of_nat_diff)
    moreover have "[J + M..<n] = map (\<lambda>l. J + M + l) [0..<n - J - M]"
    proof -
      have q: "[J + M..<J + M + q] = map (\<lambda>l. J + M + l) [0..<q]" for q by (induction q) auto
      have "J + M + (n - J - M) = n" using J M by simp
      with q[of "n - J - M"] show ?thesis by simp
    qed
    ultimately show ?thesis using J M by (simp add: nj nat_int_minus1 f_def)
  qed
  show ?thesis unfolding u by (simp add: p1 p2 p3)
qed

context prf_sig
begin

lemma prf_ok_permute:
  assumes p: "prf_ok ax H e [] pf (list_implies ps C)" and ty: "\<And>A. A \<in> set ps \<Longrightarrow> e \<turnstile> A : propT"
    and J: "jn \<le> length ps" and M: "mn \<le> length ps - jn"
  defines "ps' \<equiv> take jn ps @ drop mn (drop jn ps) @ take mn (drop jn ps)"
  shows "prf_ok ax H e [] (permute_prems_proof ps' (integer_of_nat jn) (integer_of_nat mn) pf) (list_implies ps' C)"
proof -
  let ?n = "length ps"
  define f where "f = (\<lambda>k. if k < jn then ?n - 1 - k else if k < jn + mn then mn - 1 - (k - jn)
    else ?n - jn - 1 - (k - jn - mn))"
  have l: "length ps' = ?n" using J M by (simp add: ps'_def)
  have sp: "set ps' = set ps"
  proof -
    have "set (drop mn (drop jn ps) @ take mn (drop jn ps)) = set (drop jn ps)"
      by (metis append_take_drop_id set_append Un_commute)
    then show ?thesis unfolding ps'_def by (metis append_take_drop_id set_append)
  qed
  have idx: "downto (integer_of_nat ?n - 1) (integer_of_nat ?n - integer_of_nat jn) @
      downto (integer_of_nat mn - 1) 0 @ downto (integer_of_nat ?n - integer_of_nat jn - 1) (integer_of_nat mn) =
    map (\<lambda>k. integer_of_nat (f k)) [0..<?n]"
    unfolding f_def by (rule permute_downto[OF J M])
  have "list_all2 (\<lambda>q A. prf_ok ax H e (rev ps') q A)
      (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n])) ps"
  proof (rule prf_ok_PBounds)
    show "f k < length (rev ps') \<and> rev ps' ! f k = ps ! k" if "k < length ps" for k
      using permute_index[OF J M that] by (simp add: ps'_def f_def)
  qed (use ty sp in auto)
  moreover have "prf_ok ax H e (rev ps') pf (list_implies ps C)" using prf_ok_append[OF p] by simp
  ultimately have "prf_ok ax H e (rev ps' @ []) (proof_combP pf (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n])))
      C"
    by (simp add: prf_ok_proof_combP)
  then have "prf_ok ax H e [] (mk_AbsP ps' (proof_combP pf (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))))
      (list_implies ps' C)"
    by (intro prf_ok_mk_AbsP) (use ty sp in auto)
  then show ?thesis unfolding permute_prems_proof_def Let_def l map_append[symmetric] idx .
qed

end


lemma mk_AbsP_map: "mk_AbsP (map f xs) p = mk_AbsP xs p"
  by (simp add: mk_AbsP_def foldr_map comp_def)

lemma permute_prems_proof_map: "permute_prems_proof (map f ps) j m p = permute_prems_proof ps j m p"
  by (simp add: permute_prems_proof_def mk_AbsP_map)

lemma map_proof_terms_mk_AbsP: "map_proof_terms f g (mk_AbsP xs p) = mk_AbsP xs (map_proof_terms f g p)"
  by (induction xs) (simp_all add: mk_AbsP_def)

lemma map_proof_terms_proof_combP:
  "map_proof_terms f g (proof_combP p qs) = proof_combP (map_proof_terms f g p) (map (map_proof_terms f g) qs)"
  by (induction qs arbitrary: p) (simp_all add: proof_combP_def)

lemma map_proof_terms_permute:
  "map_proof_terms f g (permute_prems_proof ps j m p) = permute_prems_proof ps j m (map_proof_terms f g p)"
  by (simp add: permute_prems_proof_def map_proof_terms_mk_AbsP map_proof_terms_proof_combP comp_def Let_def)

lemma permute_data_precise:
  assumes ok: "okT (permute_data j k rl) (th, prems', m)"
  defines "ps \<equiv> strip_imp_prems (th_prop rl)" and "C \<equiv> strip_imp_concl (th_prop rl)"
  assumes P: "th_prop rl = list_implies ps C"
  obtains J M where "j = integer_of_nat J" "m = integer_of_nat M" "J \<le> length ps" "M \<le> length ps - J"
    "prems' = take J ps @ drop M (drop J ps) @ take M (drop J ps)"
    "th = mk_rep (th_maxidx rl) (th_tpairs rl) (list_implies prems' C)"
proof -
  define J where "J = nat_of_integer j"
  have nr: "\<not> (j < 0 \<or> integer_of_nat (length ps) < j)"
    using ok by (auto simp: permute_data_def Let_def raiseW_def ps_def split: if_splits)
  then have jJ: "j = integer_of_nat J" "J \<le> length ps"
    by (simp_all add: J_def integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_integer.rep_eq
      nat_le_iff)
  define nj where "nj = length (drop J ps)"
  define mm where "mm = (if k < 0 then integer_of_nat nj + k else k)"
  have cs: "(m = mm \<and> (mm = 0 \<or> mm = integer_of_nat nj) \<and> prems' = ps \<and>
        th = mk_rep (th_maxidx rl) (th_tpairs rl) (th_prop rl)) \<or>
      (m = mm \<and> 0 < mm \<and> mm < integer_of_nat nj \<and>
        prems' = take J ps @ drop (nat_of_integer mm) (drop J ps) @ take (nat_of_integer mm) (drop J ps) \<and>
        th = mk_rep (th_maxidx rl) (th_tpairs rl) (list_implies prems' C))"
    using ok nr unfolding permute_data_def Let_def
    by (auto simp: returnW_def raiseW_def ps_def C_def J_def nj_def mm_def split: if_splits)
  from cs show thesis
  proof (elim disjE conjE)
    assume m: "m = mm" and "mm = 0" and p': "prems' = ps"
      and th: "th = mk_rep (th_maxidx rl) (th_tpairs rl) (th_prop rl)"
    with P show thesis by (intro that[OF jJ(1), of 0]) (simp_all add: jJ(2))
  next
    assume m: "m = mm" and "mm = integer_of_nat nj" and p': "prems' = ps"
      and th: "th = mk_rep (th_maxidx rl) (th_tpairs rl) (th_prop rl)"
    with P show thesis by (intro that[OF jJ(1), of nj]) (simp_all add: jJ(2) nj_def)
  next
    assume m: "m = mm" and mm: "0 < mm" "mm < integer_of_nat nj"
      and p': "prems' = take J ps @ drop (nat_of_integer mm) (drop J ps) @ take (nat_of_integer mm) (drop J ps)"
      and th: "th = mk_rep (th_maxidx rl) (th_tpairs rl) (list_implies prems' C)"
    have "mm = integer_of_nat (nat_of_integer mm)" "nat_of_integer mm \<le> length ps - J"
      using mm by (simp_all add: integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_integer.rep_eq
        nj_def)
    with m p' th show thesis by (intro that[OF jJ(1), of "nat_of_integer mm"]) (simp_all add: jJ(2))
  qed
qed

context prf_model
begin

theorem permute_prems_proof_valid:
  assumes ok: "okT (permute_data j k th0) (th, prems', m)"
    and p: "prf_valid ax H (th_tpairs th0) pf (th_prop th0)" and w: "wtp (th_prop th0)"
  shows "prf_valid ax H (th_tpairs th) (permute_prems_proof prems' j m pf) (th_prop th)"
proof -
  let ?ps = "strip_imp_prems (th_prop th0)" and ?C = "strip_imp_concl (th_prop th0)"
  have P: "th_prop th0 = list_implies ?ps ?C"
    by (rule list_implies_strip_imp[OF wtpD(2)[OF w, of "\<lambda>_. propT"]])
  obtain J M where jm: "j = integer_of_nat J" "m = integer_of_nat M" and JM: "J \<le> length ?ps" "M \<le> length ?ps - J"
    and p': "prems' = take J ?ps @ drop M (drop J ?ps) @ take M (drop J ?ps)"
    and th: "th = mk_rep (th_maxidx th0) (th_tpairs th0) (list_implies prems' ?C)"
    by (rule permute_data_precise[OF ok P])
  have wps: "wtp A" if "A \<in> set ?ps" for A
    using w that wtp_list_implies[where As = ?ps and As' = ?ps and B = ?C and B' = ?C] P by auto
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    let ?aps = "map (ap \<rho> \<sigma>) ?ps"
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> (th_prop th0))"
      by (rule prf_validD[OF p \<rho> \<sigma>]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    then have p0: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (list_implies ?aps (ap \<rho> \<sigma> ?C))"
      by (metis P ap_list_implies)
    have ty: "e \<turnstile> A : propT" if "A \<in> set ?aps" for A
      using that typing_ap_wtp[OF wps \<rho> \<sigma>] by auto
    from prf_ok_permute[OF p0 ty, of J M] JM
    have "prf_ok ax H e [] (permute_prems_proof (map (ap \<rho> \<sigma>) prems') (integer_of_nat J) (integer_of_nat M)
        (prf_ap \<rho> \<sigma> pf)) (list_implies (map (ap \<rho> \<sigma>) prems') (ap \<rho> \<sigma> ?C))"
      by (simp add: p' take_map drop_map)
    then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (permute_prems_proof prems' j m pf)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: th mk_rep_def jm permute_prems_proof_map prf_ap_def map_proof_terms_permute
        ap_list_implies)
  qed
qed

end

subsection \<open>The equality rules\<close>

text \<open>
  The closures of the equality axioms over their variables, in the order of
  \<open>Thm.forall_intr_vars\<close>, which \<open>Proofchecker.thm_of_proof\<close> uses for axioms and which the
  equality proofs of \<open>Proofterm\<close> instantiate:
\<close>

definition eq_names :: "name set" where
  "eq_names = {STR ''reflexive'', STR ''symmetric'', STR ''transitive'', STR ''equal_intr'', STR ''equal_elim'',
    STR ''abstract_rule'', STR ''combination''}"

definition eq_all :: "ptyp \<Rightarrow> pterm \<Rightarrow> pterm" where
  "eq_all T B = all_const T $ Abs STR ''x'' T B"

definition eq_closure :: "name \<Rightarrow> pterm" where
  "eq_closure a =
    (let aT = ax_aT; bT = ax_bT
     in if a = STR ''reflexive'' then eq_all aT (ax_eq aT (Bound 0) (Bound 0))
     else if a = STR ''symmetric'' then eq_all aT (eq_all aT (mk_implies (ax_eq aT (Bound 1) (Bound 0)) (ax_eq aT (Bound 0) (Bound 1))))
     else if a = STR ''transitive'' then
       eq_all aT (eq_all aT (eq_all aT (list_implies [ax_eq aT (Bound 2) (Bound 1), ax_eq aT (Bound 1) (Bound 0)]
         (ax_eq aT (Bound 2) (Bound 0)))))
     else if a = STR ''equal_intr'' then
       eq_all propT (eq_all propT (list_implies [mk_implies (Bound 1) (Bound 0), mk_implies (Bound 0) (Bound 1)]
         (ax_eq propT (Bound 1) (Bound 0))))
     else if a = STR ''equal_elim'' then
       eq_all propT (eq_all propT (list_implies [ax_eq propT (Bound 1) (Bound 0), Bound 1] (Bound 0)))
     else if a = STR ''abstract_rule'' then
       eq_all (aT \<rightarrow>\<^sub>T bT) (eq_all (aT \<rightarrow>\<^sub>T bT) (mk_implies (eq_all aT (ax_eq bT (Bound 2 $ Bound 0) (Bound 1 $ Bound 0)))
         (ax_eq (aT \<rightarrow>\<^sub>T bT) (Abs STR ''x'' aT (Bound 2 $ Bound 0)) (Abs STR ''x'' aT (Bound 1 $ Bound 0)))))
     else eq_all (aT \<rightarrow>\<^sub>T bT) (eq_all (aT \<rightarrow>\<^sub>T bT) (eq_all aT (eq_all aT
       (list_implies [ax_eq (aT \<rightarrow>\<^sub>T bT) (Bound 3) (Bound 2), ax_eq aT (Bound 1) (Bound 0)]
         (ax_eq bT (Bound 3 $ Bound 1) (Bound 2 $ Bound 0)))))))"

locale prf_eq = prf_model alg ar ctab close tyargs umem ufun uapp ulam ubool utrue ufalse tcon cls cval
  for alg ar ctab close tyargs and umem :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix \<open>\<in>\<^sub>u\<close> 50)
    and ufun uapp ulam ubool utrue ufalse tcon cls cval +
  fixes ax :: "pterm \<Rightarrow> bool"
  assumes eq_ok_ctab: "eq_ok"
    and eq_ax: "\<And>a. a \<in> eq_names \<Longrightarrow> ax (equality_axiom a)"
    and eq_close: "\<And>a. a \<in> eq_names \<Longrightarrow> close (equality_axiom a) = eq_closure a"
    and eq_tyargs: "\<And>a. a \<in> eq_names \<Longrightarrow> tyargs (equality_axiom a) = [((tvar_a, 0), []), ((tvar_b, 0), [])]"
begin

lemma typing_eq_const: "cert_typ alg ar T \<Longrightarrow> e \<turnstile> eq_const T : T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT"
proof -
  assume T: "cert_typ alg ar T"
  from eq_ok_ctab obtain v S where c: "ctab STR ''Pure.eq'' = Some (TVar v S \<rightarrow>\<^sub>T TVar v S \<rightarrow>\<^sub>T propT)"
    by (auto simp: eq_ok_def)
  have "const_typ_ok ctab STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT)"
    unfolding const_typ_ok_def using c by (auto intro!: exI[of _ "\<lambda>_ _. T"] simp: propT_def)
  then show ?thesis using T by (intro typing.Const) (simp_all add: cert_typ_fun)
qed

lemma tyinst_eq:
  "tyinst [((tvar_a, 0), []), ((tvar_b, 0), [])] [U, V] = (\<lambda>v S. if v = (tvar_a, 0) \<and> S = [] then U
    else if v = (tvar_b, 0) \<and> S = [] then V else TVar v S)"
  by (auto simp: fun_eq_iff tyinst_def tvar_a_def tvar_b_def)

lemma atom_prop_eq:
  "a \<in> eq_names \<Longrightarrow> atom_prop (equality_axiom a) [U, V] =
    inst (\<lambda>v S. if v = (tvar_a, 0) \<and> S = [] then U else if v = (tvar_b, 0) \<and> S = [] then V else TVar v S)
      (eq_closure a)"
  by (simp add: atom_prop_def eq_close eq_tyargs tyinst_eq)

lemma prf_ok_eq_axm:
  assumes "a \<in> eq_names" "cert_typ alg ar U" "cert_typ alg ar V"
    "e \<turnstile> atom_prop (equality_axiom a) [U, V] : propT"
  shows "prf_ok ax H e Hs (equality_axm a) (atom_prop (equality_axiom a) [U, V])"
  unfolding equality_axm_def
  by (rule prf_ok.PAxm[OF _ _ assms(4)]) (use assms in \<open>simp_all add: eq_ax atom_ok_def eq_tyargs\<close>)

lemma prf_ok_PAppt_beta:
  assumes "prf_ok ax H e Hs p (all_const U $ Abs x U B)" "e \<turnstile> t : U" "ann_ok t' t"
  shows "prf_ok ax H e Hs (PAppt p t') (subst_bound t B)"
proof -
  have pr: "prf_ok ax H e Hs (PAppt p t') (Abs x U B $ t)" by (rule prf_ok.PAppt[OF assms])
  have ty: "e \<turnstile> Abs x U B $ t : propT" by (rule prf_ok_typing[OF pr])
  then have "wt (Abs x U B $ t)" by (auto simp: wt_def)
  from betapply_conv[OF this] have c: "Abs x U B $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> subst_bound t B" by simp
  have red: "Abs x U B $ t \<rightarrow>\<^sub>\<beta> subst_bound t B" by (simp add: subst_bound_subst)
  from prf_ok.conv[OF pr c subject_reduction_beta[OF ty red]] show ?thesis .
qed

lemma cert_closed_typing: "e \<turnstile> t : T \<Longrightarrow> cert_typ alg ar T" if "\<And>e. e \<turnstile> t : T"
  using typing_cert[OF that[of "\<lambda>_. propT"]] by simp

theorem reflexive_proof_valid:
  assumes ok: "okT (reflexive (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "prf_valid ax H (th_tpairs th) reflexive_proof (th_prop th)"
proof -
  from ok obtain P where P: "ok (mk_equals (t, t)) P" and th: "th = mk_rep m [] P"
    by (auto simp: reflexive_def)
  have cT: "cert_typ alg ar T" using typing_cert[OF ty[of "\<lambda>_. propT"]] by simp
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    let ?U = "tsubst \<rho> T" and ?t = "ap \<rho> \<sigma> t"
    have cU: "cert_typ alg ar ?U" by (rule cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]])
    have ct: "closed ?t" using c \<sigma> by (simp add: closed_def)
    have tt: "e \<turnstile> ?t : ?U"
      using typing_closed[OF typing_ap_inst[OF ty cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] ct] .
    have a: "atom_prop (equality_axiom STR ''reflexive'') [?U, ?U] =
        all_const ?U $ Abs STR ''x'' ?U (eq_const ?U $ Bound 0 $ Bound 0)"
      by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def Let_def all_const_def)
    have "e\<langle>0:?U\<rangle> \<turnstile> eq_const ?U $ Bound 0 $ Bound 0 : propT"
      by (intro typing.App typing.Bound) (simp_all add: shift_def typing_eq_const[OF cU])
    then have "e \<turnstile> all_const ?U $ Abs STR ''x'' ?U (eq_const ?U $ Bound 0 $ Bound 0) : propT"
      using cU by (simp add: typing_all_const all_type_def cert_typ_fun)
    then have ax0: "prf_ok ax H e [] (equality_axm STR ''reflexive'')
        (all_const ?U $ Abs STR ''x'' ?U (eq_const ?U $ Bound 0 $ Bound 0))"
      using prf_ok_eq_axm[of "STR ''reflexive''" ?U ?U e H "[]"] cU by (simp add: a eq_names_def)
    from prf_ok_PAppt_beta[OF ax0 tt, of None]
    have "prf_ok ax H e [] reflexive_proof (eq_const ?U $ ?t $ ?t)"
      using ct by (simp add: reflexive_proof_def subst_bound_subst subst.simps)
    then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> reflexive_proof) (ap \<rho> \<sigma> (th_prop th))"
      using mk_equals_ok[OF P c ty] by (simp add: th mk_rep_def reflexive_proof_def equality_axm_def prf_ap_def)
  qed
qed

end

context prf_eq
begin

lemma prf_ok_PAxm_inv:
  "prf_ok ax H e Hs q \<phi> \<Longrightarrow> q = PAxm a A Us' \<Longrightarrow> \<exists>Us. ax A \<and> atom_ok A Us' Us \<and>
    atom_prop A Us \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi> \<and> e \<turnstile> atom_prop A Us : propT"
proof (induction rule: prf_ok.induct)
  case (conv e Hs q \<phi> \<psi>)
  then show ?case by (meson conv_trans)
qed auto

text \<open>The proofs that \<open>Proofterm.is_reflexive_proof\<close> recognizes are proofs of reflexivity, if the axiom
  of that name is reflexivity:\<close>

definition refl_ok :: "prf \<Rightarrow> bool" where
  "refl_ok p \<longleftrightarrow> (\<forall>A Ts t. p = PAppt (PAxm (STR ''Pure.reflexive'') A Ts) t \<longrightarrow> A = equality_axiom STR ''reflexive'')"

lemma refl_ok_map_proof_terms: "refl_ok p \<Longrightarrow> refl_ok (map_proof_terms f g p)"
  by (cases p rule: is_reflexive_proof.cases) (auto simp: refl_ok_def)

lemma eq_refl_closure:
  "atom_prop (equality_axiom STR ''reflexive'') [U, V] = all_const U $ Abs STR ''x'' U (eq_const U $ Bound 0 $ Bound 0)"
  by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def Let_def all_const_def)

lemma prf_ok_refl_inv:
  assumes "prf_ok ax H e Hs (PAppt (PAxm a (equality_axiom STR ''reflexive'') Ts) t') \<phi>"
  obtains U s where "\<phi> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const U $ s $ s" "e \<turnstile> s : U"
proof -
  obtain U f t where 1: "prf_ok ax H e Hs (PAxm a (equality_axiom STR ''reflexive'') Ts) (all_const U $ f)"
    "e \<turnstile> t : U" "f $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi>" "e \<turnstile> f $ t : propT"
    using prf_ok_PAppt_inv[OF assms HOL.refl] by blast
  obtain Us where 2: "atom_ok (equality_axiom STR ''reflexive'') Ts Us"
    "atom_prop (equality_axiom STR ''reflexive'') Us \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> all_const U $ f"
    "e \<turnstile> atom_prop (equality_axiom STR ''reflexive'') Us : propT"
    using prf_ok_PAxm_inv[OF 1(1) HOL.refl] by blast
  from 2(1) obtain U1 U2 where Us: "Us = [U1, U2]"
    by (auto simp: atom_ok_def eq_tyargs eq_names_def list_all2_Cons1)
  let ?B = "eq_const U1 $ Bound 0 $ Bound 0"
  have at2: "atom (all_const U1)" "atom (all_const U)" by (simp_all add: all_const_def)
  have w: "wt (all_const U1 \<degree>\<degree> [Abs STR ''x'' U1 ?B])" using 2(3) by (auto simp: wt_def Us eq_refl_closure)
  have c: "all_const U1 \<degree>\<degree> [Abs STR ''x'' U1 ?B] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> all_const U \<degree>\<degree> [f]" using 2(2) by (simp add: Us eq_refl_closure)
  from conv_atom_apps_inv[OF at2 w c]
  have UU: "U1 = U" and fA: "Abs STR ''x'' U1 ?B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> f" by (simp_all add: all_const_def)
  have tA: "e \<turnstile> Abs STR ''x'' U ?B : U \<rightarrow>\<^sub>T propT" using 2(3) UU by (auto simp: all_const_def Us eq_refl_closure)
  have "(sup beta eta)\<^sup>*\<^sup>* (Abs STR ''x'' U ?B $ t) (?B[t/0])"
    by (rule r_into_rtranclp, rule sup2I1, rule beta.beta)
  moreover have "wt (Abs STR ''x'' U ?B $ t)" using tA 1(2) UU by (auto simp: wt_def)
  ultimately have "Abs STR ''x'' U ?B $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?B[t/0]" by (rule beta_eta_conv)
  moreover have "Abs STR ''x'' U ?B $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> f $ t"
    using tA 1(2,4) fA UU by (intro conv_App) (auto simp: wt_def)
  ultimately have "\<phi> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?B[t/0]" using 1(3) by (meson conv_sym conv_trans)
  then have "\<phi> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const U $ t $ t" by (simp add: UU subst.simps)
  from this 1(2) show thesis by (rule that)
qed

lemma conv_eq_args:
  assumes "wt (eq_const T $ t $ u)" "eq_const T $ t $ u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const U $ s $ s'"
  shows "T = U" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s'"
proof -
  have at: "atom (eq_const T)" "atom (eq_const U)" by simp_all
  from conv_atom_apps_inv[of "eq_const T" "eq_const U" "[t, u]" "[s, s']"] at assms
  show "T = U" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s'" by simp_all
qed

theorem symmetric_proof_valid:
  assumes ok: "okT (symmetric th0) th" and p: "prf_valid ax H (th_tpairs th0) pf (th_prop th0)"
    and w: "wtp (th_prop th0)" and rf: "refl_ok pf"
  shows "prf_valid ax H (th_tpairs th) (symmetric_proof pf) (th_prop th)"
proof -
  from ok obtain c t u where P: "th_prop th0 = c $ t $ u" and d: "dest_eq_fun (th_prop th0) \<noteq> None"
    and th: "th = mk_rep (th_maxidx th0) (th_tpairs th0) (c $ u $ t)"
    by (auto simp: symmetric_def returnW_def raiseW_def split: pterm.splits option.splits)
  then obtain T' where "dest_eq_fun (th_prop th0) = Some (T', t, u)"
    by (cases "th_prop th0" rule: dest_eq_fun.cases) (auto split: if_splits)
  then have d': "dest_eq_any (th_prop th0) = Some (t, u)" by (rule dest_eq_any_dest_eq_fun)
  obtain T where P': "th_prop th0 = eq_const T $ t $ u" and ct: "closed t" "closed u"
    and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T"
    using dest_eq_any_wtp[OF eq_ok_ctab d' w] by blast
  have cc: "c = eq_const T" using P P' by simp
  have cT: "cert_typ alg ar T" using typing_cert[OF ty(1)[of "\<lambda>_. propT"]] by simp
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    let ?U = "tsubst \<rho> T" and ?t = "ap \<rho> \<sigma> t" and ?u = "ap \<rho> \<sigma> u"
    have cU: "cert_typ alg ar ?U" by (rule cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]])
    have cl: "closed ?t" "closed ?u" using ct \<sigma> by (simp_all add: closed_def)
    have tt: "e \<turnstile> ?t : ?U" "e \<turnstile> ?u : ?U"
      using typing_closed[OF typing_ap_inst[OF ty(1) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] cl(1)]
        typing_closed[OF typing_ap_inst[OF ty(2) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] cl(2)] by simp_all
    have teq: "e \<turnstile> eq_const ?U $ a $ b : propT" if "e \<turnstile> a : ?U" "e \<turnstile> b : ?U" for a b
      using that typing_eq_const[OF cU] by blast
    have pr: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (eq_const ?U $ ?t $ ?u)"
      using prf_validD[OF p \<rho> \<sigma>, of e] sol th by (simp add: mk_rep_def P' ap_def)
    have goal: "ap \<rho> \<sigma> (th_prop th) = eq_const ?U $ ?u $ ?t" by (simp add: th mk_rep_def cc ap_def)
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (symmetric_proof pf)) (ap \<rho> \<sigma> (th_prop th))"
    proof (cases "is_reflexive_proof pf")
      case True
      then obtain A Ts t' where pf: "pf = PAppt (PAxm (STR ''Pure.reflexive'') A Ts) t'"
        by (cases pf rule: is_reflexive_proof.cases) auto
      with rf have A: "A = equality_axiom STR ''reflexive''" by (simp add: refl_ok_def)
      from pr obtain U s where cv: "eq_const ?U $ ?t $ ?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const U $ s $ s" "e \<turnstile> s : U"
        by (auto simp: pf A prf_ap_def elim!: prf_ok_refl_inv)
      have we: "wt (eq_const ?U $ ?t $ ?u)" using teq[OF tt] by (auto simp: wt_def)
      from conv_eq_args[OF we cv(1)] have "?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" "?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" by simp_all
      then have tu: "?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?u" by (meson conv_sym conv_trans)
      have "eq_const ?U $ ?t $ ?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const ?U $ ?u $ ?t"
      proof -
        have w2: "wt (eq_const ?U $ ?u $ ?t)" using teq[OF tt(2,1)] by (auto simp: wt_def)
        have w3: "wt (eq_const ?U $ ?t)" and w4: "wt (eq_const ?U $ ?u)"
          using wt_AppD[OF we] wt_AppD[OF w2] by simp_all
        have "eq_const ?U $ ?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const ?U $ ?u" by (rule conv_App[OF w3 w4 conv_refl tu])
        then show ?thesis by (rule conv_App[OF we w2 _ conv_sym[OF tu]])
      qed
      from prf_ok.conv[OF pr this teq[OF tt(2,1)]] True
      show ?thesis by (simp add: symmetric_proof_def goal)
    next
      case False
      let ?B = "mk_implies (eq_const ?U $ Bound 1 $ Bound 0) (eq_const ?U $ Bound 0 $ Bound 1)"
      have a: "atom_prop (equality_axiom STR ''symmetric'') [?U, ?U] =
          all_const ?U $ Abs STR ''x'' ?U (all_const ?U $ Abs STR ''x'' ?U ?B)"
        by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def Let_def all_const_def
          mk_implies_def implies_def)
      have tB: "e\<langle>0:?U\<rangle>\<langle>0:?U\<rangle> \<turnstile> ?B : propT"
        using cU by (auto simp: mk_implies_def typing_implies shift_def typing_eq_const[OF cU] cert_imp_type)
      then have "e \<turnstile> all_const ?U $ Abs STR ''x'' ?U (all_const ?U $ Abs STR ''x'' ?U ?B) : propT"
        using cU by (simp add: typing_all_const all_type_def cert_typ_fun)
      then have ax0: "prf_ok ax H e [] (equality_axm STR ''symmetric'')
          (all_const ?U $ Abs STR ''x'' ?U (all_const ?U $ Abs STR ''x'' ?U ?B))"
        using prf_ok_eq_axm[of "STR ''symmetric''" ?U ?U e H "[]"] cU by (simp add: a eq_names_def)
      from prf_ok_PAppt_beta[OF ax0 tt(1), of None]
      have "prf_ok ax H e [] (PAppt (equality_axm STR ''symmetric'') None)
          (all_const ?U $ Abs STR ''x'' ?U (mk_implies (eq_const ?U $ ?t $ Bound 0) (eq_const ?U $ Bound 0 $ ?t)))"
        using cl by (simp add: subst_bound_subst subst.simps all_const_def mk_implies_def implies_def incr_bv_closed
          closed_def)
      from prf_ok_PAppt_beta[OF this tt(2), of None]
      have "prf_ok ax H e [] (PAppt (PAppt (equality_axm STR ''symmetric'') None) None)
          (mk_implies (eq_const ?U $ ?t $ ?u) (eq_const ?U $ ?u $ ?t))"
        using cl by (simp add: subst_bound_subst subst.simps mk_implies_def implies_def closed_subst_id)
      from prf_ok.PAppp[OF this[unfolded mk_implies_def] pr] False
      show ?thesis
        by (simp add: symmetric_proof_def goal prf_ap_def equality_axm_def)
    qed
  qed
qed

end

context prf_eq
begin

lemma is_reflexive_proof_map: "is_reflexive_proof (map_proof_terms f g p) \<longleftrightarrow> is_reflexive_proof p"
proof (cases p)
  case (PAppt q t)
  then show ?thesis
  proof (cases q)
    case (PThm x)
    then show ?thesis using PAppt by (cases x) simp
  qed simp_all
next
  case (PThm x)
  then show ?thesis by (cases x) simp
qed simp_all

lemma prf_ok_refl_conv:
  assumes "prf_ok ax H e [] p (eq_const U $ t $ u)" "is_reflexive_proof p" "refl_ok p"
    "e \<turnstile> t : U" "e \<turnstile> u : U" "cert_typ alg ar U"
  shows "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u"
proof -
  obtain A Ts t' where pf: "p = PAppt (PAxm (STR ''Pure.reflexive'') A Ts) t'"
    using assms(2) by (cases p rule: is_reflexive_proof.cases) auto
  with assms(3) have A: "A = equality_axiom STR ''reflexive''" by (simp add: refl_ok_def)
  from assms(1) obtain V s where cv: "eq_const U $ t $ u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const V $ s $ s"
    by (auto simp: pf A elim!: prf_ok_refl_inv)
  have "wt (eq_const U $ t $ u)" using assms(4,5) typing_eq_const[OF assms(6)] by (auto simp: wt_def)
  from conv_eq_args[OF this cv] show ?thesis by (meson conv_sym conv_trans)
qed

lemma conv_eq_cong:
  assumes "e \<turnstile> t : U" "e \<turnstile> u : U" "e \<turnstile> t' : U" "e \<turnstile> u' : U" "cert_typ alg ar U"
    "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u'"
  shows "eq_const U $ t $ u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const U $ t' $ u'"
proof -
  have tc: "e \<turnstile> eq_const U : U \<rightarrow>\<^sub>T U \<rightarrow>\<^sub>T propT" by (rule typing_eq_const[OF assms(5)])
  have w: "wt (eq_const U $ t $ u)" "wt (eq_const U $ t' $ u')" "wt (eq_const U $ t)" "wt (eq_const U $ t')"
    using assms(1-4) tc by (auto simp: wt_def)
  have "eq_const U $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const U $ t'" by (rule conv_App[OF w(3,4) conv_refl assms(6)])
  then show ?thesis by (rule conv_App[OF w(1,2) _ assms(7)])
qed

theorem transitive_proof_valid:
  assumes ok: "okT (transitive th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and r1: "refl_ok pf1" and r2: "refl_ok pf2"
    and u0: "dest_eq_any (th_prop th1) = Some (t0, u0)"
  shows "prf_valid ax H (th_tpairs th) (transitive_proof U u0 pf1 pf2) (th_prop th)"
proof -
  from ok obtain c x y T t1 u u' t2 where P1: "th_prop th1 = c $ x $ y" and d1: "dest_eq (th_prop th1) = Some (T, t1, u)"
    and d2: "dest_eq_any (th_prop th2) = Some (u', t2)" and a: "aconv_term u u'"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) (c $ t1 $ t2)"
    by (auto simp: transitive_def returnW_def raiseW_def split: pterm.splits option.splits prod.splits if_splits)
  have d1': "dest_eq_any (th_prop th1) = Some (t1, u)" by (rule dest_eq_any_dest_eq[OF d1])
  have uu: "u0 = u" using u0 d1' by simp
  obtain A where P1': "th_prop th1 = eq_const A $ t1 $ u" and c1: "closed t1" "closed u"
    and ty1: "\<And>e. e \<turnstile> t1 : A" "\<And>e. e \<turnstile> u : A"
    using dest_eq_any_wtp[OF eq_ok_ctab d1' w1] by blast
  obtain B where P2': "th_prop th2 = eq_const B $ u' $ t2" and c2: "closed u'" "closed t2"
    and ty2: "\<And>e. e \<turnstile> u' : B" "\<And>e. e \<turnstile> t2 : B"
    using dest_eq_any_wtp[OF eq_ok_ctab d2 w2] by blast
  have AB: "A = B" using typing_aconv[OF a ty1(2)] ty2(1) typing_unique by metis
  have cc: "c = eq_const A" using P1 P1' by simp
  have cA: "cert_typ alg ar A" using typing_cert[OF ty1(1)[of "\<lambda>_. propT"]] by simp
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have sol': "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "(t, u) \<in> set (th_tpairs th1) \<union> set (th_tpairs th2)" for t u
      by (rule sol_union_tpairs[OF _ that]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    let ?U = "tsubst \<rho> A"
    have cU: "cert_typ alg ar ?U" by (rule cert_typ_tsubst[OF cA cinstD(2)[OF \<rho>]])
    have cl: "closed (ap \<rho> \<sigma> s)" if "closed s" for s using that \<sigma> by (simp add: closed_def)
    have tt: "e \<turnstile> ap \<rho> \<sigma> s : ?U" if "closed s" "\<And>e. e \<turnstile> s : A" for s e
      using typing_closed[OF typing_ap_inst[OF that(2) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] cl[OF that(1)]] .
    note t1 = tt[OF c1(1) ty1(1)] and tu = tt[OF c1(2) ty1(2)]
      and tu' = tt[OF c2(1)] and t2 = tt[OF c2(2)]
    have tu'': "e \<turnstile> ap \<rho> \<sigma> u' : ?U" for e using tu' ty2(1) AB by simp
    have t2': "e \<turnstile> ap \<rho> \<sigma> t2 : ?U" for e using t2 ty2(2) AB by simp
    have teq: "e \<turnstile> eq_const ?U $ a $ b : propT" if "e \<turnstile> a : ?U" "e \<turnstile> b : ?U" for a b e
      using that typing_eq_const[OF cU] by blast
    have uu': "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" by (blast intro: aconv_term_conv aconv_term_ap a)
    have pr1: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf1) (eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> u)"
      using prf_validD[OF p1 \<rho> \<sigma> sol', of e] by (simp add: P1' ap_def)
    have pr2: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf2) (eq_const ?U $ ap \<rho> \<sigma> u' $ ap \<rho> \<sigma> t2)"
      using prf_validD[OF p2 \<rho> \<sigma> sol', of e] by (simp add: P2' ap_def AB)
    have goal: "ap \<rho> \<sigma> (th_prop th) = eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> t2" by (simp add: th mk_rep_def cc ap_def)
    have rf: "is_reflexive_proof (prf_ap \<rho> \<sigma> p) \<longleftrightarrow> is_reflexive_proof p" for p
      unfolding prf_ap_def by (rule is_reflexive_proof_map)
    have rk: "refl_ok (prf_ap \<rho> \<sigma> p)" if "refl_ok p" for p
      using refl_ok_map_proof_terms[OF that] by (simp add: prf_ap_def)
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (transitive_proof U u0 pf1 pf2)) (ap \<rho> \<sigma> (th_prop th))"
    proof (cases "is_reflexive_proof pf1")
      case True
      have "ap \<rho> \<sigma> t1 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
        by (rule prf_ok_refl_conv[OF pr1 _ rk[OF r1] t1 tu cU]) (simp add: rf True)
      then have "ap \<rho> \<sigma> u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t1" using uu' by (meson conv_sym conv_trans)
      from conv_eq_cong[OF tu'' t2' t1 t2' cU this conv_refl]
      have "eq_const ?U $ ap \<rho> \<sigma> u' $ ap \<rho> \<sigma> t2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> t2" .
      from prf_ok.conv[OF pr2 this teq[OF t1 t2']] True show ?thesis
        by (simp add: transitive_proof_def goal)
    next
      case nr1: False
      show ?thesis
      proof (cases "is_reflexive_proof pf2")
        case True
        have "ap \<rho> \<sigma> u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t2"
          by (rule prf_ok_refl_conv[OF pr2 _ rk[OF r2] tu'' t2' cU]) (simp add: rf True)
        then have "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t2" using uu' by (meson conv_trans)
        from conv_eq_cong[OF t1 tu t1 t2' cU conv_refl this]
        have "eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> t2" .
        from prf_ok.conv[OF pr1 this teq[OF t1 t2']] True nr1 show ?thesis
          by (simp add: transitive_proof_def goal)
      next
        case nr2: False
        let ?B = "list_implies [eq_const ?U $ Bound 2 $ Bound 1, eq_const ?U $ Bound 1 $ Bound 0]
          (eq_const ?U $ Bound 2 $ Bound 0)"
        let ?ax = "all_const ?U $ Abs STR ''x'' ?U (all_const ?U $ Abs STR ''x'' ?U (all_const ?U $ Abs STR ''x'' ?U ?B))"
        have a: "atom_prop (equality_axiom STR ''transitive'') [?U, ?U] = ?ax"
          by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def Let_def all_const_def
            mk_implies_def implies_def)
        have "e\<langle>0:?U\<rangle>\<langle>0:?U\<rangle>\<langle>0:?U\<rangle> \<turnstile> ?B : propT"
          using cU by (auto simp: typing_implies shift_def typing_eq_const[OF cU] cert_imp_type)
        then have "e \<turnstile> ?ax : propT" using cU by (simp add: typing_all_const all_type_def cert_typ_fun)
        then have ax0: "prf_ok ax H e [] (equality_axm STR ''transitive'') ?ax"
          using prf_ok_eq_axm[of "STR ''transitive''" ?U ?U e H "[]"] cU by (simp add: a eq_names_def)
        let ?ann = "if U = propT then Some (remove_types u0) else None"
        have an: "ann_ok (map_option (ap \<rho> \<sigma>) ?ann) (ap \<rho> \<sigma> u)"
          using erase_ap_cong[of "remove_types u" u \<rho> \<sigma>] by (simp add: uu)
        from prf_ok_PAppt_beta[OF ax0 t1, of None]
        have "prf_ok ax H e [] (PAppt (equality_axm STR ''transitive'') None)
            (all_const ?U $ Abs STR ''x'' ?U (all_const ?U $ Abs STR ''x'' ?U
              (list_implies [eq_const ?U $ ap \<rho> \<sigma> t1 $ Bound 1, eq_const ?U $ Bound 1 $ Bound 0]
                (eq_const ?U $ ap \<rho> \<sigma> t1 $ Bound 0))))"
          using cl[OF c1(1)] by (simp add: subst_bound_subst subst.simps all_const_def implies_def incr_bv_closed closed_def)
        from prf_ok_PAppt_beta[OF this tu an]
        have "prf_ok ax H e [] (PAppt (PAppt (equality_axm STR ''transitive'') None) (map_option (ap \<rho> \<sigma>) ?ann))
            (all_const ?U $ Abs STR ''x'' ?U
              (list_implies [eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> u, eq_const ?U $ ap \<rho> \<sigma> u $ Bound 0]
                (eq_const ?U $ ap \<rho> \<sigma> t1 $ Bound 0)))"
          using cl[OF c1(1)] cl[OF c1(2)]
          by (simp add: subst_bound_subst subst.simps all_const_def implies_def incr_bv_closed closed_def closed_subst_id)
        from prf_ok_PAppt_beta[OF this t2', of None]
        have ax3: "prf_ok ax H e [] (PAppt (PAppt (PAppt (equality_axm STR ''transitive'') None) (map_option (ap \<rho> \<sigma>) ?ann)) None)
            (list_implies [eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> u, eq_const ?U $ ap \<rho> \<sigma> u $ ap \<rho> \<sigma> t2]
              (eq_const ?U $ ap \<rho> \<sigma> t1 $ ap \<rho> \<sigma> t2))"
          using cl[OF c1(1)] cl[OF c1(2)] cl[OF c2(2)]
          by (simp add: subst_bound_subst subst.simps implies_def closed_subst_id)
        have "eq_const ?U $ ap \<rho> \<sigma> u' $ ap \<rho> \<sigma> t2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const ?U $ ap \<rho> \<sigma> u $ ap \<rho> \<sigma> t2"
          by (rule conv_eq_cong[OF tu'' t2' tu t2' cU conv_sym[OF uu'] conv_refl])
        from prf_ok.conv[OF pr2 this teq[OF tu t2']]
        have pr2': "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf2) (eq_const ?U $ ap \<rho> \<sigma> u $ ap \<rho> \<sigma> t2)" .
        from prf_ok.PAppp[OF prf_ok.PAppp[OF ax3[unfolded list_implies.simps] pr1] pr2'] nr1 nr2
        show ?thesis
          by (cases "U = propT") (simp_all add: transitive_proof_def goal prf_ap_def equality_axm_def implies_def)
      qed
    qed
  qed
qed

end

context prf_eq
begin

lemma subst_implies [simp]: "subst implies s k = implies"
  by (simp add: implies_def)

lemma ann_ok_remove_types: "ann_ok (Some (ap \<rho> \<sigma> (remove_types A))) (ap \<rho> \<sigma> A)"
  using erase_ap_cong[of "remove_types A" A \<rho> \<sigma>] by simp

lemma prf_ok_eq_axm_prop2:
  assumes "a \<in> eq_names" "atom_prop (equality_axiom a) [propT, propT] = all_const propT $ Abs STR ''x'' propT
      (all_const propT $ Abs STR ''x'' propT B)"
    "e\<langle>0:propT\<rangle>\<langle>0:propT\<rangle> \<turnstile> B : propT" "e \<turnstile> A1 : propT" "e \<turnstile> A2 : propT" "closed A1"
    "ann_ok t1 A1" "ann_ok t2 A2"
  shows "prf_ok ax H e [] (PAppt (PAppt (equality_axm a) t1) t2) (subst (subst B A1 1) A2 0)"
proof -
  have "e \<turnstile> all_const propT $ Abs STR ''x'' propT (all_const propT $ Abs STR ''x'' propT B) : propT"
    using assms(3) by (simp add: typing_all_const all_type_def cert_typ_fun)
  then have ax0: "prf_ok ax H e [] (equality_axm a) (all_const propT $ Abs STR ''x'' propT
      (all_const propT $ Abs STR ''x'' propT B))"
    using prf_ok_eq_axm[OF assms(1), of propT propT e H "[]"] assms(2) by simp
  from prf_ok_PAppt_beta[OF ax0 assms(4,7)]
  have "prf_ok ax H e [] (PAppt (equality_axm a) t1) (all_const propT $ Abs STR ''x'' propT (B[A1/1]))"
    using assms(6) by (simp add: subst_bound_subst subst.simps all_const_def incr_bv_closed closed_def)
  from prf_ok_PAppt_beta[OF this assms(5,8)] show ?thesis by (simp add: subst_bound_subst)
qed

lemma conv_implies_cong:
  assumes "e \<turnstile> A : propT" "e \<turnstile> B : propT" "e \<turnstile> A' : propT" "e \<turnstile> B' : propT"
    "A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> A'" "B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> B'"
  shows "implies $ A $ B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> implies $ A' $ B'"
proof -
  have "e \<turnstile> implies $ A $ B : propT" "e \<turnstile> implies $ A' $ B' : propT"
    using assms(1-4) by (simp_all add: typing_implies cert_imp_type)
  then have w0: "wt (implies $ A $ B)" "wt (implies $ A' $ B')" by (auto simp: wt_def)
  then have w: "wt (implies $ A $ B)" "wt (implies $ A' $ B')" "wt (implies $ A)" "wt (implies $ A')"
    using wt_AppD by blast+
  have "implies $ A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> implies $ A'" by (rule conv_App[OF w(3,4) conv_refl assms(5)])
  then show ?thesis by (rule conv_App[OF w(1,2) _ assms(6)])
qed

theorem equal_intr_proof_valid:
  assumes ok: "okT (equal_intr th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
  shows "prf_valid ax H (th_tpairs th) (equal_intr_proof A B pf1 pf2) (th_prop th)"
proof -
  from ok obtain A0 B0 B' A' P where d1: "dest_imp (th_prop th1) = Some (A0, B0)" and d2: "dest_imp (th_prop th2) = Some (B', A')"
    and a: "aconv_term A0 A'" "aconv_term B0 B'" and mk: "ok (mk_equals (A0, B0)) P"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) P"
    by (auto simp: equal_intr_def returnW_def raiseW_def split: option.splits if_splits prod.splits)
  note dw1 = dest_imp_wtp[OF d1 w1] and dw2 = dest_imp_wtp[OF d2 w2]
  have AB: "A0 = A" "B0 = B" using dw1(1) P1 by simp_all
  have P: "P = eq_const propT $ A $ B" using mk_equals_ok[OF mk wtpD(1)[OF dw1(2)] wtpD(2)[OF dw1(2)]] AB by simp
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have sol': "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "(t, u) \<in> set (th_tpairs th1) \<union> set (th_tpairs th2)" for t u
      by (rule sol_union_tpairs[OF _ that]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    have ty: "e \<turnstile> ap \<rho> \<sigma> X : propT" if "wtp X" for X by (rule typing_ap_wtp[OF that \<rho> \<sigma>])
    have cl: "closed (ap \<rho> \<sigma> X)" if "wtp X" for X using wtpD(1)[OF that] \<sigma> by (simp add: closed_def)
    have wA: "wtp A" and wB: "wtp B" using dw1(2,3) AB by simp_all
    let ?A = "ap \<rho> \<sigma> A" and ?B = "ap \<rho> \<sigma> B"
    let ?C = "list_implies [mk_implies (Bound 1) (Bound 0), mk_implies (Bound 0) (Bound 1)] (eq_const propT $ Bound 1 $ Bound 0)"
    have a2: "atom_prop (equality_axiom STR ''equal_intr'') [propT, propT] =
        all_const propT $ Abs STR ''x'' propT (all_const propT $ Abs STR ''x'' propT ?C)"
      by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def Let_def all_const_def
        mk_implies_def implies_def propT_def)
    have tC: "e\<langle>0:propT\<rangle>\<langle>0:propT\<rangle> \<turnstile> ?C : propT"
      by (auto simp: mk_implies_def typing_implies shift_def typing_eq_const cert_imp_type)
    from prf_ok_eq_axm_prop2[OF _ a2 tC ty[OF wA] ty[OF wB] cl[OF wA] ann_ok_remove_types ann_ok_remove_types]
    have ax2: "prf_ok ax H e [] (PAppt (PAppt (equality_axm STR ''equal_intr'') (Some (ap \<rho> \<sigma> (remove_types A))))
        (Some (ap \<rho> \<sigma> (remove_types B))))
        (implies $ (implies $ ?A $ ?B) $ (implies $ (implies $ ?B $ ?A) $ (eq_const propT $ ?A $ ?B)))"
      using cl[OF wA] cl[OF wB] by (simp add: eq_names_def subst.simps mk_implies_def closed_subst_id)
    have pr1: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf1) (implies $ ?A $ ?B)"
      using prf_validD[OF p1 \<rho> \<sigma> sol', of e] dw1(1) AB by (simp add: ap_def)
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf2) (implies $ ap \<rho> \<sigma> B' $ ap \<rho> \<sigma> A')"
      using prf_validD[OF p2 \<rho> \<sigma> sol', of e] dw2(1) by (simp add: ap_def)
    moreover have "implies $ ap \<rho> \<sigma> B' $ ap \<rho> \<sigma> A' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> implies $ ?B $ ?A"
      by (rule conv_implies_cong[OF ty[OF dw2(2)] ty[OF dw2(3)] ty[OF wB] ty[OF wA]])
        (use a AB in \<open>blast intro: aconv_term_conv aconv_term_ap conv_sym\<close>)+
    ultimately have pr2: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf2) (implies $ ?B $ ?A)"
      by (rule prf_ok.conv) (simp add: typing_implies ty[OF wA] ty[OF wB] cert_imp_type)
    from prf_ok.PAppp[OF prf_ok.PAppp[OF ax2 pr1] pr2]
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (equal_intr_proof A B pf1 pf2)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: equal_intr_proof_def th mk_rep_def P prf_ap_def equality_axm_def ap_def)
  qed
qed

theorem equal_elim_proof_valid:
  assumes ok: "okT (equal_elim th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
  shows "prf_valid ax H (th_tpairs th) (equal_elim_proof A B pf1 pf2) (th_prop th)"
proof -
  from ok obtain A0 B0 where d: "dest_eq_any (th_prop th1) = Some (A0, B0)" and a: "aconv_term (th_prop th2) A0"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) B0"
    by (auto simp: equal_elim_def returnW_def raiseW_def split: option.splits if_splits)
  obtain T where P: "th_prop th1 = eq_const T $ A0 $ B0" and c: "closed A0" "closed B0"
    and ty0: "\<And>e. e \<turnstile> A0 : T" "\<And>e. e \<turnstile> B0 : T"
    using dest_eq_any_wtp[OF eq_ok_ctab d w1] by blast
  have AB: "A0 = A" "B0 = B" using P P1 by simp_all
  have T: "T = propT" using typing_aconv[OF a wtpD(2)[OF w2]] ty0(1) typing_unique by metis
  have wA: "wtp A" and wB: "wtp B" using c ty0 T AB by (auto intro: wtpI)
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have sol': "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "(t, u) \<in> set (th_tpairs th1) \<union> set (th_tpairs th2)" for t u
      by (rule sol_union_tpairs[OF _ that]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    have ty: "e \<turnstile> ap \<rho> \<sigma> X : propT" if "wtp X" for X by (rule typing_ap_wtp[OF that \<rho> \<sigma>])
    have cl: "closed (ap \<rho> \<sigma> X)" if "wtp X" for X using wtpD(1)[OF that] \<sigma> by (simp add: closed_def)
    let ?A = "ap \<rho> \<sigma> A" and ?B = "ap \<rho> \<sigma> B"
    let ?C = "list_implies [eq_const propT $ Bound 1 $ Bound 0, Bound 1] (Bound 0)"
    have a2: "atom_prop (equality_axiom STR ''equal_elim'') [propT, propT] =
        all_const propT $ Abs STR ''x'' propT (all_const propT $ Abs STR ''x'' propT ?C)"
      by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def Let_def all_const_def
        mk_implies_def implies_def propT_def)
    have tC: "e\<langle>0:propT\<rangle>\<langle>0:propT\<rangle> \<turnstile> ?C : propT"
      by (auto simp: typing_implies shift_def typing_eq_const cert_imp_type)
    from prf_ok_eq_axm_prop2[OF _ a2 tC ty[OF wA] ty[OF wB] cl[OF wA] ann_ok_remove_types ann_ok_remove_types]
    have ax2: "prf_ok ax H e [] (PAppt (PAppt (equality_axm STR ''equal_elim'') (Some (ap \<rho> \<sigma> (remove_types A))))
        (Some (ap \<rho> \<sigma> (remove_types B))))
        (implies $ (eq_const propT $ ?A $ ?B) $ (implies $ ?A $ ?B))"
      using cl[OF wA] cl[OF wB] by (simp add: eq_names_def subst.simps closed_subst_id)
    have pr1: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf1) (eq_const propT $ ?A $ ?B)"
      using prf_validD[OF p1 \<rho> \<sigma> sol', of e] P AB T by (simp add: ap_def)
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf2) (ap \<rho> \<sigma> (th_prop th2))"
      by (rule prf_validD[OF p2 \<rho> \<sigma>]) (use sol' in auto)
    moreover have "ap \<rho> \<sigma> (th_prop th2) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?A"
      using a AB by (blast intro: aconv_term_conv aconv_term_ap)
    ultimately have pr2: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf2) ?A" by (rule prf_ok.conv) (rule ty[OF wA])
    from prf_ok.PAppp[OF prf_ok.PAppp[OF ax2 pr1] pr2]
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (equal_elim_proof A B pf1 pf2)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: equal_elim_proof_def th mk_rep_def AB prf_ap_def equality_axm_def)
  qed
qed

end

lemma subst_Bound_same: "\<not> loose_bvar s (k + 1) \<Longrightarrow> 0 \<le> k \<Longrightarrow> s[Bound k/k] = s"
proof (induction s arbitrary: k)
  case (Abs a T t)
  then show ?case using Abs.IH[of "k + 1"] by (simp add: integer_arith add.assoc)
qed (auto simp: subst_Bound integer_arith)

lemma beta_Bound0: "\<not> loose_bvar s 1 \<Longrightarrow> Abs b T s $ Bound 0 \<rightarrow>\<^sub>\<beta> s"
  using beta.beta[of b T s "Bound 0"] subst_Bound_same[of s 0] by simp

lemma beta_eta_step: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* s t"
  by (rule r_into_rtranclp, rule sup2I1)

lemma tvar_b_ne_a: "tvar_b \<noteq> tvar_a"
  unfolding tvar_a_def tvar_b_def by eval

context prf_eq
begin

lemma typing_eq_app: "cert_typ alg ar U \<Longrightarrow> e \<turnstile> a : U \<Longrightarrow> e \<turnstile> b : U \<Longrightarrow> e \<turnstile> eq_const U $ a $ b : propT"
  using typing_eq_const[of U e] by blast

theorem abstract_rule_proof_valid:
  assumes ok: "okT (abstract_rule b hs (CTerm x T m) th0) th"
    and p: "prf_valid ax (set hs) (th_tpairs th0) prf (th_prop th0)"
    and wt: "wt_thm (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)" and tx: "\<And>e. e \<turnstile> x : T"
    and uF: "\<And>t a U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms prf \<Longrightarrow> x = Free a T \<Longrightarrow>
      (a, U) \<in> pfrees t \<Longrightarrow> U = T"
    and uV: "\<And>t z U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms prf \<Longrightarrow> x = Var z T \<Longrightarrow>
      (z, U) \<in> vars t \<Longrightarrow> U = T"
    and axF: "\<And>A a. A \<in> prf_atoms prf \<Longrightarrow> x = Free a T \<Longrightarrow> a \<notin> fnames (close A)"
  shows "prf_valid ax (set hs) (th_tpairs th) (abstract_rule_proof b x prf) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  from ok obtain U f g P where ad: "okT (abstract_rule_data b hs (CTerm x T m) th0) (U, f, g)"
    and mk: "ok (mk_equals (f, g)) P" and th: "th = mk_rep (maxidx_typ T (th_maxidx th0)) ?tps P"
    by (auto simp: abstract_rule_def)
  obtain t u a z where d: "dest_eq_fun ?P = Some (U, t, u)"
    and f: "f = Abs b T (abstract_over x t)" and g: "g = Abs b T (abstract_over x u)"
    and xc: "(x = Free a T \<and> \<not> occs_hyps x hs ?tps) \<or> (x = Var z T \<and> \<not> occs_hyps x [] ?tps)"
    by (rule abstract_rule_data_ok[OF ad tx])
  have wP: "wtp ?P" using wt by (simp add: wt_thm_def)
  have x: "x = Free a T \<or> x = Var z T" using xc by blast
  obtain n where cs: "(x = Free n T \<and> \<not> occs_hyps x hs ?tps) \<or> (\<exists>j. x = Var (n, j) T \<and> \<not> occs_hyps x [] ?tps)"
    using xc by (cases z) blast
  note d' = dest_eq_any_dest_eq_fun[OF d]
  obtain A where P0: "?P = eq_const A $ t $ u" and c: "closed t" "closed u"
    and ty: "\<And>e. e \<turnstile> t : A" "\<And>e. e \<turnstile> u : A"
    using dest_eq_any_wtp[OF eq_ok_ctab d' wP] by blast
  have tQ: "e\<langle>0:T\<rangle> \<turnstile> abstract_over x s : A" if "closed s" "\<And>e. e \<turnstile> s : A" for s e
    unfolding abstract_over_def
    by (rule typing_abstract_over_aux[OF x that(2)]) (use that(1) in \<open>simp_all add: closed_def\<close>)
  have nl: "\<not> loose_bvar (abstract_over x s) 1" if "closed s" for s
    unfolding abstract_over_def
    by (rule loose_bvar_abstract_over_aux) (use that loose_bvar_mono[of s 0 1] in \<open>simp_all add: closed_def\<close>)
  have cT: "cert_typ alg ar T" using tx[of "\<lambda>_. propT"] x by auto
  have cA: "cert_typ alg ar A" using typing_cert[OF ty(1)[of "\<lambda>_. propT"]] by simp
  have tf: "e \<turnstile> f : T \<rightarrow>\<^sub>T A" "e \<turnstile> g : T \<rightarrow>\<^sub>T A" for e
    using tQ[OF c(1) ty(1)] tQ[OF c(2) ty(2)] cT by (auto simp: f g)
  have cf: "closed f" "closed g" using nl[OF c(1)] nl[OF c(2)] by (simp_all add: f g closed_def)
  have P: "P = eq_const (T \<rightarrow>\<^sub>T A) $ f $ g" by (rule mk_equals_ok[OF mk cf(1) tf(1)])
  have aP: "abstract_over x ?P = eq_const A $ abstract_over x t $ abstract_over x u"
    using x by (auto simp: P0 abstract_over_def aconv_term_atom)
  have fv: "prf_valid ax (set hs) ?tps (forall_intr_proof b x prf) (all_const T $ Abs b T (abstract_over x ?P))"
    by (rule forall_intr_proof_valid[OF p wt tx cs uF uV axF])
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    let ?T = "tsubst \<rho> T" and ?A = "tsubst \<rho> A"
    let ?s1 = "ap \<rho> \<sigma> (abstract_over x t)" and ?s2 = "ap \<rho> \<sigma> (abstract_over x u)"
    define F where "F = Abs b ?T ?s1"
    define G where "G = Abs b ?T ?s2"
    have cTA: "cert_typ alg ar ?T" "cert_typ alg ar ?A"
      using cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]] cert_typ_tsubst[OF cA cinstD(2)[OF \<rho>]] by simp_all
    have cTA': "cert_typ alg ar (?T \<rightarrow>\<^sub>T ?A)" using cTA by (simp add: cert_typ_fun)
    have apf: "ap \<rho> \<sigma> f = F" "ap \<rho> \<sigma> g = G" by (simp_all add: f g F_def G_def ap_def)
    have cF: "closed F" "closed G" using cf \<sigma> by (simp_all add: apf[symmetric] closed_def)
    have tF: "e' \<turnstile> F : ?T \<rightarrow>\<^sub>T ?A" "e' \<turnstile> G : ?T \<rightarrow>\<^sub>T ?A" for e'
    proof -
      have "(\<lambda>i. tsubst \<rho> (e i)) \<turnstile> F : ?T \<rightarrow>\<^sub>T ?A" "(\<lambda>i. tsubst \<rho> (e i)) \<turnstile> G : ?T \<rightarrow>\<^sub>T ?A"
        using typing_ap_inst[OF tf(1) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]]
          typing_ap_inst[OF tf(2) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] by (simp_all add: apf)
      then show "e' \<turnstile> F : ?T \<rightarrow>\<^sub>T ?A" "e' \<turnstile> G : ?T \<rightarrow>\<^sub>T ?A" using cF typing_closed by blast+
    qed
    have ns: "\<not> loose_bvar ?s1 1" "\<not> loose_bvar ?s2 1" using nl[OF c(1)] nl[OF c(2)] \<sigma> by simp_all
    have fb: "F $ Bound 0 \<rightarrow>\<^sub>\<beta> ?s1" "G $ Bound 0 \<rightarrow>\<^sub>\<beta> ?s2"
      by (simp_all add: F_def G_def beta_Bound0 ns)
    have lF: "incr_bv 1 k F = F" "incr_bv 1 k G = G" "F[s/k] = F" "G[s/k] = G" if "0 \<le> k" for k s
      using cF that by (simp_all add: closed_def incr_bv_closed closed_subst_id)
    have tB0: "e'\<langle>0:?T\<rangle> \<turnstile> H $ Bound 0 : ?A" if "\<And>e''. e'' \<turnstile> H : ?T \<rightarrow>\<^sub>T ?A" for H e'
      using that[of "e'\<langle>0:?T\<rangle>"] by (auto simp: shift_def)
    have pr: "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> (forall_intr_proof b x prf))
        (all_const ?T $ Abs b ?T (eq_const ?A $ ?s1 $ ?s2))"
      using prf_validD[OF fv \<rho> \<sigma>, of e] sol th by (simp add: mk_rep_def aP ap_def)
    let ?ax = "all_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' (?T \<rightarrow>\<^sub>T ?A) (all_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' (?T \<rightarrow>\<^sub>T ?A)
      (implies $ (all_const ?T $ Abs STR ''x'' ?T (eq_const ?A $ (Bound 2 $ Bound 0) $ (Bound 1 $ Bound 0))) $
        (eq_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' ?T (Bound 2 $ Bound 0) $ Abs STR ''x'' ?T (Bound 1 $ Bound 0))))"
    have a: "atom_prop (equality_axiom STR ''abstract_rule'') [?T, ?A] = ?ax"
      by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def ax_bT_def Let_def
        all_const_def mk_implies_def implies_def tvar_b_ne_a)
    have tax: "e \<turnstile> ?ax : propT"
    proof -
      let ?e = "e\<langle>0:?T \<rightarrow>\<^sub>T ?A\<rangle>\<langle>0:?T \<rightarrow>\<^sub>T ?A\<rangle>"
      have t1: "?e\<langle>0:?T\<rangle> \<turnstile> eq_const ?A $ (Bound 2 $ Bound 0) $ (Bound 1 $ Bound 0) : propT"
        by (rule typing_eq_app[OF cTA(2)]) (auto simp: shift_def)
      have t2: "?e \<turnstile> eq_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' ?T (Bound 2 $ Bound 0) $ Abs STR ''x'' ?T (Bound 1 $ Bound 0) : propT"
        by (rule typing_eq_app[OF cTA']) (use cTA in \<open>auto simp: shift_def\<close>)
      from t1 t2 cTA cTA' show ?thesis by (simp add: typing_all_const all_type_def cert_typ_fun typing_implies cert_imp_type)
    qed
    have ax0: "prf_ok ax (set hs) e [] (equality_axm STR ''abstract_rule'') ?ax"
      using prf_ok_eq_axm[of "STR ''abstract_rule''" ?T ?A e "set hs" "[]"] cTA tax by (simp add: a eq_names_def)
    let ?prem = "all_const ?T $ Abs STR ''x'' ?T (eq_const ?A $ (F $ Bound 0) $ (G $ Bound 0))"
    let ?concl = "eq_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' ?T (F $ Bound 0) $ Abs STR ''x'' ?T (G $ Bound 0)"
    from prf_ok_PAppt_beta[OF ax0 tF(1), of None]
    have "prf_ok ax (set hs) e [] (PAppt (equality_axm STR ''abstract_rule'') None)
        (all_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' (?T \<rightarrow>\<^sub>T ?A) (implies $
          (all_const ?T $ Abs STR ''x'' ?T (eq_const ?A $ (F $ Bound 0) $ (Bound 1 $ Bound 0))) $
          (eq_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' ?T (F $ Bound 0) $ Abs STR ''x'' ?T (Bound 1 $ Bound 0))))"
      by (simp add: subst_bound_subst subst.simps all_const_def lF)
    from prf_ok_PAppt_beta[OF this tF(2), of None]
    have ax2: "prf_ok ax (set hs) e [] (PAppt (PAppt (equality_axm STR ''abstract_rule'') None) None)
        (implies $ ?prem $ ?concl)"
      by (simp add: subst_bound_subst subst.simps all_const_def lF)
    have red1: "(sup beta eta)\<^sup>*\<^sup>* ?prem (all_const ?T $ Abs STR ''x'' ?T (eq_const ?A $ ?s1 $ ?s2))"
      by (intro rtrancl_beta_eta_App rtrancl_beta_eta_Abs rtranclp.rtrancl_refl beta_eta_step fb)
    have tprem: "e \<turnstile> ?prem : propT"
    proof -
      have "e\<langle>0:?T\<rangle> \<turnstile> eq_const ?A $ (F $ Bound 0) $ (G $ Bound 0) : propT"
        by (rule typing_eq_app[OF cTA(2) tB0 tB0]) (rule tF)+
      then show ?thesis using cTA by (simp add: typing_all_const all_type_def cert_typ_fun)
    qed
    have "?prem \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> all_const ?T $ Abs STR ''x'' ?T (eq_const ?A $ ?s1 $ ?s2)"
      by (rule beta_eta_conv[OF red1]) (use tprem in \<open>auto simp: wt_def\<close>)
    moreover have "all_const ?T $ Abs STR ''x'' ?T (eq_const ?A $ ?s1 $ ?s2) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
        all_const ?T $ Abs b ?T (eq_const ?A $ ?s1 $ ?s2)"
      by (rule aconv_term_conv) simp
    ultimately have "all_const ?T $ Abs b ?T (eq_const ?A $ ?s1 $ ?s2) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?prem"
      by (meson conv_sym conv_trans)
    from prf_ok.conv[OF pr this tprem]
    have pr': "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> (forall_intr_proof b x prf)) ?prem" .
    have red2: "(sup beta eta)\<^sup>*\<^sup>* ?concl (eq_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' ?T ?s1 $ Abs STR ''x'' ?T ?s2)"
      by (intro rtrancl_beta_eta_App rtrancl_beta_eta_Abs rtranclp.rtrancl_refl beta_eta_step fb)
    have tconcl: "e \<turnstile> ?concl : propT"
      by (rule typing_eq_app[OF cTA']) (use cTA tB0[OF tF(1)] tB0[OF tF(2)] in auto)
    have "?concl \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' ?T ?s1 $ Abs STR ''x'' ?T ?s2"
      by (rule beta_eta_conv[OF red2]) (use tconcl in \<open>auto simp: wt_def\<close>)
    moreover have "eq_const (?T \<rightarrow>\<^sub>T ?A) $ Abs STR ''x'' ?T ?s1 $ Abs STR ''x'' ?T ?s2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
        eq_const (?T \<rightarrow>\<^sub>T ?A) $ F $ G"
      by (rule aconv_term_conv) (simp add: F_def G_def)
    ultimately have cc: "?concl \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const (?T \<rightarrow>\<^sub>T ?A) $ F $ G" by (rule conv_trans)
    have tgoal: "e \<turnstile> eq_const (?T \<rightarrow>\<^sub>T ?A) $ F $ G : propT" by (rule typing_eq_app[OF cTA' tF])
    from prf_ok.conv[OF prf_ok.PAppp[OF ax2 pr'] cc tgoal]
    show "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> (abstract_rule_proof b x prf)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: abstract_rule_proof_def th mk_rep_def P prf_ap_def equality_axm_def apf[symmetric])
  qed
qed

end

context prf_eq
begin

lemma ann_ok_beta_norm:
  assumes "ok (beta_norm s) s'" "gsubst \<sigma>"
  shows "ann_ok (Some (ap \<rho> \<sigma> (remove_types s'))) (ap \<rho> \<sigma> s)"
proof -
  have "ap \<rho> \<sigma> s \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> s'"
    by (rule beta_reds_ap[OF beta_norm_reds[OF assms(1)] gsubstD(1)[OF assms(2)]])
  then have "erase (ap \<rho> \<sigma> s) \<rightarrow>\<^sub>\<beta>\<^sup>* erase (ap \<rho> \<sigma> s')"
    by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl erase_beta)
  then have "equivclp (sup beta eta) (erase (ap \<rho> \<sigma> s)) (erase (ap \<rho> \<sigma> s'))"
    by (induction rule: rtranclp_induct) (auto intro: equivclp_into_equivclp)
  moreover have "erase (ap \<rho> \<sigma> (remove_types s')) = erase (ap \<rho> \<sigma> s')"
    by (rule erase_ap_cong) simp
  ultimately show ?thesis by (simp add: equivclp_sym)
qed

lemma ann_ok_comb_arg: "ann_ok (map_option (ap \<rho> \<sigma>) (comb_arg f t)) (ap \<rho> \<sigma> t)"
  using ann_ok_remove_types[of \<rho> \<sigma> t] by (simp add: comb_arg_def split: pterm.splits)

theorem combination_proof_valid:
  assumes ok: "okT (combination th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)"
    and d: "okT (combination_data th1 th2) (fT, U, f, g, t, u)"
    and cp: "combination_proof f g t u pf1 pf2 = returnW pf"
  shows "prf_valid ax H (th_tpairs th) pf (th_prop th)"
proof -
  from ok obtain fT' U' f' g' t' u' P where cd: "okT (combination_data th1 th2) (fT', U', f', g', t', u')"
    and mk: "ok (mk_equals (f' $ t', g' $ u')) P"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) P"
    by (auto simp: combination_def)
  from cd d have same: "fT' = fT" "U' = U" "f' = f" "g' = g" "t' = t" "u' = u" by auto
  obtain T1 where d1: "dest_eq_fun (th_prop th1) = Some (fT, f, g)" and d2: "dest_eq_fun (th_prop th2) = Some (T1, t, u)"
    and fT: "fT = T1 \<rightarrow>\<^sub>T U"
    by (rule combination_data_ok[OF d])
  note d1' = dest_eq_any_dest_eq_fun[OF d1] and d2' = dest_eq_any_dest_eq_fun[OF d2]
  obtain A where P1: "th_prop th1 = eq_const A $ f $ g" and c1: "closed f" "closed g"
    and ty1: "\<And>e. e \<turnstile> f : A" "\<And>e. e \<turnstile> g : A"
    using dest_eq_any_wtp[OF eq_ok_ctab d1' w1] by blast
  obtain B where P2: "th_prop th2 = eq_const B $ t $ u" and c2: "closed t" "closed u"
    and ty2: "\<And>e. e \<turnstile> t : B" "\<And>e. e \<turnstile> u : B"
    using dest_eq_any_wtp[OF eq_ok_ctab d2' w2] by blast
  from d1 P1 have A: "A = fT" by (simp add: propT_def)
  from d2 P2 have B: "B = T1" by (simp add: propT_def)
  have tft: "e \<turnstile> f $ t : U" "e \<turnstile> g $ u : U" for e using ty1 ty2 A B fT by auto
  have cft: "closed (f $ t)" "closed (g $ u)" using c1 c2 by (simp_all add: closed_def)
  have P: "P = eq_const U $ (f $ t) $ (g $ u)" using mk_equals_ok[OF mk[unfolded same] cft(1) tft(1)] .
  have lr: "ok m x" if "liftMP m = returnW x" for m :: "prf M" and x
    using that by (cases m) (auto simp: liftMP_def returnW_def)
  from lr[OF cp[unfolded combination_proof_def]] obtain fn gn where fn: "ok (beta_norm f) fn" and gn: "ok (beta_norm g) gn"
    and pf: "pf = PAppp (PAppp (PAppt (PAppt
      (if check_comb pf1 then PAppt (PAppt (equality_axm STR ''combination'') None) None
       else if is_reflexive_proof pf1 then PAppt (equality_axm STR ''combination'' %> remove_types fn) None
       else equality_axm STR ''combination'' %> remove_types fn %> remove_types gn)
      (comb_arg fn t)) (comb_arg gn u)) pf1) pf2"
    by (auto simp: Let_def)
  have cT1: "cert_typ alg ar T1" and cU: "cert_typ alg ar U"
    using typing_cert[OF ty1(1)[of "\<lambda>_. propT"]] by (simp_all add: A fT cert_typ_fun)
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have sol': "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "(t, u) \<in> set (th_tpairs th1) \<union> set (th_tpairs th2)" for t u
      by (rule sol_union_tpairs[OF _ that]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    let ?T = "tsubst \<rho> T1" and ?U = "tsubst \<rho> U"
    let ?f = "ap \<rho> \<sigma> f" and ?g = "ap \<rho> \<sigma> g" and ?t = "ap \<rho> \<sigma> t" and ?u = "ap \<rho> \<sigma> u"
    have cTU: "cert_typ alg ar ?T" "cert_typ alg ar ?U"
      using cert_typ_tsubst[OF cT1 cinstD(2)[OF \<rho>]] cert_typ_tsubst[OF cU cinstD(2)[OF \<rho>]] by simp_all
    have cl: "closed (ap \<rho> \<sigma> s)" if "closed s" for s using that \<sigma> by (simp add: closed_def)
    have tt: "e' \<turnstile> ap \<rho> \<sigma> s : tsubst \<rho> V" if "closed s" "\<And>e. e \<turnstile> s : V" for s V e'
      using typing_closed[OF typing_ap_inst[OF that(2) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] cl[OF that(1)]] .
    have tf: "e' \<turnstile> ?f : ?T \<rightarrow>\<^sub>T ?U" "e' \<turnstile> ?g : ?T \<rightarrow>\<^sub>T ?U" for e'
      using tt[OF c1(1) ty1(1)] tt[OF c1(2) ty1(2)] by (simp_all add: A fT)
    have ttu: "e' \<turnstile> ?t : ?T" "e' \<turnstile> ?u : ?T" for e'
      using tt[OF c2(1) ty2(1)] tt[OF c2(2) ty2(2)] by (simp_all add: B)
    have pr1: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf1) (eq_const (?T \<rightarrow>\<^sub>T ?U) $ ?f $ ?g)"
      using prf_validD[OF p1 \<rho> \<sigma> sol', of e] by (simp add: P1 A fT ap_def)
    have pr2: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf2) (eq_const ?T $ ?t $ ?u)"
      using prf_validD[OF p2 \<rho> \<sigma> sol', of e] by (simp add: P2 B ap_def)
    let ?B = "list_implies [eq_const (?T \<rightarrow>\<^sub>T ?U) $ Bound 3 $ Bound 2, eq_const ?T $ Bound 1 $ Bound 0]
      (eq_const ?U $ (Bound 3 $ Bound 1) $ (Bound 2 $ Bound 0))"
    let ?all = "\<lambda>V b. all_const V $ Abs STR ''x'' V b"
    let ?ax = "?all (?T \<rightarrow>\<^sub>T ?U) (?all (?T \<rightarrow>\<^sub>T ?U) (?all ?T (?all ?T ?B)))"
    have a: "atom_prop (equality_axiom STR ''combination'') [?T, ?U] = ?ax"
      by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def ax_bT_def Let_def
        all_const_def mk_implies_def implies_def tvar_b_ne_a)
    have tax: "e \<turnstile> ?ax : propT"
    proof -
      let ?e = "e\<langle>0:?T \<rightarrow>\<^sub>T ?U\<rangle>\<langle>0:?T \<rightarrow>\<^sub>T ?U\<rangle>\<langle>0:?T\<rangle>\<langle>0:?T\<rangle>"
      have "?e \<turnstile> eq_const (?T \<rightarrow>\<^sub>T ?U) $ Bound 3 $ Bound 2 : propT"
        by (rule typing_eq_app) (use cTU in \<open>auto simp: shift_def cert_typ_fun\<close>)
      moreover have "?e \<turnstile> eq_const ?T $ Bound 1 $ Bound 0 : propT"
        by (rule typing_eq_app) (use cTU in \<open>auto simp: shift_def\<close>)
      moreover have "?e \<turnstile> eq_const ?U $ (Bound 3 $ Bound 1) $ (Bound 2 $ Bound 0) : propT"
        by (rule typing_eq_app) (use cTU in \<open>auto simp: shift_def\<close>)
      ultimately have "?e \<turnstile> ?B : propT" by (simp add: typing_implies cert_imp_type)
      then show ?thesis using cTU by (simp add: typing_all_const all_type_def cert_typ_fun)
    qed
    have ax0: "prf_ok ax H e [] (equality_axm STR ''combination'') ?ax"
      using prf_ok_eq_axm[of "STR ''combination''" ?T ?U e H "[]"] cTU tax by (simp add: a eq_names_def)
    have lc: "incr_bv 1 k s = s" "s[v/k] = s" if "closed s" "0 \<le> k" for s v k
      using that by (simp_all add: closed_def incr_bv_closed closed_subst_id)
    note cs = cl[OF c1(1)] cl[OF c1(2)] cl[OF c2(1)] cl[OF c2(2)]
    have ax4: "prf_ok ax H e [] (PAppt (PAppt (PAppt (PAppt (equality_axm STR ''combination'') a1) a2) a3) a4)
        (implies $ (eq_const (?T \<rightarrow>\<^sub>T ?U) $ ?f $ ?g) $ (implies $ (eq_const ?T $ ?t $ ?u) $
          (eq_const ?U $ (?f $ ?t) $ (?g $ ?u))))"
      if "ann_ok a1 ?f" "ann_ok a2 ?g" "ann_ok a3 ?t" "ann_ok a4 ?u" for a1 a2 a3 a4
    proof -
      from prf_ok_PAppt_beta[OF ax0 tf(1) that(1)]
      have "prf_ok ax H e [] (PAppt (equality_axm STR ''combination'') a1)
          (?all (?T \<rightarrow>\<^sub>T ?U) (?all ?T (?all ?T (list_implies [eq_const (?T \<rightarrow>\<^sub>T ?U) $ ?f $ Bound 2,
            eq_const ?T $ Bound 1 $ Bound 0] (eq_const ?U $ (?f $ Bound 1) $ (Bound 2 $ Bound 0))))))"
        using cs by (simp add: subst_bound_subst subst.simps all_const_def lc)
      from prf_ok_PAppt_beta[OF this tf(2) that(2)]
      have "prf_ok ax H e [] (PAppt (PAppt (equality_axm STR ''combination'') a1) a2)
          (?all ?T (?all ?T (list_implies [eq_const (?T \<rightarrow>\<^sub>T ?U) $ ?f $ ?g,
            eq_const ?T $ Bound 1 $ Bound 0] (eq_const ?U $ (?f $ Bound 1) $ (?g $ Bound 0)))))"
        using cs by (simp add: subst_bound_subst subst.simps all_const_def lc)
      from prf_ok_PAppt_beta[OF this ttu(1) that(3)]
      have "prf_ok ax H e [] (PAppt (PAppt (PAppt (equality_axm STR ''combination'') a1) a2) a3)
          (?all ?T (list_implies [eq_const (?T \<rightarrow>\<^sub>T ?U) $ ?f $ ?g,
            eq_const ?T $ ?t $ Bound 0] (eq_const ?U $ (?f $ ?t) $ (?g $ Bound 0))))"
        using cs by (simp add: subst_bound_subst subst.simps all_const_def lc)
      from prf_ok_PAppt_beta[OF this ttu(2) that(4)] show ?thesis
        using cs by (simp add: subst_bound_subst subst.simps lc)
    qed
    have an: "ann_ok (Some (ap \<rho> \<sigma> (remove_types fn))) ?f" "ann_ok (Some (ap \<rho> \<sigma> (remove_types gn))) ?g"
      by (rule ann_ok_beta_norm[OF fn \<sigma>], rule ann_ok_beta_norm[OF gn \<sigma>])
    let ?sel = "if check_comb pf1 then PAppt (PAppt (equality_axm STR ''combination'') None) None
       else if is_reflexive_proof pf1 then PAppt (equality_axm STR ''combination'' %> remove_types fn) None
       else equality_axm STR ''combination'' %> remove_types fn %> remove_types gn"
    have ae: "map_proof_terms (ap \<rho> \<sigma>) (tsubst \<rho>) (equality_axm STR ''combination'') = equality_axm STR ''combination''"
      by (simp add: equality_axm_def)
    have axp: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (PAppt (PAppt ?sel (comb_arg fn t)) (comb_arg gn u)))
        (implies $ (eq_const (?T \<rightarrow>\<^sub>T ?U) $ ?f $ ?g) $ (implies $ (eq_const ?T $ ?t $ ?u) $
          (eq_const ?U $ (?f $ ?t) $ (?g $ ?u))))"
    proof (cases "check_comb pf1")
      case True
      then show ?thesis by (simp add: ae prf_ap_def) (rule ax4[OF _ _ ann_ok_comb_arg ann_ok_comb_arg]; simp)
    next
      case nc: False
      show ?thesis
      proof (cases "is_reflexive_proof pf1")
        case True
        with nc show ?thesis
          by (simp add: ae prf_ap_def) (rule ax4[OF an(1) _ ann_ok_comb_arg ann_ok_comb_arg], simp)
      next
        case False
        with nc show ?thesis
          by (simp add: ae prf_ap_def) (rule ax4[OF an(1) an(2) ann_ok_comb_arg ann_ok_comb_arg])
      qed
    qed
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (eq_const ?U $ (?f $ ?t) $ (?g $ ?u))"
      using prf_ok.PAppp[OF prf_ok.PAppp[OF axp pr1] pr2] by (simp add: pf prf_ap_def)
    then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: th mk_rep_def P ap_def)
  qed
qed

end

subsection \<open>Conversions and class proofs\<close>

context prf_eq
begin

lemma prf_ok_reflexive:
  assumes "cert_typ alg ar U" "e \<turnstile> s : U" "closed s"
  shows "prf_ok ax H e [] reflexive_proof (eq_const U $ s $ s)"
proof -
  have a: "atom_prop (equality_axiom STR ''reflexive'') [U, U] =
      all_const U $ Abs STR ''x'' U (eq_const U $ Bound 0 $ Bound 0)"
    by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def Let_def all_const_def)
  have "e\<langle>0:U\<rangle> \<turnstile> eq_const U $ Bound 0 $ Bound 0 : propT"
    by (intro typing.App typing.Bound) (simp_all add: shift_def typing_eq_const[OF assms(1)])
  then have "e \<turnstile> all_const U $ Abs STR ''x'' U (eq_const U $ Bound 0 $ Bound 0) : propT"
    using assms(1) by (simp add: typing_all_const all_type_def cert_typ_fun)
  then have ax0: "prf_ok ax H e [] (equality_axm STR ''reflexive'')
      (all_const U $ Abs STR ''x'' U (eq_const U $ Bound 0 $ Bound 0))"
    using prf_ok_eq_axm[of "STR ''reflexive''" U U e H "[]"] assms(1) by (simp add: a eq_names_def)
  from prf_ok_PAppt_beta[OF ax0 assms(2), of None] assms(3)
  show ?thesis by (simp add: reflexive_proof_def subst_bound_subst subst.simps)
qed

lemma reflexive_proof_conv_valid:
  assumes c: "closed t" "closed t'" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T" and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
  shows "prf_valid ax H [] reflexive_proof (eq_const T $ t $ t')"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  let ?U = "tsubst \<rho> T"
  have cT: "cert_typ alg ar T" using typing_cert[OF ty(1)[of "\<lambda>_. propT"]] by simp
  have cU: "cert_typ alg ar ?U" by (rule cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]])
  have cl: "closed (ap \<rho> \<sigma> s)" if "closed s" for s using that \<sigma> by (simp add: closed_def)
  have tt: "e' \<turnstile> ap \<rho> \<sigma> s : ?U" if "closed s" "\<And>e. e \<turnstile> s : T" for s e'
    using typing_closed[OF typing_ap_inst[OF that(2) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] cl[OF that(1)]] .
  have "prf_ok ax H e [] reflexive_proof (eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t)"
    by (rule prf_ok_reflexive[OF cU tt[OF c(1) ty(1)] cl[OF c(1)]])
  moreover have "eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t'"
    by (rule conv_eq_cong[OF tt[OF c(1) ty(1)] tt[OF c(1) ty(1)] tt[OF c(1) ty(1)] tt[OF c(2) ty(2)] cU
      conv_refl conv_ap[OF cv cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]]])
  ultimately have "prf_ok ax H e [] reflexive_proof (eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t')"
    by (rule prf_ok.conv) (rule typing_eq_app[OF cU tt[OF c(1) ty(1)] tt[OF c(2) ty(2)]])
  then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> reflexive_proof) (ap \<rho> \<sigma> (eq_const T $ t $ t'))"
    by (simp add: reflexive_proof_def equality_axm_def prf_ap_def ap_def)
qed

theorem beta_conversion_proof_valid:
  assumes ok: "okT (beta_conversion full (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "prf_valid ax H (th_tpairs th) reflexive_proof (th_prop th)"
proof -
  from ok obtain t' P where r: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and mk: "ok (mk_equals (t, t')) P" and th: "th = mk_rep m [] P"
    by (auto simp: beta_conversion_def returnW_def raiseW_def subst_bound_subst
      dest: beta_norm_reds split: if_splits pterm.splits)
  have c': "closed t'" by (rule beta_reds_closed[OF r c])
  have ty': "e \<turnstile> t' : T" for e by (rule subject_reduction_beta'[OF r ty])
  have "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" by (rule beta_eta_conv[OF beta_reds_sup[OF r]]) (use ty in \<open>auto simp: wt_def\<close>)
  from reflexive_proof_conv_valid[OF c c' ty ty' this] show ?thesis
    using mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
qed

theorem eta_conversion_proof_valid:
  assumes ok: "okT (eta_conversion (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "prf_valid ax H (th_tpairs th) reflexive_proof (th_prop th)"
proof -
  from ok obtain P where mk: "ok (mk_equals (t, eta_contract t)) P" and th: "th = mk_rep m [] P"
    by (auto simp: eta_conversion_def)
  note r = eta_contract_reds[of t]
  have c': "closed (eta_contract t)" by (rule eta_reds_closed[OF r c])
  have ty': "e \<turnstile> eta_contract t : T" for e by (rule eta_reds_typing[OF r ty])
  have "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract t" by (rule beta_eta_conv[OF eta_reds_sup[OF r]]) (use ty in \<open>auto simp: wt_def\<close>)
  from reflexive_proof_conv_valid[OF c c' ty ty' this] show ?thesis
    using mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
qed

theorem eta_long_conversion_proof_valid:
  assumes ok: "okT (eta_long_conversion (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "prf_valid ax H (th_tpairs th) reflexive_proof (th_prop th)"
proof -
  from ok obtain t' P where el: "ok (Pure_Rules.eta_long [] t) t'" and mk: "ok (mk_equals (t, t')) P"
    and th: "th = mk_rep m [] P"
    by (auto simp: eta_long_conversion_def)
  have bv: "bvok e [] t" for e using c by (simp add: bvok_def closed_iff_loose_bvar1)
  note r = eta_long_correct[OF el HOL.refl ty bv]
  have ty': "e \<turnstile> t' : T" for e using eta_long_correct[OF el HOL.refl ty bv, of e] by blast
  have cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" and lb: "lbsub t' t" using r by blast+
  have c': "closed t'" using c lb by (auto simp: lbsub_def closed_iff_loose_bvar1)
  from reflexive_proof_conv_valid[OF c c' ty ty' cv] show ?thesis
    using mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
qed

theorem reflexive_rule_proof_valid:
  assumes ok: "okT (reflexive (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "prf_valid ax H (th_tpairs th) reflexive_proof (th_prop th)"
proof -
  from ok obtain P where P: "ok (mk_equals (t, t)) P" and th: "th = mk_rep m [] P"
    by (auto simp: reflexive_def)
  from reflexive_proof_conv_valid[OF c c ty ty conv_refl] show ?thesis
    using mk_equals_ok[OF P c ty] by (simp add: th mk_rep_def)
qed

theorem of_class_proof_valid:
  assumes ok: "okT (Pure_Subst_Rules.of_class alg T c) th"
    and cT: "cert_typ alg ar T" and w: "wtp (mk_of_class T c)"
  shows "prf_valid ax H (th_tpairs th) (PClass T c) (th_prop th)"
proof -
  from ok obtain b where b: "ok (of_sort alg T [c]) b" and b': "b"
    and th: "th = mk_rep (maxidx_of_term (mk_of_class T c)) [] (mk_of_class T c)"
    by (auto simp: Pure_Subst_Rules.of_class_def returnW_def raiseW_def Let_def split: if_splits)
  have hs: "has_sort alg T [c]" using b b' of_sort_sem[of T "[c]"] cT by (simp add: cert_typ_def return_def)
  have oc: "mk_of_class U c = Proof_Judgment.of_class U c" for U
    by (simp add: mk_of_class_def Proof_Judgment.of_class_def class_suffix_def propT_def)
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    have hs': "has_sort alg (tsubst \<rho> T) [c]" by (rule has_sort_cinst[OF \<rho> hs])
    have "e \<turnstile> ap \<rho> \<sigma> (mk_of_class T c) : propT" by (rule typing_ap_wtp[OF w \<rho> \<sigma>])
    then have "e \<turnstile> Proof_Judgment.of_class (tsubst \<rho> T) c : propT"
      by (simp add: oc ap_def Proof_Judgment.of_class_def)
    from prf_ok.PClass[OF hs' this]
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (PClass T c)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: th mk_rep_def prf_ap_def oc ap_def Proof_Judgment.of_class_def)
  qed
qed

end

end
