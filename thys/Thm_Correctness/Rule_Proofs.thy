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
  let ?Ts = "thm_terms hs ?tps ?P \<union> prf_terms prf"
  have hv: "\<And>h. h \<in> set hs \<Longrightarrow> vars h = {}" using wt by (simp add: wt_thm_def)
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
  have cT: "cert_typ alg ar T" using cases tx[of "\<lambda>_. propT"] by auto
  have fTs: "finite ?Ts" by simp
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
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
    from cases show "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> (forall_intr_proof c x prf)) (ap \<rho> \<sigma> (th_prop th))"
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
        from conv_frename[OF this sol[of t u]] tu th e[OF conjunct1[OF tTs[OF tu]] no(1)]
          e[OF conjunct2[OF tTs[OF tu]] no(2)]
        show ?thesis by (simp add: mk_rep_def)
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
          (all_const ?\<rho>T $ Abs b ?\<rho>T (fsubst (tauF b G ?\<rho>T 0) (ap \<rho> \<sigma>' ?P)))"
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
        using tm[OF PTs, of 0] by (simp add: th mk_rep_def forall_intr_proof_def prf_ap_def abstract_over_def)
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
        with tTs[OF tu] no sol[of t u] tu th show ?thesis by (simp add: mk_rep_def)
      qed
      have pr: "prf_ok ax (set hs) (e\<langle>0:?\<rho>T\<rangle>) [] (prf_ap \<rho> \<sigma>' prf) (ap \<rho> \<sigma>' ?P)"
        by (rule prf_validD[OF p \<rho> \<sigma>' sol'])
      have tm: "fsubst (tauV G ?\<rho>T lev) (ap \<rho> \<sigma>' t) = ap \<rho> \<sigma> (abstract_over_aux x lev t)"
        if "t \<in> ?Ts" "0 \<le> lev" for t lev
        unfolding \<sigma>'_def xV
        by (rule fsubst_ap_Var[OF that(2) _ Gt[OF that(1)]]) (use uV[OF that(1) xV] G\<sigma>[OF that(1)] in auto)
      have nh: "fnames h \<inter> {G} = {}" if "h \<in> set hs" for h using Gt[OF hTs[OF that]] by auto
      have "prf_ok ax (set hs) e [] (Abst c None (prf_fsubst (tauV G ?\<rho>T 0) (prf_ap \<rho> \<sigma>' prf)))
          (all_const ?\<rho>T $ Abs b ?\<rho>T (fsubst (tauV G ?\<rho>T 0) (ap \<rho> \<sigma>' ?P)))"
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
        using tm[OF PTs, of 0] by (simp add: th mk_rep_def forall_intr_proof_def prf_ap_def abstract_over_def)
    qed
  qed
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

end
