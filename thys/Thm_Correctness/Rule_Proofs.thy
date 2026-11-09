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
  assumes p: "prf_ok ax H (e\<langle>0:U\<rangle>) [] q \<phi>" and cU: "cert_typ alg ar U" and tc: "tann_ok Tc U"
    and N: "\<And>h. h \<in> H \<Longrightarrow> fnames h \<inter> N = {}" "\<forall>A\<in>prf_atoms q. fnames (close A) \<inter> N = {}"
    and \<tau>: "\<And>y V. cert_typ alg ar V \<Longrightarrow> e\<langle>0:U\<rangle> \<turnstile> \<tau> y V : V" "\<And>y V. y \<notin> N \<Longrightarrow> \<tau> y V = Free y V"
  shows "prf_ok ax H e [] (Abst c Tc (prf_fsubst \<tau> q)) (all_const U $ Abs b U (fsubst \<tau> \<phi>))"
proof -
  have "prf_ok ax H (e\<langle>0:U\<rangle>) (map (fsubst \<tau>) []) (prf_fsubst \<tau> q) (fsubst \<tau> \<phi>)"
    by (rule prf_ok_fsubst[OF N(1) p \<tau> N(2)])
  then show ?thesis using cU tc by (simp add: prf_ok.Abst)
qed

text \<open>With the type of the variable as annotation or without:\<close>

lemma forall_intr_proof_valid_ann:
  assumes p: "prf_valid ax (set hs) tps prf P"
    and wt: "wt_thm m hs tps P" and tx: "\<And>e. e \<turnstile> x : T"
    and cases: "(x = Free b T \<and> \<not> occs_hyps x hs tps) \<or> (\<exists>j. x = Var (b, j) T \<and> \<not> occs_hyps x [] tps)"
    and uF: "\<And>t a U. t \<in> thm_terms hs tps P \<union> prf_terms prf \<Longrightarrow> x = Free a T \<Longrightarrow>
      (a, U) \<in> pfrees t \<Longrightarrow> U = T"
    and uV: "\<And>t z U. t \<in> thm_terms hs tps P \<union> prf_terms prf \<Longrightarrow> x = Var z T \<Longrightarrow>
      (z, U) \<in> vars t \<Longrightarrow> U = T"
    and axF: "\<And>A a. A \<in> prf_atoms prf \<Longrightarrow> x = Free a T \<Longrightarrow> a \<notin> fnames (close A)"
    and Tc: "Tc = None \<or> Tc = Some T"
  shows "prf_valid ax (set hs) tps (Abst c Tc (prf_abstract_over x prf)) (all_const T $ Abs b' T (abstract_over x P))"
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
    have tc: "tann_ok (map_option (tsubst \<rho>) Tc) ?\<rho>T" using Tc by auto
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
    from cases show "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> (Abst c Tc (prf_abstract_over x prf)))
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
      have "prf_ok ax (set hs) e [] (Abst c (map_option (tsubst \<rho>) Tc) (prf_fsubst (tauF b G ?\<rho>T 0) (prf_ap \<rho> \<sigma>' prf)))
          (all_const ?\<rho>T $ Abs b' ?\<rho>T (fsubst (tauF b G ?\<rho>T 0) (ap \<rho> \<sigma>' ?P)))"
      proof (rule prf_ok_Abst_fsubst[OF pr c\<rho>T tc nh])
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
        using tm[OF PTs, of 0] by (simp add: prf_ap_def abstract_over_def)
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
      have "prf_ok ax (set hs) e [] (Abst c (map_option (tsubst \<rho>) Tc) (prf_fsubst (tauV G ?\<rho>T 0) (prf_ap \<rho> \<sigma>' prf)))
          (all_const ?\<rho>T $ Abs b' ?\<rho>T (fsubst (tauV G ?\<rho>T 0) (ap \<rho> \<sigma>' ?P)))"
      proof (rule prf_ok_Abst_fsubst[OF pr c\<rho>T tc nh])
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
        using tm[OF PTs, of 0] by (simp add: prf_ap_def abstract_over_def)
    qed
  qed
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
  using forall_intr_proof_valid_ann[OF p wt tx cases uF uV axF, where Tc = None and c = c and b' = b'] by (simp add: forall_intr_proof_def)

theorem forall_intr_rule_proof_valid_ann:
  assumes ok: "okT (forall_intr hs (CTerm x T m) th0) th"
    and p: "prf_valid ax (set hs) (th_tpairs th0) prf (th_prop th0)"
    and wt: "wt_thm (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)" and tx: "\<And>e. e \<turnstile> x : T"
    and uF: "\<And>t a U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms prf \<Longrightarrow> x = Free a T \<Longrightarrow>
      (a, U) \<in> pfrees t \<Longrightarrow> U = T"
    and uV: "\<And>t z U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms prf \<Longrightarrow> x = Var z T \<Longrightarrow>
      (z, U) \<in> vars t \<Longrightarrow> U = T"
    and axF: "\<And>A a. A \<in> prf_atoms prf \<Longrightarrow> x = Free a T \<Longrightarrow> a \<notin> fnames (close A)"
    and Tc: "Tc = None \<or> Tc = Some T"
  shows "prf_valid ax (set hs) (th_tpairs th) (Abst c Tc (prf_abstract_over x prf)) (th_prop th)"
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
  from forall_intr_proof_valid_ann[OF p wt tx cases uF uV axF Tc] show ?thesis by (simp add: th mk_rep_def)
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
  using forall_intr_rule_proof_valid_ann[OF ok p wt tx uF uV axF, where Tc = None and c = c] by (simp add: forall_intr_proof_def)
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

text \<open>Abstractions over proofs of assumptions with annotations:\<close>

definition mk_AbsPs :: "pterm option list \<Rightarrow> prf \<Rightarrow> prf" where
  "mk_AbsPs ts p = foldr (\<lambda>t p. AbsP STR ''H'' t p) ts p"

lemma mk_AbsP_AbsPs: "mk_AbsP xs p = mk_AbsPs (map (\<lambda>_. None) xs) p"
  by (simp add: mk_AbsP_def mk_AbsPs_def foldr_map comp_def)

context prf_sig
begin

lemma list_all2_ann_ok_None: "list_all2 ann_ok (map (\<lambda>_. None) xs) xs"
  by (induction xs) simp_all

lemma list_all2_ann_ok_None_len: "length xs = length ys \<Longrightarrow> list_all2 ann_ok (map (\<lambda>_. None) xs) ys"
  by (simp add: list_all2_conv_all_nth)

lemma prf_ok_mk_AbsPs:
  "(\<And>A. A \<in> set As \<Longrightarrow> e \<turnstile> A : propT) \<Longrightarrow> list_all2 ann_ok ts As \<Longrightarrow> prf_ok ax H e (rev As @ Hs) q C \<Longrightarrow>
    prf_ok ax H e Hs (mk_AbsPs ts q) (list_implies As C)"
proof (induction As arbitrary: Hs ts)
  case (Cons A As)
  from Cons.prems(2) obtain t ts' where ts: "ts = t # ts'" "ann_ok t A" "list_all2 ann_ok ts' As"
    by (cases ts) auto
  have "prf_ok ax H e (A # Hs) (mk_AbsPs ts' q) (list_implies As C)"
    by (rule Cons.IH) (use Cons.prems ts in auto)
  with Cons.prems(1) ts show ?case by (simp add: mk_AbsPs_def prf_ok.AbsP)
qed (simp add: mk_AbsPs_def)

lemma prf_ok_mk_AbsP:
  "(\<And>A. A \<in> set As \<Longrightarrow> e \<turnstile> A : propT) \<Longrightarrow> prf_ok ax H e (rev As @ Hs) q C \<Longrightarrow>
    prf_ok ax H e Hs (mk_AbsP As q) (list_implies As C)"
  unfolding mk_AbsP_AbsPs by (rule prf_ok_mk_AbsPs) (simp_all add: list_all2_conv_all_nth)

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

lemma prf_ok_permute_ann:
  assumes p: "prf_ok ax H e [] pf (list_implies ps C)" and ty: "\<And>A. A \<in> set ps \<Longrightarrow> e \<turnstile> A : propT"
    and J: "jn \<le> length ps" and M: "mn \<le> length ps - jn"
  defines "ps' \<equiv> take jn ps @ drop mn (drop jn ps) @ take mn (drop jn ps)"
  assumes ann: "list_all2 ann_ok ts ps'"
  shows "prf_ok ax H e [] (mk_AbsPs ts (proof_combP pf (map PBound
    (downto (integer_of_nat (length ps') - 1) (integer_of_nat (length ps') - integer_of_nat jn) @
      downto (integer_of_nat mn - 1) 0 @
      downto (integer_of_nat (length ps') - integer_of_nat jn - 1) (integer_of_nat mn)))))
    (list_implies ps' C)"
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
  then have "prf_ok ax H e [] (mk_AbsPs ts (proof_combP pf (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))))
      (list_implies ps' C)"
    by (intro prf_ok_mk_AbsPs[OF _ ann]) (use ty sp in auto)
  then show ?thesis unfolding l map_append[symmetric] idx .
qed

lemma prf_ok_permute:
  assumes p: "prf_ok ax H e [] pf (list_implies ps C)" and ty: "\<And>A. A \<in> set ps \<Longrightarrow> e \<turnstile> A : propT"
    and J: "jn \<le> length ps" and M: "mn \<le> length ps - jn"
  defines "ps' \<equiv> take jn ps @ drop mn (drop jn ps) @ take mn (drop jn ps)"
  shows "prf_ok ax H e [] (permute_prems_proof ps' (integer_of_nat jn) (integer_of_nat mn) pf) (list_implies ps' C)"
proof -
  have a: "list_all2 ann_ok (map (\<lambda>_. None) ps') ps'" by (simp add: list_all2_conv_all_nth)
  from prf_ok_permute_ann[OF p ty J M a[unfolded ps'_def], folded ps'_def] show ?thesis
    by (simp add: permute_prems_proof_def Let_def mk_AbsP_AbsPs)
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

theorem equal_intr_proof_valid_ann:
  assumes ok: "okT (equal_intr th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
    and ea: "erase At = erase A" "erase Bt = erase B"
  shows "prf_valid ax H (th_tpairs th) (PAppp (PAppp (equality_axm STR ''equal_intr'' %> At %> Bt) pf1) pf2) (th_prop th)"
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
    have ann1: "ann_ok (Some (ap \<rho> \<sigma> At)) (ap \<rho> \<sigma> A)" and ann2: "ann_ok (Some (ap \<rho> \<sigma> Bt)) (ap \<rho> \<sigma> B)"
      using erase_ap_cong[OF ea(1), of \<rho> \<sigma>] erase_ap_cong[OF ea(2), of \<rho> \<sigma>] by (simp_all add: ann_ok_def equivclp_refl)
    from prf_ok_eq_axm_prop2[OF _ a2 tC ty[OF wA] ty[OF wB] cl[OF wA] ann1 ann2]
    have ax2: "prf_ok ax H e [] (PAppt (PAppt (equality_axm STR ''equal_intr'') (Some (ap \<rho> \<sigma> At)))
        (Some (ap \<rho> \<sigma> Bt)))
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
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (PAppp (PAppp (equality_axm STR ''equal_intr'' %> At %> Bt) pf1) pf2)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: th mk_rep_def P prf_ap_def equality_axm_def ap_def)
  qed
qed


theorem equal_intr_proof_valid:
  assumes ok: "okT (equal_intr th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
  shows "prf_valid ax H (th_tpairs th) (equal_intr_proof A B pf1 pf2) (th_prop th)"
  unfolding equal_intr_proof_def by (rule equal_intr_proof_valid_ann[OF ok p1 p2 w1 w2 P1]) simp_all

theorem equal_elim_proof_valid_ann:
  assumes ok: "okT (equal_elim th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
    and ea: "erase At = erase A" "erase Bt = erase B"
  shows "prf_valid ax H (th_tpairs th) (PAppp (PAppp (equality_axm STR ''equal_elim'' %> At %> Bt) pf1) pf2) (th_prop th)"
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
    have ann1: "ann_ok (Some (ap \<rho> \<sigma> At)) (ap \<rho> \<sigma> A)" and ann2: "ann_ok (Some (ap \<rho> \<sigma> Bt)) (ap \<rho> \<sigma> B)"
      using erase_ap_cong[OF ea(1), of \<rho> \<sigma>] erase_ap_cong[OF ea(2), of \<rho> \<sigma>] by (simp_all add: ann_ok_def equivclp_refl)
    from prf_ok_eq_axm_prop2[OF _ a2 tC ty[OF wA] ty[OF wB] cl[OF wA] ann1 ann2]
    have ax2: "prf_ok ax H e [] (PAppt (PAppt (equality_axm STR ''equal_elim'') (Some (ap \<rho> \<sigma> At)))
        (Some (ap \<rho> \<sigma> Bt)))
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
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (PAppp (PAppp (equality_axm STR ''equal_elim'' %> At %> Bt) pf1) pf2)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: th mk_rep_def AB prf_ap_def equality_axm_def)
  qed
qed


theorem equal_elim_proof_valid:
  assumes ok: "okT (equal_elim th1 th2) th"
    and p1: "prf_valid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "prf_valid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
  shows "prf_valid ax H (th_tpairs th) (equal_elim_proof A B pf1 pf2) (th_prop th)"
  unfolding equal_elim_proof_def by (rule equal_elim_proof_valid_ann[OF ok p1 p2 w1 w2 P1]) simp_all

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

lemma prf_ok_reflexive_ann:
  assumes "cert_typ alg ar U" "e \<turnstile> s : U" "closed s" "ann_ok a s"
  shows "prf_ok ax H e [] (PAppt (equality_axm STR ''reflexive'') a) (eq_const U $ s $ s)"
proof -
  have b: "atom_prop (equality_axiom STR ''reflexive'') [U, U] =
      all_const U $ Abs STR ''x'' U (eq_const U $ Bound 0 $ Bound 0)"
    by (simp add: atom_prop_eq eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def Let_def all_const_def)
  have "e\<langle>0:U\<rangle> \<turnstile> eq_const U $ Bound 0 $ Bound 0 : propT"
    by (intro typing.App typing.Bound) (simp_all add: shift_def typing_eq_const[OF assms(1)])
  then have "e \<turnstile> all_const U $ Abs STR ''x'' U (eq_const U $ Bound 0 $ Bound 0) : propT"
    using assms(1) by (simp add: typing_all_const all_type_def cert_typ_fun)
  then have ax0: "prf_ok ax H e [] (equality_axm STR ''reflexive'')
      (all_const U $ Abs STR ''x'' U (eq_const U $ Bound 0 $ Bound 0))"
    using prf_ok_eq_axm[of "STR ''reflexive''" U U e H "[]"] assms(1) by (simp add: b eq_names_def)
  from prf_ok_PAppt_beta[OF ax0 assms(2,4)] assms(3)
  show ?thesis by (simp add: subst_bound_subst subst.simps)
qed

lemma prf_ok_reflexive:
  assumes "cert_typ alg ar U" "e \<turnstile> s : U" "closed s"
  shows "prf_ok ax H e [] reflexive_proof (eq_const U $ s $ s)"
  using prf_ok_reflexive_ann[OF assms, of None] by (simp add: reflexive_proof_def ann_ok_def)

text \<open>The reflexivity axiom applied to \<open>t\<close> with an annotation, as in the tight proofs:\<close>

lemma reflexive_proof_conv_valid_ann:
  assumes c: "closed t" "closed t'" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T" and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
    and a: "a = None \<or> a = Some t"
  shows "prf_valid ax H [] (PAppt (equality_axm STR ''reflexive'') a) (eq_const T $ t $ t')"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  let ?U = "tsubst \<rho> T"
  have cT: "cert_typ alg ar T" using typing_cert[OF ty(1)[of "\<lambda>_. propT"]] by simp
  have cU: "cert_typ alg ar ?U" by (rule cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]])
  have cl: "closed (ap \<rho> \<sigma> s)" if "closed s" for s using that \<sigma> by (simp add: closed_def)
  have tt: "e' \<turnstile> ap \<rho> \<sigma> s : ?U" if "closed s" "\<And>e. e \<turnstile> s : T" for s e'
    using typing_closed[OF typing_ap_inst[OF that(2) cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] cl[OF that(1)]] .
  have an: "ann_ok (map_option (ap \<rho> \<sigma>) a) (ap \<rho> \<sigma> t)" using a by (auto simp: ann_ok_def)
  have "prf_ok ax H e [] (PAppt (equality_axm STR ''reflexive'') (map_option (ap \<rho> \<sigma>) a))
      (eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t)"
    by (rule prf_ok_reflexive_ann[OF cU tt[OF c(1) ty(1)] cl[OF c(1)] an])
  moreover have "eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t'"
    by (rule conv_eq_cong[OF tt[OF c(1) ty(1)] tt[OF c(1) ty(1)] tt[OF c(1) ty(1)] tt[OF c(2) ty(2)] cU
      conv_refl conv_ap[OF cv cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]]])
  ultimately have "prf_ok ax H e [] (PAppt (equality_axm STR ''reflexive'') (map_option (ap \<rho> \<sigma>) a))
      (eq_const ?U $ ap \<rho> \<sigma> t $ ap \<rho> \<sigma> t')"
    by (rule prf_ok.conv) (rule typing_eq_app[OF cU tt[OF c(1) ty(1)] tt[OF c(2) ty(2)]])
  then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (PAppt (equality_axm STR ''reflexive'') a)) (ap \<rho> \<sigma> (eq_const T $ t $ t'))"
    by (simp add: equality_axm_def prf_ap_def ap_def)
qed

lemma reflexive_proof_conv_valid:
  assumes c: "closed t" "closed t'" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T" and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
  shows "prf_valid ax H [] reflexive_proof (eq_const T $ t $ t')"
  using reflexive_proof_conv_valid_ann[OF assms, of None] by (simp add: reflexive_proof_def)

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

subsection \<open>Proof by an equivalent assumption\<close>

text \<open>A negative bound on the number of assumptions is as good as a large enough one:\<close>

lemma strip_assums_imp_neg:
  "m < 0 \<Longrightarrow> integer_of_nat (size B) < M \<Longrightarrow> strip_assums_imp m Hs B = strip_assums_imp M Hs B"
proof (induction m Hs B arbitrary: M rule: strip_assums_imp.induct)
  case (1 m Hs B)
  have m0: "m \<noteq> 0" "M \<noteq> 0" using "1.prems" by (auto simp: less_integer.rep_eq integer_of_nat.rep_eq)
  show ?case
  proof (cases "dest_imp B")
    case None
    then show ?thesis using m0 by (simp add: strip_assums_imp.simps[of m] strip_assums_imp.simps[of M])
  next
    case (Some p)
    obtain H B' where p: "p = (H, B')" by force
    have "size B' < size B" using dest_imp_size Some p by blast
    then have s: "integer_of_nat (size B') < M - 1" using "1.prems"(2)
      by (simp add: less_integer.rep_eq integer_of_nat.rep_eq)
    have "strip_assums_imp (m - 1) (H # Hs) B' = strip_assums_imp (M - 1) (H # Hs) B'"
      by (rule "1.IH"[OF m0(1) Some[unfolded p] HOL.refl _ s]) (use "1.prems" in simp)
    then show ?thesis using m0 Some p
      by (simp add: strip_assums_imp.simps[of m] strip_assums_imp.simps[of M])
  qed
qed

lemma aimp_prf_neg: "m < 0 \<Longrightarrow> integer_of_nat (size A) < M \<Longrightarrow> aimp_prf fA A i m = aimp_prf fA A i M"
proof (induction fA A i m arbitrary: M rule: aimp_prf.induct)
  case (1 fA c U A B i m)
  have m0: "m \<noteq> 0" "M \<noteq> 0" using "1.prems" by (auto simp: less_integer.rep_eq integer_of_nat.rep_eq)
  have s: "integer_of_nat (size B) < M - 1" using "1.prems"(2) by (simp add: less_integer.rep_eq integer_of_nat.rep_eq)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    have "aimp_prf fA B (i + 1) (m - 1) = aimp_prf fA B (i + 1) (M - 1)"
      by (rule "1.IH"[OF m0(1) True _ s]) (use "1.prems" in simp)
    then show ?thesis using m0 True by simp
  qed (use m0 in simp)
qed simp_all

lemma aall_prf_neg: "m < 0 \<Longrightarrow> integer_of_nat (size A) < M \<Longrightarrow> aall_prf fA fT i m A = aall_prf fA fT i M A"
proof (induction fA fT i m A rule: aall_prf.induct)
  case (1 fA fT i m c U a T t)
  then show ?case by (auto simp: aimp_prf_neg less_integer.rep_eq integer_of_nat.rep_eq)
qed (simp_all add: aimp_prf_neg)

lemma strip_assums_all_size: "strip_assums_all ps A = (ps', A') \<Longrightarrow> size A' \<le> size A"
proof (induction ps A arbitrary: ps' A' rule: strip_assums_all.induct)
  case (1 ps A)
  show ?case
  proof (cases "dest_all A")
    case (Some x)
    obtain a T b where x: "x = (a, T, b)" by (cases x) auto
    have "size b < size A" using dest_all_size Some x by blast
    moreover have "size A' \<le> size b"
      by (rule "1.IH"[OF Some[unfolded x] HOL.refl HOL.refl]) (use "1.prems" Some x in \<open>simp add: strip_assums_all.simps[of ps]\<close>)
    ultimately show ?thesis by simp
  qed (use "1.prems" in \<open>simp add: strip_assums_all.simps[of ps]\<close>)
qed

lemma assum_problems_neg:
  "m < 0 \<Longrightarrow> integer_of_nat (size A) < M \<Longrightarrow> assum_problems m A = assum_problems M A"
proof -
  assume m: "m < 0" and M: "integer_of_nat (size A) < M"
  obtain ps A' where s: "strip_assums_all [] A = (ps, A')" by force
  have "size A' \<le> size A" by (rule strip_assums_all_size[OF s])
  with M have "integer_of_nat (size A') < M" by (simp add: less_integer.rep_eq integer_of_nat.rep_eq)
  from strip_assums_imp_neg[OF m this, of "[]"] show ?thesis by (simp add: assum_problems_def s)
qed

lemma mk_asm_prf_neg:
  "m < 0 \<Longrightarrow> integer_of_nat (size A) < M \<Longrightarrow> mk_asm_prf A i m = mk_asm_prf A i M"
  by (simp add: mk_asm_prf_aall aall_prf_neg)

lemma find_index_from_Some_nth:
  "find_index_from P xs k = Some j \<Longrightarrow> \<exists>l. j = k + integer_of_nat l \<and> l < length xs \<and> P (xs ! l)"
proof (induction P xs k rule: find_index_from.induct)
  case (2 P x xs k)
  show ?case
  proof (cases "P x")
    case False
    with "2.prems" obtain l where "j = k + 1 + integer_of_nat l" "l < length xs" "P (xs ! l)"
      using "2.IH" by auto
    then show ?thesis
      by (intro exI[of _ "Suc l"]) (simp add: integer_eq_iff integer_of_nat.rep_eq)
  qed (use "2.prems" in \<open>auto intro!: exI[of _ 0]\<close>)
qed simp

lemma eq_assumption_precise:
  assumes ok: "okT (eq_assumption i state) (n, th)" and d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
  obtains params asms concl l where "assum_problems (-1) Bi = (params, asms, concl)"
    "n = integer_of_nat l + 1" "l < length asms" "aeconv (asms ! l) concl"
    "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
proof -
  obtain tpairs' Bs' Bi' C' where d': "okT (dest_state state i) (tpairs', Bs', Bi', C')" and
    r: "okT (case assum_problems (-1) Bi' of (_, asms, concl) \<Rightarrow>
      (case find_index_from (\<lambda>asm. aeconv asm concl) asms 0 of
        None \<Rightarrow> raiseW (THM (STR ''eq_assumption'') 0 State)
      | Some n \<Rightarrow> returnW (n + 1,
          \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs', th_prop = list_implies Bs' C'\<rparr>))) (n, th)"
    using ok by (auto simp: eq_assumption_def)
  have e: "(tpairs', Bs', Bi', C') = (tpairs, Bs, Bi, C)" by (rule okW_det[OF d' d])
  obtain params asms concl where a: "assum_problems (-1) Bi = (params, asms, concl)"
    by (cases "assum_problems (-1) Bi") auto
  with r e obtain k where f: "find_index_from (\<lambda>asm. aeconv asm concl) asms 0 = Some k"
    and n: "n = k + 1"
    and th: "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
    by (auto simp: returnW_def raiseW_def split: option.splits)
  from find_index_from_Some_nth[OF f] obtain l where "k = integer_of_nat l" "l < length asms"
    "aeconv (asms ! l) concl" by auto
  with a n th show thesis by (intro that) simp_all
qed

context prf_sig
begin

lemma prf_ok_PBounds_downto:
  assumes "\<And>A. A \<in> set As \<Longrightarrow> e \<turnstile> A : propT"
  shows "list_all2 (\<lambda>q A. prf_ok ax H e (rev As) q A)
    (map PBound (downto (integer_of_nat (length As) - 1) 0)) As"
proof -
  let ?n = "length As"
  have "downto (integer_of_nat ?n - 1) 0 =
      map (\<lambda>l. integer_of_nat (nat_of_integer (integer_of_nat ?n - 1) - l)) [0..<nat_of_integer (integer_of_nat ?n - 1 - 0 + 1)]"
    by (rule downto_nat) (simp_all add: less_eq_integer.rep_eq integer_of_nat.rep_eq)
  moreover have "nat_of_integer (integer_of_nat ?n - 1 - 0 + 1) = ?n"
    by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq)
  ultimately have dt: "downto (integer_of_nat ?n - 1) 0 = map (\<lambda>k. integer_of_nat (?n - 1 - k)) [0..<?n]"
    by (simp add: nat_int_minus1)
  show ?thesis unfolding dt
    by (rule prf_ok_PBounds[where f = "\<lambda>k. ?n - 1 - k"]) (use assms in \<open>auto simp: rev_nth\<close>)
qed

end

context prf_model
begin

text \<open>
  The proof of \<^const>\<open>assumption_proof\<close> proves \<open>\<lbrakk>Bs\<rbrakk> \<Longrightarrow> C\<close> from a proof of \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close>, if
  assumption \<open>l\<close> of \<open>Bi\<close> (before normalisation) converts to its conclusion below its parameters:
\<close>

lemma prf_ok_assumption_proof:
  assumes \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and w: "wtp (list_implies (Bs @ [Bi]) C)"
    and p0: "prf_ok ax H e [] P (ap \<rho> \<sigma> (list_implies (Bs @ [Bi]) C))"
    and ap: "assum_problems (-1) Bi = (params, asms, concl)" and l: "l < length asms"
    and cv: "ap \<rho> \<sigma> (rlist_abs params (asms ! l)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs params concl)"
    and lN: "length Ns = length Bs"
  shows "prf_ok ax H e [] (mk_AbsP Ns (proof_combP P (map PBound (downto (integer_of_nat (length Bs) - 1) 0) @
    [mk_asm_prf Bi (integer_of_nat l + 1) (-1)]))) (ap \<rho> \<sigma> (list_implies Bs C))"
proof -
  let ?n = "integer_of_nat l + 1"
  have wps: "wtp A" if "A \<in> set (Bs @ [Bi])" for A
    using w that wtp_list_implies[where As = "Bs @ [Bi]" and As' = "Bs @ [Bi]" and B = C and B' = C] by auto
  have wBi: "wtp Bi" by (rule wps) simp
  define M where "M = integer_of_nat (size Bi) + 1"
  have sM: "integer_of_nat (size Bi) < M" and M0: "0 \<le> M"
    by (simp_all add: M_def less_integer.rep_eq less_eq_integer.rep_eq integer_of_nat.rep_eq)
  have apM: "assum_problems M Bi = (params, asms, concl)"
    using ap assum_problems_neg[of "-1" Bi M] sM by simp
  have mkM: "mk_asm_prf Bi ?n (-1) = mk_asm_prf Bi ?n M" by (rule mk_asm_prf_neg[OF _ sM]) simp
  have nn: "nat_of_integer ?n - 1 = l" by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq nat_add_distrib)
  have n1: "1 \<le> ?n" "?n \<le> ilength asms"
    using l by (simp_all add: ilength_eq less_eq_integer.rep_eq integer_of_nat.rep_eq)
  let ?aBs = "map (ap \<rho> \<sigma>) Bs"
  have ty: "e \<turnstile> A : propT" if "A \<in> set ?aBs" for A
    using that typing_ap_wtp[OF wps \<rho> \<sigma>] by auto
  have p1: "prf_ok ax H e (rev ?aBs) P (list_implies (?aBs @ [ap \<rho> \<sigma> Bi]) (ap \<rho> \<sigma> C))"
    using prf_ok_append[OF p0, of "rev ?aBs"] by (simp add: ap_list_implies)
  have pa: "prf_ok ax H e (rev ?aBs) (mk_asm_prf Bi ?n M) (ap \<rho> \<sigma> Bi)"
    by (rule mk_asm_prf_ok[OF \<rho> \<sigma> wBi apM M0 n1]) (subst nn, rule cv)
  have "list_all2 (\<lambda>q A. prf_ok ax H e (rev ?aBs) q A)
      (map PBound (downto (integer_of_nat (length ?aBs) - 1) 0) @ [mk_asm_prf Bi ?n M]) (?aBs @ [ap \<rho> \<sigma> Bi])"
    by (rule list_all2_appendI[OF prf_ok_PBounds_downto[OF ty]])
      (simp_all, intro list_all2_Cons[THEN iffD2] conjI pa list.rel_intros(1))
  from prf_ok_proof_combP[OF p1 this]
  have "prf_ok ax H e (rev ?aBs @ []) (proof_combP P
      (map PBound (downto (integer_of_nat (length ?aBs) - 1) 0) @ [mk_asm_prf Bi ?n M])) (ap \<rho> \<sigma> C)"
    by simp
  from prf_ok_mk_AbsP[OF ty this] show ?thesis
    using mk_AbsP_length[of ?aBs Ns] lN by (simp add: mkM ap_list_implies)
qed

lemma prf_ap_assumption_proof:
  "prf_ap \<rho> \<sigma> (assumption_proof Bs Bi n pf) =
    mk_AbsP Bs (proof_combP (prf_ap \<rho> \<sigma> pf) (map PBound (downto (integer_of_nat (length Bs) - 1) 0) @
      [mk_asm_prf Bi n (-1)]))"
  by (simp add: assumption_proof_def prf_ap_mk_AbsP prf_ap_proof_combP prf_ap_mk_asm_prf)
    (simp add: prf_ap_def comp_def)

theorem eq_assumption_proof_valid:
  assumes ok: "okT (eq_assumption i state) (n, th)" and d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and p: "prf_valid ax H (th_tpairs state) pf (th_prop state)" and w: "wtp (th_prop state)"
  shows "prf_valid ax H (th_tpairs th) (assumption_proof Bs Bi n pf) (th_prop th)"
proof -
  obtain params asms concl l where ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and nl: "n = integer_of_nat l + 1" and l: "l < length asms" and ae: "aeconv (asms ! l) concl"
    and th: "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
    by (rule eq_assumption_precise[OF ok d])
  note ds = okT_dest_state[OF d]
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  have wBi: "wtp Bi"
    using w P wtp_list_implies[where As = "Bs @ [Bi]" and As' = "Bs @ [Bi]" and B = C and B' = C] by auto
  note st = assum_problems_struct[OF ap wtpD(2)[OF wBi, of "\<lambda>_. propT"]]
  let ?E = "pushes (\<lambda>_. propT) (map snd (rev params))"
  have tBi: "(\<lambda>_. propT) \<turnstile> list_forall (rev params) (list_implies asms concl) : propT"
    using wtpD(2)[OF wBi] st(1) by simp
  have cq: "\<forall>T\<in>snd ` set (rev params). cert_typ alg ar T"
    using tBi by (auto simp: typing_list_forall)
  have tA: "?E \<turnstile> asms ! l : propT" using st(2) l by simp
  have cv0: "asms ! l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> concl" by (rule aeconv_conv[OF ae]) (use tA st(3) in \<open>auto simp: wt_def\<close>)
  have cv1: "rlist_abs params (asms ! l) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rlist_abs params concl"
    unfolding rlist_abs_abs_list
    by (rule conv_abs_list[OF _ _ cv0]) (use typing_abs_list[OF tA cq] typing_abs_list[OF st(3) cq] in \<open>auto simp: wt_def\<close>)
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> (th_prop state))"
      by (rule prf_validD[OF p \<rho> \<sigma>]) (use sol th ds(1) in simp)
    from prf_ok_assumption_proof[OF \<rho> \<sigma> w[unfolded P] this[unfolded P] ap l
        conv_ap[OF cv1 cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]] HOL.refl]
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (assumption_proof Bs Bi n pf)) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: prf_ap_assumption_proof nl th)
  qed
qed

text \<open>
  The proof of a result of \<^const>\<open>assumption\<close> for a unifier \<open>env\<close> of assumption \<open>l\<close> of subgoal
  \<open>i\<close> with its conclusion is valid, with the assumptions of \<^theory_text>\<open>assumption_result_valid\<close>
  (with the fix of \<open>patches/18-thm-assumption.patch\<close>):
\<close>

theorem ares_proof_valid:
  assumes d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and ap: "assum_problems (-1) Bi = (params, asms, concl)" and l: "l < length asms"
    and nt: "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    and pr: "ares_proof (ACtx (th_maxidx state) tpairs Bs Bi C params concl) r pf = returnW q"
    and p: "prf_valid ax H (th_tpairs state) pf (th_prop state)" and w: "wtp (th_prop state)"
    and ei: "einv A K env" and wi: "winv env X"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and solves: "\<And>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env \<Longrightarrow> cert_inst \<rho>' \<Longrightarrow> (\<forall>(t, u)\<in>set tps. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u) \<Longrightarrow>
      \<forall>(t, u)\<in>set ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs). ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
  shows "prf_valid ax H (th_tpairs (ar_thm r)) q (th_prop (ar_thm r))"
proof -
  let ?n = "integer_of_nat l + 1"
  note ds = okT_dest_state[OF d]
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  have wP: "wtp (list_implies (Bs @ [Bi]) C)" using w P by simp
  have wBC: "wtp (list_implies Bs C)"
  proof (rule wtpI)
    have tP: "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi]) C : propT" using wtpD(2)[OF wP] .
    show "closed (list_implies Bs C)" using wtpD(1)[OF wP] by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies Bs C : propT"
      using typing_list_impliesD[OF tP] typing_list_implies_imp[OF tP] by (intro typing_list_impliesI) auto
  qed
  \<comment> \<open>the new theorem and the proof\<close>
  obtain ntps P' where r: "r = ARes env ?n \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P'\<rparr>"
    and rel: "env_is_empty env \<Longrightarrow> ntps = tps \<and> P' = list_implies Bs C"
      "\<not> env_is_empty env \<Longrightarrow>
        list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps \<and>
        ok (norm_term env (list_implies Bs C)) P'"
  proof (cases "env_is_empty env")
    case True
    with nt show thesis by (intro that[of tps "list_implies Bs C"]) (auto simp: newth_def returnW_def)
  next
    case False
    with nt obtain ntps P' where n: "ok (mapM (norm_tpair env) tps) ntps" "ok (norm_term env (list_implies Bs C)) P'"
      and r: "r = ARes env ?n \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P'\<rparr>"
      by (auto simp: newth_def)
    have "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
      using n(1) unfolding ok_mapM by (rule list_all2_mono) (auto simp: norm_tpair_def split: prod.splits)
    with r n(2) False show thesis by (intro that[of ntps P']) auto
  qed
  obtain Ns where Ns: "ok (mapM (norm_term env) Bs) Ns"
    and q: "env_is_empty env \<and> q = assumption_proof Ns Bi ?n pf \<or>
      \<not> env_is_empty env \<and> norm_proof_remove_types env (assumption_proof Ns Bi ?n pf) = returnW q"
    using pr by (cases "env_is_empty env") (auto simp: ares_proof_def r bindP_eq_returnP liftMP_eq_returnP Let_def)
  have lN: "length Ns = length Bs" using Ns unfolding ok_mapM by (simp add: list_all2_lengthD)
  show ?thesis unfolding r ares.sel
  proof (rule prf_validI, unfold thm_rep.simps)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set ntps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    obtain \<rho>' \<sigma>' where ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" by (rule iext_exists_sb[OF ei wi \<rho> \<sigma>]) blast
    note i = iextD[OF ie]
    have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
    have tyi: "(\<lambda>_. propT) \<turnstile> inst \<rho>' s : tsubst \<rho>' T" if "\<And>e. e \<turnstile> s : T" "closed s" for s T
      using typing_closed[OF typing_inst[OF that(1) cert_inst_inst_ok[OF ci']]] that(2) by (simp add: closed_def)
    \<comment> \<open>the flex-flex pairs of the unifier are solved at the extension\<close>
    have stps: "\<forall>(t, u)\<in>set tps. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set tps"
      from tw tu obtain T where c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
      show "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
      proof (cases "env_is_empty env")
        case True
        have "ap \<rho>' \<sigma>' s = ap \<rho> \<sigma> s" for s by (rule iext_unb[OF ie unb_empty[OF True]])
        with sol[of t u] tu rel(1)[OF True] show ?thesis by simp
      next
        case False
        note l = conjunct1[OF rel(2)[OF False]]
        from list_all2_ex1[OF l tu] obtain tu' where tu': "tu' \<in> set ntps"
          and n: "ok (norm_term env t) (fst tu')" "ok (norm_term env u) (snd tu')" by auto
        obtain t' u' where tu'': "tu' = (t', u')" by (cases tu')
        have "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
          using conv_sym[OF iext_norm_term(1)[OF ie n(1)[unfolded tu'' fst_conv] tyi[OF ty(1) c(1)]]] .
        also have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" using sol tu' tu'' by blast
        also have "ap \<rho> \<sigma> u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
          by (rule iext_norm_term(1)[OF ie n(2)[unfolded tu'' snd_conv] tyi[OF ty(2) c(2)]])
        finally show ?thesis .
      qed
    qed
    note sv = solves[OF i(3) ci' stps]
    have "prf_ok ax H e [] (prf_ap \<rho>' \<sigma>' pf) (ap \<rho>' \<sigma>' (th_prop state))"
      by (rule prf_validD[OF p i(1,2)]) (use sv ds(1) in auto)
    from prf_ok_assumption_proof[OF i(1,2) wP this[unfolded P] ap l _ lN]
    have core: "prf_ok ax H e [] (prf_ap \<rho>' \<sigma>' (assumption_proof Ns Bi ?n pf)) (ap \<rho>' \<sigma>' (list_implies Bs C))"
      using sv lN by (simp add: prf_ap_assumption_proof)
    from q show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> q) (ap \<rho> \<sigma> P')"
    proof (elim disjE conjE)
      assume emp: "env_is_empty env" and q: "q = assumption_proof Ns Bi ?n pf"
      have l0: "vt_lookup (tyenv env) v = None" "vt_lookup (tenv env) x = None" for v x
        using emp by (simp_all add: env_is_empty_def vt_is_empty_lookup)
      have "\<rho>' = \<rho>" "\<sigma>' = \<sigma>" by (intro ext; simp add: i(6) i(7) l0)+
      with core q rel(1)[OF emp] show ?thesis by simp
    next
      assume emp: "\<not> env_is_empty env"
        and nq: "norm_proof_remove_types env (assumption_proof Ns Bi ?n pf) = returnW q"
      have "prf_aeq (prf_ap \<rho>' \<sigma>' (assumption_proof Ns Bi ?n pf)) (prf_ap \<rho> \<sigma> q)"
        using norm_proof_ok[OF einvD(6,7)[OF ei] nq[unfolded norm_proof_remove_types_def]] ie
        by (simp add: nrel_def)
      from prf_ok_aeq[OF core this]
      have pq: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> q) (ap \<rho>' \<sigma>' (list_implies Bs C))" .
      from rel(2)[OF emp] have nP: "ok (norm_term env (list_implies Bs C)) P'" by simp
      have tP: "(\<lambda>_. propT) \<turnstile> inst \<rho>' (list_implies Bs C) : propT"
        using tyi[of "list_implies Bs C" propT] wtpD[OF wBC] by (simp add: tsubst_propT)
      note n = iext_norm_term[OF ie nP tP]
      have "closed P'"
        using nsoundD(2)[OF norm_term_sound[OF nP i(5,4)], of 0] wtpD(1)[OF wBC] by (simp add: closed_def)
      then have "gterm (ap \<rho> \<sigma> P') propT" using gterm_apI[OF \<sigma> _ n(2)] by blast
      then have "e \<turnstile> ap \<rho> \<sigma> P' : propT" by (simp add: gterm_def)
      with prf_ok.conv[OF pq conv_sym[OF n(1)]] show ?thesis .
    qed
  qed
qed

end

subsection \<open>Rotation of the premises of a subgoal\<close>

lemma rotate_downto:
  assumes "M \<le> n"
  defines "f \<equiv> \<lambda>k. if k < n - M then n - M - 1 - k else n - 1 - (k - (n - M))"
  shows "downto (integer_of_nat n - integer_of_nat M - 1) 0 @
      downto (integer_of_nat n - 1) (integer_of_nat n - integer_of_nat M) =
    map (\<lambda>k. integer_of_nat (f k)) [0..<n]"
proof -
  have e: "downto (integer_of_nat n - 1) (integer_of_nat n - integer_of_nat 0) = []"
    by (subst downto.simps) simp
  have nm: "integer_of_nat (n - M) = integer_of_nat n - integer_of_nat M"
    using int_nat_minus[OF assms(1)] by simp
  from permute_downto[of 0 n "n - M"] e show ?thesis
    by (simp add: nm f_def)
qed

lemma rotate_index:
  assumes M: "M \<le> length As" and k: "k < length As"
  defines "f \<equiv> \<lambda>k. if k < length As - M then length As - M - 1 - k else length As - 1 - (k - (length As - M))"
  shows "f k < length As \<and> rev As ! f k = (drop M As @ take M As) ! k"
proof (cases "k < length As - M")
  case True
  then have "rev As ! (length As - M - 1 - k) = As ! (M + k)" using M by (simp add: rev_nth)
  with True M show ?thesis by (simp add: f_def nth_append)
next
  case False
  then have "rev As ! (length As - 1 - (k - (length As - M))) = As ! (k - (length As - M))"
    using M k by (simp add: rev_nth)
  with False M k show ?thesis by (simp add: f_def nth_append min_def)
qed

lemma rotate_data_precise:
  assumes ok: "okT (rotate_data k i state) (th, Bs, Bi', params, asms, m)"
  obtains tpairs Bi C M where "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    "th = mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C)"
    "params = strip_all_vars Bi" "asms = strip_imp_prems (strip_all_body Bi)"
    "m = integer_of_nat M" "M \<le> length asms"
    "Bi' = Bi \<and> (M = 0 \<or> M = length asms) \<or>
      Bi' = list_forall params (list_implies (drop M asms @ take M asms) (strip_imp_concl (strip_all_body Bi)))"
proof -
  obtain tpairs Bi C where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and th: "th = mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C)"
    and ps: "params = strip_all_vars Bi" "asms = strip_imp_prems (strip_all_body Bi)"
    and cs: "(0 = m \<or> m = integer_of_nat (length asms)) \<and> Bi' = Bi \<or>
      0 < m \<and> m < integer_of_nat (length asms) \<and> Bi' = list_forall params (list_implies (drop (nat_of_integer m) asms @
        take (nat_of_integer m) asms) (strip_imp_concl (strip_all_body Bi)))"
    using ok unfolding rotate_data_def Let_def
    by (auto simp: returnW_def raiseW_def simp del: strip_all_vars.simps split: if_splits)
  define M where "M = nat_of_integer m"
  have mM: "0 \<le> m \<Longrightarrow> m = integer_of_nat M"
    by (simp add: M_def integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)
  from cs show thesis
  proof (elim disjE conjE)
    assume m: "0 = m" and b: "Bi' = Bi"
    show thesis by (rule that[OF d th ps, of 0]) (use m b in simp_all)
  next
    assume m: "m = integer_of_nat (length asms)" and b: "Bi' = Bi"
    show thesis by (rule that[OF d th ps, of "length asms"]) (use m b in simp_all)
  next
    assume m: "0 < m" "m < integer_of_nat (length asms)"
      and b: "Bi' = list_forall params (list_implies (drop (nat_of_integer m) asms @
        take (nat_of_integer m) asms) (strip_imp_concl (strip_all_body Bi)))"
    have "m = integer_of_nat M" using mM m by simp
    moreover have "M \<le> length asms" using m
      by (simp add: M_def less_integer.rep_eq integer_of_nat.rep_eq nat_of_integer.rep_eq)
    ultimately show thesis by (rule that[OF d th ps]) (rule disjI2, simp add: b M_def)
  qed
qed

lemma mk_Abst_foldr: "mk_Abst params p = foldr (\<lambda>(a, T) p. Abst a ((\<lambda>_. None) T) p) params p"
  by (simp add: mk_Abst_def)

context prf_sig
begin

lemma prf_ap_mk_AbsPs: "prf_ap \<rho> \<sigma> (mk_AbsPs ts p) = mk_AbsPs (map (map_option (ap \<rho> \<sigma>)) ts) (prf_ap \<rho> \<sigma> p)"
  by (induction ts) (simp_all add: mk_AbsPs_def prf_ap_def)

lemma prf_ap_foldr_Abst:
  "prf_ap \<rho> \<sigma> (foldr (\<lambda>(a, T) p. Abst a (g T) p) params X) =
    foldr (\<lambda>(a, T) p. Abst a (map_option (tsubst \<rho>) (g T)) p) params (prf_ap \<rho> \<sigma> X)"
  by (induction params) (auto simp: prf_ap_def)

lemma prf_ap_rotate_proof:
  "prf_ap \<rho> \<sigma> (rotate_proof Bs Bi' params asms m p) = rotate_proof Bs Bi' params asms m (prf_ap \<rho> \<sigma> p)"
proof -
  have a: "prf_ap \<rho> \<sigma> (mk_Abst params q) = mk_Abst params (prf_ap \<rho> \<sigma> q)" for q
    by (induction params) (auto simp: mk_Abst_def prf_ap_def)
  show ?thesis
    by (simp add: rotate_proof_def Let_def prf_ap_mk_AbsP prf_ap_proof_combP prf_ap_proof_combt a)
      (simp add: prf_ap_def comp_def ap_def)
qed

end

context prf_model
begin

lemma prf_ok_rotate_ann:
  fixes \<rho> :: tinst and params :: binders and ps defines "ps \<equiv> map (\<lambda>(a, T). (a, tsubst \<rho> T)) params"
  assumes p0: "prf_ok ax H e [] P (list_implies (aBs @ [list_forall ps (list_implies As c)]) C)"
    and tBs: "\<And>A. A \<in> set aBs \<Longrightarrow> e \<turnstile> A : propT \<and> closed A"
    and tB: "e \<turnstile> list_forall ps (list_implies As c) : propT"
    and cB': "closed (list_forall ps (list_implies (drop K As @ take K As) c))"
    and K: "K \<le> length As"
    and ann1: "list_all2 ann_ok ts1 (aBs @ [list_forall ps (list_implies (drop K As @ take K As) c)])"
    and ann2: "list_all2 ann_ok ts2 As" and tg: "\<forall>(a, T)\<in>set params. tann_ok (g T) (tsubst \<rho> T)"
  shows "prf_ok ax H e [] (mk_AbsPs ts1 (proof_combP P (map PBound (downto (integer_of_nat (length aBs)) 1) @
    [foldr (\<lambda>(a, T) p. Abst a (g T) p) params (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat (length As)))
      (map Bound (downto (integer_of_nat (length params) - 1) 0)))
      (map PBound (downto (integer_of_nat (length As) - integer_of_nat K - 1) 0 @
        downto (integer_of_nat (length As) - 1) (integer_of_nat (length As) - integer_of_nat K)))))])))
    (list_implies (aBs @ [list_forall ps (list_implies (drop K As @ take K As) c)]) C)"
proof -
  let ?As' = "drop K As @ take K As"
  let ?B = "list_forall ps (list_implies As c)" and ?B' = "list_forall ps (list_implies ?As' c)"
  let ?n = "length As" and ?j = "length aBs"
  let ?Hs = "rev (aBs @ [?B'])"
  have sA: "set ?As' = set As" by (rule set_rotate_take_drop)
  have tB': "e \<turnstile> ?B' : propT" by (rule list_forall_implies_perm(1)[OF tB sA])
  have cHs: "e \<turnstile> A : propT \<and> closed A" if "A \<in> set ?Hs" for A using that tBs tB' cB' by auto
  have cps: "\<forall>(a, T)\<in>set ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    and tX: "pushes e (map snd ps) \<turnstile> list_implies As c : propT"
    using tB by (simp_all add: typing_list_forall)
  let ?E = "pushes e (map snd ps)"
  have msp: "map snd ps = map (tsubst \<rho>) (map snd params)" unfolding ps_def by (induction params) auto
  have lps: "length ps = length params" by (simp add: ps_def)
  note tD = typing_list_impliesD[OF tX]
  have tAs: "?E \<turnstile> A : propT" if "A \<in> set As" for A using tD that by blast
  have tHsE0: "?E \<turnstile> A : propT" if "A \<in> set ?Hs" for A
    using cHs[OF that] typing_closed by blast
  have tHsE: "?E \<turnstile> A : propT" if "A \<in> set (rev As @ ?Hs)" for A
  proof -
    from that have "A \<in> set As \<or> A \<in> set ?Hs" by (simp only: set_append set_rev Un_iff)
    then show ?thesis using tAs tHsE0 by blast
  qed
  \<comment> \<open>the rotated subgoal, instantiated with the parameters\<close>
  have pB: "prf_ok ax H ?E (rev As @ ?Hs) (PBound (integer_of_nat ?n)) ?B'"
    using prf_ok_PBound_nth[of ?n "rev As @ ?Hs" ?E ax H] tHsE[of ?B'] by (simp add: nth_append)
  have nl: "\<not> loose_bvar (list_implies ?As' c) (ilength ps)"
    using cB' by (simp add: closed_def loose_bvar_list_forall)
  have pc: "prf_ok ax H ?E (rev As @ ?Hs) (proof_combt (PBound (integer_of_nat ?n)) (map Bound (downto (ilength ps - 1) 0)))
      (list_implies ?As' c)"
  proof (rule prf_ok_combt_bounds)
    show "prf_ok ax H ?E (rev As @ ?Hs) (PBound (integer_of_nat ?n))
        (list_forall ps (incr_bv (ilength ps) (ilength ps) (list_implies ?As' c)))"
      using pB incr_bv_no_loose[OF nl] by simp
    show "\<forall>l<length ps. ?E (of_nat (length ps - 1 - l)) = snd (ps ! l)"
    proof (intro allI impI)
      fix l assume l: "l < length ps"
      have nl: "nat (int (length ps) - (1 + int l)) = length ps - Suc l" using l by arith
      have "?E (of_nat (length ps - 1 - l)) = rev (map snd ps) ! (length ps - 1 - l)"
        using l by (subst pushes_nth) (simp_all add: ilength_eq less_integer.rep_eq less_eq_integer.rep_eq
          integer_of_nat.rep_eq nat_of_integer.rep_eq integer_of_nat_eq_of_nat nl)
      with l show "?E (of_nat (length ps - 1 - l)) = snd (ps ! l)" by (simp add: rev_nth)
    qed
  qed
  \<comment> \<open>the assumptions, in the rotated order\<close>
  define f where "f = (\<lambda>k. if k < ?n - K then ?n - K - 1 - k else ?n - 1 - (k - (?n - K)))"
  have "list_all2 (\<lambda>q A. prf_ok ax H ?E (rev As @ ?Hs) q A) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n])) ?As'"
  proof (rule prf_ok_PBounds)
    show "f k < length (rev As @ ?Hs) \<and> (rev As @ ?Hs) ! f k = ?As' ! k" if "k < length ?As'" for k
      using rotate_index[OF K, of k] that by (auto simp: f_def nth_append)
  qed (use K tHsE in auto)
  from prf_ok_proof_combP[OF pc this]
  have "prf_ok ax H ?E (rev As @ ?Hs) (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))) c" .
  from prf_ok_mk_AbsPs[OF tAs ann2 this]
  have "prf_ok ax H ?E ?Hs (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))))
      (list_implies As c)" .
  moreover have "map (incr_bv (ilength params) 0) ?Hs = ?Hs"
    using cHs by (intro map_idI incr_bv_closed) auto
  ultimately have "prf_ok ax H (pushes e (map (tsubst \<rho>) (map snd params))) (map (incr_bv (ilength params) 0) ?Hs)
      (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))))
      (list_implies As c)"
    by (simp add: msp)
  moreover have "\<forall>(a, T)\<in>set params. cert_typ alg ar (tsubst \<rho> T) \<and> tann_ok (g T) (tsubst \<rho> T)"
  proof (intro ballI, clarify)
    fix a T assume aT: "(a, T) \<in> set params"
    then have "(a, tsubst \<rho> T) \<in> set ps" by (force simp: ps_def)
    with cps tg aT show "cert_typ alg ar (tsubst \<rho> T) \<and> tann_ok (g T) (tsubst \<rho> T)"
      by auto
  qed
  ultimately have "prf_ok ax H e ?Hs (foldr (\<lambda>(a, T) p. Abst a (g T) p) params
      (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n])))))
      (list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) params) (list_implies As c))"
    by (rule prf_ok_abst_chain)
  then have pX: "prf_ok ax H e ?Hs (foldr (\<lambda>(a, T) p. Abst a (g T) p) params (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n])))))
      ?B"
    by (simp only: ps_def)
  \<comment> \<open>the other subgoals\<close>
  have dj: "downto (integer_of_nat ?j) 1 = map (\<lambda>k. integer_of_nat (?j - k)) [0..<?j]"
  proof -
    have "downto (integer_of_nat ?j) 1 =
        map (\<lambda>l. integer_of_nat (nat_of_integer (integer_of_nat ?j) - l)) [0..<nat_of_integer (integer_of_nat ?j - 1 + 1)]"
      by (rule downto_nat) (simp_all add: less_eq_integer.rep_eq integer_of_nat.rep_eq)
    then show ?thesis by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq)
  qed
  have "list_all2 (\<lambda>q A. prf_ok ax H e ?Hs q A) (map PBound (map (\<lambda>k. integer_of_nat (?j - k)) [0..<?j])) aBs"
  proof (rule prf_ok_PBounds)
    show "?j - k < length ?Hs \<and> ?Hs ! (?j - k) = aBs ! k" if "k < length aBs" for k
      using that by (auto simp: nth_append rev_nth nth_Cons' Suc_diff_Suc)
  qed (use cHs in auto)
  then have "list_all2 (\<lambda>q A. prf_ok ax H e ?Hs q A)
      (map PBound (downto (integer_of_nat ?j) 1) @ [foldr (\<lambda>(a, T) p. Abst a (g T) p) params (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))))])
      (aBs @ [?B])"
    unfolding dj by (rule list_all2_appendI) (intro list_all2_Cons[THEN iffD2] conjI pX list.rel_intros(1))
  from prf_ok_proof_combP[OF prf_ok_append[OF p0, of ?Hs, unfolded append_Nil] this]
  have "prf_ok ax H e (rev (aBs @ [?B']) @ []) (proof_combP P
      (map PBound (downto (integer_of_nat ?j) 1) @ [foldr (\<lambda>(a, T) p. Abst a (g T) p) params (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))))])) C"
    by simp
  from prf_ok_mk_AbsPs[OF _ ann1 this] cHs
  have fin: "prf_ok ax H e [] (mk_AbsPs ts1 (proof_combP P
      (map PBound (downto (integer_of_nat ?j) 1) @ [foldr (\<lambda>(a, T) p. Abst a (g T) p) params (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat ?n))
      (map Bound (downto (ilength ps - 1) 0))) (map PBound (map (\<lambda>k. integer_of_nat (f k)) [0..<?n]))))])))
      (list_implies (aBs @ [?B']) C)"
    by auto
  have dK: "downto (integer_of_nat ?n - integer_of_nat K - 1) 0 @
      downto (integer_of_nat ?n - 1) (integer_of_nat ?n - integer_of_nat K) = map (\<lambda>k. integer_of_nat (f k)) [0..<?n]"
    unfolding f_def by (rule rotate_downto[OF K])
  have ip: "ilength ps = integer_of_nat (length params)" by (simp add: ilength_eq lps)
  show ?thesis
    unfolding dK using fin unfolding ip .
qed

lemma prf_ok_rotate:
  fixes \<rho> :: tinst and params :: binders and ps defines "ps \<equiv> map (\<lambda>(a, T). (a, tsubst \<rho> T)) params"
  assumes p0: "prf_ok ax H e [] P (list_implies (aBs @ [list_forall ps (list_implies As c)]) C)"
    and tBs: "\<And>A. A \<in> set aBs \<Longrightarrow> e \<turnstile> A : propT \<and> closed A"
    and tB: "e \<turnstile> list_forall ps (list_implies As c) : propT"
    and cB': "closed (list_forall ps (list_implies (drop K As @ take K As) c))"
    and K: "K \<le> length As" and l: "length Bsr = length aBs" "length asmsr = length As"
  shows "prf_ok ax H e [] (rotate_proof Bsr Bir params asmsr (integer_of_nat K) P)
    (list_implies (aBs @ [list_forall ps (list_implies (drop K As @ take K As) c)]) C)"
proof -
  have a1: "list_all2 ann_ok (map (\<lambda>_. None) (aBs @ [list_forall ps (list_implies (drop K As @ take K As) c)]))
      (aBs @ [list_forall ps (list_implies (drop K As @ take K As) c)])"
    and a2: "list_all2 ann_ok (map (\<lambda>_. None) As) As"
    by (rule list_all2_ann_ok_None)+
  have tg: "\<forall>(a, T)\<in>set params. tann_ok ((\<lambda>_. None) T) (tsubst \<rho> T)" by auto
  have m1: "mk_AbsP (Bsr @ [Bir]) X = mk_AbsPs (map (\<lambda>_. None) (aBs @ [list_forall ps (list_implies (drop K As @ take K As) c)])) X"
    for X by (simp add: mk_AbsP_AbsPs l map_replicate_const)
  have m2: "mk_AbsP asmsr X = mk_AbsPs (map (\<lambda>_. None) As) X" for X
    by (simp add: mk_AbsP_AbsPs l map_replicate_const)
  from prf_ok_rotate_ann[OF p0[unfolded ps_def] tBs tB[unfolded ps_def] cB'[unfolded ps_def] K
      a1[unfolded ps_def] a2 tg, folded ps_def]
  show ?thesis by (simp only: rotate_proof_def Let_def m1 m2 l mk_Abst_foldr)
qed

theorem rotate_proof_valid_ann:
  assumes ok: "okT (rotate_data k i state) (th, Bs, Bi', params, asms, m)"
    and p: "prf_valid ax H (th_tpairs state) pf (th_prop state)" and w: "wtp (th_prop state)"
    and ann1: "\<And>\<rho> \<sigma>. cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow>
      list_all2 ann_ok (map (map_option (ap \<rho> \<sigma>)) ts1) (map (ap \<rho> \<sigma>) (Bs @ [Bi']))"
    and ann2: "\<And>\<rho> \<sigma>. cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> list_all2 ann_ok (map (map_option (ap \<rho> \<sigma>)) ts2) (map (ap \<rho> \<sigma>) asms)"
    and tg: "\<forall>(a, T)\<in>set params. g T = None \<or> g T = Some T"
  shows "prf_valid ax H (th_tpairs th) (mk_AbsPs ts1 (proof_combP pf (map PBound (downto (integer_of_nat (length Bs)) 1) @
    [foldr (\<lambda>(a, T) p. Abst a (g T) p) params (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat (length asms)))
      (map Bound (downto (integer_of_nat (length params) - 1) 0)))
      (map PBound (downto (integer_of_nat (length asms) - m - 1) 0 @
        downto (integer_of_nat (length asms) - 1) (integer_of_nat (length asms) - m)))))])))
    (th_prop th)"
proof -
  obtain tpairs Bi C K where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and th: "th = mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C)"
    and ps: "params = strip_all_vars Bi" and As: "asms = strip_imp_prems (strip_all_body Bi)"
    and mM: "m = integer_of_nat K" and K: "K \<le> length asms"
    and Bi'0: "Bi' = Bi \<and> (K = 0 \<or> K = length asms) \<or>
      Bi' = list_forall params (list_implies (drop K asms @ take K asms) (strip_imp_concl (strip_all_body Bi)))"
    by (rule rotate_data_precise[OF ok])
  note ds = okT_dest_state[OF d]
  define c where "c = strip_imp_concl (strip_all_body Bi)"
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  have tP: "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi]) C : propT" using wtpD(2)[OF w] P by simp
  note tD = typing_list_impliesD[OF tP]
  have tBi: "(\<lambda>_. propT) \<turnstile> Bi : propT" using tD by simp
  have Bi: "Bi = list_forall params (list_implies asms c)"
  proof -
    have "pushes (\<lambda>_. propT) (map snd params) \<turnstile> strip_all_body Bi : propT"
      using tBi list_forall_strip_all[OF tBi] unfolding ps by (metis typing_list_forall)
    from list_implies_strip_imp[OF this] list_forall_strip_all[OF tBi] show ?thesis
      by (simp add: ps As c_def)
  qed
  have Bi': "Bi' = list_forall params (list_implies (drop K asms @ take K asms) c)"
  proof (cases "Bi' = Bi \<and> (K = 0 \<or> K = length asms)")
    case True
    then show ?thesis using Bi by auto
  next
    case False
    with Bi'0 have "Bi' = list_forall params (list_implies (drop K asms @ take K asms) (strip_imp_concl (strip_all_body Bi)))"
      by blast
    then show ?thesis by (simp only: c_def)
  qed
  have tBi0: "(\<lambda>_. propT) \<turnstile> list_forall params (list_implies asms c) : propT" using tBi Bi by simp
  note pm = list_forall_implies_perm[OF tBi0 set_rotate_take_drop[of K asms]]
  have w': "wtp (list_implies (Bs @ [Bi']) C)"
  proof (rule wtpI)
    show "closed (list_implies (Bs @ [Bi']) C)"
      using wtpD(1)[OF w] P pm(2) Bi Bi' by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi']) C : propT"
      using tD pm(1) Bi' typing_list_implies_imp[OF tP] by (intro typing_list_impliesI) auto
  qed
  have wps: "wtp A" if "A \<in> set (Bs @ [Bi'])" for A
    using w' that wtp_list_implies[where As = "Bs @ [Bi']" and As' = "Bs @ [Bi']" and B = C and B' = C] by auto
  have wBi: "wtp Bi"
    using w P wtp_list_implies[where As = "Bs @ [Bi]" and As' = "Bs @ [Bi]" and B = C and B' = C] by auto
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have cl: "closed (ap \<rho> \<sigma> s)" if "closed s" for s using that \<sigma> by (simp add: closed_def)
    have tw: "e \<turnstile> ap \<rho> \<sigma> A : propT \<and> closed (ap \<rho> \<sigma> A)" if "wtp A" for A
      using typing_ap_wtp[OF that \<rho> \<sigma>] cl[OF wtpD(1)[OF that]] by simp
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> (th_prop state))"
      by (rule prf_validD[OF p \<rho> \<sigma>]) (use sol th ds(1) in \<open>simp add: mk_rep_def\<close>)
    then have p0: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (list_implies (map (ap \<rho> \<sigma>) Bs @
        [list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) params) (list_implies (map (ap \<rho> \<sigma>) asms) (ap \<rho> \<sigma> c))])
        (ap \<rho> \<sigma> C))"
      by (simp add: P Bi ap_list_implies ap_list_forall)
    have tB: "e \<turnstile> list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) params) (list_implies (map (ap \<rho> \<sigma>) asms) (ap \<rho> \<sigma> c)) : propT"
      using tw[OF wBi] by (simp add: Bi ap_list_implies ap_list_forall)
    have cB': "closed (list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) params)
        (list_implies (drop K (map (ap \<rho> \<sigma>) asms) @ take K (map (ap \<rho> \<sigma>) asms)) (ap \<rho> \<sigma> c)))"
      using tw[OF wps[of Bi']] by (simp add: Bi' ap_list_implies ap_list_forall drop_map take_map)
    have tBs: "e \<turnstile> A : propT \<and> closed A" if "A \<in> set (map (ap \<rho> \<sigma>) Bs)" for A
      using that tw wps by auto
    have K': "K \<le> length (map (ap \<rho> \<sigma>) asms)" using K by simp
    have a1: "list_all2 ann_ok (map (map_option (ap \<rho> \<sigma>)) ts1) (map (ap \<rho> \<sigma>) Bs @ [list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) params)
          (list_implies (drop K (map (ap \<rho> \<sigma>) asms) @ take K (map (ap \<rho> \<sigma>) asms)) (ap \<rho> \<sigma> c))])"
      using ann1[OF \<rho> \<sigma>]
      by (simp only: Bi' ap_list_implies ap_list_forall drop_map take_map map_append list.map)
    have tg': "\<forall>(a, T)\<in>set params. tann_ok (map_option (tsubst \<rho>) (g T)) (tsubst \<rho> T)" using tg by auto
    note r = prf_ok_rotate_ann[OF p0 tBs tB cB' K' a1 ann2[OF \<rho> \<sigma>] tg']
    have "ap \<rho> \<sigma> (th_prop th) = list_implies (map (ap \<rho> \<sigma>) Bs @ [list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) params)
          (list_implies (drop K (map (ap \<rho> \<sigma>) asms) @ take K (map (ap \<rho> \<sigma>) asms)) (ap \<rho> \<sigma> c))]) (ap \<rho> \<sigma> C)"
      by (simp only: th mk_rep_def thm_rep.simps Bi' ap_list_implies ap_list_forall drop_map take_map map_append list.map)
    then show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (mk_AbsPs ts1 (proof_combP pf (map PBound (downto (integer_of_nat (length Bs)) 1) @
        [foldr (\<lambda>(a, T) p. Abst a (g T) p) params (mk_AbsPs ts2 (proof_combP (proof_combt (PBound (integer_of_nat (length asms)))
          (map Bound (downto (integer_of_nat (length params) - 1) 0)))
          (map PBound (downto (integer_of_nat (length asms) - m - 1) 0 @
            downto (integer_of_nat (length asms) - 1) (integer_of_nat (length asms) - m)))))]))))
        (ap \<rho> \<sigma> (th_prop th))"
      using r by (simp add: prf_ap_mk_AbsPs prf_ap_proof_combP prf_ap_proof_combt prf_ap_foldr_Abst mM comp_def)
  qed
qed


theorem rotate_proof_valid:
  assumes ok: "okT (rotate_data k i state) (th, Bs, Bi', params, asms, m)"
    and p: "prf_valid ax H (th_tpairs state) pf (th_prop state)" and w: "wtp (th_prop state)"
  shows "prf_valid ax H (th_tpairs th) (rotate_proof Bs Bi' params asms m pf) (th_prop th)"
proof -
  have "prf_valid ax H (th_tpairs th) (mk_AbsPs (map (\<lambda>_. None) (Bs @ [Bi'])) (proof_combP pf
      (map PBound (downto (integer_of_nat (length Bs)) 1) @
      [foldr (\<lambda>(a, T) p. Abst a ((\<lambda>_. None) T) p) params (mk_AbsPs (map (\<lambda>_. None) asms)
        (proof_combP (proof_combt (PBound (integer_of_nat (length asms)))
        (map Bound (downto (integer_of_nat (length params) - 1) 0)))
        (map PBound (downto (integer_of_nat (length asms) - m - 1) 0 @
          downto (integer_of_nat (length asms) - 1) (integer_of_nat (length asms) - m)))))])))
      (th_prop th)"
    by (rule rotate_proof_valid_ann[OF ok p w]) (auto simp: comp_def intro!: list_all2_appendI list_all2_ann_ok_None_len)
  then show ?thesis by (simp add: rotate_proof_def Let_def mk_AbsP_AbsPs mk_Abst_foldr)
qed

end

subsection \<open>Instantiation by a unifier of the flex-flex pairs\<close>

text \<open>
  The results of \<^const>\<open>flexflex_rule\<close> have no trivial flex-flex pairs (with the fix of
  \<open>patches/19-thm-flexflex-trivial.patch\<close>; without it, the empty unifier keeps them):
\<close>

context pure_model
begin

theorem fnewth_no_trivial_pairs:
  assumes "ok (fnewth th0 env) th"
  shows "\<forall>(t, u)\<in>set (th_tpairs th). \<not> aconv_term t u"
proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th0). aconv_term t u)")
  case True
  with assms have "th = th0" by (simp add: fnewth_def)
  with True show ?thesis by auto
next
  case False
  obtain ntps P where "th_tpairs th = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps"
    by (rule fnewth_ok[OF assms False])
  then show ?thesis by auto
qed

end

context prf_model
begin

text \<open>
  The proof of a result of \<^const>\<open>flexflex_rule\<close> for a unifier \<open>env\<close> (which satisfies the
  invariants of the results of unification) that is not empty or leaves trivial flex-flex pairs
  (with the fix of \<open>patches/19-thm-flexflex-trivial.patch\<close>) is the normalisation of the proof of
  the theorem:
\<close>

theorem flexflex_proof_valid:
  assumes ok: "ok (fnewth th0 env) th" and ne: "\<not> (env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th0). aconv_term t u))"
    and nq: "norm_proof_remove_types env pf = returnW q"
    and p: "prf_valid ax H (th_tpairs th0) pf (th_prop th0)" and wP: "wtp (th_prop th0)"
    and tw: "\<And>t u. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and ei: "einv A K env" and wi: "winv env X"
  shows "prf_valid ax H (th_tpairs th) q (th_prop th)"
proof -
  obtain ntps P where nt: "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu'))
      (th_tpairs th0) ntps"
    and nP: "ok (norm_term env (th_prop th0)) P"
    and th: "th_tpairs th = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps" "th_prop th = P"
    by (rule fnewth_ok[OF ok ne])
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    obtain \<rho>' \<sigma>' where ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" by (rule iext_exists_sb[OF ei wi \<rho> \<sigma>]) blast
    note i = iextD[OF ie]
    have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
    have tyi: "(\<lambda>_. propT) \<turnstile> inst \<rho>' s : tsubst \<rho>' T" if "\<And>e. e \<turnstile> s : T" "closed s" for s T
      using typing_closed[OF typing_inst[OF that(1) cert_inst_inst_ok[OF ci']]] that(2) by (simp add: closed_def)
    have "prf_ok ax H e [] (prf_ap \<rho>' \<sigma>' pf) (ap \<rho>' \<sigma>' (th_prop th0))"
    proof (rule prf_validD[OF p i(1,2)])
      fix t u assume tu: "(t, u) \<in> set (th_tpairs th0)"
      from list_all2_ex1[OF nt tu] obtain tu' where tu': "tu' \<in> set ntps"
        and n: "ok (norm_term env t) (fst tu')" "ok (norm_term env u) (snd tu')" by auto
      obtain t' u' where tu'': "tu' = (t', u')" by (cases tu')
      from tw[OF tu] obtain T where c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
      have "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
        using conv_sym[OF iext_norm_term(1)[OF ie n(1)[unfolded tu'' fst_conv] tyi[OF ty(1) c(1)]]] .
      also have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
      proof (cases "aconv_term t' u'")
        case True
        then show ?thesis by (blast intro: aconv_term_conv aconv_term_ap)
      next
        case False
        with tu' tu'' th(1) show ?thesis by (intro sol) auto
      qed
      also have "ap \<rho> \<sigma> u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
        by (rule iext_norm_term(1)[OF ie n(2)[unfolded tu'' snd_conv] tyi[OF ty(2) c(2)]])
      finally show "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" .
    qed
    moreover have "prf_aeq (prf_ap \<rho>' \<sigma>' pf) (prf_ap \<rho> \<sigma> q)"
      using norm_proof_ok[OF einvD(6,7)[OF ei] nq[unfolded norm_proof_remove_types_def]] ie
      by (simp add: nrel_def)
    ultimately have pq: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> q) (ap \<rho>' \<sigma>' (th_prop th0))" by (rule prf_ok_aeq)
    have tP: "(\<lambda>_. propT) \<turnstile> inst \<rho>' (th_prop th0) : propT"
      using tyi[of "th_prop th0" propT] wtpD[OF wP] by (simp add: tsubst_propT)
    note n = iext_norm_term[OF ie nP tP]
    have "closed P"
      using nsoundD(2)[OF norm_term_sound[OF nP i(5,4)], of 0] wtpD(1)[OF wP] by (simp add: closed_def)
    then have "gterm (ap \<rho> \<sigma> P) propT" using gterm_apI[OF \<sigma> _ n(2)] by blast
    then have "e \<turnstile> ap \<rho> \<sigma> P : propT" by (simp add: gterm_def)
    from prf_ok.conv[OF pq conv_sym[OF n(1)] this]
    show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> q) (ap \<rho> \<sigma> (th_prop th))" by (simp add: th(2))
  qed
qed

end

subsection \<open>Rules that keep the proof\<close>

context prf_model
begin

theorem weaken_proof_valid:
  assumes ok: "okT (weaken ct th0) th" and p: "prf_valid ax (set hs) (th_tpairs th0) pf (th_prop th0)"
  shows "prf_valid ax (set (A # hs)) (th_tpairs th) pf (th_prop th)"
proof -
  from ok have "th = th0" by (auto simp: weaken_def returnW_def raiseW_def Let_def split: if_splits)
  with prf_valid_mono[OF p, of "set (A # hs)"] show ?thesis by auto
qed

theorem renamed_prop_proof_valid:
  assumes ok: "okT (renamed_prop P th0) th" and p: "prf_valid ax H (th_tpairs th0) pf (th_prop th0)"
    and w: "wtp (th_prop th0)"
  shows "prf_valid ax H (th_tpairs th) pf (th_prop th)"
proof -
  from ok have a: "aconv_term (th_prop th0) P" and th: "th = mk_rep (th_maxidx th0) (th_tpairs th0) P"
    by (auto simp: renamed_prop_def returnW_def raiseW_def split: if_splits)
  have wP: "wtp P" using w a loose_bvar1_aconv[OF a]
    by (auto simp: wtp_def typing_aconv closed_iff_loose_bvar1)
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> (th_prop th0))"
      by (rule prf_validD[OF p \<rho> \<sigma>]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    moreover have "ap \<rho> \<sigma> (th_prop th0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> P"
      by (rule conv_ap[OF aconv_term_conv[OF a] cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
    moreover have "e \<turnstile> ap \<rho> \<sigma> P : propT" by (rule typing_ap_wtp[OF wP \<rho> \<sigma>])
    ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> (th_prop th))"
      by (simp add: th mk_rep_def prf_ok.conv)
  qed
qed

theorem adjust_maxidx_thm_proof_valid:
  "prf_valid ax H (th_tpairs th0) pf (th_prop th0) \<Longrightarrow>
    prf_valid ax H (th_tpairs (adjust_maxidx_thm i th0)) pf (th_prop (adjust_maxidx_thm i th0))"
  by (simp add: adjust_maxidx_thm_def mk_rep_def)

end

subsection \<open>Generalization of free variables\<close>

lemma occs_Free: "occs (Free x T) t \<longleftrightarrow> (x, T) \<in> pfrees t"
  by (induction t) (auto simp: occs_def)

lemma fnames_pfrees: "x \<in> fnames t \<longleftrightarrow> (\<exists>T. (x, T) \<in> pfrees t)"
  by (induction t) auto

lemma Free_aterms: "Free x T \<in> set (aterms t) \<longleftrightarrow> (x, T) \<in> pfrees t"
  by (induction t rule: aterms.induct) auto

lemma abstract_over_aux_Free_id: "(x, T) \<notin> pfrees t \<Longrightarrow> abstract_over_aux (Free x T) lev t = t"
  by (induction "Free x T" lev t rule: abstract_over_aux.induct) (auto simp: aconv_term_atom)

lemma pfrees_abstract_over_aux:
  "pfrees (abstract_over_aux (Free x T) lev t) = pfrees t - {(x, T)}"
  by (induction "Free x T" lev t rule: abstract_over_aux.induct) (auto simp: aconv_term_atom)

lemma vars_abstract_over_aux: "vars (abstract_over_aux (Free x T) lev t) = vars t"
  by (induction "Free x T" lev t rule: abstract_over_aux.induct) (auto simp: aconv_term_atom)

lemma ttvars_abstract_over_aux: "ttvars (abstract_over_aux (Free x T) lev t) \<subseteq> ttvars t"
  by (induction "Free x T" lev t rule: abstract_over_aux.induct) (auto simp: aconv_term_atom)

lemma prf_abstract_term_eq: "prf_abstract_term v lev t = abstract_over_aux v lev t"
  by (induction v lev t rule: prf_abstract_term.induct) simp_all

lemma prf_terms_prf_abstract_over_aux:
  "t' \<in> prf_terms (prf_abstract_over_aux v lev p) \<Longrightarrow> \<exists>t\<in>prf_terms p. \<exists>l. t' = abstract_over_aux v l t"
  by (induction v lev p rule: prf_abstract_over_aux.induct) (auto simp: prf_abstract_term_eq)

lemma prf_atoms_prf_abstract_over_aux: "prf_atoms (prf_abstract_over_aux v lev p) = prf_atoms p"
  by (induction v lev p rule: prf_abstract_over_aux.induct) simp_all

lemma fsubst_cong: "(\<And>y U. (y, U) \<in> pfrees t \<Longrightarrow> \<tau>1 y U = \<tau>2 y U) \<Longrightarrow> fsubst \<tau>1 t = fsubst \<tau>2 t"
proof (induction t arbitrary: \<tau>1 \<tau>2)
  case (Abs a T t)
  have "fsubst (\<lambda>x U. lift (\<tau>1 x U) 0) t = fsubst (\<lambda>x U. lift (\<tau>2 x U) 0) t"
    by (rule Abs.IH) (use Abs.prems in simp)
  then show ?case by simp
next
  case (App s t)
  have "fsubst \<tau>1 s = fsubst \<tau>2 s" "fsubst \<tau>1 t = fsubst \<tau>2 t"
    by (rule App.IH(1), use App.prems in simp) (rule App.IH(2), use App.prems in simp)
  then show ?case by simp
qed simp_all

lemma lift_closed0: "closed s \<Longrightarrow> lift s 0 = s"
  by (simp add: incr_bv_no_loose closed_def)

lemma fsubst_fsubst: "fsubst \<tau>1 (fsubst \<tau>2 t) = fsubst (\<lambda>y U. fsubst \<tau>1 (\<tau>2 y U)) t"
proof (induction t arbitrary: \<tau>1 \<tau>2)
  case (Abs a T t)
  have "fsubst (\<lambda>x U. lift (\<tau>1 x U) 0) (fsubst (\<lambda>x U. lift (\<tau>2 x U) 0) t) =
      fsubst (\<lambda>y U. fsubst (\<lambda>x U. lift (\<tau>1 x U) 0) (lift (\<tau>2 y U) 0)) t"
    by (rule Abs.IH)
  also have "\<dots> = fsubst (\<lambda>y U. lift (fsubst \<tau>1 (\<tau>2 y U)) 0) t"
    by (simp add: fsubst_lift)
  finally show ?case by simp
qed simp_all

text \<open>A substitution of closed terms that keeps \<open>Free x T\<close> commutes with the abstraction over it:\<close>

lemma fsubst_abstract_over_aux:
  assumes "\<tau> x T = Free x T" and "\<And>y U. (y, U) \<noteq> (x, T) \<Longrightarrow> closed (\<tau> y U) \<and> (x, T) \<notin> pfrees (\<tau> y U)"
  shows "fsubst \<tau> (abstract_over_aux (Free x T) lev t) = abstract_over_aux (Free x T) lev (fsubst \<tau> t)"
  using assms
proof (induction t arbitrary: \<tau> lev)
  case (Abs a U t)
  have l: "(\<lambda>y V. lift (\<tau> y V) 0) = \<tau>"
  proof (intro ext)
    fix y V show "lift (\<tau> y V) 0 = \<tau> y V"
      using Abs.prems by (cases "(y, V) = (x, T)") (auto simp: lift_closed0)
  qed
  show ?case using Abs.IH[of \<tau> "lev + 1"] Abs.prems by (simp add: aconv_term_atom l)
next
  case (Free y U)
  then show ?case by (cases "(y, U) = (x, T)") (auto simp: aconv_term_atom abstract_over_aux_Free_id)
qed (auto simp: aconv_term_atom)

text \<open>Instantiating the abstraction over \<open>Free x T\<close> with a closed term substitutes it:\<close>

lemma subst_abstract_over_aux:
  assumes s: "closed s"
  shows "\<not> loose_bvar t lev \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    (abstract_over_aux (Free x T) lev t)[s/lev] = fsubst (\<lambda>y U. if y = x \<and> U = T then s else Free y U) t"
proof (induction t arbitrary: lev)
  case (Abs a U t)
  have l: "(\<lambda>y V. lift (if y = x \<and> V = T then s else Free y V) 0) = (\<lambda>y V. if y = x \<and> V = T then s else Free y V)"
    using s by (intro ext) (simp add: lift_closed0)
  have "(abstract_over_aux (Free x T) (lev + 1) t)[s/lev + 1] =
      fsubst (\<lambda>y U. if y = x \<and> U = T then s else Free y U) t"
    by (rule Abs.IH) (use Abs.prems in simp_all)
  then show ?case using s by (simp add: aconv_term_atom l lift_closed0)
next
  case (Free y U)
  then show ?case by (auto simp: aconv_term_atom)
qed (auto simp: aconv_term_atom)

lemma generalize_term_fsubst:
  "generalize_term [] frees i t = fsubst (\<lambda>y U. if y \<in> set frees then Var (clean_index (y, i)) U else Free y U) t"
proof (induction t)
  case (Abs a T t)
  have "(\<lambda>y U. lift (if y \<in> set frees then Var (clean_index (y, i)) U else Free y U) 0) =
      (\<lambda>y U. if y \<in> set frees then Var (clean_index (y, i)) U else Free y U)"
    by (intro ext) simp
  with Abs show ?case by simp
qed simp_all

lemma map_proof_terms_ident: "map_proof_terms (\<lambda>t. t) (\<lambda>T. T) p = p"
proof (induction p)
  case (AbsP a t q) then show ?case by (cases t) simp_all
next
  case (PAppt q t) then show ?case by (cases t) simp_all
next
  case (PThm x) then show ?case by (cases x) (simp add: option.map_ident hd_set_types_def)
qed (simp_all add: option.map_ident)

text \<open>The variables that \<^const>\<open>generalize_proof\<close> generalizes:\<close>

definition gen_step :: "name list \<Rightarrow> pterm \<Rightarrow> (name \<times> ptyp) list \<Rightarrow> (name \<times> ptyp) list" where
  "gen_step frees a acc = (case a of Free x T \<Rightarrow> if x \<in> set frees then insert_free (x, T) acc else acc | _ \<Rightarrow> acc)"

lemma gen_step_fold:
  "set (fold (gen_step frees) xs acc) = set acc \<union> {(x, T). Free x T \<in> set xs \<and> x \<in> set frees} \<and>
    (distinct acc \<longrightarrow> distinct (fold (gen_step frees) xs acc))"
proof (induction xs arbitrary: acc)
  case (Cons a xs)
  have "set (gen_step frees a acc) = set acc \<union> {(x, T). Free x T = a \<and> x \<in> set frees} \<and>
      (distinct acc \<longrightarrow> distinct (gen_step frees a acc))"
    by (cases a) (auto simp: gen_step_def insert_free_def)
  with Cons.IH[of "gen_step frees a acc"] show ?case by auto
qed simp

context prf_model
begin

lemma typing_pfrees_cert: "e \<turnstile> t : U \<Longrightarrow> (x, T) \<in> pfrees t \<Longrightarrow> cert_typ alg ar T"
  by (induction rule: typing.induct) auto

lemma wt_thm_forall_free:
  assumes wt: "wt_thm m hs tps Q" and xT: "(x, T) \<in> pfrees Q"
  shows "wt_thm m hs tps (all_const T $ Abs x T (abstract_over (Free x T) Q))"
proof -
  have wQ: "wtp Q" using wt by (simp add: wt_thm_def)
  have cT: "cert_typ alg ar T" by (rule typing_pfrees_cert[OF wtpD(2)[OF wQ] xT])
  have nl: "\<not> loose_bvar Q k" if "0 \<le> k" for k
    using wtpD(1)[OF wQ] that loose_bvar_mono by (auto simp: closed_def)
  have "wtp (all_const T $ Abs x T (abstract_over (Free x T) Q))"
  proof (rule wtpI)
    show "closed (all_const T $ Abs x T (abstract_over (Free x T) Q))"
      using loose_bvar_abstract_over_aux[OF nl[of 1], of 0 "Free x T"]
      by (simp add: closed_def abstract_over_def all_const_def)
    have "(\<lambda>_. propT)\<langle>0:T\<rangle> \<turnstile> abstract_over (Free x T) Q : propT"
      unfolding abstract_over_def
      by (rule typing_abstract_over_aux[OF _ wtpD(2)[OF wQ]]) (use nl in \<open>simp_all add: shift_def\<close>)
    then show "(\<lambda>_. propT) \<turnstile> all_const T $ Abs x T (abstract_over (Free x T) Q) : propT"
      using cT by (simp add: typing_all_const all_type_def cert_typ_fun)
  qed
  moreover have "ibelow m (all_const T $ Abs x T (abstract_over (Free x T) Q))"
  proof -
    have "tvars T \<subseteq> ttvars Q" by (rule pfrees_typ_tvars[OF xT])
    then show ?thesis
      using wt ttvars_abstract_over_aux[of x T 0 Q]
      by (auto simp: wt_thm_def ibelow_def abstract_over_def vars_abstract_over_aux all_const_def all_type_def propT_def)
  qed
  ultimately show ?thesis using wt by (simp add: wt_thm_def)
qed

lemma prf_ok_PAppt_betapply:
  assumes "prf_ok ax H e Hs p (all_const U $ Abs x U B)" "e \<turnstile> t : U"
  shows "prf_ok ax H e Hs (PAppt p (Some t)) (subst_bound t B)"
proof -
  have pr: "prf_ok ax H e Hs (PAppt p (Some t)) (Abs x U B $ t)"
    by (rule prf_ok.PAppt[OF assms]) (simp add: ann_ok_def)
  have ty: "e \<turnstile> Abs x U B $ t : propT" by (rule prf_ok_typing[OF pr])
  then have "wt (Abs x U B $ t)" by (auto simp: wt_def)
  from betapply_conv[OF this] have c: "Abs x U B $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> subst_bound t B" by simp
  have red: "Abs x U B $ t \<rightarrow>\<^sub>\<beta> subst_bound t B" by (simp add: subst_bound_subst)
  from prf_ok.conv[OF pr c subject_reduction_beta[OF ty red]] show ?thesis .
qed

lemma prf_valid_PAppt_Var:
  assumes p: "prf_valid ax H tps q (all_const T $ Abs x T B)" and cT: "cert_typ alg ar T"
  shows "prf_valid ax H tps (q %> Var z T) (subst_bound (Var z T) B)"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  have "prf_ok ax H e [] (prf_ap \<rho> \<sigma> q) (ap \<rho> \<sigma> (all_const T $ Abs x T B))" by (rule prf_validD[OF p \<rho> \<sigma> sol])
  then have p1: "prf_ok ax H e [] (prf_ap \<rho> \<sigma> q) (all_const (tsubst \<rho> T) $ Abs x (tsubst \<rho> T) (ap \<rho> \<sigma> B))"
    by (simp add: ap_def)
  have cT': "cert_typ alg ar (tsubst \<rho> T)" by (rule cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]])
  have cs: "closed_subst \<sigma>" using gsubstD(1)[OF \<sigma>] by (simp add: wt_subst_def)
  obtain e0 where "e0 \<turnstile> \<sigma> z (tsubst \<rho> T) : tsubst \<rho> T"
    using gsubstD(1)[OF \<sigma>] cT' unfolding wt_subst_def by (cases z) blast
  then have "e \<turnstile> \<sigma> z (tsubst \<rho> T) : tsubst \<rho> T" using typing_closed cs by (blast dest: closed_substD)
  from prf_ok_PAppt_betapply[OF p1 this]
  have "prf_ok ax H e [] (PAppt (prf_ap \<rho> \<sigma> q) (Some (\<sigma> z (tsubst \<rho> T)))) (subst_bound (\<sigma> z (tsubst \<rho> T)) (ap \<rho> \<sigma> B))" .
  moreover have "ap \<rho> \<sigma> (subst_bound (Var z T) B) = subst_bound (\<sigma> z (tsubst \<rho> T)) (ap \<rho> \<sigma> B)"
    by (simp add: subst_bound_subst ap_def cs)
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (q %> Var z T)) (ap \<rho> \<sigma> (subst_bound (Var z T) B))"
    by (simp add: prf_ap_def ap_def)
qed

text \<open>
  Generalizing a list of free variables by \<^const>\<open>forall_intr_proof\<close> and instantiating the
  generalized proposition with schematic variables:
\<close>

lemma gen_frees_proof_valid:
  assumes p: "prf_valid ax (set hs) tps q Q" and wt: "wt_thm m hs tps Q" and dist: "distinct (map fst G)"
    and G: "\<And>x T. (x, T) \<in> set G \<Longrightarrow> (x, T) \<in> pfrees Q \<and> \<not> occs_hyps (Free x T) hs tps \<and>
      (\<forall>t\<in>thm_terms hs tps Q \<union> prf_terms q. \<forall>U. (x, U) \<in> pfrees t \<longrightarrow> U = T) \<and>
      (\<forall>A\<in>prf_atoms q. x \<notin> fnames (close A))"
    and V: "\<And>x T. (x, T) \<in> set G \<Longrightarrow> \<exists>z. V x T = Var z T"
  shows "prf_valid ax (set hs) tps (foldr (\<lambda>(x, T) p. p %> V x T) G (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) G q))
    (fsubst (\<lambda>y U. if (y, U) \<in> set G then V y U else Free y U) Q)"
  using p wt dist G V
proof (induction G arbitrary: q Q)
  case Nil
  have "fsubst (\<lambda>y U. Free y U) Q = Q" by (rule fsubst_id) simp
  with Nil show ?case by simp
next
  case (Cons g G)
  obtain x T where g: "g = (x, T)" by force
  note Gx = Cons.prems(4)[of x T, unfolded g, simplified]
  have xQ: "(x, T) \<in> pfrees Q" using Gx by blast
  have wQ: "wtp Q" using Cons.prems(2) by (simp add: wt_thm_def)
  have cT: "cert_typ alg ar T" by (rule typing_pfrees_cert[OF wtpD(2)[OF wQ] xQ])
  have tx: "e \<turnstile> Free x T : T" for e using cT by auto
  let ?q = "forall_intr_proof x (Free x T) q" and ?Q = "all_const T $ Abs x T (abstract_over (Free x T) Q)"
  have v1: "prf_valid ax (set hs) tps ?q ?Q"
  proof (rule forall_intr_proof_valid[OF Cons.prems(1,2) tx])
    show "(Free x T = Free x T \<and> \<not> occs_hyps (Free x T) hs tps) \<or>
        (\<exists>j. Free x T = Var (x, j) T \<and> \<not> occs_hyps (Free x T) [] tps)" using Gx by blast
  qed (use Gx in auto)
  have w1: "wt_thm m hs tps ?Q" by (rule wt_thm_forall_free[OF Cons.prems(2) xQ])
  have xG: "x \<notin> fst ` set G" using Cons.prems(3) by (simp add: g)
  have pfQ: "pfrees ?Q \<subseteq> pfrees Q" by (auto simp: abstract_over_def pfrees_abstract_over_aux all_const_def)
  have ptq: "\<exists>t\<in>prf_terms q. (y, U) \<in> pfrees t" if "t' \<in> prf_terms ?q" "(y, U) \<in> pfrees t'" for t' y U
  proof -
    from prf_terms_prf_abstract_over_aux[of t' "Free x T" 0 q] that(1) obtain t l where
      "t \<in> prf_terms q" "t' = abstract_over_aux (Free x T) l t"
      by (auto simp: forall_intr_proof_def prf_abstract_over_def)
    with that(2) show ?thesis by (auto simp: pfrees_abstract_over_aux)
  qed
  have ih: "prf_valid ax (set hs) tps (foldr (\<lambda>(x, T) p. p %> V x T) G (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) G ?q))
      (fsubst (\<lambda>y U. if (y, U) \<in> set G then V y U else Free y U) ?Q)"
  proof (rule Cons.IH[OF v1 w1])
    show "distinct (map fst G)" using Cons.prems(3) by simp
    show "\<exists>z. V y U = Var z U" if "(y, U) \<in> set G" for y U using Cons.prems(5) that by auto
    fix y U assume yU: "(y, U) \<in> set G"
    note Gy = Cons.prems(4)[of y U]
    have yx: "y \<noteq> x" using xG yU by force
    show "(y, U) \<in> pfrees ?Q \<and> \<not> occs_hyps (Free y U) hs tps \<and>
        (\<forall>t\<in>thm_terms hs tps ?Q \<union> prf_terms ?q. \<forall>U'. (y, U') \<in> pfrees t \<longrightarrow> U' = U) \<and>
        (\<forall>A\<in>prf_atoms ?q. y \<notin> fnames (close A))"
    proof (intro conjI ballI allI impI)
      show "(y, U) \<in> pfrees ?Q"
        using Gy yU yx by (auto simp: abstract_over_def pfrees_abstract_over_aux all_const_def)
      show "\<not> occs_hyps (Free y U) hs tps" using Gy yU by auto
    next
      fix t U' assume t: "t \<in> thm_terms hs tps ?Q \<union> prf_terms ?q" and yU': "(y, U') \<in> pfrees t"
      show "U' = U"
      proof (cases "t \<in> prf_terms ?q")
        case True
        from ptq[OF True yU'] Gy yU show ?thesis by auto
      next
        case False
        with t have "t \<in> thm_terms hs tps ?Q" by simp
        then have "t = ?Q \<or> t \<in> thm_terms hs tps Q" by (auto simp: thm_terms_def)
        then show ?thesis
        proof
          assume "t = ?Q"
          with yU' pfQ have "(y, U') \<in> pfrees Q" by blast
          with Gy yU show ?thesis by (auto simp: thm_terms_def)
        qed (use Gy yU yU' in auto)
      qed
    next
      fix A assume "A \<in> prf_atoms ?q"
      then show "y \<notin> fnames (close A)"
        using Gy yU by (simp add: forall_intr_proof_def prf_abstract_over_def prf_atoms_prf_abstract_over_aux)
    qed
  qed
  \<comment> \<open>the substitution of the other variables commutes with the abstraction over \<open>x\<close>\<close>
  let ?\<tau>' = "\<lambda>y U. if (y, U) \<in> set G then V y U else Free y U"
  have \<tau>'x: "?\<tau>' x T = Free x T" using xG by force
  have \<tau>'c: "closed (?\<tau>' y U) \<and> (x, T) \<notin> pfrees (?\<tau>' y U)" if "(y, U) \<noteq> (x, T)" for y U
    using Cons.prems(5)[of y U] that by (auto simp: closed_def)
  have l\<tau>': "(\<lambda>y U. lift (?\<tau>' y U) 0) = ?\<tau>'"
  proof (intro ext)
    fix y U show "lift (?\<tau>' y U) 0 = ?\<tau>' y U"
      using Cons.prems(5)[of y U] by auto
  qed
  have e1: "fsubst ?\<tau>' ?Q = all_const T $ Abs x T (abstract_over (Free x T) (fsubst ?\<tau>' Q))"
    using fsubst_abstract_over_aux[of ?\<tau>' x T 0 Q, OF \<tau>'x \<tau>'c] by (simp add: abstract_over_def l\<tau>' all_const_def)
  have wQ': "wtp (fsubst ?\<tau>' Q)"
  proof (rule wtpI)
    have nl: "\<not> loose_bvar1 (?\<tau>' y U) k" for y U k
      using Cons.prems(5)[of y U] by (cases "(y, U) \<in> set G") auto
    show "closed (fsubst ?\<tau>' Q)"
      using wtpD(1)[OF wQ] loose_bvar1_fsubst[OF _ nl] by (auto simp: closed_iff_loose_bvar1)
    show "(\<lambda>_. propT) \<turnstile> fsubst ?\<tau>' Q : propT"
    proof (rule typing_fsubst[OF wtpD(2)[OF wQ]])
      fix y U assume cU: "cert_typ alg ar U"
      show "(\<lambda>_. propT) \<turnstile> ?\<tau>' y U : U"
      proof (cases "(y, U) \<in> set G")
        case True
        then obtain z where "V y U = Var z U" using Cons.prems(5)[of y U] by auto
        with True cU show ?thesis by (auto intro: typing.intros)
      qed (use cU in \<open>auto intro: typing.intros\<close>)
    qed
  qed
  from prf_valid_PAppt_Var[OF ih[unfolded e1] cT, of "case V x T of Var z _ \<Rightarrow> z"]
  have "prf_valid ax (set hs) tps (foldr (\<lambda>(x, T) p. p %> V x T) G (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) G ?q)
      %> V x T) (subst_bound (V x T) (abstract_over (Free x T) (fsubst ?\<tau>' Q)))"
    using Cons.prems(5)[of x T] by (auto simp: g)
  moreover have "subst_bound (V x T) (abstract_over (Free x T) (fsubst ?\<tau>' Q)) =
      fsubst (\<lambda>y U. if (y, U) \<in> set (g # G) then V y U else Free y U) Q"
  proof -
    have cV: "closed (V x T)" using Cons.prems(5)[of x T] by (auto simp: g closed_def)
    have nlQ: "\<not> loose_bvar (fsubst ?\<tau>' Q) 0" using wtpD(1)[OF wQ'] by (simp add: closed_def)
    have "subst_bound (V x T) (abstract_over (Free x T) (fsubst ?\<tau>' Q)) =
        fsubst (\<lambda>y U. if y = x \<and> U = T then V x T else Free y U) (fsubst ?\<tau>' Q)"
      unfolding subst_bound_subst abstract_over_def by (rule subst_abstract_over_aux[OF cV nlQ]) simp
    also have "\<dots> = fsubst (\<lambda>y U. fsubst (\<lambda>y U. if y = x \<and> U = T then V x T else Free y U) (?\<tau>' y U)) Q"
      by (rule fsubst_fsubst)
    also have "\<dots> = fsubst (\<lambda>y U. if (y, U) \<in> set (g # G) then V y U else Free y U) Q"
    proof (rule fsubst_cong)
      fix y U assume "(y, U) \<in> pfrees Q"
      show "fsubst (\<lambda>y U. if y = x \<and> U = T then V x T else Free y U) (?\<tau>' y U) =
          (if (y, U) \<in> set (g # G) then V y U else Free y U)"
      proof (cases "(y, U) \<in> set G")
        case True
        then obtain z where "V y U = Var z U" using Cons.prems(5) by force
        with True show ?thesis by simp
      qed (auto simp: g)
    qed
    finally show ?thesis .
  qed
  ultimately show ?case by (simp add: g)
qed

theorem generalize_frees_proof_valid:
  assumes ok: "okT (generalize [] frees gi hs th0) th"
    and p: "prf_valid ax (set hs) (th_tpairs th0) pf (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)"
    and nt: "\<And>t u b. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> b \<in> set frees \<Longrightarrow> b \<notin> fnames t \<and> b \<notin> fnames u"
    and uF: "\<And>t a U V. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms pf \<Longrightarrow> a \<in> set frees \<Longrightarrow>
      (a, U) \<in> pfrees (th_prop th0) \<Longrightarrow> (a, V) \<in> pfrees t \<Longrightarrow> V = U"
    and axF: "\<And>A a. A \<in> prf_atoms pf \<Longrightarrow> a \<in> set frees \<Longrightarrow> a \<notin> fnames (close A)"
  shows "prf_valid ax (set hs) (th_tpairs th) (generalize_proof [] frees gi (th_prop th0) pf) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0" and ?gen = "generalize_term [] frees gi"
  have p1: "map_proof_terms (generalize_term [] [] gi) (generalizeT [] gi) pf = pf"
  proof -
    have "generalize_term [] [] gi = (\<lambda>t. t)" by (intro ext generalize_term_id) simp
    moreover have "generalizeT [] gi = (\<lambda>T. T)" by (intro ext) simp
    ultimately show ?thesis by (simp add: map_proof_terms_ident)
  qed
  have gP: "generalize_term [] [] gi ?P = ?P" by (rule generalize_term_id) simp
  show ?thesis
  proof (cases "frees = []")
    case True
    with ok have "th = th0" by (simp add: generalize_def returnW_def)
    with p p1 True show ?thesis by (simp add: generalize_proof_def)
  next
    case False
    from ok False have nb: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> bad_term [] frees h"
      and th: "th_tpairs th = map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps" "th_prop th = ?gen ?P"
      by (auto simp: generalize_def returnW_def raiseW_def Let_def mk_rep_def split: if_splits)
    have tps: "map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps = ?tps"
      using nt by (auto intro!: map_idI simp: generalize_term_id)
    define G where "G = fold (gen_step frees) (aterms ?P) []"
    have gs: "set G = {(x, T). (x, T) \<in> pfrees ?P \<and> x \<in> set frees}" "distinct G"
      using gen_step_fold[of frees "aterms ?P" "[]"] by (auto simp: G_def Free_aterms)
    have pf: "generalize_proof [] frees gi ?P pf =
        foldr (\<lambda>(x, T) p. p %> Var (clean_index (x, gi)) T) G (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) G pf)"
    proof -
      have "(\<lambda>a acc. case a of Free x T \<Rightarrow> if x \<in> set frees then insert_free (x, T) acc else acc | _ \<Rightarrow> acc) =
          gen_step frees" by (intro ext) (simp add: gen_step_def)
      then show ?thesis using False by (simp add: generalize_proof_def Let_def gP p1 G_def)
    qed
    have dist: "distinct (map fst G)"
    proof -
      have "inj_on fst (set G)"
      proof (rule inj_onI)
        fix a b assume ab: "a \<in> set G" "b \<in> set G" "fst a = fst b"
        obtain x U where a: "a = (x, U)" by force
        obtain y W where b: "b = (y, W)" by force
        from ab gs(1) have "(x, U) \<in> pfrees ?P" "x \<in> set frees" "(y, W) \<in> pfrees ?P" "x = y"
          by (auto simp: a b)
        with uF[of ?P x U W] have "W = U" by (auto simp: thm_terms_def)
        with \<open>x = y\<close> show "a = b" by (simp add: a b)
      qed
      with gs(2) show ?thesis by (simp add: distinct_map)
    qed
    have v: "prf_valid ax (set hs) ?tps
        (foldr (\<lambda>(x, T) p. p %> Var (clean_index (x, gi)) T) G (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) G pf))
        (fsubst (\<lambda>y U. if (y, U) \<in> set G then Var (clean_index (y, gi)) U else Free y U) ?P)"
    proof (rule gen_frees_proof_valid[OF p wt dist])
      fix x T assume xT: "(x, T) \<in> set G"
      then have xP: "(x, T) \<in> pfrees ?P" and xf: "x \<in> set frees" using gs(1) by auto
      have "\<not> occs_hyps (Free x T) hs ?tps"
        using nb bad_term_frees[of frees _ x T] nt[of _ _ x] xf
        by (fastforce simp: occs_hyps_def occs_Free fnames_pfrees)
      then show "(x, T) \<in> pfrees ?P \<and> \<not> occs_hyps (Free x T) hs ?tps \<and>
          (\<forall>t\<in>thm_terms hs ?tps ?P \<union> prf_terms pf. \<forall>U. (x, U) \<in> pfrees t \<longrightarrow> U = T) \<and>
          (\<forall>A\<in>prf_atoms pf. x \<notin> fnames (close A))"
        using xP xf uF axF by blast
    qed auto
    have "fsubst (\<lambda>y U. if (y, U) \<in> set G then Var (clean_index (y, gi)) U else Free y U) ?P = ?gen ?P"
      unfolding generalize_term_fsubst by (rule fsubst_cong) (use gs(1) in auto)
    with v pf th tps show ?thesis by simp
  qed
qed


text \<open>
  The classic proof of \<open>Thm.generalize\<close> with the fix of \<open>patches/20-thm-generalize-tpairs.patch\<close>
  is that of \<^const>\<open>generalize_proof\<close> if the generalized variables do not occur in the flex-flex
  pairs:
\<close>

lemma has_free_fnames: "has_free x t \<longleftrightarrow> x \<in> fnames t"
  by (induction t) (auto simp: has_free_def)

theorem generalize_thm_frees_proof_valid:
  assumes ok: "okT (generalize [] frees gi hs th0) th"
    and p: "prf_valid ax (set hs) (th_tpairs th0) pf (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)"
    and nt: "\<And>t u b. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> b \<in> set frees \<Longrightarrow> b \<notin> fnames t \<and> b \<notin> fnames u"
    and uF: "\<And>t a U V. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms pf \<Longrightarrow> a \<in> set frees \<Longrightarrow>
      (a, U) \<in> pfrees (th_prop th0) \<Longrightarrow> (a, V) \<in> pfrees t \<Longrightarrow> V = U"
    and axF: "\<And>A a. A \<in> prf_atoms pf \<Longrightarrow> a \<in> set frees \<Longrightarrow> a \<notin> fnames (close A)"
  shows "prf_valid ax (set hs) (th_tpairs th) (generalize_thm_proof [] frees gi (th_tpairs th0) (th_prop th0) pf)
    (th_prop th)"
proof -
  have "filter (\<lambda>x. \<exists>(t, u)\<in>set (th_tpairs th0). has_free x t \<or> has_free x u) frees = []"
    using nt by (auto simp: filter_empty_conv has_free_fnames)
  moreover have "filter (\<lambda>x. x \<notin> set []) frees = frees" by simp
  ultimately have "generalize_thm_proof [] frees gi (th_tpairs th0) (th_prop th0) pf =
      generalize_proof [] frees gi (th_prop th0) pf"
    by (simp add: generalize_thm_proof_def Let_def)
  with generalize_frees_proof_valid[OF ok p wt nt uF axF] show ?thesis by simp
qed
end

subsection \<open>Maps on atomic types\<close>

lemma erase_tmap: "erase (tmap \<psi> t) = tmap \<psi> (erase t)"
  by (induction t) (simp_all add: dummyT_def)

lemma beta_eta_equiv_tmap:
  "equivclp (sup beta eta) s t \<Longrightarrow> equivclp (sup beta eta) (tmap \<psi> s) (tmap \<psi> t)"
proof (induction rule: equivclp_induct)
  case (step t u)
  have "(sup beta eta) (tmap \<psi> t) (tmap \<psi> u) \<or> (sup beta eta) (tmap \<psi> u) (tmap \<psi> t)"
    using step(2) by (auto dest: beta_map_types eta_map_types)
  with step(3) show ?case
    by (auto intro: equivclp_trans[OF _ r_into_equivclp] equivclp_trans[OF _ equivclp_sym[OF r_into_equivclp]])
qed simp

lemma ann_ok_tmap: "ann_ok t u \<Longrightarrow> ann_ok (map_option (tmap \<psi>) t) (tmap \<psi> u)"
  by (cases t) (auto simp: erase_tmap intro: beta_eta_equiv_tmap)

lemma tmatch_map_atyps: "tmatch T U \<Longrightarrow> tmatch (map_atyps \<psi> T) (map_atyps \<psi> U)"
proof (induction rule: tmatch.induct)
  case (dummy U)
  have "map_atyps \<psi> dummyT = dummyT" by (simp add: dummyT_def)
  then show ?case by (simp add: tmatch.dummy)
next
  case (Type Ts Us a)
  then have "list_all2 tmatch (map (map_atyps \<psi>) Ts) (map (map_atyps \<psi>) Us)"
    by (simp add: list_all2_map1 list_all2_map2 list_all2_mono)
  then show ?case by (simp add: tmatch.Type)
qed simp_all

lemma tann_ok_tmap: "tann_ok T U \<Longrightarrow> tann_ok (map_option (map_atyps \<psi>) T) (map_atyps \<psi> U)"
  by (cases T) (simp_all add: tmatch_map_atyps)

lemma tmap_all_const [simp]: "tmap \<psi> (all_const U) = all_const (map_atyps \<psi> U)"
  by (simp add: all_const_def all_type_def propT_def)

lemma tmap_implies [simp]: "tmap \<psi> implies = implies"
  by (simp add: implies_def imp_type_def propT_def)

lemma tmap_of_class [simp]: "tmap \<psi> (Proof_Judgment.of_class T c) = Proof_Judgment.of_class (map_atyps \<psi> T) c"
  by (simp add: Proof_Judgment.of_class_def propT_def)

lemma tmap_id_atoms: "(\<And>B. B \<in> tatoms t \<Longrightarrow> \<psi> B = B) \<Longrightarrow> tmap \<psi> t = t"
  by (rule map_types_id, rule map_atyps_id) (auto simp: tatoms_def)

lemma map_of_zip_map_any: "map_of (zip xs (map f ys)) k = map_option f (map_of (zip xs ys) k)"
  by (induction xs ys rule: list_induct2') auto

context prf_sig
begin

lemma tmap_atom_prop:
  assumes tv: "\<And>v S. \<psi> (TVar v S) = TVar v S" and fx: "\<And>B. B \<in> tatoms (close A) \<Longrightarrow> \<psi> B = B"
    and l: "length (tyargs A) = length Us"
  shows "tmap \<psi> (atom_prop A Us) = atom_prop A (map (map_atyps \<psi>) Us)"
proof -
  have "map_atyps \<psi> (tsubst (tyinst (tyargs A) Us) U) = tsubst (tyinst (tyargs A) (map (map_atyps \<psi>) Us)) U"
    if "U \<in> typs (close A)" for U
  proof -
    have "map_atyps \<psi> (tsubst (tyinst (tyargs A) Us) U) =
        map_atyps (\<lambda>B. map_atyps \<psi> (case B of TVar v S \<Rightarrow> tyinst (tyargs A) Us v S | _ \<Rightarrow> B)) U"
      by (simp add: tsubst_as_map_atyps map_atyps_comp)
    also have "\<dots> = map_atyps (\<lambda>B. case B of TVar v S \<Rightarrow> tyinst (tyargs A) (map (map_atyps \<psi>) Us) v S | _ \<Rightarrow> B) U"
    proof (rule map_atyps_cong)
      fix B assume B: "B \<in> set (atyps U)"
      from atyps_atom[OF B] show "map_atyps \<psi> (case B of TVar v S \<Rightarrow> tyinst (tyargs A) Us v S | _ \<Rightarrow> B) =
          (case B of TVar v S \<Rightarrow> tyinst (tyargs A) (map (map_atyps \<psi>) Us) v S | _ \<Rightarrow> B)"
      proof (elim disjE exE)
        fix a S assume "B = TFree a S"
        with fx[of B] B that show ?thesis by (auto simp: tatoms_def)
      next
        fix v S assume "B = TVar v S"
        moreover have "map_of (zip (tyargs A) (map (map_atyps \<psi>) Us)) (v, S) =
            map_option (map_atyps \<psi>) (map_of (zip (tyargs A) Us) (v, S))"
          by (rule map_of_zip_map_any)
        ultimately show ?thesis using tv
          by (cases "map_of (zip (tyargs A) Us) (v, S)") (simp_all add: tyinst_def)
      qed
    qed
    finally show ?thesis by (simp add: tsubst_as_map_atyps)
  qed
  then show ?thesis unfolding atom_prop_def inst_as_map_types map_types_comp
    by (intro map_types_cong) simp
qed

lemma atom_ok_length: "atom_ok A Us' Us \<Longrightarrow> length (tyargs A) = length Us"
  by (auto simp: atom_ok_def dest: list_all2_lengthD)

lemma atom_ok_tmap:
  assumes "atom_ok A Us' Us" and \<psi>: "tmap_ok \<psi>"
    and sorts: "\<And>T S. has_sort alg T S \<Longrightarrow> has_sort alg (map_atyps \<psi> T) S"
  shows "atom_ok A (map_option (map (map_atyps \<psi>)) Us') (map (map_atyps \<psi>) Us)"
  using assms(1) \<psi> sorts unfolding atom_ok_def tmap_ok_def
  by (auto simp: list_all2_map2 elim: list_all2_mono split: option.splits)

text \<open>
  The judgment is closed under maps on the atomic types that keep the certification and the sorts
  of types and fix the schematic type variables, the hypotheses and the closures of the atoms of
  the proof:
\<close>

lemma prf_ok_tmap:
  assumes \<psi>: "tmap_ok \<psi>" and sorts: "\<And>T S. has_sort alg T S \<Longrightarrow> has_sort alg (map_atyps \<psi> T) S"
    and tv: "\<And>v S. \<psi> (TVar v S) = TVar v S"
    and hyp: "\<And>h B. h \<in> H \<Longrightarrow> B \<in> tatoms h \<Longrightarrow> \<psi> B = B"
  shows "prf_ok ax H e Hs p \<phi> \<Longrightarrow> (\<And>A B. A \<in> prf_atoms p \<Longrightarrow> B \<in> tatoms (close A) \<Longrightarrow> \<psi> B = B) \<Longrightarrow>
    prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) p) (tmap \<psi> \<phi>)"
proof (induction rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>')
  have ih: "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) p)
      (tmap \<psi> \<phi>)" using conv.IH conv.prems by simp
  have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> tmap \<psi> \<psi>' : propT"
    using typing_tmap[OF conv.hyps(3) \<psi>] by (simp add: propT_def)
  with prf_ok.conv[OF ih conv_tmap[OF conv.hyps(2) \<psi>]] show ?case .
next
  case (PBound i Hs e)
  have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> map (tmap \<psi>) Hs ! nat_of_integer i : propT"
    using typing_tmap[OF PBound.hyps(3) \<psi>] PBound.hyps(2) by (simp add: propT_def)
  with prf_ok.PBound[of i "map (tmap \<psi>) Hs"] PBound.hyps show ?case by simp
next
  case (AbsP e A t Hs p B a)
  have "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (tmap \<psi> A # map (tmap \<psi>) Hs) (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) p)
      (tmap \<psi> B)"
    using AbsP.IH AbsP.prems by simp
  moreover have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> tmap \<psi> A : propT"
    using typing_tmap[OF AbsP.hyps(1) \<psi>] by (simp add: propT_def)
  ultimately show ?case using ann_ok_tmap[OF AbsP.hyps(2)] by (simp add: prf_ok.AbsP)
next
  case (Abst T U e Hs p B a b)
  have "prf_ok ax H (\<lambda>j. map_atyps \<psi> ((e\<langle>0:U\<rangle>) j)) (map (tmap \<psi>) (map (incr_bv 1 0) Hs))
      (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) p) (tmap \<psi> B)"
    using Abst.IH Abst.prems by simp
  then have "prf_ok ax H ((\<lambda>j. map_atyps \<psi> (e j))\<langle>0:map_atyps \<psi> U\<rangle>) (map (incr_bv 1 0) (map (tmap \<psi>) Hs))
      (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) p) (tmap \<psi> B)"
    by (simp add: map_atyps_shift comp_def)
  moreover have "cert_typ alg ar (map_atyps \<psi> U)" using \<psi> Abst.hyps(2) by (simp add: tmap_ok_def)
  ultimately show ?case using tann_ok_tmap[OF Abst.hyps(1)] by (simp add: prf_ok.Abst)
next
  case (PAppt e Hs p U f t t')
  have "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) p)
      (all_const (map_atyps \<psi> U) $ tmap \<psi> f)"
    using PAppt.IH PAppt.prems by simp
  from prf_ok.PAppt[OF this typing_tmap[OF PAppt.hyps(2) \<psi>] ann_ok_tmap[OF PAppt.hyps(3)]]
  show ?case by simp
next
  case (PAppp e Hs p A B q)
  have "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) p)
      (tmap \<psi> (implies $ A $ B))"
    by (rule PAppp.IH(1), rule PAppp.prems) auto
  moreover have "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (map_proof_terms (tmap \<psi>) (map_atyps \<psi>) q)
      (tmap \<psi> A)"
    by (rule PAppp.IH(2), rule PAppp.prems) auto
  ultimately show ?case by (simp add: prf_ok.PAppp)
next
  case (Hyp t e Hs)
  have t: "tmap \<psi> t = t" by (rule tmap_id_atoms) (use hyp[OF Hyp.hyps(1)] in blast)
  have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> t : propT"
    using typing_tmap[OF Hyp.hyps(2) \<psi>] t by (simp add: propT_def)
  with Hyp.hyps(1) t show ?case by (simp add: prf_ok.Hyp)
next
  case (PAxm A Us' Us e Hs a)
  have fx: "\<psi> B = B" if "B \<in> tatoms (close A)" for B using PAxm.prems that by simp
  note l = atom_ok_length[OF PAxm.hyps(2)]
  have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> atom_prop A (map (map_atyps \<psi>) Us) : propT"
    using typing_tmap[OF PAxm.hyps(3) \<psi>] tmap_atom_prop[OF tv fx l] by (simp add: propT_def)
  moreover have "atom_ok A (map_option (map (map_atyps \<psi>)) Us') (map (map_atyps \<psi>) Us)"
    by (rule atom_ok_tmap[OF PAxm.hyps(2) \<psi>]) (rule sorts)
  ultimately have "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (PAxm a A (map_option (map (map_atyps \<psi>)) Us'))
      (atom_prop A (map (map_atyps \<psi>) Us))"
    using PAxm.hyps(1) by (intro prf_ok.PAxm)
  then
  show ?case using tmap_atom_prop[OF tv fx l] by simp
next
  case (Oracle A Us' Us e Hs a)
  have fx: "\<psi> B = B" if "B \<in> tatoms (close A)" for B using Oracle.prems that by simp
  note l = atom_ok_length[OF Oracle.hyps(2)]
  have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> atom_prop A (map (map_atyps \<psi>) Us) : propT"
    using typing_tmap[OF Oracle.hyps(3) \<psi>] tmap_atom_prop[OF tv fx l] by (simp add: propT_def)
  moreover have "atom_ok A (map_option (map (map_atyps \<psi>)) Us') (map (map_atyps \<psi>) Us)"
    by (rule atom_ok_tmap[OF Oracle.hyps(2) \<psi>]) (rule sorts)
  ultimately have "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (Oracle a A (map_option (map (map_atyps \<psi>)) Us'))
      (atom_prop A (map (map_atyps \<psi>) Us))"
    using Oracle.hyps(1) by (intro prf_ok.Oracle)
  then
  show ?case using tmap_atom_prop[OF tv fx l] by simp
next
  case (PThm h Us e Hs b)
  have fx: "\<psi> B = B" if "B \<in> tatoms (close (hd_prop h))" for B using PThm.prems that by simp
  note l = atom_ok_length[OF PThm.hyps(2)]
  let ?h = "hd_set_types h (map_option (map (map_atyps \<psi>)) (hd_types h))"
  have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> atom_prop (hd_prop ?h) (map (map_atyps \<psi>) Us) : propT"
    using typing_tmap[OF PThm.hyps(3) \<psi>] tmap_atom_prop[OF tv fx l] by (simp add: propT_def)
  moreover have "atom_ok (hd_prop ?h) (hd_types ?h) (map (map_atyps \<psi>) Us)"
    using atom_ok_tmap[OF PThm.hyps(2) \<psi>] sorts by simp
  ultimately have "prf_ok ax H (\<lambda>j. map_atyps \<psi> (e j)) (map (tmap \<psi>) Hs) (PThm (?h, b))
      (atom_prop (hd_prop ?h) (map (map_atyps \<psi>) Us))"
    using PThm.hyps(1) by (intro prf_ok.PThm) simp_all
  then show ?case using tmap_atom_prop[OF tv fx l] by simp
next
  case (PClass T c e Hs)
  have "(\<lambda>j. map_atyps \<psi> (e j)) \<turnstile> Proof_Judgment.of_class (map_atyps \<psi> T) c : propT"
    using typing_tmap[OF PClass.hyps(2) \<psi>] by (simp add: propT_def)
  from prf_ok.PClass[OF sorts[OF PClass.hyps(1)] this] show ?case by simp
qed

end

subsection \<open>Independence of the environment of the loose bound variables\<close>

text \<open>
  Simultaneous substitution of closed terms for the loose bound variables from index \<open>k\<close> on:
\<close>

fun substb :: "(integer \<Rightarrow> pterm) \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "substb \<theta> k (Bound i) = (if k \<le> i then \<theta> (i - k) else Bound i)"
| "substb \<theta> k (Abs a T t) = Abs a T (substb \<theta> (k + 1) t)"
| "substb \<theta> k (s $ t) = substb \<theta> k s $ substb \<theta> k t"
| "substb \<theta> k t = t"

lemma substb_id: "\<not> loose_bvar t k \<Longrightarrow> substb \<theta> k t = t"
  by (induction t arbitrary: k) auto

lemma closed_no_loose: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar t k"
  using loose_bvar_mono by (auto simp: closed_def)

lemma closed_incr_bv: "closed t \<Longrightarrow> 0 \<le> j \<Longrightarrow> incr_bv n j t = t"
  by (rule incr_bv_no_loose) (rule closed_no_loose)

lemma closed_subst: "closed t \<Longrightarrow> 0 \<le> i \<Longrightarrow> t[s/i] = t"
  by (rule subst_no_loose) (rule closed_no_loose)

lemma substb_incr_bv:
  assumes \<theta>: "\<And>j. closed (\<theta> j)"
  shows "0 \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> substb \<theta> (k + 1) (incr_bv 1 j t) = incr_bv 1 j (substb \<theta> k t)"
proof (induction t arbitrary: j k)
  case (Bound i)
  then show ?case using closed_incr_bv[OF \<theta>] by auto
next
  case (Abs a T t)
  have "substb \<theta> (k + 1 + 1) (incr_bv 1 (j + 1) t) = incr_bv 1 (j + 1) (substb \<theta> (k + 1) t)"
    by (rule Abs.IH) (use Abs.prems in simp_all)
  then show ?case by (simp add: algebra_simps)
qed auto

lemma loose_bvar1_loose_bvar: "loose_bvar1 t j \<Longrightarrow> loose_bvar t j"
  by (induction t arbitrary: j) auto

lemma substb_implies [simp]: "substb \<theta> k implies = implies"
  by (simp add: implies_def)

lemma substb_all_const [simp]: "substb \<theta> k (all_const U) = all_const U"
  by (simp add: all_const_def)

lemma substb_subst:
  assumes \<theta>: "\<And>j. closed (\<theta> j)"
  shows "0 \<le> i \<Longrightarrow> i \<le> k \<Longrightarrow> substb \<theta> k (t[s/i]) = (substb \<theta> (k + 1) t)[substb \<theta> k s/i]"
proof (induction t arbitrary: i k s)
  case (Bound j)
  then show ?case using closed_subst[OF \<theta>] by (auto simp: subst_Bound algebra_simps)
next
  case (Abs a T t)
  have "substb \<theta> (k + 1) (incr_bv 1 0 s) = incr_bv 1 0 (substb \<theta> k s)"
    by (rule substb_incr_bv[OF \<theta>]) (use Abs.prems in simp_all)
  with Abs.IH[of "i + 1" "k + 1" "incr_bv 1 0 s"] Abs.prems show ?case by simp
qed simp_all

lemma loose_bvar1_substb:
  assumes \<theta>: "\<And>j. closed (\<theta> j)"
  shows "\<not> loose_bvar1 t j \<Longrightarrow> 0 \<le> j \<Longrightarrow> j < k \<Longrightarrow> \<not> loose_bvar1 (substb \<theta> k t) j"
proof (induction t arbitrary: j k)
  case (Bound i)
  show ?case
  proof (cases "k \<le> i")
    case True
    have "\<not> loose_bvar (\<theta> (i - k)) j" by (rule closed_no_loose[OF \<theta>]) (use Bound.prems in simp)
    with True show ?thesis using loose_bvar1_loose_bvar by auto
  qed (use Bound.prems in simp)
qed auto

lemma beta_substb:
  assumes \<theta>: "\<And>j. closed (\<theta> j)"
  shows "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> substb \<theta> k s \<rightarrow>\<^sub>\<beta> substb \<theta> k t"
proof (induction arbitrary: k set: beta)
  case (beta a T s t)
  show ?case using substb_subst[OF \<theta>, where i = 0 and k = k and t = s and s = t] beta by simp
qed auto

lemma eta_substb:
  assumes \<theta>: "\<And>j. closed (\<theta> j)"
  shows "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> substb \<theta> k s \<rightarrow>\<^sub>\<eta> substb \<theta> k t"
proof (induction arbitrary: k set: eta)
  case (eta s a T d)
  have "\<not> loose_bvar1 (substb \<theta> (k + 1) s) 0"
    by (rule loose_bvar1_substb[OF \<theta>]) (use eta in simp_all)
  moreover have "\<not> k + 1 \<le> 0" using eta by simp
  ultimately show ?case
    using eta.eta[of "substb \<theta> (k + 1) s" a T "substb \<theta> k d"] substb_subst[OF \<theta>, where i = 0 and k = k and t = s and s = d] eta
    by simp
qed auto

lemma beta_eta_substb:
  assumes \<theta>: "\<And>j. closed (\<theta> j)" and k: "0 \<le> k"
  shows "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (substb \<theta> k s) (substb \<theta> k t)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl beta_substb[OF \<theta> _ k] eta_substb[OF \<theta> _ k])

lemma beta_eta_equiv_substb:
  assumes \<theta>: "\<And>j. closed (\<theta> j)" and k: "0 \<le> k"
  shows "equivclp (sup beta eta) s t \<Longrightarrow> equivclp (sup beta eta) (substb \<theta> k s) (substb \<theta> k t)"
proof (induction rule: equivclp_induct)
  case (step t u)
  have "(sup beta eta) (substb \<theta> k t) (substb \<theta> k u) \<or> (sup beta eta) (substb \<theta> k u) (substb \<theta> k t)"
    using step(2) by (auto dest: beta_substb[OF \<theta> _ k] eta_substb[OF \<theta> _ k])
  with step(3) show ?case
    by (auto intro: equivclp_trans[OF _ r_into_equivclp] equivclp_trans[OF _ equivclp_sym[OF r_into_equivclp]])
qed simp

lemma unname_substb: "unname (substb \<theta> k t) = substb (\<lambda>j. unname (\<theta> j)) k (unname t)"
  by (induction t arbitrary: k) simp_all

lemma erase_substb: "erase (substb \<theta> k t) = substb (\<lambda>j. erase (\<theta> j)) k (erase t)"
  by (induction t arbitrary: k) simp_all

lemma loose_bvar_erase [simp]: "loose_bvar (erase t) k \<longleftrightarrow> loose_bvar t k"
  by (induction t arbitrary: k) simp_all

lemma closed_erase: "closed t \<Longrightarrow> closed (erase t)"
  by (simp add: closed_def)

lemma ann_ok_substb:
  assumes \<theta>: "\<And>j. closed (\<theta> j)" and k: "0 \<le> k"
    and t': "\<forall>u\<in>set_option t'. \<not> loose_bvar u k" and a: "ann_ok t' t"
  shows "ann_ok t' (substb \<theta> k t)"
proof (cases t')
  case (Some u)
  have "equivclp (sup beta eta) (erase u) (erase t)" using a Some by simp
  from beta_eta_equiv_substb[OF closed_erase[OF \<theta>] k this]
  have "equivclp (sup beta eta) (substb (\<lambda>j. erase (\<theta> j)) k (erase u)) (erase (substb \<theta> k t))"
    by (simp add: erase_substb)
  moreover have "substb (\<lambda>j. erase (\<theta> j)) k (erase u) = erase u" using t' Some by (simp add: substb_id)
  ultimately show ?thesis using Some by simp
qed simp

text \<open>The proof terms whose terms have no loose bound variables from index \<open>k\<close> on:\<close>

fun prf_nolb :: "integer \<Rightarrow> prf \<Rightarrow> bool" where
  "prf_nolb k (Abst a T p) = prf_nolb (k + 1) p"
| "prf_nolb k (AbsP a t p) = ((\<forall>u\<in>set_option t. \<not> loose_bvar u k) \<and> prf_nolb k p)"
| "prf_nolb k (PAppt p t) = (prf_nolb k p \<and> (\<forall>u\<in>set_option t. \<not> loose_bvar u k))"
| "prf_nolb k (PAppp p q) = (prf_nolb k p \<and> prf_nolb k q)"
| "prf_nolb k p = True"

context prf_sig
begin

lemma typing_substb:
  "e \<turnstile> t : T \<Longrightarrow> 0 \<le> k \<Longrightarrow> (\<And>j e''. 0 \<le> j \<Longrightarrow> e'' \<turnstile> \<theta> j : e (k + j)) \<Longrightarrow>
    (\<And>i. 0 \<le> i \<Longrightarrow> i < k \<Longrightarrow> e' i = e i) \<Longrightarrow> e' \<turnstile> substb \<theta> k t : T"
proof (induction arbitrary: k e' rule: typing.induct)
  case (Bound i e T)
  show ?case
  proof (cases "k \<le> i")
    case True
    with Bound.prems(2)[of "i - k" e'] Bound.hyps show ?thesis by simp
  next
    case False
    with Bound.prems(3)[of i] Bound.hyps show ?thesis by auto
  qed
next
  case (Abs T e t U a)
  have "e'\<langle>0:T\<rangle> \<turnstile> substb \<theta> (k + 1) t : U"
  proof (rule Abs.IH)
    show "e'' \<turnstile> \<theta> j : (e\<langle>0:T\<rangle>) (k + 1 + j)" if "0 \<le> j" for j e''
      using Abs.prems(2)[OF that] Abs.prems(1) that by (simp add: shift_def algebra_simps)
    show "(e'\<langle>0:T\<rangle>) i = (e\<langle>0:T\<rangle>) i" if "0 \<le> i" "i < k + 1" for i
    proof (cases "i = 0")
      case False
      with that have "0 \<le> i - 1" "i - 1 < k" by (simp_all add: integer_arith)
      with Abs.prems(3)[of "i - 1"] False show ?thesis by (simp add: shift_def)
    qed (simp add: shift_def)
  qed (use Abs.prems in simp)
  with Abs.hyps show ?case by auto
qed auto

lemma conv_substb:
  assumes ty: "e \<turnstile> s : T" "e \<turnstile> t : T" and k: "0 \<le> k" and \<theta>c: "\<And>j. closed (\<theta> j)"
    and \<theta>t: "\<And>j e''. 0 \<le> j \<Longrightarrow> e'' \<turnstile> \<theta> j : e (k + j)" and ag: "\<And>i. 0 \<le> i \<Longrightarrow> i < k \<Longrightarrow> e' i = e i"
    and c: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "substb \<theta> k s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substb \<theta> k t"
proof -
  have ws: "wt s" using ty(1) by (auto simp: wt_def)
  have ws': "wt (substb \<theta> k s)" "wt (substb \<theta> k t)"
    using typing_substb[OF ty(1) k \<theta>t ag] typing_substb[OF ty(2) k \<theta>t ag] by (auto simp: wt_def)
  from c have "wt t \<and> (\<exists>u v. (sup beta eta)\<^sup>*\<^sup>* s u \<and> (sup beta eta)\<^sup>*\<^sup>* t v \<and> aconv_term u v)"
    by (simp only: conv_iff[OF ws])
  then obtain u v where uv: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* t v" "aconv_term u v"
    by blast
  have "aconv_term (substb \<theta> k u) (substb \<theta> k v)"
    using uv(3) by (simp add: aconv_term_unname unname_substb)
  with ws'(2) beta_eta_substb[of \<theta> k s u, OF \<theta>c k uv(1)] beta_eta_substb[of \<theta> k t v, OF \<theta>c k uv(2)]
  have "wt (substb \<theta> k t) \<and> (\<exists>u v. (sup beta eta)\<^sup>*\<^sup>* (substb \<theta> k s) u \<and> (sup beta eta)\<^sup>*\<^sup>* (substb \<theta> k t) v \<and>
      aconv_term u v)" by blast
  then show ?thesis by (simp only: conv_iff[OF ws'(1)])
qed

lemma closed_atom_prop: "closed (atom_prop A Us)"
  using closed_close[of A] by (simp add: atom_prop_def closed_def)

lemma closed_of_class: "closed (Proof_Judgment.of_class T c)"
  by (simp add: Proof_Judgment.of_class_def closed_def)

text \<open>
  Substituting closed terms for the loose bound variables from index \<open>k\<close> on (at the types of an
  environment) preserves the judgment of a proof whose terms have no such variables:
\<close>

lemma prf_ok_substb:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> closed h"
  shows "prf_ok ax H e Hs p \<phi> \<Longrightarrow> 0 \<le> k \<Longrightarrow> prf_nolb k p \<Longrightarrow> (\<And>j. closed (\<theta> j)) \<Longrightarrow>
    (\<And>j e''. 0 \<le> j \<Longrightarrow> e'' \<turnstile> \<theta> j : e (k + j)) \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> i < k \<Longrightarrow> e' i = e i) \<Longrightarrow>
    prf_ok ax H e' (map (substb \<theta> k) Hs) p (substb \<theta> k \<phi>)"
proof (induction arbitrary: k e' rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  have ih: "prf_ok ax H e' (map (substb \<theta> k) Hs) p (substb \<theta> k \<phi>)" by (rule conv.IH) (use conv.prems in auto)
  have t\<phi>: "e \<turnstile> \<phi> : propT" by (rule prf_ok_typing[OF conv.hyps(1)])
  have "substb \<theta> k \<phi> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substb \<theta> k \<psi>"
    by (rule conv_substb[OF t\<phi> conv.hyps(3)]) (use conv.prems conv.hyps(2) in auto)
  moreover have "e' \<turnstile> substb \<theta> k \<psi> : propT"
    by (rule typing_substb[OF conv.hyps(3)]) (use conv.prems in auto)
  ultimately show ?case by (rule prf_ok.conv[OF ih])
next
  case (PBound i Hs e)
  have "e' \<turnstile> substb \<theta> k (Hs ! nat_of_integer i) : propT"
    by (rule typing_substb[OF PBound.hyps(3)]) (use PBound.prems in auto)
  with prf_ok.PBound[of i "map (substb \<theta> k) Hs" e'] PBound.hyps show ?case by simp
next
  case (AbsP e A t Hs p B a)
  have "prf_ok ax H e' (map (substb \<theta> k) (A # Hs)) p (substb \<theta> k B)"
    by (rule AbsP.IH) (use AbsP.prems in auto)
  moreover have "e' \<turnstile> substb \<theta> k A : propT"
    by (rule typing_substb[OF AbsP.hyps(1)]) (use AbsP.prems in auto)
  moreover have "ann_ok t (substb \<theta> k A)"
    by (rule ann_ok_substb[OF _ AbsP.prems(1) _ AbsP.hyps(2)]) (use AbsP.prems in auto)
  ultimately show ?case by (simp add: prf_ok.AbsP)
next
  case (Abst T U e Hs p B a b)
  have "prf_ok ax H (e'\<langle>0:U\<rangle>) (map (substb \<theta> (k + 1)) (map (incr_bv 1 0) Hs)) p (substb \<theta> (k + 1) B)"
  proof (rule Abst.IH)
    show "e'' \<turnstile> \<theta> j : (e\<langle>0:U\<rangle>) (k + 1 + j)" if "0 \<le> j" for j e''
      using Abst.prems(4)[OF that] Abst.prems(1) that by (simp add: shift_def algebra_simps)
    show "(e'\<langle>0:U\<rangle>) i = (e\<langle>0:U\<rangle>) i" if "0 \<le> i" "i < k + 1" for i
    proof (cases "i = 0")
      case False
      with that have "0 \<le> i - 1" "i - 1 < k" by (simp_all add: integer_arith)
      with Abst.prems(5)[of "i - 1"] False show ?thesis by (simp add: shift_def)
    qed (simp add: shift_def)
  qed (use Abst.prems in auto)
  moreover have "map (substb \<theta> (k + 1)) (map (incr_bv 1 0) Hs) = map (incr_bv 1 0) (map (substb \<theta> k) Hs)"
    using substb_incr_bv[of \<theta> 0 k, OF Abst.prems(3)] Abst.prems(1) by simp
  ultimately have "prf_ok ax H (e'\<langle>0:U\<rangle>) (map (incr_bv 1 0) (map (substb \<theta> k) Hs)) p (substb \<theta> (k + 1) B)"
    by (simp only:)
  from prf_ok.Abst[OF Abst.hyps(1,2) this] show ?case by simp
next
  case (PAppt e Hs p U f t t')
  have "prf_ok ax H e' (map (substb \<theta> k) Hs) p (substb \<theta> k (all_const U $ f))"
    by (rule PAppt.IH) (use PAppt.prems in auto)
  then have p1: "prf_ok ax H e' (map (substb \<theta> k) Hs) p (all_const U $ substb \<theta> k f)"
    by simp
  have t1: "e' \<turnstile> substb \<theta> k t : U" by (rule typing_substb[OF PAppt.hyps(2)]) (use PAppt.prems in auto)
  have a1: "ann_ok t' (substb \<theta> k t)"
    by (rule ann_ok_substb[OF _ PAppt.prems(1) _ PAppt.hyps(3)]) (use PAppt.prems in auto)
  from prf_ok.PAppt[OF p1 t1 a1] show ?case by simp
next
  case (PAppp e Hs p A B q)
  have "prf_ok ax H e' (map (substb \<theta> k) Hs) p (substb \<theta> k (implies $ A $ B))"
    by (rule PAppp.IH(1)) (use PAppp.prems in auto)
  moreover have "prf_ok ax H e' (map (substb \<theta> k) Hs) q (substb \<theta> k A)"
    by (rule PAppp.IH(2)) (use PAppp.prems in auto)
  ultimately show ?case by (simp add: prf_ok.PAppp)
next
  case (Hyp t e Hs)
  have c: "closed t" by (rule H[OF Hyp.hyps(1)])
  then have "substb \<theta> k t = t" using Hyp.prems(1) by (simp add: substb_id closed_no_loose)
  with Hyp c show ?case by (auto intro: prf_ok.Hyp typing_closed)
next
  case (PAxm A Us' Us e Hs a)
  have "substb \<theta> k (atom_prop A Us) = atom_prop A Us"
    using PAxm.prems(1) by (simp add: substb_id closed_no_loose closed_atom_prop)
  moreover have "e' \<turnstile> atom_prop A Us : propT" by (rule typing_closed[OF PAxm.hyps(3) closed_atom_prop])
  then have "prf_ok ax H e' (map (substb \<theta> k) Hs) (PAxm a A Us') (atom_prop A Us)"
    by (intro prf_ok.PAxm) (use PAxm.hyps in simp_all)
  ultimately show ?case by simp
next
  case (Oracle A Us' Us e Hs a)
  have "substb \<theta> k (atom_prop A Us) = atom_prop A Us"
    using Oracle.prems(1) by (simp add: substb_id closed_no_loose closed_atom_prop)
  moreover have "e' \<turnstile> atom_prop A Us : propT" by (rule typing_closed[OF Oracle.hyps(3) closed_atom_prop])
  then have "prf_ok ax H e' (map (substb \<theta> k) Hs) (Oracle a A Us') (atom_prop A Us)"
    by (intro prf_ok.Oracle) (use Oracle.hyps in simp_all)
  ultimately show ?case by simp
next
  case (PThm h Us e Hs b)
  have "substb \<theta> k (atom_prop (hd_prop h) Us) = atom_prop (hd_prop h) Us"
    using PThm.prems(1) by (simp add: substb_id closed_no_loose closed_atom_prop)
  moreover have "e' \<turnstile> atom_prop (hd_prop h) Us : propT" by (rule typing_closed[OF PThm.hyps(3) closed_atom_prop])
  then have "prf_ok ax H e' (map (substb \<theta> k) Hs) (PThm (h, b)) (atom_prop (hd_prop h) Us)"
    by (intro prf_ok.PThm) (use PThm.hyps in simp_all)
  ultimately show ?case by simp
next
  case (PClass T c e Hs)
  have "substb \<theta> k (Proof_Judgment.of_class T c) = Proof_Judgment.of_class T c"
    using PClass.prems(1) by (simp add: substb_id closed_no_loose closed_of_class)
  moreover have "prf_ok ax H e' (map (substb \<theta> k) Hs) (PClass T c) (Proof_Judgment.of_class T c)"
    by (rule prf_ok.PClass[OF PClass.hyps(1) typing_closed[OF PClass.hyps(2) closed_of_class]])
  ultimately show ?case by simp
qed

text \<open>
  A closed proposition that a proof without loose bound variables proves in an environment of
  certified types it proves in every environment:
\<close>

corollary prf_ok_env:
  assumes p: "prf_ok ax H e [] p \<phi>" and H: "\<And>h. h \<in> H \<Longrightarrow> closed h"
    and ce: "\<And>i. 0 \<le> i \<Longrightarrow> cert_typ alg ar (e i)" and np: "prf_nolb 0 p" and c: "closed \<phi>"
  shows "prf_ok ax H e' [] p \<phi>"
proof -
  have "prf_ok ax H e' (map (substb (\<lambda>j. Var (STR ''x'', j) (e j)) 0) []) p (substb (\<lambda>j. Var (STR ''x'', j) (e j)) 0 \<phi>)"
    by (rule prf_ok_substb[OF H p _ np]) (use ce in \<open>auto simp: closed_def\<close>)
  moreover have "substb (\<lambda>j. Var (STR ''x'', j) (e j)) 0 \<phi> = \<phi>" using c by (simp add: substb_id closed_def)
  ultimately show ?thesis by simp
qed

end

subsection \<open>Generalization of free type variables\<close>

lemma map_proof_terms_cong2:
  "(\<And>t. t \<in> prf_terms p \<Longrightarrow> f t = f' t) \<Longrightarrow> (\<And>T. T \<in> prf_typs p \<Longrightarrow> g T = g' T) \<Longrightarrow>
    map_proof_terms f g p = map_proof_terms f' g' p"
proof (induction p)
  case (Abst a T q)
  then show ?case by (cases T) simp_all
next
  case (AbsP a t q)
  then show ?case by (cases t) simp_all
next
  case (PAppt q t)
  then show ?case by (cases t) simp_all
next
  case (PAxm a A Us)
  then show ?case by (cases Us) simp_all
next
  case (Oracle a A Us)
  then show ?case by (cases Us) simp_all
next
  case (PThm x)
  obtain h b where x: "x = (h, b)" by force
  show ?case using PThm by (cases "hd_types h") (auto simp: x hd_set_types_def)
qed simp_all

lemma prf_nolb_map:
  "(\<And>t k. 0 \<le> k \<Longrightarrow> \<not> loose_bvar t k \<Longrightarrow> \<not> loose_bvar (f t) k) \<Longrightarrow> 0 \<le> k \<Longrightarrow> prf_nolb k p \<Longrightarrow>
    prf_nolb k (map_proof_terms f g p)"
  by (induction k p rule: prf_nolb.induct) auto

context wf_algebra
begin

lemma has_sort_map_atyps:
  assumes "\<And>a S0. TFree a S0 \<in> set (atyps T) \<Longrightarrow> has_sort alg (\<psi> (TFree a S0)) S0"
    and "\<And>v S0. TVar v S0 \<in> set (atyps T) \<Longrightarrow> has_sort alg (\<psi> (TVar v S0)) S0"
  shows "has_sort alg T S \<Longrightarrow> has_sort alg (map_atyps \<psi> T) S"
  using assms
proof (induction T arbitrary: S)
  case (Type a Ts)
  have ih: "has_sort alg (map_atyps \<psi> (Ts ! i)) S'" if "i < length Ts" "has_sort alg (Ts ! i) S'" for i S'
    by (rule Type.IH[OF nth_mem[OF that(1)] that(2)]) (use Type.prems(2,3) that(1) in \<open>force dest: nth_mem\<close>)+
  from Type.prems(1) show ?case by (auto simp: ih)
next
  case (TFree b S0)
  then show ?case by (auto intro: has_sort_mono simp: sort_le_iff)
next
  case (TVar v S0)
  then show ?case by (auto intro: has_sort_mono simp: sort_le_iff)
qed

end

text \<open>
  The instantiation \<open>\<psi>\<close> of the generalized free type variables \<open>A\<close> by the instance \<open>\<rho>\<close> of the new
  schematic type variables commutes with the generalization:
\<close>

definition inst_tf :: "(name \<times> psort) set \<Rightarrow> (name \<Rightarrow> psort \<Rightarrow> indexname) \<Rightarrow> tinst \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "inst_tf A g \<rho> B = (case B of TFree a S \<Rightarrow> if (a, S) \<in> A then \<rho> (g a S) S else B | _ \<Rightarrow> B)"

lemma inst_tf_simps [simp]:
  "inst_tf A g \<rho> (TVar v S) = TVar v S"
  "inst_tf A g \<rho> (TFree a S) = (if (a, S) \<in> A then \<rho> (g a S) S else TFree a S)"
  by (simp_all add: inst_tf_def)

lemma inst_tf_id: "\<not> has_tf A U \<Longrightarrow> map_atyps (inst_tf A g \<rho>) U = U"
  by (rule map_atyps_has_tf_id) (auto simp: inst_tf_def)

lemma map_atyps_inst_tf_tsubst:
  assumes "\<And>v S. (v, S) \<in> tvars T \<Longrightarrow> \<not> has_tf A (\<rho> v S)"
  shows "map_atyps (inst_tf A g \<rho>) (tsubst \<rho> T) = tsubst \<rho> (map_atyps (gen_atom A g) T)"
proof -
  have "map_atyps (inst_tf A g \<rho>) (tsubst \<rho> T) =
      map_atyps (\<lambda>B. map_atyps (inst_tf A g \<rho>) (case B of TVar v S \<Rightarrow> \<rho> v S | _ \<Rightarrow> B)) T"
    by (simp add: tsubst_as_map_atyps map_atyps_comp)
  also have "\<dots> = map_atyps (\<lambda>B. tsubst \<rho> (gen_atom A g B)) T"
  proof (rule map_atyps_cong)
    fix B assume B: "B \<in> set (atyps T)"
    from atyps_atom[OF B] show "map_atyps (inst_tf A g \<rho>) (case B of TVar v S \<Rightarrow> \<rho> v S | _ \<Rightarrow> B) =
        tsubst \<rho> (gen_atom A g B)"
    proof (elim disjE exE)
      fix v S assume "B = TVar v S"
      with B assms[of v S] show ?thesis by (simp add: inst_tf_id gen_atom_def tvars_atyps)
    qed (auto simp: inst_tf_def gen_atom_def)
  qed
  also have "\<dots> = tsubst \<rho> (map_atyps (gen_atom A g) T)"
    by (simp add: tsubst_as_map_atyps map_atyps_comp)
  finally show ?thesis .
qed

text \<open>Injections of a finite set that avoid a finite set:\<close>

lemma fresh_inj:
  fixes V :: "'a set" and N :: "'b set"
  assumes "finite V" "finite N" "infinite (UNIV :: 'b set)"
  obtains c :: "'a \<Rightarrow> 'b" where "inj_on c V" "c ` V \<inter> N = {}"
proof -
  have "infinite (UNIV - N)" using assms(2,3) by (simp add: Diff_infinite_finite)
  then obtain f :: "nat \<Rightarrow> 'b" where f: "inj f" "range f \<subseteq> UNIV - N"
    using infinite_countable_subset by blast
  obtain h :: "'a \<Rightarrow> nat" and n where h: "inj_on h V"
    using finite_imp_inj_to_nat_seg[OF assms(1)] by blast
  have "inj_on (f \<circ> h) V" using f(1) h by (simp add: comp_inj_on inj_on_subset)
  moreover have "(f \<circ> h) ` V \<inter> N = {}" using f(2) by auto
  ultimately show ?thesis by (rule that)
qed

lemma infinite_indexname: "infinite (UNIV :: indexname set)"
  using infinite_literal by (simp add: finite_prod)

lemma vsubst_Var_id: "(\<And>x U. (x, U) \<in> vars t \<Longrightarrow> \<sigma> x U = Var x U) \<Longrightarrow> vsubst \<sigma> t = t"
  by (induction t) auto

context pure_sig
begin

lemma gen_inst_term:
  assumes "\<And>v S. (v, S) \<in> ttvars t \<Longrightarrow> \<not> has_tf A (\<rho> v S)"
    and "\<And>x U. (x, U) \<in> vars t \<Longrightarrow>
      vsubst \<sigma>2 (tmap (inst_tf A g \<rho>) (\<sigma>P x (tsubst \<rho> U))) = \<sigma> x (tsubst \<rho> (map_atyps (gen_atom A g) U))"
  shows "ap TVar \<sigma>2 (tmap (inst_tf A g \<rho>) (ap \<rho> \<sigma>P t)) = ap \<rho> \<sigma> (tmap (gen_atom A g) t)"
  using assms
proof (induction t)
  case (Abs a T t)
  have "map_atyps (inst_tf A g \<rho>) (tsubst \<rho> T) = tsubst \<rho> (map_atyps (gen_atom A g) T)"
    by (rule map_atyps_inst_tf_tsubst) (use Abs.prems(1) in \<open>auto simp: ttvars_def\<close>)
  moreover have "ap TVar \<sigma>2 (tmap (inst_tf A g \<rho>) (ap \<rho> \<sigma>P t)) = ap \<rho> \<sigma> (tmap (gen_atom A g) t)"
    by (rule Abs.IH) (use Abs.prems in \<open>auto simp: ttvars_def\<close>)
  ultimately show ?case by (simp add: ap_def)
next
  case (App s t)
  have "ap TVar \<sigma>2 (tmap (inst_tf A g \<rho>) (ap \<rho> \<sigma>P s)) = ap \<rho> \<sigma> (tmap (gen_atom A g) s)"
    by (rule App.IH(1)) (use App.prems in \<open>auto simp: ttvars_def\<close>)
  moreover have "ap TVar \<sigma>2 (tmap (inst_tf A g \<rho>) (ap \<rho> \<sigma>P t)) = ap \<rho> \<sigma> (tmap (gen_atom A g) t)"
    by (rule App.IH(2)) (use App.prems in \<open>auto simp: ttvars_def\<close>)
  ultimately show ?case by (simp add: ap_def)
next
  case (Var x T)
  then show ?case by (simp add: ap_def)
next
  case (Const a T)
  have "map_atyps (inst_tf A g \<rho>) (tsubst \<rho> T) = tsubst \<rho> (map_atyps (gen_atom A g) T)"
    by (rule map_atyps_inst_tf_tsubst) (use Const.prems(1) in \<open>auto simp: ttvars_def\<close>)
  then show ?case by (simp add: ap_def)
next
  case (Free a T)
  have "map_atyps (inst_tf A g \<rho>) (tsubst \<rho> T) = tsubst \<rho> (map_atyps (gen_atom A g) T)"
    by (rule map_atyps_inst_tf_tsubst) (use Free.prems(1) in \<open>auto simp: ttvars_def\<close>)
  then show ?case by (simp add: ap_def)
qed (simp add: ap_def)

end

context prf_model
begin

text \<open>
  The core of the generalization of free type variables \<open>A\<close> for an instance that does not
  introduce them (conditions \<open>R1\<close> and \<open>R2\<close> as in @{thm [source] holds_gen_inst}):
\<close>

lemma prf_gen_inst:
  assumes p: "prf_valid ax H tps q P" and wP: "wtp P"
    and H: "\<And>h. h \<in> H \<Longrightarrow> closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in A h"
    and nt: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> \<not> tf_in A t \<and> \<not> tf_in A u"
    and na: "\<And>X. X \<in> prf_atoms q \<Longrightarrow> \<not> tf_in A (close X)"
    and np: "prf_nolb 0 q"
    and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and TS: "P \<in> TS" "prf_terms q \<subseteq> TS" "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> t \<in> TS \<and> u \<in> TS" "finite TS"
    and R1: "\<And>X v S. X \<in> TS \<Longrightarrow> (v, S) \<in> ttvars X \<Longrightarrow> \<not> has_tf A (\<rho> v S)"
    and R1T: "\<And>T v S. T \<in> prf_typs q \<Longrightarrow> (v, S) \<in> tvars T \<Longrightarrow> \<not> has_tf A (\<rho> v S)"
    and R2: "\<And>X x U. X \<in> TS \<Longrightarrow> (x, U) \<in> vars (inst \<rho> X) \<Longrightarrow> \<not> has_tf A U \<Longrightarrow> \<not> tf_in A (\<sigma> x U)"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  shows "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (map_proof_terms (tmap (gen_atom A g)) (map_atyps (gen_atom A g)) q))
    (ap \<rho> \<sigma> (tmap (gen_atom A g) P))"
proof -
  let ?gA = "gen_atom A g" and ?\<psi> = "inst_tf A g \<rho>"
  define V0 where "V0 = fst ` (\<Union>X\<in>TS. vars X)"
  define N where "N = fst ` (\<Union>X\<in>TS. \<Union>(x, U)\<in>vars (inst \<rho> X). vars (\<sigma> x U))"
  have fV0: "finite V0" using TS(4) by (simp add: V0_def)
  have fN: "finite N" using TS(4) by (simp add: N_def split_def)
  obtain fr :: "indexname \<Rightarrow> indexname" where fr: "inj_on fr V0" "fr ` V0 \<inter> N = {}"
    using fresh_inj[OF fV0 fN infinite_indexname] by blast
  define \<sigma>P where "\<sigma>P x U = (if has_tf A U then Var (fr x) U else \<sigma> x U)" for x U
  define \<sigma>2 where "\<sigma>2 y V = (if y \<in> fr ` V0 then \<sigma> (the_inv_into V0 fr y) V else Var y V)" for y V
  have ws: "wt_subst \<sigma>" using \<sigma> by (simp add: gsubst_def)
  have cs: "closed (\<sigma> x U)" for x U using ws unfolding wt_subst_def by (blast intro: closed_substD)
  have \<sigma>P: "gsubst \<sigma>P"
    unfolding gsubst_def wt_subst_def closed_subst_def
    using cs wt_subst_typing[OF ws] by (auto simp: \<sigma>P_def closed_def)
  have \<sigma>2: "gsubst \<sigma>2"
    unfolding gsubst_def wt_subst_def closed_subst_def
    using cs wt_subst_typing[OF ws] by (auto simp: \<sigma>2_def closed_def)
  have tid: "has_tf A (tsubst \<rho> U) \<longleftrightarrow> has_tf A U" if "X \<in> TS" "(x, U) \<in> vars X" for X x U
    using has_tf_tsubst[of A \<rho> U] has_tf_tsubst_mono[of A U \<rho>] R1[OF that(1)] vars_typ_tvars[OF that(2)] by blast
  have apP: "ap \<rho> \<sigma>P X = ap \<rho> \<sigma> X" if X: "X \<in> TS" "\<not> tf_in A X" for X
  proof (rule ap_cong_vars)
    fix v U assume vU: "(v, U) \<in> vars X"
    with X(2) have "\<not> has_tf A U" using has_tf_vars by blast
    with tid[OF X(1) vU] show "\<sigma>P v (tsubst \<rho> U) = \<sigma> v (tsubst \<rho> U)" by (simp add: \<sigma>P_def)
  qed
  define e0 where "e0 = (\<lambda>_ :: integer. propT)"
  have s1: "prf_ok ax H e0 [] (prf_ap \<rho> \<sigma>P q) (ap \<rho> \<sigma>P P)"
  proof (rule prf_validD[OF p \<rho> \<sigma>P])
    fix t u assume tu: "(t, u) \<in> set tps"
    with sol[OF tu] apP TS(3)[OF tu] nt[OF tu] show "ap \<rho> \<sigma>P t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>P u" by simp
  qed
  have c\<psi>: "tmap_ok ?\<psi>"
  proof (rule tmap_okI)
    fix a S assume S: "sort_ok alg S"
    have "cert_typ alg ar (\<rho> (g a S) S)" using cinstD(2)[OF \<rho>] S by (cases "g a S") (simp add: cert_inst_def)
    then show "cert_typ alg ar (?\<psi> (TFree a S))" using S by (simp add: inst_tf_def cert_typ_def)
  qed (simp add: inst_tf_def cert_typ_def)
  have sorts: "has_sort alg (map_atyps ?\<psi> T) S" if "has_sort alg T S" for T S
  proof (rule has_sort_map_atyps[OF _ _ that])
    fix a S0
    show "has_sort alg (?\<psi> (TFree a S0)) S0"
    proof (cases "(a, S0) \<in> A")
      case True
      then show ?thesis using cinstD(1)[OF \<rho>] by (cases "g a S0") (simp add: wsinst_def)
    next
      case False
      then show ?thesis by (simp add: has_sort_TFree_iff del: has_sort.simps)
    qed
  next
    fix v S0
    show "has_sort alg (?\<psi> (TVar v S0)) S0" by (simp del: has_sort.simps)
  qed
  have fix\<psi>: "?\<psi> B = B" if "B \<in> tatoms Y" "\<not> tf_in A Y" for B Y
  proof -
    from that(1) obtain U where "B \<in> set (atyps U)" by (auto simp: tatoms_def)
    from atyps_atom[OF this] that show ?thesis by (auto simp: inst_tf_def tf_in_def)
  qed
  have s2: "prf_ok ax H (\<lambda>j. map_atyps ?\<psi> (e0 j)) (map (tmap ?\<psi>) [])
      (map_proof_terms (tmap ?\<psi>) (map_atyps ?\<psi>) (prf_ap \<rho> \<sigma>P q)) (tmap ?\<psi> (ap \<rho> \<sigma>P P))"
  proof (rule prf_ok_tmap[OF c\<psi> sorts _ _ s1])
    fix h B assume "h \<in> H" "B \<in> tatoms h"
    with fix\<psi> H show "?\<psi> B = B" by blast
  next
    fix X B assume "X \<in> prf_atoms (prf_ap \<rho> \<sigma>P q)" "B \<in> tatoms (close X)"
    with fix\<psi> na show "?\<psi> B = B" by (simp add: prf_ap_def)
  next
    fix v S
    show "?\<psi> (TVar v S) = TVar v S" by simp
  qed
  have c0: "cinst TVar" by (simp add: cinst_def wsinst_def cert_inst_def cert_typ_def del: has_sort.simps)
  have s3: "prf_ok ax H (ienv TVar (\<lambda>j. map_atyps ?\<psi> (e0 j))) (map (ap TVar \<sigma>2) (map (tmap ?\<psi>) []))
      (prf_ap TVar \<sigma>2 (map_proof_terms (tmap ?\<psi>) (map_atyps ?\<psi>) (prf_ap \<rho> \<sigma>P q)))
      (ap TVar \<sigma>2 (tmap ?\<psi> (ap \<rho> \<sigma>P P)))"
    by (rule prf_ok_ap[OF c0 \<sigma>2 _ s2]) (use H in blast)
  have hV: "vsubst \<sigma>2 (tmap ?\<psi> (\<sigma>P x (tsubst \<rho> U))) = \<sigma> x (tsubst \<rho> (map_atyps ?gA U))"
    if X: "X \<in> TS" and xU: "(x, U) \<in> vars X" for X x U
  proof (cases "has_tf A U")
    case True
    have x: "x \<in> V0" using X xU by (force simp: V0_def)
    have "map_atyps ?\<psi> (tsubst \<rho> U) = tsubst \<rho> (map_atyps ?gA U)"
      by (rule map_atyps_inst_tf_tsubst) (use R1[OF X] vars_typ_tvars[OF xU] in blast)
    with True tid[OF X xU] x the_inv_into_f_f[OF fr(1) x] show ?thesis by (simp add: \<sigma>P_def \<sigma>2_def)
  next
    case False
    let ?s = "\<sigma> x (tsubst \<rho> U)"
    have xU': "(x, tsubst \<rho> U) \<in> vars (inst \<rho> X)" using xU by (auto simp: vars_inst)
    have nU: "\<not> has_tf A (tsubst \<rho> U)" using False tid[OF X xU] by simp
    have ns: "\<not> tf_in A ?s" by (rule R2[OF X xU' nU])
    have "tmap ?\<psi> ?s = ?s" by (rule map_types_id, rule inst_tf_id) (use ns in \<open>auto simp: tf_in_typs\<close>)
    moreover have "vsubst \<sigma>2 ?s = ?s"
    proof (rule vsubst_Var_id)
      fix y V assume "(y, V) \<in> vars ?s"
      then have "y \<in> N" using X xU' by (force simp: N_def)
      with fr(2) show "\<sigma>2 y V = Var y V" by (auto simp: \<sigma>2_def)
    qed
    moreover have "map_atyps ?gA U = U"
      by (rule map_atyps_has_tf_id[OF False]) (simp_all add: gen_atom_def)
    ultimately show ?thesis using nU by (simp add: \<sigma>P_def)
  qed
  have tm: "ap TVar \<sigma>2 (tmap ?\<psi> (ap \<rho> \<sigma>P X)) = ap \<rho> \<sigma> (tmap ?gA X)" if X: "X \<in> TS" for X
    by (rule gen_inst_term) (use R1[OF X] hV[OF X] in blast)+
  have ty: "tsubst TVar (map_atyps ?\<psi> (tsubst \<rho> T)) = tsubst \<rho> (map_atyps ?gA T)" if "T \<in> prf_typs q" for T
    by (subst map_atyps_inst_tf_tsubst) (use R1T[OF that] in auto)
  have "prf_ap TVar \<sigma>2 (map_proof_terms (tmap ?\<psi>) (map_atyps ?\<psi>) (prf_ap \<rho> \<sigma>P q)) =
      map_proof_terms (ap TVar \<sigma>2 \<circ> (tmap ?\<psi> \<circ> ap \<rho> \<sigma>P)) (tsubst TVar \<circ> (map_atyps ?\<psi> \<circ> tsubst \<rho>)) q"
    by (simp only: prf_ap_def map_proof_terms_comp)
  also have "\<dots> = map_proof_terms (ap \<rho> \<sigma> \<circ> tmap ?gA) (tsubst \<rho> \<circ> map_atyps ?gA) q"
    by (rule map_proof_terms_cong2) (use tm TS(2) ty in auto)
  also have "\<dots> = prf_ap \<rho> \<sigma> (map_proof_terms (tmap ?gA) (map_atyps ?gA) q)"
    by (simp only: prf_ap_def map_proof_terms_comp)
  finally have pe: "prf_ap TVar \<sigma>2 (map_proof_terms (tmap ?\<psi>) (map_atyps ?\<psi>) (prf_ap \<rho> \<sigma>P q)) =
      prf_ap \<rho> \<sigma> (map_proof_terms (tmap ?gA) (map_atyps ?gA) q)" .
  have e0': "ienv TVar (\<lambda>j. map_atyps ?\<psi> (e0 j)) = e0" by (simp add: e0_def propT_def)
  from s3 have s4: "prf_ok ax H e0 [] (prf_ap \<rho> \<sigma> (map_proof_terms (tmap ?gA) (map_atyps ?gA) q))
      (ap \<rho> \<sigma> (tmap ?gA P))"
    by (simp only: pe e0' tm[OF TS(1)] list.map)
  show ?thesis
  proof (rule prf_ok_env[OF s4])
    show "closed h" if "h \<in> H" for h using H[OF that] by blast
    show "cert_typ alg ar (e0 i)" for i by (simp add: e0_def)
    show "prf_nolb 0 (prf_ap \<rho> \<sigma> (map_proof_terms (tmap ?gA) (map_atyps ?gA) q))"
    proof -
      have n1: "prf_nolb 0 (map_proof_terms (tmap ?gA) (map_atyps ?gA) q)"
        by (rule prf_nolb_map[OF _ _ np]) simp_all
      show ?thesis unfolding prf_ap_def by (rule prf_nolb_map[OF _ _ n1]) (use \<sigma> in simp_all)
    qed
    show "closed (ap \<rho> \<sigma> (tmap ?gA P))" using wtpD(1)[OF wP] \<sigma> by (simp add: closed_def)
  qed
qed

end

lemma finite_prf_typs [simp]: "finite (prf_typs p)"
proof (induction p)
  case (PThm x)
  then show ?case by (cases x) (auto split: option.split)
qed (auto split: option.split)

lemma prf_typs_map_proof_terms: "prf_typs (map_proof_terms f g p) = g ` prf_typs p"
proof (induction p)
  case (Abst a T q)
  then show ?case by (cases T) auto
next
  case (PThm x)
  then show ?case by (cases x) (auto split: option.split)
qed (auto split: option.split)

lemma tmap_gen_atom_cong:
  "(\<And>a S. TFree a S \<in> tatoms t \<Longrightarrow> (a, S) \<in> A \<longleftrightarrow> (a, S) \<in> A') \<Longrightarrow> tmap (gen_atom A g) t = tmap (gen_atom A' g) t"
  by (rule map_types_cong, rule map_atyps_cong) (auto simp: gen_atom_def tatoms_def split: ptyp.splits)

lemma map_atyps_gen_atom_cong:
  "(\<And>a S. TFree a S \<in> set (atyps T) \<Longrightarrow> (a, S) \<in> A \<longleftrightarrow> (a, S) \<in> A') \<Longrightarrow>
    map_atyps (gen_atom A g) T = map_atyps (gen_atom A' g) T"
  by (rule map_atyps_cong) (auto simp: gen_atom_def split: ptyp.splits)

context prf_model
begin

text \<open>
  Generalizing free type variables that occur neither in the hypotheses, nor in the flex-flex
  pairs, nor in the closures of the atoms of a proof, keeps proofs valid:
\<close>

theorem prf_valid_gen_tfrees:
  assumes p: "prf_valid ax H tps q P" and wP: "wtp P" and fH: "finite H"
    and H: "\<And>h. h \<in> H \<Longrightarrow> closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in A h"
    and nt: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> \<not> tf_in A t \<and> \<not> tf_in A u"
    and na: "\<And>X. X \<in> prf_atoms q \<Longrightarrow> \<not> tf_in A (close X)"
    and np: "prf_nolb 0 q"
  shows "prf_valid ax H tps (map_proof_terms (tmap (gen_atom A g)) (map_atyps (gen_atom A g)) q)
    (tmap (gen_atom A g) P)"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  define TS where "TS = insert P (prf_terms q \<union> fst ` set tps \<union> snd ` set tps)"
  let ?TY = "prf_typs q"
  have fTS: "finite TS" by (simp add: TS_def)
  have TS: "P \<in> TS" "prf_terms q \<subseteq> TS" "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> t \<in> TS \<and> u \<in> TS"
    by (force simp: TS_def)+
  define A0 where "A0 = {(a, S) \<in> A. TFree a S \<in> (\<Union>X\<in>TS. tatoms X) \<union> (\<Union>T\<in>?TY. set (atyps T))}"
  have fA0: "finite A0"
  proof -
    have "A0 \<subseteq> (\<lambda>(a, S). TFree a S) -` ((\<Union>X\<in>TS. tatoms X) \<union> (\<Union>T\<in>?TY. set (atyps T)))"
      by (auto simp: A0_def)
    moreover have "finite ((\<lambda>(a, S). TFree a S) -` ((\<Union>X\<in>TS. tatoms X) \<union> (\<Union>T\<in>?TY. set (atyps T))))"
      by (rule finite_vimageI) (use fTS in \<open>auto simp: inj_on_def\<close>)
    ultimately show ?thesis by (rule finite_subset)
  qed
  define NB where "NB = (\<Union>X\<in>TS. tatoms X \<union> (\<Union>(v, S)\<in>ttvars X. set (atyps (\<rho> v S))) \<union>
      (\<Union>(x, U)\<in>vars (inst \<rho> X). tatoms (\<sigma> x U))) \<union>
    (\<Union>T\<in>?TY. set (atyps T) \<union> (\<Union>(v, S)\<in>tvars T. set (atyps (\<rho> v S)))) \<union>
    (\<Union>h\<in>H. tatoms h) \<union> (\<Union>X\<in>prf_atoms q. tatoms (close X))"
  define N where "N = {a. \<exists>S. TFree a S \<in> NB}"
  have fNB: "finite NB" using fTS fH by (auto simp: NB_def)
  have fN: "finite N"
  proof -
    have "N \<subseteq> (\<lambda>B. case B of TFree a S \<Rightarrow> a | _ \<Rightarrow> undefined) ` NB" by (force simp: N_def)
    then show ?thesis by (rule finite_surj[OF fNB])
  qed
  obtain c where c: "inj_on c A0" "c ` A0 \<inter> N = {}" using fresh_names[OF fA0 fN] by blast
  have XNB: "tatoms X \<subseteq> NB" if "X \<in> TS" for X using that by (auto simp: NB_def)
  have TNB: "set (atyps T) \<subseteq> NB" if "T \<in> ?TY" for T using that by (auto simp: NB_def)
  have A0N: "a \<in> N" if "(a, S) \<in> A0" for a S
    using that XNB TNB unfolding A0_def N_def by blast
  have cA0: "(c (a, S), b) \<notin> A0" if "(a, S) \<in> A0" for a S b
    using that c(2) A0N by blast
  define p where "p = swap_names A0 c"
  have ri: "ren_inv p" unfolding p_def by (rule swap_names_inv[OF c(1) cA0])
  have pA0: "p a S = c (a, S)" if "(a, S) \<in> A0" for a S using that by (simp add: p_def swap_names_def)
  have pfix: "p a S = a" if "a \<in> N" "(a, S) \<notin> A0" for a S
    using that c(2) by (auto simp: p_def swap_names_def)
  have K: "\<not> has_tf A0 (map_atyps (ren p) U)" if U: "set (atyps U) \<subseteq> NB" for U
  proof
    assume "has_tf A0 (map_atyps (ren p) U)"
    then obtain a' S' B where a': "(a', S') \<in> A0" and B: "B \<in> set (atyps U)"
      and BB: "TFree a' S' \<in> set (atyps (ren p B))"
      by (auto simp: has_tf_def atyps_map_atyps)
    from atyps_atom[OF B] show False
    proof (elim disjE exE)
      fix a S assume BF: "B = TFree a S"
      with BB have e: "a' = p a S" "S' = S" by simp_all
      from BF B U have aN: "a \<in> N" by (auto simp: N_def)
      show False
      proof (cases "(a, S) \<in> A0")
        case True
        then have "p a S = c (a, S)" by (rule pA0)
        with e a' cA0[OF True] show False by simp
      next
        case False
        with e a' pfix[OF aN] show False by simp
      qed
    qed (use BB in simp)
  qed
  have Kt: "\<not> tf_in A0 (tmap (ren p) Y)" if "tatoms Y \<subseteq> NB" for Y
    unfolding tf_in_typs typs_map_types using K that by (fastforce simp: tatoms_def)
  have F1: "map_atyps (ren p) U = U" if F: "\<And>a S. TFree a S \<in> set (atyps U) \<Longrightarrow> a \<in> N \<and> (a, S) \<notin> A0" for U
  proof (rule map_atyps_id)
    fix B assume B: "B \<in> set (atyps U)"
    from atyps_atom[OF B] show "ren p B = B"
      by (elim disjE exE) (use B F pfix in auto)
  qed
  have F1t: "tmap (ren p) Y = Y" if F: "\<And>a S. TFree a S \<in> tatoms Y \<Longrightarrow> a \<in> N \<and> (a, S) \<notin> A0" for Y
    by (rule map_types_id, rule F1) (use F in \<open>auto simp: tatoms_def\<close>)
  have FX: "a \<in> N \<and> (a, S) \<notin> A0" if "tatoms X \<subseteq> NB" "\<not> tf_in A X" "TFree a S \<in> tatoms X" for X a S
    using that by (auto simp: N_def tf_in_def A0_def)
  have renB: "ren p B = B" if "B \<in> tatoms X" "tatoms X \<subseteq> NB" "\<not> tf_in A X" for B X
  proof -
    from that(1) obtain U where "B \<in> set (atyps U)" by (auto simp: tatoms_def)
    from atyps_atom[OF this] show ?thesis
      by (elim disjE exE) (use that FX pfix in auto)
  qed
  let ?gA = "gen_atom A g" and ?gB = "gen_atom A0 g"
  have gT: "map_atyps (ren p) (map_atyps ?gB T) = map_atyps ?gB T" if "set (atyps T) \<subseteq> NB" for T
  proof (rule F1)
    fix a S assume "TFree a S \<in> set (atyps (map_atyps ?gB T))"
    then obtain B where B: "B \<in> set (atyps T)" "TFree a S \<in> set (atyps (?gB B))"
      by (auto simp: atyps_map_atyps)
    from atyps_atom[OF B(1)] B(2) have "B = TFree a S \<and> (a, S) \<notin> A0"
      by (auto simp: gen_atom_def split: if_splits)
    with B(1) that show "a \<in> N \<and> (a, S) \<notin> A0" by (auto simp: N_def)
  qed
  have gX: "tmap (ren p) (tmap ?gB X) = tmap ?gB X" if XN: "tatoms X \<subseteq> NB" for X
  proof (rule F1t)
    fix a S assume "TFree a S \<in> tatoms (tmap ?gB X)"
    then obtain B where B: "B \<in> tatoms X" "TFree a S \<in> set (atyps (?gB B))"
      by (auto simp: tatoms_tmap)
    from B(1) obtain U where "B \<in> set (atyps U)" by (auto simp: tatoms_def)
    from atyps_atom[OF this] B(2) have "B = TFree a S \<and> (a, S) \<notin> A0"
      by (auto simp: gen_atom_def split: if_splits)
    with B(1) XN show "a \<in> N \<and> (a, S) \<notin> A0" by (auto simp: N_def)
  qed
  define q' where "q' = map_proof_terms (tmap ?gB) (map_atyps ?gB) q"
  have q'eq: "map_proof_terms (tmap ?gA) (map_atyps ?gA) q = q'"
    unfolding q'_def
  proof (rule map_proof_terms_cong2)
    fix t assume "t \<in> prf_terms q"
    with TS(2) show "tmap ?gA t = tmap ?gB t" by (intro tmap_gen_atom_cong) (auto simp: A0_def)
  next
    fix T assume "T \<in> ?TY"
    then show "map_atyps ?gA T = map_atyps ?gB T" by (intro map_atyps_gen_atom_cong) (auto simp: A0_def)
  qed
  have P'eq: "tmap ?gA P = tmap ?gB P" by (rule tmap_gen_atom_cong) (use TS(1) in \<open>auto simp: A0_def\<close>)
  define \<rho>1 where "\<rho>1 v S = map_atyps (ren p) (\<rho> v S)" for v S
  define \<sigma>1 where "\<sigma>1 x U = tmap (ren p) (\<sigma> x (map_atyps (ren p) U))" for x U
  have conj: "ap \<rho>1 \<sigma>1 X = tmap (ren p) (ap \<rho> \<sigma> X)" if "tmap (ren p) X = X" for X
    using tmap_ren_ap[OF ri, of \<rho> \<sigma> X] that by (simp add: \<rho>1_def[abs_def] \<sigma>1_def[abs_def])
  have ft: "tmap (ren p) t = t \<and> tmap (ren p) u = u" if "(t, u) \<in> set tps" for t u
    using F1t FX XNB TS(3)[OF that] nt[OF that] by blast
  have A0A: "A0 \<subseteq> A" by (auto simp: A0_def)
  have s1: "prf_ok ax H (\<lambda>j. map_atyps (ren p) (e j)) [] (prf_ap \<rho>1 \<sigma>1 q') (ap \<rho>1 \<sigma>1 (tmap ?gB P))"
    unfolding q'_def
  proof (rule prf_gen_inst[OF p wP _ _ _ np _ _ TS fTS])
    show "closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in A0 h" if "h \<in> H" for h
      using H[OF that] tf_in_mono[OF _ A0A] by blast
    show "\<not> tf_in A0 t \<and> \<not> tf_in A0 u" if "(t, u) \<in> set tps" for t u
      using nt[OF that] tf_in_mono[OF _ A0A] by blast
    show "\<not> tf_in A0 (close X)" if "X \<in> prf_atoms q" for X using na[OF that] tf_in_mono[OF _ A0A] by blast
    show "cinst \<rho>1" unfolding \<rho>1_def by (rule cinst_ren[OF \<rho>])
    show "gsubst \<sigma>1" unfolding \<sigma>1_def by (rule gsubst_ren[OF ri \<sigma>])
    show "\<not> has_tf A0 (\<rho>1 v S)" if "X \<in> TS" "(v, S) \<in> ttvars X" for X v S
      unfolding \<rho>1_def by (rule K) (use that in \<open>auto simp: NB_def\<close>)
    show "\<not> has_tf A0 (\<rho>1 v S)" if "T \<in> ?TY" "(v, S) \<in> tvars T" for T v S
      unfolding \<rho>1_def by (rule K) (use that in \<open>auto simp: NB_def\<close>)
    show "\<not> tf_in A0 (\<sigma>1 x U)" if X: "X \<in> TS" and xU: "(x, U) \<in> vars (inst \<rho>1 X)"
      and nU: "\<not> has_tf A0 U" for X x U
    proof -
      from xU obtain T where xT: "(x, T) \<in> vars X" and U: "U = tsubst \<rho>1 T" by (auto simp: vars_inst)
      have "\<not> has_tf A0 T" using nU U has_tf_tsubst_mono by blast
      then have T: "map_atyps (ren p) T = T"
        by (intro F1) (use XNB[OF X] vars_typ_atoms[OF xT] in \<open>auto simp: N_def has_tf_def\<close>)
      have "map_atyps (ren p) U = tsubst \<rho> T"
        by (simp add: U map_atyps_ren_tsubst T \<rho>1_def ren_inv.map_atyps_ren_ren[OF ri])
      moreover have "(x, tsubst \<rho> T) \<in> vars (inst \<rho> X)" using xT by (auto simp: vars_inst)
      then have "tatoms (\<sigma> x (tsubst \<rho> T)) \<subseteq> NB" using X by (force simp: NB_def)
      ultimately show ?thesis unfolding \<sigma>1_def by (simp add: Kt)
    qed
    show "ap \<rho>1 \<sigma>1 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 \<sigma>1 u" if "(t, u) \<in> set tps" for t u
      using conv_tmap[OF sol[OF that] tmap_ok_ren] conj ft[OF that] by simp
  qed
  have s2: "prf_ok ax H (\<lambda>j. map_atyps (ren p) (map_atyps (ren p) (e j))) (map (tmap (ren p)) [])
      (map_proof_terms (tmap (ren p)) (map_atyps (ren p)) (prf_ap \<rho>1 \<sigma>1 q'))
      (tmap (ren p) (ap \<rho>1 \<sigma>1 (tmap ?gB P)))"
  proof (rule prf_ok_tmap[OF tmap_ok_ren _ _ _ s1])
    fix T S show "has_sort alg T S \<Longrightarrow> has_sort alg (map_atyps (ren p) T) S" by (simp add: has_sort_map_atyps_ren)
  next
    fix h B assume "h \<in> H" "B \<in> tatoms h"
    with H show "ren p B = B" by (intro renB) (auto simp: NB_def)
  next
    fix X B assume "X \<in> prf_atoms (prf_ap \<rho>1 \<sigma>1 q')" "B \<in> tatoms (close X)"
    with na show "ren p B = B" by (intro renB) (auto simp: NB_def prf_ap_def q'_def)
  qed simp
  have tq: "tmap (ren p) t = t" if "t \<in> prf_terms q'" for t
    using that gX XNB TS(2) by (auto simp: q'_def prf_terms_map_proof_terms)
  have yq: "map_atyps (ren p) T = T" if "T \<in> prf_typs q'" for T
    using that gT TNB by (auto simp: q'_def prf_typs_map_proof_terms)
  have "map_proof_terms (tmap (ren p)) (map_atyps (ren p)) (prf_ap \<rho>1 \<sigma>1 q') =
      map_proof_terms (tmap (ren p) \<circ> ap \<rho>1 \<sigma>1) (map_atyps (ren p) \<circ> tsubst \<rho>1) q'"
    by (simp only: prf_ap_def map_proof_terms_comp)
  also have "\<dots> = map_proof_terms (ap \<rho> \<sigma>) (tsubst \<rho>) q'"
  proof (rule map_proof_terms_cong2)
    fix t assume "t \<in> prf_terms q'"
    then show "(tmap (ren p) \<circ> ap \<rho>1 \<sigma>1) t = ap \<rho> \<sigma> t"
      using conj[OF tq] by (simp add: ren_inv.tmap_ren_ren[OF ri])
  next
    fix T assume "T \<in> prf_typs q'"
    then show "(map_atyps (ren p) \<circ> tsubst \<rho>1) T = tsubst \<rho> T"
      using yq by (simp add: map_atyps_ren_tsubst \<rho>1_def ren_inv.map_atyps_ren_ren[OF ri])
  qed
  finally have pe: "map_proof_terms (tmap (ren p)) (map_atyps (ren p)) (prf_ap \<rho>1 \<sigma>1 q') = prf_ap \<rho> \<sigma> q'"
    by (simp only: prf_ap_def)
  have "tmap (ren p) (ap \<rho>1 \<sigma>1 (tmap ?gB P)) = ap \<rho> \<sigma> (tmap ?gB P)"
    using conj[OF gX[OF XNB[OF TS(1)]]] by (simp add: ren_inv.tmap_ren_ren[OF ri])
  with s2 pe show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (map_proof_terms (tmap ?gA) (map_atyps ?gA) q)) (ap \<rho> \<sigma> (tmap ?gA P))"
    by (simp add: q'eq P'eq ren_inv.map_atyps_ren_ren[OF ri])
qed

end

lemma generalize_proof_split:
  "generalize_proof tfrees frees gi prop prf =
    generalize_proof [] frees gi (tmap (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))) prop)
      (map_proof_terms (tmap (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))))
        (map_atyps (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi)))) prf)"
proof -
  let ?g = "gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))"
  have t: "generalize_term tfrees [] gi = generalize_term [] [] gi \<circ> tmap ?g"
    by (rule ext) (simp add: generalize_term_split[of tfrees])
  have T: "generalizeT tfrees gi = generalizeT [] gi \<circ> map_atyps ?g"
    by (rule ext) (simp add: generalizeT_gen_atom[of tfrees])
  show ?thesis
    unfolding generalize_proof_def Let_def t T map_proof_terms_comp[symmetric] by simp
qed

lemma generalize_thm_proof_split:
  "generalize_thm_proof tfrees frees gi tpairs prop prf =
    generalize_thm_proof [] frees gi tpairs (tmap (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))) prop)
      (map_proof_terms (tmap (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi))))
        (map_atyps (gen_atom (tf_set tfrees) (\<lambda>a S. (a, gi)))) prf)"
  unfolding generalize_thm_proof_def Let_def generalize_proof_split[of tfrees] ..

context prf_model
begin

theorem generalize_tfrees_proof_valid:
  assumes ok: "okT (generalize tfrees frees i hs th0) th"
    and p: "prf_valid ax (set hs) (th_tpairs th0) pf (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)"
    and nt: "\<And>t u b. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> b \<in> set frees \<Longrightarrow> b \<notin> fnames t \<and> b \<notin> fnames u"
    and ntf: "\<And>t u. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow>
      \<not> tf_in (tf_set tfrees) t \<and> \<not> tf_in (tf_set tfrees) u"
    and uF: "\<And>t a U V. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<union> prf_terms pf \<Longrightarrow> a \<in> set frees \<Longrightarrow>
      (a, U) \<in> pfrees (th_prop th0) \<Longrightarrow> (a, V) \<in> pfrees t \<Longrightarrow> V = U"
    and axF: "\<And>A a. A \<in> prf_atoms pf \<Longrightarrow> a \<in> set frees \<Longrightarrow> a \<notin> fnames (close A)"
    and na: "\<And>A. A \<in> prf_atoms pf \<Longrightarrow> \<not> tf_in (tf_set tfrees) (close A)"
    and np: "prf_nolb 0 pf"
  shows "prf_valid ax (set hs) (th_tpairs th) (generalize_thm_proof tfrees frees i (th_tpairs th0) (th_prop th0) pf)
    (th_prop th)"
proof (cases "tfrees = []")
  case True
  with ok have "okT (generalize [] frees i hs th0) th" by simp
  from generalize_thm_frees_proof_valid[OF this p wt nt uF axF] True show ?thesis by simp
next
  case False
  let ?A = "tf_set tfrees" and ?g = "\<lambda>a (S :: psort). (a, i)"
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  let ?P1 = "tmap (gen_atom ?A ?g) ?P" and ?gen = "generalize_term tfrees frees i"
    and ?genE = "generalize_term [] frees i"
  let ?q = "map_proof_terms (tmap (gen_atom ?A ?g)) (map_atyps (gen_atom ?A ?g)) pf"
  from ok False have i: "\<not> i \<le> th_maxidx th0" and nb: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> bad_term tfrees frees h"
    and th: "th_tpairs th = map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps" "th_prop th = ?gen ?P"
    by (auto simp: generalize_def returnW_def raiseW_def Let_def mk_rep_def split: if_splits)
  have wP: "wtp ?P" and hw: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h \<and> vars h = {} \<and> ttvars h = {}"
    using wt by (auto simp: wt_thm_def)
  have nth: "\<not> tf_in ?A h" if "h \<in> set hs" for h using nb[OF that] bad_term_tf_in by blast
  have tid: "tmap (gen_atom ?A ?g) t = t \<and> tmap (gen_atom ?A ?g) u = u" if "(t, u) \<in> set ?tps" for t u
    using ntf[OF that] by (simp add: tmap_gen_atom_id)
  have v1: "prf_valid ax (set hs) ?tps ?q ?P1"
  proof (rule prf_valid_gen_tfrees[OF p wP])
    show "closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in ?A h" if "h \<in> set hs" for h
      using hw[OF that] nth[OF that] wtpD(1) by blast
  qed (use ntf na np in auto)
  have tps: "map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps = map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps"
    by (rule map_cong) (auto simp: generalize_term_split[of tfrees] dest: tid)
  have P: "?gen ?P = ?genE ?P1" by (rule generalize_term_split[of tfrees frees i ?P])
  have pf: "generalize_thm_proof tfrees frees i ?tps ?P pf = generalize_thm_proof [] frees i ?tps ?P1 ?q"
    by (rule generalize_thm_proof_split)
  show ?thesis
  proof (cases "frees = []")
    case True
    have g0: "?genE t = t" for t using True generalize_term_id[of frees t i] by simp
    have m: "map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps = ?tps" by (simp add: g0 case_prod_beta')
    have qq: "generalize_thm_proof [] [] i ?tps ?P1 ?q = ?q"
    proof -
      have "generalize_term [] [] i = (\<lambda>t. t)" by (intro ext generalize_term_id) simp
      moreover have "generalizeT [] i = (\<lambda>T. T)" by (intro ext) simp
      ultimately show ?thesis
        by (simp add: generalize_thm_proof_def generalize_proof_def Let_def map_proof_terms_ident)
    qed
    have T: "th_tpairs th = ?tps" using th(1) tps m by simp
    have Pe: "th_prop th = ?P1" using th(2) P g0 by simp
    have Q: "generalize_thm_proof tfrees frees i ?tps ?P pf = ?q" using pf qq True by simp
    show ?thesis unfolding T Pe Q by (rule v1)
  next
    case nf: False
    define th1 where "th1 = mk_rep (th_maxidx th0) ?tps ?P1"
    define th' where "th' = mk_rep (maxidx_tpairs (map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps)
      (maxidx_of_term (?genE ?P1))) (map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps) (?genE ?P1)"
    have nb0: "\<forall>h\<in>set hs. \<not> bad_term [] frees h" using nb bad_term_tf_in by blast
    have ok1: "okT (generalize [] frees i hs th1) th'"
      using nf i nb0 by (simp add: generalize_def returnW_def Let_def th1_def th'_def mk_rep_def)
    have wt1: "wt_thm (max m i) hs ?tps ?P1"
    proof -
      have ib: "ibelow m ?P" using wt by (simp add: wt_thm_def)
      have "ibelow (max m i) ?P1"
        unfolding ibelow_def
      proof (intro conjI ballI)
        fix x assume "x \<in> vars ?P1"
        then obtain U where "(fst x, U) \<in> vars ?P" using vars_tmap_index[of "fst x" "snd x"] by auto
        with ib show "snd (fst x) \<le> max m i" by (force simp: ibelow_def)
      next
        fix q assume "q \<in> ttvars ?P1"
        then have "fst q \<in> fst ` ttvars ?P \<or> snd (fst q) = i"
          using ttvars_tmap_gen_atom[of "fst q" "snd q"] by force
        with ib show "snd (fst q) \<le> max m i" by (force simp: ibelow_def)
      qed
      moreover have "\<forall>(t, u)\<in>set ?tps. closed t \<and> closed u \<and> ibelow (max m i) t \<and> ibelow (max m i) u \<and>
          (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
        using wt by (fastforce simp: wt_thm_def intro: ibelow_mono)
      ultimately show ?thesis using wt wtp_tmap[OF wP tmap_ok_gen_atom] by (simp add: wt_thm_def)
    qed
    have uF1: "V = U" if t: "t \<in> thm_terms hs (th_tpairs th1) (th_prop th1) \<union> prf_terms ?q" and a: "a \<in> set frees"
      and aU: "(a, U) \<in> pfrees (th_prop th1)" and aV: "(a, V) \<in> pfrees t" for t a U V
    proof -
      from aU obtain U0 where U0: "(a, U0) \<in> pfrees ?P" "U = map_atyps (gen_atom ?A ?g) U0"
        by (auto simp: th1_def mk_rep_def pfrees_map_types)
      have nA: "\<not> has_tf ?A V" if "\<not> tf_in ?A t" using has_tf_pfrees[OF aV] that by blast
      have "t \<in> thm_terms hs ?tps ?P \<and> \<not> tf_in ?A t \<or> t = ?P1 \<or> t \<in> prf_terms ?q"
        using t nth ntf by (auto simp: th1_def mk_rep_def thm_terms_def)
      then show ?thesis
      proof (elim disjE conjE)
        assume "t \<in> thm_terms hs ?tps ?P" "\<not> tf_in ?A t"
        with uF[OF _ a U0(1) aV] nA have "V = U0" "\<not> has_tf ?A V" by auto
        then show ?thesis using U0(2) map_atyps_has_tf_id[of ?A V "gen_atom ?A ?g"] by (simp add: gen_atom_def)
      next
        assume "t = ?P1"
        with aV obtain V0 where "(a, V0) \<in> pfrees ?P" "V = map_atyps (gen_atom ?A ?g) V0"
          by (auto simp: pfrees_map_types)
        with uF[of ?P a U0 V0] a U0 show ?thesis by (simp add: thm_terms_def)
      next
        assume "t \<in> prf_terms ?q"
        then obtain t0 where t0: "t0 \<in> prf_terms pf" "t = tmap (gen_atom ?A ?g) t0"
          by (auto simp: prf_terms_map_proof_terms)
        with aV obtain V0 where "(a, V0) \<in> pfrees t0" "V = map_atyps (gen_atom ?A ?g) V0"
          by (auto simp: pfrees_map_types)
        with uF[of t0 a U0 V0] a U0 t0(1) show ?thesis by simp
      qed
    qed
    have "prf_valid ax (set hs) (th_tpairs th1) ?q (th_prop th1)" using v1 by (simp add: th1_def mk_rep_def)
    from generalize_thm_frees_proof_valid[OF ok1 this _ _ uF1] wt1 nt axF
    have "prf_valid ax (set hs) (th_tpairs th') (generalize_thm_proof [] frees i (th_tpairs th1) (th_prop th1) ?q)
        (th_prop th')"
      by (simp add: th1_def mk_rep_def)
    then show ?thesis by (simp add: th'_def th1_def mk_rep_def th tps P pf)
  qed
qed

end

context prf_model
begin

theorem varifyT_global_proof_valid:
  assumes ok: "okT (varifyT_global vl fixed hs th0) (names, th)"
    and p: "prf_valid ax (set hs) (th_tpairs th0) pf (th_prop th0)"
    and wP: "wtp (th_prop th0)" and wh: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and nt: "\<And>t u a S. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> TFree a S \<in> tatoms t \<union> tatoms u \<Longrightarrow>
      (a, S) \<in> set (fold add_tfrees hs fixed)"
    and na: "\<And>A a S. A \<in> prf_atoms pf \<Longrightarrow> TFree a S \<in> tatoms (close A) \<Longrightarrow>
      (a, S) \<in> set (fold add_tfrees hs fixed)"
    and np: "prf_nolb 0 pf"
  shows "prf_valid ax (set hs) (th_tpairs th) (varifyT_proof names pf) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0" and ?tf = "fold add_tfrees hs fixed"
  from ok obtain P1 ts P3 tps0 where f: "ok (full_prop_of ?tps ?P) P1"
    and nm: "names = varify_global_names vl ?tf P1"
    and sp: "ok (strip_prems (integer_of_nat (length ?tps)) [] (map_types (map_atyps (varify_tfree names)) P1))
      (ts, P3)"
    and d: "ok (mapM dest_equals ts) tps0"
    and th: "th_tpairs th = rev tps0" "th_prop th = P3"
    by (auto simp: varifyT_global_def Let_def mk_rep_def split: prod.splits)
  let ?A = "varA names" and ?g = "varg names"
  have vt: "varify_tfree names = gen_atom ?A ?g"
    by (rule varify_tfree_gen_atom) (use map_of_varify_global_names nm in blast)
  have A: "(a, S) \<notin> set ?tf" if "(a, S) \<in> ?A" for a S
    using that map_of_varify_global_names nm by (auto simp: varA_def)
  obtain eqs where eqs: "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) ?tps eqs"
    and P1: "P1 = list_implies eqs ?P"
    by (rule ok_full_prop_of[OF f])
  have l: "integer_of_nat (length ?tps) = ilength (map (tmap (gen_atom ?A ?g)) eqs)"
    using list_all2_lengthD[OF eqs] by (simp add: ilength_eq)
  from sp[unfolded vt P1 tmap_list_implies l strip_prems_list_implies]
  have ts: "ts = rev (map (tmap (gen_atom ?A ?g)) eqs)" and P3: "P3 = tmap (gen_atom ?A ?g) ?P"
    by (simp_all add: return_def)
  have ntf: "\<not> tf_in ?A t \<and> \<not> tf_in ?A u" if "(t, u) \<in> set ?tps" for t u
    using nt[OF that] A by (fastforce simp: tf_in_def)
  have "rev tps0 = map (\<lambda>(t, u). (tmap (gen_atom ?A ?g) t, tmap (gen_atom ?A ?g) u)) ?tps"
    by (rule ok_dest_equals_map_types[OF eqs d ts])
  also have "\<dots> = ?tps" using ntf by (auto intro!: map_idI simp: tmap_gen_atom_id)
  finally have tps: "th_tpairs th = ?tps" by (simp add: th)
  have nh: "\<not> tf_in ?A h" if "h \<in> set hs" for h
    using that A by (fastforce simp: tf_in_def set_fold_add_tfrees)
  have v: "prf_valid ax (set hs) ?tps (map_proof_terms (tmap (gen_atom ?A ?g)) (map_atyps (gen_atom ?A ?g)) pf)
      (tmap (gen_atom ?A ?g) ?P)"
  proof (rule prf_valid_gen_tfrees[OF p wP])
    show "closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in ?A h" if "h \<in> set hs" for h
      using wh[OF that] nh[OF that] wtpD(1) by blast
    show "\<not> tf_in ?A (close X)" if "X \<in> prf_atoms pf" for X
      using na[OF that] A by (fastforce simp: tf_in_def)
  qed (use ntf np in auto)
  have "varifyT_proof names pf = map_proof_terms (tmap (gen_atom ?A ?g)) (map_atyps (gen_atom ?A ?g)) pf"
  proof (cases "names = []")
    case True
    then have "gen_atom ?A ?g = (\<lambda>T. T)" by (auto simp: gen_atom_def varA_def split: ptyp.splits)
    moreover have m: "map_atyps (\<lambda>T. T) = (\<lambda>T. T)" by (rule ext, rule map_atyps_id) simp
    moreover have "map_types (\<lambda>T. T) = (\<lambda>t. t)" by (rule ext, rule map_types_id) simp
    ultimately show ?thesis using True by (simp add: varifyT_proof_def m map_proof_terms_ident)
  next
    case False
    then show ?thesis by (simp add: varifyT_proof_def vt)
  qed
  with v show ?thesis by (simp add: th(2) tps P3)
qed

end

end
