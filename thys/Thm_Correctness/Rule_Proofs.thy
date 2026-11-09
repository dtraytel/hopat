section \<open>Validity of the proofs of the inference rules\<close>

theory Rule_Proofs
  imports Varify_Correct
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

end
