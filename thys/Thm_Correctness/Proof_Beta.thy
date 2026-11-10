section \<open>Contraction of proof redexes\<close>

theory Proof_Beta
  imports Proof_Bicompose
begin

text \<open>
  The normalisation of tight proofs contracts the applications of abstractions over terms to
  terms. The contraction substitutes the argument for the loose bound variable in the annotations
  of the body (\<open>Proofterm.subst_proof_bound\<close>); it is sound for proofs without atoms (axioms,
  oracles and theorems) and with closed hypotheses.
\<close>

fun prf_subst :: "pterm \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_subst u k (Abst a T p) = Abst a T (prf_subst (lift u 0) (k + 1) p)"
| "prf_subst u k (AbsP a t p) = AbsP a (map_option (\<lambda>t. t[u/k]) t) (prf_subst u k p)"
| "prf_subst u k (PAppt p t) = PAppt (prf_subst u k p) (map_option (\<lambda>t. t[u/k]) t)"
| "prf_subst u k (PAppp p q) = PAppp (prf_subst u k p) (prf_subst u k q)"
| "prf_subst u k p = p"

lemma prf_atoms_prf_subst [simp]: "prf_atoms (prf_subst u k p) = prf_atoms p"
  by (induction u k p rule: prf_subst.induct) simp_all


subsection \<open>Equality of annotations\<close>

lemma ueq_subst:
  fixes s t u :: pterm
  shows "s \<approx> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> s[u/k] \<approx> t[u/k]"
proof -
  assume st: "s \<approx> t" and k: "0 \<le> k"
  have "sup beta eta x y \<Longrightarrow> sup beta eta (x[erase u/k]) (y[erase u/k])" for x y
    using k by (auto intro: subst_preserves_beta eta_subst)
  from ueq_cong[OF this st] show ?thesis by simp
qed

lemma beta_eta_subst_arg:
  fixes t s s' :: pterm
  assumes "sup beta eta s s'" "0 \<le> k"
  shows "(sup beta eta)\<^sup>*\<^sup>* (t[s/k]) (t[s'/k])"
proof -
  have b: "beta\<^sup>*\<^sup>* x y \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* x y" for x y
    by (erule rtranclp_mono[THEN predicate2D, rotated]) auto
  have e: "eta\<^sup>*\<^sup>* x y \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* x y" for x y
    by (erule rtranclp_mono[THEN predicate2D, rotated]) auto
  from assms(1) show ?thesis
  proof
    assume "s \<rightarrow>\<^sub>\<beta> s'"
    then have "s \<Rightarrow>\<^sub>\<beta> s'" using beta_subset_par_beta by blast
    from par_beta_subst[OF this par_beta_refl assms(2)] have "t[s/k] \<Rightarrow>\<^sub>\<beta> t[s'/k]" .
    then show ?thesis using par_beta_subset_beta b by blast
  next
    assume "s \<rightarrow>\<^sub>\<eta> s'"
    from rtrancl_eta_subst[OF this assms(2)] show ?thesis by (rule e)
  qed
qed

lemma ueq_subst_arg:
  fixes t s s' :: pterm
  shows "s \<approx> s' \<Longrightarrow> 0 \<le> k \<Longrightarrow> t[s/k] \<approx> t[s'/k]"
proof -
  assume ss: "s \<approx> s'" and k: "0 \<le> k"
  have "equivclp (sup beta eta) ((erase t)[erase s/k]) ((erase t)[erase s'/k])"
    using ss
  proof (induction rule: equivclp_induct)
    case (step y z)
    from step(2) have "(sup beta eta)\<^sup>*\<^sup>* ((erase t)[y/k]) ((erase t)[z/k]) \<or>
        (sup beta eta)\<^sup>*\<^sup>* ((erase t)[z/k]) ((erase t)[y/k])"
      using beta_eta_subst_arg[OF _ k] by blast
    then have "equivclp (sup beta eta) ((erase t)[y/k]) ((erase t)[z/k])"
      by (meson equivclp_sym rtranclp_into_equivclp)
    with step(3) show ?case by (rule equivclp_trans)
  qed simp
  then show ?thesis by simp
qed

lemma prf_aeq_subst_arg: "s \<approx> s' \<Longrightarrow> 0 \<le> k \<Longrightarrow> prf_aeq (prf_subst s k p) (prf_subst s' k p)"
proof (induction p arbitrary: s s' k)
  case (Abst a T p)
  have "lift s 0 \<approx> lift s' 0" by (rule ueq_lift[OF Abst.prems(1)]) simp
  from Abst.IH[OF this] Abst.prems(2) have "prf_aeq (prf_subst (lift s 0) (k + 1) p) (prf_subst (lift s' 0) (k + 1) p)"
    by simp
  then show ?case by (simp add: prf_aeq.Abst)
next
  case (AbsP a t p)
  have "ann_eq (map_option (\<lambda>t. t[s/k]) t) (map_option (\<lambda>t. t[s'/k]) t)"
  proof (cases t)
    case (Some b)
    with ueq_subst_arg[OF AbsP.prems, of b] show ?thesis by (simp add: ann_eq_def)
  qed (simp add: ann_eq_def)
  with AbsP show ?case by (auto intro!: prf_aeq.AbsP)
next
  case (PAppt p t)
  have "ann_eq (map_option (\<lambda>t. t[s/k]) t) (map_option (\<lambda>t. t[s'/k]) t)"
  proof (cases t)
    case (Some b)
    with ueq_subst_arg[OF PAppt.prems, of b] show ?thesis by (simp add: ann_eq_def)
  qed (simp add: ann_eq_def)
  with PAppt show ?case by (auto intro!: prf_aeq.PAppt)
next
  case (PAppp p q)
  then show ?case by (auto intro: prf_aeq.PAppp)
qed (simp_all add: prf_aeq.refl)


context prf_sig
begin

subsection \<open>Substitution\<close>

lemma beta_eta_subst:
  "(sup beta eta)\<^sup>*\<^sup>* x y \<Longrightarrow> 0 \<le> k \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (x[u/k]) (y[u/k])"
proof (induction rule: rtranclp_induct)
  case (step y z)
  then have "sup beta eta (y[u/k]) (z[u/k])" by (auto intro: subst_preserves_beta eta_subst)
  with step show ?case by (blast intro: rtranclp.rtrancl_into_rtrancl)
qed simp

lemma conv_subst:
  fixes \<phi> \<psi> u :: pterm
  assumes c: "\<phi> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<psi>" and t: "e\<langle>k:U\<rangle> \<turnstile> \<phi> : T" "e\<langle>k:U\<rangle> \<turnstile> \<psi> : T'" and u: "e \<turnstile> u : U" and k: "0 \<le> k"
  shows "\<phi>[u/k] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<psi>[u/k]"
proof -
  have w: "wt \<phi>" using t(1) by (auto simp: wt_def)
  obtain a b where ab: "(sup beta eta)\<^sup>*\<^sup>* \<phi> a" "(sup beta eta)\<^sup>*\<^sup>* \<psi> b" "aconv_term a b"
    using church_rosser[OF w c] by blast
  have t': "wt (\<phi>[u/k])" "wt (\<psi>[u/k])"
    using subst_lemma[OF t(1) u HOL.refl k] subst_lemma[OF t(2) u HOL.refl k] by (auto simp: wt_def)
  have 1: "\<phi>[u/k] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> a[u/k]" by (rule beta_eta_conv[OF beta_eta_subst[OF ab(1) k] t'(1)])
  have 2: "a[u/k] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b[u/k]" using ab(3) by (intro aconv_term_conv) (simp add: aconv_term_unname)
  have 3: "\<psi>[u/k] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b[u/k]" by (rule beta_eta_conv[OF beta_eta_subst[OF ab(2) k] t'(2)])
  from 1 2 3 show ?thesis by (meson conv_sym conv_trans)
qed

lemma implies_subst [simp]: "implies[u/k] = implies"
  by (simp add: implies_def)

lemma all_const_subst [simp]: "(all_const U)[u/k] = all_const U"
  by (simp add: all_const_def)

lemma of_class_subst [simp]: "(of_class T c)[u/k] = of_class T c"
  by (simp add: of_class_def)

lemma closed_subst_id: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> t[u/k] = t"
  by (simp add: closed_loose_bvar subst_no_loose)

lemma eqv_subst:
  fixes s t u :: pterm
  shows "eqv (ceqs E) e' s t \<Longrightarrow> e' = e\<langle>k:U\<rangle> \<Longrightarrow> e \<turnstile> u : U \<Longrightarrow> 0 \<le> k \<Longrightarrow> eqv (ceqs E) e (s[u/k]) (t[u/k])"
proof (induction arbitrary: e k u rule: eqv.induct)
  case (eqv_ax s t e' T)
  have c: "closed s" "closed t" using eqv_ax.hyps(1) by simp_all
  have "eqv (ceqs E) e s t" by (rule eqv.eqv_ax[OF eqv_ax.hyps(1) typing_closed[OF eqv_ax.hyps(2) c(1)]
    typing_closed[OF eqv_ax.hyps(3) c(2)]])
  then show ?case using closed_subst_id[OF c(1) eqv_ax.prems(3)] closed_subst_id[OF c(2) eqv_ax.prems(3)] by simp
next
  case (eqv_conv s t e' T)
  show ?case
    by (rule eqv.eqv_conv[OF conv_subst[OF eqv_conv.hyps(1) _ _ eqv_conv.prems(2,3)]
        subst_lemma[OF eqv_conv.hyps(2) eqv_conv.prems(2,1,3)] subst_lemma[OF eqv_conv.hyps(3) eqv_conv.prems(2,1,3)]])
      (use eqv_conv.hyps(2,3) eqv_conv.prems(1) in simp_all)
next
  case (eqv_sym e' s t)
  then show ?case by (blast intro: eqv.eqv_sym)
next
  case (eqv_trans e' s t u')
  then show ?case by (blast intro: eqv.eqv_trans)
next
  case (eqv_app e' s s' t t' V)
  have "e \<turnstile> (s $ t)[u/k] : V" "e \<turnstile> (s' $ t')[u/k] : V"
    by (rule subst_lemma[OF eqv_app.hyps(3) eqv_app.prems(2,1,3)], rule subst_lemma[OF eqv_app.hyps(4) eqv_app.prems(2,1,3)])
  with eqv.eqv_app[OF eqv_app.IH(1)[OF eqv_app.prems] eqv_app.IH(2)[OF eqv_app.prems]] show ?case by simp
next
  case (eqv_abs e' T s t a b)
  have "e'\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>k + 1:U\<rangle>" using eqv_abs.prems(1,3) by simp
  from eqv_abs.IH[OF this _ ] eqv_abs.prems(2,3)
  have "eqv (ceqs E) (e\<langle>0:T\<rangle>) (s[lift u 0/k + 1]) (t[lift u 0/k + 1])" by auto
  from eqv.eqv_abs[OF this eqv_abs.hyps(2)] show ?case by simp
qed

lemma ann_ok_subst:
  fixes u A :: pterm
  assumes "ann_ok t A" "0 \<le> k"
  shows "ann_ok (map_option (\<lambda>t. t[u/k]) t) (A[u/k])"
proof (cases t)
  case (Some a)
  then have "a \<approx> A" using assms(1) by (simp add: ann_ok_def)
  from ueq_subst[OF this assms(2), of u] show ?thesis using Some by (simp add: ann_ok_def)
qed (simp add: ann_ok_def)

lemma prf_ok_subst:
  assumes "prf_ok ax H E e' Hs p \<phi>" "e' = e\<langle>k:U\<rangle>" "e \<turnstile> u : U" "0 \<le> k" "\<forall>h\<in>H. closed h"
  shows "prf_ok ax H E e (map (\<lambda>h. h[u/k]) Hs) (prf_subst u k p) (\<phi>[u/k])"
  using assms
proof (induction arbitrary: e k u U rule: prf_ok.induct)
  case (conv e0 Hs p \<phi> \<psi>)
  have "prf_ok ax H E e (map (\<lambda>h. h[u/k]) Hs) (prf_subst u k p) (\<phi>[u/k])"
    using conv.IH conv.prems by blast
  moreover have "\<phi>[u/k] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<psi>[u/k]"
    using conv_subst[OF conv.hyps(2) _ _ conv.prems(2,3)] prf_ok_typing[OF conv.hyps(1)] conv.hyps(3) conv.prems(1)
    by blast
  moreover have "e \<turnstile> \<psi>[u/k] : propT" by (rule subst_lemma[OF conv.hyps(3) conv.prems(2,1,3)])
  ultimately show ?case by (rule prf_ok.conv)
next
  case (PBound i Hs e0)
  have "e \<turnstile> (Hs ! nat_of_integer i)[u/k] : propT" by (rule subst_lemma[OF PBound.hyps(3) PBound.prems(2,1,3)])
  then show ?case using PBound.hyps(1,2) prf_ok.PBound[of i "map (\<lambda>h. h[u/k]) Hs" e] by simp
next
  case (AbsP e0 A t Hs p B a)
  have "e \<turnstile> A[u/k] : propT" by (rule subst_lemma[OF AbsP.hyps(1) AbsP.prems(2,1,3)])
  moreover have "ann_ok (map_option (\<lambda>t. t[u/k]) t) (A[u/k])" by (rule ann_ok_subst[OF AbsP.hyps(2) AbsP.prems(3)])
  moreover have "prf_ok ax H E e (map (\<lambda>h. h[u/k]) (A # Hs)) (prf_subst u k p) (B[u/k])"
    using AbsP.IH AbsP.prems by simp
  ultimately show ?case by (simp add: prf_ok.AbsP)
next
  case (Abst T U' e0 Hs p B a b)
  have e: "e0\<langle>0:U'\<rangle> = e\<langle>0:U'\<rangle>\<langle>k + 1:U\<rangle>" using Abst.prems(1,3) by simp
  have u: "e\<langle>0:U'\<rangle> \<turnstile> lift u 0 : U" using Abst.prems(2) by auto
  have "prf_ok ax H E (e\<langle>0:U'\<rangle>) (map (\<lambda>h. h[lift u 0/k + 1]) (map (incr_bv 1 0) Hs))
      (prf_subst (lift u 0) (k + 1) p) (B[lift u 0/k + 1])"
    using Abst.IH[OF e u] Abst.prems(3,4) by simp
  moreover have "map (\<lambda>h. h[lift u 0/k + 1]) (map (incr_bv 1 0) Hs) = map (incr_bv 1 0) (map (\<lambda>h. h[u/k]) Hs)"
  proof -
    have "(incr_bv 1 0 h)[lift u 0/k + 1] = incr_bv 1 0 (h[u/k])" for h
      by (rule sym, rule lift_subst_lt) (use Abst.prems(3) in simp_all)
    then show ?thesis by simp
  qed
  ultimately have "prf_ok ax H E (e\<langle>0:U'\<rangle>) (map (incr_bv 1 0) (map (\<lambda>h. h[u/k]) Hs))
      (prf_subst (lift u 0) (k + 1) p) (B[lift u 0/k + 1])" by (simp only:)
  from prf_ok.Abst[OF Abst.hyps(1,2) this] show ?case by simp
next
  case (PAppt e0 Hs p U' f t t')
  have "prf_ok ax H E e (map (\<lambda>h. h[u/k]) Hs) (prf_subst u k p) (all_const U' $ f[u/k])"
    using PAppt.IH PAppt.prems by simp
  moreover have "e \<turnstile> t[u/k] : U'" by (rule subst_lemma[OF PAppt.hyps(2) PAppt.prems(2,1,3)])
  moreover have "ann_ok (map_option (\<lambda>t. t[u/k]) t') (t[u/k])" by (rule ann_ok_subst[OF PAppt.hyps(3) PAppt.prems(3)])
  ultimately show ?case by (simp add: prf_ok.PAppt)
next
  case (PAppp e0 Hs p A B q A')
  have "prf_ok ax H E e (map (\<lambda>h. h[u/k]) Hs) (prf_subst u k p) (implies $ A[u/k] $ B[u/k])"
    using PAppp.IH(1) PAppp.prems by simp
  moreover have "prf_ok ax H E e (map (\<lambda>h. h[u/k]) Hs) (prf_subst u k q) (A'[u/k])"
    using PAppp.IH(2) PAppp.prems by simp
  moreover have "eqv (ceqs E) e (A'[u/k]) (A[u/k])" by (rule eqv_subst[OF PAppp.hyps(3) PAppp.prems(1-3)])
  ultimately show ?case unfolding prf_subst.simps by (rule prf_ok.PAppp)
next
  case (Hyp t e0 Hs)
  have c: "closed t" using Hyp.hyps(1) Hyp.prems(4) by blast
  have "e \<turnstile> t : propT" by (rule typing_closed[OF Hyp.hyps(2) c])
  then show ?case using Hyp.hyps(1) closed_subst_id[OF c Hyp.prems(3)] by (simp add: prf_ok.Hyp)
next
  case (PClass T c e0 Hs)
  have "e \<turnstile> (of_class T c)[u/k] : propT" by (rule subst_lemma[OF PClass.hyps(2) PClass.prems(2,1,3)])
  then show ?case using PClass.hyps(1) by (simp add: prf_ok.PClass)
next
  case (PAxm A Us' Us e0 a Hs)
  have "e \<turnstile> atom_prop A Us : propT" by (rule typing_closed[OF PAxm.hyps(3) closed_atom_prop])
  then show ?case using PAxm.hyps(1,2,4) closed_subst_id[OF closed_atom_prop PAxm.prems(3)]
    by (simp add: prf_ok.PAxm)
next
  case (Oracle A Us' Us e0 Hs a)
  have "e \<turnstile> atom_prop A Us : propT" by (rule typing_closed[OF Oracle.hyps(3) closed_atom_prop])
  then show ?case using Oracle.hyps(1,2) closed_subst_id[OF closed_atom_prop Oracle.prems(3)]
    by (simp add: prf_ok.Oracle)
next
  case (PThm h Us e0 Hs b)
  have "e \<turnstile> atom_prop (hd_prop h) Us : propT" by (rule typing_closed[OF PThm.hyps(3) closed_atom_prop])
  then show ?case using PThm.hyps(1,2) closed_subst_id[OF closed_atom_prop PThm.prems(3)]
    by (simp add: prf_ok.PThm)
qed


subsection \<open>Inversion\<close>

lemma prf_ok_Abst_inv:
  "prf_ok ax H E e Hs q \<phi> \<Longrightarrow> q = Abst a T p \<Longrightarrow> \<exists>U b B. tann_ok T U \<and> cert_typ alg ar U \<and>
    prf_ok ax H E (e\<langle>0:U\<rangle>) (map (incr_bv 1 0) Hs) p B \<and> all_const U $ Abs b U B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi> \<and>
    e \<turnstile> all_const U $ Abs b U B : propT"
proof (induction rule: prf_ok.induct)
  case (conv e Hs q \<phi> \<psi>)
  then show ?case by (meson conv_trans)
next
  case (Abst T' U e Hs p' B a' b)
  then show ?case using prf_ok_typing[OF prf_ok.Abst[OF Abst.hyps]] conv_refl by blast
qed simp_all

lemma prf_ok_PAppt_inv:
  "prf_ok ax H E e Hs q \<phi> \<Longrightarrow> q = PAppt p t' \<Longrightarrow> \<exists>U f t. prf_ok ax H E e Hs p (all_const U $ f) \<and>
    e \<turnstile> t : U \<and> ann_ok t' t \<and> f $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi> \<and> e \<turnstile> f $ t : propT"
proof (induction rule: prf_ok.induct)
  case (conv e Hs q \<phi> \<psi>)
  then show ?case by (meson conv_trans)
next
  case (PAppt e Hs p' U f t t'')
  then show ?case using prf_ok_typing[OF prf_ok.PAppt[OF PAppt.hyps]] conv_refl by blast
qed simp_all


subsection \<open>Contraction\<close>

theorem prf_ok_beta:
  assumes ok: "prf_ok ax H E e Hs (PAppt (Abst a T p) (Some u0)) \<phi>"
    and H: "\<forall>h\<in>H. closed h"
  shows "prf_ok ax H E e Hs (prf_subst u0 0 p) \<phi>"
proof -
  obtain U f t where 1: "prf_ok ax H E e Hs (Abst a T p) (all_const U $ f)" "e \<turnstile> t : U"
    "ann_ok (Some u0) t" "f $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi>" "e \<turnstile> f $ t : propT"
    using prf_ok_PAppt_inv[OF ok HOL.refl] by blast
  obtain U' b B where 2: "prf_ok ax H E (e\<langle>0:U'\<rangle>) (map (incr_bv 1 0) Hs) p B"
    "all_const U' $ Abs b U' B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> all_const U $ f" "e \<turnstile> all_const U' $ Abs b U' B : propT"
    using prf_ok_Abst_inv[OF 1(1) HOL.refl] by blast
  have at2: "atom (all_const U')" "atom (all_const U)" by (simp_all add: all_const_def)
  have w: "wt (all_const U' \<degree>\<degree> [Abs b U' B])" using 2(3) by (auto simp: wt_def)
  have c: "all_const U' \<degree>\<degree> [Abs b U' B] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> all_const U \<degree>\<degree> [f]" using 2(2) by simp
  from conv_atom_apps_inv[OF at2 w c]
  have UU: "U' = U" and fA: "Abs b U' B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> f" by (simp_all add: all_const_def)
  have tA: "e \<turnstile> Abs b U B : U \<rightarrow>\<^sub>T propT" using 2(3) UU by (auto simp: all_const_def)
  have "prf_ok ax H E e (map (\<lambda>h. h[t/0]) (map (incr_bv 1 0) Hs)) (prf_subst t 0 p) (B[t/0])"
    by (rule prf_ok_subst[OF 2(1) _ 1(2) _ H]) (simp_all add: UU)
  moreover have "map (\<lambda>h. h[t/0]) (map (incr_bv 1 0) Hs) = Hs"
  proof (induction Hs)
    case (Cons h Hs)
    have "(incr_bv 1 0 h)[t/0] = h" by (rule subst_lift)
    with Cons show ?case by (simp only: list.map)
  qed (simp only: list.map)
  ultimately have p: "prf_ok ax H E e Hs (prf_subst t 0 p) (B[t/0])" by (simp only:)
  have "Abs b U B $ t \<rightarrow>\<^sub>\<beta> B[t/0]" by (rule beta.beta)
  then have "Abs b U B $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> B[t/0]"
    using tA 1(2) by (intro beta_eta_conv) (auto simp: wt_def)
  moreover have "Abs b U B $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> f $ t"
    using tA 1(2,5) fA UU by (intro conv_App) (auto simp: wt_def)
  ultimately have "B[t/0] \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<phi>" using 1(4) by (meson conv_sym conv_trans)
  from prf_ok.conv[OF p this prf_ok_typing[OF ok]] have "prf_ok ax H E e Hs (prf_subst t 0 p) \<phi>" .
  moreover have "prf_aeq (prf_subst t 0 p) (prf_subst u0 0 p)"
    using 1(3) by (intro prf_aeq_subst_arg) (simp_all add: ann_ok_def ueq_sym)
  ultimately show ?thesis by (rule prf_ok_aeq)
qed

end

end
