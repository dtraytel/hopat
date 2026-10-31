section \<open>Composition of proofs\<close>

theory Proof_Compose
  imports Proof_Freeze
begin

context prf_csig
begin

subsection \<open>Conversion of assumptions\<close>

definition hconv :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "hconv V Ts h h' \<longleftrightarrow> wty V Ts h propT \<and> wty V Ts h' propT \<and> tr h \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h'"

lemma hconv_incr_bv:
  assumes "hconv V Ts h h'"
  shows "hconv V (U # Ts) (incr_bv 1 0 h) (incr_bv 1 0 h')"
proof -
  from assms have w: "wty V Ts h propT" "wty V Ts h' propT" and e: "tr h \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h'" by (simp_all add: hconv_def)
  have p: "proper h" "proper h'" using w by (auto simp: wty_def intro: has_type_proper)
  have "wty V (U # Ts) (incr_bv 1 0 h) propT" "wty V (U # Ts) (incr_bv 1 0 h') propT"
    using wty_incr_bv[OF w(1), of 0 U] wty_incr_bv[OF w(2), of 0 U] by (simp_all add: integer_reps)
  moreover have "tr (incr_bv 1 0 h) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (incr_bv 1 0 h')"
    unfolding tr_incr_bv1[OF p(1) order_refl] tr_incr_bv1[OF p(2) order_refl] by (rule lift_equiv[OF e])
  ultimately show ?thesis by (simp add: hconv_def)
qed

lemma prf_ok_Hs_conv:
  "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> list_all2 (hconv V Ts) Hs Hs' \<Longrightarrow> prf_ok V H Ts Hs' p \<phi>"
proof (induction arbitrary: Hs' rule: prf_ok.induct)
  case (conv Ts Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv)
next
  case (PBound i Hs Ts)
  have l: "nat_of_integer i < length Hs'" using PBound list_all2_lengthD by fastforce
  have e: "hconv V Ts (Hs ! nat_of_integer i) (Hs' ! nat_of_integer i)"
    using PBound by (auto simp: list_all2_conv_all_nth)
  have "prf_ok V H Ts Hs' (PBound i) (Hs' ! nat_of_integer i)"
    using PBound(1) l e by (intro prf_ok.PBound) (auto simp: hconv_def)
  then show ?case using e PBound(3) by (auto simp: hconv_def intro: prf_ok.conv equiv_sym)
next
  case (AbsP Ts A t Hs p B a)
  have "hconv V Ts A A" using AbsP(1) by (simp add: hconv_def)
  with AbsP.prems have "list_all2 (hconv V Ts) (A # Hs) (A # Hs')" by simp
  then show ?case using AbsP by (auto intro: prf_ok.AbsP)
next
  case (Abst T U Ts Hs p B a b)
  have "list_all2 (hconv V (U # Ts)) (map (incr_bv 1 0) Hs) (map (incr_bv 1 0) Hs')"
    using Abst.prems by (simp add: list.rel_map) (auto elim: list.rel_mono_strong intro: hconv_incr_bv)
  then show ?case using Abst by (auto intro: prf_ok.Abst)
next
  case (PAppp Ts Hs p A B q)
  then show ?case by (auto intro: prf_ok.PAppp)
qed (auto intro: prf_ok.intros)


subsection \<open>Equivalent annotations\<close>

definition ann_eq :: "pterm option \<Rightarrow> pterm option \<Rightarrow> bool" where
  "ann_eq t t' \<longleftrightarrow> (case (t, t') of
      (None, None) \<Rightarrow> True
    | (Some u, Some u') \<Rightarrow> proper u' \<and> (\<forall>x\<in>vars u'. 0 \<le> snd x) \<and> tr (remove_types u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types u')
    | _ \<Rightarrow> False)"

lemma ann_ok_ann_eq: "ann_ok t A \<Longrightarrow> ann_eq t t' \<Longrightarrow> ann_ok t' A"
  by (auto simp: ann_ok_def ann_eq_def split: option.splits intro: equiv_sym equiv_trans)

text \<open>Proofs that differ only in equivalent annotations.\<close>

inductive prf_aeq :: "prf \<Rightarrow> prf \<Rightarrow> bool" where
  refl: "prf_aeq p p"
| Abst: "prf_aeq p q \<Longrightarrow> prf_aeq (Abst a T p) (Abst b T q)"
| AbsP: "ann_eq t t' \<Longrightarrow> prf_aeq p q \<Longrightarrow> prf_aeq (AbsP a t p) (AbsP b t' q)"
| PAppt: "prf_aeq p q \<Longrightarrow> ann_eq t t' \<Longrightarrow> prf_aeq (PAppt p t) (PAppt q t')"
| PAppp: "prf_aeq p p' \<Longrightarrow> prf_aeq q q' \<Longrightarrow> prf_aeq (PAppp p q) (PAppp p' q')"

inductive_cases prf_aeq_elims:
  "prf_aeq (Abst a T p) q" "prf_aeq (AbsP a t p) q" "prf_aeq (PAppt p t) q" "prf_aeq (PAppp p p') q"

lemma ann_eq_refl: "ann_ok t A \<Longrightarrow> ann_eq t t"
  by (auto simp: ann_ok_def ann_eq_def split: option.splits)

lemma prf_ok_aeq: "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> prf_aeq p q \<Longrightarrow> prf_ok V H Ts Hs q \<phi>"
proof (induction arbitrary: q rule: prf_ok.induct)
  case (conv Ts Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv)
next
  case (AbsP Ts A t Hs p B a)
  from AbsP.prems show ?case
    by (cases rule: prf_aeq_elims(2)) (use AbsP in \<open>auto intro: prf_ok.AbsP ann_ok_ann_eq\<close>)
next
  case (Abst T U Ts Hs p B a b)
  from Abst.prems show ?case
    by (cases rule: prf_aeq_elims(1)) (use Abst in \<open>auto intro: prf_ok.Abst\<close>)
next
  case (PAppt Ts Hs p U f t t')
  from PAppt.prems show ?case
    by (cases rule: prf_aeq_elims(3)) (use PAppt in \<open>auto intro: prf_ok.PAppt ann_ok_ann_eq\<close>)
next
  case (PAppp Ts Hs p A B q)
  from PAppp.prems show ?case
    by (cases rule: prf_aeq_elims(4)) (use PAppp in \<open>auto intro: prf_ok.PAppp\<close>)
qed (auto elim: prf_aeq.cases intro: prf_ok.intros)


subsection \<open>The skeleton of \<open>Proofterm.bicompose_proof\<close>\<close>

lemma list_implies_append: "list_implies (As @ As') C = list_implies As (list_implies As' C)"
  by (induction As) simp_all

lemma rev_nth_downto:
  assumes "length Ns = lb + la" "k < lb"
  shows "rev Ns ! (lb + la - 1 - k) = Ns ! k"
  using assms by (simp add: rev_nth)

lemma downto_PBound:
  "map PBound (downto (integer_of_nat lb + integer_of_nat la - 1) (integer_of_nat la)) =
    map (\<lambda>k. PBound (integer_of_nat (lb + la - 1 - k))) [0..<lb]"
proof -
  have "nat_of_integer (integer_of_nat lb + integer_of_nat la - 1 - integer_of_nat la + 1) = lb"
    by (simp add: integer_reps integer_of_nat.rep_eq)
  moreover have "integer_of_nat lb + integer_of_nat la - 1 - integer_of_nat k = integer_of_nat (lb + la - 1 - k)"
    if "k < lb" for k
    using that by (simp add: integer_eq_iff integer_of_nat.rep_eq of_nat_diff)
  ultimately show ?thesis by (auto simp: downto_map)
qed

lemma prf_ok_compose:
  assumes S: "prf_ok V H [] [] sp (list_implies (Bs @ [Bi]) C)"
    and R: "prf_ok V H [] [] rp (list_implies (Pre @ Olds) B)"
    and BBi: "tr B \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr Bi"
    and Ns: "length Ns = length Bs + length As" "\<forall>N\<in>set Ns. wty V [] N propT"
    and NB: "\<forall>j<length Bs. tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Bs ! j)"
    and args: "list_all2 (\<lambda>a P. prf_ok V H [] (rev Ns) a P) qs (Pre @ Olds)"
  shows "prf_ok V H [] [] (mk_AbsP Ns (PAppp
      (proof_combP sp (map PBound (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As)))))
      (proof_combP rp qs))) (list_implies Ns C)"
proof -
  let ?lb = "length Bs" and ?la = "length As"
  have wS: "\<forall>X\<in>set (Bs @ [Bi]). wty V [] X propT" "wty V [] C propT"
    using wty_list_implies[OF prf_ok_wty[OF S]] by auto
  have wR: "wty V [] B propT" using wty_list_implies[OF prf_ok_wty[OF R]] by auto
  have S': "prf_ok V H [] (rev Ns) sp (list_implies Bs (list_implies [Bi] C))"
    using prf_ok_append[OF S, of "rev Ns"] by (simp add: list_implies_append)
  have "list_all2 (prf_ok V H [] (rev Ns)) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]) Bs"
  proof (rule list_all2_all_nthI)
    fix k assume k: "k < length (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])"
    then have k': "k < ?lb" by simp
    have j: "?lb + ?la - 1 - k < length (rev Ns)" using k' Ns(1) by simp
    then have "rev Ns ! (?lb + ?la - 1 - k) \<in> set Ns" by (metis nth_mem set_rev)
    then have "prf_ok V H [] (rev Ns) (PBound (integer_of_nat (?lb + ?la - 1 - k))) (rev Ns ! (?lb + ?la - 1 - k))"
      using prf_ok.PBound[of "integer_of_nat (?lb + ?la - 1 - k)" "rev Ns" V "[]" H] j Ns(2) by simp
    moreover have "rev Ns ! (?lb + ?la - 1 - k) = Ns ! k" using rev_nth_downto[OF Ns(1) k'] .
    moreover have "tr (Ns ! k) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Bs ! k)" using NB k' by blast
    moreover have "wty V [] (Bs ! k) propT" using wS k' by auto
    ultimately show "prf_ok V H [] (rev Ns) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb] ! k) (Bs ! k)"
      using k' by (auto intro: prf_ok.conv)
  qed simp
  with S' have q: "prf_ok V H [] (rev Ns)
      (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])) (implies $ Bi $ C)"
    by (auto intro: prf_ok_proof_combP)
  have "prf_ok V H [] (rev Ns) (proof_combP rp qs) B"
    using prf_ok_append[OF R, of "rev Ns"] args by (auto intro: prf_ok_proof_combP)
  then have "prf_ok V H [] (rev Ns) (proof_combP rp qs) Bi" using BBi wS by (auto intro: prf_ok.conv)
  with q have "prf_ok V H [] (rev Ns @ []) (PAppp (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]))
      (proof_combP rp qs)) C" by (auto intro: prf_ok.PAppp)
  then show ?thesis using Ns(2) by (auto simp: downto_PBound intro: prf_ok_mk_AbsP)
qed

end

end
