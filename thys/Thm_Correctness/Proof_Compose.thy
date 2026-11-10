section \<open>Composition of proofs\<close>

theory Proof_Compose
  imports Proof_Lift
begin

text \<open>
  The skeleton of \<^const>\<open>bicompose_core\<close>: the proof of the proof state, applied to the
  first premises, applied to the proof of the rule, applied to the proofs of its premises. Two
  tools: the hypotheses of the proof level may be replaced by convertible ones, and the
  annotations of a proof by equivalent ones.
\<close>

subsection \<open>Conversion of hypotheses\<close>

context prf_sig
begin

definition hconv :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "hconv e h h' \<longleftrightarrow> e \<turnstile> h' : propT \<and> h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h'"

end


subsection \<open>Equivalent annotations\<close>

definition ann_eq :: "pterm option \<Rightarrow> pterm option \<Rightarrow> bool" where
  "ann_eq t t' \<longleftrightarrow> (case (t, t') of (None, None) \<Rightarrow> True | (Some u, Some u') \<Rightarrow> u \<approx> u' | _ \<Rightarrow> False)"

lemma ann_ok_ann_eq: "ann_ok t A \<Longrightarrow> ann_eq t t' \<Longrightarrow> ann_ok t' A"
  by (auto simp: ann_ok_def ann_eq_def split: option.splits intro: equivclp_sym equivclp_trans)

text \<open>Proofs that differ only in equivalent annotations and in the names of binders:\<close>

inductive prf_aeq :: "prf \<Rightarrow> prf \<Rightarrow> bool" where
  refl: "prf_aeq p p"
| Abst: "prf_aeq p q \<Longrightarrow> prf_aeq (Abst a T p) (Abst b T q)"
| AbsP: "ann_eq t t' \<Longrightarrow> prf_aeq p q \<Longrightarrow> prf_aeq (AbsP a t p) (AbsP b t' q)"
| PAppt: "prf_aeq p q \<Longrightarrow> ann_eq t t' \<Longrightarrow> prf_aeq (PAppt p t) (PAppt q t')"
| PAppp: "prf_aeq p p' \<Longrightarrow> prf_aeq q q' \<Longrightarrow> prf_aeq (PAppp p q) (PAppp p' q')"

inductive_cases prf_aeq_elims:
  "prf_aeq (Abst a T p) q" "prf_aeq (AbsP a t p) q" "prf_aeq (PAppt p t) q" "prf_aeq (PAppp p p') q"

context prf_sig
begin

lemma prf_ok_aeq: "prf_ok ax H E e Hs p \<phi> \<Longrightarrow> prf_aeq p q \<Longrightarrow> prf_ok ax H E e Hs q \<phi>"
proof (induction arbitrary: q rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv)
next
  case (AbsP e A t Hs p B a)
  from AbsP.prems show ?case
    by (cases rule: prf_aeq_elims(2)) (use AbsP in \<open>auto intro: prf_ok.AbsP ann_ok_ann_eq\<close>)
next
  case (Abst T U e Hs p B a b)
  from Abst.prems show ?case
    by (cases rule: prf_aeq_elims(1)) (use Abst in \<open>auto intro: prf_ok.Abst\<close>)
next
  case (PAppt e Hs p U f t t')
  from PAppt.prems show ?case
    by (cases rule: prf_aeq_elims(3)) (use PAppt in \<open>auto intro: prf_ok.PAppt ann_ok_ann_eq\<close>)
next
  case (PAppp e Hs p A B q A')
  from PAppp.prems show ?case
    by (cases rule: prf_aeq_elims(4)) (use PAppp in \<open>auto intro: prf_ok.PAppp\<close>)
qed (auto elim: prf_aeq.cases intro: prf_ok.intros)

end


subsection \<open>The skeleton of \<open>Proofterm.bicompose_proof\<close>\<close>

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

context prf_sig
begin

lemma prf_ok_compose_body:
  assumes S: "prf_ok ax H E e [] sp (list_implies (Bs @ [Bi]) C)"
    and R: "prf_ok ax H E e [] rp (list_implies (Pre @ Olds) B)"
    and BBi: "eqv (ceqs E) e B Bi"
    and Ns: "length Ns = length Bs + length As" "\<forall>N\<in>set Ns. e \<turnstile> N : propT"
    and NB: "\<forall>j<length Bs. Ns ! j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bs ! j"
    and args: "list_all2 (\<lambda>a P. \<exists>P'. prf_ok ax H E e (rev Ns) a P' \<and> eqv (ceqs E) e P' P) qs (Pre @ Olds)"
  shows "prf_ok ax H E e (rev Ns @ []) (PAppp
      (proof_combP sp (map PBound (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As)))))
      (proof_combP rp qs)) C"
proof -
  let ?lb = "length Bs" and ?la = "length As"
  have wS: "\<forall>X\<in>set (Bs @ [Bi]). e \<turnstile> X : propT" "e \<turnstile> C : propT"
    using typing_list_impliesD[OF prf_ok_typing[OF S]] by auto
  have S': "prf_ok ax H E e (rev Ns) sp (list_implies Bs (list_implies [Bi] C))"
    using prf_ok_append[OF S, of "rev Ns"] by (simp add: list_implies_append)
  have "list_all2 (prf_ok ax H E e (rev Ns)) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]) Bs"
  proof (rule list_all2_all_nthI)
    fix k assume k: "k < length (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])"
    then have k': "k < ?lb" by simp
    have j: "?lb + ?la - 1 - k < length (rev Ns)" using k' Ns(1) by simp
    then have "rev Ns ! (?lb + ?la - 1 - k) \<in> set Ns" by (metis nth_mem set_rev)
    then have "prf_ok ax H E e (rev Ns) (PBound (integer_of_nat (?lb + ?la - 1 - k))) (rev Ns ! (?lb + ?la - 1 - k))"
      using prf_ok.PBound[of "integer_of_nat (?lb + ?la - 1 - k)" "rev Ns" e ax H] j Ns(2)
      by (simp add: integer_of_nat_nonneg)
    moreover have "rev Ns ! (?lb + ?la - 1 - k) = Ns ! k" using Ns(1) k' by (simp add: rev_nth)
    moreover have "Ns ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bs ! k" using NB k' by blast
    moreover have "e \<turnstile> Bs ! k : propT" using wS k' by auto
    ultimately show "prf_ok ax H E e (rev Ns) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb] ! k) (Bs ! k)"
      using k' by (auto intro: prf_ok.conv)
  qed simp
  with S' have q: "prf_ok ax H E e (rev Ns)
      (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])) (implies $ Bi $ C)"
    by (auto intro: prf_ok_proof_combP)
  have "prf_ok ax H E e (rev Ns) (proof_combP rp qs) B"
    using prf_ok_append[OF R, of "rev Ns"] args by (auto intro: prf_ok_proof_combP_eqv)
  with q have "prf_ok ax H E e (rev Ns @ []) (PAppp (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]))
      (proof_combP rp qs)) C" using BBi by (auto intro: prf_ok.PAppp)
  then show ?thesis by (simp add: downto_PBound)
qed

lemma prf_ok_compose:
  assumes S: "prf_ok ax H E e [] sp (list_implies (Bs @ [Bi]) C)"
    and R: "prf_ok ax H E e [] rp (list_implies (Pre @ Olds) B)"
    and BBi: "eqv (ceqs E) e B Bi"
    and Ns: "length Ns = length Bs + length As" "\<forall>N\<in>set Ns. e \<turnstile> N : propT"
    and NB: "\<forall>j<length Bs. Ns ! j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bs ! j"
    and args: "list_all2 (\<lambda>a P. \<exists>P'. prf_ok ax H E e (rev Ns) a P' \<and> eqv (ceqs E) e P' P) qs (Pre @ Olds)"
  shows "prf_ok ax H E e [] (mk_AbsP Ns (PAppp
      (proof_combP sp (map PBound (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As)))))
      (proof_combP rp qs))) (list_implies Ns C)"
  by (rule prf_ok_mk_AbsP[OF prf_ok_compose_body[OF assms] Ns(2)])

end

end
