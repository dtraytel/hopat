section \<open>Lifting proofs\<close>

theory Proof_Lift
  imports Proof_Judgment
begin

text \<open>
  \<^const>\<open>lift_proof\<close> turns a valid proof of a rule into a valid proof of the rule lifted over a
  subgoal (\<open>prf_valid_lift_proof\<close>). The proof of each lifted premise is applied to the
  parameters and assumptions of the subgoal (a spine), and the proof of the rule is lifted
  (\<^const>\<open>lift_prf\<close>). The lifted proof of the rule is a proof of an instance of the rule at
  fresh free variables for the parameters, which are then replaced by the parameters
  (\<open>prf_ok_fsubst\<close>).
\<close>


subsection \<open>Weakening\<close>

lemma integer_of_nat_0 [simp]: "integer_of_nat 0 = 0"
  by (simp add: integer_eq_iff integer_of_nat.rep_eq)

lemma integer_of_nat_Suc: "integer_of_nat (Suc n) = integer_of_nat n + 1"
  by (simp add: integer_eq_iff integer_of_nat.rep_eq)

lemma nat_of_integer_plus1: "0 \<le> c \<Longrightarrow> nat_of_integer (c + 1) = Suc (nat_of_integer c)"
  by (simp add: nat_of_integer.rep_eq less_eq_integer.rep_eq nat_add_distrib)

text \<open>Proof-level weakening: a new hypothesis at position \<open>c\<close>.\<close>

fun incr_pbv :: "integer \<Rightarrow> prf \<Rightarrow> prf" where
  "incr_pbv c (PBound i) = (if c \<le> i then PBound (i + 1) else PBound i)"
| "incr_pbv c (AbsP a t p) = AbsP a t (incr_pbv (c + 1) p)"
| "incr_pbv c (Abst a T p) = Abst a T (incr_pbv c p)"
| "incr_pbv c (PAppt p t) = PAppt (incr_pbv c p) t"
| "incr_pbv c (PAppp p q) = PAppp (incr_pbv c p) (incr_pbv c q)"
| "incr_pbv c p = p"

text \<open>Term-level weakening: a new bound variable at position \<open>c\<close>.\<close>

fun incr_tbv :: "integer \<Rightarrow> prf \<Rightarrow> prf" where
  "incr_tbv c (AbsP a t p) = AbsP a (map_option (\<lambda>t. lift t c) t) (incr_tbv c p)"
| "incr_tbv c (Abst a T p) = Abst a T (incr_tbv (c + 1) p)"
| "incr_tbv c (PAppt p t) = PAppt (incr_tbv c p) (map_option (\<lambda>t. lift t c) t)"
| "incr_tbv c (PAppp p q) = PAppp (incr_tbv c p) (incr_tbv c q)"
| "incr_tbv c p = p"

lemma ueq_lift:
  assumes st: "s \<approx> t" and k: "0 \<le> k"
  shows "lift s k \<approx> lift t k"
proof -
  have "equivclp (sup beta eta) (lift x k) (lift y k)" if "equivclp (sup beta eta) x y" for x y
    using that
  proof (induction rule: equivclp_induct)
    case (step y z)
    have "sup beta eta (lift y k) (lift z k) \<or> sup beta eta (lift z k) (lift y k)"
      using step(2) k by (auto intro: beta_lift eta_lift)
    from equivclp_into_equivclp[OF step(3) this] show ?case .
  qed simp
  from this[OF st] show ?thesis by simp
qed

lemma lift_closed: "closed t \<Longrightarrow> 0 \<le> c \<Longrightarrow> incr_bv n c t = t"
  by (rule incr_bv_no_loose) (use loose_bvar_mono[of t c 0] in \<open>auto simp: closed_def\<close>)

context prf_sig
begin

lemma prf_ok_incr_pbv:
  "prf_ok ax H e Hs p \<phi> \<Longrightarrow> 0 \<le> c \<Longrightarrow> nat_of_integer c \<le> length Hs \<Longrightarrow>
    prf_ok ax H e (take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs) (incr_pbv c p) \<phi>"
proof (induction arbitrary: c A rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv)
next
  case (PBound i Hs e)
  let ?Hs = "take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs"
  show ?case
  proof (cases "c \<le> i")
    case True
    then have "nat_of_integer c \<le> nat_of_integer i" by (simp add: integer_reps nat_mono)
    then have "?Hs ! nat_of_integer (i + 1) = Hs ! nat_of_integer i"
      using PBound nat_of_integer_plus1[of i] by (simp add: nth_append)
    moreover have "nat_of_integer (i + 1) < length ?Hs"
      using PBound nat_of_integer_plus1[of i] by simp
    ultimately show ?thesis
      using True PBound prf_ok.PBound[of "i + 1" ?Hs] by simp
  next
    case False
    then have "nat_of_integer i < nat_of_integer c" using PBound(1) by (simp add: integer_reps)
    then have "?Hs ! nat_of_integer i = Hs ! nat_of_integer i"
      using PBound.prems by (simp add: nth_append)
    then show ?thesis
      using False PBound prf_ok.PBound[of i ?Hs] by simp
  qed
next
  case (AbsP e A' t Hs p B a)
  have "prf_ok ax H e (take (nat_of_integer (c + 1)) (A' # Hs) @ A # drop (nat_of_integer (c + 1)) (A' # Hs))
      (incr_pbv (c + 1) p) B"
    using AbsP.IH[of "c + 1" A] AbsP.prems nat_of_integer_plus1[of c] by simp
  then show ?case using AbsP nat_of_integer_plus1[of c] by (auto intro: prf_ok.AbsP)
next
  case (Abst T U e Hs p B a b)
  have "prf_ok ax H (e\<langle>0:U\<rangle>) (take (nat_of_integer c) (map (incr_bv 1 0) Hs) @ incr_bv 1 0 A #
      drop (nat_of_integer c) (map (incr_bv 1 0) Hs)) (incr_pbv c p) B"
    using Abst by simp
  then show ?case using Abst by (auto intro: prf_ok.Abst simp: take_map drop_map)
next
  case (PAppp e Hs p A' B q)
  show ?case unfolding incr_pbv.simps
    by (rule prf_ok.PAppp[OF PAppp.IH(1)[OF PAppp.prems] PAppp.IH(2)[OF PAppp.prems]])
qed (auto intro: prf_ok.intros)

lemma prf_ok_incr_tbv:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> closed h"
  shows "prf_ok ax H e Hs p \<phi> \<Longrightarrow> 0 \<le> c \<Longrightarrow>
    prf_ok ax H (e\<langle>c:U\<rangle>) (map (\<lambda>h. lift h c) Hs) (incr_tbv c p) (lift \<phi> c)"
proof (induction arbitrary: c U rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv conv_lift)
next
  case (PBound i Hs e)
  then show ?case using prf_ok.PBound[of i "map (\<lambda>h. lift h c) Hs"] by auto
next
  case (AbsP e A t Hs p B a)
  then show ?case by (auto intro!: prf_ok.AbsP intro: ueq_lift[simplified] simp: ann_ok_def split: option.splits)
next
  case (Abst T U' e Hs p B a b)
  have eq: "map (\<lambda>h. lift h (c + 1)) (map (incr_bv 1 0) Hs) = map (incr_bv 1 0) (map (\<lambda>h. lift h c) Hs)"
    using lift_lift[of 0 c] Abst.prems by simp
  have "prf_ok ax H (e\<langle>0:U'\<rangle>\<langle>c + 1:U\<rangle>) (map (\<lambda>h. lift h (c + 1)) (map (incr_bv 1 0) Hs)) (incr_tbv (c + 1) p)
      (lift B (c + 1))"
    using Abst.IH[of "c + 1" U] Abst.prems by simp
  then have "prf_ok ax H (e\<langle>c:U\<rangle>\<langle>0:U'\<rangle>) (map (incr_bv 1 0) (map (\<lambda>h. lift h c) Hs)) (incr_tbv (c + 1) p)
      (lift B (c + 1))"
    unfolding eq using shift_commute[OF Abst.prems, of e U U'] by simp
  then show ?case using Abst.hyps(1,2) by (simp add: prf_ok.Abst)
next
  case (PAppt e Hs p U' f t t')
  then show ?case by (auto intro!: prf_ok.PAppt intro: ueq_lift[simplified] simp: ann_ok_def split: option.splits)
next
  case (PAppp e Hs p A B q)
  have "prf_ok ax H (e\<langle>c:U\<rangle>) (map (\<lambda>h. lift h c) Hs) (incr_tbv c p) (implies $ lift A c $ lift B c)"
    using PAppp.IH(1)[OF PAppp.prems, of U] by simp
  then show ?case using PAppp.IH(2)[OF PAppp.prems, of U] by (simp add: prf_ok.PAppp)
next
  case (Hyp t e Hs)
  have "lift t c = t" using H[OF Hyp.hyps(1)] Hyp.prems by (rule lift_closed)
  with Hyp lift_type[OF Hyp.hyps(2) Hyp.prems, of U] show ?case by (simp add: prf_ok.Hyp)
next
  case (PAxm A Us' Us e Hs a)
  have "lift (atom_prop A Us) c = atom_prop A Us" using closed_atom_prop PAxm.prems by (rule lift_closed)
  with PAxm lift_type[OF PAxm.hyps(3) PAxm.prems, of U] show ?case by (simp add: prf_ok.PAxm)
next
  case (Oracle A Us' Us e Hs a)
  have "lift (atom_prop A Us) c = atom_prop A Us" using closed_atom_prop Oracle.prems by (rule lift_closed)
  with Oracle lift_type[OF Oracle.hyps(3) Oracle.prems, of U] show ?case by (simp add: prf_ok.Oracle)
next
  case (PThm h Us e Hs b)
  have "lift (atom_prop (hd_prop h) Us) c = atom_prop (hd_prop h) Us"
    using closed_atom_prop PThm.prems by (rule lift_closed)
  with PThm lift_type[OF PThm.hyps(3) PThm.prems, of U] show ?case by (simp add: prf_ok.PThm)
next
  case (PClass T c' e Hs)
  have "lift (of_class T c') c = of_class T c'" by (simp add: of_class_def)
  with PClass lift_type[OF PClass.hyps(2) PClass.prems, of U] show ?case by (simp add: prf_ok.PClass)
qed

end


subsection \<open>Spines\<close>

text \<open>The proofs of the premises, applied to the parameters and assumptions passed so far.\<close>

definition spine :: "bool list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "spine bs i j c = snd (snd (foldr mk_app bs (i - 1, j - 1, PBound c)))"

lemma foldr_mk_app_fst:
  "foldr mk_app bs (a, b, p) =
    (a - integer_of_nat (length (filter id bs)), b - integer_of_nat (length (filter Not bs)),
     snd (snd (foldr mk_app bs (a, b, p))))"
  by (induction bs) (auto simp: mk_app_def integer_of_nat_Suc split: prod.splits)

lemma foldr_mk_app_Cons:
  "snd (snd (foldr mk_app (x # bs) (a, b, p))) =
    (if x then PAppp (snd (snd (foldr mk_app bs (a, b, p)))) (PBound (a - integer_of_nat (length (filter id bs))))
     else PAppt (snd (snd (foldr mk_app bs (a, b, p)))) (Some (Bound (b - integer_of_nat (length (filter Not bs))))))"
proof -
  obtain a' b' r where e: "foldr mk_app bs (a, b, p) = (a', b', r)" by (cases "foldr mk_app bs (a, b, p)") auto
  then have "a' = a - integer_of_nat (length (filter id bs))" "b' = b - integer_of_nat (length (filter Not bs))"
    using foldr_mk_app_fst[of bs a b p] by simp_all
  with e show ?thesis by (simp add: mk_app_def)
qed

lemma foldr_mk_app_pbv:
  "integer_of_nat (length (filter id bs)) \<le> a + 1 \<Longrightarrow>
    snd (snd (foldr mk_app bs (a + 1, b, incr_pbv 0 p))) = incr_pbv 0 (snd (snd (foldr mk_app bs (a, b, p))))"
proof (induction bs)
  case (Cons x bs)
  show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) (auto simp: integer_of_nat_Suc id_def)
qed simp

lemma foldr_mk_app_tbv:
  "integer_of_nat (length (filter Not bs)) \<le> b + 1 \<Longrightarrow>
    snd (snd (foldr mk_app bs (a, b + 1, incr_tbv 0 p))) = incr_tbv 0 (snd (snd (foldr mk_app bs (a, b, p))))"
proof (induction bs)
  case (Cons x bs)
  show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) (auto simp: integer_of_nat_Suc id_def)
qed simp

lemma spine_True:
  assumes "i = integer_of_nat (length (filter id bs))" "0 \<le> c"
  shows "spine (True # bs) (i + 1) j (c + 1) = PAppp (incr_pbv 0 (spine bs i j c)) (PBound 0)"
proof -
  have "snd (snd (foldr mk_app bs (i - 1 + 1, j - 1, incr_pbv 0 (PBound c)))) = incr_pbv 0 (spine bs i j c)"
    unfolding spine_def using assms by (intro foldr_mk_app_pbv) simp
  then show ?thesis using assms unfolding spine_def foldr_mk_app_Cons by simp
qed

lemma spine_False:
  assumes "j = integer_of_nat (length (filter Not bs))"
  shows "spine (False # bs) i (j + 1) c = PAppt (incr_tbv 0 (spine bs i j c)) (Some (Bound 0))"
proof -
  have "snd (snd (foldr mk_app bs (i - 1, j - 1 + 1, incr_tbv 0 (PBound c)))) = incr_tbv 0 (spine bs i j c)"
    unfolding spine_def using assms by (intro foldr_mk_app_tbv) simp
  then show ?thesis using assms unfolding spine_def foldr_mk_app_Cons by simp
qed

lemma downto_map: "downto a b = map (\<lambda>m. a - integer_of_nat m) [0..<nat_of_integer (a - b + 1)]"
proof (induction a b rule: downto.induct)
  case (1 a b)
  show ?case
  proof (cases "a < b")
    case True
    then have "nat_of_integer (a - b + 1) = 0" by (simp add: integer_reps)
    with True show ?thesis by (simp add: downto.simps)
  next
    case False
    then have n: "nat_of_integer (a - b + 1) = Suc (nat_of_integer (a - b))" by (simp add: integer_reps)
    have "downto a b = a # downto (a - 1) b" using False by (simp add: downto.simps)
    also have "\<dots> = a # map (\<lambda>m. a - 1 - integer_of_nat m) [0..<nat_of_integer (a - b)]" using 1 False by simp
    also have "\<dots> = map (\<lambda>m. a - integer_of_nat m) [0..<Suc (nat_of_integer (a - b))]"
      by (simp del: upt_Suc add: map_upt_Suc integer_of_nat_Suc algebra_simps)
    finally show ?thesis by (simp only: n)
  qed
qed

context prf_sig
begin

lemma prf_ap_spine: "prf_ap \<rho> \<sigma> (spine bs i j c) = spine bs i j c"
proof -
  have "prf_ap \<rho> \<sigma> (snd (snd (foldr mk_app bs (a, b, p)))) = snd (snd (foldr mk_app bs (a, b, prf_ap \<rho> \<sigma> p)))"
    for a b p
  proof (induction bs)
    case (Cons x bs)
    show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) (simp_all add: prf_ap_def)
  qed simp
  then show ?thesis by (simp add: spine_def prf_ap_def)
qed

lemma prf_ap_proof_combP: "prf_ap \<rho> \<sigma> (proof_combP p qs) = proof_combP (prf_ap \<rho> \<sigma> p) (map (prf_ap \<rho> \<sigma>) qs)"
  by (induction qs arbitrary: p) (simp_all add: proof_combP_def prf_ap_def)

lemma prf_ap_mk_AbsP: "prf_ap \<rho> \<sigma> (mk_AbsP xs p) = mk_AbsP xs (prf_ap \<rho> \<sigma> p)"
  by (induction xs) (simp_all add: mk_AbsP_def prf_ap_def)

lemma mk_AbsP_length: "length xs = length ys \<Longrightarrow> mk_AbsP xs p = mk_AbsP ys p"
  by (induction xs ys rule: list_induct2) (simp_all add: mk_AbsP_def)

lemma prf_ok_proof_combP:
  "prf_ok ax H e Hs p (list_implies As B) \<Longrightarrow> list_all2 (prf_ok ax H e Hs) qs As \<Longrightarrow>
    prf_ok ax H e Hs (proof_combP p qs) B"
proof (induction As arbitrary: p qs)
  case Nil
  then show ?case by (simp add: proof_combP_def)
next
  case (Cons A As)
  then obtain q qs' where "qs = q # qs'" by (cases qs) auto
  with Cons show ?case by (auto simp: proof_combP_def intro: prf_ok.PAppp)
qed

lemma prf_ok_mk_AbsP:
  "prf_ok ax H e (rev Ps @ Hs) q X \<Longrightarrow> \<forall>P\<in>set Ps. e \<turnstile> P : propT \<Longrightarrow>
    prf_ok ax H e Hs (mk_AbsP Ps q) (list_implies Ps X)"
proof (induction Ps arbitrary: Hs)
  case (Cons P Ps)
  have "prf_ok ax H e (P # Hs) (mk_AbsP Ps q) (list_implies Ps X)" using Cons by simp
  then show ?case using Cons.prems(2) by (auto simp: mk_AbsP_def intro: prf_ok.AbsP)
qed (simp add: mk_AbsP_def)

end

end
