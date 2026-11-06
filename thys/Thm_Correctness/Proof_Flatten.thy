section \<open>Proofs of flattened premises and by assumption\<close>

theory Proof_Flatten
  imports Proof_Compose
begin

text \<open>
  \<^const>\<open>flatten_params_proof\<close> proves a premise of the rule from its flattened form (all
  parameters moved to the front, possibly without the assumption \<open>n\<close>), and
  \<^const>\<open>mk_asm_prf\<close> proves the premise that elim-resolution closes by an assumption.
\<close>


subsection \<open>Prefixes\<close>

text \<open>The assumptions of a prefix as seen below all its parameters, the outermost first:\<close>

fun lhyps :: "litem list \<Rightarrow> pterm list" where
  "lhyps [] = []"
| "lhyps (LImp c H # p) = incr_bv (ilength (ptys p)) 0 H # lhyps p"
| "lhyps (LAll c a T # p) = lhyps p"

fun pparams :: "litem list \<Rightarrow> binders" where
  "pparams [] = []"
| "pparams (LImp c H # p) = pparams p"
| "pparams (LAll c a T # p) = (a, T) # pparams p"

lemma map_snd_pparams: "map snd (pparams p) = ptys p"
  by (induction p rule: pparams.induct) simp_all

definition items_ok :: "litem list \<Rightarrow> bool" where
  "items_ok p \<longleftrightarrow> (\<forall>it\<in>set p. case it of LImp c H \<Rightarrow> c = implies | LAll c a T \<Rightarrow> c = all_const T)"

lemma items_ok_simps [simp]:
  "items_ok []" "items_ok (LImp c H # p) \<longleftrightarrow> c = implies \<and> items_ok p"
  "items_ok (LAll c a T # p) \<longleftrightarrow> c = all_const T \<and> items_ok p"
  by (simp_all add: items_ok_def)

lemma items_ok_litem_ok: "items_ok p \<Longrightarrow> \<forall>it\<in>set p. litem_ok it"
proof (intro ballI)
  fix it assume "items_ok p" "it \<in> set p"
  then show "litem_ok it" by (cases it) (auto simp: items_ok_def implies_def all_const_def)
qed

lemma integer_of_nat_ge0 [simp]: "0 \<le> integer_of_nat n"
  by (simp add: less_eq_integer.rep_eq integer_of_nat.rep_eq)

lemma incr_bv_plus: "0 \<le> m \<Longrightarrow> 0 \<le> n \<Longrightarrow> incr_bv m k (incr_bv n k t) = incr_bv (m + n) k t"
  by (induction t arbitrary: k) (auto simp: algebra_simps)

lemma incr_bv_0 [simp]: "incr_bv 0 k t = t"
  by (induction "0 :: integer" k t rule: incr_bv.induct) simp_all

lemma incr_boundvars_eq: "incr_boundvars n t = incr_bv n 0 t"
  by (simp add: incr_boundvars_def)

lemma strip_params_lift_pre:
  "items_ok p \<Longrightarrow> atomic C \<Longrightarrow> strip_params (lift_pre p C) = pparams p"
proof (induction p)
  case Nil
  then show ?case by (simp add: strip_params.simps[of C] atomic_def)
next
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H)
    with Cons show ?thesis by (subst strip_params.simps) (simp add: implies_def)
  next
    case (LAll c a T)
    with Cons show ?thesis by (subst strip_params.simps) (simp add: all_const_def)
  qed
qed

text \<open>The assumptions that \<^const>\<open>remove_params\<close> keeps:\<close>

fun rmhyps :: "integer \<Rightarrow> integer \<Rightarrow> litem list \<Rightarrow> pterm list" where
  "rmhyps j n [] = []"
| "rmhyps j n (LImp c H # p) =
    (if n = 1 then rmhyps j (n - 1) p else incr_boundvars j H # rmhyps j (n - 1) p)"
| "rmhyps j n (LAll c a T # p) = rmhyps (j - 1) n p"

lemma remove_params_lift_pre:
  assumes "items_ok p" "atomic C" "ilength (ptys p) = j" "n \<le> ilength (lhyps p)"
  shows "remove_params j n (lift_pre p C) = return (list_implies (rmhyps j n p) C)"
  using assms
proof (induction p arbitrary: j n)
  case Nil
  then have "j = 0" "n \<le> 0" by simp_all
  moreover have "dest_imp C = None" "dest_all C = None" using Nil(2) by (simp_all add: atomic_def)
  ultimately show ?case by (subst remove_params.simps) simp
next
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H)
    with Cons.prems have c: "c = implies" and ok: "items_ok p" by simp_all
    have n': "n - 1 \<le> ilength (lhyps p)" using Cons.prems(4) LImp by simp
    have j: "ilength (ptys p) = j" using Cons.prems(3) LImp by simp
    show ?thesis
    proof (cases "j = 0 \<and> n \<le> 0")
      case True
      have "remove_params j n (lift_pre (it # p) C) = return (lift_pre (it # p) C)"
        using True by (subst remove_params.simps) simp
      moreover have "list_implies (rmhyps j n (it # p)) C = lift_pre (it # p) C"
      proof -
        have "list_implies (rmhyps 0 n' q) C = lift_pre q C" if "n' \<le> 0" "ptys q = []" "items_ok q" for n' q
          using that
        proof (induction q arbitrary: n')
          case (Cons it' q)
          then show ?case by (cases it') (auto simp: incr_boundvars_def)
        qed simp
        moreover have "ptys (it # p) = []" using True Cons.prems(3)
          by (simp add: ilength_eq integer_eq_iff integer_of_nat.rep_eq)
        ultimately show ?thesis using True Cons.prems(1) by simp
      qed
      ultimately show ?thesis by simp
    next
      case False
      with LImp c n' j ok Cons.IH Cons.prems(2) show ?thesis
        by (subst remove_params.simps) (auto simp: implies_def bindM_def return_def)
    qed
  next
    case (LAll c a T)
    with Cons.prems have c: "c = all_const T" and ok: "items_ok p" by simp_all
    have j1: "ilength (ptys p) = j - 1" using Cons.prems(3) LAll by (simp add: algebra_simps)
    have "j \<noteq> 0"
    proof
      assume "j = 0"
      with j1 ilength_nonneg[of "ptys p"] show False by simp
    qed
    note j = j1 this
    have n': "n \<le> ilength (lhyps p)" using Cons.prems(4) LAll by simp
    with Cons.IH[OF ok Cons.prems(2) j(1) n'] LAll c j(2) show ?thesis
      by (subst remove_params.simps) (simp add: all_const_def)
  qed
qed

lemma rmhyps_lhyps:
  "rmhyps (ilength (ptys p)) n p = map (\<lambda>l. lhyps p ! l) [l \<leftarrow> [0..<length (lhyps p)]. integer_of_nat l + 1 \<noteq> n]"
proof (induction p arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons it p)
  have up: "[0..<Suc L] = 0 # map Suc [0..<L]" for L by (simp add: map_Suc_upt upt_conv_Cons del: upt_Suc)
  have e: "\<And>l. integer_of_nat (Suc l) + 1 \<noteq> n \<longleftrightarrow> integer_of_nat l + 1 \<noteq> n - 1"
    by (auto simp: integer_of_nat_Suc algebra_simps)
  show ?case
  proof (cases it)
    case (LImp c H)
    show ?thesis
    proof (cases "n = 1")
      case True
      have "[l \<leftarrow> [0..<length (lhyps p)]. integer_of_nat l + 1 \<noteq> 0] = [0..<length (lhyps p)]"
        by (intro filter_True) (simp add: integer_eq_iff plus_integer.rep_eq integer_of_nat.rep_eq)
      moreover have "[l \<leftarrow> [0..<length (lhyps p)]. integer_of_nat (Suc l) + 1 \<noteq> 1] = [0..<length (lhyps p)]"
        by (intro filter_True) (simp add: integer_of_nat_Suc integer_eq_iff plus_integer.rep_eq integer_of_nat.rep_eq)
      ultimately show ?thesis using True Cons.IH[of 0] LImp
        by (simp add: up filter_map comp_def del: upt_Suc)
    next
      case False
      with Cons.IH[of "n - 1"] LImp show ?thesis
        by (simp add: up filter_map comp_def e incr_boundvars_eq del: upt_Suc)
    qed
  next
    case (LAll c a T)
    with Cons.IH[of n] show ?thesis by simp
  qed
qed


subsection \<open>Typing\<close>

context prf_sig
begin

lemma typing_incr_pushes: "e \<turnstile> t : T \<Longrightarrow> pushes e Us \<turnstile> incr_bv (ilength Us) 0 t : T"
proof (induction Us arbitrary: e t)
  case (Cons U Us)
  have "e\<langle>0:U\<rangle> \<turnstile> lift t 0 : T" using Cons.prems by auto
  from Cons.IH[OF this] show ?case by (simp add: incr_bv_incr_bv)
qed simp

lemma typing_lift_pre_items:
  "\<forall>it\<in>set p. litem_ok it \<Longrightarrow> e \<turnstile> lift_pre p C : propT \<Longrightarrow>
    items_ok p \<and> pushes e (ptys p) \<turnstile> C : propT \<and> (\<forall>h\<in>set (lhyps p). pushes e (ptys p) \<turnstile> h : propT)"
proof (induction p arbitrary: e)
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H)
    note t = typing_lift_pre_imp[OF _ Cons.prems(2) LImp]
    have c: "c = implies" using t(1) Cons.prems(1) LImp by (auto simp: implies_def)
    have "pushes e (ptys p) \<turnstile> incr_bv (ilength (ptys p)) 0 H : propT"
      using typing_incr_pushes[OF t(2)] Cons.prems(1) LImp by simp
    with Cons.IH[of e] t Cons.prems(1) LImp c show ?thesis by simp
  next
    case (LAll c a T)
    note t = typing_lift_pre_all[OF _ Cons.prems(2) LAll]
    have c: "c = all_const T" using t(1) Cons.prems(1) LAll by (auto simp: all_const_def)
    with Cons.IH[of "e\<langle>0:T\<rangle>"] t Cons.prems(1) LAll show ?thesis by simp
  qed
qed simp

end


subsection \<open>Applying a proof to the parameters\<close>

lemma subst_incr_bv_Bound:
  "0 \<le> k \<Longrightarrow> 0 \<le> n \<Longrightarrow> (incr_bv (n + 1) (k + 1) Y)[Bound (k + n)/k] = incr_bv n k Y"
proof (induction Y arbitrary: k)
  case (Bound i)
  then show ?case
    by (auto simp: subst_Bound less_integer.rep_eq less_eq_integer.rep_eq plus_integer.rep_eq integer_eq_iff)
next
  case (Abs a T Y)
  have "(incr_bv (n + 1) (k + 1 + 1) Y)[Bound (k + 1 + n)/k + 1] = incr_bv n (k + 1) Y"
    using Abs.IH[of "k + 1"] Abs.prems by simp
  moreover have "0 \<le> k + n" using Abs.prems by simp
  ultimately show ?case by (simp add: algebra_simps)
qed simp_all

lemma subst_list_forall:
  "(list_forall vs Z)[s/k] = list_forall vs (Z[incr_bv (ilength vs) 0 s / k + ilength vs])"
proof (induction vs arbitrary: k s)
  case (Cons v vs)
  obtain a T where v: "v = (a, T)" by (cases v)
  have "incr_bv (ilength vs) 0 (lift s 0) = incr_bv (ilength vs + 1) 0 s"
    using incr_bv_plus[of "ilength vs" 1 0 s] ilength_nonneg[of vs] by simp
  with Cons.IH[of "lift s 0" "k + 1"] show ?case by (simp add: v all_const_def algebra_simps)
qed simp

lemma proof_combt_Cons: "proof_combt p (t # ts) = proof_combt (PAppt p (Some t)) ts"
  by (simp add: proof_combt_def)

lemma downto_Cons: "0 \<le> a \<Longrightarrow> downto a 0 = a # downto (a - 1) 0"
  by (subst downto.simps) simp

context prf_sig
begin

lemma prf_ok_combt_bounds:
  "prf_ok ax H e Hs q (list_forall vs (incr_bv (ilength vs) (ilength vs) Y)) \<Longrightarrow>
    (\<forall>l<length vs. e (of_nat (length vs - 1 - l)) = snd (vs ! l)) \<Longrightarrow>
    prf_ok ax H e Hs (proof_combt q (map Bound (downto (ilength vs - 1) 0))) Y"
proof (induction vs arbitrary: q)
  case Nil
  then show ?case by (simp add: downto.simps proof_combt_def)
next
  case (Cons v vs)
  obtain a T where v: "v = (a, T)" by (cases v)
  let ?m = "ilength vs"
  have m0: "0 \<le> ?m" by (rule ilength_nonneg)
  have im: "ilength (v # vs) = ?m + 1" by simp
  have pf: "prf_ok ax H e Hs q (all_const T $ Abs a T (list_forall vs (incr_bv (?m + 1) (?m + 1) Y)))"
    using Cons.prems(1) by (simp add: v)
  have eT: "e ?m = T" using Cons.prems(2)[rule_format, of 0] by (simp add: v ilength_eq integer_of_nat_eq_of_nat)
  have pa: "prf_ok ax H e Hs (PAppt q (Some (Bound ?m))) (Abs a T (list_forall vs (incr_bv (?m + 1) (?m + 1) Y)) $ Bound ?m)"
    by (rule prf_ok.PAppt[OF pf]) (use eT m0 in auto)
  have "(list_forall vs (incr_bv (?m + 1) (?m + 1) Y))[Bound ?m/0] = list_forall vs (incr_bv ?m ?m Y)"
    using subst_incr_bv_Bound[of ?m ?m Y] m0 by (simp add: subst_list_forall)
  then have red: "Abs a T (list_forall vs (incr_bv (?m + 1) (?m + 1) Y)) $ Bound ?m \<rightarrow>\<^sub>\<beta> list_forall vs (incr_bv ?m ?m Y)"
    using beta.beta[of a T "list_forall vs (incr_bv (?m + 1) (?m + 1) Y)" "Bound ?m"] by simp
  have ty: "e \<turnstile> Abs a T (list_forall vs (incr_bv (?m + 1) (?m + 1) Y)) $ Bound ?m : propT"
    by (rule prf_ok_typing[OF pa])
  have cv: "Abs a T (list_forall vs (incr_bv (?m + 1) (?m + 1) Y)) $ Bound ?m \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> list_forall vs (incr_bv ?m ?m Y)"
    by (rule conv_beta_eta) (use ty red in \<open>auto simp: wt_def\<close>)
  have "prf_ok ax H e Hs (PAppt q (Some (Bound ?m))) (list_forall vs (incr_bv ?m ?m Y))"
    by (rule prf_ok.conv[OF pa cv subject_reduction_beta[OF ty red]])
  moreover have "\<forall>l<length vs. e (of_nat (length vs - 1 - l)) = snd (vs ! l)"
  proof (intro allI impI)
    fix l assume l: "l < length vs"
    from Cons.prems(2)[rule_format, of "Suc l"] l show "e (of_nat (length vs - 1 - l)) = snd (vs ! l)" by simp
  qed
  ultimately have "prf_ok ax H e Hs (proof_combt (PAppt q (Some (Bound ?m))) (map Bound (downto (?m - 1) 0))) Y"
    by (rule Cons.IH)
  then show ?case using m0 by (simp add: downto_Cons proof_combt_Cons)
qed

end


subsection \<open>Flattened premises\<close>

definition leafprf :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "leafprf i j n k = proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
    (map PBound (removeAll (i - n) (downto (i - 1) 0)))"

lemma fpp_atomic: "atomic C \<Longrightarrow> flatten_params_proof i j n (C, k) = leafprf i j n k"
  by (cases "(i, j, n, (C, k))" rule: flatten_params_proof.cases) (auto simp: atomic_def leafprf_def)

lemma fpp_imp: "flatten_params_proof i j n (implies $ H $ X, k) = AbsP (STR ''H'') None (flatten_params_proof (i + 1) j n (X, k))"
  and fpp_all: "flatten_params_proof i j n (all_const T $ Abs a T X, k) = Abst a None (flatten_params_proof i (j + 1) n (X, k))"
  by (simp_all add: implies_def all_const_def)

text \<open>Instances of prefixes:\<close>

context prf_sig
begin

fun ap_item :: "tinst \<Rightarrow> vsubst \<Rightarrow> litem \<Rightarrow> litem" where
  "ap_item \<rho> \<sigma> (LImp c H) = LImp c (ap \<rho> \<sigma> H)"
| "ap_item \<rho> \<sigma> (LAll c a T) = LAll (all_const (tsubst \<rho> T)) a (tsubst \<rho> T)"

lemma ptys_ap_item [simp]: "ptys (map (ap_item \<rho> \<sigma>) p) = map (tsubst \<rho>) (ptys p)"
  by (induction p rule: ptys.induct) simp_all

lemma ilength_ptys_ap_item [simp]: "ilength (ptys (map (ap_item \<rho> \<sigma>) p)) = ilength (ptys p)"
  by (simp add: ilength_eq)

lemma lhyps_length_ap_item [simp]: "length (lhyps (map (ap_item \<rho> \<sigma>) p)) = length (lhyps p)"
  by (induction p rule: lhyps.induct) simp_all

lemma items_ok_ap_item: "items_ok p \<Longrightarrow> items_ok (map (ap_item \<rho> \<sigma>) p)"
  by (induction p rule: lhyps.induct) simp_all

lemma ap_lift_pre_items: "items_ok p \<Longrightarrow> ap \<rho> \<sigma> (lift_pre p C) = lift_pre (map (ap_item \<rho> \<sigma>) p) (ap \<rho> \<sigma> C)"
  by (induction p rule: lhyps.induct) simp_all

lemma lhyps_ap_item: "gsubst \<sigma> \<Longrightarrow> lhyps (map (ap_item \<rho> \<sigma>) p) = map (ap \<rho> \<sigma>) (lhyps p)"
  by (induction p rule: lhyps.induct) (simp_all add: ap_lift gsubstD(1) ilength_nonneg)

lemma rmhyps_ap_item: "gsubst \<sigma> \<Longrightarrow> rmhyps j n (map (ap_item \<rho> \<sigma>) p) = map (ap \<rho> \<sigma>) (rmhyps j n p)"
  by (induction j n p rule: rmhyps.induct) (auto simp: incr_boundvars_def ap_lift gsubstD(1))

text \<open>
  The proof walks the prefix of the uninstantiated premise; below the prefix, a proof of the
  instance of the body is given.
\<close>

lemma fpp_gen:
  assumes C: "atomic C" and \<sigma>: "gsubst \<sigma>"
  shows "items_ok p \<Longrightarrow> e \<turnstile> lift_pre (map (ap_item \<rho> \<sigma>) p) C' : propT \<Longrightarrow> (\<forall>h\<in>set Hs. e \<turnstile> h : propT) \<Longrightarrow>
    prf_ok ax H (pushes e (map (tsubst \<rho>) (ptys p)))
      (rev (lhyps (map (ap_item \<rho> \<sigma>) p)) @ map (incr_bv (ilength (ptys p)) 0) Hs)
      (leafprf (i + ilength (lhyps p)) (j + ilength (ptys p)) n k) C' \<Longrightarrow>
    prf_ok ax H e Hs (flatten_params_proof i j n (lift_pre p C, k)) (lift_pre (map (ap_item \<rho> \<sigma>) p) C')"
proof (induction p arbitrary: i j e Hs)
  case Nil
  then show ?case by (simp add: fpp_atomic[OF C])
next
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H')
    then have c: "c = implies" and ok: "items_ok p" using Cons.prems(1) by simp_all
    let ?H = "ap \<rho> \<sigma> H'"
    have t: "e \<turnstile> ?H : propT" "e \<turnstile> lift_pre (map (ap_item \<rho> \<sigma>) p) C' : propT"
      using Cons.prems(2) by (simp_all add: LImp c typing_implies)
    have "prf_ok ax H e (?H # Hs) (flatten_params_proof (i + 1) j n (lift_pre p C, k)) (lift_pre (map (ap_item \<rho> \<sigma>) p) C')"
    proof (rule Cons.IH[OF ok t(2)])
      show "\<forall>h\<in>set (?H # Hs). e \<turnstile> h : propT" using t(1) Cons.prems(3) by simp
      show "prf_ok ax H (pushes e (map (tsubst \<rho>) (ptys p)))
          (rev (lhyps (map (ap_item \<rho> \<sigma>) p)) @ map (incr_bv (ilength (ptys p)) 0) (?H # Hs))
          (leafprf (i + 1 + ilength (lhyps p)) (j + ilength (ptys p)) n k) C'"
        using Cons.prems(4) by (simp add: LImp algebra_simps)
    qed
    then show ?thesis using t(1) by (simp add: LImp c fpp_imp prf_ok.AbsP)
  next
    case (LAll c a T)
    then have c: "c = all_const T" and ok: "items_ok p" using Cons.prems(1) by simp_all
    let ?T = "tsubst \<rho> T"
    have t: "e\<langle>0:?T\<rangle> \<turnstile> lift_pre (map (ap_item \<rho> \<sigma>) p) C' : propT"
      using Cons.prems(2) by (auto simp: LAll all_const_def)
    have cT: "cert_typ alg ar ?T" using Cons.prems(2) by (auto simp: LAll all_const_def)
    have "prf_ok ax H (e\<langle>0:?T\<rangle>) (map (incr_bv 1 0) Hs) (flatten_params_proof i (j + 1) n (lift_pre p C, k))
        (lift_pre (map (ap_item \<rho> \<sigma>) p) C')"
    proof (rule Cons.IH[OF ok t])
      show "\<forall>h\<in>set (map (incr_bv 1 0) Hs). e\<langle>0:?T\<rangle> \<turnstile> h : propT" using Cons.prems(3) by auto
      have eq: "map (incr_bv (ilength (ptys p)) 0) (map (incr_bv 1 0) Hs) = map (incr_bv (ilength (ptys p) + 1) 0) Hs"
        using incr_bv_plus[of "ilength (ptys p)" 1 0] ilength_nonneg[of "ptys p"] by simp
      show "prf_ok ax H (pushes (e\<langle>0:?T\<rangle>) (map (tsubst \<rho>) (ptys p)))
          (rev (lhyps (map (ap_item \<rho> \<sigma>) p)) @ map (incr_bv (ilength (ptys p)) 0) (map (incr_bv 1 0) Hs))
          (leafprf (i + ilength (lhyps p)) (j + 1 + ilength (ptys p)) n k) C'"
        unfolding eq using Cons.prems(4) by (simp add: LAll algebra_simps)
    qed
    then have "prf_ok ax H e Hs (Abst a None (flatten_params_proof i (j + 1) n (lift_pre p C, k)))
        (all_const ?T $ Abs a ?T (lift_pre (map (ap_item \<rho> \<sigma>) p) C'))"
      using cT by (simp add: prf_ok.Abst)
    then show ?thesis by (simp add: LAll c fpp_all)
  qed
qed

lemma removeAll_downto:
  "removeAll (integer_of_nat I - n) (downto (integer_of_nat I - 1) 0) =
    map (\<lambda>l. integer_of_nat I - 1 - integer_of_nat l) [l \<leftarrow> [0..<I]. integer_of_nat l + 1 \<noteq> n]"
proof -
  have "downto (integer_of_nat I - 1) 0 = map (\<lambda>l. integer_of_nat I - 1 - integer_of_nat l) [0..<I]"
    by (simp add: downto_map integer_reps integer_of_nat.rep_eq)
  moreover have "filter (\<lambda>l. integer_of_nat I - 1 - integer_of_nat l \<noteq> integer_of_nat I - n) [0..<I] =
      filter (\<lambda>l. integer_of_nat l + 1 \<noteq> n) [0..<I]"
    by (rule filter_cong) auto
  ultimately show ?thesis
    by (simp add: removeAll_filter_not_eq filter_map comp_def eq_commute[of "integer_of_nat I - n"])
qed

lemma loose_bvar_list_forall: "loose_bvar (list_forall vs Y) k \<longleftrightarrow> loose_bvar Y (k + ilength vs)"
  by (induction vs arbitrary: k) (auto simp: all_const_def algebra_simps)

lemma fpp_leaf:
  assumes ok: "items_ok p" and ty: "e \<turnstile> lift_pre p C : propT"
    and vs: "map snd vs = ptys p"
    and k: "k < length Hs" and ck: "closed (Hs ! k)" and wk: "e \<turnstile> Hs ! k : propT"
    and wN: "wtp (list_forall vs (list_implies (rmhyps (ilength (ptys p)) n p) C))"
    and eN: "Hs ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> list_forall vs (list_implies (rmhyps (ilength (ptys p)) n p) C)"
  shows "prf_ok ax H (pushes e (ptys p)) (rev (lhyps p) @ map (incr_bv (ilength (ptys p)) 0) Hs)
    (leafprf (ilength (lhyps p)) (ilength (ptys p)) n (integer_of_nat k)) C"
proof -
  let ?E = "pushes e (ptys p)" and ?J = "ilength (ptys p)" and ?I = "ilength (lhyps p)"
  let ?Y = "list_implies (rmhyps ?J n p) C"
  let ?Hs = "rev (lhyps p) @ map (incr_bv ?J 0) Hs"
  have tl: "?E \<turnstile> C : propT" "\<forall>h\<in>set (lhyps p). ?E \<turnstile> h : propT"
    using typing_lift_pre_items[OF items_ok_litem_ok[OF ok] ty] by simp_all
  have lv: "ilength vs = ?J" using arg_cong[OF vs, of length] by (simp add: ilength_eq)
  have hk: "?Hs ! (length (lhyps p) + k) = Hs ! k"
    using k lift_closed[OF ck order.refl, of "ilength (ptys p)"] by (simp add: nth_append)
  have ik: "nat_of_integer (integer_of_nat k + ?I) = length (lhyps p) + k"
    by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq nat_add_distrib)
  have "prf_ok ax H ?E ?Hs (PBound (integer_of_nat k + ?I)) (Hs ! k)"
    using prf_ok.PBound[of "integer_of_nat k + ?I" ?Hs ?E ax H] hk ik k typing_closed[OF wk ck, of ?E]
    by (simp add: integer_of_nat_nonneg ilength_nonneg)
  then have "prf_ok ax H ?E ?Hs (PBound (integer_of_nat k + ?I)) (list_forall vs ?Y)"
    using eN wtpD(2)[OF wN] by (rule prf_ok.conv)
  moreover have "incr_bv (ilength vs) (ilength vs) ?Y = ?Y"
  proof (rule incr_bv_no_loose)
    show "\<not> loose_bvar ?Y (ilength vs)" using wtpD(1)[OF wN] loose_bvar_list_forall[of vs ?Y 0] by (simp add: closed_def)
  qed
  ultimately have p1: "prf_ok ax H ?E ?Hs (PBound (integer_of_nat k + ?I)) (list_forall vs (incr_bv (ilength vs) (ilength vs) ?Y))"
    by simp
  have lvs: "length vs = length (ptys p)" using arg_cong[OF vs, of length] by simp
  have bnd: "\<forall>l<length vs. ?E (of_nat (length vs - 1 - l)) = snd (vs ! l)"
  proof (intro allI impI)
    fix l assume l: "l < length vs"
    have "?E (of_nat (length vs - 1 - l)) = ptys p ! (length (ptys p) - 1 - (length vs - 1 - l))"
      using pushes_of_nat[of "length vs - 1 - l" "ptys p" e] l lvs by simp
    also have "\<dots> = ptys p ! l" using l lvs by simp
    also have "\<dots> = snd (vs ! l)" using l vs by (metis nth_map)
    finally show "?E (of_nat (length vs - 1 - l)) = snd (vs ! l)" .
  qed
  have pY: "prf_ok ax H ?E ?Hs (proof_combt (PBound (integer_of_nat k + ?I)) (map Bound (downto (?J - 1) 0))) ?Y"
    using prf_ok_combt_bounds[OF p1 bnd] lv by simp
  have ld: "length (lhyps p) = nat_of_integer ?I" by (simp add: ilength_eq)
  have "list_all2 (prf_ok ax H ?E ?Hs) (map PBound (removeAll (?I - n) (downto (?I - 1) 0))) (rmhyps ?J n p)"
  proof -
    have ri: "removeAll (?I - n) (downto (?I - 1) 0) =
        map (\<lambda>l. ?I - 1 - integer_of_nat l) [l \<leftarrow> [0..<length (lhyps p)]. integer_of_nat l + 1 \<noteq> n]"
      using removeAll_downto[of "length (lhyps p)" n] by (simp add: ilength_eq)
    have "prf_ok ax H ?E ?Hs (PBound (?I - 1 - integer_of_nat l)) (lhyps p ! l)" if l: "l < length (lhyps p)" for l
    proof -
      have n: "nat_of_integer (?I - 1 - integer_of_nat l) = length (lhyps p) - 1 - l"
        using l by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq nat_diff_distrib of_nat_diff)
      have "length (lhyps p) - 1 - l < length (lhyps p)" using l by linarith
      then have "?Hs ! (length (lhyps p) - 1 - l) = lhyps p ! l" using l by (simp add: nth_append rev_nth)
      moreover have "0 \<le> ?I - 1 - integer_of_nat l" using l by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
      ultimately show ?thesis using prf_ok.PBound[of "?I - 1 - integer_of_nat l" ?Hs ?E ax H] n l tl(2) by simp
    qed
    then show ?thesis unfolding ri rmhyps_lhyps list_all2_map1 list_all2_map2
      by (intro list.rel_refl_strong) simp
  qed
  with pY have "prf_ok ax H ?E ?Hs (proof_combP (proof_combt (PBound (integer_of_nat k + ?I)) (map Bound (downto (?J - 1) 0)))
      (map PBound (removeAll (?I - n) (downto (?I - 1) 0)))) C"
    by (rule prf_ok_proof_combP)
  then show ?thesis by (simp add: leafprf_def)
qed

end


end
