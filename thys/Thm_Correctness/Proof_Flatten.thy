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
        by (simp add: up filter_map comp_def e incr_boundvars_incr_bv del: upt_Suc)
    qed
  next
    case (LAll c a T)
    with Cons.IH[of n] show ?thesis by simp
  qed
qed


subsection \<open>Typing\<close>

context prf_sig
begin

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
    using incr_bv_incr_bv[of "ilength vs" 1 0 s] ilength_nonneg[of vs] by simp
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

text \<open>
  The proof of a flattened premise with annotations \<open>fA\<close> of the assumptions and \<open>fT\<close> of the
  parameters: none in \<open>Proofterm.flatten_params_proof\<close>, the propositions and types themselves
  in \<open>ZTerm.flatten_params_proof\<close>.
\<close>

fun aflatten_params_proof :: "(pterm \<Rightarrow> pterm option) \<Rightarrow> (ptyp \<Rightarrow> ptyp option) \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow>
    integer \<Rightarrow> pterm \<times> integer \<Rightarrow> prf" where
  "aflatten_params_proof fA fT i j n (Const c U $ A $ B, k) =
    (if c = STR ''Pure.imp'' then AbsP (STR ''H'') (fA A) (aflatten_params_proof fA fT (i + 1) j n (B, k))
     else proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
       (map PBound (removeAll (i - n) (downto (i - 1) 0))))"
| "aflatten_params_proof fA fT i j n (Const c U $ Abs a T t, k) =
    (if c = STR ''Pure.all'' then Abst a (fT T) (aflatten_params_proof fA fT i (j + 1) n (t, k))
     else proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
       (map PBound (removeAll (i - n) (downto (i - 1) 0))))"
| "aflatten_params_proof fA fT i j n (_, k) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
      (map PBound (removeAll (i - n) (downto (i - 1) 0)))"

lemma flatten_params_proof_aflatten:
  "flatten_params_proof i j n x = aflatten_params_proof (\<lambda>_. None) (\<lambda>_. None) i j n x"
  by (induction i j n x rule: flatten_params_proof.induct) simp_all

lemma fpp_atomic: "atomic C \<Longrightarrow> aflatten_params_proof fA fT i j n (C, k) = leafprf i j n k"
  by (cases "(fA, fT, i, j, n, (C, k))" rule: aflatten_params_proof.cases) (auto simp: atomic_def leafprf_def)

lemma fpp_imp: "aflatten_params_proof fA fT i j n (implies $ H $ X, k) =
    AbsP (STR ''H'') (fA H) (aflatten_params_proof fA fT (i + 1) j n (X, k))"
  and fpp_all: "aflatten_params_proof fA fT i j n (all_const T $ Abs a T X, k) =
    Abst a (fT T) (aflatten_params_proof fA fT i (j + 1) n (X, k))"
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

lemma rmhyps_ap_item: "gsubst \<sigma> \<Longrightarrow> rmhyps j n (map (ap_item \<rho> \<sigma>) p) = map (ap \<rho> \<sigma>) (rmhyps j n p)"
  by (induction j n p rule: rmhyps.induct) (auto simp: incr_boundvars_def ap_lift gsubstD(1))

text \<open>
  The proof walks the prefix of the uninstantiated premise; below the prefix, a proof of the
  instance of the body is given.
\<close>

lemma prf_ap_leafprf: "prf_ap \<rho> \<sigma> (leafprf i j n k) = leafprf i j n k"
proof -
  have ct: "prf_ap \<rho> \<sigma> (proof_combt p ts) = proof_combt (prf_ap \<rho> \<sigma> p) (map (ap \<rho> \<sigma>) ts)" for p ts
    unfolding proof_combt_def by (induction ts arbitrary: p) (simp_all add: prf_ap_def)
  have "prf_ap \<rho> \<sigma> (PBound x) = PBound x" for x by (simp add: prf_ap_def)
  then show ?thesis by (simp add: leafprf_def prf_ap_proof_combP ct comp_def)
qed

lemma fpp_gen:
  assumes C: "atomic C" and \<sigma>: "gsubst \<sigma>"
    and fA: "\<And>A. fA A = None \<or> fA A = Some A" and fT: "\<And>T. fT T = None \<or> fT T = Some T"
  shows "items_ok p \<Longrightarrow> e \<turnstile> lift_pre (map (ap_item \<rho> \<sigma>) p) C' : propT \<Longrightarrow> (\<forall>h\<in>set Hs. e \<turnstile> h : propT) \<Longrightarrow>
    prf_ok ax H (pushes e (map (tsubst \<rho>) (ptys p)))
      (rev (lhyps (map (ap_item \<rho> \<sigma>) p)) @ map (incr_bv (ilength (ptys p)) 0) Hs)
      (leafprf (i + ilength (lhyps p)) (j + ilength (ptys p)) n k) C' \<Longrightarrow>
    prf_ok ax H e Hs (prf_ap \<rho> \<sigma> (aflatten_params_proof fA fT i j n (lift_pre p C, k)))
      (lift_pre (map (ap_item \<rho> \<sigma>) p) C')"
proof (induction p arbitrary: i j e Hs)
  case Nil
  then show ?case by (simp add: fpp_atomic[OF C] prf_ap_leafprf)
next
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H')
    then have c: "c = implies" and ok: "items_ok p" using Cons.prems(1) by simp_all
    let ?H = "ap \<rho> \<sigma> H'"
    have t: "e \<turnstile> ?H : propT" "e \<turnstile> lift_pre (map (ap_item \<rho> \<sigma>) p) C' : propT"
      using Cons.prems(2) by (simp_all add: LImp c typing_implies)
    have "prf_ok ax H e (?H # Hs) (prf_ap \<rho> \<sigma> (aflatten_params_proof fA fT (i + 1) j n (lift_pre p C, k)))
        (lift_pre (map (ap_item \<rho> \<sigma>) p) C')"
    proof (rule Cons.IH[OF ok t(2)])
      show "\<forall>h\<in>set (?H # Hs). e \<turnstile> h : propT" using t(1) Cons.prems(3) by simp
      show "prf_ok ax H (pushes e (map (tsubst \<rho>) (ptys p)))
          (rev (lhyps (map (ap_item \<rho> \<sigma>) p)) @ map (incr_bv (ilength (ptys p)) 0) (?H # Hs))
          (leafprf (i + 1 + ilength (lhyps p)) (j + ilength (ptys p)) n k) C'"
        using Cons.prems(4) by (simp add: LImp algebra_simps)
    qed
    moreover have "ann_ok (map_option (ap \<rho> \<sigma>) (fA H')) ?H" using fA[of H'] by auto
    ultimately show ?thesis using t(1) by (simp add: LImp c fpp_imp prf_ok.AbsP prf_ap_def)
  next
    case (LAll c a T)
    then have c: "c = all_const T" and ok: "items_ok p" using Cons.prems(1) by simp_all
    let ?T = "tsubst \<rho> T"
    have t: "e\<langle>0:?T\<rangle> \<turnstile> lift_pre (map (ap_item \<rho> \<sigma>) p) C' : propT"
      using Cons.prems(2) by (auto simp: LAll all_const_def)
    have cT: "cert_typ alg ar ?T" using Cons.prems(2) by (auto simp: LAll all_const_def)
    have "prf_ok ax H (e\<langle>0:?T\<rangle>) (map (incr_bv 1 0) Hs) (prf_ap \<rho> \<sigma> (aflatten_params_proof fA fT i (j + 1) n (lift_pre p C, k)))
        (lift_pre (map (ap_item \<rho> \<sigma>) p) C')"
    proof (rule Cons.IH[OF ok t])
      show "\<forall>h\<in>set (map (incr_bv 1 0) Hs). e\<langle>0:?T\<rangle> \<turnstile> h : propT" using Cons.prems(3) by auto
      have eq: "map (incr_bv (ilength (ptys p)) 0) (map (incr_bv 1 0) Hs) = map (incr_bv (ilength (ptys p) + 1) 0) Hs"
        using incr_bv_incr_bv[of "ilength (ptys p)" 1 0] ilength_nonneg[of "ptys p"] by simp
      show "prf_ok ax H (pushes (e\<langle>0:?T\<rangle>) (map (tsubst \<rho>) (ptys p)))
          (rev (lhyps (map (ap_item \<rho> \<sigma>) p)) @ map (incr_bv (ilength (ptys p)) 0) (map (incr_bv 1 0) Hs))
          (leafprf (i + ilength (lhyps p)) (j + 1 + ilength (ptys p)) n k) C'"
        unfolding eq using Cons.prems(4) by (simp add: LAll algebra_simps)
    qed
    moreover have "tann_ok (map_option (tsubst \<rho>) (fT T)) ?T" using fT[of T] by auto
    ultimately have "prf_ok ax H e Hs (Abst a (map_option (tsubst \<rho>) (fT T))
        (prf_ap \<rho> \<sigma> (aflatten_params_proof fA fT i (j + 1) n (lift_pre p C, k))))
        (all_const ?T $ Abs a ?T (lift_pre (map (ap_item \<rho> \<sigma>) p) C'))"
      using cT by (simp add: prf_ok.Abst)
    then show ?thesis by (simp add: LAll c fpp_all prf_ap_def)
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
    using k incr_bv_closed[OF ck order.refl, of "ilength (ptys p)"] by (simp add: nth_append)
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



lemma remove_params_n_le:
  "items_ok p \<Longrightarrow> atomic C \<Longrightarrow> ilength (ptys p) = j \<Longrightarrow> ok (remove_params j n (lift_pre p C)) X \<Longrightarrow>
    n \<le> ilength (lhyps p)"
proof (induction p arbitrary: j n X)
  case Nil
  then have j: "j = 0" by simp
  have "dest_imp C = None" "dest_all C = None" using Nil(2) by (simp_all add: atomic_def)
  with Nil(4) j show ?case by (subst (asm) remove_params.simps) (auto split: if_splits)
next
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H)
    with Cons.prems have c: "c = implies" and ok: "items_ok p" by simp_all
    have j: "ilength (ptys p) = j" using Cons.prems(3) LImp by simp
    show ?thesis
    proof (cases "j = 0 \<and> n \<le> 0")
      case True
      then show ?thesis using ilength_nonneg[of "lhyps (it # p)"] by (meson order.trans)
    next
      case False
      show ?thesis
      proof (cases "n = 1")
        case True
        then show ?thesis using LImp ilength_nonneg[of "lhyps p"] by simp
      next
        case n1: False
        from Cons.prems(4) False n1 LImp c obtain B' where "ok (remove_params j (n - 1) (lift_pre p C)) B'"
          by (subst (asm) remove_params.simps) (auto simp: implies_def)
        from Cons.IH[OF ok Cons.prems(2) j this] LImp show ?thesis by simp
      qed
    qed
  next
    case (LAll c a T)
    with Cons.prems have c: "c = all_const T" and ok: "items_ok p" by simp_all
    have j1: "ilength (ptys p) = j - 1" using Cons.prems(3) LAll by (simp add: algebra_simps)
    have j0: "j \<noteq> 0"
    proof
      assume "j = 0"
      with j1 ilength_nonneg[of "ptys p"] show False by simp
    qed
    from Cons.prems(4) j0 LAll c have "ok (remove_params (j - 1) n (lift_pre p C)) X"
      by (subst (asm) remove_params.simps) (simp add: all_const_def)
    from Cons.IH[OF ok Cons.prems(2) j1 this] LAll show ?thesis by simp
  qed
qed

context prf_sig
begin

lemma ap_list_forall: "ap \<rho> \<sigma> (list_forall vs Y) = list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) vs) (ap \<rho> \<sigma> Y)"
  by (induction vs) auto

lemma wtp_ap: "wtp X \<Longrightarrow> cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> wtp (ap \<rho> \<sigma> X)"
  by (rule wtpI[OF _ typing_ap_wtp]) (auto simp: closed_def dest: wtpD(1))

text \<open>
  The proof of a premise \<open>A\<close> of the rule (a closed proposition) from a hypothesis \<open>k\<close> that is
  convertible to the instance of the flattened premise:
\<close>

theorem aflatten_params_proof_ok:
  assumes \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and wA: "wtp A"
    and fA: "\<And>A. fA A = None \<or> fA A = Some A" and fT: "\<And>T. fT T = None \<or> fT T = Some T"
    and fl: "ok (flatten_params vl n A) A'" and wA': "wtp A'"
    and vl: "\<And>xs. length (vl xs) = length xs"
    and k: "k < length Hs" and ck: "closed (Hs ! k)" and wk: "e \<turnstile> Hs ! k : propT"
    and wHs: "\<forall>h\<in>set Hs. e \<turnstile> h : propT"
    and eA': "Hs ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> A'"
  shows "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> (aflatten_params_proof fA fT 0 0 n (A, integer_of_nat k))) (ap \<rho> \<sigma> A)"
proof -
  obtain p C where ls: "lsplit A = (p, C)" by (cases "lsplit A")
  from lsplit_ok[OF ls] have A: "A = lift_pre p C" and lo: "\<forall>it\<in>set p. litem_ok it" and at: "atomic C"
    by auto
  have ok: "items_ok p" using typing_lift_pre_items[OF lo wtpD(2)[OF wA[unfolded A]]] by simp
  let ?p = "map (ap_item \<rho> \<sigma>) p"
  let ?J = "ilength (ptys p)"
  define vars where "vars = zip (vl (map fst (pparams p))) (map snd (pparams p))"
  have "length (pparams p) = length (ptys p)" by (metis length_map map_snd_pparams)
  then have sv: "map snd vars = ptys p" using vl[of "map fst (pparams p)"] by (simp add: vars_def map_snd_pparams)
  have lv: "ilength vars = ?J" using arg_cong[OF sv, of length] by (simp add: ilength_eq)
  from fl obtain A'' where r: "ok (remove_params (ilength vars) n A) A''" and A': "A' = list_forall vars A''"
    by (auto simp: flatten_params_def Let_def strip_params_lift_pre[OF ok at] A vars_def)
  have nle: "n \<le> ilength (lhyps p)" using remove_params_n_le[OF ok at lv[symmetric]] r by (simp add: A)
  have A'': "A'' = list_implies (rmhyps ?J n p) C"
    using r remove_params_lift_pre[OF ok at HOL.refl nle] by (simp add: A lv)
  have apA: "ap \<rho> \<sigma> A = lift_pre ?p (ap \<rho> \<sigma> C)" by (simp add: A ap_lift_pre_items[OF ok])
  let ?vs = "map (\<lambda>(a, T). (a, tsubst \<rho> T)) vars"
  have apA': "ap \<rho> \<sigma> A' = list_forall ?vs (list_implies (rmhyps (ilength (ptys ?p)) n ?p) (ap \<rho> \<sigma> C))"
    by (simp add: A' A'' ap_list_forall ap_list_implies rmhyps_ap_item[OF \<sigma>])
  have svs: "map snd ?vs = ptys ?p"
  proof -
    have "map snd ?vs = map (tsubst \<rho>) (map snd vars)" by (induction vars) auto
    then show ?thesis using sv by simp
  qed
  have tA: "e \<turnstile> lift_pre ?p (ap \<rho> \<sigma> C) : propT" using typing_ap_wtp[OF wA \<rho> \<sigma>] apA by simp
  have "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> (aflatten_params_proof fA fT 0 0 n (lift_pre p C, integer_of_nat k)))
      (lift_pre ?p (ap \<rho> \<sigma> C))"
  proof (rule fpp_gen[OF at \<sigma> fA fT ok tA wHs])
    have "prf_ok ax H (pushes e (ptys ?p)) (rev (lhyps ?p) @ map (incr_bv (ilength (ptys ?p)) 0) Hs)
        (leafprf (ilength (lhyps ?p)) (ilength (ptys ?p)) n (integer_of_nat k)) (ap \<rho> \<sigma> C)"
    proof (rule fpp_leaf[OF items_ok_ap_item[OF ok] tA svs k ck wk])
      show "wtp (list_forall ?vs (list_implies (rmhyps (ilength (ptys ?p)) n ?p) (ap \<rho> \<sigma> C)))"
        using wtp_ap[OF wA' \<rho> \<sigma>] apA' by simp
      show "Hs ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> list_forall ?vs (list_implies (rmhyps (ilength (ptys ?p)) n ?p) (ap \<rho> \<sigma> C))"
        using eA' apA' by simp
    qed
    then show "prf_ok ax H (pushes e (map (tsubst \<rho>) (ptys p))) (rev (lhyps ?p) @ map (incr_bv ?J 0) Hs)
        (leafprf (0 + ilength (lhyps p)) (0 + ?J) n (integer_of_nat k)) (ap \<rho> \<sigma> C)"
      by (simp add: ilength_eq)
  qed
  with apA show ?thesis by (simp add: A)
qed

lemma prf_ap_aflatten_None:
  "prf_ap \<rho> \<sigma> (aflatten_params_proof (\<lambda>_. None) (\<lambda>_. None) i j n x) = aflatten_params_proof (\<lambda>_. None) (\<lambda>_. None) i j n x"
proof -
  have a: "prf_ap \<rho> \<sigma> (AbsP a None q) = AbsP a None (prf_ap \<rho> \<sigma> q)"
    "prf_ap \<rho> \<sigma> (Abst a None q) = Abst a None (prf_ap \<rho> \<sigma> q)" for a q
    by (simp_all add: prf_ap_def)
  show ?thesis
    by (induction "\<lambda>_ :: pterm. None :: pterm option" "\<lambda>_ :: ptyp. None :: ptyp option" i j n x
        rule: aflatten_params_proof.induct)
      (simp_all add: a leafprf_def[symmetric] prf_ap_leafprf)
qed

corollary flatten_params_proof_ok:
  assumes "cinst \<rho>" "gsubst \<sigma>" "wtp A" "ok (flatten_params vl n A) A'" "wtp A'"
    "\<And>xs. length (vl xs) = length xs" "k < length Hs" "closed (Hs ! k)" "e \<turnstile> Hs ! k : propT"
    "\<forall>h\<in>set Hs. e \<turnstile> h : propT" "Hs ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> A'"
  shows "prf_ok ax H e Hs (flatten_params_proof 0 0 n (A, integer_of_nat k)) (ap \<rho> \<sigma> A)"
  using aflatten_params_proof_ok[OF assms(1-3) _ _ assms(4-), of "\<lambda>_. None" "\<lambda>_. None"]
  by (simp add: flatten_params_proof_aflatten prf_ap_aflatten_None)

end


subsection \<open>Proofs by assumption\<close>

text \<open>
  The proof by assumption with annotations \<open>fA\<close> of the assumptions and \<open>fT\<close> of the
  parameters, as in \<open>ZTerm.mk_asm_prf\<close> (none in \<open>Proofterm.mk_asm_prf\<close>):
\<close>

fun aimp_prf :: "(pterm \<Rightarrow> pterm option) \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "aimp_prf fA (Const c U $ A $ B) i m =
    (if m = 0 then PBound i
     else if c = STR ''Pure.imp'' then AbsP (STR ''H'') (fA A) (aimp_prf fA B (i + 1) (m - 1))
     else PBound i)"
| "aimp_prf fA _ i m = PBound i"

fun aall_prf :: "(pterm \<Rightarrow> pterm option) \<Rightarrow> (ptyp \<Rightarrow> ptyp option) \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> prf" where
  "aall_prf fA fT i m (Const c U $ Abs a T t) =
    (if c = STR ''Pure.all'' then Abst a (fT T) (aall_prf fA fT i m t)
     else aimp_prf fA (Const c U $ Abs a T t) (- i) m)"
| "aall_prf fA fT i m t = aimp_prf fA t (- i) m"

lemma mk_asm_prf_aall: "mk_asm_prf C i m = aall_prf (\<lambda>_. None) (\<lambda>_. None) i m C"
proof -
  have "imp_prf A i m = aimp_prf (\<lambda>_. None) A i m" for A i m
    by (induction A i m rule: imp_prf.induct) simp_all
  then have "all_prf i m C = aall_prf (\<lambda>_. None) (\<lambda>_. None) i m C"
    by (induction i m C rule: all_prf.induct) simp_all
  then show ?thesis by (simp add: mk_asm_prf_def)
qed

lemma all_prf_list_forall:
  "dest_all X = None \<Longrightarrow> aall_prf fA fT i m (list_forall qs X) = foldr (\<lambda>(a, T) p. Abst a (fT T) p) qs (aimp_prf fA X (- i) m)"
proof (induction qs)
  case Nil
  then show ?case by (cases "(fA, fT, i, m, X)" rule: aall_prf.cases) (auto split: if_splits)
next
  case (Cons q qs)
  then show ?case by (cases q) (simp add: all_const_def)
qed

lemma imp_prf_list_implies:
  "ilength as \<le> m \<Longrightarrow> (ilength as < m \<longrightarrow> dest_imp B = None) \<Longrightarrow>
    aimp_prf fA (list_implies as B) i m = foldr (\<lambda>A p. AbsP (STR ''H'') (fA A) p) as (PBound (i + ilength as))"
proof (induction as arbitrary: i m)
  case Nil
  then show ?case
    by (cases "(fA, B, i, m)" rule: aimp_prf.cases) (auto split: if_splits)
next
  case (Cons a as)
  have m: "m \<noteq> 0"
  proof
    assume "m = 0"
    with Cons.prems(1) ilength_nonneg[of as] show False by simp
  qed
  have "aimp_prf fA (list_implies as B) (i + 1) (m - 1) = foldr (\<lambda>A p. AbsP (STR ''H'') (fA A) p) as (PBound (i + 1 + ilength as))"
    by (rule Cons.IH) (use Cons.prems in simp_all)
  with m show ?case by (simp add: implies_def algebra_simps)
qed

context prf_sig
begin

lemma strip_assums_all_list_forall:
  "strip_assums_all ps t = (ps', t') \<Longrightarrow> e \<turnstile> t : propT \<Longrightarrow>
    \<exists>qs. t = list_forall qs t' \<and> ps' = rev qs @ ps \<and> dest_all t' = None \<and>
      pushes e (map snd qs) \<turnstile> t' : propT \<and> (\<forall>T\<in>set (map snd qs). cert_typ alg ar T)"
proof (induction ps t arbitrary: e rule: strip_assums_all.induct)
  case (1 ps t)
  show ?case
  proof (cases "dest_all t")
    case None
    with "1.prems" show ?thesis by (subst (asm) strip_assums_all.simps) auto
  next
    case (Some x)
    then obtain a T b where d: "dest_all t = Some (a, T, b)" by (cases x) auto
    note ty = typing_dest_all[OF "1.prems"(2) d]
    from "1.prems"(1) d have "strip_assums_all ((a, T) # ps) b = (ps', t')"
      by (subst (asm) strip_assums_all.simps) simp
    from "1.IH"[OF d HOL.refl HOL.refl this ty(5)] obtain qs where
      "b = list_forall qs t'" "ps' = rev qs @ (a, T) # ps" "dest_all t' = None"
      "pushes (e\<langle>0:T\<rangle>) (map snd qs) \<turnstile> t' : propT" "\<forall>T\<in>set (map snd qs). cert_typ alg ar T"
      by blast
    with ty(1,4) show ?thesis by (intro exI[of _ "(a, T) # qs"]) simp
  qed
qed

lemma strip_assums_imp_list_implies:
  "strip_assums_imp m Hs B = (Hs', B') \<Longrightarrow> e \<turnstile> B : propT \<Longrightarrow> 0 \<le> m \<Longrightarrow>
    \<exists>as. B = list_implies as B' \<and> Hs' = rev as @ Hs \<and> ilength as \<le> m \<and>
      (ilength as < m \<longrightarrow> dest_imp B' = None) \<and> (\<forall>a\<in>set as. e \<turnstile> a : propT) \<and> e \<turnstile> B' : propT"
proof (induction m Hs B arbitrary: Hs' B' rule: strip_assums_imp.induct)
  case (1 m Hs B)
  show ?case
  proof (cases "m = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_assums_imp.simps) auto
  next
    case False
    show ?thesis
    proof (cases "dest_imp B")
      case None
      with "1.prems" False show ?thesis by (subst (asm) strip_assums_imp.simps) auto
    next
      case (Some x)
      then obtain A C where d: "dest_imp B = Some (A, C)" by (cases x) auto
      note ty = typing_dest_imp[OF "1.prems"(2) d]
      from "1.prems"(1) d False have st: "strip_assums_imp (m - 1) (A # Hs) C = (Hs', B')"
        by (subst (asm) strip_assums_imp.simps) simp
      have m1: "0 \<le> m - 1" using "1.prems"(3) False by (simp add: less_eq_integer.rep_eq integer_eq_iff)
      from "1.IH"[OF False d HOL.refl st ty(5) m1] obtain as where
        "C = list_implies as B'" "Hs' = rev as @ A # Hs" "ilength as \<le> m - 1"
        "ilength as < m - 1 \<longrightarrow> dest_imp B' = None" "\<forall>a\<in>set as. e \<turnstile> a : propT" "e \<turnstile> B' : propT"
        by auto
      with ty(1,4) show ?thesis by (intro exI[of _ "A # as"]) (auto simp: algebra_simps)
    qed
  qed
qed

lemma typing_list_forall_body: "e \<turnstile> list_forall qs X : propT \<Longrightarrow> pushes e (map snd qs) \<turnstile> X : propT"
proof (induction qs arbitrary: e)
  case (Cons q qs)
  then show ?case by (cases q) (auto simp: all_const_def)
qed simp

lemma prf_ok_abst_chain:
  "prf_ok ax H (pushes e (map (tsubst \<rho>) (map snd qs))) (map (incr_bv (ilength qs) 0) Hs) q X \<Longrightarrow>
    \<forall>(a, T)\<in>set qs. cert_typ alg ar (tsubst \<rho> T) \<and> tann_ok (g T) (tsubst \<rho> T) \<Longrightarrow>
    prf_ok ax H e Hs (foldr (\<lambda>(a, T) p. Abst a (g T) p) qs q) (list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) qs) X)"
proof (induction qs arbitrary: e Hs)
  case (Cons b qs)
  obtain a T where b: "b = (a, T)" by (cases b)
  have eq: "map (incr_bv (ilength qs) 0) (map (incr_bv 1 0) Hs) = map (incr_bv (ilength qs + 1) 0) Hs"
    using incr_bv_incr_bv[of "ilength qs" 1 0] ilength_nonneg[of qs] by simp
  have "prf_ok ax H (pushes (e\<langle>0:tsubst \<rho> T\<rangle>) (map (tsubst \<rho>) (map snd qs)))
      (map (incr_bv (ilength qs) 0) (map (incr_bv 1 0) Hs)) q X"
    using Cons.prems(1) unfolding eq by (simp add: b algebra_simps)
  then have "prf_ok ax H (e\<langle>0:tsubst \<rho> T\<rangle>) (map (incr_bv 1 0) Hs) (foldr (\<lambda>(a, T) p. Abst a (g T) p) qs q)
      (list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) qs) X)"
    by (rule Cons.IH) (use Cons.prems(2) in \<open>simp add: b\<close>)
  then show ?case using Cons.prems(2) by (simp add: b prf_ok.Abst)
qed (simp add: map_idI)

text \<open>
  \<^const>\<open>mk_asm_prf\<close> proves the premise of elim-resolution if its assumption \<open>n\<close> unifies with its
  conclusion below its parameters:
\<close>

theorem amk_asm_prf_ok:
  assumes \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and wA: "wtp A1"
    and fA: "\<And>A. fA A = None \<or> fA A = Some A" and fT: "\<And>T. fT T = None \<or> fT T = Some T"
    and apb: "assum_problems m A1 = (params, asms, concl)" and m: "0 \<le> m"
    and n: "1 \<le> n" "n \<le> ilength asms"
    and cv: "ap \<rho> \<sigma> (rlist_abs params (asms ! (nat_of_integer n - 1))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs params concl)"
  shows "prf_ok ax H e Hs (prf_ap \<rho> \<sigma> (aall_prf fA fT n m A1)) (ap \<rho> \<sigma> A1)"
proof -
  obtain A' Hs0 where s1: "strip_assums_all [] A1 = (params, A')" and s2: "strip_assums_imp m [] A' = (Hs0, concl)"
    and asms: "asms = rev Hs0"
    using apb by (auto simp: assum_problems_def split: prod.splits)
  let ?e0 = "\<lambda>_::integer. propT"
  from strip_assums_all_list_forall[OF s1 wtpD(2)[OF wA, of ?e0]] obtain qs where
    A1: "A1 = list_forall qs A'" and ps: "params = rev qs" and da: "dest_all A' = None"
    and tA': "pushes ?e0 (map snd qs) \<turnstile> A' : propT" and cq: "\<forall>T\<in>set (map snd qs). cert_typ alg ar T"
    by auto
  from strip_assums_imp_list_implies[OF s2 tA' m] obtain as where
    A': "A' = list_implies as concl" and Hs0: "Hs0 = rev as" and la: "ilength as \<le> m"
    and di: "ilength as < m \<longrightarrow> dest_imp concl = None" and tas: "\<forall>a\<in>set as. pushes ?e0 (map snd qs) \<turnstile> a : propT"
    and tc: "pushes ?e0 (map snd qs) \<turnstile> concl : propT"
    by auto
  have asms': "asms = as" using asms Hs0 by simp
  let ?qs = "map (\<lambda>(a, T). (a, tsubst \<rho> T)) qs"
  let ?E = "pushes e (map snd ?qs)"
  have msq: "map snd ?qs = map (tsubst \<rho>) (map snd qs)" by (induction qs) auto
  have peq: "aall_prf fA fT n m A1 = foldr (\<lambda>(a, T) p. Abst a (fT T) p) qs
      (foldr (\<lambda>A p. AbsP (STR ''H'') (fA A) p) as (PBound (- n + ilength as)))"
    by (simp only: A1 all_prf_list_forall[OF da]) (simp add: A' imp_prf_list_implies[OF la di])
  have apA: "ap \<rho> \<sigma> A1 = list_forall ?qs (list_implies (map (ap \<rho> \<sigma>) as) (ap \<rho> \<sigma> concl))"
    by (simp add: A1 A' ap_list_forall ap_list_implies)
  have tapA: "e \<turnstile> ap \<rho> \<sigma> A1 : propT" by (rule typing_ap_wtp[OF wA \<rho> \<sigma>])
  have tb: "?E \<turnstile> list_implies (map (ap \<rho> \<sigma>) as) (ap \<rho> \<sigma> concl) : propT"
    using typing_list_forall_body[OF tapA[unfolded apA]] .
  have tas': "\<forall>a\<in>set (map (ap \<rho> \<sigma>) as). ?E \<turnstile> a : propT" and tc': "?E \<turnstile> ap \<rho> \<sigma> concl : propT"
    using typing_list_impliesD[OF tb] by simp_all
  have cq': "\<forall>T\<in>snd ` set ?qs. cert_typ alg ar T"
    using cq cinstD(2)[OF \<rho>] by (auto simp: cert_typ_tsubst)
  text \<open>The assumption \<open>n\<close> converts to the conclusion below the parameters.\<close>
  let ?k = "nat_of_integer n - 1"
  have k: "?k < length as" using n by (simp add: asms' ilength_eq integer_reps integer_of_nat.rep_eq)
  have rl: "ap \<rho> \<sigma> (rlist_abs params X) = abs_list ?qs (ap \<rho> \<sigma> X)" for X
    by (simp add: ps rlist_abs_abs_list ap_abs_list)
  have tk: "?E \<turnstile> ap \<rho> \<sigma> (as ! ?k) : propT" using tas' k by simp
  have cvk: "ap \<rho> \<sigma> (as ! ?k) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> concl"
  proof (rule conv_abs_list_inv)
    show "e \<turnstile> abs_list ?qs (ap \<rho> \<sigma> (as ! ?k)) : map snd ?qs \<Rrightarrow> propT"
      using typing_abs_list[OF tk cq'] .
    show "e \<turnstile> abs_list ?qs (ap \<rho> \<sigma> concl) : map snd ?qs \<Rrightarrow> propT"
      using typing_abs_list[OF tc' cq'] .
    show "abs_list ?qs (ap \<rho> \<sigma> (as ! ?k)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?qs (ap \<rho> \<sigma> concl)"
      using cv by (simp add: rl asms')
  qed
  let ?Hs = "map (incr_bv (ilength ?qs) 0) Hs"
  have idx: "nat_of_integer (- n + ilength as) = length as - Suc ?k"
    using n by (simp add: asms' ilength_eq integer_reps integer_of_nat.rep_eq nat_diff_distrib)
  have j: "length as - Suc ?k < length as" using k by linarith
  have nth: "(rev (map (ap \<rho> \<sigma>) as) @ ?Hs) ! nat_of_integer (- n + ilength as) = ap \<rho> \<sigma> (as ! ?k)"
    unfolding idx using k j by (simp add: nth_append rev_nth)
  have b0: "0 \<le> - n + ilength as" using n by (simp add: asms')
  have "prf_ok ax H ?E (rev (map (ap \<rho> \<sigma>) as) @ ?Hs) (PBound (- n + ilength as))
      ((rev (map (ap \<rho> \<sigma>) as) @ ?Hs) ! nat_of_integer (- n + ilength as))"
    by (rule prf_ok.PBound[OF b0]) (use idx j tk nth in simp_all)
  then have "prf_ok ax H ?E (rev (map (ap \<rho> \<sigma>) as) @ ?Hs) (PBound (- n + ilength as)) (ap \<rho> \<sigma> (as ! ?k))"
    by (simp only: nth)
  then have pb: "prf_ok ax H ?E (rev (map (ap \<rho> \<sigma>) as) @ ?Hs) (PBound (- n + ilength as)) (ap \<rho> \<sigma> concl)"
    using cvk tc' by (rule prf_ok.conv)
  let ?ts = "map (\<lambda>A. map_option (ap \<rho> \<sigma>) (fA A)) as"
  have "list_all2 ann_ok ?ts (map (ap \<rho> \<sigma>) as)"
  proof (rule list_all2_all_nthI)
    fix l assume "l < length ?ts"
    then show "ann_ok (?ts ! l) (map (ap \<rho> \<sigma>) as ! l)" using fA[of "as ! l"] by auto
  qed simp
  from prf_ok_foldr_AbsP[OF pb tas' this]
  have pA: "prf_ok ax H ?E ?Hs (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ?ts (PBound (- n + ilength as)))
      (list_implies (map (ap \<rho> \<sigma>) as) (ap \<rho> \<sigma> concl))" .
  have "prf_ok ax H e Hs (foldr (\<lambda>(a, T) p. Abst a (map_option (tsubst \<rho>) (fT T)) p) qs
      (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ?ts (PBound (- n + ilength as))))
      (list_forall ?qs (list_implies (map (ap \<rho> \<sigma>) as) (ap \<rho> \<sigma> concl)))"
  proof (rule prf_ok_abst_chain)
    show "prf_ok ax H (pushes e (map (tsubst \<rho>) (map snd qs))) (map (incr_bv (ilength qs) 0) Hs)
        (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ?ts (PBound (- n + ilength as)))
        (list_implies (map (ap \<rho> \<sigma>) as) (ap \<rho> \<sigma> concl))"
      using pA[unfolded msq] by (simp add: ilength_eq)
    have "tann_ok (map_option (tsubst \<rho>) (fT T)) (tsubst \<rho> T)" for T using fT[of T] by auto
    then show "\<forall>(a, T)\<in>set qs. cert_typ alg ar (tsubst \<rho> T) \<and> tann_ok (map_option (tsubst \<rho>) (fT T)) (tsubst \<rho> T)"
      using cq cinstD(2)[OF \<rho>] by (fastforce simp: cert_typ_tsubst)
  qed
  moreover have "prf_ap \<rho> \<sigma> (foldr (\<lambda>(a, T) p. Abst a (fT T) p) qs (foldr (\<lambda>A p. AbsP (STR ''H'') (fA A) p) as q)) =
      foldr (\<lambda>(a, T) p. Abst a (map_option (tsubst \<rho>) (fT T)) p) qs (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ?ts (prf_ap \<rho> \<sigma> q))"
    for q
  proof -
    have "prf_ap \<rho> \<sigma> (foldr (\<lambda>A p. AbsP (STR ''H'') (fA A) p) as q) = foldr (\<lambda>t p. AbsP (STR ''H'') t p) ?ts (prf_ap \<rho> \<sigma> q)"
      by (induction as) (simp_all add: prf_ap_def)
    then show ?thesis by (induction qs) (auto simp: prf_ap_def)
  qed
  moreover have "prf_ap \<rho> \<sigma> (PBound (- n + ilength as)) = PBound (- n + ilength as)" by (simp add: prf_ap_def)
  ultimately show ?thesis by (simp add: peq apA)
qed

corollary mk_asm_prf_ok:
  assumes "cinst \<rho>" "gsubst \<sigma>" "wtp A1" "assum_problems m A1 = (params, asms, concl)" "0 \<le> m"
    "1 \<le> n" "n \<le> ilength asms"
    "ap \<rho> \<sigma> (rlist_abs params (asms ! (nat_of_integer n - 1))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs params concl)"
  shows "prf_ok ax H e Hs (mk_asm_prf A1 n m) (ap \<rho> \<sigma> A1)"
proof -
  have "prf_ap \<rho> \<sigma> (aall_prf (\<lambda>_. None) (\<lambda>_. None) n m A1) = aall_prf (\<lambda>_. None) (\<lambda>_. None) n m A1"
  proof -
    have "prf_ap \<rho> \<sigma> (aimp_prf (\<lambda>_. None) A i m') = aimp_prf (\<lambda>_. None) A i m'" for A i m'
      by (induction "\<lambda>_ :: pterm. None :: pterm option" A i m' rule: aimp_prf.induct) (simp_all add: prf_ap_def)
    then show ?thesis
      by (induction "\<lambda>_ :: pterm. None :: pterm option" "\<lambda>_ :: ptyp. None :: ptyp option" n m A1 rule: aall_prf.induct)
        (simp_all add: prf_ap_def)
  qed
  with amk_asm_prf_ok[OF assms(1-3) _ _ assms(4-), of "\<lambda>_. None" "\<lambda>_. None"] show ?thesis
    by (simp add: mk_asm_prf_aall)
qed

end

end
