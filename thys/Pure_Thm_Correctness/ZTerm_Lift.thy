section \<open>Tight proofs and their lifting\<close>

theory ZTerm_Lift
  imports ZTerm_Decode
begin

text \<open>
  A tight proof stands for the classic proof with the decoded terms and types as annotations
  (\<open>zprf_tr\<close>); the judgment on tight proofs is the classic judgment on this
  translation. Proof constants (\<open>ZConstp\<close>, with their instantiations) do not occur in the
  proofs of the theorems built here.
\<close>

context csig
begin

subsection \<open>Translation to classic proofs\<close>

fun zprf_tr :: "zproof \<Rightarrow> prf" where
  "zprf_tr ZNop = MinProof"
| "zprf_tr (ZConstp c) = MinProof"
| "zprf_tr (ZBoundp i) = PBound i"
| "zprf_tr (ZAbst a T p) = Abst a (Some (typ_of T)) (zprf_tr p)"
| "zprf_tr (ZAbsp a t p) = AbsP a (Some (zdec t)) (zprf_tr p)"
| "zprf_tr (ZAppt p t) = PAppt (zprf_tr p) (Some (zdec t))"
| "zprf_tr (ZAppp p q) = PAppp (zprf_tr p) (zprf_tr q)"
| "zprf_tr (ZHyp t) = Hyp (zdec t)"
| "zprf_tr (OFCLASSp T c) = PClass (typ_of T) c"

fun zconst_free :: "zproof \<Rightarrow> bool" where
  "zconst_free (ZConstp c) = False"
| "zconst_free (ZAbst a T p) = zconst_free p"
| "zconst_free (ZAbsp a t p) = zconst_free p"
| "zconst_free (ZAppt p t) = zconst_free p"
| "zconst_free (ZAppp p q) = (zconst_free p \<and> zconst_free q)"
| "zconst_free _ = True"

text \<open>Tight terms and types whose schematic (type) variables have non-negative indices.\<close>

definition ztyp_ok :: "ztyp \<Rightarrow> bool" where
  "ztyp_ok T \<longleftrightarrow> (\<forall>(v, S)\<in>tvars (typ_of T). 0 \<le> snd v)"

fun zterm_ok :: "zterm \<Rightarrow> bool" where
  "zterm_ok (ZVar xi T) \<longleftrightarrow> (0 \<le> snd xi \<or> snd xi = -1) \<and> ztyp_ok T"
| "zterm_ok (ZBound i) \<longleftrightarrow> True"
| "zterm_ok (ZConst0 c) \<longleftrightarrow> True"
| "zterm_ok (ZConst1 c T) \<longleftrightarrow> ztyp_ok T"
| "zterm_ok (ZConst c Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. ztyp_ok T)"
| "zterm_ok (ZAbs a T t) \<longleftrightarrow> ztyp_ok T \<and> zterm_ok t"
| "zterm_ok (ZApp t u) \<longleftrightarrow> zterm_ok t \<and> zterm_ok u"
| "zterm_ok (ZOfclass T c) \<longleftrightarrow> ztyp_ok T"

text \<open>The terms and types of a tight proof (not those of hypotheses and class proofs, which lifting keeps).\<close>

fun zprf_all :: "(zterm \<Rightarrow> bool) \<Rightarrow> (ztyp \<Rightarrow> bool) \<Rightarrow> zproof \<Rightarrow> bool" where
  "zprf_all P Q (ZAbst a T p) \<longleftrightarrow> Q T \<and> zprf_all P Q p"
| "zprf_all P Q (ZAbsp a t p) \<longleftrightarrow> P t \<and> zprf_all P Q p"
| "zprf_all P Q (ZAppt p t) \<longleftrightarrow> zprf_all P Q p \<and> P t"
| "zprf_all P Q (ZAppp p q) \<longleftrightarrow> zprf_all P Q p \<and> zprf_all P Q q"
| "zprf_all P Q (OFCLASSp T c) \<longleftrightarrow> Q T"
| "zprf_all P Q _ \<longleftrightarrow> True"


subsection \<open>Decoding and lifting\<close>

lemma incr_tvar_tsubst: "incr_tvar inc (tsubst \<sigma> U) = tsubst (\<lambda>v S. incr_tvar inc (\<sigma> v S)) U"
  by (induction U) simp_all

lemma incr_tvar_dummyT[simp]: "incr_tvar inc dummyT = dummyT"
  by (simp add: dummyT_def)

lemma map_of_zip_map_snd: "map_of (zip xs (map f ys)) x = map_option f (map_of (zip xs ys) x)"
  by (induction xs arbitrary: ys) (auto simp: zip_Cons1 split: list.splits)

lemma zconst_typ_incr: "zconst_typ c (map (incr_tvar inc) Us) = incr_tvar inc (zconst_typ c Us)"
proof -
  have i: "incr_tvar inc imp_type = imp_type" by (simp add: imp_type_def)
  show ?thesis
    by (cases "ctab c")
      (auto simp: zconst_typ_def i propT_def incr_tvar_tsubst map_of_zip_map_snd
        split: list.splits option.splits intro!: tsubst_cong)
qed

lemma typ_of_zincr_tvar:
  assumes "ztyp_ok T" "0 \<le> inc"
  shows "typ_of (zincr_tvar inc T) = incr_tvar inc (typ_of T)"
proof (cases "inc = 0")
  case True
  then show ?thesis by (simp add: zincr_tvar_def)
next
  case False
  have "typ_of (zsubst_type (\<lambda>((a, i), S). if 0 \<le> i then Some (ZTVar (a, i + inc) S) else None) T) =
      incr_tvar inc (typ_of T)" if "ztyp_ok T" for T
    using that
  proof (induction T)
    case (ZTVar v S)
    then show ?case using assms(2) by (cases v) (auto simp: ztyp_ok_def)
  qed (auto simp: ztyp_ok_def)
  with assms False show ?thesis by (simp add: zincr_tvar_def)
qed

lemma integer_nonneg_ne_m1: "0 \<le> (x :: integer) \<Longrightarrow> x \<noteq> -1"
  by transfer simp

lemma zdec_zcombound: "zdec (zcombound t n k) = combound (zdec t) n k"
  by (induction t n k rule: zcombound.induct) simp_all

lemma typ_of_ZFuns: "typ_of (ZFuns Ts T) = foldr fun_type (map typ_of Ts) (typ_of T)"
  by (induction Ts) (simp_all add: ZFuns_def)

lemma ztyp_ok_simps:
  "ztyp_ok (ZFun T U) \<longleftrightarrow> ztyp_ok T \<and> ztyp_ok U" "ztyp_ok (ZType1 a T) \<longleftrightarrow> ztyp_ok T"
  "ztyp_ok (ZType a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. ztyp_ok T)"
  by (auto simp: ztyp_ok_def)

lemma zdec_zlift_term:
  assumes "zterm_ok t" "\<forall>T\<in>set Ts. ztyp_ok T" "0 \<le> inc"
  shows "zdec (zlift_term inc Ts lev t) = incr_idx (map typ_of Ts) inc lev (zdec t)"
  using assms(1)
proof (induction t arbitrary: lev)
  case (ZVar xi T)
  obtain x i where xi: "xi = (x, i)" by (cases xi)
  have T: "typ_of (zincr_tvar inc T) = incr_tvar inc (typ_of T)"
    using ZVar assms(3) by (intro typ_of_zincr_tvar) simp_all
  show ?case
  proof (cases "0 \<le> i")
    case True
    have "i + inc \<noteq> -1" using True assms(3) by (intro integer_nonneg_ne_m1 add_nonneg_nonneg)
    then show ?thesis using True T by (simp add: xi zdec_zcombound typ_of_ZFuns)
  next
    case False
    with ZVar have "i = -1" by (simp add: xi)
    then show ?thesis using T by (simp add: xi)
  qed
next
  case (ZConst1 c T)
  then have "typ_of (zincr_tvar inc T) = incr_tvar inc (typ_of T)" using assms(3) by (intro typ_of_zincr_tvar) simp_all
  then show ?case using zconst_typ_incr[of c inc "[typ_of T]"] by simp
next
  case (ZConst c Us)
  then have e: "map (\<lambda>x. typ_of (zincr_tvar inc x)) Us = map (\<lambda>x. incr_tvar inc (typ_of x)) Us"
    using assms(3) by (auto simp: map_eq_conv intro: typ_of_zincr_tvar)
  have "zconst_typ c (map typ_of (map (zincr_tvar inc) Us)) = incr_tvar inc (zconst_typ c (map typ_of Us))"
    using zconst_typ_incr[of c inc "map typ_of Us"] by (simp only: map_map comp_def e)
  then show ?case by simp
next
  case (ZAbs a T t)
  then show ?case using assms(3) by (simp add: typ_of_zincr_tvar)
next
  case (ZOfclass T c)
  then show ?case using assms(3) by (simp add: typ_of_zincr_tvar of_class_def propT_def)
qed (simp_all add: zconst_typ_incr[of _ _ "[]", simplified])

lemma zdec_zlift_term':
  assumes "zterm_ok t" "\<forall>T\<in>set Ts. ztyp_ok T" "0 \<le> inc"
  shows "zdec (zlift_term' inc Ts lev t) = incr_idx (map typ_of Ts) inc lev (zdec t)"
  using zdec_zlift_term[OF assms] by (auto simp: zlift_term'_def incr_idx_0)

text \<open>Lifting a tight proof without proof constants is the lifting of the classic proof.\<close>

lemma zlift_prf_tr:
  assumes "zconst_free p" "zprf_all zterm_ok ztyp_ok p" "\<forall>T\<in>set Ts. ztyp_ok T" "0 \<le> inc"
  shows "\<exists>q. zlift_prf inc Ts lev p = returnZ q \<and> zprf_tr q = lift_prf inc (map typ_of Ts) lev (zprf_tr p) \<and>
    zconst_free q"
  using assms(1,2)
proof (induction p arbitrary: lev)
  case (ZAbst a T p)
  then obtain q where "zlift_prf inc Ts (lev + 1) p = returnZ q"
    "zprf_tr q = lift_prf inc (map typ_of Ts) (lev + 1) (zprf_tr p)" "zconst_free q"
    by auto
  then show ?case using ZAbst.prems assms(4) by (simp add: typ_of_zincr_tvar)
next
  case (ZAbsp a t p)
  then obtain q where "zlift_prf inc Ts lev p = returnZ q"
    "zprf_tr q = lift_prf inc (map typ_of Ts) lev (zprf_tr p)" "zconst_free q"
    by auto
  then show ?case using ZAbsp.prems assms(3,4) by (simp add: zdec_zlift_term')
next
  case (ZAppt p t)
  then obtain q where "zlift_prf inc Ts lev p = returnZ q"
    "zprf_tr q = lift_prf inc (map typ_of Ts) lev (zprf_tr p)" "zconst_free q"
    by auto
  then show ?case using ZAppt.prems assms(3,4) by (simp add: zdec_zlift_term')
next
  case (ZAppp p1 p2)
  from ZAppp obtain q1 where "zlift_prf inc Ts lev p1 = returnZ q1"
    "zprf_tr q1 = lift_prf inc (map typ_of Ts) lev (zprf_tr p1)" "zconst_free q1"
    by auto
  moreover from ZAppp obtain q2 where "zlift_prf inc Ts lev p2 = returnZ q2"
    "zprf_tr q2 = lift_prf inc (map typ_of Ts) lev (zprf_tr p2)" "zconst_free q2"
    by auto
  ultimately show ?case by simp
next
  case (OFCLASSp T c)
  then show ?case using assms(4) by (simp add: typ_of_zincr_tvar)
qed simp_all

end

context prf_wf_csig
begin

subsection \<open>Lifting with annotations\<close>

text \<open>
  \<^const>\<open>lift_prems\<close> and \<^const>\<open>lift_proof\<close> with annotations at the abstractions, as in the
  tight proofs: the assumptions and parameters of the subgoal, and the premises of the rule.
\<close>

fun lift_prems_a :: "integer \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> ptyp list \<Rightarrow> bool list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> prf" where
  "lift_prems_a inc k prf Ts bs i j (Const c U $ A $ B) =
    (if c = STR ''Pure.imp'' then AbsP (STR ''H'') (Some A) (lift_prems_a inc k prf Ts (True # bs) (i + 1) j B)
     else proof_combP (lift_prf inc (rev Ts) 0 prf)
       (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i)))"
| "lift_prems_a inc k prf Ts bs i j (Const c U $ Abs a T t) =
    (if c = STR ''Pure.all'' then Abst a (Some T) (lift_prems_a inc k prf (T # Ts) (False # bs) i (j + 1) t)
     else proof_combP (lift_prf inc (rev Ts) 0 prf)
       (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i)))"
| "lift_prems_a inc k prf Ts bs i j _ =
    proof_combP (lift_prf inc (rev Ts) 0 prf)
      (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"

definition mk_AbsPs :: "pterm list \<Rightarrow> prf \<Rightarrow> prf" where
  "mk_AbsPs As p = foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) As p"

definition lift_proof_a :: "pterm \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> prf \<Rightarrow> prf" where
  "lift_proof_a gprop inc prems prf =
    mk_AbsPs prems (lift_prems_a inc (integer_of_nat (length prems)) prf [] [] 0 0 gprop)"

lemma prf_inst_mk_AbsPs:
  "prf_inst \<rho> \<theta> lev (mk_AbsPs As p) = mk_AbsPs (map (psubst \<rho> \<theta> lev) As) (prf_inst \<rho> \<theta> lev p)"
  by (induction As) (simp_all add: mk_AbsPs_def)

lemma ann_ok_refl: "wty V Ts A T \<Longrightarrow> ann_ok (Some A) A"
  by (auto simp: wty_def intro: has_type_proper equiv_refl)

lemma prf_ok_mk_AbsPs:
  "prf_ok V H Ts (rev Ps @ Hs) q X \<Longrightarrow> \<forall>P\<in>set Ps. wty V Ts P propT \<Longrightarrow>
    prf_ok V H Ts Hs (mk_AbsPs Ps q) (list_implies Ps X)"
proof (induction Ps arbitrary: Hs)
  case (Cons P Ps)
  have "prf_ok V H Ts (P # Hs) (mk_AbsPs Ps q) (list_implies Ps X)" using Cons by simp
  then show ?case using Cons.prems(2) by (auto simp: mk_AbsPs_def intro: prf_ok.AbsP ann_ok_refl)
qed (simp add: mk_AbsPs_def)

lemma lift_prems_a_inst_leaf_gen:
  assumes leaf: "lift_Ts Ts G = Ts" "\<And>A. lift_all_aux inc Ts G A = incr_indexes (rev Ts) inc A"
      "lift_prems_a inc k pf Ts bs i j G = proof_combP (lift_prf inc (rev Ts) 0 pf)
        (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"
  shows "wty V2 Ts G propT \<Longrightarrow>
    i = integer_of_nat (length (filter id bs)) \<Longrightarrow> length Ts = length (filter Not bs) \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (spine bs i j (i + k - 1 - integer_of_nat m))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G (As ! m)))) \<Longrightarrow>
    (\<forall>Hs'. prf_ok V3 H (map (tsubst \<rho>) (lift_Ts Ts G) @ Us) Hs'
      (prf_inst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (lift_prf inc (rev (lift_Ts Ts G)) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (incr_indexes (rev (lift_Ts Ts G)) inc (list_implies As B)))) \<Longrightarrow>
    k = integer_of_nat (length As) \<Longrightarrow>
    prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (prf_inst \<rho> \<theta> j (lift_prems_a inc k pf Ts bs i j G))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G B))"
  unfolding leaf by (rule lift_prems_inst_leaf)

lemma prf_ok_lift_prems_a_inst:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and \<theta>: "inst_typed V2 V3 Us \<rho> \<theta>"
  shows "wty V2 Ts G propT \<Longrightarrow>
    i = integer_of_nat (length (filter id bs)) \<Longrightarrow> length Ts = length (filter Not bs) \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (spine bs i j (i + k - 1 - integer_of_nat m))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G (As ! m)))) \<Longrightarrow>
    (\<forall>Hs'. prf_ok V3 H (map (tsubst \<rho>) (lift_Ts Ts G) @ Us) Hs'
      (prf_inst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (lift_prf inc (rev (lift_Ts Ts G)) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (incr_indexes (rev (lift_Ts Ts G)) inc (list_implies As B)))) \<Longrightarrow>
    k = integer_of_nat (length As) \<Longrightarrow>
    prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (prf_inst \<rho> \<theta> j (lift_prems_a inc k pf Ts bs i j G))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G B))"
proof (induction inc k pf Ts bs i j G arbitrary: Hs rule: lift_prems_a.induct)
  case (1 inc k pf Ts bs i j c U A' G')
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    note tA = has_type_imp_E[of V2 Ts U A' G' propT, OF 1(2)[unfolded wty_def True, THEN conjunct1]]
    have wA0: "wty V2 Ts A' propT" "wty V2 Ts G' propT" using 1(2) tA by (auto simp: wty_def True)
    let ?A = "psubst \<rho> \<theta> j A'"
    let ?Ts = "map (tsubst \<rho>) Ts @ Us"
    have wA: "wty V3 ?Ts ?A propT" using wty_psubst[OF wA0(1) \<theta>] 1(5) by (simp add: propT_def)
    have e: "psubst \<rho> \<theta> j (Const STR ''Pure.imp'' U) = implies"
      using tA by (simp add: implies_def propT_def)
    have "prf_ok V3 H ?Ts (?A # Hs) (prf_inst \<rho> \<theta> j (lift_prems_a inc k pf Ts (True # bs) (i + 1) j G'))
        (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' B))"
    proof (rule 1(1)[OF True])
      show "\<forall>m<length As. prf_ok V3 H ?Ts (?A # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
          (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        have "integer_of_nat (Suc m) \<le> k" using m 1(8) by (simp add: less_eq_integer.rep_eq integer_of_nat.rep_eq)
        then have c0: "0 \<le> i + k - 1 - integer_of_nat m" using 1(3) integer_of_nat_nonneg[of "length (filter id bs)"]
          by (simp only: integer_of_nat_Suc)
        have "prf_ok V3 H ?Ts (take (nat_of_integer 0) Hs @ ?A # drop (nat_of_integer 0) Hs)
            (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (psubst \<rho> \<theta> j (lift_all_aux inc Ts (Const c U $ A' $ G') (As ! m)))"
          using 1(6) m by (intro prf_ok_incr_pbv) (auto simp: integer_reps)
        then have "prf_ok V3 H ?Ts (?A # Hs) (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m)))
            (implies $ ?A $ psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))"
          using True e by (simp add: integer_reps)
        moreover have "prf_ok V3 H ?Ts (?A # Hs) (PBound 0) ?A"
          using prf_ok.PBound[of 0 "?A # Hs" V3 ?Ts H] wA by (simp add: integer_reps)
        ultimately have "prf_ok V3 H ?Ts (?A # Hs) (PAppp (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (PBound 0))
            (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))" by (rule prf_ok.PAppp)
        then show "prf_ok V3 H ?Ts (?A # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
            (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))"
          using spine_True[OF 1(3) c0, of j] by (simp add: algebra_simps)
      qed
    qed (use wA0 1(3-5) 1(7-8) True in \<open>simp_all add: integer_of_nat_Suc\<close>)
    then have "prf_ok V3 H ?Ts Hs (AbsP (STR ''H'') (Some ?A) (prf_inst \<rho> \<theta> j (lift_prems_a inc k pf Ts (True # bs) (i + 1) j G')))
        (implies $ ?A $ psubst \<rho> \<theta> j (lift_all_aux inc Ts G' B))" using wA by (auto intro!: prf_ok.AbsP ann_ok_refl)
    then show ?thesis using True e by simp
  next
    case False
    show ?thesis by (rule lift_prems_a_inst_leaf_gen[OF _ _ _ 1(2-8)]) (use False in simp_all)
  qed
next
  case (2 inc k pf Ts bs i j c U a T G')
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    note tG = has_type_all_E[of V2 Ts U a T G' propT, OF 2(2)[unfolded wty_def True, THEN conjunct1]]
    have wG: "wty V2 (T # Ts) G' propT" using 2(2) tG by (auto simp: wty_def True)
    let ?Ts = "map (tsubst \<rho>) Ts @ Us"
    let ?T = "tsubst \<rho> T"
    have e: "psubst \<rho> \<theta> j (Const STR ''Pure.all'' U) = all_const ?T"
      using tG by (simp add: all_const_def propT_def)
    have "prf_ok V3 H (map (tsubst \<rho>) (T # Ts) @ Us) (map (incr_bv 1 0) Hs)
        (prf_inst \<rho> \<theta> (j + 1) (lift_prems_a inc k pf (T # Ts) (False # bs) i (j + 1) G'))
        (psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' B))"
    proof (rule 2(1)[OF True])
      show "\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) (T # Ts) @ Us) (map (incr_bv 1 0) Hs)
          (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m))
          (psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' (As ! m)))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        let ?X = "psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' (As ! m))"
        let ?s = "spine bs i j (i + k - 1 - integer_of_nat m)"
        have sm: "prf_ok V3 H ?Ts Hs ?s (all_const ?T $ Abs a ?T ?X)"
          using 2(6) m True e by simp
        have wX: "wty V3 (?T # ?Ts) ?X propT"
          using prf_ok_wty[OF sm] by (auto simp: wty_def all_const_def dest!: has_type_all_E)
        have Hc: "\<forall>h\<in>H. \<not> loose_bvar h 0" using H by blast
        have "prf_ok V3 H (take (nat_of_integer 0) ?Ts @ ?T # drop (nat_of_integer 0) ?Ts) (map (incr_bv 1 0) Hs)
            (incr_tbv 0 ?s) (incr_bv 1 0 (all_const ?T $ Abs a ?T ?X))"
          using sm by (intro prf_ok_incr_tbv[OF Hc]) (auto simp: integer_reps)
        then have "prf_ok V3 H (?T # ?Ts) (map (incr_bv 1 0) Hs) (incr_tbv 0 ?s) (all_const ?T $ Abs a ?T (incr_bv 1 1 ?X))"
          by (simp add: integer_reps)
        then have "prf_ok V3 H (?T # ?Ts) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0)))
            (Abs a ?T (incr_bv 1 1 ?X) $ Bound 0)"
          by (rule prf_ok.PAppt) (auto simp: wty_def has_type_Bound_iff integer_reps)
        moreover have "tr (Abs a ?T (incr_bv 1 1 ?X) $ Bound 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ?X"
        proof -
          have "proper ?X" using wX by (auto simp: wty_def intro: has_type_proper)
          then have e1: "tr (Abs a ?T (incr_bv 1 1 ?X) $ Bound 0) = dB.Abs (lift (tr ?X) (Suc 0)) \<degree> BVar 0"
            by (simp add: tr_incr_bv1 integer_reps)
          have e2: "dB.Abs (lift (tr ?X) (Suc 0)) \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> tr ?X"
            using beta.beta[of "lift (tr ?X) (Suc 0)" "BVar 0"] by (simp only: subst_lift_0)
          show ?thesis unfolding e1 by (rule beta_into_equiv, rule r_into_rtranclp, rule e2)
        qed
        ultimately have "prf_ok V3 H (?T # ?Ts) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0))) ?X"
          using wX by (rule prf_ok.conv)
        then show "prf_ok V3 H (map (tsubst \<rho>) (T # Ts) @ Us) (map (incr_bv 1 0) Hs)
            (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m)) ?X"
          using spine_False[of j bs i] 2(4,5) by simp
      qed
    qed (use wG 2(3-5) 2(7-8) True in \<open>simp_all add: integer_of_nat_Suc\<close>)
    then have "prf_ok V3 H ?Ts Hs (Abst a (Some ?T) (prf_inst \<rho> \<theta> (j + 1) (lift_prems_a inc k pf (T # Ts) (False # bs) i (j + 1) G')))
        (all_const ?T $ Abs a ?T (psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' B)))"
      by (auto intro!: prf_ok.Abst[where T = "Some ?T", simplified])
    then show ?thesis using True e by simp
  next
    case False
    show ?thesis by (rule lift_prems_a_inst_leaf_gen[OF _ _ _ 2(2-8)]) (use False in simp_all)
  qed
qed (rule lift_prems_a_inst_leaf_gen; (assumption | simp))+

theorem prf_valid_lift_proof_a:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and inc: "0 \<le> inc" and P: "prf_valid_ctx alg ar V H tps pf (list_implies As B)"
    and wR: "wty V [] (list_implies As B) propT"
    and G: "wty V2 [] G propT" and V2: "lift_venv (rev (lift_Ts [] G)) inc V V2"
  shows "prf_valid_ctx alg ar V2 H (map (\<lambda>(t, u). (lift_abs inc G t, lift_abs inc G u)) tps)
    (lift_proof_a G inc (map (lift_all inc G) As) pf) (list_implies (map (lift_all inc G) As) (lift_all inc G B))"
  unfolding prf_valid_ctx_def
proof (intro allI impI)
  fix V3 Us \<rho> \<theta>
  assume ws: "ginst alg ar \<rho>" and \<theta>: "inst_typed V2 V3 Us \<rho> \<theta>"
    and sol: "\<forall>(t, u)\<in>set (map (\<lambda>(t, u). (lift_abs inc G t, lift_abs inc G u)) tps).
      tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)"
  let ?L = "lift_Ts [] G"
  let ?n = "length ?L"
  let ?Ps = "map (lift_all inc G) As"
  let ?\<rho> = "lift_tinst inc \<rho>" and ?\<theta> = "lift_sinst inc ?n \<theta>"
  let ?Ctx = "map (tsubst \<rho>) ?L @ Us"
  text \<open>The instance of the rule in the context of the parameters of the subgoal.\<close>
  have leaf0: "prf_ok V3 H ?Ctx [] (prf_inst ?\<rho> ?\<theta> 0 pf) (psubst ?\<rho> ?\<theta> 0 (list_implies As B))"
  proof (rule prf_valid_ctxD[OF P ginst_lift_tinst[OF ws]])
    show "inst_typed V V3 ?Ctx ?\<rho> ?\<theta>" using inst_typed_lift[OF \<theta> _ inc] V2 by simp
    show "tr (psubst ?\<rho> ?\<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst ?\<rho> ?\<theta> 0 u)" if "(t, u) \<in> set tps" for t u
      using sol that by (intro lift_abs_solves) auto
  qed
  have leaf: "prf_ok V3 H ?Ctx Hs' (prf_inst \<rho> \<theta> (integer_of_nat ?n) (lift_prf inc (rev ?L) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat ?n) (incr_indexes (rev ?L) inc (list_implies As B)))" for Hs'
    using prf_ok_append[OF leaf0, of Hs'] prf_inst_lift_prf[of 0 \<rho> \<theta> "rev ?L" inc pf]
      psubst_incr_idx[of 0 \<rho> \<theta> "rev ?L" inc "list_implies As B"]
    by (simp add: incr_indexes_incr_idx)
  have wA: "\<forall>A\<in>set As. wty V [] A propT" using wty_list_implies[OF wR] by simp
  have wP: "\<forall>P\<in>set ?Ps. wty V2 [] P propT"
    using wA G V2 inc by (auto simp: lift_all_def intro: wty_lift_all_aux)
  let ?Qs = "map (psubst \<rho> \<theta> 0) ?Ps"
  have "prf_ok V3 H (map (tsubst \<rho>) [] @ Us) (rev ?Qs)
      (prf_inst \<rho> \<theta> 0 (lift_prems_a inc (integer_of_nat (length As)) pf [] [] 0 0 G)) (psubst \<rho> \<theta> 0 (lift_all_aux inc [] G B))"
  proof (rule prf_ok_lift_prems_a_inst[OF H \<theta> G])
    show "\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) [] @ Us) (rev ?Qs)
        (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m)) (psubst \<rho> \<theta> 0 (lift_all_aux inc [] G (As ! m)))"
    proof (intro allI impI)
      fix m assume m: "m < length As"
      have c: "integer_of_nat (length As) - 1 - integer_of_nat m = integer_of_nat (length As - Suc m)"
        using m by (simp add: integer_eq_iff integer_of_nat.rep_eq of_nat_diff)
      have "rev ?Qs ! (length As - Suc m) = psubst \<rho> \<theta> 0 (lift_all inc G (As ! m))" using m by (simp add: rev_nth)
      moreover have "wty V3 Us (psubst \<rho> \<theta> 0 (lift_all inc G (As ! m))) propT"
        using wty_psubst[of V2 "[]" "lift_all inc G (As ! m)" propT V3 Us \<rho> \<theta>] wP m \<theta> by (simp add: propT_def)
      ultimately show "prf_ok V3 H (map (tsubst \<rho>) [] @ Us) (rev ?Qs)
          (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m)) (psubst \<rho> \<theta> 0 (lift_all_aux inc [] G (As ! m)))"
        using prf_ok.PBound[of "integer_of_nat (length As - Suc m)" "rev ?Qs" V3 Us H] m
        by (simp add: spine_def c lift_all_def)
    qed
  qed (use leaf in simp_all)
  moreover have "\<forall>Q\<in>set ?Qs. wty V3 Us Q propT"
    using wP \<theta> wty_psubst[of V2 "[]" _ propT V3 Us \<rho> \<theta>] by (auto simp: propT_def)
  ultimately have "prf_ok V3 H Us [] (mk_AbsPs ?Qs (prf_inst \<rho> \<theta> 0 (lift_prems_a inc (integer_of_nat (length As)) pf [] [] 0 0 G)))
      (list_implies ?Qs (psubst \<rho> \<theta> 0 (lift_all inc G B)))"
    by (auto simp: lift_all_def intro!: prf_ok_mk_AbsPs)
  then show "prf_ok V3 H Us [] (prf_inst \<rho> \<theta> 0 (lift_proof_a G inc ?Ps pf)) (psubst \<rho> \<theta> 0 (list_implies ?Ps (lift_all inc G B)))"
    by (simp add: lift_proof_a_def psubst_list_implies prf_inst_mk_AbsPs)
qed



subsection \<open>Tight lifting is annotated lifting\<close>

lemma zmk_app_tr:
  "(case foldr zmk_app bs (i, j, p) of (a, b, q) \<Rightarrow> (a, b, zprf_tr q)) = foldr mk_app bs (i, j, zprf_tr p)"
  by (induction bs) (auto simp: zmk_app_def mk_app_def split: prod.splits)

lemma zmk_app_tr':
  "zprf_tr (snd (snd (foldr zmk_app bs (i, j, p)))) = snd (snd (foldr mk_app bs (i, j, zprf_tr p)))"
proof -
  obtain a b q where e: "foldr zmk_app bs (i, j, p) = (a, b, q)" by (cases "foldr zmk_app bs (i, j, p)")
  then have "foldr mk_app bs (i, j, zprf_tr p) = (a, b, zprf_tr q)" using zmk_app_tr[of bs i j p] by simp
  with e show ?thesis by simp
qed

lemma ZAppps_tr: "zprf_tr (ZAppps p qs) = proof_combP (zprf_tr p) (map zprf_tr qs)"
  by (induction qs arbitrary: p) (simp_all add: ZAppps_def proof_combP_def)

lemma ZAbsps_tr: "zprf_tr (ZAbsps ts p) = mk_AbsPs (map zdec ts) (zprf_tr p)"
  by (induction ts) (simp_all add: ZAbsps_def mk_AbsPs_def)

lemma zlift_prems_leaf_tr:
  assumes "zconst_free pz" "zprf_all zterm_ok ztyp_ok pz" "\<forall>T\<in>set Tsz. ztyp_ok T" "0 \<le> inc"
  shows "\<exists>q. bindZ (zlift_prf inc (rev Tsz) 0 pz)
      (\<lambda>p. returnZ (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))) =
      returnZ q \<and>
    zprf_tr q = proof_combP (lift_prf inc (rev (map typ_of Tsz)) 0 (zprf_tr pz))
      (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"
proof -
  from zlift_prf_tr[OF assms(1,2) _ assms(4), of "rev Tsz" 0] assms(3) obtain q where
    "zlift_prf inc (rev Tsz) 0 pz = returnZ q" "zprf_tr q = lift_prf inc (map typ_of (rev Tsz)) 0 (zprf_tr pz)"
    by auto
  then show ?thesis by (simp add: ZAppps_tr zmk_app_tr' comp_def rev_map)
qed

lemma zlift_prems_tr:
  "ta = ztargs \<Longrightarrow> zconst_free pz \<Longrightarrow> zprf_all zterm_ok ztyp_ok pz \<Longrightarrow> 0 \<le> inc \<Longrightarrow>
    wty V (map typ_of Tsz) G propT \<Longrightarrow> \<forall>U\<in>tys G. \<forall>(v, S)\<in>tvars U. 0 \<le> snd v \<Longrightarrow> \<forall>T\<in>set Tsz. ztyp_ok T \<Longrightarrow>
    \<exists>q. zlift_prems ta inc k pz Tsz bs i j G = returnZ q \<and>
      zprf_tr q = lift_prems_a inc k (zprf_tr pz) (map typ_of Tsz) bs i j G"
proof (induction ta inc k pz Tsz bs i j G arbitrary: V rule: zlift_prems.induct)
  case (1 ta inc k pz Tsz bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    from has_type_imp_E[of V "map typ_of Tsz" U A B propT, OF "1.prems"(5)[unfolded wty_def True, THEN conjunct1]]
    have tA: "has_type V (map typ_of Tsz) A propT" "has_type V (map typ_of Tsz) B propT" by simp_all
    have v0: "\<forall>v\<in>vars A \<union> vars B. 0 \<le> snd v" using "1.prems"(5) True by (simp add: wty_def)
    then have vA: "\<forall>v\<in>vars A. snd v \<noteq> -1" "\<forall>v\<in>vars B. 0 \<le> snd v"
      using integer_nonneg_ne_m1 by blast+
    have tyA: "\<forall>U\<in>tys A. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1" using "1.prems"(6) integer_nonneg_ne_m1 by fastforce
    from zterm_of_zdec[OF tA(1) vA(1) tyA] "1.prems"(1) obtain A' where A': "zterm_of ta A = returnZ A'" "zdec A' = A"
      by blast
    have wB: "wty V (map typ_of Tsz) B propT" using tA vA(2) by (simp add: wty_def)
    have tB: "\<forall>U\<in>tys B. \<forall>(v, S)\<in>tvars U. 0 \<le> snd v" using "1.prems"(6) by auto
    from "1.IH"[OF True A'(1)[unfolded returnZ_def] "1.prems"(1-4) wB tB "1.prems"(7)] obtain q where
      "zlift_prems ta inc k pz Tsz (True # bs) (i + 1) j B = returnZ q"
      "zprf_tr q = lift_prems_a inc k (zprf_tr pz) (map typ_of Tsz) (True # bs) (i + 1) j B"
      by blast
    with True A' show ?thesis by simp
  next
    case False
    with zlift_prems_leaf_tr[OF "1.prems"(2,3,7,4)] show ?thesis by simp
  qed
next
  case (2 ta inc k pz Tsz bs i j c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    from has_type_all_E[of V "map typ_of Tsz" U a T t propT, OF "2.prems"(5)[unfolded wty_def True, THEN conjunct1]]
    have tG: "has_type V (T # map typ_of Tsz) t propT" by simp
    have Tr: "typ_of (ztyp_of T) = T" using "2.prems"(6) by (intro typ_of_ztyp_of) fastforce
    have Tok: "ztyp_ok (ztyp_of T)" using "2.prems"(6) Tr by (auto simp: ztyp_ok_def)
    have wt: "wty V (map typ_of (ztyp_of T # Tsz)) t propT" using tG "2.prems"(5) Tr by (auto simp: wty_def)
    from "2.IH"[OF True "2.prems"(1-4) wt _ ] "2.prems"(6,7) Tok obtain q where
      "zlift_prems ta inc k pz (ztyp_of T # Tsz) (False # bs) i (j + 1) t = returnZ q"
      "zprf_tr q = lift_prems_a inc k (zprf_tr pz) (map typ_of (ztyp_of T # Tsz)) (False # bs) i (j + 1) t"
      by auto
    with True Tr show ?thesis by simp
  next
    case False
    with zlift_prems_leaf_tr[OF "2.prems"(2,3,7,4)] show ?thesis by simp
  qed
qed (use zlift_prems_leaf_tr in auto)


lemma mapZ_zterm_of:
  "\<forall>P\<in>set Ps. \<exists>z. zterm_of ztargs P = returnZ z \<and> zdec z = P \<Longrightarrow>
    \<exists>zs. mapZ (zterm_of ztargs) Ps = returnZ zs \<and> map zdec zs = Ps"
  by (induction Ps) auto

lemma zterm_of_wty:
  assumes "wty V Ts t T" "\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. 0 \<le> snd v"
  shows "\<exists>z. zterm_of ztargs t = returnZ z \<and> zdec z = t"
proof (rule zterm_of_zdec)
  show "has_type V Ts t T" using assms(1) by (simp add: wty_def)
  show "\<forall>v\<in>vars t. snd v \<noteq> -1" using assms(1) integer_nonneg_ne_m1 by (auto simp: wty_def)
  show "\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1" using assms(2) integer_nonneg_ne_m1 by fastforce
qed

text \<open>The tight lifting of a proof without proof constants is the annotated lifting.\<close>

theorem zlift_proof_tr:
  assumes "zconst_free pz" "zprf_all zterm_ok ztyp_ok pz" "0 \<le> inc"
    and G: "wty V [] G propT" "\<forall>U\<in>tys G. \<forall>(v, S)\<in>tvars U. 0 \<le> snd v"
    and P: "\<forall>P\<in>set prems. wty V2 [] P propT \<and> (\<forall>U\<in>tys P. \<forall>(v, S)\<in>tvars U. 0 \<le> snd v)"
  shows "\<exists>q. zlift_proof ztargs G inc prems pz = returnZ q \<and> zprf_tr q = lift_proof_a G inc prems (zprf_tr pz)"
proof -
  from mapZ_zterm_of[of prems] P zterm_of_wty obtain As where
    As: "mapZ (zterm_of ztargs) prems = returnZ As" "map zdec As = prems"
    by blast
  from zlift_prems_tr[OF HOL.refl assms(1-3), of V "[]" G "integer_of_nat (length prems)" "[]" 0 0] G
  obtain q where "zlift_prems ztargs inc (integer_of_nat (length prems)) pz [] [] 0 0 G = returnZ q"
    "zprf_tr q = lift_prems_a inc (integer_of_nat (length prems)) (zprf_tr pz) [] [] 0 0 G"
    by auto
  with As show ?thesis by (simp add: zlift_proof_def lift_proof_a_def ZAbsps_tr)
qed

text \<open>
  Lifting a valid tight proof yields a valid tight proof of the lifted rule, without exceptions
  (with fixes \<open>zterm-lift-hyps\<close> and \<open>zterm-lift-frees\<close>).
\<close>

theorem zprf_valid_lift:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and inc: "0 \<le> inc" and P: "prf_valid alg ar V H tps (zprf_tr pz) (list_implies As B)"
    and tps: "\<forall>(t, u)\<in>set tps. \<exists>T. wty V [] t T \<and> wty V [] u T"
    and wR: "wty V [] (list_implies As B) propT"
    and G: "wty V2 [] G propT" and V2: "lift_venv (rev (lift_Ts [] G)) inc V V2"
    and z: "zconst_free pz" "zprf_all zterm_ok ztyp_ok pz"
    and tG: "\<forall>U\<in>tys G. \<forall>(v, S)\<in>tvars U. 0 \<le> snd v"
    and tA: "\<forall>A\<in>set As. \<forall>U\<in>tys (lift_all inc G A). \<forall>(v, S)\<in>tvars U. 0 \<le> snd v"
  shows "\<exists>q. zlift_proof ztargs G inc (map (lift_all inc G) As) pz = returnZ q \<and>
    prf_valid alg ar V2 H (map (\<lambda>(t, u). (lift_abs inc G t, lift_abs inc G u)) tps)
      (zprf_tr q) (list_implies (map (lift_all inc G) As) (lift_all inc G B))"
proof -
  have wA: "\<forall>A\<in>set As. wty V [] A propT" using wty_list_implies[OF wR] by simp
  have wP: "\<forall>P\<in>set (map (lift_all inc G) As). wty V2 [] P propT"
    using wA G V2 inc by (auto simp: lift_all_def intro: wty_lift_all_aux)
  from zlift_proof_tr[OF z inc G tG, of "map (lift_all inc G) As" V2] wP tA obtain q where
    q: "zlift_proof ztargs G inc (map (lift_all inc G) As) pz = returnZ q"
      "zprf_tr q = lift_proof_a G inc (map (lift_all inc G) As) (zprf_tr pz)"
    by auto
  have H': "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {})" using H by blast
  have "prf_valid alg ar V2 H (map (\<lambda>(t, u). (lift_abs inc G t, lift_abs inc G u)) tps)
      (lift_proof_a G inc (map (lift_all inc G) As) (zprf_tr pz)) (list_implies (map (lift_all inc G) As) (lift_all inc G B))"
    by (rule prf_valid_ctx_prf_valid[OF prf_valid_lift_proof_a[OF H inc prf_valid_prf_valid_ctx[OF H' P tps] wR G V2]])
  with q show ?thesis by simp
qed

end

end
