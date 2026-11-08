section \<open>Lifting tight proofs\<close>

theory ZProof_Lift
  imports ZProof_Decode
begin

text \<open>
  The tight proof of a lifted rule (\<open>ZTerm.lift_proof\<close>) decodes to the classic lifted proof with
  the premises, the assumptions and the parameters of the subgoal as annotations
  (\<^const>\<open>alift_proof\<close>), which is valid if the proof of the rule is.
\<close>

subsection \<open>Decoding the lifting of terms\<close>

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

text \<open>The terms and types of a tight proof (not those of hypotheses, which lifting keeps).\<close>

fun zprf_all :: "(zterm \<Rightarrow> bool) \<Rightarrow> (ztyp \<Rightarrow> bool) \<Rightarrow> zproof \<Rightarrow> bool" where
  "zprf_all P Q (ZAbst a T p) \<longleftrightarrow> Q T \<and> zprf_all P Q p"
| "zprf_all P Q (ZAbsp a t p) \<longleftrightarrow> P t \<and> zprf_all P Q p"
| "zprf_all P Q (ZAppt p t) \<longleftrightarrow> zprf_all P Q p \<and> P t"
| "zprf_all P Q (ZAppp p q) \<longleftrightarrow> zprf_all P Q p \<and> zprf_all P Q q"
| "zprf_all P Q (OFCLASSp T c) \<longleftrightarrow> Q T"
| "zprf_all P Q _ \<longleftrightarrow> True"

lemma incr_tvar_tsubst: "incr_tvar inc (tsubst \<sigma> U) = tsubst (\<lambda>v S. incr_tvar inc (\<sigma> v S)) U"
  by (induction U) simp_all

lemma incr_tvar_dummyT [simp]: "incr_tvar inc dummyT = dummyT"
  by (simp add: dummyT_def)

lemma map_of_zip_map_snd: "map_of (zip xs (map f ys)) x = map_option f (map_of (zip xs ys) x)"
  by (induction xs arbitrary: ys) (auto simp: zip_Cons1 split: list.splits)

lemma typ_of_zincr_tvar:
  assumes "ztyp_ok T" "0 \<le> inc"
  shows "typ_of (zincr_tvar inc T) = incr_tvar inc (typ_of T)"
proof (cases "inc = 0")
  case True
  then show ?thesis by (simp add: zincr_tvar_def)
next
  case False
  have "typ_of (zsubst_type (\<lambda>((a, i), S). if 0 \<le> i then Some (ZTVar (a, i + inc) S) else None) U) =
      incr_tvar inc (typ_of U)" if "ztyp_ok U" for U
    using that
  proof (induction U)
    case (ZTVar v S)
    then show ?case using assms(2) by (cases v) (auto simp: ztyp_ok_def)
  qed (auto simp: ztyp_ok_def propT_def)
  with assms False show ?thesis by (simp add: zincr_tvar_def)
qed

lemma integer_nonneg_ne_m1: "0 \<le> (x :: integer) \<Longrightarrow> x \<noteq> -1"
  by transfer simp

lemma typ_of_ZFuns: "typ_of (ZFuns Ts T) = foldr fun_type (map typ_of Ts) (typ_of T)"
  by (induction Ts) (simp_all add: ZFuns_def)

context pure_sig
begin

lemma zconst_typ_incr: "zconst_typ c (map (incr_tvar inc) Us) = incr_tvar inc (zconst_typ c Us)"
proof -
  have i: "incr_tvar inc imp_type = imp_type" by (simp add: imp_type_def propT_def)
  show ?thesis
    by (cases "ctab c")
      (auto simp: zconst_typ_def i propT_def incr_tvar_tsubst map_of_zip_map_snd
        split: list.splits option.splits intro!: tsubst_cong)
qed

lemma zdec_zcombound: "zdec (zcombound t n k) = combound (zdec t) n k"
  by (induction t n k rule: zcombound.induct) simp_all

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
    moreover have "i \<noteq> -1" using True by (rule integer_nonneg_ne_m1)
    ultimately show ?thesis using True T by (simp add: xi zdec_zcombound typ_of_ZFuns)
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
  using zdec_zlift_term[OF assms] by (auto simp: zlift_term'_def incr_idx_id)

text \<open>Lifting a tight proof without proof constants is the lifting of the classic proof.\<close>

lemma zlift_prf_tr:
  assumes "zconst_free p" "zprf_all zterm_ok ztyp_ok p" "\<forall>T\<in>set Ts. ztyp_ok T" "0 \<le> inc"
  shows "\<exists>q. zlift_prf inc Ts lev p = return q \<and> zprf_tr q = lift_prf inc (map typ_of Ts) lev (zprf_tr p) \<and>
    zconst_free q"
  using assms(1,2)
proof (induction p arbitrary: lev)
  case (ZAbst a T p)
  then obtain q where "zlift_prf inc Ts (lev + 1) p = return q"
    "zprf_tr q = lift_prf inc (map typ_of Ts) (lev + 1) (zprf_tr p)" "zconst_free q"
    by auto
  then show ?case using ZAbst.prems assms(4) by (simp add: typ_of_zincr_tvar)
next
  case (ZAbsp a t p)
  then obtain q where "zlift_prf inc Ts lev p = return q"
    "zprf_tr q = lift_prf inc (map typ_of Ts) lev (zprf_tr p)" "zconst_free q"
    by auto
  then show ?case using ZAbsp.prems assms(3,4) by (simp add: zdec_zlift_term')
next
  case (ZAppt p t)
  then obtain q where "zlift_prf inc Ts lev p = return q"
    "zprf_tr q = lift_prf inc (map typ_of Ts) lev (zprf_tr p)" "zconst_free q"
    by auto
  then show ?case using ZAppt.prems assms(3,4) by (simp add: zdec_zlift_term')
next
  case (ZAppp p1 p2)
  from ZAppp obtain q1 where "zlift_prf inc Ts lev p1 = return q1"
    "zprf_tr q1 = lift_prf inc (map typ_of Ts) lev (zprf_tr p1)" "zconst_free q1"
    by auto
  moreover from ZAppp obtain q2 where "zlift_prf inc Ts lev p2 = return q2"
    "zprf_tr q2 = lift_prf inc (map typ_of Ts) lev (zprf_tr p2)" "zconst_free q2"
    by auto
  ultimately show ?case by simp
next
  case (OFCLASSp T c)
  then show ?case using assms(4) by (simp add: typ_of_zincr_tvar)
qed simp_all


subsection \<open>Decoding the lifted proof\<close>

text \<open>The assumptions and parameters of the subgoal convert to tight terms and back:\<close>

fun zlift_ok :: "pterm \<Rightarrow> bool" where
  "zlift_ok (Const c U $ A $ B) \<longleftrightarrow>
    (c = STR ''Pure.imp'' \<longrightarrow> (\<exists>z. zterm_of ztargs A = return z \<and> zdec z = A) \<and> zlift_ok B)"
| "zlift_ok (Const c U $ Abs a T t) \<longleftrightarrow>
    (c = STR ''Pure.all'' \<longrightarrow> typ_of (ztyp_of T) = T \<and> ztyp_ok (ztyp_of T) \<and> zlift_ok t)"
| "zlift_ok _ \<longleftrightarrow> True"

lemma zprf_tr_ZAppps: "zprf_tr (ZAppps p qs) = proof_combP (zprf_tr p) (map zprf_tr qs)"
  by (induction qs arbitrary: p) (simp_all add: ZAppps_def proof_combP_def)

lemma mk_app_simps:
  "mk_app True (x, y, p) = (x - 1, y, PAppp p (PBound x))" "mk_app False (x, y, p) = (x, y - 1, PAppt p (Some (Bound y)))"
  "zmk_app True (x, y, q) = (x - 1, y, ZAppp q (ZBoundp x))" "zmk_app False (x, y, q) = (x, y - 1, ZAppt q (ZBound y))"
  by (simp_all add: mk_app_def zmk_app_def)

lemma zprf_tr_foldr_zmk_app:
  "foldr mk_app bs (a, b, zprf_tr p) = (\<lambda>(x, y, q). (x, y, zprf_tr q)) (foldr zmk_app bs (a, b, p))"
proof (induction bs)
  case (Cons c bs)
  obtain x y q where e: "foldr zmk_app bs (a, b, p) = (x, y, q)" by (cases "foldr zmk_app bs (a, b, p)")
  with Cons have "foldr mk_app bs (a, b, zprf_tr p) = (x, y, zprf_tr q)" by simp
  with e show ?case by (cases c) (simp_all add: mk_app_simps)
qed simp

lemma zprf_tr_spine:
  "zprf_tr (snd (snd (foldr zmk_app bs (a, b, ZBoundp k)))) = snd (snd (foldr mk_app bs (a, b, PBound k)))"
  using zprf_tr_foldr_zmk_app[of bs a b "ZBoundp k"] by (cases "foldr zmk_app bs (a, b, ZBoundp k)") simp

lemma zlift_prems_leaf:
  assumes pf: "zconst_free pf" "zprf_all zterm_ok ztyp_ok pf" and inc: "0 \<le> inc"
    and Ts: "\<forall>T\<in>set Ts. ztyp_ok T"
  shows "\<exists>q. do {p \<leftarrow> zlift_prf inc (rev Ts) 0 pf;
      return (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))} = return q \<and>
      zprf_tr q = proof_combP (lift_prf inc (rev (map typ_of Ts)) 0 (zprf_tr pf))
        (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"
  using zlift_prf_tr[OF pf, of "rev Ts" inc 0] Ts inc
  by (auto simp: zprf_tr_ZAppps comp_def zprf_tr_spine rev_map)

lemma zlift_prems_tr:
  "zconst_free pf \<Longrightarrow> zprf_all zterm_ok ztyp_ok pf \<Longrightarrow> 0 \<le> inc \<Longrightarrow> zlift_ok G \<Longrightarrow>
    \<forall>T\<in>set Ts. ztyp_ok T \<Longrightarrow>
    \<exists>q. zlift_prems ztargs inc k pf Ts bs i j G = return q \<and>
      zprf_tr q = alift_prems Some Some inc k (zprf_tr pf) (map typ_of Ts) bs i j G"
proof (induction ztargs inc k pf Ts bs i j G rule: zlift_prems.induct)
  case (1 inc k pf Ts bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with 1(5) obtain z where z: "zterm_of ztargs A = return z" "zdec z = A" and ok: "zlift_ok B" by auto
    from 1(1)[OF True z(1) 1(2-4) ok 1(6)] obtain q where
      "zlift_prems ztargs inc k pf Ts (True # bs) (i + 1) j B = return q"
      "zprf_tr q = alift_prems Some Some inc k (zprf_tr pf) (map typ_of Ts) (True # bs) (i + 1) j B"
      by blast
    with True z show ?thesis by simp
  next
    case False
    with zlift_prems_leaf[OF 1(2-4) 1(6)] show ?thesis by simp
  qed
next
  case (2 inc k pf Ts bs i j c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with 2(5) have T: "typ_of (ztyp_of T) = T" "ztyp_ok (ztyp_of T)" and ok: "zlift_ok t" by auto
    from 2(1)[OF True 2(2-4) ok] 2(6) T(2) obtain q where
      "zlift_prems ztargs inc k pf (ztyp_of T # Ts) (False # bs) i (j + 1) t = return q"
      "zprf_tr q = alift_prems Some Some inc k (zprf_tr pf) (map typ_of (ztyp_of T # Ts)) (False # bs) i (j + 1) t"
      by auto
    with True T show ?thesis by simp
  next
    case False
    with zlift_prems_leaf[OF 2(2-4) 2(6)] show ?thesis by simp
  qed
qed (simp only: zlift_prems.simps alift_prems.simps, rule zlift_prems_leaf, assumption+)+

lemma zlift_proof_tr:
  assumes pf: "zconst_free pf" "zprf_all zterm_ok ztyp_ok pf" and inc: "0 \<le> inc" and G: "zlift_ok G"
    and prems: "\<forall>A\<in>set prems. \<exists>z. zterm_of ztargs A = return z \<and> zdec z = A"
  shows "\<exists>q. zlift_proof ztargs G inc prems pf = return q \<and>
    zprf_tr q = alift_proof Some Some Some G inc prems (zprf_tr pf)"
proof -
  have "\<exists>zs. mapM (zterm_of ztargs) prems = return zs \<and> map zdec zs = prems"
    using prems by (induction prems) auto
  then obtain zs where zs: "mapM (zterm_of ztargs) prems = return zs" "map zdec zs = prems" by blast
  from zlift_prems_tr[OF pf inc G, of "[]" "integer_of_nat (length prems)" "[]" 0 0] obtain q where
    q: "zlift_prems ztargs inc (integer_of_nat (length prems)) pf [] [] 0 0 G = return q"
    "zprf_tr q = alift_prems Some Some inc (integer_of_nat (length prems)) (zprf_tr pf) [] [] 0 0 G"
    by auto
  have "zprf_tr (ZAbsps zs q) = foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) (map zdec zs) (zprf_tr q)"
    by (induction zs) (simp_all add: ZAbsps_def)
  with zs q show ?thesis by (simp add: zlift_proof_def alift_proof_def)
qed

end

end
