section \<open>Lifting tight proofs\<close>

theory ZProof_Lift
  imports ZProof_Hidden
begin

text \<open>
  The tight proof of a lifted rule (\<open>ZTerm.lift_proof\<close>) decodes to the classic lifted proof with
  the premises, the assumptions and the parameters of the subgoal as annotations
  (\<^const>\<open>alift_proof\<close>). Hence it is valid modulo hidden variables if the proof of the rule is.
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


subsection \<open>Decoding the lifted proof\<close>

text \<open>The assumptions and parameters of the subgoal convert to tight terms and back:\<close>

fun zlift_ok :: "pterm \<Rightarrow> bool" where
  "zlift_ok (Const c U $ A $ B) \<longleftrightarrow>
    (c = STR ''Pure.imp'' \<longrightarrow> (\<exists>z. zterm_of ztargs A = returnZ z \<and> zdec z = A) \<and> zlift_ok B)"
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
      returnZ (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))} = returnZ q \<and>
      zprf_tr q = proof_combP (lift_prf inc (rev (map typ_of Ts)) 0 (zprf_tr pf))
        (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"
  using zlift_prf_tr[OF pf, of "rev Ts" inc 0] Ts inc
  by (auto simp: zprf_tr_ZAppps comp_def zprf_tr_spine rev_map)

lemma zlift_prems_tr:
  "zconst_free pf \<Longrightarrow> zprf_all zterm_ok ztyp_ok pf \<Longrightarrow> 0 \<le> inc \<Longrightarrow> zlift_ok G \<Longrightarrow>
    \<forall>T\<in>set Ts. ztyp_ok T \<Longrightarrow>
    \<exists>q. zlift_prems ztargs inc k pf Ts bs i j G = returnZ q \<and>
      zprf_tr q = alift_prems Some Some inc k (zprf_tr pf) (map typ_of Ts) bs i j G"
proof (induction ztargs inc k pf Ts bs i j G rule: zlift_prems.induct)
  case (1 inc k pf Ts bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with 1(5) obtain z where z: "zterm_of ztargs A = returnZ z" "zdec z = A" and ok: "zlift_ok B" by auto
    from 1(1)[OF True z(1)[unfolded returnZ_def] 1(2-4) ok 1(6)] obtain q where
      "zlift_prems ztargs inc k pf Ts (True # bs) (i + 1) j B = returnZ q"
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
      "zlift_prems ztargs inc k pf (ztyp_of T # Ts) (False # bs) i (j + 1) t = returnZ q"
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
    and prems: "\<forall>A\<in>set prems. \<exists>z. zterm_of ztargs A = returnZ z \<and> zdec z = A"
  shows "\<exists>q. zlift_proof ztargs G inc prems pf = returnZ q \<and>
    zprf_tr q = alift_proof Some Some Some G inc prems (zprf_tr pf)"
proof -
  have "\<exists>zs. mapZ (zterm_of ztargs) prems = returnZ zs \<and> map zdec zs = prems"
    using prems by (induction prems) auto
  then obtain zs where zs: "mapZ (zterm_of ztargs) prems = returnZ zs" "map zdec zs = prems" by blast
  from zlift_prems_tr[OF pf inc G, of "[]" "integer_of_nat (length prems)" "[]" 0 0] obtain q where
    q: "zlift_prems ztargs inc (integer_of_nat (length prems)) pf [] [] 0 0 G = returnZ q"
    "zprf_tr q = alift_prems Some Some inc (integer_of_nat (length prems)) (zprf_tr pf) [] [] 0 0 G"
    by auto
  have "zprf_tr (ZAbsps zs q) = foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) (map zdec zs) (zprf_tr q)"
    by (induction zs) (simp_all add: ZAbsps_def)
  with zs q show ?thesis by (simp add: zlift_proof_def alift_proof_def)
qed

end


subsection \<open>Hidden variables of the lifted proof\<close>

text \<open>
  Lifting maps the variables of the rule injectively to variables with indices above the
  maximal index of the subgoal; a separation of the hidden variables of the lifted proof pulls
  back to one of the proof of the rule.
\<close>

definition lpair :: "ptyp list \<Rightarrow> integer \<Rightarrow> indexname \<times> ptyp \<Rightarrow> indexname \<times> ptyp" where
  "lpair Us inc v = ((fst (fst v), snd (fst v) + inc), foldr fun_type Us (incr_tvar inc (snd v)))"

definition lpull :: "ptyp list \<Rightarrow> integer \<Rightarrow> (indexname \<Rightarrow> ptyp \<Rightarrow> indexname) \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> indexname" where
  "lpull Us inc \<nu>' x T = (let y = \<nu>' (fst x, snd x + inc) (foldr fun_type Us (incr_tvar inc T)) in (fst y, snd y - inc))"

lemma incr_tvar_incr_tvar: "incr_tvar a (incr_tvar b T) = incr_tvar (a + b) T"
proof (induction T)
  case (TVar v S)
  then show ?case by (cases v) (simp add: ac_simps)
qed simp_all

lemma incr_tvar_inj: "incr_tvar inc T = incr_tvar inc U \<Longrightarrow> T = U"
  by (drule arg_cong[of _ _ "incr_tvar (- inc)"]) (simp add: incr_tvar_incr_tvar)

lemma foldr_fun_type_inj: "foldr fun_type Us T = foldr fun_type Us U \<Longrightarrow> T = U"
  by (induction Us) auto

lemma lpair_inj: "inj (lpair Us inc)"
  by (rule injI) (auto simp: lpair_def prod_eq_iff dest: foldr_fun_type_inj incr_tvar_inj)

lemma rnv_id: "vars t \<subseteq> V \<Longrightarrow> rnv V \<nu> t = t"
  by (induction t) auto

lemma rnv_combound: "rnv V \<nu> (combound u n k) = combound (rnv V \<nu> u) n k"
  by (induction u n k rule: combound.induct) simp_all

lemma rnv_incr_idx:
  assumes "\<forall>v\<in>vars t. v \<in> V \<longleftrightarrow> lpair Us inc v \<in> V'"
  shows "rnv V' \<nu>' (incr_idx Us inc lev t) = incr_idx Us inc lev (rnv V (lpull Us inc \<nu>') t)"
  using assms
proof (induction Us inc lev t rule: incr_idx.induct)
  case (1 Ts inc lev x i T)
  then show ?case
    by (cases "\<nu>' (x, i + inc) (foldr fun_type Ts (incr_tvar inc T))")
      (simp add: rnv_combound lpair_def lpull_def Let_def)
qed simp_all

context prf_sig
begin

lemma prf_terms_lift_prf:
  "prf_terms (lift_prf inc Us lev q) \<subseteq> (\<Union>l. (incr_idx Us inc l) ` prf_terms q)"
  by (induction inc Us lev q rule: lift_prf.induct) fastforce+

lemma prf_rnv_lift_prf:
  assumes "\<forall>v\<in>prf_vars q. v \<in> V \<longleftrightarrow> lpair Us inc v \<in> V'"
  shows "prf_rnv V' \<nu>' (lift_prf inc Us lev q) = lift_prf inc Us lev (prf_rnv V (lpull Us inc \<nu>') q)"
  using assms
proof (induction inc Us lev q rule: lift_prf.induct)
  case (2 inc Ts lev a t p)
  then show ?case by (cases t) (auto simp: prf_rnv_def prf_vars_def intro!: rnv_incr_idx)
next
  case (3 inc Ts lev p t)
  then show ?case by (cases t) (auto simp: prf_rnv_def prf_vars_def intro!: rnv_incr_idx)
qed (auto simp: prf_rnv_def prf_vars_def option.map_ident id_def)

lemma prf_rnv_proof_combP: "prf_rnv V \<nu> (proof_combP p qs) = proof_combP (prf_rnv V \<nu> p) (map (prf_rnv V \<nu>) qs)"
  by (induction qs arbitrary: p) (simp_all add: proof_combP_def prf_rnv_def)

lemma prf_rnv_spine: "prf_rnv V \<nu> (spine bs i j c) = spine bs i j c"
proof -
  have "prf_rnv V \<nu> (snd (snd (foldr mk_app bs (a, b, p)))) = snd (snd (foldr mk_app bs (a, b, prf_rnv V \<nu> p)))"
    for a b p
  proof (induction bs)
    case (Cons x bs)
    show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) (simp_all add: prf_rnv_def)
  qed simp
  then show ?thesis by (simp add: spine_def prf_rnv_def)
qed

lemma prf_rnv_alift_prems:
  assumes q: "\<forall>v\<in>prf_vars q. v \<in> V \<longleftrightarrow> lpair Us inc v \<in> V'" and G0: "atomic G0"
    and fA: "\<And>A. fA A = None \<or> fA A = Some A"
  shows "\<forall>it\<in>set p. litem_ok it \<Longrightarrow> pvars p \<subseteq> V' \<Longrightarrow> rev Ts @ ptys p = Us \<Longrightarrow>
    prf_rnv V' \<nu>' (alift_prems fA fT inc k q Ts bs i j (lift_pre p G0)) =
      alift_prems fA fT inc k (prf_rnv V (lpull Us inc \<nu>') q) Ts bs i j (lift_pre p G0)"
proof (induction p arbitrary: Ts bs i j)
  case Nil
  then show ?case
    using prf_rnv_lift_prf[OF q, of \<nu>' 0]
    by (simp add: alift_prems_atomic[OF G0] prf_rnv_proof_combP prf_rnv_spine comp_def)
next
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have "rnv V' \<nu>' H = H" by (rule rnv_id) (use Cons.prems(2) LImp in auto)
    then have "map_option (rnv V' \<nu>') (fA H) = fA H" using fA[of H] by auto
    with Cons LImp c show ?thesis by (simp add: prf_rnv_def)
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    have "rev (T # Ts) @ ptys p = Us" using Cons.prems(3) LAll by simp
    with Cons LAll c show ?thesis by (simp add: prf_rnv_def option.map_ident id_def)
  qed
qed

end

lemma lpair_alt: "lpair Us inc = (\<lambda>((x, i), T). ((x, i + inc), foldr fun_type Us (incr_tvar inc T)))"
  by (auto simp: lpair_def fun_eq_iff)

lemma prf_vars_simps [simp]:
  "prf_vars (AbsP a t q) = (\<Union>u\<in>set_option t. vars u) \<union> prf_vars q"
  "prf_vars (PAppt q t) = prf_vars q \<union> (\<Union>u\<in>set_option t. vars u)"
  "prf_vars (PAppp q q') = prf_vars q \<union> prf_vars q'"
  "prf_vars (Abst a T q) = prf_vars q"
  by (auto simp: prf_vars_def)

lemma prf_vars_proof_combP: "prf_vars (proof_combP p qs) = prf_vars p \<union> (\<Union>q\<in>set qs. prf_vars q)"
  by (induction qs arbitrary: p) (auto simp: proof_combP_def)

lemma prf_vars_lift_prf: "prf_vars (lift_prf inc Us lev q) = lpair Us inc ` prf_vars q"
proof (induction inc Us lev q rule: lift_prf.induct)
  case (2 inc Ts lev a t p)
  then show ?case by (cases t) (auto simp: vars_incr_idx lpair_alt image_Un)
next
  case (3 inc Ts lev p t)
  then show ?case by (cases t) (auto simp: vars_incr_idx lpair_alt image_Un)
qed (auto simp: prf_vars_def image_Un)

lemma prf_vars_alift_prems:
  assumes G0: "atomic G0"
  shows "\<forall>it\<in>set p. litem_ok it \<Longrightarrow> rev Ts @ ptys p = Us \<Longrightarrow>
    lpair Us inc ` prf_vars q \<subseteq> prf_vars (alift_prems fA fT inc k q Ts bs i j (lift_pre p G0))"
proof (induction p arbitrary: Ts bs i j)
  case Nil
  then show ?case by (simp add: alift_prems_atomic[OF G0] prf_vars_proof_combP prf_vars_lift_prf)
next
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have "lpair Us inc ` prf_vars q \<subseteq> prf_vars (alift_prems fA fT inc k q Ts (True # bs) (i + 1) j (lift_pre p G0))"
      by (rule Cons.IH) (use Cons.prems LImp in auto)
    with LImp c show ?thesis by auto
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    have "lpair Us inc ` prf_vars q \<subseteq> prf_vars (alift_prems fA fT inc k q (T # Ts) (False # bs) i (j + 1) (lift_pre p G0))"
      by (rule Cons.IH) (use Cons.prems LAll in auto)
    with LAll c show ?thesis by auto
  qed
qed

context prf_sig
begin

theorem hvalid_alift_proof:
  assumes hv: "hvalid ax (set hs) (th_tpairs rule) pf (th_prop rule)"
    and w: "wt_thm rmax hs (th_tpairs rule) (th_prop rule)" and G: "wtp G" and ib: "ibelow gmax G"
    and nn: "\<forall>v\<in>prf_vars pf. 0 \<le> snd (fst v)"
    and fP: "\<And>A. fP A = None \<or> fP A = Some A"
    and fA: "\<And>A. fA A = None \<or> fA A = Some A" and fT: "\<And>T. fT T = None \<or> fT T = Some T"
  shows "hvalid ax (set hs) (th_tpairs (lift_rule G gmax rule))
    (alift_proof fP fA fT G (gmax + 1) (map (lift_all (gmax + 1) G) (strip_imp_prems (th_prop rule))) pf)
    (th_prop (lift_rule G gmax rule))"
proof -
  obtain p G0 where sp: "lsplit G = (p, G0)" by (cases "lsplit G")
  have pok: "G = lift_pre p G0" and ok: "\<forall>it\<in>set p. litem_ok it" and G0: "atomic G0"
    using lsplit_ok[OF sp] by simp_all
  define inc where "inc = gmax + 1"
  define Us where "Us = ptys p"
  define P where "P = th_prop rule"
  define As where "As = strip_imp_prems P"
  define B where "B = strip_imp_concl P"
  let ?V = "vars_thm (th_tpairs rule) P" and ?V' = "vars_thm (th_tpairs (lift_rule G gmax rule)) (th_prop (lift_rule G gmax rule))"
  let ?prems = "map (lift_all inc G) As"
  have wP: "wtp P" using w by (simp add: wt_thm_def P_def)
  have PAB: "P = list_implies As B" unfolding As_def B_def by (rule list_implies_strip_imp[OF wtpD(2)[OF wP]])
  have la: "vars (lift_all inc G X) = pvars p \<union> lpair Us inc ` vars X" for X
    by (simp add: lift_all_lsplit[OF sp] vars_lift_pre vars_incr_indexes lpair_alt Us_def)
  have lb: "vars (lift_abs inc G X) = lpair Us inc ` vars X" for X
    by (simp add: lift_abs_lsplit[OF sp] vars_incr_indexes lpair_alt Us_def)
  have vP: "vars (th_prop (lift_rule G gmax rule)) = pvars p \<union> lpair Us inc ` vars P"
  proof -
    have "th_prop (lift_rule G gmax rule) = list_implies (map (lift_all inc G) As) (lift_all inc G B)"
      by (simp add: lift_rule_def Let_def inc_def As_def B_def P_def)
    then show ?thesis unfolding PAB by (auto simp: vars_list_implies la)
  qed
  have vT: "(\<Union>(t, u)\<in>set (th_tpairs (lift_rule G gmax rule)). vars t \<union> vars u) =
      lpair Us inc ` (\<Union>(t, u)\<in>set (th_tpairs rule). vars t \<union> vars u)"
    by (simp add: lift_rule_def Let_def inc_def[symmetric] lb image_UN image_Un split_def)
  have V': "?V' = pvars p \<union> lpair Us inc ` ?V"
    unfolding vars_thm_def vP vT by blast
  have pv: "\<forall>v\<in>pvars p. snd (fst v) \<le> gmax" using ib pok by (auto simp: ibelow_def vars_lift_pre)
  have corr: "\<forall>v\<in>prf_vars pf. v \<in> ?V \<longleftrightarrow> lpair Us inc v \<in> ?V'"
  proof
    fix v assume v: "v \<in> prf_vars pf"
    have "lpair Us inc v \<notin> pvars p"
      using pv nn v by (fastforce simp: lpair_def inc_def)
    then show "v \<in> ?V \<longleftrightarrow> lpair Us inc v \<in> ?V'"
      unfolding V' by (simp add: inj_image_mem_iff[OF lpair_inj])
  qed
  have pP: "vars A \<subseteq> ?V'" if "A \<in> set ?prems" for A
  proof -
    from that obtain x where x: "x \<in> set As" "A = lift_all inc G x" by auto
    have "vars x \<subseteq> ?V" using x(1) by (auto simp: vars_thm_def PAB vars_list_implies)
    then show ?thesis by (auto simp: x(2) la V')
  qed
  show ?thesis unfolding hvalid_def P_def[symmetric] inc_def[symmetric] As_def[symmetric]
  proof (intro allI impI)
    fix \<nu>' assume sep': "hsep ?V' \<nu>' (prf_vars (alift_proof fP fA fT G inc ?prems pf))"
    let ?\<nu> = "lpull Us inc \<nu>'"
    have sub: "lpair Us inc ` prf_vars pf \<subseteq> prf_vars (alift_proof fP fA fT G inc ?prems pf)"
    proof -
      have "lpair Us inc ` prf_vars pf \<subseteq> prf_vars (alift_prems fA fT inc (integer_of_nat (length ?prems)) pf [] [] 0 0 G)"
        unfolding pok by (rule prf_vars_alift_prems[OF G0 ok]) (simp add: Us_def)
      moreover have "prf_vars q \<subseteq> prf_vars (foldr (\<lambda>A p. AbsP (STR ''H'') (fP A) p) xs q)" for q xs
        by (induction xs) auto
      ultimately show ?thesis by (auto simp: alift_proof_def)
    qed
    have sep: "hsep ?V ?\<nu> (prf_vars pf)"
      unfolding hsep_def
    proof (intro conjI ballI)
      show "inj_on (\<lambda>(x, T). ?\<nu> x T) (prf_vars pf - ?V)"
      proof (rule inj_onI)
        fix v w assume v: "v \<in> prf_vars pf - ?V" and w: "w \<in> prf_vars pf - ?V"
          and e: "(\<lambda>(x, T). ?\<nu> x T) v = (\<lambda>(x, T). ?\<nu> x T) w"
        have hv': "lpair Us inc v \<in> prf_vars (alift_proof fP fA fT G inc ?prems pf) - ?V'"
          "lpair Us inc w \<in> prf_vars (alift_proof fP fA fT G inc ?prems pf) - ?V'"
          using v w sub corr by auto
        from e have "(\<lambda>(x, T). \<nu>' x T) (lpair Us inc v) = (\<lambda>(x, T). \<nu>' x T) (lpair Us inc w)"
          by (cases v; cases w) (auto simp: lpull_def lpair_def Let_def prod_eq_iff)
        with sep' hv' have "lpair Us inc v = lpair Us inc w" by (auto simp: hsep_def dest: inj_onD)
        then show "v = w" using inj_eq[OF lpair_inj] by blast
      qed
      fix v assume v: "v \<in> prf_vars pf - ?V"
      obtain x T where xT: "v = (x, T)" by (cases v)
      have hv': "lpair Us inc v \<in> prf_vars (alift_proof fP fA fT G inc ?prems pf) - ?V'"
        using v sub corr by auto
      show "case v of (x, T) \<Rightarrow> ?\<nu> x T \<notin> fst ` ?V"
        unfolding xT prod.case
      proof
        assume "?\<nu> x T \<in> fst ` ?V"
        then obtain w where w: "w \<in> ?V" "?\<nu> x T = fst w" by blast
        let ?y = "\<nu>' (fst (lpair Us inc (x, T))) (snd (lpair Us inc (x, T)))"
        have "?y = fst (lpair Us inc w)"
          using w(2) by (cases ?y) (auto simp: lpull_def lpair_def Let_def prod_eq_iff)
        then have yin: "?y \<in> fst ` ?V'" using w(1) V' by auto
        from sep' have "\<forall>z\<in>prf_vars (alift_proof fP fA fT G inc ?prems pf) - ?V'. case z of (a, b) \<Rightarrow> \<nu>' a b \<notin> fst ` ?V'"
          by (simp add: hsep_def)
        from bspec[OF this hv'[unfolded xT]] have "?y \<notin> fst ` ?V'" by (simp add: case_prod_beta)
        with yin show False by contradiction
      qed
    qed
    have "prf_valid ax (set hs) (th_tpairs rule) (prf_rnv ?V ?\<nu> pf) P"
      using hv sep by (simp add: hvalid_def P_def)
    from prf_valid_alift_proof[OF this[unfolded P_def] w G fP fA fT, of gmax]
    have val: "prf_valid ax (set hs) (th_tpairs (lift_rule G gmax rule))
        (alift_proof fP fA fT G inc ?prems (prf_rnv ?V ?\<nu> pf)) (th_prop (lift_rule G gmax rule))"
      by (simp add: inc_def As_def P_def)
    have "prf_rnv ?V' \<nu>' (alift_proof fP fA fT G inc ?prems pf) = alift_proof fP fA fT G inc ?prems (prf_rnv ?V ?\<nu> pf)"
    proof -
      have "prf_rnv ?V' \<nu>' (alift_prems fA fT inc k pf [] [] 0 0 (lift_pre p G0)) =
          alift_prems fA fT inc k (prf_rnv ?V ?\<nu> pf) [] [] 0 0 (lift_pre p G0)" for k
        by (rule prf_rnv_alift_prems[OF corr G0 fA ok]) (use V' in \<open>auto simp: Us_def\<close>)
      then have "prf_rnv ?V' \<nu>' (alift_prems fA fT inc k pf [] [] 0 0 G) = alift_prems fA fT inc k (prf_rnv ?V ?\<nu> pf) [] [] 0 0 G" for k
        using pok by metis
      moreover have "prf_rnv ?V' \<nu>' (foldr (\<lambda>A p. AbsP (STR ''H'') (fP A) p) xs q) =
          foldr (\<lambda>A p. AbsP (STR ''H'') (fP A) p) xs (prf_rnv ?V' \<nu>' q)" if "\<forall>A\<in>set xs. vars A \<subseteq> ?V'" for xs q
        using that
      proof (induction xs)
        case (Cons A xs)
        have "map_option (rnv ?V' \<nu>') (fP A) = fP A" using fP[of A] rnv_id[of A ?V'] Cons.prems by auto
        with Cons show ?case by (simp add: prf_rnv_def)
      qed simp
      ultimately show ?thesis using pP by (simp add: alift_proof_def)
    qed
    with val show "prf_valid ax (set hs) (th_tpairs (lift_rule G gmax rule))
        (prf_rnv ?V' \<nu>' (alift_proof fP fA fT G inc ?prems pf)) (th_prop (lift_rule G gmax rule))"
      by simp
  qed
qed

end

end
