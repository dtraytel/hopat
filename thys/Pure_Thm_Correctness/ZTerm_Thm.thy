section \<open>Theorems with tight proofs\<close>

theory ZTerm_Thm
  imports ZTerm_BicomposeMain
begin

text \<open>
  The tight proofs of the theorems of the model are kept with the invariant
  @{const prf_wf_csig.zthm_prf_inv}. Biresolution lifts the tight proof of the rule
  (\<open>ZTerm.lift_proof\<close>), renames it as the new premises and composes it with the tight proof of
  the proof state (\<open>ZTerm.bicompose_proof\<close>). This theory shows that lifting keeps the invariant
  of the annotations of tight proofs.
\<close>

context prf_wf_csig
begin

subsection \<open>Typing contexts of terms without loose bound variables\<close>

lemmas integer_int_simps = less_eq_integer.rep_eq less_integer.rep_eq plus_integer.rep_eq
  integer_of_nat.rep_eq one_integer.rep_eq zero_integer.rep_eq

lemma integer_of_nat_plus: "integer_of_nat (k + n) = integer_of_nat k + integer_of_nat n"
  by (simp add: integer_eq_iff integer_int_simps)

lemma nat_of_integer_less: "0 \<le> i \<Longrightarrow> i < integer_of_nat n \<Longrightarrow> nat_of_integer i < n"
  by (simp add: less_integer.rep_eq less_eq_integer.rep_eq integer_of_nat.rep_eq nat_of_integer.rep_eq nat_less_iff)

lemma has_type_ctx_agree:
  "has_type V Ts t T \<Longrightarrow> \<not> loose_bvar t (integer_of_nat n) \<Longrightarrow>
    \<forall>i<n. i < length Ts \<longrightarrow> i < length Us \<and> Us ! i = Ts ! i \<Longrightarrow> has_type V Us t T"
proof (induction t arbitrary: Ts Us n T)
  case (Bound i)
  from Bound.prems(1) have i: "0 \<le> i" "nat_of_integer i < length Ts" "T = Ts ! nat_of_integer i"
    by (auto elim: has_type_elims)
  from Bound.prems(2) have "i < integer_of_nat n" by simp
  with i(1) have "nat_of_integer i < n" by (rule nat_of_integer_less)
  with i Bound.prems(3) show ?case by (auto intro: has_type.Bound)
next
  case (Abs x T' t)
  from Abs.prems(1) obtain U where T: "T = T' \<rightarrow>\<^sub>T U" and h: "has_type V (T' # Ts) t U"
    by (auto elim: has_type_elims)
  have "has_type V (T' # Us) t U"
  proof (rule Abs.IH[OF h])
    show "\<not> loose_bvar t (integer_of_nat (Suc n))" using Abs.prems(2) by (simp add: integer_of_nat_Suc)
    show "\<forall>i<Suc n. i < length (T' # Ts) \<longrightarrow> i < length (T' # Us) \<and> (T' # Us) ! i = (T' # Ts) ! i"
      using Abs.prems(3) by (auto simp: less_Suc_eq_0_disj)
  qed
  then show ?case using T by (simp add: has_type.Abs)
next
  case (App s t)
  from App.prems(1) obtain T' where s: "has_type V Ts s (T' \<rightarrow>\<^sub>T T)" and t: "has_type V Ts t T'"
    by (auto elim: has_type_elims)
  have "has_type V Us s (T' \<rightarrow>\<^sub>T T)" by (rule App.IH(1)[OF s _ App.prems(3)]) (use App.prems(2) in simp)
  moreover have "has_type V Us t T'" by (rule App.IH(2)[OF t _ App.prems(3)]) (use App.prems(2) in simp)
  ultimately show ?case by (rule has_type.App)
qed (auto elim!: has_type_elims intro: has_type.intros)

lemma has_type_resize:
  assumes "has_type V Ts t T" "\<not> loose_bvar t (integer_of_nat n)"
  shows "\<exists>Us. length Us = n \<and> has_type V Us t T"
proof -
  let ?Us = "map (\<lambda>i. if i < length Ts then Ts ! i else propT) [0..<n]"
  have "has_type V ?Us t T" by (rule has_type_ctx_agree[OF assms]) auto
  then show ?thesis by (intro exI[of _ ?Us]) simp
qed


subsection \<open>Lifting tight terms\<close>

lemma zincr_tvar_0[simp]: "zincr_tvar 0 = (\<lambda>T. T)"
  by (simp add: zincr_tvar_def fun_eq_iff)

lemma zlift_term_0: "zlift_term 0 [] lev t = t"
proof (induction t arbitrary: lev)
  case (ZVar xi T)
  then show ?case by (cases xi) (simp add: zincr_tvar_def ZFuns_def)
qed simp_all

lemma zlift_term'_eq: "zlift_term' inc Ts lev t = zlift_term inc Ts lev t"
  by (simp add: zlift_term'_def zlift_term_0)

lemma zvars_zcombound: "zvars (zcombound t n k) = zvars t"
  by (induction t n k rule: zcombound.induct) simp_all

lemma ztys_zcombound: "ztys (zcombound t n k) = ztys t"
  by (induction t n k rule: zcombound.induct) simp_all

lemma zvars_zlift_term:
  "(y, U) \<in> zvars (zlift_term inc Ts lev t) \<Longrightarrow> snd y \<noteq> -1 \<Longrightarrow> zterm_ok t \<Longrightarrow>
    \<exists>x T. (x, T) \<in> zvars t \<and> 0 \<le> snd x \<and> y = incr_ix inc x"
proof (induction t arbitrary: lev)
  case (ZVar xi T)
  then show ?case by (cases xi) (auto simp: zvars_zcombound incr_ix_def split: if_splits)
next
  case (ZApp t1 t2)
  from ZApp.prems(1) have "(y, U) \<in> zvars (zlift_term inc Ts lev t1) \<or> (y, U) \<in> zvars (zlift_term inc Ts lev t2)"
    by simp
  then show ?case
  proof
    assume "(y, U) \<in> zvars (zlift_term inc Ts lev t1)"
    from ZApp.IH(1)[OF this ZApp.prems(2)] ZApp.prems(3) show ?thesis by auto
  next
    assume "(y, U) \<in> zvars (zlift_term inc Ts lev t2)"
    from ZApp.IH(2)[OF this ZApp.prems(2)] ZApp.prems(3) show ?thesis by auto
  qed
qed auto

lemma ztys_zlift_term:
  "U \<in> ztys (zlift_term inc Ts lev t) \<Longrightarrow> \<exists>T\<in>ztys t. U = zincr_tvar inc T \<or> U = ZFuns Ts (zincr_tvar inc T)"
proof (induction t arbitrary: lev)
  case (ZVar xi T)
  then show ?case by (cases xi) (auto simp: ztys_zcombound split: if_splits)
qed auto

lemma zcan_zincr_tvar: "zcan T \<Longrightarrow> zcan (zincr_tvar inc T)"
  unfolding zincr_tvar_def by (auto intro!: zcan_zsubst_type split: prod.splits if_splits)

lemma zcan_ZFuns: "\<forall>T\<in>set Ts. zcan T \<Longrightarrow> zcan U \<Longrightarrow> zcan (ZFuns Ts U)"
  by (induction Ts) (simp_all add: ZFuns_def)

lemma ztyp_ok_zty: "zty A m T \<Longrightarrow> \<forall>q\<in>A. 0 \<le> snd (fst q) \<Longrightarrow> ztyp_ok T"
  by (fastforce simp: zty_def ztyp_ok_def)

text \<open>The conditions of lifting a tight proof of a rule with a typing over \<open>Ar\<close> and maximal index
  \<open>mr\<close> into a typing over \<open>A\<close> with maximal index \<open>m\<close>.\<close>

definition zlift_ok :: "(indexname \<times> psort) set \<Rightarrow> integer \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> integer \<Rightarrow>
    integer \<Rightarrow> bool" where
  "zlift_ok Ar mr A m inc \<longleftrightarrow> (\<forall>q\<in>Ar. 0 \<le> snd (fst q)) \<and> (\<forall>q\<in>A. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> m) \<and>
    0 \<le> inc \<and> incrA inc Ar \<subseteq> A \<and> mr + inc \<le> m"

lemma zty_zincr_tvar:
  assumes "zty Ar mr T" "zlift_ok Ar mr A m inc"
  shows "zty A m (zincr_tvar inc T)"
proof -
  have ok: "ztyp_ok T" using assms ztyp_ok_zty by (auto simp: zlift_ok_def)
  have t: "typ_of (zincr_tvar inc T) = incr_tvar inc (typ_of T)"
    by (rule typ_of_zincr_tvar[OF ok]) (use assms(2) in \<open>simp add: zlift_ok_def\<close>)
  have "tvars (typ_of T) \<subseteq> Ar" using assms(1) by (simp add: zty_def)
  then have "(\<lambda>(v, S). (incr_ix inc v, S)) ` tvars (typ_of T) \<subseteq> A"
    using assms(2) unfolding zlift_ok_def incrA_def by blast
  then have "tvars (typ_of (zincr_tvar inc T)) \<subseteq> A" by (simp add: t tvars_incr_tvar)
  moreover have "snd v \<le> m" if "(v, S) \<in> tvars (typ_of (zincr_tvar inc T))" for v S
  proof -
    from that obtain w where "(w, S) \<in> tvars (typ_of T)" "v = incr_ix inc w"
      by (auto simp: t tvars_incr_tvar)
    with assms show ?thesis by (fastforce simp: zty_def zlift_ok_def incr_ix_def)
  qed
  ultimately show ?thesis using assms(1) by (auto simp: zty_def zcan_zincr_tvar)
qed

lemma zty_ZFuns: "\<forall>T\<in>set Ts. zty A m T \<Longrightarrow> zty A m U \<Longrightarrow> zty A m (ZFuns Ts U)"
  by (induction Ts) (auto simp: ZFuns_def zty_def)

lemma zterm_ok_zvars:
  "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<Longrightarrow> \<forall>T\<in>ztys t. ztyp_ok T \<Longrightarrow> zterm_ok t"
  by (induction t) auto

lemma zterm_ok_zann: "zann Ar Wr mr t \<Longrightarrow> \<forall>q\<in>Ar. 0 \<le> snd (fst q) \<Longrightarrow> zterm_ok t"
  by (rule zterm_ok_zvars) (auto simp: zann_def intro: ztyp_ok_zty)

lemma loose_bvar_combound:
  "\<not> loose_bvar t j \<Longrightarrow> n + integer_of_nat k \<le> j \<Longrightarrow> \<not> loose_bvar (combound t n k) j"
proof (induction t n k rule: combound.induct)
  case (2 t n k)
  have k0: "0 \<le> integer_of_nat k" by simp
  have "n + 1 + integer_of_nat k \<le> j" using "2.prems"(2) by (simp add: integer_of_nat_Suc add_ac)
  then have "\<not> loose_bvar (combound t (n + 1) k) j" by (rule "2.IH"[OF "2.prems"(1)])
  moreover have "n < j" using "2.prems"(2) by (simp add: integer_of_nat_Suc integer_int_simps)
  ultimately show ?case by simp
qed simp

lemma loose_bvar_incr_idx:
  "\<not> loose_bvar t lev \<Longrightarrow> \<not> loose_bvar (incr_idx Us inc lev t) (lev + integer_of_nat (length Us))"
proof (induction Us inc lev t rule: incr_idx.induct)
  case (1 Ts inc lev x i T)
  show ?case by (simp only: incr_idx.simps) (rule loose_bvar_combound; simp)
next
  case (3 Ts inc lev x T t)
  then show ?case by (simp add: add.commute add.left_commute)
next
  case (6 Ts inc lev i)
  then show ?case by (simp add: integer_int_simps)
qed simp_all

lemma zann_zlift_term:
  assumes z: "zann Ar Wr mr t" and lb: "\<not> loose_bvar (zdec t) (integer_of_nat k)"
    and ok: "zlift_ok Ar mr A m inc" and Ts: "\<forall>T\<in>set Ts. zty A m T"
    and V: "lift_venv (map typ_of Ts) inc Wr W"
  shows "zann A W m (zlift_term' inc Ts (integer_of_nat k) t)
    \<and> \<not> loose_bvar (zdec (zlift_term' inc Ts (integer_of_nat k) t)) (integer_of_nat (k + length Ts))"
proof -
  have Ar0: "\<forall>q\<in>Ar. 0 \<le> snd (fst q)" and A0: "\<forall>q\<in>A. 0 \<le> snd (fst q)" and inc: "0 \<le> inc"
    using ok by (auto simp: zlift_ok_def)
  have zok: "zterm_ok t" by (rule zterm_ok_zann[OF z Ar0])
  have Tok: "\<forall>T\<in>set Ts. ztyp_ok T" using Ts A0 ztyp_ok_zty by blast
  have d: "zdec (zlift_term' inc Ts (integer_of_nat k) t) = incr_idx (map typ_of Ts) inc (integer_of_nat k) (zdec t)"
    by (rule zdec_zlift_term'[OF zok Tok inc])
  from z obtain Ts0 U where "has_type Wr Ts0 (zdec t) U" by (auto simp: zann_def)
  from has_type_resize[OF this lb] obtain Us where Us: "length Us = k" "has_type Wr Us (zdec t) U" by blast
  have v0: "\<forall>v\<in>vars (zdec t). 0 \<le> snd v" using z by (auto simp: vars_zdec zann_def)
  from has_type_incr_idx[OF Us(2) V v0] Us(1)
  have h: "has_type W (map (incr_tvar inc) Us @ rev (map typ_of Ts))
      (zdec (zlift_term' inc Ts (integer_of_nat k) t)) (incr_tvar inc U)"
    by (simp add: d)
  have "zann A W m (zlift_term' inc Ts (integer_of_nat k) t)"
  proof (rule zann_intro[OF _ _ h])
    show "\<forall>(y, T')\<in>zvars (zlift_term' inc Ts (integer_of_nat k) t). snd y \<noteq> -1 \<longrightarrow> 0 \<le> snd y \<and> snd y \<le> m"
    proof (intro ballI impI, clarify)
      fix a i T' assume y: "((a, i), T') \<in> zvars (zlift_term' inc Ts (integer_of_nat k) t)" "snd (a, i) \<noteq> -1"
      from zvars_zlift_term[OF y[unfolded zlift_term'_eq] zok] obtain x T where
        x: "(x, T) \<in> zvars t" "0 \<le> snd x" "(a, i) = incr_ix inc x" by blast
      have "snd x \<le> mr" using z x(1,2) by (auto simp: zann_def)
      with x(2,3) ok show "0 \<le> snd (a, i) \<and> snd (a, i) \<le> m" by (auto simp: incr_ix_def zlift_ok_def)
    qed
    show "\<forall>T'\<in>ztys (zlift_term' inc Ts (integer_of_nat k) t). zty A m T'"
    proof
      fix T' assume "T' \<in> ztys (zlift_term' inc Ts (integer_of_nat k) t)"
      from ztys_zlift_term[OF this[unfolded zlift_term'_eq]] obtain T where
        T: "T \<in> ztys t" "T' = zincr_tvar inc T \<or> T' = ZFuns Ts (zincr_tvar inc T)" by blast
      have "zty Ar mr T" using z T(1) by (auto simp: zann_def)
      then have "zty A m (zincr_tvar inc T)" by (rule zty_zincr_tvar[OF _ ok])
      with T(2) Ts show "zty A m T'" by (auto intro: zty_ZFuns)
    qed
  qed
  moreover have "\<not> loose_bvar (zdec (zlift_term' inc Ts (integer_of_nat k) t)) (integer_of_nat (k + length Ts))"
    using loose_bvar_incr_idx[OF lb, of "map typ_of Ts" inc] by (simp add: d integer_of_nat_plus)
  ultimately show ?thesis by blast
qed


subsection \<open>Lifting tight proofs\<close>

definition zlinv0 :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> zproof \<Rightarrow> bool" where
  "zlinv0 A W m n q \<longleftrightarrow> zconst_free q \<and> zno_class q \<and> zprf_all (zann A W m) (zty A m) q \<and> zlb n q"

definition zlinv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> zproof \<Rightarrow> bool" where
  "zlinv A W m n q \<longleftrightarrow> zlinv0 A W m n q \<and> zrf q"

lemma zlift_prf_ZAbst:
  "zlift_prf inc Ts lev p = returnZ q \<Longrightarrow> (\<exists>a T r. q = ZAbst a T r) \<longleftrightarrow> (\<exists>a T r. p = ZAbst a T r)"
proof (cases p)
  case (ZConstp c)
  then show "zlift_prf inc Ts lev p = returnZ q \<Longrightarrow> ?thesis" by (cases c) (auto simp: bindZ_eq_returnZ)
qed (auto simp: bindZ_eq_returnZ)

lemma zlift_prf_inv:
  assumes "zlift_prf inc Ts (integer_of_nat k) p = returnZ q" "zconst_free p" "zno_class p"
    "zprf_all (zann Ar Wr mr) (zty Ar mr) p" "zlb k p"
    and ok: "zlift_ok Ar mr A m inc" and Ts: "\<forall>T\<in>set Ts. zty A m T"
    and V: "lift_venv (map typ_of Ts) inc Wr W"
  shows "zlinv0 A W m (k + length Ts) q"
  using assms(1-5)
proof (induction p arbitrary: k q)
  case (ZAbst a T p)
  have e: "integer_of_nat k + 1 = integer_of_nat (Suc k)" by (simp add: integer_of_nat_Suc)
  from ZAbst.prems(1) obtain p' where p': "zlift_prf inc Ts (integer_of_nat (Suc k)) p = returnZ p'"
    "q = ZAbst a (zincr_tvar inc T) p'"
    by (auto simp: bindZ_eq_returnZ e)
  have "zlinv0 A W m (Suc k + length Ts) p'" by (rule ZAbst.IH[OF p'(1)]) (use ZAbst.prems in simp_all)
  moreover have "zty A m (zincr_tvar inc T)" using ZAbst.prems(4) by (auto intro: zty_zincr_tvar[OF _ ok])
  ultimately show ?case using p'(2) by (simp add: zlinv0_def)
next
  case (ZAbsp a t p)
  from ZAbsp.prems(1) obtain p' where p': "zlift_prf inc Ts (integer_of_nat k) p = returnZ p'"
    "q = ZAbsp a (zlift_term' inc Ts (integer_of_nat k) t) p'"
    by (auto simp: bindZ_eq_returnZ)
  have "zlinv0 A W m (k + length Ts) p'" by (rule ZAbsp.IH[OF p'(1)]) (use ZAbsp.prems in simp_all)
  moreover have "zann A W m (zlift_term' inc Ts (integer_of_nat k) t)
      \<and> \<not> loose_bvar (zdec (zlift_term' inc Ts (integer_of_nat k) t)) (integer_of_nat (k + length Ts))"
    by (rule zann_zlift_term[OF _ _ ok Ts V]) (use ZAbsp.prems(4,5) in simp_all)
  ultimately show ?case using p'(2) by (simp add: zlinv0_def)
next
  case (ZAppt p t)
  from ZAppt.prems(1) obtain p' where p': "zlift_prf inc Ts (integer_of_nat k) p = returnZ p'"
    "q = ZAppt p' (zlift_term' inc Ts (integer_of_nat k) t)"
    by (auto simp: bindZ_eq_returnZ)
  have "zlinv0 A W m (k + length Ts) p'" by (rule ZAppt.IH[OF p'(1)]) (use ZAppt.prems in simp_all)
  moreover have "zann A W m (zlift_term' inc Ts (integer_of_nat k) t)
      \<and> \<not> loose_bvar (zdec (zlift_term' inc Ts (integer_of_nat k) t)) (integer_of_nat (k + length Ts))"
    by (rule zann_zlift_term[OF _ _ ok Ts V]) (use ZAppt.prems(4,5) in simp_all)
  ultimately show ?case using p'(2) by (simp add: zlinv0_def)
next
  case (ZAppp p1 p2)
  from ZAppp.prems(1) obtain q1 q2 where q: "zlift_prf inc Ts (integer_of_nat k) p1 = returnZ q1"
    "zlift_prf inc Ts (integer_of_nat k) p2 = returnZ q2" "q = ZAppp q1 q2"
    by (auto simp: bindZ_eq_returnZ)
  have "zlinv0 A W m (k + length Ts) q1" by (rule ZAppp.IH(1)[OF q(1)]) (use ZAppp.prems in simp_all)
  moreover have "zlinv0 A W m (k + length Ts) q2" by (rule ZAppp.IH(2)[OF q(2)]) (use ZAppp.prems in simp_all)
  ultimately show ?case using q(3) by (simp add: zlinv0_def)
qed (auto simp: zlinv0_def)

lemma zlift_prf_zrf: "zlift_prf inc Ts lev p = returnZ q \<Longrightarrow> zrf p \<Longrightarrow> zrf q"
proof (induction p arbitrary: lev q)
  case (ZAbst a T p)
  then show ?case by (auto simp: bindZ_eq_returnZ)
next
  case (ZAppt p t)
  from ZAppt.prems(1) obtain p' where p': "zlift_prf inc Ts lev p = returnZ p'"
    "q = ZAppt p' (zlift_term' inc Ts lev t)"
    by (auto simp: bindZ_eq_returnZ)
  have "\<forall>a T r. p' \<noteq> ZAbst a T r" using zlift_prf_ZAbst[OF p'(1)] ZAppt.prems(2) by auto
  with ZAppt.IH[OF p'(1)] ZAppt.prems(2) p'(2) show ?case by simp
next
  case (ZConstp c)
  then show ?case by (cases c) (auto simp: bindZ_eq_returnZ)
qed (auto simp: bindZ_eq_returnZ)

lemma foldr_zmk_app_fst:
  "fst (snd (foldr zmk_app bs (a, b, p))) = b - integer_of_nat (length (filter Not bs))"
  by (induction bs) (auto simp: zmk_app_def integer_of_nat_Suc algebra_simps split: prod.splits)

lemma foldr_zmk_app_inv:
  assumes "\<forall>x. 0 \<le> x \<and> x \<le> b \<longrightarrow> zann A W m (ZBound x) \<and> \<not> loose_bvar (Bound x) (integer_of_nat n)"
  shows "integer_of_nat (length (filter Not bs)) \<le> b + 1 \<Longrightarrow>
    zlinv A W m n (snd (snd (foldr zmk_app bs (a, b, ZBoundp c)))) \<and>
    (\<forall>d T r. snd (snd (foldr zmk_app bs (a, b, ZBoundp c))) \<noteq> ZAbst d T r)"
proof (induction bs)
  case Nil
  then show ?case by (simp add: zlinv_def zlinv0_def)
next
  case (Cons x bs)
  obtain a' b' q' where r: "foldr zmk_app bs (a, b, ZBoundp c) = (a', b', q')" by (rule prod_cases3)
  have b': "b' = b - integer_of_nat (length (filter Not bs))"
    using foldr_zmk_app_fst[of bs a b "ZBoundp c"] r by simp
  have le: "integer_of_nat (length (filter Not bs)) \<le> b + 1"
    using Cons.prems by (cases x) (auto simp: integer_of_nat_Suc integer_int_simps)
  from Cons.IH[OF le] r have IH: "zlinv A W m n q'" "\<forall>d T r. q' \<noteq> ZAbst d T r" by simp_all
  show ?case
  proof (cases x)
    case True
    have e: "foldr zmk_app (x # bs) (a, b, ZBoundp c) = zmk_app x (a', b', q')" using r by simp
    show ?thesis unfolding e using IH True by (simp add: zmk_app_def zlinv_def zlinv0_def)
  next
    case False
    have "0 \<le> b' \<and> b' \<le> b" using Cons.prems False b' by (simp add: integer_of_nat_Suc integer_int_simps)
    with assms have "zann A W m (ZBound b') \<and> \<not> loose_bvar (Bound b') (integer_of_nat n)" by blast
    moreover have e: "foldr zmk_app (x # bs) (a, b, ZBoundp c) = zmk_app x (a', b', q')" using r by simp
    ultimately show ?thesis unfolding e using IH False by (simp add: zmk_app_def zlinv_def zlinv0_def)
  qed
qed

lemma zann_ZBound: "0 \<le> x \<Longrightarrow> zann A W m (ZBound x)"
  unfolding zann_def
  by (auto intro!: exI[of _ "replicate (Suc (nat_of_integer x)) propT"] has_type.Bound)

lemma zrf_ZAppps: "zrf p \<Longrightarrow> zrf (ZAppps p qs)"
  by (induction qs arbitrary: p) (simp_all add: ZAppps_def)

lemma zlift_prems_leaf_inv:
  assumes "bindZ (zlift_prf inc (rev Tsz) 0 pz) (\<lambda>p. returnZ (ZAppps p
      (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))) = returnZ q"
    and z: "zconst_free pz" "zno_class pz" "zrf pz" "zprf_all (zann Ar Wr mr) (zty Ar mr) pz" "zlb 0 pz"
    and ok: "zlift_ok Ar mr A m inc" and Ts: "\<forall>T\<in>set Tsz. zty A m T"
    and V: "lift_venv (rev (map typ_of Tsz)) inc Wr W"
    and j: "j = integer_of_nat (length Tsz)" "length (filter Not bs) = length Tsz"
  shows "zlinv A W m (length Tsz) q"
proof -
  from assms(1) obtain p where p: "zlift_prf inc (rev Tsz) (integer_of_nat 0) pz = returnZ p"
    and q: "q = ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i))"
    by (auto simp: bindZ_eq_returnZ)
  have "zlinv0 A W m (0 + length (rev Tsz)) p"
    by (rule zlift_prf_inv[OF p z(1,2,4,5) ok]) (use Ts V in \<open>simp_all add: rev_map\<close>)
  moreover have "zrf p" by (rule zlift_prf_zrf[OF p z(3)])
  ultimately have P: "zlinv A W m (length Tsz) p" by (simp add: zlinv_def)
  have B: "\<forall>x. 0 \<le> x \<and> x \<le> j - 1 \<longrightarrow> zann A W m (ZBound x) \<and> \<not> loose_bvar (Bound x) (integer_of_nat (length Tsz))"
    using j(1) by (auto simp: zann_ZBound integer_int_simps)
  have le: "integer_of_nat (length (filter Not bs)) \<le> j - 1 + 1" using j by simp
  have "zlinv A W m (length Tsz) r" if "r \<in> set (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k))))
      (downto (i + k - 1) i))" for r
    using that foldr_zmk_app_inv[OF B le] by auto
  with P show ?thesis
    by (auto simp: q zlinv_def zlinv0_def zconst_free_ZAppps zno_class_ZAppps zprf_all_ZAppps zlb_ZAppps intro: zrf_ZAppps)
qed

lemma zann_zterm_of:
  assumes "zterm_of ztargs t = returnZ z" "has_type W Ts t U" "\<forall>v\<in>vars t. 0 \<le> snd v \<and> snd v \<le> m"
    "\<forall>U\<in>tys t. tvars U \<subseteq> A" "\<forall>q\<in>A. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> m"
  shows "zann A W m z \<and> zdec z = t"
proof -
  have c: "cts t" using assms(2) by (rule has_type_cts)
  have v: "\<forall>v\<in>vars t. snd v \<noteq> -1" using assms(3) integer_nonneg_ne_m1 by blast
  have tv: "\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1" using assms(4,5) integer_nonneg_ne_m1 by fastforce
  from zterm_of_zdec_cts[OF c v tv] assms(1) have d: "zdec z = t"
    and zt: "\<forall>V\<in>ztys z. tvars (typ_of V) \<subseteq> (\<Union>U\<in>tys t. tvars U)" by auto
  have "zann A W m z"
  proof (rule zann_intro)
    show "\<forall>(x, T)\<in>zvars z. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m" by (rule zvars_bound) (use assms(3) d in simp)
    show "\<forall>T\<in>ztys z. zty A m T"
    proof
      fix T assume T: "T \<in> ztys z"
      have "tvars (typ_of T) \<subseteq> A" using zt T assms(4) by blast
      with assms(5) ztys_zterm_of_zcan[OF assms(1)] T show "zty A m T" by (fastforce simp: zty_def)
    qed
    show "has_type W Ts (zdec z) U" using assms(2) d by simp
  qed
  with d show ?thesis by simp
qed

lemma zlift_prems_inv:
  "zlift_prems ta inc k pz Tsz bs i j G = returnZ q \<Longrightarrow> ta = ztargs \<Longrightarrow>
    zconst_free pz \<Longrightarrow> zno_class pz \<Longrightarrow> zrf pz \<Longrightarrow> zprf_all (zann Ar Wr mr) (zty Ar mr) pz \<Longrightarrow> zlb 0 pz \<Longrightarrow>
    zlift_ok Ar mr A m inc \<Longrightarrow> \<forall>T\<in>set Tsz. zty A m T \<Longrightarrow>
    has_type W (map typ_of Tsz) G propT \<Longrightarrow> \<forall>v\<in>vars G. 0 \<le> snd v \<and> snd v \<le> m \<Longrightarrow> \<forall>U\<in>tys G. tvars U \<subseteq> A \<Longrightarrow>
    lift_venv (rev (lift_Ts (map typ_of Tsz) G)) inc Wr W \<Longrightarrow>
    j = integer_of_nat (length Tsz) \<Longrightarrow> length (filter Not bs) = length Tsz \<Longrightarrow>
    zlinv A W m (length Tsz) q"
proof (induction ta inc k pz Tsz bs i j G arbitrary: q rule: zlift_prems.induct)
  case (1 ta inc k pz Tsz bs i j c U HA B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    from "1.prems"(1) True obtain A' p where A': "zterm_of ta HA = returnZ A'"
      and p: "zlift_prems ta inc k pz Tsz (True # bs) (i + 1) j B = returnZ p" and q: "q = ZAbsp (STR ''H'') A' p"
      by (auto simp: bindZ_eq_returnZ)
    from has_type_imp_E[OF "1.prems"(10)[unfolded True]]
    have hA: "has_type W (map typ_of Tsz) HA propT" and hB: "has_type W (map typ_of Tsz) B propT" by simp_all
    have "zlinv A W m (length Tsz) p"
      by (rule "1.IH"[OF True A'[unfolded returnZ_def] p]) (use "1.prems" hB True in simp_all)
    moreover have "zann A W m A' \<and> zdec A' = HA"
      by (rule zann_zterm_of[OF A'[unfolded "1.prems"(2)] hA]) (use "1.prems"(8,11,12) in \<open>auto simp: zlift_ok_def\<close>)
    moreover have "\<not> loose_bvar HA (integer_of_nat (length Tsz))" using has_type_loose_bvar[OF hA] by simp
    ultimately show ?thesis using q by (simp add: zlinv_def zlinv0_def)
  next
    case False
    with "1.prems" show ?thesis by (intro zlift_prems_leaf_inv[of inc Tsz pz bs i j k q]) simp_all
  qed
next
  case (2 ta inc k pz Tsz bs i j c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    from "2.prems"(1) True obtain p where p: "zlift_prems ta inc k pz (ztyp_of T # Tsz) (False # bs) i (j + 1) t = returnZ p"
      and q: "q = ZAbst a (ztyp_of T) p"
      by (auto simp: bindZ_eq_returnZ)
    from has_type_all_E[OF "2.prems"(10)[unfolded True]] have ht: "has_type W (T # map typ_of Tsz) t propT" by simp
    have TA: "tvars T \<subseteq> A" using "2.prems"(12) by simp
    have Tr: "typ_of (ztyp_of T) = T"
      using TA "2.prems"(8) by (intro typ_of_ztyp_of) (fastforce simp: zlift_ok_def intro: integer_nonneg_ne_m1)
    have zT: "zty A m (ztyp_of T)" using TA "2.prems"(8) Tr by (fastforce simp: zty_def zlift_ok_def)
    have "zlinv A W m (length (ztyp_of T # Tsz)) p"
      by (rule "2.IH"[OF True p]) (use "2.prems" ht True Tr zT in \<open>simp_all add: integer_of_nat_Suc\<close>)
    then show ?thesis using q zT by (simp add: zlinv_def zlinv0_def)
  next
    case False
    with "2.prems" show ?thesis by (intro zlift_prems_leaf_inv[of inc Tsz pz bs i j k q]) simp_all
  qed
qed (intro zlift_prems_leaf_inv; simp_all)+

theorem zinv_zlift_proof:
  assumes q: "zlift_proof ztargs G inc prems pz = returnZ q"
    and z: "zinv Ar Wr mr pz" "zlb 0 pz" and ok: "zlift_ok Ar mr A m inc"
    and G: "has_type W [] G propT" "\<forall>v\<in>vars G. 0 \<le> snd v \<and> snd v \<le> m" "\<forall>U\<in>tys G. tvars U \<subseteq> A"
    and V: "lift_venv (rev (lift_Ts [] G)) inc Wr W"
    and P: "\<forall>P\<in>set prems. has_type W [] P propT \<and> (\<forall>v\<in>vars P. 0 \<le> snd v \<and> snd v \<le> m) \<and> (\<forall>U\<in>tys P. tvars U \<subseteq> A)"
  shows "zinv A W m q \<and> zlb 0 q"
proof -
  from q obtain As p where As: "mapZ (zterm_of ztargs) prems = returnZ As"
    and p: "zlift_prems ztargs inc (integer_of_nat (length prems)) pz [] [] 0 0 G = returnZ p"
    and qe: "q = ZAbsps As p"
    by (auto simp: zlift_proof_def bindZ_eq_returnZ)
  have "zlinv A W m (length ([] :: ztyp list)) p"
    by (rule zlift_prems_inv[OF p HOL.refl]) (use z ok G V in \<open>simp_all add: zinv_def\<close>)
  then have pz: "zlinv A W m 0 p" by simp
  have Az: "zann A W m a \<and> \<not> loose_bvar (zdec a) 0" if "a \<in> set As" for a
  proof -
    from that obtain i where i: "i < length As" "a = As ! i" by (auto simp: in_set_conv_nth)
    have il: "i < length prems" using i(1) length_mapZ[OF As] by simp
    have e: "zterm_of ztargs (prems ! i) = returnZ a" using mapZ_nth[OF As il] i(2) by simp
    have Pi: "has_type W [] (prems ! i) propT" "\<forall>v\<in>vars (prems ! i). 0 \<le> snd v \<and> snd v \<le> m"
      "\<forall>U\<in>tys (prems ! i). tvars U \<subseteq> A" using P nth_mem[OF il] by blast+
    have "zann A W m a \<and> zdec a = prems ! i"
      by (rule zann_zterm_of[OF e Pi(1,2,3)]) (use ok in \<open>simp add: zlift_ok_def\<close>)
    moreover have "\<not> loose_bvar (prems ! i) 0" using has_type_loose_bvar[OF Pi(1)] by simp
    ultimately show ?thesis by simp
  qed
  have "zrf (ZAbsps As p)" using pz by (cases As) (simp_all add: zlinv_def ZAbsps_def)
  then show ?thesis using pz Az
    by (auto simp: qe zinv_def zlinv_def zlinv0_def zconst_free_ZAbsps zno_class_ZAbsps zprf_all_ZAbsps zlb_ZAbsps)
qed

end

end
