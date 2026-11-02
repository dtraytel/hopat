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


subsection \<open>Composition\<close>

lemma full_prop_of_ok: "\<forall>(t, u)\<in>set tps. \<exists>T. has_type V [] t T \<Longrightarrow> \<exists>p. ok (full_prop_of tps P) p"
proof -
  assume a: "\<forall>(t, u)\<in>set tps. \<exists>T. has_type V [] t T"
  have "\<exists>e. ok (mk_equals x) e" if "x \<in> set tps" for x
  proof -
    obtain t u where x: "x = (t, u)" by (cases x)
    from a that x obtain T where "has_type V [] t T" by blast
    then have "fastype_of t = return T" by (rule fastype_of_closed)
    then show ?thesis by (simp add: x mk_equals_def)
  qed
  then have "\<forall>x\<in>set tps. \<exists>e. ok (mk_equals x) e" by blast
  from ok_mapM_exI[OF this] obtain eqs where "ok (mapM mk_equals tps) eqs" by blast
  then show ?thesis by (auto simp: full_prop_of_def)
qed

text \<open>
  The condition of the main theorem on the renaming of the new premises of the lifted rule, for
  the tight proof \<open>rprf\<close> of the lifted rule: the renaming keeps its hidden variables and renames no
  variable of the rule to one of them. (Injectivity and freshness of the renaming on the variables
  of the theorems follow from \<open>rename_bvars\<close>.)
\<close>

definition zren_ok :: "newas \<Rightarrow> integer \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow>
    zproof \<Rightarrow> zproof \<Rightarrow> bool" where
  "zren_ok na smax stps S rtps R sprf rprf \<longleftrightarrow>
    (\<forall>x\<in>prf_vars (zprf_tr rprf) - vars_thm rtps R. ren_of na smax x = x \<and> x \<notin> ren_of na smax ` vars_thm rtps R)"

text \<open>
  The tight proof of a result of \<^const>\<open>biresolution\<close>: the tight proof of the rule, lifted over the
  subgoal and renamed as the new premises, composed with the tight proof of the proof state. If
  the tight proofs of the proof state and the rule satisfy the invariant, lifting returns without
  exceptions; if the renaming satisfies @{const zren_ok}, the composition returns without
  exceptions, and its result satisfies the invariant with the hypotheses of both.
\<close>

theorem zbiresolution_prf_inv:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) alg rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and st: "thm_typeds ar 0 \<Sigma>s state" and ru: "thm_typeds ar 0 \<Sigma>r (rep rule)"
    and si: "zthm_prf_inv (th_maxidx state) (th_tpairs state) (th_prop state) Hs sprf" "zlb 0 sprf"
    and ri: "zthm_prf_inv (th_maxidx (rep rule)) (th_tpairs (rep rule)) (th_prop (rep rule)) Hr rprf" "zlb 0 rprf"
    and hs: "\<forall>h\<in>Hr. hyp_ok ar h"
  defines "inc \<equiv> th_maxidx state + 1" and "lr \<equiv> lift_rule Bi (th_maxidx state) (rep rule)"
  shows "\<exists>q. zlift_proof ztargs Bi inc (map (lift_all inc Bi) (strip_imp_prems (th_prop (rep rule)))) rprf = returnZ q \<and>
    (\<exists>vS. ok (full_prop_of (th_tpairs state) (th_prop state)) vS) \<and>
    (\<exists>vR. ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR) \<and>
    (\<forall>vS vR. ok (full_prop_of (th_tpairs state) (th_prop state)) vS \<longrightarrow> ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR \<longrightarrow>
      zren_ok (br_newas x) (th_maxidx state) (th_tpairs state) (th_prop state) (th_tpairs lr) (th_prop lr) sprf q \<longrightarrow>
      (\<exists>p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr (th_maxidx state) q) \<bind>
        (\<lambda>rp. zbicompose_proof ztargs (br_env x) (th_maxidx state) True Bs (na_As (br_newas x)) (br_A x)
          (na_oldAs (br_newas x)) (na_n (br_newas x))
          (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) [vS, vR] rp sprf) = returnZ p \<and>
      zthm_prf_inv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) p \<and> zlb 0 p) \<and>
      (\<forall>rp p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr (th_maxidx state) q) = returnZ rp \<longrightarrow>
        zbicompose_proof ztargs (br_env x) (th_maxidx state) True Bs (na_As (br_newas x)) (br_A x)
          (na_oldAs (br_newas x)) (na_n (br_newas x))
          (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) [vS, vR] rp sprf = returnZ p \<longrightarrow>
        (\<exists>Ar Wf. finite Ar \<and> scons Ar \<and> tcert alg Ar \<and> (\<forall>q\<in>Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> maxidx (br_env x)) \<and>
          (\<forall>x. tyA ar Ar (Wf x)) \<and> wt_thm ar Ar Wf (maxidx (br_env x)) (br_tpairs x) (br_prop x) \<and>
          prf_valid alg ar Wf (Hs \<union> Hr) (br_tpairs x) (zprf_tr p) (br_prop x) \<and> zinv Ar Wf (maxidx (br_env x)) p \<and>
          (\<not> env_is_empty (br_env x) \<longrightarrow> (\<exists>V PU. znorm_hyps (br_env x) [vS, vR] V Wf PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) \<and>
            (\<forall>U. PU U \<longrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> maxidx (br_env x))) \<and>
            znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) rp \<and>
            (\<not> above (br_env x) (th_maxidx state) \<longrightarrow> znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) sprf))))))"
proof -
  from br res obtain stpairs' Bs' Bi' C' goal where d': "okT (dest_state state i) (stpairs', Bs', Bi', C')"
    and g: "okT (cprem_of state i) goal" and r: "(eres_flg, rule) \<in> set brules"
    and xq: "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state)
      (stpairs', Bs', Bi', C') True eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule)))
      (nprems_of (rep rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result)
  from okT_det[OF d d'] have e: "stpairs' = stpairs" "Bs' = Bs" "Bi' = Bi" "C' = C" by simp_all
  let ?smax = "th_maxidx state" and ?R = "rep rule"
  let ?lr = "lift_rule goal ?smax ?R"
  from si(1) obtain As Ws where As: "finite As" "scons As" "tcert alg As"
    "\<forall>q\<in>As. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> ?smax" "\<forall>x. tyA ar As (Ws x)"
    and wS: "wt_thm ar As Ws ?smax (th_tpairs state) (th_prop state)"
    and sv0: "prf_valid alg ar Ws Hs (th_tpairs state) (zprf_tr sprf) (th_prop state)"
    and sz0: "zinv As Ws ?smax sprf"
    by (auto simp: zthm_prf_inv_def)
  from ri(1) obtain Ar Wr where Ar: "finite Ar" "scons Ar" "tcert alg Ar"
    "\<forall>q\<in>Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> th_maxidx ?R" "\<forall>x. tyA ar Ar (Wr x)"
    and wR: "wt_thm ar Ar Wr (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R)"
    and rv0: "prf_valid alg ar Wr Hr (th_tpairs ?R) (zprf_tr rprf) (th_prop ?R)"
    and rz0: "zinv Ar Wr (th_maxidx ?R) rprf"
    by (auto simp: zthm_prf_inv_def)
  from st have sm: "-1 \<le> ?smax" and Slo: "\<forall>x\<in>vars_thm (th_tpairs state) (th_prop state). 0 \<le> snd x"
    by (auto simp: thm_typeds_def)
  from ru have nn: "\<forall>x\<in>vars_thm (th_tpairs ?R) (th_prop ?R). 0 \<le> snd x" and rm: "-1 \<le> th_maxidx ?R"
    by (auto simp: thm_typeds_def)
  have Asb: "\<forall>p\<in>As. snd (fst p) \<le> ?smax" "\<forall>p\<in>As. 0 \<le> snd (fst p)" using As(4) by auto
  define A where "A = As \<union> (\<lambda>(v, S). (incr_ix (?smax + 1) v, S)) ` Ar"
  define W where "W = (\<lambda>x. if snd x \<le> ?smax then Ws x
      else foldr fun_type (Bicompose_Typing.csig.ptys (fst (lsplit Bi)))
        (incr_tvar (?smax + 1) (Wr (fst x, snd x - (?smax + 1)))))"
  note ct = compose_typed_explicit[OF d g As(1,2) Asb(1) As(5) wS sm Asb(2) Slo Ar(1,2,4,5) wR nn rm]
  have c: "finite A" "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max (th_maxidx ?lr) ?smax"
    "\<forall>x. tyA ar A (W x)"
    "wt_thm ar A W ?smax stpairs (list_implies (Bs @ [Bi]) C)"
    "ibelow ?smax (list_implies (Bs @ [Bi]) C)"
    "wt_thm ar A W (th_maxidx ?lr) (th_tpairs ?lr) (th_prop ?lr)"
    "lifted_over ?smax Bi (th_prop ?lr) (nprems_of ?R)"
    "th_tpairs state = stpairs" "th_prop state = list_implies (Bs @ [Bi]) C" "goal = Bi"
    "-1 \<le> th_maxidx ?lr"
    "(0::integer) \<le> 0 \<Longrightarrow> \<forall>p\<in>A. 0 \<le> snd (fst p)"
    "(0::integer) \<le> 0 \<Longrightarrow> \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm (th_tpairs ?lr) (th_prop ?lr).
      0 \<le> snd x"
    unfolding A_def W_def by (rule ct; assumption)+
  have A0: "\<forall>p\<in>A. 0 \<le> snd (fst p)" and nnc: "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union>
      vars_thm (th_tpairs ?lr) (th_prop ?lr). 0 \<le> snd x"
    using c(13,14) by simp_all
  have lr: "lr = ?lr" using c(11) by (simp add: lr_def)
  have cA: "tcert alg A" using As(3) Ar(3) by (auto simp: A_def tcert_def)
  from xq obtain xq0 where ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (?smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of ?R)) xq0"
    and rx: "bresult (unify_ops cfg vl) xq0 x"
    using c(9,10) e by (auto simp: pthm_of_def)
  have ns: "0 \<le> nprems_of ?R" "nprems_of ?R \<le> count_prems (th_prop ?lr)"
    using count_prems_nonneg nprems_lift_rule by (auto simp: nprems_of_def)
  have er: "0 < nprems_of ?R" if eres_flg
  proof (rule ccontr)
    assume "\<not> 0 < nprems_of ?R"
    with ns(1) have "nprems_of ?R = 0" by simp
    with ok that bicompose_aux_eres_no_prems show False by fastforce
  qed
  have mlr: "th_maxidx ?lr = th_maxidx ?R + inc" by (simp add: lift_rule_def Let_def inc_def)
  have inc0: "0 \<le> inc" using sm by (simp add: inc_def)
  text \<open>The proofs with the common typing.\<close>
  have Wsm: "W y = Ws y" if "snd y \<le> ?smax" for y using that by (simp add: W_def)
  have sv: "prf_valid alg ar W (Hs \<union> Hr) stpairs (zprf_tr sprf) (list_implies (Bs @ [Bi]) C)"
  proof (rule prf_valid_mono_H[OF prf_valid_cong_vars])
    show "prf_valid alg ar Ws Hs stpairs (zprf_tr sprf) (list_implies (Bs @ [Bi]) C)" using sv0 c(9,10) by simp
    show "\<forall>y\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> prf_vars (zprf_tr sprf). W y = Ws y"
    proof (intro ballI Wsm)
      fix y assume "y \<in> vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> prf_vars (zprf_tr sprf)"
      then show "snd y \<le> ?smax"
      proof
        assume "y \<in> vars_thm stpairs (list_implies (Bs @ [Bi]) C)"
        then show ?thesis using wt_thm_below[OF wS, of y] c(9,10) by simp
      next
        assume "y \<in> prf_vars (zprf_tr sprf)"
        then show ?thesis using zinv_prf_vars[OF sz0] by simp
      qed
    qed
  qed simp
  let ?As = "strip_imp_prems (th_prop ?R)" and ?B = "strip_imp_concl (th_prop ?R)"
  have cR: "cok (th_prop ?R)" using wR by (simp add: wt_thm_def)
  have PR: "th_prop ?R = list_implies ?As ?B" by (rule list_implies_strip_imp[OF cR])
  have wBi: "wt_term ar A W ?smax Bi propT"
    using wt_term_list_implies(1)[of ar A W ?smax "Bs @ [Bi]" C] c(5) by (simp add: wt_thm_def)
  have G: "wty W [] Bi propT"
    using wBi Slo c(10) by (auto simp: wt_term_def wty_def vars_thm_def vars_list_implies)
  obtain pG G0 where ls: "lsplit Bi = (pG, G0)" by (cases "lsplit Bi")
  have V2: "lift_venv (rev (lift_Ts [] Bi)) inc Wr W"
    unfolding lift_venv_def lift_Ts_lsplit[OF ls] using sm
    by (auto simp: W_def ls inc_def)
  have zr: "zconst_free rprf" "zprf_all zterm_ok ztyp_ok rprf"
    using rz0 Ar(4) by (auto simp: zinv_def elim!: zprf_all_mono intro: zterm_ok_zann ztyp_ok_zty)
  have wlr: "wt_term ar A W (th_maxidx ?lr) (th_prop ?lr) propT" using c(7) by (simp add: wt_thm_def)
  have plr: "th_prop ?lr = list_implies (map (lift_all inc Bi) ?As) (lift_all inc Bi ?B)"
    by (simp add: lift_rule_def Let_def inc_def c(11))
  have tGA: "\<forall>U\<in>tys Bi. tvars U \<subseteq> A" using wBi by (auto simp: wt_term_def tyA_def)
  have tG: "\<forall>U\<in>tys Bi. \<forall>(v, S)\<in>tvars U. 0 \<le> snd v" using tGA A0 by fastforce
  have wP: "\<forall>P\<in>set (map (lift_all inc Bi) ?As). wt_term ar A W (th_maxidx ?lr) P propT"
    using wt_term_list_implies(1)[OF wlr[unfolded plr]] .
  have tA: "\<forall>X\<in>set ?As. \<forall>U\<in>tys (lift_all inc Bi X). \<forall>(v, S)\<in>tvars U. 0 \<le> snd v"
    using wP A0 by (fastforce simp: wt_term_def tyA_def)
  have rv1: "\<exists>q. zlift_proof ztargs Bi inc (map (lift_all inc Bi) ?As) rprf = returnZ q \<and>
      prf_valid alg ar W Hr (map (\<lambda>(t, u). (lift_abs inc Bi t, lift_abs inc Bi u)) (th_tpairs ?R))
        (zprf_tr q) (list_implies (map (lift_all inc Bi) ?As) (lift_all inc Bi ?B))"
  proof (rule zprf_valid_lift[OF _ inc0 _ _ _ G V2 zr tG tA])
    show "\<forall>h\<in>Hr. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
      using hs hyp_ok_props by blast
    show "prf_valid alg ar Wr Hr (th_tpairs ?R) (zprf_tr rprf) (list_implies ?As ?B)" using rv0 PR by simp
    show "\<forall>(t, u)\<in>set (th_tpairs ?R). \<exists>T. wty Wr [] t T \<and> wty Wr [] u T"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set (th_tpairs ?R)"
      from wR tu obtain T where "wt_term ar Ar Wr (th_maxidx ?R) t T" "wt_term ar Ar Wr (th_maxidx ?R) u T"
        by (auto simp: wt_thm_def)
      moreover have "\<forall>v\<in>vars t. 0 \<le> snd v" "\<forall>v\<in>vars u. 0 \<le> snd v"
        using nn tu by (auto simp: vars_thm_def)
      ultimately show "\<exists>T. wty Wr [] t T \<and> wty Wr [] u T" by (auto simp: wt_term_def wty_def)
    qed
    show "wty Wr [] (list_implies ?As ?B) propT"
      using wR nn PR by (auto simp: wt_thm_def wt_term_def wty_def vars_thm_def)
  qed
  then obtain q where q: "zlift_proof ztargs Bi inc (map (lift_all inc Bi) ?As) rprf = returnZ q"
    and rv2: "prf_valid alg ar W Hr (th_tpairs ?lr) (zprf_tr q) (th_prop ?lr)"
    by (auto simp: lift_rule_def Let_def inc_def c(11))
  have rv: "prf_valid alg ar W (Hs \<union> Hr) (th_tpairs ?lr) (zprf_tr q) (th_prop ?lr)"
    by (rule prf_valid_mono_H[OF rv2]) blast
  have zl: "zlift_ok Ar (th_maxidx ?R) A (th_maxidx ?lr) inc"
    unfolding zlift_ok_def
  proof (intro conjI)
    show "\<forall>q\<in>Ar. 0 \<le> snd (fst q)" using Ar(4) by blast
    show "\<forall>q\<in>A. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> th_maxidx ?lr"
      using A0 c(3) sm rm mlr by (fastforce simp: inc_def)
    show "0 \<le> inc" by (rule inc0)
    show "incrA inc Ar \<subseteq> A" by (auto simp: incrA_def A_def inc_def)
    show "th_maxidx ?R + inc \<le> th_maxidx ?lr" by (simp add: mlr)
  qed
  have rzq: "zinv A W (th_maxidx ?lr) q \<and> zlb 0 q"
  proof (rule zinv_zlift_proof[OF q rz0 ri(2) zl])
    show "has_type W [] Bi propT" using G by (simp add: wty_def)
    show "\<forall>v\<in>vars Bi. 0 \<le> snd v \<and> snd v \<le> th_maxidx ?lr"
      using G wBi rm mlr by (fastforce simp: wty_def wt_term_def below_def inc_def)
    show "\<forall>U\<in>tys Bi. tvars U \<subseteq> A" by (rule tGA)
    show "lift_venv (rev (lift_Ts [] Bi)) inc Wr W" by (rule V2)
    show "\<forall>P\<in>set (map (lift_all inc Bi) ?As). has_type W [] P propT \<and>
        (\<forall>v\<in>vars P. 0 \<le> snd v \<and> snd v \<le> th_maxidx ?lr) \<and> (\<forall>U\<in>tys P. tvars U \<subseteq> A)"
    proof
      fix P assume P: "P \<in> set (map (lift_all inc Bi) ?As)"
      have "\<forall>v\<in>vars P. 0 \<le> snd v"
        using nnc P by (auto simp: plr vars_thm_def vars_list_implies)
      with wP P show "has_type W [] P propT \<and> (\<forall>v\<in>vars P. 0 \<le> snd v \<and> snd v \<le> th_maxidx ?lr) \<and>
          (\<forall>U\<in>tys P. tvars U \<subseteq> A)"
        by (fastforce simp: wt_term_def below_def tyA_def)
    qed
  qed
  have sz: "zinv A W ?smax sprf"
    by (rule zinv_mono[OF sz0]) (use Wsm zinv_prf_vars[OF sz0] in \<open>auto simp: A_def\<close>)
  have eS: "\<exists>vS. ok (full_prop_of (th_tpairs state) (th_prop state)) vS"
    by (rule full_prop_of_ok[of _ Ws]) (use wS in \<open>fastforce simp: wt_thm_def wt_term_def\<close>)
  have eR: "\<exists>vR. ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR"
    by (rule full_prop_of_ok[of _ W]) (use c(7) lr in \<open>fastforce simp: wt_thm_def wt_term_def\<close>)
  show ?thesis
  proof (rule exI[of _ q], intro conjI, goal_cases)
    show "zlift_proof ztargs Bi inc (map (lift_all inc Bi) ?As) rprf = returnZ q" by (rule q)
    show "\<exists>vS. ok (full_prop_of (th_tpairs state) (th_prop state)) vS" by (rule eS)
    show "\<exists>vR. ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR" by (rule eR)
  next
    case 4
    show ?case
    proof (intro allI impI)
    fix vS vR
    assume vS: "ok (full_prop_of (th_tpairs state) (th_prop state)) vS"
      and vR: "ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR"
      and ro: "zren_ok (br_newas x) ?smax (th_tpairs state) (th_prop state) (th_tpairs lr) (th_prop lr) sprf q"
    from ro[unfolded zren_ok_def lr c(9,10)] have hid: "\<forall>y\<in>prf_vars (zprf_tr q) - vars_thm (th_tpairs ?lr) (th_prop ?lr).
        ren_of (br_newas x) ?smax y = y \<and> y \<notin> ren_of (br_newas x) ?smax ` vars_thm (th_tpairs ?lr) (th_prop ?lr)"
      by blast
    have vS': "ok (full_prop_of stpairs (list_implies (Bs @ [Bi]) C)) vS" using vS c(9,10) by simp
    have vR': "ok (full_prop_of (th_tpairs ?lr) (th_prop ?lr)) vR" using vR lr by simp
    show "(\<exists>p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr ?smax q) \<bind>
        (\<lambda>rp. zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
          (na_oldAs (br_newas x)) (na_n (br_newas x))
          (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) [vS, vR] rp sprf) = returnZ p \<and>
      zthm_prf_inv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) p \<and> zlb 0 p) \<and>
      (\<forall>rp p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr (th_maxidx state) q) = returnZ rp \<longrightarrow>
        zbicompose_proof ztargs (br_env x) (th_maxidx state) True Bs (na_As (br_newas x)) (br_A x)
          (na_oldAs (br_newas x)) (na_n (br_newas x))
          (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) [vS, vR] rp sprf = returnZ p \<longrightarrow>
        (\<exists>Ar Wf. finite Ar \<and> scons Ar \<and> tcert alg Ar \<and> (\<forall>q\<in>Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> maxidx (br_env x)) \<and>
          (\<forall>x. tyA ar Ar (Wf x)) \<and> wt_thm ar Ar Wf (maxidx (br_env x)) (br_tpairs x) (br_prop x) \<and>
          prf_valid alg ar Wf (Hs \<union> Hr) (br_tpairs x) (zprf_tr p) (br_prop x) \<and> zinv Ar Wf (maxidx (br_env x)) p \<and>
          (\<not> env_is_empty (br_env x) \<longrightarrow> (\<exists>V PU. znorm_hyps (br_env x) [vS, vR] V Wf PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) \<and>
            (\<forall>U. PU U \<longrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> maxidx (br_env x))) \<and>
            znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) rp \<and>
            (\<not> above (br_env x) (th_maxidx state) \<longrightarrow> znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) sprf)))))"
      by (rule zbicompose_proof_valid[OF ok rx cfg c(1) c(5,6) c(7) _ c(2) _ c(4) ns er _ vl cA sm A0 nnc sv rv
            sz conjunct1[OF rzq] si(2) conjunct2[OF rzq] vS' vR' hid])
        (use c(3,8) in auto)
    qed
  qed
qed

end

text \<open>The value of a computation of a tight proof, if it returns.\<close>

definition valZ :: "'a Z \<Rightarrow> 'a \<Rightarrow> 'a" where
  "valZ m d = (case m of Some (ZOk x) \<Rightarrow> x | _ \<Rightarrow> d)"

lemma valZ_returnZ[simp]: "valZ (returnZ x) d = x"
  by (simp add: valZ_def returnZ_def)

lemma bindZ_returnZ[simp]: "bindZ (returnZ x) f = f x"
  by (simp add: bindZ_def returnZ_def)

end
