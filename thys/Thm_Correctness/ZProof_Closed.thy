section \<open>Closed tight proofs and their hypotheses\<close>

theory ZProof_Closed
  imports ZProof_Syntax
begin

text \<open>
  The terms of a tight proof refer only to bound variables of abstractions of the proof
  (\<open>znolb\<close>), and its hypotheses (\<open>zhyps\<close>) are the encodings of propositions. Lifting,
  normalisation and composition keep the first property and the hypotheses.
\<close>

subsection \<open>Loose bound variables\<close>

fun zloose :: "zterm \<Rightarrow> integer \<Rightarrow> bool" where
  "zloose (ZBound i) k \<longleftrightarrow> k \<le> i"
| "zloose (ZAbs a T t) k \<longleftrightarrow> zloose t (k + 1)"
| "zloose (ZApp t u) k \<longleftrightarrow> zloose t k \<or> zloose u k"
| "zloose _ k \<longleftrightarrow> False"

lemma zloose_mono: "\<not> zloose t k \<Longrightarrow> k \<le> k' \<Longrightarrow> \<not> zloose t k'"
  by (induction t arbitrary: k k') force+

lemma zloose_le: "zloose t k' \<Longrightarrow> k \<le> k' \<Longrightarrow> zloose t k"
  using zloose_mono by blast

lemma (in pure_sig) loose_bvar_zdec [simp]: "loose_bvar (zdec t) k = zloose t k"
  by (induction t arbitrary: k) (simp_all add: of_class_def)

lemma zloose_zcombound: "zloose (zcombound t n m) k \<longleftrightarrow> zloose t k \<or> (0 < m \<and> k < n + integer_of_nat m)"
proof (induction t n m rule: zcombound.induct)
  case (2 t n m)
  then show ?case by (auto simp: integer_arith)
qed simp

lemma zloose_zincr_bv:
  "\<not> zloose t k \<Longrightarrow> lev \<le> k \<Longrightarrow> 0 \<le> inc \<Longrightarrow> \<not> zloose (zincr_bv inc lev t) (k + inc)"
proof (induction inc lev t arbitrary: k rule: zincr_bv.induct)
  case (2 inc lev a T t)
  then show ?case using "2.IH"[of "k + 1"] by (simp add: algebra_simps)
qed (auto simp: integer_arith)

lemma zloose_zsubst_bound:
  "\<not> zloose t (lev + k + 1) \<Longrightarrow> \<not> zloose arg k \<Longrightarrow> 0 \<le> lev \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    \<not> zloose (zsubst_bound arg lev t) (lev + k)"
proof (induction arg lev t rule: zsubst_bound.induct)
  case (1 arg lev i)
  consider "i < lev" | "i = lev" | "lev < i" by fastforce
  then show ?case
  proof cases
    case 1
    then show ?thesis using "1.prems" by (simp add: integer_arith)
  next
    case 2
    show ?thesis
    proof (cases "lev = 0")
      case True
      then show ?thesis using 2 "1.prems" by (simp add: zincr_boundvars_def)
    next
      case False
      have "\<not> zloose (zincr_bv lev 0 arg) (k + lev)"
        by (rule zloose_zincr_bv[OF "1.prems"(2)]) (use "1.prems" in simp_all)
      with 2 False show ?thesis by (simp add: zincr_boundvars_def add.commute)
    qed
  next
    case 3
    then show ?thesis using "1.prems" by (simp add: integer_arith)
  qed
next
  case (2 arg lev a T t)
  then show ?case by (simp add: algebra_simps)
qed auto

lemma zloose_zsubst_boundD:
  "zloose (zsubst_bound arg lev t) (lev + k) \<Longrightarrow> \<not> zloose arg k \<Longrightarrow> 0 \<le> lev \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    zloose t (lev + k + 1)"
  using zloose_zsubst_bound by blast

lemma zloose_subst_term_bound:
  "\<not> zloose body (k + 1) \<Longrightarrow> \<not> zloose u k \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> zloose (subst_term_bound u body) k"
  using zloose_zsubst_bound[of body 0 k u] by (simp add: subst_term_bound_def add.commute)

lemma zloose_beta_norm_term:
  assumes "beta_norm_term t = Some t'"
  shows "0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose t' k"
  using assms
proof (induction t t' arbitrary: k rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn t t')
  note h = "1.hyps" and IH = "1.IH" and k = "1.prems"(1) and ok = "1.prems"(2)
  show ?case
  proof (cases t)
    case (ZAbs a T b)
    with h obtain b' where "bn b = Some b'" "t' = ZAbs a T b'" by (auto simp: bind_eq_Some_conv)
    with IH[of b b' "k + 1"] ok ZAbs k show ?thesis by auto
  next
    case (ZApp g u)
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbs b U body")
      case True
      then obtain b U body where g: "g = ZAbs b U body" by blast
      have "bn (subst_term_bound u body) = Some t'" using h ZApp g by simp
      moreover have "\<not> zloose (subst_term_bound u body) k"
        by (rule zloose_subst_term_bound) (use ok ZApp g k in simp_all)
      ultimately show ?thesis using IH k by blast
    next
      case False
      with h ZApp obtain nf where hf: "bn g = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some t'"
        by (cases g) (auto simp: bind_eq_Some_conv)
      have onf: "\<not> zloose nf k" using IH[OF hf k] ok ZApp by simp
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbs b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbs b U body" by blast
        have "bn (subst_term_bound u body) = Some t'" using rest nfb by simp
        moreover have "\<not> zloose (subst_term_bound u body) k"
          by (rule zloose_subst_term_bound) (use onf nfb ok ZApp k in simp_all)
        ultimately show ?thesis using IH k by blast
      next
        case False
        with rest obtain nu where hu: "bn u = Some nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        with IH[OF hu k] onf ok ZApp show ?thesis by simp
      qed
    qed
  qed (use h ok in auto)
qed

lemma zloose_zsubst_term:
  "\<not> zloose t k \<Longrightarrow> 0 \<le> k \<Longrightarrow> (\<And>v u. vf v = Some u \<Longrightarrow> \<not> zloose u 0) \<Longrightarrow> \<not> zloose (zsubst_term tf vf t) k"
proof (induction tf vf t arbitrary: k rule: zsubst_term.induct)
  case (1 tf vf x T)
  show ?case using "1.prems"(3)[of "(x, tf T)"] "1.prems"(2) by (auto split: option.splits dest: zloose_le)
qed auto

lemma zloose_zren_term [simp]: "zloose (zren_term r m t) k = zloose t k"
  by (induction r m t arbitrary: k rule: zren_term.induct) simp_all

lemma zloose_zlift_term:
  "\<not> zloose t k \<Longrightarrow> lev \<le> k \<Longrightarrow> \<not> zloose (zlift_term inc Ts lev t) (k + integer_of_nat (length Ts))"
proof (induction inc Ts lev t arbitrary: k rule: zlift_term.induct)
  case (1 inc Ts lev x i T)
  then show ?case by (auto simp: zloose_zcombound integer_arith)
next
  case (6 inc Ts lev x T t)
  then show ?case using "6.IH"[of "k + 1"] by (simp add: algebra_simps)
qed (auto simp: integer_arith)

lemma zloose_zlift_term':
  "\<not> zloose t k \<Longrightarrow> lev \<le> k \<Longrightarrow> \<not> zloose (zlift_term' inc Ts lev t) (k + integer_of_nat (length Ts))"
  by (auto simp: zlift_term'_def zloose_zlift_term dest: zloose_le)

lemma zloose_zlift_term'D:
  "zloose (zlift_term' inc Ts lev t) (k + integer_of_nat (length Ts)) \<Longrightarrow> lev \<le> k \<Longrightarrow> zloose t k"
  using zloose_zlift_term' by blast

context pure_sig
begin

lemma zloose_zterm_of: "zterm_of ta t = return z \<Longrightarrow> zloose z k = loose_bvar t k"
proof (induction ta t arbitrary: z k rule: zterm_of.induct)
  case (4 ta c T)
  then obtain Ts where "z = (case Ts of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Ts))"
    by (auto simp: Z_ok_simps return_def)
  then show ?case by (cases Ts rule: remdups_adj.cases) simp_all
next
  case (5 ta a T b)
  then show ?case by (auto simp: Z_ok_simps return_def)
next
  case (6 ta t u)
  show ?case
  proof (cases "match_of_class (t $ u)")
    case None
    with "6.prems" obtain zt zu where "zterm_of ta t = return zt" "zterm_of ta u = return zu" "z = ZApp zt zu"
      by (auto simp: Z_ok_simps return_def)
    with "6.IH"(1,2)[OF None] show ?thesis by (auto simp: return_def)
  next
    case (Some Tc)
    show ?thesis
    proof (cases "t $ u = mk_of_class (fst Tc) (snd Tc)")
      case True
      have "zterm_of ta (t $ u) = return (ZOfclass (ztyp_of (fst Tc)) (snd Tc))"
        by (subst zterm_of.simps) (simp only: Some option.case if_P[OF True])
      with "6.prems" have "z = ZOfclass (ztyp_of (fst Tc)) (snd Tc)" by simp
      with True show ?thesis by (simp add: mk_of_class_def)
    next
      case False
      with "6.prems" Some obtain zt zu where "zterm_of ta t = return zt" "zterm_of ta u = return zu" "z = ZApp zt zu"
        by (auto simp: Z_ok_simps return_def)
      with "6.IH"(3,4)[OF Some False] show ?thesis by (auto simp: return_def)
    qed
  qed
qed (auto simp: return_def)

end


subsection \<open>Proofs\<close>

fun znolb :: "integer \<Rightarrow> zproof \<Rightarrow> bool" where
  "znolb k (ZAbst a T p) \<longleftrightarrow> znolb (k + 1) p"
| "znolb k (ZAbsp a t p) \<longleftrightarrow> \<not> zloose t k \<and> znolb k p"
| "znolb k (ZAppt p t) \<longleftrightarrow> znolb k p \<and> \<not> zloose t k"
| "znolb k (ZAppp p q) \<longleftrightarrow> znolb k p \<and> znolb k q"
| "znolb k (ZConstp (c, instT, tab)) \<longleftrightarrow> (\<forall>x t. zv_lookup tab x = Some t \<longrightarrow> \<not> zloose t k)"
| "znolb k _ \<longleftrightarrow> True"

text \<open>The hypotheses of a tight proof:\<close>

fun zhyps :: "zproof \<Rightarrow> zterm set" where
  "zhyps (ZHyp t) = {t}"
| "zhyps (ZAbst a T p) = zhyps p"
| "zhyps (ZAbsp a t p) = zhyps p"
| "zhyps (ZAppt p t) = zhyps p"
| "zhyps (ZAppp p q) = zhyps p \<union> zhyps q"
| "zhyps _ = {}"

lemma znolb_mono: "znolb k p \<Longrightarrow> k \<le> k' \<Longrightarrow> znolb k' p"
  by (induction k p arbitrary: k' rule: znolb.induct) (auto dest: zloose_le)

lemma znolb_ZAppps: "znolb k (ZAppps p qs) \<longleftrightarrow> znolb k p \<and> (\<forall>q\<in>set qs. znolb k q)"
  unfolding ZAppps_def by (induction qs arbitrary: p) auto

lemma znolb_ZAppts: "znolb k (ZAppts p ts) \<longleftrightarrow> znolb k p \<and> (\<forall>t\<in>set ts. \<not> zloose t k)"
  unfolding ZAppts_def by (induction ts arbitrary: p) auto

lemma znolb_ZAbsps: "znolb k (ZAbsps ts p) \<longleftrightarrow> (\<forall>t\<in>set ts. \<not> zloose t k) \<and> znolb k p"
  by (induction ts) (auto simp: ZAbsps_def)

lemma zhyps_ZAppps: "zhyps (ZAppps p qs) = zhyps p \<union> (\<Union>q\<in>set qs. zhyps q)"
  unfolding ZAppps_def by (induction qs arbitrary: p) auto

lemma zhyps_ZAppts [simp]: "zhyps (ZAppts p ts) = zhyps p"
  unfolding ZAppts_def by (induction ts arbitrary: p) auto

lemma zhyps_ZAbsps [simp]: "zhyps (ZAbsps ts p) = zhyps p"
  by (induction ts) (auto simp: ZAbsps_def)

lemma znolb_map_zproof:
  "map_zproof tf tm p = return p' \<Longrightarrow> zconsts_ok p \<Longrightarrow>
    (\<And>t t' k. tm t = return t' \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose t' k) \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    znolb k p \<Longrightarrow> znolb k p'"
proof (induction p arbitrary: p' k)
  case (ZConstp c)
  obtain a instT tab where c: "c = (a, instT, tab)" by (cases c)
  from ZConstp.prems(1) obtain ins' where mi: "map_insts tf tm (instT, tab) = return ins'"
    and q: "p' = ZConstp (a, ins')" by (auto simp: c bindZ_eq_returnZ)
  obtain instT' tab' where i: "ins' = (instT', tab')" by (cases ins')
  have ok: "ztab_names_ok tab" using ZConstp.prems(2) by (simp add: c)
  have "\<not> zloose t' k" if "zv_lookup tab' x = Some t'" for x t'
    using map_insts_values[OF mi[unfolded i] ok that] ZConstp.prems(3-5) by (fastforce simp: c)
  then show ?case by (simp add: q i)
qed (auto simp: bindZ_eq_returnZ)

lemma zhyps_map_zproof: "map_zproof tf tm p = return p' \<Longrightarrow> zhyps p' = zhyps p"
  by (induction p arbitrary: p') (auto simp: bindZ_eq_returnZ)

lemma znolb_zsubst_proof_bound:
  "znolb (lev + k + 1) p \<Longrightarrow> \<not> zloose arg k \<Longrightarrow> 0 \<le> lev \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    znolb (lev + k) (zsubst_proof_bound arg lev p)"
proof (induction arg lev p rule: zsubst_proof_bound.induct)
  case (2 arg lev a T p)
  then show ?case by (simp add: algebra_simps)
qed (auto dest: zloose_zsubst_boundD)

lemma znolb_subst_proof_bound:
  "znolb (k + 1) body \<Longrightarrow> \<not> zloose u k \<Longrightarrow> 0 \<le> k \<Longrightarrow> znolb k (subst_proof_bound u body)"
  using znolb_zsubst_proof_bound[of 0 k body u] by (simp add: subst_proof_bound_def add.commute)

lemma zhyps_zsubst_proof_bound [simp]: "zhyps (zsubst_proof_bound arg lev p) = zhyps p"
  by (induction arg lev p rule: zsubst_proof_bound.induct) auto

lemma zhyps_subst_proof_bound [simp]: "zhyps (subst_proof_bound u p) = zhyps p"
  by (simp add: subst_proof_bound_def)

lemma beta_norm_prooft_closed:
  assumes "beta_norm_prooft p = Some p'"
  shows "(0 \<le> k \<longrightarrow> znolb k p \<longrightarrow> znolb k p') \<and> zhyps p' \<subseteq> zhyps p"
  using assms
proof (induction p p' arbitrary: k rule: beta_norm_prooft.raw_induct[rotated, consumes 1])
  case (1 bn p p')
  note h = "1.hyps" and IH = "1.IH"
  show ?case
  proof (cases p)
    case (ZAbst a T q)
    with h obtain q' where "bn q = Some q'" "p' = ZAbst a T q'" by (auto simp: bind_eq_Some_conv)
    with IH[of q q' "k + 1"] ZAbst show ?thesis by auto
  next
    case (ZAppt g u)
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbst b U body")
      case True
      then obtain b U body where g: "g = ZAbst b U body" by blast
      have b: "bn (subst_proof_bound u body) = Some p'" using h ZAppt g by simp
      have "znolb k p'" if "0 \<le> k" "znolb k p"
      proof -
        have "znolb k (subst_proof_bound u body)"
          by (rule znolb_subst_proof_bound) (use that ZAppt g in simp_all)
        with IH[OF b, of k] that(1) show ?thesis by blast
      qed
      moreover have "zhyps p' \<subseteq> zhyps p" using IH[OF b, of k] ZAppt g by simp
      ultimately show ?thesis by blast
    next
      case False
      with h ZAppt obtain nf where hf: "bn g = Some nf"
        and rest: "(case nf of ZAbst _ _ body \<Rightarrow> bn (subst_proof_bound u body)
          | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZAppt nf nu))) = Some p'"
        by (cases g) (auto simp: bind_eq_Some_conv)
      note IHf = IH[OF hf]
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbst b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbst b U body" by blast
        have b: "bn (subst_proof_bound u body) = Some p'" using rest nfb by simp
        have "znolb k p'" if "0 \<le> k" "znolb k p"
        proof -
          have "znolb k nf" using IHf[of k] that ZAppt by simp
          then have "znolb k (subst_proof_bound u body)"
            by (intro znolb_subst_proof_bound) (use that ZAppt nfb in simp_all)
          with IH[OF b, of k] that(1) show ?thesis by blast
        qed
        moreover have "zhyps p' \<subseteq> zhyps p" using IH[OF b, of k] IHf[of k] ZAppt nfb by auto
        ultimately show ?thesis by blast
      next
        case False
        with rest obtain nu where hu: "beta_norm_term u = Some nu" and p': "p' = ZAppt nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        with zloose_beta_norm_term[OF hu] IHf[of k] ZAppt show ?thesis by auto
      qed
    qed
  qed (use h in auto)
qed

lemma znolb_zlift_prf:
  "zlift_prf inc Ts lev p = return q \<Longrightarrow> zconsts_ok p \<Longrightarrow> znolb k p \<Longrightarrow> lev \<le> k \<Longrightarrow>
    znolb (k + integer_of_nat (length Ts)) q"
proof (induction p arbitrary: lev q k)
  case (ZConstp c)
  obtain a instT tab where c: "c = (a, instT, tab)" by (cases c)
  from ZConstp.prems(1) obtain ins' where
    mi: "map_insts (zincr_tvar inc) (\<lambda>t. return (zlift_term' inc Ts lev t)) (instT, tab) = return ins'"
    and q: "q = ZConstp (a, ins')" by (auto simp: c bindZ_eq_returnZ)
  obtain instT' tab' where i: "ins' = (instT', tab')" by (cases ins')
  have ok: "ztab_names_ok tab" using ZConstp.prems(2) by (simp add: c)
  have "\<not> zloose t' (k + integer_of_nat (length Ts))" if "zv_lookup tab' x = Some t'" for x t'
    using map_insts_values[OF mi[unfolded i] ok that] ZConstp.prems(3,4)
    by (auto simp: c dest: zloose_zlift_term'D)
  then show ?case by (simp add: q i)
next
  case (ZAbst a T p)
  from ZAbst.prems(1) obtain x where x: "zlift_prf inc Ts (lev + 1) p = return x" "q = ZAbst a (zincr_tvar inc T) x"
    by (auto simp: bindZ_eq_returnZ)
  have "znolb (k + 1 + integer_of_nat (length Ts)) x" by (rule ZAbst.IH[OF x(1)]) (use ZAbst.prems in simp_all)
  then show ?case by (simp add: x(2) algebra_simps)
qed (auto simp: bindZ_eq_returnZ dest: zloose_zlift_term'D)

lemma zhyps_zlift_prf: "zlift_prf inc Ts lev p = return q \<Longrightarrow> zhyps q = zhyps p"
  by (induction p arbitrary: lev q) (auto simp: bindZ_eq_returnZ)

lemma spine_closed:
  "b < k \<Longrightarrow> znolb k p \<Longrightarrow> fst (snd (foldr zmk_app bs (a, b, p))) \<le> b \<and>
    znolb k (snd (snd (foldr zmk_app bs (a, b, p)))) \<and> zhyps (snd (snd (foldr zmk_app bs (a, b, p)))) = zhyps p"
  by (induction bs) (auto simp: zmk_app_def split: prod.splits)

lemma zlift_leaf_closed:
  "do {p \<leftarrow> zlift_prf inc (rev Ts) 0 pf;
      return (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))} = return q \<Longrightarrow>
    zconsts_ok pf \<Longrightarrow> znolb 0 pf \<Longrightarrow> j = integer_of_nat (length Ts) \<Longrightarrow> znolb j q \<and> zhyps q \<subseteq> zhyps pf"
proof -
  assume h: "do {p \<leftarrow> zlift_prf inc (rev Ts) 0 pf;
      return (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i)))} = return q"
    and zc: "zconsts_ok pf" and n: "znolb 0 pf" and j: "j = integer_of_nat (length Ts)"
  from h obtain p where p: "zlift_prf inc (rev Ts) 0 pf = return p"
    and q: "q = ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i))"
    by (auto simp: bindZ_eq_returnZ)
  have "znolb j p" using znolb_zlift_prf[OF p zc n] j by simp
  moreover have "zhyps p = zhyps pf" by (rule zhyps_zlift_prf[OF p])
  moreover have "znolb j (snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k')))) \<and>
      zhyps (snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k')))) = {}" for k'
    using spine_closed[of "j - 1" j "ZBoundp k'" bs "i - 1"] by simp
  ultimately show ?thesis by (auto simp: q znolb_ZAppps zhyps_ZAppps)
qed

context pure_sig
begin

lemma zlift_prems_closed:
  "zlift_prems ztargs inc k pf Ts bs i j G = return q \<Longrightarrow> zconsts_ok pf \<Longrightarrow> znolb 0 pf \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow> \<not> loose_bvar G j \<Longrightarrow> znolb j q \<and> zhyps q \<subseteq> zhyps pf"
proof (induction ztargs inc k pf Ts bs i j G arbitrary: q rule: zlift_prems.induct)
  case (1 inc k pf Ts bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with "1.prems"(1) obtain A' p where A': "zterm_of ztargs A = return A'"
      and p: "zlift_prems ztargs inc k pf Ts (True # bs) (i + 1) j B = return p" and q: "q = ZAbsp (STR ''H'') A' p"
      by (auto simp: bindZ_eq_returnZ)
    have "znolb j p \<and> zhyps p \<subseteq> zhyps pf" by (rule "1.hyps"(1)[OF True A' p]) (use "1.prems" in simp_all)
    moreover have "\<not> zloose A' j" using zloose_zterm_of[OF A'] "1.prems"(5) by simp
    ultimately show ?thesis by (simp add: q)
  next
    case False
    with "1.prems" show ?thesis by (intro zlift_leaf_closed) simp_all
  qed
next
  case (2 inc k pf Ts bs i j c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with "2.prems"(1) obtain p where p: "zlift_prems ztargs inc k pf (ztyp_of T # Ts) (False # bs) i (j + 1) t = return p"
      and q: "q = ZAbst a (ztyp_of T) p"
      by (auto simp: bindZ_eq_returnZ)
    have "znolb (j + 1) p \<and> zhyps p \<subseteq> zhyps pf"
      by (rule "2.hyps"(1)[OF True p]) (use "2.prems" in \<open>simp_all add: integer_arith\<close>)
    then show ?thesis by (simp add: q)
  next
    case False
    with "2.prems" show ?thesis by (intro zlift_leaf_closed) simp_all
  qed
qed (rule zlift_leaf_closed; simp)+

theorem zlift_proof_closed:
  assumes "zlift_proof ztargs G inc prems pf = return q" "zconsts_ok pf" "znolb 0 pf" "closed G"
    "\<forall>A\<in>set prems. closed A"
  shows "znolb 0 q" "zhyps q \<subseteq> zhyps pf"
proof -
  from assms(1) obtain As p where As: "list_all2 (\<lambda>A z. zterm_of ztargs A = return z) prems As"
    and p: "zlift_prems ztargs inc (integer_of_nat (length prems)) pf [] [] 0 0 G = return p"
    and q: "q = ZAbsps As p"
    by (auto simp: zlift_proof_def bindZ_eq_returnZ mapZ_eq_returnZ)
  have "\<forall>z\<in>set As. \<not> zloose z 0"
  proof
    fix z assume "z \<in> set As"
    from list_all2_ex2[OF As this] obtain A where "A \<in> set prems" "zterm_of ztargs A = return z" by blast
    with assms(5) zloose_zterm_of show "\<not> zloose z 0" by (auto simp: closed_def)
  qed
  moreover have "znolb 0 p \<and> zhyps p \<subseteq> zhyps pf"
    by (rule zlift_prems_closed[OF p assms(2,3)]) (use assms(4) in \<open>simp_all add: closed_def\<close>)
  ultimately show "znolb 0 q" "zhyps q \<subseteq> zhyps pf" by (simp_all add: q znolb_ZAbsps)
qed

end


subsection \<open>Normalisation\<close>

context prf_sig
begin

lemma zloose_znorm_term_aux:
  assumes "znorm_term_aux x = Some r"
  shows "r = Ok t' \<Longrightarrow> snd (fst x) = env \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> closed_env env \<Longrightarrow>
    \<forall>k\<ge>0. \<not> zloose (snd x) k \<longrightarrow> \<not> zloose t' k"
  using assms
proof (induction x r arbitrary: t' rule: znorm_term_aux.raw_induct[rotated, consumes 1])
  case (1 nt x r)
  let ?\<theta> = "tyenv env"
  note r = "1.prems"(1) and E = "1.prems"(2) and tac = "1.prems"(3) and ce = "1.prems"(4)
  obtain ta t where x: "x = ((ta, env), t)" using E by (metis prod.collapse)
  have h: "(case t of
      ZVar xi T \<Rightarrow> do {
        r \<leftarrow> zlookup ta env xi T;
        case r of
          Some u \<Rightarrow> nt ((ta, env), u)
        | None \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; return (ZVar xi T')}}
    | ZConst1 a T \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; return (ZConst1 a T')}
    | ZConst a Ts \<Rightarrow> do {Ts' \<leftarrow> mapM (znorm_type ?\<theta>) Ts; return (ZConst a Ts')}
    | ZAbs a T b \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; b' \<leftarrow> nt ((ta, env), b); return (ZAbs a T' b')}
    | ZApp g u \<Rightarrow>
        (case g of
          ZAbs _ _ body \<Rightarrow> nt ((ta, env), subst_term_bound u body)
        | _ \<Rightarrow> do {
            nf \<leftarrow> nt ((ta, env), g);
            case nf of
              ZAbs _ _ body \<Rightarrow> nt ((ta, env), subst_term_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> nt ((ta, env), u); return (ZApp nf nu)}})
    | ZOfclass T c \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; return (ZOfclass T' c)}
    | t \<Rightarrow> return t) = return t'"
    using "1.hyps" r unfolding x prod.sel by (simp add: return_def)
  have IH: "\<not> zloose u' k" if "nt ((ta, env), u) = return u'" "0 \<le> k" "\<not> zloose u k" for u u' k
  proof -
    have "snd (fst ((ta, env), u)) = env" by simp
    from "1.IH"[OF that(1)[unfolded return_def] HOL.refl this tac ce] that(2,3) show ?thesis by simp
  qed
  have "\<not> zloose t' k" if k: "0 \<le> k" and ok: "\<not> zloose t k" for k
  proof (cases t)
    case (ZVar xi T)
    from h ZVar obtain lr where lk: "zlookup ta env xi T = return lr"
      and rest: "(case lr of Some u \<Rightarrow> nt ((ta, env), u)
        | None \<Rightarrow> bindM (znorm_type ?\<theta> T) (\<lambda>T'. return (ZVar xi T'))) = return t'"
      by (auto simp: bindZ_eq_returnZ)
    from lk tac show ?thesis
    proof (cases rule: zlookup_success)
      case None
      with rest show ?thesis by (auto simp: bindZ_eq_returnZ)
    next
      case (Some U u u')
      have "closed u" using ce Some(1) unfolding closed_env_def by blast
      then have "\<not> zloose u' 0" using zloose_zterm_of[OF Some(3)] by (simp add: closed_def)
      then have "\<not> zloose u' k" using k by (rule zloose_mono)
      moreover have "nt ((ta, env), u') = return t'" using rest Some(2) by simp
      ultimately show ?thesis using IH k by blast
    qed
  next
    case (ZAbs a T b)
    with h obtain T' b' where "nt ((ta, env), b) = return b'" "t' = ZAbs a T' b'"
      by (auto simp: bindZ_eq_returnZ)
    with IH[of b b' "k + 1"] ok ZAbs k show ?thesis by simp
  next
    case (ZApp g u)
    have og: "\<not> zloose g k" and ou: "\<not> zloose u k" using ok ZApp by simp_all
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbs b U body")
      case True
      then obtain b U body where g: "g = ZAbs b U body" by blast
      have "nt ((ta, env), subst_term_bound u body) = return t'" using h ZApp g by simp
      moreover have "\<not> zloose (subst_term_bound u body) k"
        by (rule zloose_subst_term_bound) (use og ou g k in simp_all)
      ultimately show ?thesis using IH k by blast
    next
      case False
      with h ZApp obtain nf where hf: "nt ((ta, env), g) = return nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> nt ((ta, env), subst_term_bound u body)
          | _ \<Rightarrow> bindM (nt ((ta, env), u)) (\<lambda>nu. return (ZApp nf nu))) = return t'"
        by (cases g) (auto simp: bindZ_eq_returnZ)
      have onf: "\<not> zloose nf k" by (rule IH[OF hf k og])
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbs b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbs b U body" by blast
        have "nt ((ta, env), subst_term_bound u body) = return t'" using rest nfb by simp
        moreover have "\<not> zloose (subst_term_bound u body) k"
          by (rule zloose_subst_term_bound) (use onf ou nfb k in simp_all)
        ultimately show ?thesis using IH k by blast
      next
        case False
        with rest obtain nu where hu: "nt ((ta, env), u) = return nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bindZ_eq_returnZ)
        with IH[OF hu k ou] onf show ?thesis by simp
      qed
    qed
  qed (use h ok in \<open>auto simp: bindZ_eq_returnZ\<close>)
  then show ?case unfolding x by simp
qed

theorem zloose_znorm_term:
  assumes "znorm_term ta env t = return t'" "tacyc (tyenv env)" "closed_env env" "0 \<le> k" "\<not> zloose t k"
  shows "\<not> zloose t' k"
proof (cases "env_is_empty env")
  case True
  with assms(1) have "beta_norm_term t = Some t'" by (simp add: znorm_term_def liftOZ_eq_returnZ)
  from zloose_beta_norm_term[OF this assms(4,5)] show ?thesis .
next
  case False
  with assms(1) have "znorm_term_aux ((ta, env), t) = Some (Ok t')" by (simp add: znorm_term_def return_def)
  from zloose_znorm_term_aux[OF this HOL.refl _ assms(2,3)] assms(4,5) show ?thesis by simp
qed

theorem znorm_proof_closed:
  assumes nz: "znorm_proof ztargs env vis q = return r" and zc: "zconsts_ok q"
    and tac: "tacyc (tyenv env)" and ce: "closed_env env"
  shows "znolb 0 q \<Longrightarrow> znolb 0 r" "zhyps r \<subseteq> zhyps q"
proof -
  have "(znolb 0 q \<longrightarrow> znolb 0 r) \<and> zhyps r \<subseteq> zhyps q"
  proof (cases "env_is_empty env \<or> vis = []")
    case True
    with nz have "beta_norm_prooft q = Some r" by (auto simp: znorm_proof_def liftOZ_eq_returnZ)
    from beta_norm_prooft_closed[OF this, of 0] show ?thesis by simp
  next
    case False
    then obtain ityp lk m where
      m: "map_zproof ityp (\<lambda>t. if zvars_all (\<lambda>(x, T). \<not> Option.is_none (lk (x, ityp T)) \<or> Option.is_none (vt_lookup (tenv env) x)) t
          then liftOZ (beta_norm_term (zsubst_term ityp lk t))
          else raise (ZExn (Term_Error STR ''norm_proof: variable bound by the environment is not visible'' []))) q = return m"
      and bn: "beta_norm_prooft m = Some r"
      and lkc: "\<And>v u. lk v = Some u \<Longrightarrow> \<not> zloose u 0"
    proof -
      let ?\<theta> = "tyenv env" and ?VT = "visible_tvars vis" and ?VV = "visible_vars vis"
      define ityp where "ityp instT = (case instT of None \<Rightarrow> id
        | Some xs \<Rightarrow> if List.null xs then id else zsubst_type (map_of xs))" for instT :: "((indexname \<times> psort) \<times> ztyp) list option"
      obtain instT us m where
        us: "mapM (\<lambda>(a, T). znorm_term ztargs env (ZVar a T))
          (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) = return us"
        and m: "map_zproof (ityp instT) (\<lambda>t.
          if zvars_all (\<lambda>(x, T). \<not> Option.is_none (zlookup_var (zip (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) us)
              (x, ityp instT T)) \<or> Option.is_none (vt_lookup (tenv env) x)) t
          then liftOZ (beta_norm_term (zsubst_term (ityp instT)
            (zlookup_var (zip (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) us)) t))
          else raise (ZExn (Term_Error STR ''norm_proof: variable bound by the environment is not visible'' []))) q = return m"
        and bn: "beta_norm_prooft m = Some r"
        using nz False unfolding znorm_proof_def Let_def ityp_def
        by (auto simp: bindZ_eq_returnZ liftOZ_eq_returnZ)
      define vs where "vs = zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)"
      have us': "list_all2 (\<lambda>v u. \<not> zloose u 0) vs us"
        using us unfolding vs_def[symmetric] mapZ_eq_returnZ
      proof (rule list.rel_mono_strong)
        fix v u assume z: "(case v of (a, T) \<Rightarrow> znorm_term ztargs env (ZVar a T)) = return u"
        obtain a T where va: "v = (a, T)" by (cases v)
        from z va have "znorm_term ztargs env (ZVar a T) = return u" by simp
        from zloose_znorm_term[OF this tac ce] show "\<not> zloose u 0" by simp
      qed
      have "\<not> zloose u 0" if "zlookup_var (zip vs us) v = Some u" for v u
        using zlookup_var_zip_Some[OF us' that] by blast
      with m bn show thesis unfolding vs_def by (intro that) auto
    qed
    have "znolb 0 m" if "znolb 0 q"
    proof (rule znolb_map_zproof[OF m zc _ _ that])
      fix t t' k assume tt: "(if zvars_all (\<lambda>(x, T). \<not> Option.is_none (lk (x, ityp T)) \<or> Option.is_none (vt_lookup (tenv env) x)) t
          then liftOZ (beta_norm_term (zsubst_term ityp lk t))
          else raise (ZExn (Term_Error STR ''norm_proof: variable bound by the environment is not visible'' []))) = return t'"
        and k: "0 \<le> k" and ok: "\<not> zloose t k"
      from tt have bt: "beta_norm_term (zsubst_term ityp lk t) = Some t'"
        by (auto simp: liftOZ_eq_returnZ split: if_splits)
      have "\<not> zloose (zsubst_term ityp lk t) k" by (rule zloose_zsubst_term[OF ok k lkc])
      from zloose_beta_norm_term[OF bt k this] show "\<not> zloose t' k" .
    qed simp
    moreover have "zhyps m = zhyps q" by (rule zhyps_map_zproof[OF m])
    ultimately show ?thesis using beta_norm_prooft_closed[OF bn, of 0] by auto
  qed
  then show "znolb 0 q \<Longrightarrow> znolb 0 r" "zhyps r \<subseteq> zhyps q" by blast+
qed

end


subsection \<open>Composition\<close>

lemma zhyps_zimp_prf [simp]: "zhyps (zimp_prf A i m) = {}"
  by (induction A i m rule: zimp_prf.induct) auto

lemma zhyps_zmk_asm_prf [simp]: "zhyps (zmk_asm_prf C i m) = {}"
proof -
  have "zhyps (zall_prf i m A) = {}" for A by (induction i m A rule: zall_prf.induct) auto
  then show ?thesis by (simp add: zmk_asm_prf_def)
qed

lemma zhyps_zflatten_params_proof [simp]: "zhyps (zflatten_params_proof i j n x) = {}"
  by (induction i j n x rule: zflatten_params_proof.induct) (auto simp: zhyps_ZAppps)

lemma zimp_prf_closed: "\<not> zloose A k \<Longrightarrow> znolb k (zimp_prf A i m) \<and> zhyps (zimp_prf A i m) = {}"
  by (induction A i m rule: zimp_prf.induct) auto

lemma zmk_asm_prf_closed: "\<not> zloose C k \<Longrightarrow> znolb k (zmk_asm_prf C i m) \<and> zhyps (zmk_asm_prf C i m) = {}"
proof -
  have "\<not> zloose A k \<Longrightarrow> znolb k (zall_prf i m A) \<and> zhyps (zall_prf i m A) = {}" for A
    by (induction i m A arbitrary: k rule: zall_prf.induct) (auto simp: zimp_prf_closed)
  then show "\<not> zloose C k \<Longrightarrow> znolb k (zmk_asm_prf C i m) \<and> zhyps (zmk_asm_prf C i m) = {}"
    by (simp add: zmk_asm_prf_def)
qed

lemma downto_le: "x \<in> set (downto a b) \<Longrightarrow> x \<le> a"
proof (induction a b rule: downto.induct)
  case (1 a b)
  show ?case
  proof (cases "a < b")
    case True
    with "1.prems" show ?thesis by (subst (asm) downto.simps) simp
  next
    case False
    with "1.prems" have "x = a \<or> x \<in> set (downto (a - 1) b)" by (subst (asm) downto.simps) simp
    with "1.IH"[OF False] show ?thesis by (auto simp: integer_arith)
  qed
qed

lemma zflatten_params_proof_closed:
  "\<not> zloose (fst x) k \<Longrightarrow> j \<le> k \<Longrightarrow> znolb k (zflatten_params_proof i j n x) \<and> zhyps (zflatten_params_proof i j n x) = {}"
proof (induction i j n x arbitrary: k rule: zflatten_params_proof.induct)
  case (2 i j n c U a T t k')
  then show ?case by (auto simp: znolb_ZAppps znolb_ZAppts zhyps_ZAppps integer_arith dest!: downto_le)
qed (auto simp: znolb_ZAppps znolb_ZAppts zhyps_ZAppps integer_arith dest!: downto_le)

context prf_sig
begin

lemma zbicompose_core_closed:
  assumes c: "zbicompose_core ztargs env flatten Bs As A oldAs n m vis p q = return r"
    and tac: "tacyc (tyenv env)" and ce: "closed_env env"
    and cl: "\<forall>t\<in>set (Bs @ As @ oldAs). closed t" "\<forall>C. A = Some C \<longrightarrow> closed C"
  shows "znolb 0 p \<Longrightarrow> znolb 0 q \<Longrightarrow> znolb 0 r" "zhyps r \<subseteq> zhyps p \<union> zhyps q"
proof -
  let ?normt = "\<lambda>t. bindM (zterm_of ztargs t) (znorm_term ztargs env)"
  obtain Ns asm Os ks fs where Ns: "mapM ?normt (Bs @ As) = return Ns"
    and asm: "(if n > 0 then (case A of None \<Rightarrow> raise ZOption
        | Some C \<Rightarrow> bindM (?normt C) (\<lambda>C'. return [zmk_asm_prf C' n (zasm_count m C)])) else return []) = return asm"
    and Os: "mapM (zterm_of ztargs) oldAs = return Os"
    and ks: "liftMZ (zip_eq Os (downto (integer_of_nat (length As) - 1) 0)) = return ks"
    and fs: "(if flatten then mapM (\<lambda>x. znorm_proof ztargs env vis (zflatten_params_proof 0 0 n x)) ks
        else return (map (\<lambda>x. ZBoundp (snd x)) ks)) = return fs"
    and r: "r = ZAbsps Ns (ZAppp (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As))))) (ZAppps p (asm @ fs)))"
    using c unfolding zbicompose_core_def Let_def by (auto simp: bindZ_eq_returnZ)
  have normt: "\<not> zloose t' 0" if "?normt t = return t'" "closed t" for t t'
  proof -
    from that(1) obtain z where z: "zterm_of ztargs t = return z" "znorm_term ztargs env z = return t'"
      by (auto simp: bindZ_eq_returnZ)
    have "\<not> zloose z 0" using zloose_zterm_of[OF z(1)] that(2) by (simp add: closed_def)
    from zloose_znorm_term[OF z(2) tac ce _ this] show ?thesis by simp
  qed
  have N: "\<forall>t'\<in>set Ns. \<not> zloose t' 0"
  proof
    fix t' assume "t' \<in> set Ns"
    from list_all2_ex2[OF Ns[unfolded mapZ_eq_returnZ] this] obtain t where "t \<in> set (Bs @ As)" "?normt t = return t'"
      by blast
    with normt cl(1) show "\<not> zloose t' 0" by auto
  qed
  have a: "\<forall>a\<in>set asm. znolb 0 a \<and> zhyps a = {}"
  proof (cases "0 < n")
    case True
    with asm obtain C C' where "A = Some C" "?normt C = return C'" "asm = [zmk_asm_prf C' n (zasm_count m C)]"
      by (auto simp: bindZ_eq_returnZ split: option.splits)
    with normt cl(2) show ?thesis by (auto simp: zmk_asm_prf_closed)
  next
    case False
    with asm show ?thesis by simp
  qed
  have f: "\<forall>f\<in>set fs. znolb 0 f \<and> zhyps f = {}"
  proof -
    have kO: "\<forall>x\<in>set ks. \<not> zloose (fst x) 0"
    proof
      fix x assume x: "x \<in> set ks"
      from ks have "ks = zip Os (downto (integer_of_nat (length As) - 1) 0)"
        by (auto simp: liftMZ_eq_returnZ dest: ok_zip_eq_D)
      with x have "(fst x, snd x) \<in> set (zip Os (downto (integer_of_nat (length As) - 1) 0))" by simp
      then have "fst x \<in> set Os" by (rule set_zip_leftD)
      from list_all2_ex2[OF Os[unfolded mapZ_eq_returnZ] this] obtain B0 where "B0 \<in> set oldAs" "zterm_of ztargs B0 = return (fst x)"
        by blast
      with cl(1) zloose_zterm_of show "\<not> zloose (fst x) 0" by (auto simp: closed_def)
    qed
    show ?thesis
    proof (cases flatten)
      case True
      show ?thesis
      proof
        fix f assume "f \<in> set fs"
        from list_all2_ex2[OF fs[unfolded if_P[OF True] mapZ_eq_returnZ] this] obtain x where
          x: "x \<in> set ks" and fx: "znorm_proof ztargs env vis (zflatten_params_proof 0 0 n x) = return f" by blast
        have fl: "znolb 0 (zflatten_params_proof 0 0 n x) \<and> zhyps (zflatten_params_proof 0 0 n x) = {}"
          by (rule zflatten_params_proof_closed) (use kO x in simp_all)
        note nf = znorm_proof_closed[OF fx zconsts_ok_zflatten_params_proof tac ce]
        show "znolb 0 f \<and> zhyps f = {}" using nf fl by auto
      qed
    next
      case False
      with fs show ?thesis by auto
    qed
  qed
  show "znolb 0 p \<Longrightarrow> znolb 0 q \<Longrightarrow> znolb 0 r"
    using N a f by (auto simp: r znolb_ZAbsps znolb_ZAppps)
  show "zhyps r \<subseteq> zhyps p \<union> zhyps q"
    using a f by (auto simp: r zhyps_ZAppps)
qed

theorem zbicompose_proof_closed:
  assumes c: "zbicompose_proof ztargs env smax flatten Bs As A oldAs n m vis rprf sprf = return r"
    and zc: "zconsts_ok rprf" "zconsts_ok sprf" and tac: "tacyc (tyenv env)" and ce: "closed_env env"
    and cl: "\<forall>t\<in>set (Bs @ As @ oldAs). closed t" "\<forall>C. A = Some C \<longrightarrow> closed C"
  shows "znolb 0 rprf \<Longrightarrow> znolb 0 sprf \<Longrightarrow> znolb 0 r" "zhyps r \<subseteq> zhyps rprf \<union> zhyps sprf"
proof -
  have "((znolb 0 rprf \<and> znolb 0 sprf) \<longrightarrow> znolb 0 r) \<and> zhyps r \<subseteq> zhyps rprf \<union> zhyps sprf"
  proof (cases "env_is_empty env")
    case True
    with c have "zbicompose_core ztargs env flatten Bs As A oldAs n m vis rprf sprf = return r"
      by (simp add: zbicompose_proof_def)
    from zbicompose_core_closed[OF this tac ce cl] show ?thesis by blast
  next
    case False
    with c obtain rprf' sprf' where r': "znorm_proof ztargs env vis rprf = return rprf'"
      and s': "(if above env smax then return sprf else znorm_proof ztargs env vis sprf) = return sprf'"
      and cc: "zbicompose_core ztargs env flatten Bs As A oldAs n m vis rprf' sprf' = return r"
      by (auto simp: zbicompose_proof_def bindZ_eq_returnZ)
    note nr = znorm_proof_closed[OF r' zc(1) tac ce]
    have ns: "(znolb 0 sprf \<longrightarrow> znolb 0 sprf') \<and> zhyps sprf' \<subseteq> zhyps sprf"
    proof (cases "above env smax")
      case True
      with s' show ?thesis by simp
    next
      case False
      with s' have s: "znorm_proof ztargs env vis sprf = return sprf'" by simp
      from znorm_proof_closed[OF s zc(2) tac ce] show ?thesis by blast
    qed
    note cr = zbicompose_core_closed[OF cc tac ce cl]
    show ?thesis using nr ns cr by blast
  qed
  then show "znolb 0 rprf \<Longrightarrow> znolb 0 sprf \<Longrightarrow> znolb 0 r" "zhyps r \<subseteq> zhyps rprf \<union> zhyps sprf" by blast+
qed

end

end
