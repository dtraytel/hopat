section \<open>Proofs of flattened subgoals and of assumptions\<close>

theory Proof_Flatten
  imports Proof_Compose
begin

context prf_csig
begin

subsection \<open>Closed instantiations\<close>

text \<open>Values without loose bound variables are not lifted over abstractions.\<close>

definition closed_inst :: "(indexname \<Rightarrow> pterm) \<Rightarrow> pterm \<Rightarrow> bool" where
  "closed_inst \<theta> t \<longleftrightarrow> (\<forall>x\<in>vars t. \<not> loose_bvar (\<theta> x) 0)"

lemma psubst_closed_lev:
  "(\<forall>x\<in>vars t. \<not> loose_bvar (\<theta> x) 0) \<Longrightarrow> 0 \<le> lev \<Longrightarrow> psubst \<rho> \<theta> lev t = psubst \<rho> \<theta> 0 t"
proof (induction t arbitrary: lev)
  case (Var x T)
  then show ?case by (simp add: incr_boundvars_eq incr_bv_no_loose)
next
  case (Abs a T t)
  have "psubst \<rho> \<theta> (lev + 1) t = psubst \<rho> \<theta> 0 t" "psubst \<rho> \<theta> 1 t = psubst \<rho> \<theta> 0 t"
    using Abs.IH[of "lev + 1"] Abs.IH[of 1] Abs.prems by simp_all
  then show ?case by simp
next
  case (App s t)
  show ?case using App.IH(1)[of lev] App.IH(2)[of lev] App.prems by simp
qed simp_all

lemma psubst_incr_bv_closed:
  "(\<forall>x\<in>vars t. \<not> loose_bvar (\<theta> x) 0) \<Longrightarrow> 0 \<le> c \<Longrightarrow>
    psubst \<rho> \<theta> 0 (incr_bv n c t) = incr_bv n c (psubst \<rho> \<theta> 0 t)"
proof (induction t arbitrary: c)
  case (Var x T)
  then show ?case by (simp add: incr_boundvars_eq incr_bv_no_loose)
next
  case (Abs a T t)
  have "psubst \<rho> \<theta> 1 (incr_bv n (c + 1) t) = psubst \<rho> \<theta> 0 (incr_bv n (c + 1) t)"
    "psubst \<rho> \<theta> 1 t = psubst \<rho> \<theta> 0 t"
    using Abs.prems psubst_closed_lev[of "incr_bv n (c + 1) t" \<theta> 1 \<rho>] psubst_closed_lev[of t \<theta> 1 \<rho>]
    by (simp_all add: vars_incr_bv)
  then show ?case using Abs.IH[of "c + 1"] Abs.prems by simp
next
  case (App s t)
  show ?case using App.IH(1)[of c] App.IH(2)[of c] App.prems by simp
qed simp_all

lemma subst_bound_aux_no_loose: "\<not> loose_bvar t k \<Longrightarrow> k \<le> lev \<Longrightarrow> subst_bound_aux u lev t = t"
  by (induction u lev t arbitrary: k rule: subst_bound_aux.induct) fastforce+

lemma vars_subst_bound_aux_sub: "vars (subst_bound_aux u lev t) \<subseteq> vars u \<union> vars t"
  by (induction u lev t rule: subst_bound_aux.induct) (auto simp: incr_boundvars_eq vars_incr_bv)

lemma psubst_subst_bound_aux_closed:
  "(\<forall>x\<in>vars t \<union> vars u. \<not> loose_bvar (\<theta> x) 0) \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    psubst \<rho> \<theta> 0 (subst_bound_aux u lev t) = subst_bound_aux (psubst \<rho> \<theta> 0 u) lev (psubst \<rho> \<theta> 0 t)"
proof (induction t arbitrary: lev)
  case (Var x T)
  then show ?case by (simp add: incr_boundvars_eq incr_bv_no_loose subst_bound_aux_no_loose[of _ 0])
next
  case (Bound i)
  then show ?case by (simp add: incr_boundvars_eq psubst_incr_bv_closed)
next
  case (Abs a T t)
  have "psubst \<rho> \<theta> 1 (subst_bound_aux u (lev + 1) t) = psubst \<rho> \<theta> 0 (subst_bound_aux u (lev + 1) t)"
    "psubst \<rho> \<theta> 1 t = psubst \<rho> \<theta> 0 t"
    using Abs.prems vars_subst_bound_aux_sub[of u "lev + 1" t]
      psubst_closed_lev[of "subst_bound_aux u (lev + 1) t" \<theta> 1 \<rho>] psubst_closed_lev[of t \<theta> 1 \<rho>]
    by auto
  then show ?case using Abs.IH[of "lev + 1"] Abs.prems by simp
next
  case (App s t)
  have "\<forall>x\<in>vars s \<union> vars u. \<not> loose_bvar (\<theta> x) 0" "\<forall>x\<in>vars t \<union> vars u. \<not> loose_bvar (\<theta> x) 0"
    using App.prems by auto
  then show ?case using App.IH(1)[of lev] App.IH(2)[of lev] App.prems(2) by simp
qed simp_all


subsection \<open>Removing parameters from lifted subgoals\<close>

fun npar :: "litem list \<Rightarrow> nat" where
  "npar [] = 0"
| "npar (LImp c H # p) = npar p"
| "npar (LAll c a T # p) = Suc (npar p)"

fun nhyp :: "litem list \<Rightarrow> nat" where
  "nhyp [] = 0"
| "nhyp (LImp c H # p) = Suc (nhyp p)"
| "nhyp (LAll c a T # p) = nhyp p"

text \<open>The assumptions that \<^const>\<open>remove_params\<close> keeps, renumbered.\<close>

fun rmhyps :: "integer \<Rightarrow> integer \<Rightarrow> litem list \<Rightarrow> pterm list" where
  "rmhyps j n [] = []"
| "rmhyps j n (LImp c H # p) =
    (if n = 1 then rmhyps j (n - 1) p else incr_boundvars j H # rmhyps j (n - 1) p)"
| "rmhyps j n (LAll c a T # p) = rmhyps (j - 1) n p"

lemma strip_params_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic C \<Longrightarrow>
    strip_params (lift_pre p C) = concat (map (\<lambda>i. case i of LAll c a T \<Rightarrow> [(a, T)] | _ \<Rightarrow> []) p)"
proof (induction p)
  case Nil
  then show ?case by (simp add: strip_params.simps[of C] atomic_def)
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems obtain U where "c = Const STR ''Pure.imp'' U" by auto
    with Cons LImp show ?thesis by (subst strip_params.simps) simp
  next
    case (LAll c a T)
    with Cons.prems obtain U where "c = Const STR ''Pure.all'' U" by auto
    with Cons LAll show ?thesis by (subst strip_params.simps) simp
  qed
qed

lemma length_strip_params_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic C \<Longrightarrow> length (strip_params (lift_pre p C)) = npar p"
proof -
  have "length (concat (map (\<lambda>i. case i of LAll c a T \<Rightarrow> [(a, T)] | _ \<Rightarrow> []) p)) = npar p" for p :: "litem list"
    by (induction p) (auto split: litem.split)
  then show "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic C \<Longrightarrow> length (strip_params (lift_pre p C)) = npar p"
    by (simp add: strip_params_lift_pre)
qed

lemma remove_params_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic C" "integer_of_nat (npar p) = j" "integer_of_nat (nhyp p) \<ge> n"
    "\<forall>i\<in>set p. case i of LImp c H \<Rightarrow> c = implies | _ \<Rightarrow> True"
  shows "remove_params j n (lift_pre p C) = return (list_implies (rmhyps j n p) C)"
  using assms
proof (induction p arbitrary: j n)
  case Nil
  then have "j = 0" "n \<le> 0" by (simp_all add: integer_eq_iff integer_of_nat.rep_eq)
  then show ?case by (subst remove_params.simps) simp
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems have c: "c = implies" and IH: "\<And>n'. n' \<le> integer_of_nat (nhyp p) \<Longrightarrow>
        remove_params j n' (lift_pre p C) = return (list_implies (rmhyps j n' p) C)"
      using Cons.IH by auto
    have n': "n - 1 \<le> integer_of_nat (nhyp p)" using Cons.prems(4) LImp by (simp add: integer_of_nat_Suc)
    show ?thesis
    proof (cases "j = 0 \<and> n \<le> 0")
      case True
      have "remove_params j n (lift_pre (i # p) C) = return (lift_pre (i # p) C)"
        using True by (subst remove_params.simps) simp
      moreover have "list_implies (rmhyps j n (i # p)) C = lift_pre (i # p) C"
      proof -
        have "list_implies (rmhyps 0 n' q) C = lift_pre q C" if "n' \<le> 0" "npar q = 0"
          "\<forall>i\<in>set q. case i of LImp c H \<Rightarrow> c = implies | _ \<Rightarrow> True" for n' q
          using that by (induction q arbitrary: n') (auto split: litem.splits simp: incr_boundvars_eq)
        note helper = this
        have j0: "j = 0" using True by simp
        have "npar p = 0" using Cons.prems(3) LImp j0 by (simp add: integer_eq_iff integer_of_nat.rep_eq)
        then show ?thesis using helper[of n "i # p"] True j0 Cons.prems(5) LImp by simp
      qed
      ultimately show ?thesis by simp
    next
      case False
      with LImp c n' IH Cons.prems(1) show ?thesis
        by (subst remove_params.simps) (auto simp: implies_def bindM_def return_def)
    qed
  next
    case (LAll c a T)
    with Cons.prems have j1: "integer_of_nat (npar p) = j - 1" by (auto simp: integer_of_nat_Suc)
    then have j: "integer_of_nat (npar p) = j - 1" "j \<noteq> 0" using integer_of_nat_nonneg[of "npar p"] by auto
    have "\<exists>U. c = Const STR ''Pure.all'' U" using Cons.prems(1) LAll by simp
    with Cons.IH[OF _ _ j(1)] Cons.prems LAll j(2) show ?thesis
      by (subst remove_params.simps) auto
  qed
qed


subsection \<open>Proofs applied to bound variables\<close>

lemma subst_bound_aux_list_forall:
  "subst_bound_aux arg lev (list_forall vs X) = list_forall vs (subst_bound_aux arg (lev + integer_of_nat (length vs)) X)"
  by (induction vs arbitrary: lev) (auto simp: all_const_def integer_of_nat_Suc algebra_simps)

lemma proper_list_forall[simp]: "proper (list_forall vs X) \<longleftrightarrow> proper X"
  by (induction vs) (auto simp: all_const_def)

lemma Abs_m_subst_BVar: "(Abs_m m t)[BVar x/n] = Abs_m m (t[BVar (x + m)/n + m])"
  by (induction m arbitrary: x n) (simp, force)

lemma proof_combt_Cons: "proof_combt p (t # ts) = proof_combt (PAppt p (Some t)) ts"
  by (simp add: proof_combt_def)

lemma prf_ok_combt_bounds:
  "prf_ok V H Ts Hs p (list_forall vs X) \<Longrightarrow> length bs = length vs \<Longrightarrow> \<forall>b\<in>set bs. 0 \<le> b \<Longrightarrow>
    (\<forall>l<length vs. wty V Ts (Bound (bs ! l)) (snd (vs ! l))) \<Longrightarrow>
    \<exists>Y. prf_ok V H Ts Hs (proof_combt p (map Bound bs)) Y \<and>
      tr Y = appb (Abs_m (length vs) (tr X)) (map nat_of_integer bs)"
proof (induction vs arbitrary: bs p X)
  case Nil
  then show ?case by (auto simp: proof_combt_def)
next
  case (Cons v vs)
  obtain a T where v: "v = (a, T)" by (cases v)
  from Cons.prems(2) obtain b bs' where bs: "bs = b # bs'" by (cases bs) auto
  have wb: "wty V Ts (Bound b) T" using Cons.prems(4)[rule_format, of 0] by (simp add: bs v)
  have pf: "prf_ok V H Ts Hs p (all_const T $ Abs a T (list_forall vs X))" using Cons.prems(1) by (simp add: v)
  then have w: "wty V Ts (all_const T $ Abs a T (list_forall vs X)) propT" by (rule prf_ok_wty)
  then have wbody: "has_type V (T # Ts) (list_forall vs X) propT" "\<forall>x\<in>vars (list_forall vs X). 0 \<le> snd x"
    by (auto simp: wty_def all_const_def dest!: has_type_all_E)
  let ?Y = "subst_bound (Bound b) (list_forall vs X)"
  have b0: "0 \<le> b" using Cons.prems(3) bs by simp
  have "prf_ok V H Ts Hs (PAppt p (Some (Bound b))) (Abs a T (list_forall vs X) $ Bound b)"
    using pf wb by (rule prf_ok.PAppt) (use b0 in simp)
  moreover have "tr (Abs a T (list_forall vs X) $ Bound b) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ?Y"
  proof -
    have "proper (list_forall vs X)" using has_type_proper[OF wbody(1)] .
    then have "tr ?Y = subst (tr (list_forall vs X)) (BVar (nat_of_integer b)) 0"
      using b0 tr_subst_bound[of "list_forall vs X" "Bound b"] by simp
    then show ?thesis using b0 by (auto intro: beta_into_equiv r_into_rtranclp beta.beta)
  qed
  moreover have wY: "wty V Ts ?Y propT"
    using has_type_subst_bound[OF wbody(1)] wb wbody(2) vars_subst_bound[of "Bound b" "list_forall vs X"]
    by (auto simp: wty_def)
  ultimately have pY: "prf_ok V H Ts Hs (PAppt p (Some (Bound b))) ?Y" by (rule prf_ok.conv)
  have "?Y = list_forall vs (subst_bound_aux (Bound b) (integer_of_nat (length vs)) X)"
    by (simp add: subst_bound_def subst_bound_aux_list_forall)
  with pY Cons.IH[where bs = bs' and p = "PAppt p (Some (Bound b))"
      and X = "subst_bound_aux (Bound b) (integer_of_nat (length vs)) X"]
    Cons.prems(2-4) bs
  obtain Y where Y: "prf_ok V H Ts Hs (proof_combt (PAppt p (Some (Bound b))) (map Bound bs')) Y"
    "tr Y = appb (Abs_m (length vs) (tr (subst_bound_aux (Bound b) (integer_of_nat (length vs)) X))) (map nat_of_integer bs')"
    by (fastforce simp: v)
  have pX: "proper X" using has_type_proper[OF wbody(1)] by (simp add: proper_list_forall)
  have "tr (subst_bound_aux (Bound b) (integer_of_nat (length vs)) X) =
      (tr X)[BVar (nat_of_integer b + length vs)/length vs]"
    using pX Cons.prems(3) bs by (simp add: tr_subst_bound_aux substn_subst_n)
  moreover have "(Abs_m (length vs) (tr X))[BVar (nat_of_integer b)/0] =
      Abs_m (length vs) ((tr X)[BVar (nat_of_integer b + length vs)/length vs])"
    using Abs_m_subst_BVar[of "length vs" "tr X" "nat_of_integer b" 0] by simp
  ultimately have "tr Y = appb (Abs_m (length (v # vs)) (tr X)) (map nat_of_integer bs)"
    using Y(2) by (simp add: bs)
  with Y(1) show ?case by (auto simp: bs proof_combt_Cons)
qed


subsection \<open>Proofs by assumption\<close>

lemma strip_assums_imp_acc:
  "strip_assums_imp m Gs0 B = (fst (strip_assums_imp m [] B) @ Gs0, snd (strip_assums_imp m [] B))"
proof (induction B arbitrary: m Gs0 rule: measure_induct_rule[of size])
  case (less B)
  show ?case
  proof (cases "m = 0")
    case True
    then show ?thesis by (simp add: strip_assums_imp.simps[of 0])
  next
    case False
    show ?thesis
    proof (cases "dest_imp B")
      case None
      with False show ?thesis by (simp add: strip_assums_imp.simps[of m _ B])
    next
      case (Some HB)
      then obtain H' B' where HB: "dest_imp B = Some (H', B')" by (cases HB) auto
      then have s: "size B' < size B" by (auto dest: dest_size)
      have "strip_assums_imp m Gs0 B = strip_assums_imp (m - 1) (H' # Gs0) B'"
        "strip_assums_imp m [] B = strip_assums_imp (m - 1) [H'] B'"
        using False HB by (simp_all add: strip_assums_imp.simps[of m _ B])
      with less.IH[OF s, of "m - 1" "H' # Gs0"] less.IH[OF s, of "m - 1" "[H']"] show ?thesis by simp
    qed
  qed
qed

lemma imp_prf_eq:
  "imp_prf B i m = (AbsP (STR ''H'') None ^^ length (fst (strip_assums_imp m [] B)))
    (PBound (i + integer_of_nat (length (fst (strip_assums_imp m [] B)))))"
proof (induction B i m rule: imp_prf.induct)
  case (1 c U A B i m)
  show ?case
  proof (cases "m \<noteq> 0 \<and> c = STR ''Pure.imp''")
    case True
    then have "strip_assums_imp m [] (Const c U $ A $ B) = strip_assums_imp (m - 1) [A] B"
      by (simp add: strip_assums_imp.simps[of m])
    then have "fst (strip_assums_imp m [] (Const c U $ A $ B)) = fst (strip_assums_imp (m - 1) [] B) @ [A]"
      by (subst (asm) strip_assums_imp_acc) simp
    with True "1.IH" show ?thesis by (simp add: integer_of_nat_Suc funpow_Suc_right algebra_simps)
  next
    case False
    then show ?thesis by (auto simp: strip_assums_imp.simps[of m])
  qed
qed (auto simp: strip_assums_imp.simps)

lemma strip_assums_imp_list_implies:
  "strip_assums_imp m [] B = (Gs, B0) \<Longrightarrow> cok B \<Longrightarrow> B = list_implies (rev Gs) B0"
proof (induction B arbitrary: m Gs B0 rule: measure_induct_rule[of size])
  case (less B)
  show ?case
  proof (cases "m \<noteq> 0 \<and> dest_imp B \<noteq> None")
    case True
    then obtain H' B' where HB: "dest_imp B = Some (H', B')" by auto
    then have s: "size B' < size B" by (auto dest: dest_size)
    have e: "B = implies $ H' $ B'" "cok B'" using cok_dest_imp[OF less.prems(2) HB] by auto
    have "strip_assums_imp m [] B = strip_assums_imp (m - 1) [H'] B'"
      using True HB by (simp add: strip_assums_imp.simps[of m _ B])
    then obtain Gs' where "Gs = Gs' @ [H']" "strip_assums_imp (m - 1) [] B' = (Gs', B0)"
      using less.prems(1) strip_assums_imp_acc[of "m - 1" "[H']" B'] by (cases "strip_assums_imp (m - 1) [] B'") auto
    with less.IH[OF s] e show ?thesis by simp
  next
    case False
    then show ?thesis using less.prems
      by (cases "dest_imp B") (auto simp: strip_assums_imp.simps[of m _ B] strip_assums_imp.simps[of 0 _ B] split: if_splits)
  qed
qed

lemma prf_ok_AbsP_pow:
  "prf_ok V H Ts (rev Ps @ Hs) q X \<Longrightarrow> \<forall>P\<in>set Ps. wty V Ts P propT \<Longrightarrow>
    prf_ok V H Ts Hs ((AbsP (STR ''H'') None ^^ length Ps) q) (list_implies Ps X)"
  using prf_ok_mk_AbsP[of V H Ts Ps Hs q X] by (simp add: mk_AbsP_funpow)

lemma vars_implies[simp]: "vars implies = {}"
  by (simp add: implies_def)

lemma wty_list_implies_iff:
  "wty V Ts (list_implies Ps X) propT \<longleftrightarrow> (\<forall>P\<in>set Ps. wty V Ts P propT) \<and> wty V Ts X propT"
proof
  show "wty V Ts (list_implies Ps X) propT \<Longrightarrow> (\<forall>P\<in>set Ps. wty V Ts P propT) \<and> wty V Ts X propT"
    by (rule wty_list_implies)
  show "(\<forall>P\<in>set Ps. wty V Ts P propT) \<and> wty V Ts X propT \<Longrightarrow> wty V Ts (list_implies Ps X) propT"
    by (induction Ps) (auto simp: wty_def has_type_implies)
qed

lemma psubst_list_implies':
  "psubst \<rho> \<theta> lev (list_implies As B) = list_implies (map (psubst \<rho> \<theta> lev) As) (psubst \<rho> \<theta> lev B)"
  by (induction As) simp_all

lemma imp_prf_ok:
  assumes "cok B" "wty V Ts (psubst \<rho> \<theta> 0 B) propT" "strip_assums_imp m [] B = (Gs, B0)"
    "0 \<le> i + integer_of_nat (length Gs)" "nat_of_integer (i + integer_of_nat (length Gs)) < length Gs"
    "tr (psubst \<rho> \<theta> 0 (Gs ! nat_of_integer (i + integer_of_nat (length Gs)))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 B0)"
  shows "prf_ok V H Ts Hs (imp_prf B i m) (psubst \<rho> \<theta> 0 B)"
proof -
  let ?k = "nat_of_integer (i + integer_of_nat (length Gs))"
  have B: "B = list_implies (rev Gs) B0" by (rule strip_assums_imp_list_implies[OF assms(3,1)])
  have w: "\<forall>P\<in>set (map (psubst \<rho> \<theta> 0) (rev Gs)). wty V Ts P propT" "wty V Ts (psubst \<rho> \<theta> 0 B0) propT"
    using assms(2) by (simp_all add: B psubst_list_implies' wty_list_implies_iff)
  have "(map (psubst \<rho> \<theta> 0) Gs @ Hs) ! ?k = psubst \<rho> \<theta> 0 (Gs ! ?k)" using assms(5) by (simp add: nth_append)
  moreover have "wty V Ts (psubst \<rho> \<theta> 0 (Gs ! ?k)) propT" using w(1) assms(5) by (simp add: rev_map[symmetric])
  ultimately have "prf_ok V H Ts (map (psubst \<rho> \<theta> 0) Gs @ Hs) (PBound (i + integer_of_nat (length Gs)))
      (psubst \<rho> \<theta> 0 (Gs ! ?k))"
    using prf_ok.PBound[of "i + integer_of_nat (length Gs)" "map (psubst \<rho> \<theta> 0) Gs @ Hs" V Ts H] assms(4,5) by simp
  then have "prf_ok V H Ts (rev (map (psubst \<rho> \<theta> 0) (rev Gs)) @ Hs) (PBound (i + integer_of_nat (length Gs)))
      (psubst \<rho> \<theta> 0 B0)"
    using assms(6) w(2) by (auto simp: rev_map intro: prf_ok.conv)
  from prf_ok_AbsP_pow[OF this w(1)] assms(3) show ?thesis
    by (simp add: imp_prf_eq B psubst_list_implies')
qed


fun abst_chain :: "binders \<Rightarrow> prf \<Rightarrow> prf" where
  "abst_chain [] q = q"
| "abst_chain ((a, T) # vs) q = Abst a None (abst_chain vs q)"

lemma strip_assums_all_acc:
  "strip_assums_all ps C = (fst (strip_assums_all [] C) @ ps, snd (strip_assums_all [] C))"
proof (induction C arbitrary: ps rule: measure_induct_rule[of size])
  case (less C)
  show ?case
  proof (cases "dest_all C")
    case None
    then show ?thesis by (simp add: strip_assums_all.simps[of _ C])
  next
    case (Some aTb)
    then obtain a T b where d: "dest_all C = Some (a, T, b)" by (cases aTb) auto
    then have s: "size b < size C" by (auto dest: dest_size)
    have "strip_assums_all ps C = strip_assums_all ((a, T) # ps) b" "strip_assums_all [] C = strip_assums_all [(a, T)] b"
      using d by (simp_all add: strip_assums_all.simps[of _ C])
    with less.IH[OF s, of "(a, T) # ps"] less.IH[OF s, of "[(a, T)]"] show ?thesis by simp
  qed
qed

lemma all_prf_eq:
  "all_prf i m C = abst_chain (rev (fst (strip_assums_all [] C))) (imp_prf (snd (strip_assums_all [] C)) (- i) m)"
proof (induction i m C rule: all_prf.induct)
  case (1 i m c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    then have "strip_assums_all [] (Const c U $ Abs a T t) = strip_assums_all [(a, T)] t"
      by (simp add: strip_assums_all.simps[of _ "Const STR ''Pure.all'' U $ Abs a T t"])
    then have "strip_assums_all [] (Const c U $ Abs a T t) =
        (fst (strip_assums_all [] t) @ [(a, T)], snd (strip_assums_all [] t))"
      by (subst (asm) strip_assums_all_acc) simp
    with True "1.IH" show ?thesis by simp
  next
    case False
    then show ?thesis by (simp add: strip_assums_all.simps[of _ "Const c U $ Abs a T t"])
  qed
qed (simp_all add: strip_assums_all.simps)

lemma strip_assums_all_list_forall:
  "strip_assums_all [] C = (ps, C1) \<Longrightarrow> cok C \<Longrightarrow> C = list_forall (rev ps) C1 \<and> cok C1"
proof (induction C arbitrary: ps rule: measure_induct_rule[of size])
  case (less C)
  show ?case
  proof (cases "dest_all C")
    case None
    then show ?thesis using less.prems by (simp add: strip_assums_all.simps[of _ C])
  next
    case (Some aTb)
    then obtain a T b where d: "dest_all C = Some (a, T, b)" by (cases aTb) auto
    then have s: "size b < size C" by (auto dest: dest_size)
    have e: "C = all_const T $ Abs a T b" "cok b" using cok_dest_all[OF less.prems(2) d] by auto
    have "strip_assums_all [] C = strip_assums_all [(a, T)] b"
      using d by (simp add: strip_assums_all.simps[of _ C])
    then obtain ps' where "ps = ps' @ [(a, T)]" "strip_assums_all [] b = (ps', C1)"
      using less.prems(1) strip_assums_all_acc[of "[(a, T)]" b] by (cases "strip_assums_all [] b") auto
    with less.IH[OF s] e show ?thesis by simp
  qed
qed

lemma incr_bv_comp0: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> incr_bv a 0 (incr_bv b 0 v) = incr_bv (a + b) 0 v"
  using incr_bv_comp[of 0 0 b a v] by simp

lemma prf_ok_abst_chain:
  "prf_ok V H (rev (map (f \<circ> snd) vs) @ Ts) (map (incr_bv (integer_of_nat (length vs)) 0) Hs) q X \<Longrightarrow>
    prf_ok V H Ts Hs (abst_chain vs q) (list_forall (map (\<lambda>(a, T). (a, f T)) vs) X)"
proof (induction vs arbitrary: Ts Hs)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  obtain a T where v: "v = (a, T)" by (cases v)
  have e: "map (incr_bv (integer_of_nat (length vs)) 0) (map (incr_bv 1 0) Hs) =
      map (incr_bv (integer_of_nat (length (v # vs))) 0) Hs"
    by (simp add: incr_bv_comp0 integer_of_nat_Suc)
  have "prf_ok V H (rev (map (f \<circ> snd) vs) @ f T # Ts)
      (map (incr_bv (integer_of_nat (length vs)) 0) (map (incr_bv 1 0) Hs)) q X"
    unfolding e using Cons.prems by (simp add: v comp_def)
  from Cons.IH[OF this]
  have "prf_ok V H (f T # Ts) (map (incr_bv 1 0) Hs) (abst_chain vs q) (list_forall (map (\<lambda>(a, T). (a, f T)) vs) X)" .
  then show ?case by (simp add: v) (rule prf_ok.Abst[where T = None, simplified])
qed

lemma psubst_list_forall:
  "psubst \<rho> \<theta> lev (list_forall vs X) =
    list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) vs) (psubst \<rho> \<theta> (lev + integer_of_nat (length vs)) X)"
  by (induction vs arbitrary: lev) (auto simp: all_const_def propT_def integer_of_nat_Suc algebra_simps)

lemma vars_list_forall[simp]: "vars (list_forall vs X) = vars X"
  by (induction vs X rule: list_forall.induct) (simp_all add: all_const_def)

lemma has_type_list_forall_body:
  "has_type V Ts (list_forall vs X) propT \<Longrightarrow> has_type V (rev (map snd vs) @ Ts) X propT"
  by (induction vs arbitrary: Ts) (auto simp: all_const_def dest!: has_type_all_E)

lemma mk_asm_prf_ok:
  assumes "cok A" "closed_inst \<theta> A" "wty V Ts (psubst \<rho> \<theta> 0 A) propT"
    "assum_problems m A = (params, asms, concl)" "1 \<le> n" "n \<le> integer_of_nat (length asms)"
    "tr (psubst \<rho> \<theta> 0 (asms ! (nat_of_integer n - 1))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 concl)"
  shows "prf_ok V H Ts Hs (mk_asm_prf A n m) (psubst \<rho> \<theta> 0 A)"
proof -
  obtain A' Gs where sa: "strip_assums_all [] A = (params, A')" and si: "strip_assums_imp m [] A' = (Gs, concl)"
    and asms: "asms = rev Gs"
    using assms(4) unfolding assum_problems_def
    by (cases "strip_assums_all [] A"; cases "strip_assums_imp m [] (snd (strip_assums_all [] A))") auto
  from strip_assums_all_list_forall[OF sa assms(1)] have A: "A = list_forall (rev params) A'" and cA': "cok A'"
    by auto
  let ?vs = "rev params"
  have cl: "closed_inst \<theta> A'" using assms(2) by (simp add: closed_inst_def A)
  have psA: "psubst \<rho> \<theta> 0 A = list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) ?vs) (psubst \<rho> \<theta> 0 A')"
    using cl psubst_closed_lev[of A' \<theta> "integer_of_nat (length ?vs)" \<rho>]
    by (simp add: A psubst_list_forall closed_inst_def)
  let ?Ts = "rev (map (tsubst \<rho> \<circ> snd) ?vs) @ Ts"
  have rv: "rev (map snd (map (\<lambda>(a, T). (a, tsubst \<rho> T)) ?vs)) = rev (map (tsubst \<rho> \<circ> snd) ?vs)"
    by (induction params) auto
  have wA': "wty V ?Ts (psubst \<rho> \<theta> 0 A') propT"
    using assms(3) has_type_list_forall_body[of V Ts "map (\<lambda>(a, T). (a, tsubst \<rho> T)) ?vs" "psubst \<rho> \<theta> 0 A'"]
    by (simp only: psA rv) (auto simp: wty_def)
  have len: "length asms = length Gs" by (simp add: asms)
  have k: "nat_of_integer (- n + integer_of_nat (length Gs)) = length Gs - nat_of_integer n"
    "nat_of_integer (- n + integer_of_nat (length Gs)) < length Gs"
    using assms(5,6) len by (simp_all add: integer_reps integer_of_nat.rep_eq nat_diff_distrib)
  have "Gs ! (length Gs - nat_of_integer n) = asms ! (nat_of_integer n - 1)"
    using assms(5,6) len by (simp add: asms rev_nth integer_reps integer_of_nat.rep_eq)
  then have "prf_ok V H ?Ts (map (incr_bv (integer_of_nat (length ?vs)) 0) Hs) (imp_prf A' (- n) m) (psubst \<rho> \<theta> 0 A')"
    using imp_prf_ok[OF cA' wA' si, of "- n"] assms(5,6,7) k len by (simp add: integer_reps integer_of_nat.rep_eq)
  from prf_ok_abst_chain[OF this] show ?thesis
    by (simp add: psA mk_asm_prf_def all_prf_eq sa)
qed


subsection \<open>Proofs of flattened subgoals\<close>

definition leafprf :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "leafprf i j n k = proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
    (map PBound (removeAll (i - n) (downto (i - 1) 0)))"

lemma fpp_atomic: "atomic C \<Longrightarrow> flatten_params_proof i j n (C, k) = leafprf i j n k"
  by (cases "(i, j, n, (C, k))" rule: flatten_params_proof.cases) (auto simp: atomic_def leafprf_def)

fun ptys :: "tinst \<Rightarrow> litem list \<Rightarrow> ptyp list" where
  "ptys \<rho> [] = []"
| "ptys \<rho> (LImp c H # p) = ptys \<rho> p"
| "ptys \<rho> (LAll c a T # p) = ptys \<rho> p @ [tsubst \<rho> T]"

fun phs :: "tinst \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> litem list \<Rightarrow> pterm list" where
  "phs \<rho> \<theta> [] = []"
| "phs \<rho> \<theta> (LImp c H # p) = phs \<rho> \<theta> p @ [incr_bv (integer_of_nat (npar p)) 0 (psubst \<rho> \<theta> 0 H)]"
| "phs \<rho> \<theta> (LAll c a T # p) = phs \<rho> \<theta> p"

lemma cok_lift_pre_items:
  "\<forall>it\<in>set p. litem_ok it \<Longrightarrow> cok (lift_pre p C) \<Longrightarrow>
    (\<forall>it\<in>set p. case it of LImp c H \<Rightarrow> c = implies | LAll c a T \<Rightarrow> c = all_const T) \<and> cok C"
proof (induction p)
  case (Cons it p)
  show ?case
  proof (cases it)
    case (LImp c H)
    with Cons.prems obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have "dest_imp (lift_pre (it # p) C) = Some (H, lift_pre p C)" using LImp c by simp
    from cok_dest_imp[OF Cons.prems(2) this] have "lift_pre (it # p) C = implies $ H $ lift_pre p C" "cok (lift_pre p C)"
      by auto
    with Cons LImp show ?thesis by auto
  next
    case (LAll c a T)
    with Cons.prems obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    have "dest_all (lift_pre (it # p) C) = Some (a, T, lift_pre p C)" using LAll c by simp
    from cok_dest_all[OF Cons.prems(2) this] have "lift_pre (it # p) C = all_const T $ Abs a T (lift_pre p C)"
      "cok (lift_pre p C)" by auto
    with Cons LAll show ?thesis by auto
  qed
qed simp

lemma fpp_gen:
  assumes "\<forall>it\<in>set p. litem_ok it" "atomic C" "cok (lift_pre p C)" "closed_inst \<theta> (lift_pre p C)"
  shows "wty V Ts (psubst \<rho> \<theta> 0 (lift_pre p C)) propT \<Longrightarrow> \<forall>h\<in>set Hs. wty V Ts h propT \<Longrightarrow>
    prf_ok V H (ptys \<rho> p @ Ts) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) Hs)
      (leafprf (i + integer_of_nat (nhyp p)) (j + integer_of_nat (npar p)) n k) (psubst \<rho> \<theta> 0 C) \<Longrightarrow>
    prf_ok V H Ts Hs (flatten_params_proof i j n (lift_pre p C, k)) (psubst \<rho> \<theta> 0 (lift_pre p C))"
  using assms
proof (induction p arbitrary: i j Ts Hs)
  case Nil
  then show ?case by (simp add: fpp_atomic)
next
  case (Cons it p)
  note items = cok_lift_pre_items[OF Cons.prems(4,6)]
  have cl: "closed_inst \<theta> (lift_pre p C)" using Cons.prems(7) by (cases it) (auto simp: closed_inst_def)
  show ?case
  proof (cases it)
    case (LImp c H')
    then have c: "c = implies" using items by simp
    have cok': "cok (lift_pre p C)" using Cons.prems(6) by (simp add: LImp c)
    have w: "wty V Ts (psubst \<rho> \<theta> 0 H') propT" "wty V Ts (psubst \<rho> \<theta> 0 (lift_pre p C)) propT"
      using Cons.prems(1) by (auto simp: LImp c wty_def has_type_implies)
    have fpp: "flatten_params_proof i j n (implies $ H' $ lift_pre p C, k) =
        AbsP (STR ''H'') None (flatten_params_proof (i + 1) j n (lift_pre p C, k))"
      by (simp add: implies_def)
    have "prf_ok V H Ts (psubst \<rho> \<theta> 0 H' # Hs) (flatten_params_proof (i + 1) j n (lift_pre p C, k))
        (psubst \<rho> \<theta> 0 (lift_pre p C))"
    proof (rule Cons.IH[OF w(2)])
      show "\<forall>h\<in>set (psubst \<rho> \<theta> 0 H' # Hs). wty V Ts h propT" using w(1) Cons.prems(2) by simp
      show "prf_ok V H (ptys \<rho> p @ Ts) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) (psubst \<rho> \<theta> 0 H' # Hs))
          (leafprf (i + 1 + integer_of_nat (nhyp p)) (j + integer_of_nat (npar p)) n k) (psubst \<rho> \<theta> 0 C)"
        using Cons.prems(3) by (simp add: LImp integer_of_nat_Suc algebra_simps)
    qed (use Cons.prems(4,5) cok' cl in auto)
    then show ?thesis using w(1) by (auto simp: fpp LImp c intro: prf_ok.AbsP)
  next
    case (LAll c a T)
    then have c: "c = all_const T" using items by simp
    have cok': "cok (lift_pre p C)" using Cons.prems(6) by (simp add: LAll c all_const_def)
    have e1: "psubst \<rho> \<theta> 1 (lift_pre p C) = psubst \<rho> \<theta> 0 (lift_pre p C)"
      using cl psubst_closed_lev[of "lift_pre p C" \<theta> 1 \<rho>] by (simp add: closed_inst_def)
    have w: "wty V (tsubst \<rho> T # Ts) (psubst \<rho> \<theta> 0 (lift_pre p C)) propT"
      using Cons.prems(1) e1 by (auto simp: LAll c wty_def all_const_def dest!: has_type_all_E)
    have fpp: "flatten_params_proof i j n (all_const T $ Abs a T (lift_pre p C), k) =
        Abst a None (flatten_params_proof i (j + 1) n (lift_pre p C, k))"
      by (simp add: all_const_def)
    have "prf_ok V H (tsubst \<rho> T # Ts) (map (incr_bv 1 0) Hs) (flatten_params_proof i (j + 1) n (lift_pre p C, k))
        (psubst \<rho> \<theta> 0 (lift_pre p C))"
    proof (rule Cons.IH[OF w])
      show "\<forall>h\<in>set (map (incr_bv 1 0) Hs). wty V (tsubst \<rho> T # Ts) h propT"
        using Cons.prems(2) wty_incr_bv[of V Ts _ propT 0 "tsubst \<rho> T"] by (auto simp: integer_reps)
      have e: "map (incr_bv (integer_of_nat (npar p)) 0) (map (incr_bv 1 0) Hs) =
          map (incr_bv (integer_of_nat (npar (it # p))) 0) Hs"
        by (simp add: LAll incr_bv_comp0 integer_of_nat_Suc)
      have j: "j + 1 + integer_of_nat (npar p) = j + integer_of_nat (npar (it # p))"
        by (simp add: LAll integer_of_nat_Suc)
      show "prf_ok V H (ptys \<rho> p @ tsubst \<rho> T # Ts) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) (map (incr_bv 1 0) Hs))
          (leafprf (i + integer_of_nat (nhyp p)) (j + 1 + integer_of_nat (npar p)) n k) (psubst \<rho> \<theta> 0 C)"
        unfolding e j using Cons.prems(3) by (simp add: LAll)
    qed (use Cons.prems(4,5) cok' cl in auto)
    then have "prf_ok V H Ts Hs (Abst a None (flatten_params_proof i (j + 1) n (lift_pre p C, k)))
        (all_const (tsubst \<rho> T) $ Abs a (tsubst \<rho> T) (psubst \<rho> \<theta> 0 (lift_pre p C)))"
      by (rule prf_ok.Abst[where T = None, simplified])
    then show ?thesis using e1 by (simp add: fpp LAll c)
  qed
qed


text \<open>The assumptions of a prefix with the numbers of parameters after them.\<close>

fun pre_hyps :: "litem list \<Rightarrow> (pterm \<times> nat) list" where
  "pre_hyps [] = []"
| "pre_hyps (LImp c H # p) = (H, npar p) # pre_hyps p"
| "pre_hyps (LAll c a T # p) = pre_hyps p"

lemma length_pre_hyps: "length (pre_hyps p) = nhyp p"
  by (induction p rule: pre_hyps.induct) auto

lemma phs_pre_hyps: "phs \<rho> \<theta> p = rev (map (\<lambda>(H, a). incr_bv (integer_of_nat a) 0 (psubst \<rho> \<theta> 0 H)) (pre_hyps p))"
  by (induction p rule: pre_hyps.induct) auto

lemma filter_upt_Suc_Cons:
  "[l \<leftarrow> [0..<Suc L]. P l] = (if P 0 then [0] else []) @ map Suc [l \<leftarrow> [0..<L]. P (Suc l)]"
proof -
  have "[0..<Suc L] = 0 # map Suc [0..<L]" by (simp add: map_Suc_upt upt_conv_Cons del: upt_Suc)
  then show ?thesis by (simp add: filter_map comp_def)
qed

lemma rmhyps_pre_hyps:
  "rmhyps (integer_of_nat (npar p)) n p =
    map (\<lambda>l. case pre_hyps p ! l of (H, a) \<Rightarrow> incr_boundvars (integer_of_nat a) H)
      [l \<leftarrow> [0..<length (pre_hyps p)]. integer_of_nat l + 1 \<noteq> n]"
proof (induction p arbitrary: n rule: pre_hyps.induct)
  case 1
  then show ?case by simp
next
  case (2 c H p)
  have e: "\<And>l. integer_of_nat (Suc l) + 1 \<noteq> n \<longleftrightarrow> integer_of_nat l + 1 \<noteq> n - 1"
    by (auto simp: integer_of_nat_Suc algebra_simps)
  show ?case
  proof (cases "n = 1")
    case True
    have nz: "integer_of_nat l + 1 \<noteq> 0" for l using integer_of_nat_nonneg[of l] by linarith
    have "[l \<leftarrow> [0..<length (pre_hyps p)]. integer_of_nat (Suc l) \<noteq> 0] = [0..<length (pre_hyps p)]"
      using nz by (intro filter_True) (simp add: integer_of_nat_Suc)
    moreover have "[l \<leftarrow> [0..<length (pre_hyps p)]. integer_of_nat l + 1 \<noteq> 0] = [0..<length (pre_hyps p)]"
      using nz by (intro filter_True) simp
    ultimately show ?thesis using True "2.IH"[of 0]
      by (simp add: filter_upt_Suc_Cons e del: upt_Suc)
  next
    case False
    with "2.IH"[of "n - 1"] show ?thesis
      by (simp add: filter_upt_Suc_Cons e comp_def del: upt_Suc)
  qed
next
  case (3 c a T p)
  then show ?case by (simp add: integer_of_nat_Suc)
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

lemma ptys_concat:
  "ptys \<rho> p = rev (map (tsubst \<rho> \<circ> snd) (concat (map (\<lambda>i. case i of LAll c a T \<Rightarrow> [(a, T)] | _ \<Rightarrow> []) p)))"
  by (induction p rule: ptys.induct) auto

lemma ptys_strip_params:
  "\<forall>it\<in>set p. litem_ok it \<Longrightarrow> atomic C \<Longrightarrow>
    ptys \<rho> p = rev (map (tsubst \<rho> \<circ> snd) (strip_params (lift_pre p C)))"
  by (simp add: strip_params_lift_pre ptys_concat)

lemma npar_strip_params:
  "\<forall>it\<in>set p. litem_ok it \<Longrightarrow> atomic C \<Longrightarrow> length (ptys \<rho> p) = npar p"
  by (induction p rule: ptys.induct) auto

lemma map_nat_downto: "map nat_of_integer (downto (integer_of_nat J - 1) 0) = rev [0..<J]"
proof -
  have "downto (integer_of_nat J - 1) 0 = map (\<lambda>l. integer_of_nat J - 1 - integer_of_nat l) [0..<J]"
    by (simp add: downto_map integer_reps integer_of_nat.rep_eq)
  moreover have "map (\<lambda>l. nat_of_integer (integer_of_nat J - 1 - integer_of_nat l)) [0..<J] = rev [0..<J]"
    by (rule nth_equalityI) (auto simp: rev_nth integer_reps integer_of_nat.rep_eq nat_diff_distrib)
  ultimately show ?thesis by (simp add: comp_def)
qed


lemma vars_rmhyps: "H \<in> set (rmhyps j n p) \<Longrightarrow> vars H \<subseteq> (\<Union>(H', a)\<in>set (pre_hyps p). vars H')"
  by (induction j n p rule: rmhyps.induct) (auto simp: incr_boundvars_eq vars_incr_bv split: if_splits)

lemma pre_hyps_vars: "(H', a) \<in> set (pre_hyps p) \<Longrightarrow> vars H' \<subseteq> vars (lift_pre p C)"
proof (induction p)
  case (Cons it p)
  then show ?case by (cases it) auto
qed simp

lemma vars_lift_pre_C: "vars C \<subseteq> vars (lift_pre p C)"
proof (induction p)
  case (Cons it p)
  then show ?case by (cases it) auto
qed simp

lemma vars_list_implies: "vars (list_implies Hs C) = (\<Union>h\<in>set Hs. vars h) \<union> vars C"
  by (induction Hs) auto

lemma integer_of_nat_plus: "integer_of_nat (a + b) = integer_of_nat a + integer_of_nat b"
  by (simp add: integer_eq_iff integer_of_nat.rep_eq)

lemma fpp_leaf:
  assumes items: "\<forall>it\<in>set p. litem_ok it" and at: "atomic C"
    and cl: "closed_inst \<theta> (lift_pre p C)"
    and vs: "length vs = npar p" "map snd vs = map snd (strip_params (lift_pre p C))"
    and k: "k < length Hs" and wk: "wty V [] (Hs ! k) propT"
    and wN: "wty V [] (psubst \<rho> \<theta> 0 (list_forall vs (list_implies (rmhyps (integer_of_nat (npar p)) n p) C))) propT"
    and eN: "tr (Hs ! k) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 (list_forall vs (list_implies (rmhyps (integer_of_nat (npar p)) n p) C)))"
  shows "prf_ok V H (ptys \<rho> p) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) Hs)
    (leafprf (integer_of_nat (nhyp p)) (integer_of_nat (npar p)) n (integer_of_nat k)) (psubst \<rho> \<theta> 0 C)"
proof -
  let ?J = "npar p" and ?I = "nhyp p"
  let ?Ts = "ptys \<rho> p" and ?Hs = "phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) Hs"
  let ?Y = "list_implies (rmhyps (integer_of_nat ?J) n p) C"
  let ?F = "psubst \<rho> \<theta> 0"
  let ?vs = "map (\<lambda>(a, T). (a, tsubst \<rho> T)) vs"
  have hlv: "vars H' \<subseteq> vars (lift_pre p C)" if "(H', a) \<in> set (pre_hyps p)" for H' a
    using that pre_hyps_vars by blast
  have vY: "vars ?Y \<subseteq> vars (lift_pre p C)"
  proof -
    have "vars C \<subseteq> vars (lift_pre p C)" by (rule vars_lift_pre_C)
    moreover have "vars h \<subseteq> vars (lift_pre p C)" if "h \<in> set (rmhyps (integer_of_nat ?J) n p)" for h
      using vars_rmhyps[OF that] hlv by blast
    ultimately show ?thesis by (auto simp: vars_list_implies)
  qed
  then have clY: "\<forall>x\<in>vars ?Y. \<not> loose_bvar (\<theta> x) 0" using cl by (auto simp: closed_inst_def)
  have FN: "?F (list_forall vs ?Y) = list_forall ?vs (?F ?Y)"
    using clY psubst_closed_lev[of ?Y \<theta> "integer_of_nat (length vs)" \<rho>] by (simp add: psubst_list_forall)
  have Ts: "?Ts = rev (map snd ?vs)"
  proof -
    have a: "map snd ?vs = map (tsubst \<rho>) (map snd vs)" by (induction vs) auto
    have b: "?Ts = rev (map (tsubst \<rho>) (map snd (strip_params (lift_pre p C))))"
      using ptys_strip_params[OF items at, of \<rho>] by simp
    show ?thesis by (simp only: a b vs(2))
  qed
  have wY: "wty V ?Ts (?F ?Y) propT" using wN has_type_list_forall_body[of V "[]" ?vs "?F ?Y"]
    by (auto simp: FN Ts wty_def)
  have lvs: "length ?vs = ?J" using vs by simp
  have nlb: "no_loose_bound (tr (?F ?Y)) ?J"
    using has_type_closed[of V ?Ts "?F ?Y" propT] wY lvs by (simp add: wty_def Ts)
  text \<open>The flattened subgoal, applied to the parameters.\<close>
  have hk: "?Hs ! (k + ?I) = Hs ! k"
  proof -
    have "length (phs \<rho> \<theta> p) = ?I" by (simp add: phs_pre_hyps length_pre_hyps)
    moreover have "\<not> loose_bvar (Hs ! k) 0" using has_type_loose_bvar[of V "[]" "Hs ! k" propT] wk by (simp add: wty_def)
    ultimately show ?thesis using k by (simp add: nth_append incr_bv_no_loose)
  qed
  have "prf_ok V H ?Ts ?Hs (PBound (integer_of_nat k + integer_of_nat ?I)) (Hs ! k)"
    using prf_ok.PBound[of "integer_of_nat k + integer_of_nat ?I" ?Hs V ?Ts H] hk k wk has_type_weaken[of V "[]" "Hs ! k" propT ?Ts]
    by (simp add: wty_def phs_pre_hyps length_pre_hyps integer_of_nat_plus[symmetric])
  then have p1: "prf_ok V H ?Ts ?Hs (PBound (integer_of_nat k + integer_of_nat ?I)) (list_forall ?vs (?F ?Y))"
    using eN wN has_type_weaken[of V "[]" _ propT ?Ts] by (auto simp: FN wty_def intro: prf_ok.conv)
  let ?bs = "downto (integer_of_nat ?J - 1) 0"
  have lbs: "length ?bs = length ?vs" using lvs by (simp add: downto_map integer_reps integer_of_nat.rep_eq)
  have bs0: "\<forall>b\<in>set ?bs. 0 \<le> b" by (auto simp: downto_map integer_reps integer_of_nat.rep_eq)
  have tb: "\<forall>l<length ?vs. wty V ?Ts (Bound (?bs ! l)) (snd (?vs ! l))"
  proof (intro allI impI)
    fix l assume l: "l < length ?vs"
    have "?bs ! l = integer_of_nat (?J - 1 - l)"
      using l lvs by (simp add: downto_map integer_eq_iff integer_reps integer_of_nat.rep_eq of_nat_diff)
    moreover have "?Ts ! (?J - 1 - l) = snd (?vs ! l)" using l lvs by (simp add: Ts rev_nth)
    ultimately show "wty V ?Ts (Bound (?bs ! l)) (snd (?vs ! l))"
      using l lvs by (auto simp: wty_def has_type_Bound_iff Ts)
  qed
  obtain Y0 where Y0: "prf_ok V H ?Ts ?Hs (proof_combt (PBound (integer_of_nat k + integer_of_nat ?I)) (map Bound ?bs)) Y0"
    "tr Y0 = appb (Abs_m (length ?vs) (tr (?F ?Y))) (map nat_of_integer ?bs)"
    using prf_ok_combt_bounds[OF p1 lbs bs0 tb] by blast
  have "tr Y0 = tr (?F ?Y)" using Y0(2) nlb lvs by (simp add: map_nat_downto appb_downs)
  with Y0(1) wY have p2: "prf_ok V H ?Ts ?Hs (proof_combt (PBound (integer_of_nat k + integer_of_nat ?I)) (map Bound ?bs))
      (list_implies (map ?F (rmhyps (integer_of_nat ?J) n p)) (?F C))"
    by (auto simp: psubst_list_implies' intro: prf_ok.conv)
  text \<open>The other assumptions.\<close>
  let ?ks = "[l \<leftarrow> [0..<length (pre_hyps p)]. integer_of_nat l + 1 \<noteq> n]"
  let ?g = "\<lambda>l. case pre_hyps p ! l of (H', a) \<Rightarrow> incr_boundvars (integer_of_nat a) H'"
  have "list_all2 (prf_ok V H ?Ts ?Hs) (map (\<lambda>l. PBound (integer_of_nat ?I - 1 - integer_of_nat l)) ?ks)
      (map ?F (map ?g ?ks))"
  proof (rule list_all2_all_nthI)
    fix q assume q: "q < length (map (\<lambda>l. PBound (integer_of_nat ?I - 1 - integer_of_nat l)) ?ks)"
    let ?l = "?ks ! q"
    have l: "?l < length (pre_hyps p)" using q nth_mem[of q ?ks] by auto
    obtain H' a where Ha: "pre_hyps p ! ?l = (H', a)" by (cases "pre_hyps p ! ?l")
    have Hin: "(H', a) \<in> set (pre_hyps p)" using l Ha nth_mem by metis
    have clH: "\<forall>x\<in>vars H'. \<not> loose_bvar (\<theta> x) 0" using cl hlv[OF Hin] by (auto simp: closed_inst_def)
    have "?F (?g ?l) = incr_bv (integer_of_nat a) 0 (?F H')"
      using Ha psubst_incr_bv_closed[OF clH order_refl, of \<rho> "integer_of_nat a"] by (simp add: incr_boundvars_eq)
    moreover have "?Hs ! (?I - 1 - ?l) = incr_bv (integer_of_nat a) 0 (?F H')"
      using l Ha by (simp add: nth_append phs_pre_hyps length_pre_hyps rev_nth)
    moreover have "?g ?l \<in> set (rmhyps (integer_of_nat ?J) n p)"
    proof -
      have "?g ?l = map ?g ?ks ! q" using q by simp
      moreover have "map ?g ?ks ! q \<in> set (map ?g ?ks)" using q by (intro nth_mem) simp
      ultimately show ?thesis by (simp only: rmhyps_pre_hyps)
    qed
    then have "wty V ?Ts (?F (?g ?l)) propT"
      using wY by (auto simp: psubst_list_implies' wty_list_implies_iff)
    moreover have "integer_of_nat ?I - 1 - integer_of_nat ?l = integer_of_nat (?I - 1 - ?l)"
      using l by (simp add: length_pre_hyps integer_eq_iff integer_of_nat.rep_eq of_nat_diff)
    ultimately show "prf_ok V H ?Ts ?Hs (map (\<lambda>l. PBound (integer_of_nat ?I - 1 - integer_of_nat l)) ?ks ! q)
        (map ?F (map ?g ?ks) ! q)"
      using q l prf_ok.PBound[of "integer_of_nat (?I - 1 - ?l)" ?Hs V ?Ts H]
      by (auto simp: length_pre_hyps phs_pre_hyps)
  qed simp
  then have "list_all2 (prf_ok V H ?Ts ?Hs) (map PBound (removeAll (integer_of_nat ?I - n) (downto (integer_of_nat ?I - 1) 0)))
      (map ?F (rmhyps (integer_of_nat ?J) n p))"
    by (simp add: removeAll_downto rmhyps_pre_hyps length_pre_hyps comp_def)
  with p2 show ?thesis by (auto simp: leafprf_def intro: prf_ok_proof_combP)
qed


lemma remove_params_n_le:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic C \<Longrightarrow> integer_of_nat (npar p) = j \<Longrightarrow>
    ok (remove_params j n (lift_pre p C)) X \<Longrightarrow> n \<le> integer_of_nat (nhyp p)"
proof (induction p arbitrary: j n X)
  case Nil
  then have j: "j = 0" by simp
  show ?case
  proof (rule ccontr)
    assume "\<not> n \<le> integer_of_nat (nhyp [])"
    then have "0 < n" by simp
    with Nil.prems(2,4) j show False by (subst (asm) remove_params.simps) (simp add: atomic_def raise_def)
  qed
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    show ?thesis
    proof (cases "j = 0 \<and> n \<le> 0 \<or> n = 1")
      case True
      have h: "0 \<le> integer_of_nat (nhyp p) + 1" by (simp add: add_nonneg_nonneg)
      from True LImp show ?thesis using h by (auto simp: integer_of_nat_Suc intro: order.trans)
    next
      case False
      with Cons.prems(4) LImp c obtain B' where "ok (remove_params j (n - 1) (lift_pre p C)) B'"
        by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
      from Cons.IH[OF _ Cons.prems(2) _ this] Cons.prems(1,3) LImp show ?thesis
        by (simp add: integer_of_nat_Suc)
    qed
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    from Cons.prems(3) LAll have j1: "integer_of_nat (npar p) = j - 1" by (auto simp: integer_of_nat_Suc)
    have "0 \<le> integer_of_nat (npar p)" by simp
    with j1 have j: "integer_of_nat (npar p) = j - 1" "j \<noteq> 0" by auto
    with Cons.prems(4) LAll c have "ok (remove_params (j - 1) n (lift_pre p C)) X"
      by (subst (asm) remove_params.simps) simp
    from Cons.IH[OF _ Cons.prems(2) j(1) this] Cons.prems(1) LAll show ?thesis by simp
  qed
qed

theorem flatten_params_proof_ok:
  assumes cA: "cok A" and cl: "closed_inst \<theta> A" and fl: "ok (flatten_params vl n A) A'"
    and vl: "length (vl (map fst (strip_params A))) = length (strip_params A)"
    and wA: "wty V [] (psubst \<rho> \<theta> 0 A) propT" and wA': "wty V [] (psubst \<rho> \<theta> 0 A') propT"
    and k: "k < length Hs" and wk: "wty V [] (Hs ! k) propT"
    and eA': "tr (Hs ! k) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 A')"
    and wHs: "\<forall>h\<in>set Hs. wty V [] h propT"
  shows "prf_ok V H [] Hs (flatten_params_proof 0 0 n (A, integer_of_nat k)) (psubst \<rho> \<theta> 0 A)"
proof -
  obtain p C where ls: "lsplit A = (p, C)" by (cases "lsplit A")
  from lsplit_ok[OF ls] have A: "A = lift_pre p C" and items: "\<forall>i\<in>set p. litem_ok i" and at: "atomic C"
    by auto
  note it = cok_lift_pre_items[OF items cA[unfolded A]]
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  have lps: "length ?ps = npar p" using length_strip_params_lift_pre[OF items at] by (simp add: A)
  have lv: "length ?vars = npar p" using vl lps by simp
  have sv: "map snd ?vars = map snd ?ps" using vl by (simp add: map_snd_zip)
  from fl obtain A'' where r: "ok (remove_params (ilength ?vars) n A) A''" and A': "A' = list_forall ?vars A''"
    by (auto simp: flatten_params_def Let_def bindM_def return_def split: option.splits res.splits)
  have j: "ilength ?vars = integer_of_nat (npar p)" using lv by (simp add: ilength_eq)
  have nle: "n \<le> integer_of_nat (nhyp p)"
    using remove_params_n_le[OF items at j[symmetric]] r by (simp add: A)
  have impl: "\<forall>i\<in>set p. case i of LImp c H \<Rightarrow> c = implies | _ \<Rightarrow> True"
    using it by (auto split: litem.splits)
  have "remove_params (ilength ?vars) n A = return (list_implies (rmhyps (integer_of_nat (npar p)) n p) C)"
    unfolding j by (simp only: A) (rule remove_params_lift_pre[OF items at HOL.refl nle impl])
  with r have A'': "A'' = list_implies (rmhyps (integer_of_nat (npar p)) n p) C" by (simp add: return_def)
  have clA: "closed_inst \<theta> (lift_pre p C)" using cl by (simp add: A)
  have "prf_ok V H [] Hs (flatten_params_proof 0 0 n (lift_pre p C, integer_of_nat k)) (psubst \<rho> \<theta> 0 (lift_pre p C))"
  proof (rule fpp_gen[OF items at _ clA])
    show "cok (lift_pre p C)" using cA by (simp add: A)
    show "wty V [] (psubst \<rho> \<theta> 0 (lift_pre p C)) propT" using wA by (simp add: A)
    show "\<forall>h\<in>set Hs. wty V [] h propT" by (rule wHs)
    have sv': "map snd ?vars = map snd (strip_params (lift_pre p C))" using sv by (simp add: A)
    show "prf_ok V H (ptys \<rho> p @ []) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) Hs)
        (leafprf (0 + integer_of_nat (nhyp p)) (0 + integer_of_nat (npar p)) n (integer_of_nat k)) (psubst \<rho> \<theta> 0 C)"
      using fpp_leaf[OF items at clA lv sv' k wk] wA' eA' by (simp add: A' A'')
  qed
  then show ?thesis by (simp add: A)
qed

end

end
