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

end

end
