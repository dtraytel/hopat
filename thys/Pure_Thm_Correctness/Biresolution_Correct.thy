section \<open>Correctness of \<open>biresolution\<close>\<close>

theory Biresolution_Correct
  imports Bicompose_Complete "Pure_Thm.Pure_Biresolution"
begin

text \<open>
  \<open>biresolution\<close> lifts each rule over the subgoal (\<^const>\<open>lift_rule\<close>) and composes it with the
  proof state by \<^const>\<open>bicompose_aux\<close>. The lifted rule has the shape that the theorems on
  \<^const>\<open>bicompose_aux\<close> assume (\<^const>\<open>lifted_over\<close>), its variables are those of the rule with
  their indices incremented above the proof state, and it is valid and well-typed if the rule
  is.
\<close>


subsection \<open>The syntax of lifted rules\<close>

lemma lift_all_aux_atomic: "atomic G \<Longrightarrow> lift_all_aux inc Ts G t = incr_indexes (rev Ts) inc t"
  by (cases "(inc, Ts, G, t)" rule: lift_all_aux.cases) (auto simp: atomic_def)

lemma lift_abs_aux_atomic: "atomic G \<Longrightarrow> lift_abs_aux inc Ts G t = incr_indexes (rev Ts) inc t"
  by (cases "(inc, Ts, G, t)" rule: lift_abs_aux.cases) (auto simp: atomic_def)

lemma lift_all_aux_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic G0 \<Longrightarrow>
    lift_all_aux inc Ts (lift_pre p G0) t = lift_pre p (incr_indexes (rev Ts @ ptys p) inc t)"
proof (induction p arbitrary: Ts)
  case Nil
  then show ?case by (simp add: lift_all_aux_atomic)
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems obtain U where "c = Const STR ''Pure.imp'' U" by auto
    with Cons LImp show ?thesis by simp
  next
    case (LAll c a T)
    with Cons.prems obtain U where "c = Const STR ''Pure.all'' U" by auto
    with Cons LAll show ?thesis by simp
  qed
qed

lemma lift_abs_aux_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic G0 \<Longrightarrow>
    lift_abs_aux inc Ts (lift_pre p G0) t = abs_pre p (incr_indexes (rev Ts @ ptys p) inc t)"
proof (induction p arbitrary: Ts)
  case Nil
  then show ?case by (simp add: lift_abs_aux_atomic)
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems obtain U where "c = Const STR ''Pure.imp'' U" by auto
    with Cons LImp show ?thesis by simp
  next
    case (LAll c a T)
    with Cons.prems obtain U where "c = Const STR ''Pure.all'' U" by auto
    with Cons LAll show ?thesis by simp
  qed
qed

lemma lift_all_lsplit:
  "lsplit G = (p, G0) \<Longrightarrow> lift_all inc G t = lift_pre p (incr_indexes (ptys p) inc t)"
  using lift_all_aux_lift_pre[of p G0 inc "[]" t] by (simp add: lift_all_def lsplit_lift_pre_iff)

lemma lift_abs_lsplit:
  "lsplit G = (p, G0) \<Longrightarrow> lift_abs inc G t = abs_pre p (incr_indexes (ptys p) inc t)"
  using lift_abs_aux_lift_pre[of p G0 inc "[]" t] by (simp add: lift_abs_def lsplit_lift_pre_iff)

lemma vars_incr_idx: "vars (incr_idx Ts inc lev t) = (\<lambda>(x, i). (x, i + inc)) ` vars t"
proof (induction Ts inc lev t rule: incr_idx.induct)
  case (1 Ts inc lev x i T)
  have "vars (combound u n k) = vars u" for u n k
    by (induction u n k rule: combound.induct) simp_all
  then show ?case by simp
qed auto

lemma vars_incr_indexes: "vars (incr_indexes Ts inc t) = (\<lambda>(x, i). (x, i + inc)) ` vars t"
  by (auto simp: incr_indexes_def vars_incr_idx)

lemma strip_imp_list_implies:
  "strip_imp_prems (list_implies As B) = As @ strip_imp_prems B"
  "strip_imp_concl (list_implies As B) = strip_imp_concl B"
  by (induction As) (subst strip_imp_prems.simps strip_imp_concl.simps; simp add: implies_def)+

lemma list_implies_strip_imp: "cok t \<Longrightarrow> t = list_implies (strip_imp_prems t) (strip_imp_concl t)"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "dest_imp t")
    case (Some AB)
    then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
    then obtain U where t: "t = Const STR ''Pure.imp'' U $ A $ B" by (auto simp: dest_imp_Some)
    from cok_imp[of _ U A] less.prems t have "U = imp_type" "cok B" by auto
    with less.IH[of B] AB show ?thesis
      by (subst strip_imp_prems.simps, subst strip_imp_concl.simps)
        (auto simp: t implies_imp_type dest_size)
  next
    case None
    then show ?thesis
      by (subst strip_imp_prems.simps, subst strip_imp_concl.simps) simp
  qed
qed

lemma vars_strip_imp:
  "A \<in> set (strip_imp_prems t) \<Longrightarrow> vars A \<subseteq> vars t" "vars (strip_imp_concl t) \<subseteq> vars t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  {
    case 1
    show ?case
    proof (cases "dest_imp t")
      case (Some AB)
      then obtain A' B where AB: "dest_imp t = Some (A', B)" by (cases AB) auto
      then obtain U where t: "t = Const STR ''Pure.imp'' U $ A' $ B" by (auto simp: dest_imp_Some)
      from 1 AB have "A = A' \<or> A \<in> set (strip_imp_prems B)"
        by (subst (asm) strip_imp_prems.simps) simp
      with less.IH(1)[of B] t show ?thesis by (auto simp: dest_size)
    next
      case None
      with 1 show ?thesis by (subst (asm) strip_imp_prems.simps) simp
    qed
  next
    case 2
    show ?case
    proof (cases "dest_imp t")
      case (Some AB)
      then obtain A' B where AB: "dest_imp t = Some (A', B)" by (cases AB) auto
      then obtain U where t: "t = Const STR ''Pure.imp'' U $ A' $ B" by (auto simp: dest_imp_Some)
      from less.IH(2)[of B] AB t show ?thesis
        by (subst strip_imp_concl.simps) (auto simp: dest_size)
    next
      case None
      then show ?thesis by (subst strip_imp_concl.simps) simp
    qed
  }
qed

lemma count_prems_strip_imp: "count_prems t = ilength (strip_imp_prems t)"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "dest_imp t")
    case (Some AB)
    then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
    from less.IH[of B] AB dest_imp_size[OF AB] show ?thesis
      by (subst count_prems.simps, subst strip_imp_prems.simps) (simp add: ilength_Cons)
  next
    case None
    then show ?thesis
      by (subst count_prems.simps, subst strip_imp_prems.simps) (simp add: ilength_eq)
  qed
qed

text \<open>A rule lifted over a subgoal of a proof state is lifted over it (\<^const>\<open>lifted_over\<close>).\<close>

lemma lift_rule_lifted_over:
  assumes "\<forall>x\<in>vars (th_prop rule). 0 \<le> snd x" "0 \<le> smax"
  shows "lifted_over smax G (th_prop (lift_rule G smax rule)) (nprems_of rule)"
proof -
  obtain p G0 where ls: "lsplit G = (p, G0)" by (cases "lsplit G")
  let ?inc = "smax + 1" and ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  let ?f = "incr_indexes (ptys p) ?inc"
  have la: "lift_all ?inc G = (\<lambda>t. lift_pre p (?f t))" by (rule ext) (rule lift_all_lsplit[OF ls])
  have P: "th_prop (lift_rule G smax rule) = list_implies (map (lift_pre p) (map ?f ?As)) (lift_pre p (?f ?B))"
    by (simp add: lift_rule_def Let_def la comp_def)
  have v: "\<forall>x\<in>vars X. 0 \<le> snd x" if "X \<in> insert ?B (set ?As)" for X
    using that vars_strip_imp(1)[of _ "th_prop rule"] vars_strip_imp(2)[of "th_prop rule"] assms(1) by blast
  have "\<forall>x\<in>vars (?f X). smax < snd x" if "X \<in> insert ?B (set ?As)" for X
    using v[OF that] by (auto simp: vars_incr_indexes)
  then have "\<forall>X\<in>insert (?f ?B) (set (map ?f ?As)). \<forall>x\<in>vars X. smax < snd x" by auto
  moreover have "nprems_of rule = ilength (map ?f ?As)"
    by (simp add: nprems_of_def count_prems_strip_imp ilength_eq)
  ultimately show ?thesis unfolding lifted_over_def using ls P by blast
qed


subsection \<open>Well-formedness of lifted terms\<close>

lemma incr_tvar_0[simp]: "incr_tvar 0 T = T"
proof (induction T)
  case (Type a Ts)
  then show ?case by (simp add: map_idI)
next
  case (TVar x S)
  then show ?case by (cases x) simp
qed simp

lemma incr_idx_0: "incr_idx [] 0 lev t = t"
  by (induction t arbitrary: lev) auto

lemma incr_indexes_idx: "incr_indexes Ts inc t = incr_idx Ts inc 0 t"
  by (simp add: incr_indexes_def incr_idx_0)

lemma combound_not_Const: "combound (Var x T) n k \<noteq> Const c U"
  by (induction "Var x T" n k rule: combound.induct) auto

lemma cok_app_nonConst: "(\<And>c U. s \<noteq> Const c U) \<Longrightarrow> cok (s $ t) \<longleftrightarrow> cok s \<and> cok t"
  by (cases s) auto

lemma combound_not_Abs: "combound (Var x T) n k \<noteq> Abs a U b"
  by (induction "Var x T" n k rule: combound.induct) auto

lemma cok_app_nonAbs: "(\<And>a T b. t \<noteq> Abs a T b) \<Longrightarrow> cok (s $ t) \<longleftrightarrow> cok s \<and> cok t"
  by (cases s; cases t) auto

lemma cok_combound: "cok t \<Longrightarrow> cok (combound t n k)"
  by (induction t n k rule: combound.induct) auto

lemma cok_incr_idx: "cok X \<Longrightarrow> cok (incr_idx Ts inc lev X)"
proof (induction X arbitrary: lev rule: cok.induct)
  case (1 c U a T b)
  then show ?case by (auto simp: imp_type_def all_type_def propT_def)
next
  case (2 c U)
  then show ?case by (auto simp: imp_type_def all_type_def propT_def)
qed (auto simp: cok_combound cok_app_nonConst combound_not_Const cok_app_nonAbs combound_not_Abs)

lemma cok_lift_pre: "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> cok (lift_pre p G0) \<Longrightarrow> cok Y \<Longrightarrow> cok (lift_pre p Y)"
proof (induction p)
  case (Cons i p)
  then show ?case by (cases i) auto
qed simp

lemma map_BVar_upt_Suc:
  "map (\<lambda>j. BVar (m + j)) [0..<Suc k] = BVar m # map (\<lambda>j. BVar (Suc m + j)) [0..<k]"
  by (induction k) auto

lemma tr_combound:
  "0 \<le> n \<Longrightarrow> tr (combound t n k) = tr t \<degree>\<degree> rev (map (\<lambda>j. BVar (nat_of_integer n + j)) [0..<k])"
proof (induction t n k rule: combound.induct)
  case (2 t n k)
  have "nat_of_integer (n + 1) = Suc (nat_of_integer n)" using "2.prems"
    by (simp add: integer_eq_iff integer_reps nat_add_distrib)
  with 2 show ?case by (simp only: map_BVar_upt_Suc) simp
qed simp

lemma no_loose_bound_incr_idx:
  "no_loose_bound (tr X) (nat_of_integer lev) \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    no_loose_bound (tr (incr_idx Ts inc lev X)) (nat_of_integer lev + length Ts)"
proof (induction X arbitrary: lev)
  case (Var x T)
  then show ?case by (cases x) (simp add: tr_combound no_loose_bound_list_app)
next
  case (Abs a T t)
  from Abs.prems have "no_loose_bound (tr t) (nat_of_integer (lev + 1))" "0 \<le> lev + 1"
    by (simp_all add: integer_eq_iff integer_reps nat_add_distrib)
  from Abs.IH[OF this] Abs.prems show ?case by (simp add: integer_eq_iff integer_reps nat_add_distrib)
qed auto

lemma no_loose_bound_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> no_loose_bound (tr (lift_pre p G0)) k \<Longrightarrow> no_loose_bound (tr Y) (k + nall p) \<Longrightarrow>
    no_loose_bound (tr (lift_pre p Y)) k"
proof (induction p arbitrary: k)
  case (Cons i p)
  then show ?case by (cases i) auto
qed simp

lemma nall_ptys: "length (ptys p) = nall p"
  by (induction p rule: ptys.induct) auto


subsection \<open>The instances of lifted terms\<close>

text \<open>
  The indices of variables incremented by \<open>inc\<close> (\<open>Logic.incr_indexes\<close>): for the types, an
  instantiation \<open>\<rho>\<close> of the incremented type variables is the instantiation \<open>tinc inc \<rho>\<close> of the
  original ones; for the terms, the substitution \<open>\<sigma>\<close> of the incremented variables, applied to
  the instances \<open>us\<close> of the parameters, is the substitution \<open>isub inc \<sigma> us\<close> of the original ones.
\<close>

definition incr_ix :: "integer \<Rightarrow> indexname \<Rightarrow> indexname" where
  "incr_ix inc x = (fst x, snd x + inc)"

definition tinc :: "integer \<Rightarrow> tinst \<Rightarrow> tinst" where
  "tinc inc \<rho> v S = \<rho> (incr_ix inc v) S"

lemma tsubst_incr_tvar: "tsubst \<rho> (incr_tvar inc T) = tsubst (tinc inc \<rho>) T"
proof (induction T)
  case (TVar x S)
  then show ?case by (cases x) (simp add: tinc_def incr_ix_def)
qed simp_all

definition isub :: "integer \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> dB list \<Rightarrow> nat \<Rightarrow> dB" where
  "isub inc \<sigma> us n = (if \<exists>x. n = code (AVar x)
    then \<sigma> (code (AVar (incr_ix inc (THE x. n = code (AVar x))))) \<degree>\<degree> us else \<sigma> n)"

lemma isub_AVar[simp]: "isub inc \<sigma> us (code (AVar x)) = \<sigma> (code (AVar (incr_ix inc x))) \<degree>\<degree> us"
  by (auto simp: isub_def)

lemma isub_rigid: "rigid_code n \<Longrightarrow> isub inc \<sigma> us n = \<sigma> n"
  by (auto simp: isub_def rigid_code_def)

lemma substs_list_app: "substs k vs (t \<degree>\<degree> ts) = substs k vs t \<degree>\<degree> map (substs k vs) ts"
  by (induction ts arbitrary: t) simp_all

lemma substs_incr_idx:
  assumes "\<forall>v\<in>set vs. closed v" "length vs = length Ts" "closed_on UNIV \<sigma>"
  shows "no_loose_bound (tr X) (nat_of_integer lev) \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    substs (nat_of_integer lev) vs (mk_subst \<sigma> (tr (inst \<rho> (incr_idx Ts inc lev X)))) =
    mk_subst (isub inc \<sigma> (rev vs)) (tr (inst (tinc inc \<rho>) X))"
proof (induction X arbitrary: lev)
  case (Var x T)
  obtain a i where x: "x = (a, i)" by (cases x)
  have cl: "closed (\<sigma> n)" for n using assms(3) by (simp add: closed_on_def)
  have m: "map (\<lambda>j. substs (nat_of_integer lev) vs (mk_subst \<sigma> (BVar (nat_of_integer lev + j))))
      [0..<length Ts] = vs"
    using assms(2) by (auto intro: nth_equalityI)
  have "map (\<lambda>u. substs (nat_of_integer lev) vs (mk_subst \<sigma> u))
      (rev (map (\<lambda>j. BVar (nat_of_integer lev + j)) [0..<length Ts])) = rev vs"
    using m by (simp add: rev_map[symmetric] comp_def)
  with Var.prems cl show ?case
    by (simp add: x tr_combound substs_list_app incr_ix_def tinc_def comp_def)
next
  case (Bound i)
  then show ?case by simp
next
  case (Abs a T t)
  from Abs.prems have "no_loose_bound (tr t) (nat_of_integer (lev + 1))" "0 \<le> lev + 1"
    by (simp_all add: integer_eq_iff integer_reps nat_add_distrib)
  from Abs.IH[OF this] Abs.prems show ?case by (simp add: integer_eq_iff integer_reps nat_add_distrib)
next
  case (Const c T)
  have cl: "closed (\<sigma> n)" for n using assms(3) by (simp add: closed_on_def)
  show ?case by (simp add: tsubst_incr_tvar isub_rigid cl)
next
  case (Free c T)
  have cl: "closed (\<sigma> n)" for n using assms(3) by (simp add: closed_on_def)
  show ?case by (simp add: tsubst_incr_tvar isub_rigid cl)
qed simp

lemma (in wf_algebra) gtinst_tinc: "gtinst \<rho> \<Longrightarrow> gtinst (tinc inc \<rho>)"
  by (auto simp: gtinst_def wsinst_def tinc_def incr_ix_def)

lemma closed_isub: "closed_on UNIV \<sigma> \<Longrightarrow> \<forall>u\<in>set us. closed u \<Longrightarrow> closed_on UNIV (isub inc \<sigma> us)"
  by (auto simp: closed_on_def isub_def no_loose_bound_list_app)

lemma rigid_isub: "rigid_subst \<sigma> \<Longrightarrow> rigid_subst (isub inc \<sigma> us)"
  by (simp add: rigid_subst_def isub_rigid)


subsection \<open>Validity of lifted rules\<close>

context pure_sem
begin

text \<open>
  If \<open>Y\<close> holds whenever all of \<open>Xs\<close> hold, for all instances of the parameters of a prefix, then
  \<open>Y\<close> under the prefix holds if all of \<open>Xs\<close> under the prefix do.
\<close>

lemma holds_lift_pre_list:
  assumes "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "\<forall>i\<in>set p. litem_ok i"
    "\<forall>X\<in>insert Y (set Xs). cok (lift_pre p X) \<and> no_loose_bound (tr (lift_pre p X)) (length ws)"
    "\<forall>w\<in>set ws. closed w"
    "\<And>vs. \<forall>v\<in>set vs. closed v \<Longrightarrow> length vs = nall p \<Longrightarrow>
      \<forall>X\<in>set Xs. holds (substs 0 (vs @ ws) (sm \<rho> \<sigma> X)) \<Longrightarrow> holds (substs 0 (vs @ ws) (sm \<rho> \<sigma> Y))"
    "\<forall>X\<in>set Xs. holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p X)))"
  shows "holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p Y)))"
  using assms(3-)
proof (induction p arbitrary: ws)
  case Nil
  from Nil.prems(4)[of "[]"] Nil.prems(5) show ?case by simp
next
  case (Cons i p)
  have cl: "closed (substs 0 ws (sm \<rho> \<sigma> Z))" if "no_loose_bound (tr Z) (length ws)" for Z
    using no_loose_bound_substs[OF Cons.prems(3), of _ 0] that assms(2) by (simp add: no_loose_bound_sm)
  show ?case
  proof (cases i)
    case (LImp c H)
    from Cons.prems(1) LImp obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have ok: "U = imp_type \<and> cok H \<and> cok (lift_pre p X)" if "X \<in> insert Y (set Xs)" for X
      using cok_imp[of _ U H] Cons.prems(2) that LImp c by auto
    then have c: "c = implies" using c by (auto simp: implies_imp_type)
    have sm: "substs 0 ws (sm \<rho> \<sigma> (lift_pre (i # p) Z)) =
        dIMP (substs 0 ws (sm \<rho> \<sigma> H)) (substs 0 ws (sm \<rho> \<sigma> (lift_pre p Z)))" for Z
      using assms(1) by (simp add: LImp c)
    have nbH: "no_loose_bound (tr H) (length ws)"
      using Cons.prems(2) by (auto simp: LImp c)
    have nb: "no_loose_bound (tr (lift_pre p X)) (length ws)" if "X \<in> insert Y (set Xs)" for X
      using Cons.prems(2) that by (auto simp: LImp c)
    have h: "holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p Y)))" if hH: "holds (substs 0 ws (sm \<rho> \<sigma> H))"
    proof (rule Cons.IH)
      show "\<forall>X\<in>set Xs. holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p X)))"
        using Cons.prems(5) hH unfolding sm by (auto simp: holds_imp cl nbH nb)
    qed (use Cons.prems ok nb in \<open>simp_all add: LImp\<close>)
    show ?thesis unfolding sm using h by (simp add: holds_imp cl nbH nb)
  next
    case (LAll c a T)
    from Cons.prems(1) LAll obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    have ok: "U = all_type T \<and> cok (lift_pre p X)" if "X \<in> insert Y (set Xs)" for X
      using Cons.prems(2) that LAll c by auto
    then have c: "c = all_const T" using c by (auto simp: all_const_all_type)
    have sm: "substs 0 ws (sm \<rho> \<sigma> (lift_pre (i # p) Z)) =
        dALL (tsubst \<rho> T) (substs (Suc 0) ws (sm \<rho> \<sigma> (lift_pre p Z)))" for Z
      using assms(1) by (simp add: LAll c)
    have nb: "no_loose_bound (tr (lift_pre p X)) (Suc (length ws))" if "X \<in> insert Y (set Xs)" for X
      using Cons.prems(2) that by (auto simp: LAll c)
    have nb1: "no_loose_bound (substs (Suc 0) ws (sm \<rho> \<sigma> (lift_pre p Z))) 1"
      if "no_loose_bound (tr (lift_pre p Z)) (Suc (length ws))" for Z
      using no_loose_bound_substs[OF Cons.prems(3), of _ "Suc 0"] that assms(2) by (simp add: no_loose_bound_sm)
    have eq: "(substs (Suc 0) ws t)[u/0] = substs 0 (u # ws) t" if "inhab (tsubst \<rho> T) u" for u t
      using substs_Suc_subst[OF inhab_closed[OF that] Cons.prems(3)] by simp
    have IH: "holds (substs 0 (u # ws) (sm \<rho> \<sigma> (lift_pre p Y)))" if u: "inhab (tsubst \<rho> T) u" for u
    proof (rule Cons.IH)
      show "\<forall>X\<in>insert Y (set Xs). cok (lift_pre p X) \<and> no_loose_bound (tr (lift_pre p X)) (length (u # ws))"
        using ok nb by simp
      show "\<forall>w\<in>set (u # ws). closed w" using Cons.prems(3) inhab_closed[OF u] by simp
      show "holds (substs 0 (vs @ u # ws) (sm \<rho> \<sigma> Y))"
        if "\<forall>v\<in>set vs. closed v" "length vs = nall p" "\<forall>X\<in>set Xs. holds (substs 0 (vs @ u # ws) (sm \<rho> \<sigma> X))"
        for vs
        using Cons.prems(4)[of "vs @ [u]"] that inhab_closed[OF u] by (simp add: LAll)
      show "\<forall>X\<in>set Xs. holds (substs 0 (u # ws) (sm \<rho> \<sigma> (lift_pre p X)))"
      proof
        fix X assume X: "X \<in> set Xs"
        with Cons.prems(5) have "holds (dALL (tsubst \<rho> T) (substs (Suc 0) ws (sm \<rho> \<sigma> (lift_pre p X))))"
          unfolding sm by blast
        with holds_all[OF nb1[OF nb]] X u eq show "holds (substs 0 (u # ws) (sm \<rho> \<sigma> (lift_pre p X)))"
          by auto
      qed
    qed (use Cons.prems in simp)
    then show ?thesis unfolding sm using eq by (simp add: holds_all[OF nb1[OF nb]])
  qed
qed

end

lemma cok_list_implies: "cok (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. cok A) \<and> cok B"
  by (induction As) simp_all

context bicompose_sem
begin

text \<open>A rule lifted over a closed subgoal is valid if the rule is.\<close>

theorem lift_rule_valid:
  assumes valid: "valid (th_tpairs rule) (th_prop rule)"
    and ls: "lsplit G = (p, G0)" and G: "cok G" "no_loose_bound (tr G) 0"
    and rule: "cok (th_prop rule)" "no_loose_bound (tr (th_prop rule)) 0"
      "\<forall>(t, u)\<in>set (th_tpairs rule). no_loose_bound (tr t) 0 \<and> no_loose_bound (tr u) 0"
  shows "valid (th_tpairs (lift_rule G gmax rule)) (th_prop (lift_rule G gmax rule))"
proof (rule validI)
  fix \<rho> \<sigma> assume \<rho>: "gtinst \<rho>" and cl: "closed_on UNIV \<sigma>" and rg: "rigid_subst \<sigma>"
    and tps: "\<And>t u. (t, u) \<in> set (th_tpairs (lift_rule G gmax rule)) \<Longrightarrow> sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u"
  let ?inc = "gmax + 1"
  let ?f = "incr_indexes (ptys p) ?inc"
  let ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  from lsplit_ok[OF ls] have Gp: "G = lift_pre p G0" and ok: "\<forall>i\<in>set p. litem_ok i" by auto
  have rp: "th_prop rule = list_implies ?As ?B" by (rule list_implies_strip_imp[OF rule(1)])
  have nbAB: "no_loose_bound (tr X) 0" if "X \<in> insert ?B (set ?As)" for X
    using rule(2) that by (subst (asm) rp) (auto simp: no_loose_bound_list_implies)
  have cokAB: "cok X" if "X \<in> insert ?B (set ?As)" for X
    using rule(1) that by (subst (asm) rp) (auto simp: cok_list_implies)
  have la: "lift_all ?inc G = (\<lambda>t. lift_pre p (?f t))" by (rule ext) (rule lift_all_lsplit[OF ls])
  have P: "th_prop (lift_rule G gmax rule) = list_implies (map (\<lambda>X. lift_pre p (?f X)) ?As) (lift_pre p (?f ?B))"
    by (simp add: lift_rule_def Let_def la)
  text \<open>The instance of the rule for instances \<open>vs\<close> of the parameters.\<close>
  have inst: "substs 0 vs (sm \<rho> \<sigma> (?f X)) = sm (tinc ?inc \<rho>) (isub ?inc \<sigma> (rev vs)) X"
    if "\<forall>v\<in>set vs. closed v" "length vs = nall p" "no_loose_bound (tr X) 0" for vs X
    using substs_incr_idx[OF that(1) _ cl, where X = X and lev = 0 and \<rho> = \<rho> and inc = ?inc and Ts = "ptys p"]
      that(2,3)
    by (simp add: sm_def incr_indexes_idx nall_ptys)
  have hrule: "holds (substs 0 vs (sm \<rho> \<sigma> (?f ?B)))"
    if vs: "\<forall>v\<in>set vs. closed v" "length vs = nall p"
      and hA: "\<forall>X\<in>set (map ?f ?As). holds (substs 0 vs (sm \<rho> \<sigma> X))" for vs
  proof -
    let ?\<rho> = "tinc ?inc \<rho>" and ?\<sigma> = "isub ?inc \<sigma> (rev vs)"
    have cl': "closed_on UNIV ?\<sigma>" by (rule closed_isub[OF cl]) (use vs in simp)
    have rg': "rigid_subst ?\<sigma>" by (rule rigid_isub[OF rg])
    have tp: "sm ?\<rho> ?\<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm ?\<rho> ?\<sigma> u" if tu: "(t, u) \<in> set (th_tpairs rule)" for t u
    proof -
      have "(lift_abs ?inc G t, lift_abs ?inc G u) \<in> set (th_tpairs (lift_rule G gmax rule))"
        using tu by (force simp: lift_rule_def Let_def)
      from tps[OF this] have "sm \<rho> \<sigma> (abs_pre p (?f t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> (abs_pre p (?f u))"
        by (simp add: lift_abs_lsplit[OF ls])
      then have e: "Abs_m (nall p) (sm \<rho> \<sigma> (?f t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (nall p) (sm \<rho> \<sigma> (?f u))"
        by (simp add: sm_abs_pre)
      have cu: "\<forall>u\<in>set (rev vs). closed u" "length (rev vs) = nall p" using vs by simp_all
      have "substs 0 vs (sm \<rho> \<sigma> (?f t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (nall p) (sm \<rho> \<sigma> (?f t)) \<degree>\<degree> rev vs"
        using Abs_m_apps_substs[OF cu, of "sm \<rho> \<sigma> (?f t)"] by (simp add: equiv_sym beta_into_equiv)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (nall p) (sm \<rho> \<sigma> (?f u)) \<degree>\<degree> rev vs"
        by (rule equiv_list_app[OF e]) (simp add: list_all2_refl)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 vs (sm \<rho> \<sigma> (?f u))"
        using Abs_m_apps_substs[OF cu, of "sm \<rho> \<sigma> (?f u)"] by (simp add: beta_into_equiv)
      finally show ?thesis using inst[OF vs] rule(3) tu by auto
    qed
    from validD[OF valid gtinst_tinc[OF \<rho>] cl' rg' tp]
    have "holds (sm ?\<rho> ?\<sigma> (list_implies ?As ?B))" by (simp flip: rp)
    then have h: "holds (foldr dIMP (map (sm ?\<rho> ?\<sigma>) ?As) (sm ?\<rho> ?\<sigma> ?B))"
      by (simp add: sm_list_implies[OF rg'])
    have clAB: "closed (sm ?\<rho> ?\<sigma> X)" if "X \<in> insert ?B (set ?As)" for X
      using nbAB[OF that] cl' by (simp add: no_loose_bound_sm)
    have "\<forall>A\<in>set ?As. holds (sm ?\<rho> ?\<sigma> A)" using hA inst[OF vs] nbAB by auto
    with h clAB have "holds (sm ?\<rho> ?\<sigma> ?B)" by (subst (asm) holds_foldr_dIMP) auto
    then show ?thesis using inst[OF vs] nbAB by simp
  qed
  have nbG: "no_loose_bound (tr (lift_pre p G0)) 0" using G(2) Gp by simp
  have cokG: "cok (lift_pre p G0)" using G(1) Gp by simp
  have wfX: "cok (lift_pre p (?f X)) \<and> no_loose_bound (tr (lift_pre p (?f X))) 0"
    if "X \<in> insert ?B (set ?As)" for X
  proof
    show "cok (lift_pre p (?f X))"
      by (rule cok_lift_pre[OF ok cokG]) (simp add: incr_indexes_idx cok_incr_idx cokAB[OF that])
    have "no_loose_bound (tr (?f X)) (0 + nall p)"
      using no_loose_bound_incr_idx[of X 0 "ptys p" ?inc] nbAB[OF that] by (simp add: incr_indexes_idx nall_ptys)
    then show "no_loose_bound (tr (lift_pre p (?f X))) 0" by (rule no_loose_bound_lift_pre[OF ok nbG])
  qed
  have "holds (substs 0 [] (sm \<rho> \<sigma> (lift_pre p (?f ?B))))"
    if "\<forall>X\<in>set (map ?f ?As). holds (substs 0 [] (sm \<rho> \<sigma> (lift_pre p X)))"
    by (rule holds_lift_pre_list[OF rg cl ok _ _ _ that]) (use wfX hrule in auto)
  then have imp: "(\<forall>A\<in>set ?As. holds (sm \<rho> \<sigma> (lift_pre p (?f A)))) \<longrightarrow> holds (sm \<rho> \<sigma> (lift_pre p (?f ?B)))"
    by simp
  have clL: "closed (sm \<rho> \<sigma> (lift_pre p (?f X)))" if "X \<in> insert ?B (set ?As)" for X
    using wfX[OF that] cl by (simp add: no_loose_bound_sm)
  show "holds (sm \<rho> \<sigma> (th_prop (lift_rule G gmax rule)))"
    unfolding P sm_list_implies[OF rg] using imp clL by (subst holds_foldr_dIMP) auto
qed

end

end
