section \<open>Correctness of \<open>biresolution\<close>\<close>

theory Biresolution_Correct
  imports Bicompose_Complete "Pure_Thm.Pure_Biresolution"
begin

text \<open>
  \<open>biresolution\<close> lifts each rule over the subgoal (\<^const>\<open>lift_rule\<close>) and composes it with the
  proof state by \<^const>\<open>bicompose_aux\<close>. The lifted rule has the shape that the theorems on
  \<^const>\<open>bicompose_aux\<close> assume (\<^const>\<open>lifted_over\<close>), its variables are those of the rule with
  their indices incremented above the proof state, and it is valid and well-typed if the rule
  is. Hence the theorems on \<^const>\<open>bicompose_aux\<close> carry over to \<open>biresolution\<close>: its results are
  valid, the evaluation of its sequence of results terminates, and it enumerates all results of
  the compositions of the rules that pass its quick test.
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
  assumes "\<forall>x\<in>vars (th_prop rule). 0 \<le> snd x"
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


subsection \<open>Typing of lifted rules\<close>

lemma incr_tvar_propT[simp]: "incr_tvar inc propT = propT"
  by (simp add: propT_def)

lemma has_type_combound:
  "has_type W Ctx t (foldr fun_type Ts T) \<Longrightarrow> 0 \<le> n \<Longrightarrow>
    (\<forall>j<length Ts. nat_of_integer n + j < length Ctx \<and> Ctx ! (nat_of_integer n + j) = rev Ts ! j) \<Longrightarrow>
    has_type W Ctx (combound t n (length Ts)) T"
proof (induction Ts arbitrary: n T rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc Tl Ts)
  have n1: "nat_of_integer (n + 1) = Suc (nat_of_integer n)" using snoc.prems(2)
    by (simp add: integer_eq_iff integer_reps nat_add_distrib)
  have "has_type W Ctx (combound t (n + 1) (length Ts)) (Tl \<rightarrow>\<^sub>T T)"
  proof (rule snoc.IH)
    show "has_type W Ctx t (foldr fun_type Ts (Tl \<rightarrow>\<^sub>T T))" using snoc.prems(1) by simp
    show "0 \<le> n + 1" using snoc.prems(2) by simp
    show "\<forall>j<length Ts. nat_of_integer (n + 1) + j < length Ctx \<and> Ctx ! (nat_of_integer (n + 1) + j) = rev Ts ! j"
    proof (intro allI impI)
      fix j assume "j < length Ts"
      with snoc.prems(3)[rule_format, of "Suc j"] n1
      show "nat_of_integer (n + 1) + j < length Ctx \<and> Ctx ! (nat_of_integer (n + 1) + j) = rev Ts ! j"
        by simp
    qed
  qed
  moreover have "has_type W Ctx (Bound n) Tl"
    using snoc.prems(2) snoc.prems(3)[rule_format, of 0] by (intro has_type.Bound) simp_all
  ultimately show ?case by (simp add: has_type.App)
qed

lemma const_typ_ok_incr_tvar[intro]: "const_typ_ok c T \<Longrightarrow> const_typ_ok c (incr_tvar inc T)"
  by (auto simp: const_typ_ok_def)

lemma has_type_incr_idx:
  "has_type W Us X T \<Longrightarrow> 0 \<le> lev \<Longrightarrow> length Us = nat_of_integer lev \<Longrightarrow>
    (\<forall>x\<in>vars X. W' (incr_ix inc x) = foldr fun_type Ts (incr_tvar inc (W x))) \<Longrightarrow>
    has_type W' (map (incr_tvar inc) Us @ rev Ts) (incr_idx Ts inc lev X) (incr_tvar inc T)"
proof (induction X arbitrary: Us lev T)
  case (Var x T0)
  obtain a i where x: "x = (a, i)" by (cases x)
  from Var.prems(1) have T: "T = T0" "W x = T0" by (auto elim: has_type_elims)
  have "has_type W' (map (incr_tvar inc) Us @ rev Ts) (Var (a, i + inc) (foldr fun_type Ts (incr_tvar inc T0)))
      (foldr fun_type Ts (incr_tvar inc T0))"
    using Var.prems(4) T x by (intro has_type.Var) (simp add: incr_ix_def)
  then show ?case
    by (simp add: x T) (rule has_type_combound, use Var.prems(2,3) in \<open>auto simp: nth_append\<close>)
next
  case (Bound i)
  then show ?case by (auto elim!: has_type_elims intro!: has_type.Bound simp: nth_append)
next
  case (Abs a T0 t)
  from Abs.prems(1) obtain U where T: "T = T0 \<rightarrow>\<^sub>T U" and t: "has_type W (T0 # Us) t U"
    by (auto elim: has_type_elims)
  have "length (T0 # Us) = nat_of_integer (lev + 1)" "0 \<le> lev + 1"
    using Abs.prems(2,3) by (simp_all add: integer_eq_iff integer_reps nat_add_distrib)
  from Abs.IH[OF t this(2,1)] Abs.prems(4) show ?case by (auto simp: T intro: has_type.Abs)
next
  case (App s t)
  from App.prems(1) obtain U where s: "has_type W Us s (U \<rightarrow>\<^sub>T T)" and t: "has_type W Us t U"
    by (auto elim: has_type_elims)
  from App.IH(1)[OF s App.prems(2,3)] App.IH(2)[OF t App.prems(2,3)] App.prems(4)
  show ?case by (auto intro: has_type.App)
qed (auto elim!: has_type_elims intro: has_type.intros)

lemma has_type_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> cok (lift_pre p G0) \<Longrightarrow> has_type W Ts (lift_pre p G0) propT \<Longrightarrow>
    has_type W (rev (ptys p) @ Ts) Y propT \<Longrightarrow> has_type W Ts (lift_pre p Y) propT"
proof (induction p arbitrary: Ts)
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    with cok_imp[of _ U H] Cons.prems(2) LImp have "U = imp_type" "cok H" "cok (lift_pre p G0)" by auto
    then have c: "c = implies" using c by (simp add: implies_imp_type)
    with Cons LImp show ?thesis by (simp add: has_type_implies)
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    with Cons.prems(2) LAll have "U = all_type T" "cok (lift_pre p G0)" by auto
    then have c: "c = all_const T" using c by (simp add: all_const_all_type)
    with Cons LAll show ?thesis by (simp add: has_type_all_const)
  qed
qed simp

lemma has_type_abs_pre_gen:
  "has_type W (rev (ptys p) @ Ts) X T \<Longrightarrow> has_type W Ts (abs_pre p X) (foldr fun_type (ptys p) T)"
proof (induction p arbitrary: Ts)
  case (Cons i p)
  then show ?case by (cases i) (auto intro: has_type.Abs)
qed simp

lemma tvars_incr_tvar: "tvars (incr_tvar inc T) = (\<lambda>(v, S). (incr_ix inc v, S)) ` tvars T"
  by (induction inc T rule: incr_tvar.induct) (auto simp: incr_ix_def image_UN)

lemma wft_incr_tvar[simp]: "wft ar (incr_tvar inc T) \<longleftrightarrow> wft ar T"
  by (induction inc T rule: incr_tvar.induct) auto

lemma tys_combound: "tys (combound t n k) = tys t"
  by (induction t n k rule: combound.induct) auto

lemma tys_incr_idx:
  "tys (incr_idx Ts inc lev X) \<subseteq> incr_tvar inc ` tys X \<union> (\<lambda>T. foldr fun_type Ts (incr_tvar inc T)) ` tys X"
  by (induction Ts inc lev X rule: incr_idx.induct) (auto simp: tys_combound)

lemma proper_incr_idx: "proper X \<Longrightarrow> 0 \<le> lev \<Longrightarrow> proper (incr_idx Ts inc lev X)"
  by (induction Ts inc lev X rule: incr_idx.induct) (auto simp: proper_combound)

lemma tvars_foldr_fun: "tvars (foldr fun_type Ts U) = (\<Union>T\<in>set Ts. tvars T) \<union> tvars U"
  by (induction Ts) auto

lemma wft_foldr_fun: "\<forall>T\<in>set Ts. wft ar T \<Longrightarrow> wft ar U \<Longrightarrow> wft ar (foldr fun_type Ts U)"
  by (induction Ts) (auto simp: tarity_def)

lemma tys_lift_pre: "tys (lift_pre p Y) \<subseteq> tys (lift_pre p G0) \<union> tys Y"
  by (induction p Y rule: lift_pre.induct) auto

lemma proper_lift_pre: "proper (lift_pre p G0) \<Longrightarrow> proper Y \<Longrightarrow> proper (lift_pre p Y)"
  by (induction p Y rule: lift_pre.induct) auto

lemma ptys_tys: "T \<in> set (ptys p) \<Longrightarrow> T \<in> tys (lift_pre p G0)"
  by (induction p rule: ptys.induct) auto

lemma tys_abs_pre: "tys (abs_pre p Y) = set (ptys p) \<union> tys Y"
  by (induction p Y rule: abs_pre.induct) auto

lemma proper_abs_pre[simp]: "proper (abs_pre p Y) \<longleftrightarrow> proper Y"
  by (induction p Y rule: abs_pre.induct) auto

lemma tr_abs_pre: "tr (abs_pre p Y) = Abs_m (nall p) (tr Y)"
  by (induction p Y rule: abs_pre.induct) auto

lemma wt_term_list_impliesI:
  assumes "\<forall>X\<in>set As. wt_term ar A W m X propT" "wt_term ar A W m B propT" "As \<noteq> [] \<Longrightarrow> wft ar imp_type"
  shows "wt_term ar A W m (list_implies As B) propT"
proof -
  have "has_type W [] (list_implies As B) propT"
    using assms(1,2) by (induction As) (auto simp: wt_term_def has_type_implies)
  then show ?thesis
    using assms by (auto simp: wt_term_def swf_tm_def twft_tys tys_list_implies no_loose_bound_list_implies
      below_def vars_list_implies tyA_def imp_type_def propT_def split: if_splits)
qed

text \<open>
  The lifted rule is well-typed: its incremented variables have the types of the variables of
  the rule, incremented and lifted over the types of the parameters of the subgoal, and its type
  variables are those of the subgoal and those of the rule, incremented.
\<close>

theorem lift_rule_wt_thm:
  assumes G: "wt_term ar A Ws smax G propT" "cok G" and ls: "lsplit G = (p, G0)"
    and rule: "wt_thm ar Ar Wr (th_maxidx rule) (th_tpairs rule) (th_prop rule)"
    and nn: "\<forall>x\<in>vars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd x"
    and m: "-1 \<le> th_maxidx rule"
  defines "W' \<equiv> \<lambda>x. if snd x \<le> smax then Ws x
      else foldr fun_type (ptys p) (incr_tvar (smax + 1) (Wr (fst x, snd x - (smax + 1))))"
    and "A' \<equiv> A \<union> (\<lambda>(v, S). (incr_ix (smax + 1) v, S)) ` Ar"
  shows "wt_thm ar A' W' (th_maxidx (lift_rule G smax rule)) (th_tpairs (lift_rule G smax rule))
    (th_prop (lift_rule G smax rule))"
proof -
  let ?inc = "smax + 1" and ?Ts = "ptys p" and ?m = "th_maxidx rule + (smax + 1)"
  let ?f = "incr_indexes (ptys p) (smax + 1)"
  let ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  from lsplit_ok[OF ls] have Gp: "G = lift_pre p G0" and ok: "\<forall>i\<in>set p. litem_ok i" by auto
  have hG: "has_type Ws [] G propT" "proper G" "no_loose_bound (tr G) 0" "below smax G"
    "\<forall>U\<in>tys G. tyA ar A U"
    using G(1) by (auto simp: wt_term_def swf_tm_def)
  have AA': "tyA ar A' U" if "tyA ar A U" for U using that by (auto simp: tyA_def A'_def)
  have "agreeV smax Ws W'" by (simp add: agreeV_def W'_def)
  from has_type_agreeV[OF hG(1,4) this] have hG': "has_type W' [] (lift_pre p G0) propT"
    by (simp add: Gp)
  have cG0: "cok (lift_pre p G0)" "proper (lift_pre p G0)" "no_loose_bound (tr (lift_pre p G0)) 0"
    "\<forall>U\<in>tys (lift_pre p G0). tyA ar A' U"
    using G(2) hG(2,3,5) AA' by (simp_all add: Gp)
  have pv: "\<forall>x\<in>pvars p. snd x \<le> smax" using hG(4) by (auto simp: Gp below_def vars_lift_pre)
  have Tsw: "\<forall>T\<in>set ?Ts. tyA ar A' T" using ptys_tys[of _ p G0] cG0(4) by auto
  text \<open>The incremented terms of the rule.\<close>
  have fX: "has_type W' (rev ?Ts) (?f X) (incr_tvar ?inc T) \<and> proper (?f X) \<and>
      no_loose_bound (tr (?f X)) (length ?Ts) \<and> below ?m (?f X) \<and> (\<forall>U\<in>tys (?f X). tyA ar A' U)"
    if X: "wt_term ar Ar Wr (th_maxidx rule) X T" "\<forall>x\<in>vars X. 0 \<le> snd x" for X T
  proof (intro conjI)
    have hX: "has_type Wr [] X T" "proper X" "no_loose_bound (tr X) 0" "below (th_maxidx rule) X"
      "\<forall>U\<in>tys X. tyA ar Ar U"
      using X(1) by (auto simp: wt_term_def swf_tm_def)
    have vW: "\<forall>x\<in>vars X. W' (incr_ix ?inc x) = foldr fun_type ?Ts (incr_tvar ?inc (Wr x))"
      using X(2) by (auto simp: W'_def incr_ix_def)
    have "has_type W' (map (incr_tvar ?inc) [] @ rev ?Ts) (incr_idx ?Ts ?inc 0 X) (incr_tvar ?inc T)"
      by (rule has_type_incr_idx[OF hX(1)]) (use vW in simp_all)
    then show "has_type W' (rev ?Ts) (?f X) (incr_tvar ?inc T)" by (simp add: incr_indexes_idx)
    show "proper (?f X)" using proper_incr_idx[OF hX(2)] by (simp add: incr_indexes_idx)
    show "no_loose_bound (tr (?f X)) (length ?Ts)"
      using no_loose_bound_incr_idx[of X 0 ?Ts ?inc] hX(3) by (simp add: incr_indexes_idx)
    show "below ?m (?f X)" using hX(4) by (auto simp: below_def incr_indexes_idx vars_incr_idx)
    show "\<forall>U\<in>tys (?f X). tyA ar A' U"
    proof
      fix U assume U: "U \<in> tys (?f X)"
      then obtain U0 where U0: "U0 \<in> tys X"
        and "U = incr_tvar ?inc U0 \<or> U = foldr fun_type ?Ts (incr_tvar ?inc U0)"
        using tys_incr_idx[of ?Ts ?inc 0 X] by (auto simp: incr_indexes_idx)
      moreover have i: "tvars (incr_tvar ?inc U0) \<subseteq> A'" "wft ar (incr_tvar ?inc U0)"
      proof -
        have "tvars U0 \<subseteq> Ar" "wft ar U0" using hX(5) U0 by (auto simp: tyA_def)
        then show "tvars (incr_tvar ?inc U0) \<subseteq> A'" "wft ar (incr_tvar ?inc U0)"
          unfolding A'_def tvars_incr_tvar by (blast, simp)
      qed
      moreover have "tvars (foldr fun_type ?Ts (incr_tvar ?inc U0)) \<subseteq> A'"
        using Tsw i(1) unfolding tvars_foldr_fun tyA_def by blast
      moreover have "wft ar (foldr fun_type ?Ts (incr_tvar ?inc U0))"
        by (rule wft_foldr_fun) (use Tsw i(2) in \<open>auto simp: tyA_def\<close>)
      ultimately show "tyA ar A' U" unfolding tyA_def by blast
    qed
  qed
  have rp: "th_prop rule = list_implies ?As ?B"
    by (rule list_implies_strip_imp) (use rule in \<open>simp add: wt_thm_def\<close>)
  have wP: "wt_term ar Ar Wr (th_maxidx rule) (list_implies ?As ?B) propT"
    using rule by (simp only: rp[symmetric]) (simp add: wt_thm_def)
  have cP: "cok (list_implies ?As ?B)"
    using rule by (simp only: rp[symmetric]) (simp add: wt_thm_def)
  have wAB: "wt_term ar Ar Wr (th_maxidx rule) X propT" if "X \<in> insert ?B (set ?As)" for X
    using wt_term_list_implies[OF wP] that by auto
  have nnAB: "\<forall>x\<in>vars X. 0 \<le> snd x" if "X \<in> insert ?B (set ?As)" for X
  proof -
    have "vars X \<subseteq> vars (th_prop rule)"
      using that vars_strip_imp(2)[of "th_prop rule"] vars_strip_imp(1)[of _ "th_prop rule"] by auto
    with nn show ?thesis by (auto simp: vars_thm_def)
  qed
  have lX: "wt_term ar A' W' ?m (lift_pre p (?f X)) propT" if "X \<in> insert ?B (set ?As)" for X
  proof -
    note f = fX[OF wAB[OF that] nnAB[OF that]]
    have "has_type W' [] (lift_pre p (?f X)) propT"
      using has_type_lift_pre[OF ok cG0(1) hG', of "?f X"] f by (simp add: propT_def)
    moreover have "proper (lift_pre p (?f X))" using proper_lift_pre[OF cG0(2)] f by simp
    moreover have "no_loose_bound (tr (lift_pre p (?f X))) 0"
      using no_loose_bound_lift_pre[OF ok cG0(3), of "?f X"] f by (simp add: nall_ptys)
    moreover have tyl: "\<forall>U\<in>tys (lift_pre p (?f X)). tyA ar A' U"
      using tys_lift_pre[of p "?f X" G0] cG0(4) f by blast
    moreover have "below ?m (lift_pre p (?f X))"
      using f pv m by (auto simp: below_def vars_lift_pre)
    ultimately show ?thesis by (auto simp: wt_term_def swf_tm_def twft_tys tyA_def)
  qed
  have la: "lift_all ?inc G = (\<lambda>t. lift_pre p (?f t))" by (rule ext) (rule lift_all_lsplit[OF ls])
  have P: "th_prop (lift_rule G smax rule) = list_implies (map (\<lambda>X. lift_pre p (?f X)) ?As) (lift_pre p (?f ?B))"
    by (simp add: lift_rule_def Let_def la)
  have M: "th_maxidx (lift_rule G smax rule) = ?m" by (simp add: lift_rule_def Let_def)
  have imp: "wft ar imp_type" if "?As \<noteq> []"
  proof -
    have "imp_type \<in> tys (list_implies ?As ?B)" using that by (simp add: tys_list_implies)
    with wP show ?thesis by (auto simp: wt_term_def tyA_def)
  qed
  have wt: "wt_term ar A' W' ?m (th_prop (lift_rule G smax rule)) propT"
    unfolding P by (rule wt_term_list_impliesI) (use lX imp in auto)
  have "cok (lift_pre p (?f X))" if "X \<in> insert ?B (set ?As)" for X
  proof (rule cok_lift_pre[OF ok cG0(1)])
    have "cok X" using cP that by (auto simp: cok_list_implies)
    then show "cok (?f X)" by (simp add: incr_indexes_idx cok_incr_idx)
  qed
  then have ck: "cok (th_prop (lift_rule G smax rule))" unfolding P by (auto simp: cok_list_implies)
  have tp: "\<exists>T. wt_term ar A' W' ?m t T \<and> wt_term ar A' W' ?m u T"
    if tu: "(t, u) \<in> set (th_tpairs (lift_rule G smax rule))" for t u
  proof -
    obtain t0 u0 where tu0: "(t0, u0) \<in> set (th_tpairs rule)" and t: "t = abs_pre p (?f t0)"
      and u: "u = abs_pre p (?f u0)"
      using tu by (auto simp: lift_rule_def Let_def lift_abs_lsplit[OF ls])
    from rule tu0 obtain T where wt: "wt_term ar Ar Wr (th_maxidx rule) t0 T"
      "wt_term ar Ar Wr (th_maxidx rule) u0 T"
      by (auto simp: wt_thm_def)
    have nnt: "\<forall>x\<in>vars t0. 0 \<le> snd x" "\<forall>x\<in>vars u0. 0 \<le> snd x" using nn tu0 by (auto simp: vars_thm_def)
    have wa: "wt_term ar A' W' ?m (abs_pre p (?f X)) (foldr fun_type ?Ts (incr_tvar ?inc T))"
      if "wt_term ar Ar Wr (th_maxidx rule) X T" "\<forall>x\<in>vars X. 0 \<le> snd x" for X
    proof -
      note f = fX[OF that]
      have "has_type W' [] (abs_pre p (?f X)) (foldr fun_type ?Ts (incr_tvar ?inc T))"
        using has_type_abs_pre_gen[of W' p "[]" "?f X"] f by simp
      with f Tsw show ?thesis
        by (auto simp: wt_term_def swf_tm_def tr_abs_pre nall_ptys twft_tys tys_abs_pre below_def
          vars_abs_pre tyA_def)
    qed
    from wa[OF wt(1) nnt(1)] wa[OF wt(2) nnt(2)] t u show ?thesis by blast
  qed
  show ?thesis unfolding wt_thm_def M using wt ck tp by blast
qed


subsection \<open>The subgoal of biresolution\<close>

lemma okT_handleT_raises: "okT (handleT m h) y \<Longrightarrow> (\<And>e. \<not> okT (h e) y) \<Longrightarrow> okT m y"
  by (auto simp: okT_handleT)

lemma okT_of_snd: "m = Some r \<Longrightarrow> snd r = TOk x \<Longrightarrow> okT m x"
  by (cases r) auto

lemma okT_dest_state:
  assumes "okT (dest_state state i) (stpairs, Bs, Bi, C)"
  shows "stpairs = th_tpairs state" "ok (strip_prems i [] (th_prop state)) (Bi # rev Bs, C)"
proof -
  have "okT (do {
      (rBs, C) \<leftarrow> liftMT (strip_prems i [] (th_prop state));
      (case rBs of
        B # rBs' \<Rightarrow> returnT (th_tpairs state, rev rBs', B, C)
      | [] \<Rightarrow> raiseT (THM (STR ''dest_state'') i State))}) (stpairs, Bs, Bi, C)"
    by (rule okT_handleT_raises[OF assms[unfolded dest_state_def]])
      (auto simp: raiseT_def split: texn.splits uexn.splits exn.splits)
  then show "stpairs = th_tpairs state" "ok (strip_prems i [] (th_prop state)) (Bi # rev Bs, C)"
    by (auto simp: neq_Nil_conv split: list.splits)
qed

lemma nth_prem_strip_prems:
  assumes "ok (strip_prems i As P) (rAs, C)" "length As < length rAs"
  shows "ok (nth_prem i P) (hd rAs)"
  using assms
proof (induction i As P rule: strip_prems.induct)
  case (1 i As P)
  show ?case
  proof (cases "i = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_prems.simps) simp
  next
    case False
    with "1.prems"(1) obtain A B where AB: "dest_imp P = Some (A, B)"
      and r: "ok (strip_prems (i - 1) (A # As) B) (rAs, C)"
      by (subst (asm) strip_prems.simps) (auto split: option.splits)
    show ?thesis
    proof (cases "i = 1")
      case True
      with r have "rAs = A # As" by (subst (asm) strip_prems.simps) simp
      with AB True show ?thesis by (subst nth_prem.simps) simp
    next
      case i1: False
      from Bicompose_Syntax.strip_prems_ok[OF r] have "0 \<le> i - 1" by blast
      with strip_prems_length[OF r] False i1 have "length (A # As) < length rAs"
        by (simp add: integer_reps)
      from "1.IH"[OF False AB refl r this] AB i1 show ?thesis by (subst nth_prem.simps) simp
    qed
  qed
qed

lemma okT_cprem_of: "okT (cprem_of th i) goal \<Longrightarrow> ok (nth_prem i (th_prop th)) goal"
  unfolding cprem_of_def
  by (drule okT_handleT_raises) (auto simp: raiseT_def split: texn.splits uexn.splits exn.splits)

text \<open>The subgoal of a proof state, and the proof state as composed with the rules.\<close>

lemma dest_state_cprem_of:
  assumes "okT (dest_state state i) (stpairs, Bs, Bi, C)" "okT (cprem_of state i) goal"
    "cok (th_prop state)"
  shows "goal = Bi" "stpairs = th_tpairs state" "th_prop state = list_implies (Bs @ [Bi]) C"
proof -
  note d = okT_dest_state[OF assms(1)]
  from nth_prem_strip_prems[OF d(2)] okT_cprem_of[OF assms(2)] show "goal = Bi" by simp
  show "stpairs = th_tpairs state" by (rule d(1))
  from list_implies_strip_prems[OF d(2) assms(3)] show "th_prop state = list_implies (Bs @ [Bi]) C"
    by simp
qed

lemma okT_biresolution:
  assumes "okT (biresolution trace match_flg rep brules i state) s0"
  obtains stpairs Bs Bi C goal where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal"
    "s0 = res rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi)) brules"
  using assms by (auto simp: biresolution_def)


subsection \<open>The result sequence\<close>

text \<open>The sequences of results of a call of \<^const>\<open>bicompose_aux\<close> reached by pulling.\<close>

inductive breach :: "'u bops \<Rightarrow> 'u bseq \<Rightarrow> 'u bseq \<Rightarrow> bool" for ops where
  Refl: "breach ops s s"
| Step: "breach ops s0 s \<Longrightarrow> okT (bpull ops s) (Some (r, s')) \<Longrightarrow> breach ops s0 s'"

lemma breach_bresult: "breach ops s0 s \<Longrightarrow> bresult ops s r \<Longrightarrow> bresult ops s0 r"
  by (induction rule: breach.induct) (auto intro: bresult.Next)

text \<open>
  The invariant of the result sequence of \<^const>\<open>biresolution\<close> for the call context \<open>ctx\<close> and
  the rules \<open>brules0\<close>: the closures are those of rules of \<open>brules0\<close>, and the sequences of results
  are reached from the results of the composition of a rule with the proof state.
\<close>

inductive rinv :: "'u bops \<Rightarrow> algebra \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> brctx \<Rightarrow> (bool \<times> 'r) list \<Rightarrow>
    ('u, 'r) rseq \<Rightarrow> bool" for ops alg rep ctx brules0 where
  Empty: "rinv ops alg rep ctx brules0 RQ_Empty"
| Make: "set (r # brules) \<subseteq> set brules0 \<Longrightarrow> rinv ops alg rep ctx brules0 (RQ_Make ctx r brules)"
| App: "r \<in> set brules0 \<Longrightarrow> okT (compose ops alg ctx (fst r) (rep (snd r))) xq0 \<Longrightarrow> breach ops xq0 xq \<Longrightarrow>
    rinv ops alg rep ctx brules0 xqq \<Longrightarrow> rinv ops alg rep ctx brules0 (RQ_App r xq xqq)"

lemma res_rinv: "set brules \<subseteq> set brules0 \<Longrightarrow> rinv ops alg rep ctx brules0 (res rep ctx brules)"
  by (induction rep ctx brules rule: res.induct) (simp_all add: rinv.Empty rinv.Make)

definition rchar_br :: "'u bops \<Rightarrow> algebra \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> brctx \<Rightarrow> (bool \<times> 'r) list \<Rightarrow>
    bres \<times> (bool \<times> 'r) \<Rightarrow> bool" where
  "rchar_br ops alg rep ctx brules0 xr \<longleftrightarrow> (case xr of (x, r) \<Rightarrow> r \<in> set brules0 \<and>
    (\<exists>xq0. okT (compose ops alg ctx (fst r) (rep (snd r))) xq0 \<and> bresult ops xq0 x))"

lemma brstep_rinv:
  assumes "rinv ops alg rep ctx brules0 s" "okT (brstep ops alg rep s) st"
  shows "case st of
      RS_Done \<Rightarrow> True
    | RS_Skip s' \<Rightarrow> rinv ops alg rep ctx brules0 s'
    | RS_Result xr s' \<Rightarrow> rinv ops alg rep ctx brules0 s' \<and> rchar_br ops alg rep ctx brules0 xr"
  using assms(1)
proof cases
  case Empty
  with assms(2) show ?thesis by simp
next
  case (Make r brules)
  obtain e rule where r: "r = (e, rule)" by (cases r)
  from assms(2) Make r obtain xq where xq: "okT (compose ops alg ctx e (rep rule)) xq"
    and st: "st = RS_Skip (RQ_App (e, rule) xq (res rep ctx brules))"
    by auto
  have "rinv ops alg rep ctx brules0 (RQ_App (e, rule) xq (res rep ctx brules))"
    by (rule rinv.App[OF _ _ breach.Refl res_rinv]) (use Make r xq in auto)
  with st show ?thesis by simp
next
  case (App r xq0 xq xqq)
  from assms(2) App obtain x where p: "okT (bpull ops xq) x"
    and st: "okT (case x of None \<Rightarrow> returnT (RS_Skip xqq)
      | Some (th, xq') \<Rightarrow> returnT (RS_Result (th, r) (RQ_App r xq' xqq))) st"
    by auto
  show ?thesis
  proof (cases x)
    case None
    with st App show ?thesis by simp
  next
    case (Some y)
    then obtain th xq' where y: "x = Some (th, xq')" by (cases y) auto
    with st have st': "st = RS_Result (th, r) (RQ_App r xq' xqq)" by simp
    have "rinv ops alg rep ctx brules0 (RQ_App r xq' xqq)"
      by (rule rinv.App[OF App(2,3) breach.Step[OF App(4)] App(5)]) (use p y in simp)
    moreover have "bresult ops xq0 th"
      by (rule breach_bresult[OF App(4) bresult.First]) (use p y in simp)
    ultimately show ?thesis using st' App(2,3) by (auto simp: rchar_br_def)
  qed
qed

lemma brpull_rinv:
  "brpull ops alg rep s = Some r0 \<Longrightarrow> snd r0 = TOk (Some (xr, s')) \<Longrightarrow> rinv ops alg rep ctx brules0 s \<Longrightarrow>
    rchar_br ops alg rep ctx brules0 xr \<and> rinv ops alg rep ctx brules0 s'"
proof (induction ops alg rep s r0 arbitrary: xr s' rule: brpull.raw_induct[rotated, consumes 1])
  case (1 P ops alg rep s r0)
  note hyps = okT_of_snd[OF "1.hyps" "1.prems"(1)]
  from hyps obtain st where st: "okT (brstep ops alg rep s) st"
    and cont: "okT (case st of
        RS_Done \<Rightarrow> returnT None
      | RS_Skip s' \<Rightarrow> P ops alg rep s'
      | RS_Result x s' \<Rightarrow> returnT (Some (x, s'))) (Some (xr, s'))"
    by auto
  note inv = brstep_rinv[OF "1.prems"(2) st]
  show ?case
  proof (cases st)
    case RS_Done
    with cont show ?thesis by simp
  next
    case (RS_Skip s1)
    with cont obtain evs where "P ops alg rep s1 = Some (evs, TOk (Some (xr, s')))" by auto
    from "1.IH"[OF this _] inv RS_Skip show ?thesis by simp
  next
    case (RS_Result x s1)
    with cont inv show ?thesis by simp
  qed
qed

text \<open>The results of the sequence of \<^const>\<open>biresolution\<close>, as for \<^const>\<open>bicompose_aux\<close>.\<close>

inductive brresult :: "'u bops \<Rightarrow> algebra \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> ('u, 'r) rseq \<Rightarrow> bres \<times> (bool \<times> 'r) \<Rightarrow> bool"
  for ops alg rep where
  First: "okT (brpull ops alg rep s) (Some (xr, s')) \<Longrightarrow> brresult ops alg rep s xr"
| Next: "okT (brpull ops alg rep s) (Some (xr', s')) \<Longrightarrow> brresult ops alg rep s' xr \<Longrightarrow> brresult ops alg rep s xr"

lemma brresult_rchar:
  assumes "brresult ops alg rep s xr" "rinv ops alg rep ctx brules0 s"
  shows "rchar_br ops alg rep ctx brules0 xr"
  using assms
proof (induction rule: brresult.induct)
  case (First s xr s')
  then obtain evs where "brpull ops alg rep s = Some (evs, TOk (Some (xr, s')))" by blast
  from brpull_rinv[OF this _ First.prems] show ?case by simp
next
  case (Next s xr' s' xr)
  then obtain evs where "brpull ops alg rep s = Some (evs, TOk (Some (xr', s')))" by blast
  from brpull_rinv[OF this _ Next.prems] Next.IH show ?case by simp
qed

text \<open>
  A result of \<^const>\<open>biresolution\<close> is a result of the composition of one of the rules, lifted
  over the subgoal, with the proof state.
\<close>

lemma biresolution_result:
  assumes "okT (biresolution trace match_flg rep brules i state) s0"
    and "brresult ops alg rep s0 (x, (eres_flg, rule))"
  obtains stpairs Bs Bi C goal where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal" "(eres_flg, rule) \<in> set brules"
    "\<exists>xq0. okT (bicompose_aux ops alg True match_flg True (pthm_of state) (stpairs, Bs, Bi, C) True
      eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule))) (nprems_of (rep rule))) xq0 \<and>
      bresult ops xq0 x"
proof -
  from assms(1) obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal"
    and s0: "s0 = res rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi)) brules"
    by (rule okT_biresolution)
  let ?ctx = "BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi)"
  have "rinv ops alg rep ?ctx brules s0" unfolding s0 by (rule res_rinv) simp
  from brresult_rchar[OF assms(2) this] show thesis
    by (intro that[OF d g]) (auto simp: rchar_br_def compose_def)
qed


subsection \<open>Well-typed theorems\<close>

text \<open>
  The typing of a theorem: its type variables are among a finite, sort-consistent set \<open>A\<close> of
  type variables with indices between \<open>lo\<close> and its maximal index, and its variables are typed
  by a typing \<open>W\<close> with types over \<open>A\<close>; the indices of its variables are at least \<open>lo\<close>. Rules
  are lifted only if \<open>lo = 0\<close>: the certified terms of Pure have no negative indices.
\<close>

definition thm_typed :: "(name \<Rightarrow> nat) \<Rightarrow> integer \<Rightarrow> thm_rep \<Rightarrow> bool" where
  "thm_typed ar lo th \<longleftrightarrow> -1 \<le> th_maxidx th \<and> (\<forall>x\<in>vars_thm (th_tpairs th) (th_prop th). lo \<le> snd x) \<and>
    (\<exists>A W. finite A \<and> scons A \<and> (\<forall>p\<in>A. lo \<le> snd (fst p) \<and> snd (fst p) \<le> th_maxidx th) \<and>
      (\<forall>x. tyA ar A (W x)) \<and> wt_thm ar A W (th_maxidx th) (th_tpairs th) (th_prop th))"

lemma tyA_mono: "tyA ar A T \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> tyA ar A' T"
  by (auto simp: tyA_def)

lemma wt_term_mono_A: "wt_term ar A W m t T \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> wt_term ar A' W m t T"
  by (auto simp: wt_term_def intro: tyA_mono)

lemma wt_thm_mono_A: "wt_thm ar A W m tps P \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> wt_thm ar A' W m tps P"
  unfolding wt_thm_def using wt_term_mono_A by blast

lemma wt_term_ibelow: "wt_term ar A W m t T \<Longrightarrow> \<forall>p\<in>A. snd (fst p) \<le> m \<Longrightarrow> ibelow m t"
  by (fastforce simp: wt_term_def ibelow_def tyA_def below_def)

lemma wt_thm_below: "wt_thm ar A W m tps P \<Longrightarrow> x \<in> vars_thm tps P \<Longrightarrow> snd x \<le> m"
  by (fastforce simp: wt_thm_def wt_term_def below_def vars_thm_def)

lemma wt_thm_closed:
  assumes "wt_thm ar A W m tps P"
  shows "cok P" "no_loose_bound (tr P) 0"
    "\<forall>(t, u)\<in>set tps. no_loose_bound (tr t) 0 \<and> no_loose_bound (tr u) 0"
  using assms by (fastforce simp: wt_thm_def wt_term_def swf_tm_def)+

lemma tyA_incr_tvar: "tyA ar A T \<Longrightarrow> tyA ar ((\<lambda>(v, S). (incr_ix inc v, S)) ` A) (incr_tvar inc T)"
  unfolding tyA_def tvars_incr_tvar wft_incr_tvar using image_mono by blast

lemma wt_thm_vars_cong:
  assumes "wt_thm ar A W m tps P" "\<forall>x\<in>vars_thm tps P. W' x = W x"
  shows "wt_thm ar A W' m tps P"
proof -
  have c: "wt_term ar A W' m t T" if "wt_term ar A W m t T" "vars t \<subseteq> vars_thm tps P" for t T
    using that assms(2) has_type_vars[of W "[]" t T W'] by (auto simp: wt_term_def)
  from assms(1) have P: "wt_term ar A W m P propT" "cok P"
    and tps: "\<forall>(t, u)\<in>set tps. \<exists>T. wt_term ar A W m t T \<and> wt_term ar A W m u T"
    by (simp_all add: wt_thm_def)
  have "wt_term ar A W' m P propT" by (rule c[OF P(1)]) (auto simp: vars_thm_def)
  moreover have "\<forall>(t, u)\<in>set tps. \<exists>T. wt_term ar A W' m t T \<and> wt_term ar A W' m u T"
  proof (intro ballI, clarify)
    fix t u assume tu: "(t, u) \<in> set tps"
    with tps obtain T where "wt_term ar A W m t T" "wt_term ar A W m u T" by blast
    moreover have "vars t \<subseteq> vars_thm tps P" "vars u \<subseteq> vars_thm tps P"
      using tu by (auto simp: vars_thm_def)
    ultimately show "\<exists>T. wt_term ar A W' m t T \<and> wt_term ar A W' m u T" using c by blast
  qed
  ultimately show ?thesis using P(2) by (simp add: wt_thm_def)
qed

lemma tyA_foldr_fun: "\<forall>T\<in>set Ts. tyA ar A T \<Longrightarrow> tyA ar A U \<Longrightarrow> tyA ar A (foldr fun_type Ts U)"
  by (auto simp: tyA_def tvars_foldr_fun intro!: wft_foldr_fun)

text \<open>
  The proof state and the lifted rule as composed by \<^const>\<open>biresolution\<close>: they are typed by a
  common typing.
\<close>

lemma compose_typed:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of state i) goal"
    and st: "thm_typed ar lo state" and ru: "thm_typed ar 0 rule"
  defines "lr \<equiv> lift_rule goal (th_maxidx state) rule"
  obtains A W where "finite A" "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max (th_maxidx lr) (th_maxidx state)"
    "\<forall>x. tyA ar A (W x)"
    "wt_thm ar A W (th_maxidx state) stpairs (list_implies (Bs @ [Bi]) C)"
    "ibelow (th_maxidx state) (list_implies (Bs @ [Bi]) C)"
    "wt_thm ar A W (th_maxidx lr) (th_tpairs lr) (th_prop lr)"
    "lifted_over (th_maxidx state) Bi (th_prop lr) (nprems_of rule)"
    "th_tpairs state = stpairs" "th_prop state = list_implies (Bs @ [Bi]) C" "goal = Bi"
    "-1 \<le> th_maxidx lr"
    "lo \<le> 0 \<Longrightarrow> \<forall>p\<in>A. lo \<le> snd (fst p)"
    "lo \<le> 0 \<Longrightarrow> \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm (th_tpairs lr) (th_prop lr).
      lo \<le> snd x"
proof -
  let ?smax = "th_maxidx state" and ?inc = "th_maxidx state + 1"
  from st obtain As Ws where As: "finite As" "scons As" "\<forall>p\<in>As. snd (fst p) \<le> ?smax"
    "\<forall>x. tyA ar As (Ws x)" and wS: "wt_thm ar As Ws ?smax (th_tpairs state) (th_prop state)"
    and sm: "-1 \<le> ?smax" and Aslo: "\<forall>p\<in>As. lo \<le> snd (fst p)"
    and Slo: "\<forall>x\<in>vars_thm (th_tpairs state) (th_prop state). lo \<le> snd x"
    by (auto simp: thm_typed_def)
  from ru obtain Ar Wr where Ar: "finite Ar" "scons Ar" "\<forall>p\<in>Ar. 0 \<le> snd (fst p) \<and> snd (fst p) \<le> th_maxidx rule"
    "\<forall>x. tyA ar Ar (Wr x)" and wR: "wt_thm ar Ar Wr (th_maxidx rule) (th_tpairs rule) (th_prop rule)"
    and nn: "\<forall>x\<in>vars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd x" and rm: "-1 \<le> th_maxidx rule"
    by (auto simp: thm_typed_def)
  have cS: "cok (th_prop state)" using wS by (simp add: wt_thm_def)
  note ds = dest_state_cprem_of[OF d g cS]
  have wSt: "wt_thm ar As Ws ?smax stpairs (list_implies (Bs @ [Bi]) C)" using wS ds(2,3) by simp
  have wP: "wt_term ar As Ws ?smax (list_implies (Bs @ [Bi]) C) propT" "cok (list_implies (Bs @ [Bi]) C)"
    using wSt by (simp_all add: wt_thm_def)
  have wBi: "wt_term ar As Ws ?smax Bi propT" using wt_term_list_implies(1)[OF wP(1)] by simp
  have cBi: "cok Bi" using wP(2) by (simp add: cok_list_implies)
  obtain p G0 where ls: "lsplit Bi = (p, G0)" by (cases "lsplit Bi")
  define W where "W \<equiv> \<lambda>x. if snd x \<le> ?smax then Ws x
      else foldr fun_type (ptys p) (incr_tvar ?inc (Wr (fst x, snd x - ?inc)))"
  define A where "A \<equiv> As \<union> (\<lambda>(v, S). (incr_ix ?inc v, S)) ` Ar"
  have lr: "lr = lift_rule Bi ?smax rule" by (simp add: lr_def ds(1))
  show thesis
  proof (rule that[of A W])
    show "finite A" using As(1) Ar(1) by (simp add: A_def)
    show "scons A"
      using As(2,3) Ar(2,3) unfolding scons_def A_def by (fastforce simp: incr_ix_def)
    show "\<forall>p\<in>A. snd (fst p) \<le> max (th_maxidx lr) ?smax"
      using As(3) Ar(3) by (auto simp: A_def incr_ix_def lr lift_rule_def Let_def)
    have AsA: "As \<subseteq> A" by (simp add: A_def)
    show "\<forall>x. tyA ar A (W x)"
    proof
      fix x
      have Ts: "\<forall>T\<in>set (ptys p). tyA ar A T"
        using ptys_tys[of _ p G0] wBi lsplit_ok[OF ls] AsA by (auto simp: wt_term_def intro: tyA_mono)
      have inc: "tyA ar A (incr_tvar ?inc U)" if "tyA ar Ar U" for U
        using tyA_incr_tvar[OF that, of ?inc] by (rule tyA_mono) (auto simp: A_def)
      show "tyA ar A (W x)"
      proof (cases "snd x \<le> ?smax")
        case True
        then show ?thesis using tyA_mono[OF As(4)[rule_format] AsA] by (simp add: W_def)
      next
        case False
        then show ?thesis using tyA_foldr_fun[OF Ts inc[OF Ar(4)[rule_format]]] by (simp add: W_def)
      qed
    qed
    have "wt_thm ar A Ws ?smax stpairs (list_implies (Bs @ [Bi]) C)"
      by (rule wt_thm_mono_A[OF wSt]) (simp add: A_def)
    then show "wt_thm ar A W ?smax stpairs (list_implies (Bs @ [Bi]) C)"
      by (rule wt_thm_vars_cong) (auto simp: W_def dest: wt_thm_below[OF wSt])
    show "ibelow ?smax (list_implies (Bs @ [Bi]) C)" by (rule wt_term_ibelow[OF wP(1) As(3)])
    show "wt_thm ar A W (th_maxidx lr) (th_tpairs lr) (th_prop lr)"
      unfolding lr W_def A_def by (rule lift_rule_wt_thm[OF wBi cBi ls wR nn rm])
    show "lifted_over ?smax Bi (th_prop lr) (nprems_of rule)"
      unfolding lr by (rule lift_rule_lifted_over) (use nn in \<open>simp add: vars_thm_def\<close>)
    show "th_tpairs state = stpairs" "th_prop state = list_implies (Bs @ [Bi]) C" using ds(2,3) by simp_all
    show "goal = Bi" by (rule ds(1))
    show "-1 \<le> th_maxidx lr" using rm sm by (simp add: lr lift_rule_def Let_def)
    text \<open>The variables of the lifted rule are those of the subgoal and the incremented ones.\<close>
    assume lo0: "lo \<le> 0"
    have inc: "lo \<le> i + ?inc" if "0 \<le> i" for i using that lo0 sm by transfer linarith
    show "\<forall>p\<in>A. lo \<le> snd (fst p)"
      using Aslo Ar(3) inc by (auto simp: A_def incr_ix_def)
    have la: "vars (lift_all ?inc Bi t) \<subseteq> pvars p \<union> (\<lambda>(x, i). (x, i + ?inc)) ` vars t" for t
      by (simp add: lift_all_lsplit[OF ls] vars_lift_pre vars_incr_indexes)
    have lb: "vars (lift_abs ?inc Bi t) = (\<lambda>(x, i). (x, i + ?inc)) ` vars t" for t
      by (simp add: lift_abs_lsplit[OF ls] vars_abs_pre vars_incr_indexes)
    have pB: "pvars p \<subseteq> vars_thm (th_tpairs state) (th_prop state)"
      using lsplit_ok[OF ls] ds(3) by (auto simp: vars_thm_def vars_list_implies vars_lift_pre)
    let ?f = "\<lambda>(x, i). (x, i + ?inc)" and ?VR = "vars_thm (th_tpairs rule) (th_prop rule)"
    have key: "lo \<le> snd x" if "x \<in> pvars p \<union> ?f ` ?VR" for x
      using that pB Slo nn inc by auto
    have P: "vars (th_prop lr) \<subseteq> pvars p \<union> ?f ` ?VR"
    proof -
      have "vars X \<subseteq> ?VR" if "X \<in> insert (strip_imp_concl (th_prop rule)) (set (strip_imp_prems (th_prop rule)))" for X
        using that vars_strip_imp(1)[of _ "th_prop rule"] vars_strip_imp(2)[of "th_prop rule"]
        by (auto simp: vars_thm_def)
      then have "vars (lift_all ?inc Bi X) \<subseteq> pvars p \<union> ?f ` ?VR"
        if "X \<in> insert (strip_imp_concl (th_prop rule)) (set (strip_imp_prems (th_prop rule)))" for X
        using la[of X] that by blast
      then show ?thesis by (auto simp: lr lift_rule_def Let_def vars_list_implies)
    qed
    have T: "vars t \<union> vars u \<subseteq> ?f ` ?VR" if "(t, u) \<in> set (th_tpairs lr)" for t u
    proof -
      from that obtain a b where ab: "(a, b) \<in> set (th_tpairs rule)" "t = lift_abs ?inc Bi a"
        "u = lift_abs ?inc Bi b"
        by (auto simp: lr lift_rule_def Let_def)
      then have "vars a \<union> vars b \<subseteq> ?VR" by (auto simp: vars_thm_def)
      then show ?thesis unfolding ab(2,3) lb image_Un[symmetric] by (rule image_mono)
    qed
    show "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm (th_tpairs lr) (th_prop lr).
        lo \<le> snd x"
    proof
      fix x assume "x \<in> vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm (th_tpairs lr) (th_prop lr)"
      then consider "x \<in> vars_thm stpairs (list_implies (Bs @ [Bi]) C)" | "x \<in> vars (th_prop lr)"
        | t u where "(t, u) \<in> set (th_tpairs lr)" "x \<in> vars t \<union> vars u"
        unfolding vars_thm_def[of "th_tpairs lr"] by blast
      then show "lo \<le> snd x"
      proof cases
        case 1
        with Slo ds(2,3) show ?thesis by simp
      next
        case 2
        with P key show ?thesis by blast
      next
        case 3
        with T key show ?thesis by blast
      qed
    qed
  qed
qed


subsection \<open>Soundness\<close>

context bicompose_sem
begin

text \<open>
  The results of \<^const>\<open>biresolution\<close> of a valid, well-typed proof state with valid,
  well-typed rules are valid.
\<close>

theorem biresolution_valid:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) alg rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "valid (th_tpairs state) (th_prop state)" "thm_typed ar lo state"
    and rules: "(eres_flg, rule) \<in> set brules \<Longrightarrow> valid (th_tpairs (rep rule)) (th_prop (rep rule)) \<and> thm_typed ar 0 (rep rule)"
  shows "valid (br_tpairs x) (br_prop x)"
proof -
  from br res obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal" and r: "(eres_flg, rule) \<in> set brules"
    and xq: "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state)
      (stpairs, Bs, Bi, C) True eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule)))
      (nprems_of (rep rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result)
  from rules[OF r] have vr: "valid (th_tpairs (rep rule)) (th_prop (rep rule))"
    and tr: "thm_typed ar 0 (rep rule)" by auto
  let ?lr = "lift_rule goal (th_maxidx state) (rep rule)"
  obtain A W where A: "finite A" "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max (th_maxidx ?lr) (th_maxidx state)"
    "\<forall>x. tyA ar A (W x)"
    and wS: "wt_thm ar A W (th_maxidx state) stpairs (list_implies (Bs @ [Bi]) C)"
    and iS: "ibelow (th_maxidx state) (list_implies (Bs @ [Bi]) C)"
    and wR: "wt_thm ar A W (th_maxidx ?lr) (th_tpairs ?lr) (th_prop ?lr)"
    and lov: "lifted_over (th_maxidx state) Bi (th_prop ?lr) (nprems_of (rep rule))"
    and tS: "th_tpairs state = stpairs" and pS: "th_prop state = list_implies (Bs @ [Bi]) C"
    and gB: "goal = Bi" and "-1 \<le> th_maxidx ?lr"
    by (rule compose_typed[OF d g state(2) tr])
  from tr obtain Ar Wr where "wt_thm ar Ar Wr (th_maxidx (rep rule)) (th_tpairs (rep rule)) (th_prop (rep rule))"
    by (auto simp: thm_typed_def)
  note rc = wt_thm_closed[OF this]
  obtain p G0 where ls: "lsplit goal = (p, G0)" by (cases "lsplit goal")
  have wG: "cok goal" "no_loose_bound (tr goal) 0"
    using wt_thm_closed(1,2)[OF wS] gB by (simp_all add: cok_list_implies no_loose_bound_list_implies)
  have vl': "valid (th_tpairs ?lr) (th_prop ?lr)"
    by (rule lift_rule_valid[OF vr ls wG rc])
  have vS: "valid stpairs (list_implies (Bs @ [Bi]) C)" using state(1) tS pS by simp
  from xq obtain xq0 where ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (th_maxidx state, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of (rep rule))) xq0"
    and rx: "bresult (unify_ops cfg vl) xq0 x"
    by (auto simp: pthm_of_def tS pS)
  show ?thesis
    by (rule bicompose_aux_valid[OF ok rx cfg A(1) vS wS iS vl' wR _ A(2,3,4,4) _ vl])
      (use lov in simp_all)
qed

end


subsection \<open>Termination\<close>

text \<open>The evaluation of the result sequence of \<^const>\<open>biresolution\<close> to the list of its results.\<close>

inductive brevals :: "'u bops \<Rightarrow> algebra \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> ('u, 'r) rseq \<Rightarrow>
    (bres \<times> (bool \<times> 'r)) list \<Rightarrow> bool" for ops alg rep where
  Nil: "okT (brpull ops alg rep s) None \<Longrightarrow> brevals ops alg rep s []"
| Cons: "okT (brpull ops alg rep s) (Some (xr, s')) \<Longrightarrow> brevals ops alg rep s' xs \<Longrightarrow>
    brevals ops alg rep s (xr # xs)"

lemma brevals_skip:
  assumes "okT (brstep ops alg rep s) (RS_Skip s')" "brevals ops alg rep s' xs"
  shows "brevals ops alg rep s xs"
proof -
  have p: "okT (brpull ops alg rep s) y" if "okT (brpull ops alg rep s') y" for y
    using assms(1) that by (subst brpull.simps) force
  from assms(2) show ?thesis
  proof cases
    case Nil
    with p show ?thesis by (blast intro: brevals.Nil)
  next
    case (Cons xr s'' xs')
    with p show ?thesis by (blast intro: brevals.Cons)
  qed
qed

lemma brevals_App:
  assumes "bevals ops xq rs" "brevals ops alg rep xqq xs"
  shows "brevals ops alg rep (RQ_App r xq xqq) (map (\<lambda>x. (x, r)) rs @ xs)"
  using assms(1)
proof (induction rule: bevals.induct)
  case (Nil s)
  have "okT (brstep ops alg rep (RQ_App r s xqq)) (RS_Skip xqq)" using Nil by force
  from brevals_skip[OF this assms(2)] show ?case by simp
next
  case (Cons s r' s' rs)
  have "okT (brpull ops alg rep (RQ_App r s xqq)) (Some ((r', r), RQ_App r s' xqq))"
    using Cons(1) by (subst brpull.simps) force
  from brevals.Cons[OF this Cons.IH] show ?case by simp
qed

text \<open>
  The results of the rules that pass the quick test are those of their compositions with the
  proof state, in order.
\<close>

definition brres :: "'u bops \<Rightarrow> algebra \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> brctx \<Rightarrow> bool \<times> 'r \<Rightarrow>
    (bres \<times> (bool \<times> 'r)) list \<Rightarrow> bool" where
  "brres ops alg rep ctx r xs \<longleftrightarrow> (\<exists>xq rs. okT (compose ops alg ctx (fst r) (rep (snd r))) xq \<and>
    bevals ops xq rs \<and> map (\<lambda>x. (x, r)) rs = xs)"

lemma brevals_res:
  assumes "\<And>r. r \<in> set brules \<Longrightarrow> \<exists>xq rs. okT (compose ops alg ctx (fst r) (rep (snd r))) xq \<and> bevals ops xq rs"
  shows "\<exists>xs. brevals ops alg rep (res rep ctx brules) xs \<and>
    (\<forall>r\<in>set brules. brc_trace ctx \<or> could_bires (brc_Hs ctx) (brc_B ctx) (fst r) (rep (snd r)) \<longrightarrow>
      (\<exists>ys. brres ops alg rep ctx r ys \<and> set ys \<subseteq> set xs))"
  using assms
proof (induction brules)
  case Nil
  have "okT (brpull ops alg rep RQ_Empty) None" by (subst brpull.simps) simp
  then show ?case by (auto intro: brevals.Nil)
next
  case (Cons r brules)
  obtain e rule where r: "r = (e, rule)" by (cases r)
  from Cons.IH Cons.prems obtain xs where xs: "brevals ops alg rep (res rep ctx brules) xs"
    and al: "\<forall>r\<in>set brules. brc_trace ctx \<or> could_bires (brc_Hs ctx) (brc_B ctx) (fst r) (rep (snd r)) \<longrightarrow>
      (\<exists>ys. brres ops alg rep ctx r ys \<and> set ys \<subseteq> set xs)"
    by auto
  show ?case
  proof (cases "brc_trace ctx \<or> could_bires (brc_Hs ctx) (brc_B ctx) e (rep rule)")
    case True
    from Cons.prems[of r] r obtain xq rs where c: "okT (compose ops alg ctx e (rep rule)) xq"
      and b: "bevals ops xq rs" by auto
    have "okT (brstep ops alg rep (RQ_Make ctx (e, rule) brules))
        (RS_Skip (RQ_App (e, rule) xq (res rep ctx brules)))"
      using c by simp
    from brevals_skip[OF this brevals_App[OF b xs]]
    have "brevals ops alg rep (res rep ctx (r # brules)) (map (\<lambda>x. (x, (e, rule))) rs @ xs)"
      using True r by simp
    moreover have "brres ops alg rep ctx r (map (\<lambda>x. (x, (e, rule))) rs)"
      using c b r by (auto simp: brres_def)
    ultimately show ?thesis using al r by (intro exI[of _ "map (\<lambda>x. (x, (e, rule))) rs @ xs"]) fastforce
  next
    case False
    with xs al r show ?thesis by (intro exI[of _ xs]) auto
  qed
qed

lemma count_prems_list_implies: "count_prems (list_implies Xs Y) = ilength Xs + count_prems Y"
proof (induction Xs)
  case (Cons X Xs)
  then show ?case by (subst count_prems.simps) (simp add: implies_def)
qed simp

lemma nprems_lift_rule: "nprems_of rule \<le> count_prems (th_prop (lift_rule G smax rule))"
proof -
  have "count_prems (th_prop (lift_rule G smax rule)) = ilength (strip_imp_prems (th_prop rule)) +
      count_prems (lift_all (smax + 1) G (strip_imp_concl (th_prop rule)))"
    by (simp add: lift_rule_def Let_def count_prems_list_implies ilength_eq)
  moreover have "nprems_of rule = ilength (strip_imp_prems (th_prop rule))"
    by (simp add: nprems_of_def count_prems_strip_imp)
  ultimately show ?thesis
    using count_prems_nonneg[of "lift_all (smax + 1) G (strip_imp_concl (th_prop rule))"] by simp
qed

context wf_algebra
begin

text \<open>
  The composition of a well-typed rule with a well-typed proof state terminates, and the
  sequence of its results is finite.
\<close>

lemma compose_terminates:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of state i) goal"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_typed ar lo state" and ru: "thm_typed ar 0 rule" and er: "eres_flg \<Longrightarrow> 0 < nprems_of rule"
  shows "\<exists>xq rs. okT (compose (unify_ops cfg vl) alg
      (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal B Hs) eres_flg rule) xq \<and>
    bevals (unify_ops cfg vl) xq rs"
proof -
  let ?lr = "lift_rule goal (th_maxidx state) rule"
  obtain A W where A: "finite A" "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max (th_maxidx ?lr) (th_maxidx state)"
    "\<forall>x. tyA ar A (W x)"
    and wS: "wt_thm ar A W (th_maxidx state) stpairs (list_implies (Bs @ [Bi]) C)"
    and iS: "ibelow (th_maxidx state) (list_implies (Bs @ [Bi]) C)"
    and wR: "wt_thm ar A W (th_maxidx ?lr) (th_tpairs ?lr) (th_prop ?lr)"
    and lov: "lifted_over (th_maxidx state) Bi (th_prop ?lr) (nprems_of rule)"
    and tS: "th_tpairs state = stpairs" and pS: "th_prop state = list_implies (Bs @ [Bi]) C"
    and gB: "goal = Bi" and "-1 \<le> th_maxidx ?lr"
    by (rule compose_typed[OF d g st ru])
  have ns: "0 \<le> nprems_of rule" "nprems_of rule \<le> count_prems (th_prop ?lr)"
    using count_prems_nonneg nprems_lift_rule by (auto simp: nprems_of_def)
  have "\<exists>s rs. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (th_maxidx state, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of rule)) s \<and> bevals (unify_ops cfg vl) s rs"
    by (rule bicompose_aux_terminates[OF cfg A(1) wS iS wR _ A(2,3,4,4) _ ns _ _ vl])
      (use lov er in simp_all)
  then show ?thesis by (simp add: compose_def pthm_of_def tS pS)
qed

text \<open>
  The evaluation of the result sequence of \<^const>\<open>biresolution\<close> of a well-typed proof state
  with well-typed rules terminates, unless elim-resolution is requested for a rule without
  premises; the results of each rule that passes the quick test are those of its composition
  with the proof state.
\<close>

theorem biresolution_terminates:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "thm_typed ar lo state"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> thm_typed ar 0 (rep r) \<and> (e \<longrightarrow> 0 < nprems_of (rep r))"
  obtains stpairs Bs Bi C goal xs where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal" "brevals (unify_ops cfg vl) alg rep s0 xs"
    "\<And>r. r \<in> set brules \<Longrightarrow> trace \<or> could_bires (strip_assums_hyp Bi) (strip_assums_concl Bi) (fst r) (rep (snd r)) \<Longrightarrow>
      \<exists>ys. brres (unify_ops cfg vl) alg rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal
        (strip_assums_concl Bi) (strip_assums_hyp Bi)) r ys \<and> set ys \<subseteq> set xs"
proof -
  from br obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal"
    and s0: "s0 = res rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi)) brules"
    by (rule okT_biresolution)
  let ?ctx = "BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi) (strip_assums_hyp Bi)"
  have "\<exists>xs. brevals (unify_ops cfg vl) alg rep (res rep ?ctx brules) xs \<and>
      (\<forall>r\<in>set brules. brc_trace ?ctx \<or> could_bires (brc_Hs ?ctx) (brc_B ?ctx) (fst r) (rep (snd r)) \<longrightarrow>
        (\<exists>ys. brres (unify_ops cfg vl) alg rep ?ctx r ys \<and> set ys \<subseteq> set xs))"
    by (rule brevals_res) (use compose_terminates[OF d g cfg vl state] rules in fastforce)
  then obtain xs where xs: "brevals (unify_ops cfg vl) alg rep s0 xs"
    and al: "\<forall>r\<in>set brules. trace \<or> could_bires (strip_assums_hyp Bi) (strip_assums_concl Bi) (fst r) (rep (snd r)) \<longrightarrow>
        (\<exists>ys. brres (unify_ops cfg vl) alg rep ?ctx r ys \<and> set ys \<subseteq> set xs)"
    by (simp only: s0 brctx.sel) blast
  show thesis by (rule that[OF d g xs]) (use al in blast)
qed

end


subsection \<open>Completeness\<close>

lemma bevals_det: "bevals ops s rs \<Longrightarrow> bevals ops s rs' \<Longrightarrow> rs = rs'"
proof (induction arbitrary: rs' rule: bevals.induct)
  case (Nil s)
  from Nil.prems show ?case
  proof cases
    case (Cons r2 s2 rs2)
    with Nil.hyps show ?thesis by auto
  qed simp
next
  case (Cons s r s' rs)
  note hyp = Cons.hyps(1) and IH = Cons.IH
  from Cons.prems show ?case
  proof cases
    case Nil
    with hyp show ?thesis by auto
  next
    case (Cons r2 s2 rs2)
    with hyp have "r2 = r" "s2 = s'" by auto
    with Cons IH show ?thesis by simp
  qed
qed

context wf_algebra
begin

text \<open>
  \<^const>\<open>biresolution\<close> enumerates all results of the composition of each rule that passes the
  quick test with the proof state, by \<^const>\<open>bicompose_aux\<close> for the rule lifted over the
  subgoal: by @{thm [source] bicompose_aux_complete}, for which @{thm [source] compose_typed}
  provides the assumptions, every solution of the problems of the composition that the search
  bound admits is an instance of one of them.
\<close>

theorem biresolution_complete:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "thm_typed ar lo state"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> thm_typed ar 0 (rep r) \<and> (e \<longrightarrow> 0 < nprems_of (rep r))"
  obtains stpairs Bs Bi C goal xs where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal" "brevals (unify_ops cfg vl) alg rep s0 xs"
    "\<And>e rule xq rs x. (e, rule) \<in> set brules \<Longrightarrow>
      trace \<or> could_bires (strip_assums_hyp Bi) (strip_assums_concl Bi) e (rep rule) \<Longrightarrow>
      okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state) (stpairs, Bs, Bi, C)
        True e (pthm_of (lift_rule goal (th_maxidx state) (rep rule))) (nprems_of (rep rule))) xq \<Longrightarrow>
      bevals (unify_ops cfg vl) xq rs \<Longrightarrow> x \<in> set rs \<Longrightarrow> (x, (e, rule)) \<in> set xs"
proof -
  from biresolution_terminates[OF assms] obtain stpairs Bs Bi C goal xs
    where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of state i) goal"
      and xs: "brevals (unify_ops cfg vl) alg rep s0 xs"
      and al: "\<And>r. r \<in> set brules \<Longrightarrow> trace \<or> could_bires (strip_assums_hyp Bi) (strip_assums_concl Bi) (fst r) (rep (snd r)) \<Longrightarrow>
        \<exists>ys. brres (unify_ops cfg vl) alg rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal
          (strip_assums_concl Bi) (strip_assums_hyp Bi)) r ys \<and> set ys \<subseteq> set xs"
    by blast
  show thesis
  proof (rule that[OF d g xs])
    fix e rule xq rs x
    assume r: "(e, rule) \<in> set brules"
      and t: "trace \<or> could_bires (strip_assums_hyp Bi) (strip_assums_concl Bi) e (rep rule)"
      and ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state) (stpairs, Bs, Bi, C)
        True e (pthm_of (lift_rule goal (th_maxidx state) (rep rule))) (nprems_of (rep rule))) xq"
      and bv: "bevals (unify_ops cfg vl) xq rs" and x: "x \<in> set rs"
    from al[of "(e, rule)"] r t obtain ys xq' rs' where
      c: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state) (stpairs, Bs, Bi, C)
        True e (pthm_of (lift_rule goal (th_maxidx state) (rep rule))) (nprems_of (rep rule))) xq'"
      and bv': "bevals (unify_ops cfg vl) xq' rs'" and ys: "map (\<lambda>x. (x, (e, rule))) rs' = ys"
      and sub: "set ys \<subseteq> set xs"
      by (auto simp: brres_def compose_def)
    from c ok have "xq' = xq" by auto
    with bv bv' have "rs' = rs" using bevals_det by blast
    with x ys sub show "(x, (e, rule)) \<in> set xs" by auto
  qed
qed

end

end
