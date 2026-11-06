section \<open>Lifting a rule over a subgoal\<close>

theory Lift_Rule
  imports Bicompose_Complete "Pure_Thm.Pure_Biresolution"
begin

text \<open>
  \<open>biresolution\<close> lifts each rule over the subgoal (\<^const>\<open>lift_rule\<close>) and composes it with the
  proof state by \<^const>\<open>bicompose_aux\<close>. The lifted rule has the shape that the theorems on
  \<^const>\<open>bicompose_aux\<close> assume (\<open>lifted_over\<close>), it is well-typed if the rule is, and it is
  valid if the rule is.
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
  using lift_all_aux_lift_pre[of p G0 inc "[]" t] lsplit_ok[of G p G0] by (simp add: lift_all_def)

lemma lift_abs_lsplit:
  "lsplit G = (p, G0) \<Longrightarrow> lift_abs inc G t = abs_pre p (incr_indexes (ptys p) inc t)"
  using lift_abs_aux_lift_pre[of p G0 inc "[]" t] lsplit_ok[of G p G0] by (simp add: lift_abs_def)

lemma vars_combound: "vars (combound u n k) = vars u"
  by (induction u n k rule: combound.induct) simp_all

lemma vars_incr_idx:
  "vars (incr_idx Ts inc lev t) = (\<lambda>((x, i), T). ((x, i + inc), foldr fun_type Ts (incr_tvar inc T))) ` vars t"
  by (induction Ts inc lev t rule: incr_idx.induct) (simp_all add: vars_combound image_Un)

lemma incr_tvar_0 [simp]: "incr_tvar 0 T = T"
  by (induction T) (auto simp: map_idI)

lemma vars_incr_indexes:
  "vars (incr_indexes Ts inc t) = (\<lambda>((x, i), T). ((x, i + inc), foldr fun_type Ts (incr_tvar inc T))) ` vars t"
  by (cases "Ts = [] \<and> inc = 0") (auto simp: incr_indexes_def vars_incr_idx image_iff)

lemma strip_imp_list_implies:
  "strip_imp_prems (list_implies As B) = As @ strip_imp_prems B"
  "strip_imp_concl (list_implies As B) = strip_imp_concl B"
  by (induction As) (subst strip_imp_prems.simps strip_imp_concl.simps; simp add: implies_def)+

lemma count_prems_strip_imp: "count_prems t = ilength (strip_imp_prems t)"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "dest_imp t")
    case (Some AB)
    then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
    from less.IH[of B] AB dest_imp_size[OF AB] show ?thesis
      by (subst count_prems.simps, subst strip_imp_prems.simps) simp
  next
    case None
    then show ?thesis
      by (subst count_prems.simps, subst strip_imp_prems.simps) simp
  qed
qed

lemma strip_imp_vars:
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

context pure_sig
begin

text \<open>A proposition is the implication of its premises and its conclusion:\<close>

lemma list_implies_strip_imp: "e \<turnstile> t : T \<Longrightarrow> t = list_implies (strip_imp_prems t) (strip_imp_concl t)"
proof (induction t arbitrary: T rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "dest_imp t")
    case (Some AB)
    then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
    note td = typing_dest_imp[OF less.prems AB]
    have IH: "B = list_implies (strip_imp_prems B) (strip_imp_concl B)"
      by (rule less.IH[OF _ td(5)]) (use dest_imp_size[OF AB] in simp)
    have "list_implies (strip_imp_prems t) (strip_imp_concl t) =
        implies $ A $ list_implies (strip_imp_prems B) (strip_imp_concl B)"
      by (subst strip_imp_prems.simps, subst strip_imp_concl.simps) (simp add: AB)
    with IH td(1) show ?thesis by simp
  next
    case None
    then show ?thesis
      by (subst strip_imp_prems.simps, subst strip_imp_concl.simps) simp
  qed
qed

end



subsection \<open>Instantiating the lifted parameters\<close>

text \<open>
  \<open>bfree lev fs t\<close> replaces the loose bound variables \<open>lev, \<dots>, lev + n - 1\<close> of \<open>t\<close> (as seen at
  the top) by the closed terms \<open>fs\<close> of length \<open>n\<close>, the outermost first.
\<close>

fun bfree :: "integer \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "bfree lev fs (Bound i) =
    (if lev \<le> i \<and> i < lev + ilength fs then fs ! nat_of_integer (lev + ilength fs - 1 - i) else Bound i)"
| "bfree lev fs (Abs a T t) = Abs a T (bfree (lev + 1) fs t)"
| "bfree lev fs (t $ u) = bfree lev fs t $ bfree lev fs u"
| "bfree lev fs t = t"

lemma incr_bv_no_loose: "\<not> loose_bvar t k \<Longrightarrow> incr_bv n k t = t"
  by (induction t arbitrary: k) auto

lemma bfree_no_loose: "\<not> loose_bvar t lev \<Longrightarrow> bfree lev fs t = t"
  by (induction t arbitrary: lev) auto

lemma bfree_Nil [simp]: "bfree lev [] t = t"
  by (induction t arbitrary: lev) auto

lemma subst_bfree:
  assumes f: "closed f"
  shows "\<not> loose_bvar s (lev + ilength fs + 1) \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    bfree lev fs (s[f / lev + ilength fs]) = bfree lev (f # fs) s"
proof (induction s arbitrary: lev)
  case (Bound i)
  let ?n = "ilength fs"
  have bf: "bfree lev fs f = f"
  proof (rule bfree_no_loose)
    show "\<not> loose_bvar f lev" using f loose_bvar_mono[of f lev 0] Bound.prems(2) by (auto simp: closed_def)
  qed
  show ?case
  proof (cases "i < lev + ?n")
    case True
    then have si: "(Bound i)[f / lev + ?n] = Bound i" by simp
    show ?thesis
    proof (cases "lev \<le> i")
      case True
      have "nat_of_integer (lev + ilength (f # fs) - 1 - i) = Suc (nat_of_integer (lev + ?n - 1 - i))"
        using True \<open>i < lev + ?n\<close> by (simp add: integer_reps integer_arith nat_eq_iff)
      with True \<open>i < lev + ?n\<close> si show ?thesis by (simp add: integer_arith)
    next
      case False
      with si show ?thesis by simp
    qed
  next
    case False
    with Bound.prems have i: "i = lev + ?n" by (simp add: integer_arith)
    have "nat_of_integer (lev + ilength (f # fs) - 1 - i) = 0" using i by simp
    moreover have "(Bound i)[f / lev + ?n] = f" using i by simp
    moreover have "lev \<le> i" "i < lev + ilength (f # fs)" using i by simp_all
    ultimately show ?thesis using bf by simp
  qed
next
  case (Abs a T t)
  have "lift f 0 = f" using f by (simp add: closed_def incr_bv_no_loose)
  with Abs.IH[of "lev + 1"] Abs.prems show ?case by (simp add: algebra_simps)
qed auto

lemma subst_abs_list:
  "closed f \<Longrightarrow> (abs_list bs t)[f/k] = abs_list bs (t[f / k + ilength bs])"
proof (induction bs arbitrary: k)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by (cases b)
  have "lift f 0 = f" using Cons.prems by (simp add: closed_def incr_bv_no_loose)
  with Cons.IH[OF Cons.prems, of "k + 1"] show ?case by (simp add: b algebra_simps)
qed simp

text \<open>Applying the closure over the parameters to closed terms instantiates the parameters:\<close>

lemma abs_list_apps_beta:
  "length bs = length fs \<Longrightarrow> \<forall>f\<in>set fs. closed f \<Longrightarrow> \<not> loose_bvar t (ilength bs) \<Longrightarrow>
    abs_list bs t \<degree>\<degree> fs \<rightarrow>\<^sub>\<beta>\<^sup>* bfree 0 fs t"
proof (induction bs arbitrary: fs t)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  obtain f fs' where fs: "fs = f # fs'" using Cons.prems(1) by (cases fs) auto
  obtain x T where b: "b = (x, T)" by (cases b)
  have lf: "length bs = length fs'" using Cons.prems(1) fs by simp
  have cf: "closed f" "\<forall>f\<in>set fs'. closed f" using Cons.prems(2) fs by auto
  have il: "ilength fs' = ilength bs" using lf by (simp add: ilength_eq)
  have "abs_list (b # bs) t \<degree>\<degree> fs = (Abs x T (abs_list bs t) $ f) \<degree>\<degree> fs'" by (simp add: b fs)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* (abs_list bs t)[f/0] \<degree>\<degree> fs'" by (intro apps_preserves_beta2) blast
  also have "(abs_list bs t)[f/0] = abs_list bs (t[f / ilength bs])" by (simp add: subst_abs_list[OF cf(1)])
  also have "abs_list bs (t[f / ilength bs]) \<degree>\<degree> fs' \<rightarrow>\<^sub>\<beta>\<^sup>* bfree 0 fs' (t[f / ilength bs])"
  proof (rule Cons.IH[OF lf cf(2)])
    have "\<not> loose_bvar t (ilength bs + 1)" using Cons.prems(3) by simp
    moreover have "\<not> loose_bvar f (ilength bs)"
      using cf(1) loose_bvar_mono[of f "ilength bs" 0] by (auto simp: closed_def)
    ultimately show "\<not> loose_bvar (t[f / ilength bs]) (ilength bs)"
      by (intro loose_bvar_subst) simp_all
  qed
  also have "bfree 0 fs' (t[f / ilength bs]) = bfree 0 fs t"
    using subst_bfree[OF cf(1), of t 0 fs'] Cons.prems(3) il fs by simp
  finally show ?case .
qed


context pure_sig
begin

text \<open>
  The instance of the original term that corresponds to an instance of a lifted term at fixed
  parameters \<open>fs\<close>: the indices of the type variables are shifted (\<open>tinc\<close>), and each variable
  is instantiated by the term for its lifted variable, applied to the parameters (\<open>lsubst\<close>).
\<close>

definition tinc :: "integer \<Rightarrow> tinst \<Rightarrow> tinst" where
  "tinc inc \<rho> = (\<lambda>(a, i) S. \<rho> (a, i + inc) S)"

lemma tsubst_incr_tvar: "tsubst \<rho> (incr_tvar inc T) = tsubst (tinc inc \<rho>) T"
  by (induction inc T rule: incr_tvar.induct) (simp_all add: tinc_def)

definition lsubst :: "integer \<Rightarrow> tinst \<Rightarrow> ptyp list \<Rightarrow> vsubst \<Rightarrow> pterm list \<Rightarrow> vsubst" where
  "lsubst inc \<rho> Ts \<sigma> fs = (\<lambda>(x, i) U. \<sigma> (x, i + inc) (foldr fun_type (map (tsubst \<rho>) Ts) U) \<degree>\<degree> fs)"

lemma ap_combound: "ap \<rho> \<sigma> (combound t n k) = combound (ap \<rho> \<sigma> t) n k"
  by (induction t n k rule: combound.induct) simp_all

lemma bfree_combound:
  "closed c \<Longrightarrow> k + m = length fs \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    bfree lev fs (combound c (lev + of_nat m) k) = c \<degree>\<degree> take k fs"
proof (induction k arbitrary: m)
  case 0
  have "\<not> loose_bvar c lev" using 0(1,3) loose_bvar_mono[of c lev 0] by (auto simp: closed_def)
  then show ?case by (simp add: bfree_no_loose)
next
  case (Suc k)
  have IH: "bfree lev fs (combound c (lev + of_nat (Suc m)) k) = c \<degree>\<degree> take k fs"
    by (rule Suc.IH) (use Suc.prems in simp_all)
  have k: "k < length fs" using Suc.prems(2) by simp
  have n: "ilength fs = of_nat (Suc k + m)" using Suc.prems(2) by (simp add: ilength_eq integer_of_nat_eq_of_nat)
  have c1: "lev \<le> lev + of_nat m" "lev + of_nat m < lev + ilength fs" using n by (simp_all add: integer_arith)
  have i: "nat_of_integer (lev + ilength fs - 1 - (lev + of_nat m)) = k"
    using n by (simp add: integer_reps)
  have "bfree lev fs (Bound (lev + of_nat m)) = fs ! nat_of_integer (lev + ilength fs - 1 - (lev + of_nat m))"
    using c1 by simp
  then have b: "bfree lev fs (Bound (lev + of_nat m)) = fs ! k" using i by simp
  have e: "lev + of_nat (Suc m) = lev + of_nat m + 1" by (simp add: algebra_simps)
  show ?case using IH[unfolded e] b k by (simp add: take_Suc_conv_app_nth)
qed

lemma bfree_ap_incr_idx:
  assumes cs: "closed_subst \<sigma>" and l: "length fs = length Ts"
  shows "\<not> loose_bvar t lev \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    bfree lev fs (ap \<rho> \<sigma> (incr_idx Ts inc lev t)) = ap (tinc inc \<rho>) (lsubst inc \<rho> Ts \<sigma> fs) t"
proof (induction t arbitrary: lev)
  case (Var xi T)
  obtain x i where xi: "xi = (x, i)" by (cases xi)
  let ?c = "\<sigma> (x, i + inc) (foldr fun_type (map (tsubst \<rho>) Ts) (tsubst (tinc inc \<rho>) T))"
  have c: "closed ?c" by (rule closed_substD[OF cs])
  have "tsubst \<rho> (foldr fun_type Ts (incr_tvar inc T)) = foldr fun_type (map (tsubst \<rho>) Ts) (tsubst (tinc inc \<rho>) T)"
    by (induction Ts) (simp_all add: tsubst_incr_tvar)
  then have "ap \<rho> \<sigma> (incr_idx Ts inc lev (Var (x, i) T)) = combound ?c lev (length Ts)"
    by (simp add: ap_combound)
  moreover have "bfree lev fs (combound ?c (lev + of_nat 0) (length Ts)) = ?c \<degree>\<degree> take (length Ts) fs"
    by (rule bfree_combound[OF c]) (use l Var.prems(2) in simp_all)
  then have "bfree lev fs (combound ?c lev (length Ts)) = ?c \<degree>\<degree> fs" using l by simp
  ultimately show ?case by (simp add: lsubst_def xi)
next
  case (Abs a T t)
  then show ?case by (simp add: tsubst_incr_tvar algebra_simps)
qed (simp_all add: tsubst_incr_tvar)

end

end
