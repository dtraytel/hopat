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


subsection \<open>Free variables and parameters\<close>

text \<open>The names of the free variables of a term:\<close>

fun fnames :: "pterm \<Rightarrow> name set" where
  "fnames (Free x T) = {x}"
| "fnames (Abs a T t) = fnames t"
| "fnames (t $ u) = fnames t \<union> fnames u"
| "fnames _ = {}"

lemma finite_fnames [simp]: "finite (fnames t)"
  by (induction t) simp_all

lemma incr_idx_id: "incr_idx [] 0 lev t = t"
  by (induction "[] :: ptyp list" "0 :: integer" lev t rule: incr_idx.induct) simp_all

lemma incr_indexes_idx: "incr_indexes Ts inc t = incr_idx Ts inc 0 t"
  by (simp add: incr_indexes_def incr_idx_id)

lemma loose_bvar_combound: "\<not> loose_bvar c j \<Longrightarrow> k + of_nat m \<le> j \<Longrightarrow> \<not> loose_bvar (combound c k m) j"
proof (induction m arbitrary: k)
  case (Suc m)
  have "k < j" using Suc.prems(2) by (simp add: integer_arith)
  moreover have "\<not> loose_bvar (combound c (k + 1) m) j"
    by (rule Suc.IH) (use Suc.prems in \<open>simp_all add: algebra_simps\<close>)
  ultimately show ?case by simp
qed simp

lemma loose_bvar_incr_idx:
  "\<not> loose_bvar t lev \<Longrightarrow> \<not> loose_bvar (incr_idx Ts inc lev t) (lev + ilength Ts)"
proof (induction Ts inc lev t rule: incr_idx.induct)
  case (1 Ts inc lev x i T)
  have "\<not> loose_bvar (combound (Var (x, i + inc) (foldr fun_type Ts (incr_tvar inc T))) lev (length Ts))
      (lev + ilength Ts)"
    by (rule loose_bvar_combound) (simp_all add: ilength_eq integer_of_nat_eq_of_nat)
  then show ?case by simp
next
  case (3 Ts inc lev x T t)
  then show ?case by (simp add: algebra_simps)
next
  case (6 Ts inc lev i)
  then show ?case using ilength_nonneg[of Ts] by (simp add: integer_arith)
qed simp_all

context pure_model
begin

text \<open>The fresh free variables \<open>Fs\<close> valued by \<open>us\<close>:\<close>

definition fval :: "'u vval \<Rightarrow> (name \<times> ptyp) list \<Rightarrow> 'u list \<Rightarrow> 'u vval" where
  "fval \<xi> Fs us = (fst \<xi>, \<lambda>F T. case map_of (zip Fs us) (F, T) of Some u \<Rightarrow> u | None \<Rightarrow> snd \<xi> F T)"

lemma sem_fresh:
  "fnames t \<inter> fst ` set Fs = {} \<Longrightarrow> sem \<eta> (fval \<xi> Fs us) bv t = sem \<eta> \<xi> bv t"
proof (induction t arbitrary: bv)
  case (Free x T)
  then have "(x, T) \<notin> set Fs" by force
  then have "map_of (zip Fs us) (x, T) = None"
    by (auto simp: map_of_eq_None_iff dest: set_zip_leftD)
  then show ?case by (simp add: fval_def)
next
  case (App t u)
  then show ?case by (simp add: Int_Un_distrib2)
qed (simp_all add: fval_def)

lemma sem_bfree:
  assumes d: "distinct Fs" and l: "length us = length Fs"
  shows "fnames s \<inter> fst ` set Fs = {} \<Longrightarrow> \<not> loose_bvar s (lev + ilength Fs) \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    (\<And>i. 0 \<le> i \<Longrightarrow> i < lev \<Longrightarrow> bv' i = bv i) \<Longrightarrow>
    (\<And>j. j < length Fs \<Longrightarrow> bv (lev + of_nat j) = us ! (length Fs - 1 - j)) \<Longrightarrow>
    sem \<eta> (fval \<xi> Fs us) bv' (bfree lev (map (\<lambda>(F, T). Free F T) Fs) s) = sem \<eta> \<xi> bv s"
proof (induction s arbitrary: lev bv bv')
  case (Bound i)
  let ?n = "length Fs"
  show ?case
  proof (cases "lev \<le> i")
    case True
    with Bound.prems(2) have i: "i < lev + ilength Fs" by simp
    define j where "j = nat_of_integer (i - lev)"
    have ij: "i = lev + of_nat j" and jn: "j < ?n"
      using True i by (simp_all add: j_def integer_reps ilength_eq integer_of_nat_eq_of_nat integer_eq_iff)
    have k: "nat_of_integer (lev + ilength (map (\<lambda>(F, T). Free F T) Fs) - 1 - i) = ?n - 1 - j"
      using ij jn by (simp add: ilength_eq integer_of_nat_eq_of_nat integer_reps)
    obtain F T where FT: "Fs ! (?n - 1 - j) = (F, T)" by (cases "Fs ! (?n - 1 - j)")
    have mem: "?n - 1 - j < ?n" using jn by simp
    have "map_of (zip Fs us) (F, T) = Some (us ! (?n - 1 - j))"
    proof -
      have "(Fs ! (?n - 1 - j), us ! (?n - 1 - j)) \<in> set (zip Fs us)"
        using mem l by (auto simp: set_zip intro!: exI[of _ "?n - 1 - j"])
      moreover have "distinct (map fst (zip Fs us))" using d l by simp
      ultimately show ?thesis using FT by (simp add: map_of_is_SomeI)
    qed
    moreover have "0 \<le> i" using True Bound.prems(3) by simp
    ultimately show ?thesis
      using True i k FT mem Bound.prems(5)[OF jn] ij by (simp add: fval_def)
  next
    case False
    then show ?thesis using Bound.prems(4)[of i] by simp
  qed
next
  case (Free x T)
  then show ?case using sem_fresh[of "Free x T" Fs \<eta> \<xi> us bv'] by simp
next
  case (Abs a T t)
  have "sem \<eta> (fval \<xi> Fs us) (push v bv') (bfree (lev + 1) (map (\<lambda>(F, T). Free F T) Fs) t) =
      sem \<eta> \<xi> (push v bv) t" for v
  proof (rule Abs.IH)
    show "fnames t \<inter> fst ` set Fs = {}" using Abs.prems(1) by simp
    show "\<not> loose_bvar t (lev + 1 + ilength Fs)" using Abs.prems(2) by (simp add: algebra_simps)
    show "0 \<le> lev + 1" using Abs.prems(3) by simp
    show "push v bv' i = push v bv i" if "0 \<le> i" "i < lev + 1" for i
    proof (cases "i = 0")
      case False
      then have "0 \<le> i - 1" "i - 1 < lev" using that by (simp_all add: integer_arith)
      with Abs.prems(4) False show ?thesis by (simp add: push_def)
    qed (simp add: push_def)
    show "push v bv (lev + 1 + of_nat j) = us ! (length Fs - 1 - j)" if "j < length Fs" for j
    proof -
      have "lev + 1 + of_nat j \<noteq> 0" "lev + 1 + of_nat j - 1 = lev + of_nat j"
        using Abs.prems(3) by (simp_all add: integer_arith)
      with Abs.prems(5)[OF that] show ?thesis by (simp add: push_def)
    qed
  qed
  then show ?case by simp
next
  case (App t u)
  from App.prems(1,2) have p: "fnames t \<inter> fst ` set Fs = {}" "fnames u \<inter> fst ` set Fs = {}"
    "\<not> loose_bvar t (lev + ilength Fs)" "\<not> loose_bvar u (lev + ilength Fs)" by auto
  show ?case using App.IH(1)[OF p(1) p(3) App.prems(3-5)] App.IH(2)[OF p(2) p(4) App.prems(3-5)] by simp
qed (simp_all add: fval_def)

lemma vpushes_snoc: "vpushes bv (us @ [u]) = push u (vpushes bv us)"
  by (induction us arbitrary: bv) simp_all

lemma vpushes_nth: "j < length us \<Longrightarrow> vpushes bv us (of_nat j) = us ! (length us - 1 - j)"
proof (induction us arbitrary: j rule: rev_induct)
  case (snoc u us)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis by (simp add: vpushes_snoc push_def nth_append)
  next
    case (Suc j')
    have "of_nat j \<noteq> (0 :: integer)" "of_nat j - 1 = (of_nat j' :: integer)" using Suc by (simp_all add: integer_arith)
    then have "vpushes bv (us @ [u]) (of_nat j) = vpushes bv us (of_nat j')"
      by (simp add: vpushes_snoc push_def)
    moreover have "j' < length us" "length us - Suc j' < length us" using snoc.prems Suc by simp_all
    ultimately show ?thesis using snoc.IH[of j'] Suc by (simp add: nth_append)
  qed
qed simp

end


context pure_valuation
begin

text \<open>
  If, for all values of the parameters of a prefix, the instances of \<open>Xs\<close> imply that of \<open>Y\<close>,
  then the instances of \<open>Xs\<close> under the prefix imply that of \<open>Y\<close> under the prefix.
\<close>

lemma hb_lift_pre_mp:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
  shows "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> \<forall>X\<in>set Xs. e \<turnstile> lift_pre p X : propT \<Longrightarrow> e \<turnstile> lift_pre p Y : propT \<Longrightarrow>
    bvals \<eta> (ienv \<rho> e) bv \<Longrightarrow>
    (\<And>us. list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) (ptys p) us \<Longrightarrow>
      \<forall>X\<in>set Xs. hb (vpushes bv us) (ap \<rho> \<sigma> X) \<Longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> Y)) \<Longrightarrow>
    \<forall>X\<in>set Xs. hb bv (ap \<rho> \<sigma> (lift_pre p X)) \<Longrightarrow> hb bv (ap \<rho> \<sigma> (lift_pre p Y))"
proof (induction p arbitrary: e bv)
  case Nil
  then show ?case using Nil.prems(5)[of "[]"] by simp
next
  case (Cons i p)
  have oki: "litem_ok i" and okp: "\<forall>i\<in>set p. litem_ok i" using Cons.prems(1) by simp_all
  show ?case
  proof (cases i)
    case (LImp c H)
    note iY = typing_lift_pre_imp[OF oki Cons.prems(3) LImp]
    have iX: "lift_pre (i # p) X = implies $ H $ lift_pre p X" "e \<turnstile> lift_pre p X : propT"
      if "X \<in> set Xs" for X
      using typing_lift_pre_imp[OF oki _ LImp, where e = e and X = X] Cons.prems(2) that by auto
    have "hb bv (ap \<rho> \<sigma> (lift_pre p Y))" if hH: "hb bv (ap \<rho> \<sigma> H)"
    proof (rule Cons.IH[OF okp _ iY(3) Cons.prems(4)])
      show "\<forall>X\<in>set Xs. e \<turnstile> lift_pre p X : propT" using iX(2) by blast
      show "hb (vpushes bv us) (ap \<rho> \<sigma> Y)" if "list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) (ptys p) us"
        "\<forall>X\<in>set Xs. hb (vpushes bv us) (ap \<rho> \<sigma> X)" for us
        using Cons.prems(5)[of us] that LImp by simp
      show "\<forall>X\<in>set Xs. hb bv (ap \<rho> \<sigma> (lift_pre p X))"
      proof
        fix X assume X: "X \<in> set Xs"
        from Cons.prems(6) X have "hb bv (ap \<rho> \<sigma> (lift_pre (i # p) X))" by blast
        with hb_imp[OF \<rho> \<sigma> iY(2) iX(2)[OF X] Cons.prems(4)] iX(1)[OF X] hH
        show "hb bv (ap \<rho> \<sigma> (lift_pre p X))" by simp
      qed
    qed
    then show ?thesis using iY(1) hb_imp[OF \<rho> \<sigma> iY(2,3) Cons.prems(4)] by simp
  next
    case (LAll c a T)
    note iY = typing_lift_pre_all[OF oki Cons.prems(3) LAll]
    have iX: "lift_pre (i # p) X = all_const T $ Abs a T (lift_pre p X)" "e\<langle>0:T\<rangle> \<turnstile> lift_pre p X : propT"
      if "X \<in> set Xs" for X
      using typing_lift_pre_all[OF oki _ LAll, where e = e and X = X] Cons.prems(2) that by auto
    have "hb (push u bv) (ap \<rho> \<sigma> (lift_pre p Y))" if u: "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" for u
    proof (rule Cons.IH[OF okp _ iY(2) bvals_ienv_push[OF Cons.prems(4) u]])
      show "\<forall>X\<in>set Xs. e\<langle>0:T\<rangle> \<turnstile> lift_pre p X : propT" using iX(2) by blast
      show "hb (vpushes (push u bv) us) (ap \<rho> \<sigma> Y)"
        if "list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) (ptys p) us"
          "\<forall>X\<in>set Xs. hb (vpushes (push u bv) us) (ap \<rho> \<sigma> X)" for us
        using Cons.prems(5)[of "u # us"] that u LAll by simp
      show "\<forall>X\<in>set Xs. hb (push u bv) (ap \<rho> \<sigma> (lift_pre p X))"
      proof
        fix X assume X: "X \<in> set Xs"
        from Cons.prems(6) X have "hb bv (ap \<rho> \<sigma> (lift_pre (i # p) X))" by blast
        with hb_all[OF \<rho> \<sigma> iX(2)[OF X] Cons.prems(4)] iX(1)[OF X] u
        show "hb (push u bv) (ap \<rho> \<sigma> (lift_pre p X))" by simp
      qed
    qed
    then show ?thesis using hb_all[OF \<rho> \<sigma> iY(2) Cons.prems(4)] iY(1) by simp
  qed
qed

end


subsection \<open>Typing of lifted terms\<close>

definition tren :: "integer \<Rightarrow> tinst" where
  "tren inc = (\<lambda>(a, i) S. TVar (a, i + inc) S)"

lemma incr_tvar_tren: "incr_tvar inc T = tsubst (tren inc) T"
  by (induction inc T rule: incr_tvar.induct) (simp_all add: tren_def)

context pure_sig
begin

lemma cert_inst_tren: "cert_inst (tren inc)"
  by (auto simp: cert_inst_def tren_def cert_typ_def)

lemma cert_typ_incr_tvar: "cert_typ alg ar T \<Longrightarrow> cert_typ alg ar (incr_tvar inc T)"
  by (simp add: incr_tvar_tren cert_typ_tsubst[OF _ cert_inst_tren])

lemma typing_combound:
  "k + m = length Ts \<Longrightarrow> (\<And>j. j < length Ts \<Longrightarrow> e (lev + of_nat j) = Ts ! (length Ts - 1 - j)) \<Longrightarrow>
    0 \<le> lev \<Longrightarrow> e \<turnstile> c : take k Ts \<Rrightarrow> (drop k Ts \<Rrightarrow> U) \<Longrightarrow>
    e \<turnstile> combound c (lev + of_nat m) k : drop k Ts \<Rrightarrow> U"
proof (induction k arbitrary: m)
  case (Suc k)
  have k: "k < length Ts" using Suc.prems(1) by simp
  have d: "drop k Ts = Ts ! k # drop (Suc k) Ts" using k by (simp add: Cons_nth_drop_Suc)
  have IH: "e \<turnstile> combound c (lev + of_nat (Suc m)) k : drop k Ts \<Rrightarrow> U"
  proof (rule Suc.IH)
    show "k + Suc m = length Ts" using Suc.prems(1) by simp
    have "take (Suc k) Ts = take k Ts @ [Ts ! k]" using k by (simp add: take_Suc_conv_app_nth)
    then show "e \<turnstile> c : take k Ts \<Rrightarrow> (drop k Ts \<Rrightarrow> U)" using Suc.prems(4) d by simp
  qed (use Suc.prems in simp_all)
  have e1: "lev + of_nat (Suc m) = lev + of_nat m + 1" by (simp add: algebra_simps)
  have "length Ts - 1 - m = k" using Suc.prems(1) by simp
  then have "e (lev + of_nat m) = Ts ! k" using Suc.prems(2)[of m] Suc.prems(1) by simp
  moreover have "0 \<le> lev + of_nat m" using Suc.prems(3) by (simp add: integer_arith)
  ultimately show ?case using IH[unfolded e1] d by auto
qed simp

lemma typing_incr_idx:
  "e \<turnstile> t : T \<Longrightarrow> (\<And>j. 0 \<le> j \<Longrightarrow> j < lev \<Longrightarrow> e' j = incr_tvar inc (e j)) \<Longrightarrow>
    (\<And>j. j < length Ts \<Longrightarrow> e' (lev + of_nat j) = Ts ! (length Ts - 1 - j)) \<Longrightarrow>
    \<forall>U\<in>set Ts. cert_typ alg ar U \<Longrightarrow> 0 \<le> lev \<Longrightarrow> \<not> loose_bvar t lev \<Longrightarrow>
    e' \<turnstile> incr_idx Ts inc lev t : incr_tvar inc T"
proof (induction arbitrary: e' lev rule: typing.induct)
  case (Const c T e)
  then show ?case
    by (auto simp: incr_tvar_tren intro!: const_typ_ok_tsubst cert_typ_tsubst[OF _ cert_inst_tren])
next
  case (Free T e x)
  then show ?case by (auto intro!: cert_typ_incr_tvar)
next
  case (Var T e xi)
  obtain x i where xi: "xi = (x, i)" by (cases xi)
  have c: "cert_typ alg ar (Ts \<Rrightarrow> incr_tvar inc T)"
    using Var.prems(3) cert_typ_incr_tvar[OF Var.hyps] by (induction Ts) (auto simp: cert_typ_def tarity_def)
  have "e' \<turnstile> combound (Var (x, i + inc) (Ts \<Rrightarrow> incr_tvar inc T)) (lev + of_nat 0) (length Ts) :
      drop (length Ts) Ts \<Rrightarrow> incr_tvar inc T"
    by (rule typing_combound) (use Var.prems c in auto)
  then show ?case by (simp add: xi)
next
  case (Bound i e T)
  then show ?case by auto
next
  case (Abs T e t U a)
  have "e'\<langle>0:incr_tvar inc T\<rangle> \<turnstile> incr_idx Ts inc (lev + 1) t : incr_tvar inc U"
  proof (rule Abs.IH)
    show "(e'\<langle>0:incr_tvar inc T\<rangle>) j = incr_tvar inc ((e\<langle>0:T\<rangle>) j)" if "0 \<le> j" "j < lev + 1" for j
      using that Abs.prems(1)[of "j - 1"] by (auto simp: shift_def integer_arith)
    show "(e'\<langle>0:incr_tvar inc T\<rangle>) (lev + 1 + of_nat j) = Ts ! (length Ts - 1 - j)" if "j < length Ts" for j
    proof -
      have "\<not> lev + 1 + of_nat j < 0" "lev + 1 + of_nat j \<noteq> 0" "lev + 1 + of_nat j - 1 = lev + of_nat j"
        using Abs.prems(4) by (simp_all add: integer_arith)
      with Abs.prems(2)[OF that] show ?thesis by (simp add: shift_def)
    qed
  qed (use Abs.prems in \<open>simp_all add: algebra_simps\<close>)
  then show ?case using Abs.hyps(1) by (auto intro!: cert_typ_incr_tvar)
next
  case (App e s T U t)
  then show ?case by auto
qed

end

end
