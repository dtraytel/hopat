section \<open>Lifting a rule over a subgoal\<close>

theory Lift_Rule
  imports Bicompose_Thm "Pure_Thm.Pure_Biresolution"
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
        using True \<open>i < lev + ?n\<close> by (simp add: integer_reps nat_eq_iff)
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
      using True i by (simp_all add: j_def integer_reps ilength_eq integer_of_nat_eq_of_nat)
    have k: "nat_of_integer (lev + ilength (map (\<lambda>(F, T). Free F T) Fs) - 1 - i) = ?n - 1 - j"
      using ij jn by (simp add: ilength_eq integer_of_nat_eq_of_nat integer_reps)
    obtain F T where FT: "Fs ! (?n - 1 - j) = (F, T)" by (cases "Fs ! (?n - 1 - j)")
    have mem: "?n - 1 - j < ?n" using jn by simp
    have "map_of (zip Fs us) (F, T) = Some (us ! (?n - 1 - j))"
    proof -
      have "(Fs ! (?n - 1 - j), us ! (?n - 1 - j)) \<in> set (zip Fs us)"
        using mem l by (auto simp: set_zip intro!: exI[of _ "?n - 1 - j"])
      moreover have "distinct (map fst (zip Fs us))" using d l by simp
      ultimately show ?thesis using FT by simp
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


subsection \<open>Auxiliary facts\<close>

lemma infinite_literal: "infinite (UNIV :: String.literal set)"
proof
  assume fin: "finite (UNIV :: String.literal set)"
  have "inj (\<lambda>n. String.implode (replicate n CHR ''a''))"
  proof (rule injI)
    fix m n assume "String.implode (replicate m CHR ''a'') = String.implode (replicate n CHR ''a'')"
    then have "String.explode (String.implode (replicate m CHR ''a'')) =
        String.explode (String.implode (replicate n CHR ''a''))" by simp
    then have "length (replicate m CHR ''a'') = length (replicate n CHR ''a'')"
      by (metis String.explode_implode_eq length_map)
    then show "m = n" by simp
  qed
  moreover have "finite (range (\<lambda>n. String.implode (replicate n CHR ''a'')))"
    using fin by (rule finite_subset[rotated]) simp
  ultimately have "finite (UNIV :: nat set)" by (rule finite_imageD[rotated])
  then show False by simp
qed

lemma fresh_name_list:
  assumes "finite N"
  obtains xs :: "name list" where "length xs = n" "distinct xs" "set xs \<inter> N = {}"
proof -
  have "infinite (UNIV - N)" using infinite_literal assms by (simp add: Diff_infinite_finite)
  then obtain g :: "nat \<Rightarrow> name" where g: "inj g" "range g \<subseteq> UNIV - N"
    using infinite_countable_subset by blast
  show thesis
  proof (rule that[of "map g [0..<n]"])
    show "distinct (map g [0..<n])" using g(1) by (simp add: distinct_map) (meson g(1) inj_on_subset subset_UNIV)
  qed (use g(2) in auto)
qed

lemma tsubst_no_tvars: "tvars T = {} \<Longrightarrow> tsubst \<rho> T = T"
  by (induction T) (auto simp: map_idI)


lemma lparams_length: "length (lparams p) = length (ptys p)"
  by (induction p rule: lparams.induct) simp_all

context pure_sig
begin

lemma ap_ground: "vars t = {} \<Longrightarrow> ttvars t = {} \<Longrightarrow> ap \<rho> \<sigma> t = t"
  by (induction t) (auto simp: ttvars_def tsubst_no_tvars)

lemma typing_lift_preI:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> e \<turnstile> lift_pre p G0 : propT \<Longrightarrow> pushes e (ptys p) \<turnstile> X : propT \<Longrightarrow>
    e \<turnstile> lift_pre p X : propT"
proof (induction p arbitrary: e)
  case (Cons i p)
  have oki: "litem_ok i" and okp: "\<forall>i\<in>set p. litem_ok i" using Cons.prems(1) by simp_all
  show ?case
  proof (cases i)
    case (LImp c H)
    note iG = typing_lift_pre_imp[OF oki Cons.prems(2) LImp]
    from oki LImp obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have "lift_pre (i # p) X = c $ H $ lift_pre p X" "lift_pre (i # p) G0 = c $ H $ lift_pre p G0"
      using LImp by simp_all
    with iG(1) have X: "lift_pre (i # p) X = implies $ H $ lift_pre p X" by (simp add: implies_def)
    have "e \<turnstile> lift_pre p X : propT" by (rule Cons.IH[OF okp iG(3)]) (use Cons.prems(3) LImp in simp)
    moreover have "cert_typ alg ar imp_type"
      using Cons.prems(2) iG(1) by (simp add: typing_implies)
    ultimately show ?thesis using X iG(2) by (simp add: typing_implies)
  next
    case (LAll c a T)
    note iG = typing_lift_pre_all[OF oki Cons.prems(2) LAll]
    have "lift_pre (i # p) X = c $ Abs a T (lift_pre p X)" "lift_pre (i # p) G0 = c $ Abs a T (lift_pre p G0)"
      using LAll by simp_all
    with iG(1) have X: "lift_pre (i # p) X = all_const T $ Abs a T (lift_pre p X)" by simp
    have "e\<langle>0:T\<rangle> \<turnstile> lift_pre p X : propT" by (rule Cons.IH[OF okp iG(2)]) (use Cons.prems(3) LAll in simp)
    moreover have "cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
      using Cons.prems(2) iG(1) by (simp add: typing_all_const)
    ultimately show ?thesis using X by (simp add: typing_all_const)
  qed
qed simp

end

lemma loose_bvar_lift_preI:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> \<not> loose_bvar (lift_pre p G0) k \<Longrightarrow> \<not> loose_bvar X (k + ilength (ptys p)) \<Longrightarrow>
    \<not> loose_bvar (lift_pre p X) k"
proof (induction p arbitrary: k)
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons show ?thesis by auto
  next
    case (LAll c a T)
    with Cons.prems have "\<not> loose_bvar (lift_pre p G0) (k + 1)" "\<not> loose_bvar X (k + 1 + ilength (ptys p))"
      by (auto simp: ac_simps)
    from Cons.IH[OF _ this] Cons.prems(1) LAll show ?thesis by auto
  qed
qed simp


context pure_sig
begin

lemma incr_tvar_propT [simp]: "incr_tvar inc propT = propT"
  by (simp add: propT_def)

lemma pushes_of_nat: "j < length Ts \<Longrightarrow> pushes e Ts (of_nat j) = Ts ! (length Ts - 1 - j)"
  using pushes_nth[of "of_nat j" e Ts]
  by (simp add: ilength_eq integer_of_nat_eq_of_nat rev_nth integer_reps)

lemma cinst_tinc: "cinst \<rho> \<Longrightarrow> cinst (tinc inc \<rho>)"
  unfolding cinst_def wsinst_def cert_inst_def tinc_def by (simp add: split_beta)

lemma typings_Frees: "\<forall>(F, T)\<in>set Fs. cert_typ alg ar T \<Longrightarrow> e \<tturnstile> map (\<lambda>(F, T). Free F T) Fs : map snd Fs"
  by (induction Fs) auto

lemma closed_Frees: "\<forall>f\<in>set (map (\<lambda>(F, T). Free F T) Fs). closed f"
  by (auto simp: closed_def)

lemma gsubst_lsubst:
  assumes \<sigma>: "gsubst \<sigma>" and \<rho>: "cert_inst \<rho>" and Ts: "\<forall>T\<in>set Ts. cert_typ alg ar T"
    and c: "\<forall>f\<in>set fs. closed f" and t: "\<And>e. e \<tturnstile> fs : map (tsubst \<rho>) Ts"
  shows "gsubst (lsubst inc \<rho> Ts \<sigma> fs)"
proof -
  have "closed (lsubst inc \<rho> Ts \<sigma> fs xi U) \<and> (cert_typ alg ar U \<longrightarrow> (\<exists>e. e \<turnstile> lsubst inc \<rho> Ts \<sigma> fs xi U : U))"
    for xi U
  proof -
    obtain x i where xi: "xi = (x, i)" by (cases xi)
    let ?c = "\<sigma> (x, i + inc) (map (tsubst \<rho>) Ts \<Rrightarrow> U)"
    have "closed ?c" using gsubstD(2)[OF \<sigma>] by (rule closed_substD)
    then have "closed (?c \<degree>\<degree> fs)" using c by (auto simp: closed_def loose_bvar_apps)
    moreover have "e \<turnstile> ?c \<degree>\<degree> fs : U" if "cert_typ alg ar U" for e
    proof (rule list_app_typeI[OF _ t])
      have "cert_typ alg ar (map (tsubst \<rho>) Ts \<Rrightarrow> U)"
        using Ts that \<rho> by (auto simp: cert_typ_funs cert_typ_tsubst)
      then show "e \<turnstile> ?c : map (tsubst \<rho>) Ts \<Rrightarrow> U" by (rule wt_subst_typing[OF gsubstD(1)[OF \<sigma>]])
    qed
    ultimately show ?thesis by (auto simp: lsubst_def xi)
  qed
  then show ?thesis by (simp add: gsubst_def wt_subst_def closed_subst_def)
qed

lemma typing_incr_idx0:
  assumes "e \<turnstile> X : T" "closed X" "\<forall>U\<in>set Ts. cert_typ alg ar U"
  shows "pushes e' Ts \<turnstile> incr_idx Ts inc 0 X : incr_tvar inc T"
proof (rule typing_incr_idx[OF assms(1)])
  show "pushes e' Ts (0 + of_nat j) = Ts ! (length Ts - 1 - j)" if "j < length Ts" for j
    using pushes_of_nat[OF that] by simp
qed (use assms(2,3) in \<open>simp_all add: closed_def\<close>)

lemma closed_incr_idx0:
  "closed X \<Longrightarrow> \<not> loose_bvar (incr_idx Ts inc 0 X) (ilength Ts)"
  using loose_bvar_incr_idx[of X 0 Ts inc] by (simp add: closed_def)

lemma wtp_lift_pre_incr:
  assumes sp: "lsplit G = (p, G0)" and G: "wtp G" and X: "wtp X"
  shows "wtp (lift_pre p (incr_idx (ptys p) inc 0 X))"
proof (rule wtpI)
  note pok = lsplit_ok[OF sp]
  let ?e = "\<lambda>_::integer. propT"
  have tG: "?e \<turnstile> lift_pre p G0 : propT" using wtpD(2)[OF G] pok by simp
  note tp = typing_lift_pre[OF conjunct1[OF conjunct2[OF pok]] tG]
  have "pushes ?e (ptys p) \<turnstile> incr_idx (ptys p) inc 0 X : incr_tvar inc propT"
    by (rule typing_incr_idx0[OF wtpD(2)[OF X] wtpD(1)[OF X]]) (use tp in simp)
  then show "?e \<turnstile> lift_pre p (incr_idx (ptys p) inc 0 X) : propT"
    by (intro typing_lift_preI[OF conjunct1[OF conjunct2[OF pok]] tG]) simp
  have "\<not> loose_bvar (lift_pre p G0) 0" using wtpD(1)[OF G] pok by (simp add: closed_def)
  from loose_bvar_lift_preI[OF conjunct1[OF conjunct2[OF pok]] this] closed_incr_idx0[OF wtpD(1)[OF X]]
  show "closed (lift_pre p (incr_idx (ptys p) inc 0 X))" by (simp add: closed_def)
qed

lemma typing_list_implies_imp: "e \<turnstile> list_implies As B : propT \<Longrightarrow> As \<noteq> [] \<Longrightarrow> cert_typ alg ar imp_type"
  by (cases As) (simp_all add: typing_implies)

lemma wtp_list_implies:
  "wtp (list_implies As B) \<Longrightarrow> wtp (list_implies As' B') \<longleftrightarrow> (\<forall>A\<in>set As'. wtp A) \<and> wtp B'"
  if "length As' = length As"
proof -
  have *: "wtp (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. wtp A) \<and> wtp B \<and> (As \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type)"
    for As B
  proof
    assume w: "wtp (list_implies As B)"
    from typing_list_impliesD[OF wtpD(2)[OF w]] wtpD(1)[OF w] typing_list_implies_imp[OF wtpD(2)[OF w]]
    show "(\<forall>A\<in>set As. wtp A) \<and> wtp B \<and> (As \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type)"
      by (auto simp: closed_def loose_bvar_list_implies wtp_def dest: typing_list_impliesD)
  next
    assume w: "(\<forall>A\<in>set As. wtp A) \<and> wtp B \<and> (As \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type)"
    show "wtp (list_implies As B)"
      by (rule wtpI[where e = "\<lambda>_. propT"]) (use w in \<open>auto simp: closed_def loose_bvar_list_implies wtp_def intro!: typing_list_impliesI\<close>)
  qed
  show "wtp (list_implies As B) \<Longrightarrow> ?thesis" using *[of As B] *[of As' B'] that by auto
qed

end

context pure_model
begin

lemma good_fval:
  assumes g: "good \<eta> \<xi>" and us: "list_all2 (\<lambda>(F, T) u. u \<in>\<^sub>u tsem \<eta> T) Fs us"
  shows "good \<eta> (fval \<xi> Fs us)"
proof -
  have "u \<in>\<^sub>u tsem \<eta> T" if "map_of (zip Fs us) (F, T) = Some u" for F T u
  proof -
    from map_of_SomeD[OF that] obtain n where n: "n < length Fs" "n < length us" "Fs ! n = (F, T)" "us ! n = u"
      by (auto simp: set_zip)
    from list_all2_nthD[OF us n(1)] n show ?thesis by simp
  qed
  with g show ?thesis by (auto simp: good_def good_v_def fval_def split: option.splits)
qed

end


context pure_sig
begin

text \<open>
  The lifted term applied to the fresh parameters \<open>fs\<close> \<open>\<beta>\<close>-reduces to the corresponding
  instance of the original term:
\<close>

lemma lift_beta:
  assumes \<sigma>: "gsubst \<sigma>" and \<rho>: "cert_inst \<rho>" and Ts: "\<forall>T\<in>set (ptys p). cert_typ alg ar T"
    and Fs: "map snd Fs = map (tsubst \<rho>) (ptys p)" and cF: "\<forall>(F, T)\<in>set Fs. cert_typ alg ar T"
    and X: "closed X" "e \<turnstile> X : T"
  shows "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 X)) \<degree>\<degree> map (\<lambda>(F, T). Free F T) Fs \<rightarrow>\<^sub>\<beta>\<^sup>*
      ap (tinc inc \<rho>) (lsubst inc \<rho> (ptys p) \<sigma> (map (\<lambda>(F, T). Free F T) Fs)) X \<and>
    wt (ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 X)) \<degree>\<degree> map (\<lambda>(F, T). Free F T) Fs)"
proof
  let ?fs = "map (\<lambda>(F, T). Free F T) Fs"
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (lparams p)"
  let ?t = "ap \<rho> \<sigma> (incr_idx (ptys p) inc 0 X)"
  have a: "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 X)) = abs_list ?bs ?t"
    by (simp add: abs_pre_abs_list ap_abs_list)
  have lF: "length Fs = length (ptys p)" using arg_cong[OF Fs, of length] by simp
  have lb: "length ?bs = length ?fs" using lF by (simp add: lparams_length)
  have "ilength ?bs = ilength (ptys p)" using lb lF by (simp add: ilength_eq)
  then have nl: "\<not> loose_bvar ?t (ilength ?bs)"
    using closed_incr_idx0[OF X(1), of "ptys p" inc] \<sigma> ilength_nonneg[of "ptys p"] by simp
  have "abs_list ?bs ?t \<degree>\<degree> ?fs \<rightarrow>\<^sub>\<beta>\<^sup>* bfree 0 ?fs ?t"
    by (rule abs_list_apps_beta[OF lb closed_Frees nl])
  moreover have "bfree 0 ?fs ?t = ap (tinc inc \<rho>) (lsubst inc \<rho> (ptys p) \<sigma> ?fs) X"
    by (rule bfree_ap_incr_idx[OF gsubstD(2)[OF \<sigma>]]) (use X(1) lF in \<open>simp_all add: closed_def\<close>)
  ultimately show "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 X)) \<degree>\<degree> ?fs \<rightarrow>\<^sub>\<beta>\<^sup>*
      ap (tinc inc \<rho>) (lsubst inc \<rho> (ptys p) \<sigma> ?fs) X" using a by simp
  let ?e = "\<lambda>_::integer. propT"
  have ms: "map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) = map (tsubst \<rho>) (map snd bs)" for bs :: "(name \<times> ptyp) list"
    by (induction bs) auto
  have "pushes ?e (ptys p) \<turnstile> incr_idx (ptys p) inc 0 X : incr_tvar inc T"
    by (rule typing_incr_idx0[OF X(2,1) Ts])
  then have "ienv \<rho> (pushes ?e (ptys p)) \<turnstile> ?t : tsubst \<rho> (incr_tvar inc T)"
    by (rule typing_ap_inst[OF _ \<rho> gsubstD(1)[OF \<sigma>]])
  then have "pushes (ienv \<rho> ?e) (map snd ?bs) \<turnstile> ?t : tsubst \<rho> (incr_tvar inc T)"
  proof -
    have ip: "ienv \<rho> (pushes e Us) = pushes (ienv \<rho> e) (map (tsubst \<rho>) Us)" for e Us
      by (induction Us arbitrary: e) (simp_all add: tsubst_shift)
    show "ienv \<rho> (pushes ?e (ptys p)) \<turnstile> ?t : tsubst \<rho> (incr_tvar inc T) \<Longrightarrow> ?thesis"
      unfolding ip using ms[of "lparams p"] by simp
  qed
  moreover have "\<forall>U\<in>snd ` set ?bs. cert_typ alg ar U"
  proof -
    have "snd ` set ?bs = tsubst \<rho> ` set (ptys p)" using ms[of "lparams p"] by (metis map_snd_lparams set_map)
    then show ?thesis using Ts \<rho> by (auto simp: cert_typ_tsubst)
  qed
  ultimately have "ienv \<rho> ?e \<turnstile> abs_list ?bs ?t : map snd ?bs \<Rrightarrow> tsubst \<rho> (incr_tvar inc T)"
    by (rule typing_abs_list)
  moreover have "map snd ?bs = map snd Fs" using ms[of "lparams p"] Fs by simp
  ultimately have "ienv \<rho> ?e \<turnstile> abs_list ?bs ?t \<degree>\<degree> ?fs : tsubst \<rho> (incr_tvar inc T)"
    using typings_Frees[OF cF] by (auto intro: list_app_typeI)
  then show "wt (ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 X)) \<degree>\<degree> ?fs)" using a by (auto simp: wt_def)
qed

end


subsection \<open>Validity of the lifted rule\<close>

context pure_model
begin

lemma inh_inst_tinc: "inh_inst \<rho> \<Longrightarrow> inh_inst (tinc inc \<rho>)"
  unfolding inh_inst_def tinc_def by (simp add: split_beta)

theorem lift_rule_valid:
  assumes v: "valid Sh hs (th_tpairs rule) (th_prop rule)"
    and w: "wt_thm rmax hs (th_tpairs rule) (th_prop rule)" and G: "wtp G"
  shows "valid Sh hs (th_tpairs (lift_rule G gmax rule)) (th_prop (lift_rule G gmax rule))"
proof -
  obtain p G0 where sp: "lsplit G = (p, G0)" by (cases "lsplit G")
  have pok: "G = lift_pre p G0" and ok: "\<forall>i\<in>set p. litem_ok i" using lsplit_ok[OF sp] by simp_all
  define inc where "inc = gmax + 1"
  define Ts where "Ts = ptys p"
  define f where "f = incr_idx Ts inc 0"
  define P where "P = th_prop rule"
  define tps where "tps = th_tpairs rule"
  define As where "As = strip_imp_prems P"
  define B where "B = strip_imp_concl P"
  have wP: "wtp P" using w by (simp add: wt_thm_def P_def)
  have PAB: "P = list_implies As B" unfolding As_def B_def by (rule list_implies_strip_imp[OF wtpD(2)[OF wP]])
  have la: "lift_all inc G = (\<lambda>X. lift_pre p (f X))"
    by (rule ext) (simp add: lift_all_lsplit[OF sp] incr_indexes_idx f_def Ts_def)
  have lP: "th_prop (lift_rule G gmax rule) = list_implies (map (\<lambda>X. lift_pre p (f X)) As) (lift_pre p (f B))"
    by (simp add: lift_rule_def Let_def la[unfolded inc_def] As_def B_def P_def)
  have lT: "th_tpairs (lift_rule G gmax rule) = map (\<lambda>(t, u). (abs_pre p (f t), abs_pre p (f u))) tps"
    by (simp add: lift_rule_def Let_def lift_abs_lsplit[OF sp] incr_indexes_idx f_def Ts_def inc_def tps_def)
  have wAB: "(\<forall>A\<in>set As. wtp A) \<and> wtp B" using wtp_list_implies[of As As B B] wP PAB by simp
  have wL: "wtp (lift_pre p (f X))" if "wtp X" for X
    unfolding f_def Ts_def by (rule wtp_lift_pre_incr[OF sp G that])
  have wLP: "wtp (th_prop (lift_rule G gmax rule))"
    unfolding lP using wtp_list_implies[of "map (\<lambda>X. lift_pre p (f X)) As" As B "lift_pre p (f B)"] wP PAB wAB wL
    by auto
  have tG: "(\<lambda>_. propT) \<turnstile> lift_pre p G0 : propT" using wtpD(2)[OF G] pok by simp
  have cTs: "\<forall>T\<in>set Ts. cert_typ alg ar T" using typing_lift_pre[OF ok tG] by (simp add: Ts_def)
  have hs0: "vars h = {} \<and> ttvars h = {}" if "h \<in> set hs" for h using w that by (simp add: wt_thm_def)
  have tps0: "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)" if "(t, u) \<in> set tps" for t u
    using w that by (fastforce simp: wt_thm_def tps_def)
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs (lift_rule G gmax rule)) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    have core: "hb (vpushes bv0 us) (ap \<rho> \<sigma> (f B))"
      if us: "list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) Ts us"
        and hA: "\<forall>X\<in>set (map f As). hb (vpushes bv0 us) (ap \<rho> \<sigma> X)" for us
    proof -
      define N where "N = (\<Union>h\<in>set hs. fnames h) \<union> (\<Union>X\<in>set (B # As). fnames (ap \<rho> \<sigma> (f X)))"
      have "finite N" by (simp add: N_def)
      then obtain names where nm: "length names = length Ts" "distinct names" "set names \<inter> N = {}"
        by (rule fresh_name_list)
      define Fs where "Fs = zip names (map (tsubst \<rho>) Ts)"
      define fs where "fs = map (\<lambda>(F, T). Free F T) Fs"
      define \<rho>0 where "\<rho>0 = tinc inc \<rho>"
      define \<sigma>0 where "\<sigma>0 = lsubst inc \<rho> Ts \<sigma> fs"
      define \<xi>0 where "\<xi>0 = fval \<xi> Fs us"
      have lus: "length us = length Fs" using list_all2_lengthD[OF us] nm(1) by (simp add: Fs_def)
      have dF: "distinct Fs" using nm(2) by (simp add: Fs_def distinct_zipI1)
      have nF: "fst ` set Fs = set names" using nm(1) by (metis Fs_def length_map map_fst_zip set_map)
      have sF: "map snd Fs = map (tsubst \<rho>) Ts" using nm(1) by (simp add: Fs_def)
      have cF: "\<forall>(F, T)\<in>set Fs. cert_typ alg ar T"
        using cTs cinstD(2)[OF \<rho>] by (auto simp: Fs_def cert_typ_tsubst dest!: set_zip_rightD)
      have tfs: "e \<tturnstile> fs : map (tsubst \<rho>) Ts" for e using typings_Frees[OF cF] sF by (simp add: fs_def)
      have g0: "good \<eta> \<xi>0" unfolding \<xi>0_def
      proof (rule good_fval[OF g])
        show "list_all2 (\<lambda>(F, T) u. u \<in>\<^sub>u tsem \<eta> T) Fs us"
          using us nm(1) by (auto simp: Fs_def list_all2_conv_all_nth)
      qed
      interpret V0: pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>0
        by unfold_locales (rule g0)
      have \<rho>0: "cinst \<rho>0" by (simp add: \<rho>0_def cinst_tinc[OF \<rho>])
      have \<rho>0i: "inh_inst \<rho>0" by (simp add: \<rho>0_def inh_inst_tinc[OF \<rho>i])
      have \<sigma>0: "gsubst \<sigma>0" unfolding \<sigma>0_def
        by (rule gsubst_lsubst[OF \<sigma> cinstD(2)[OF \<rho>] cTs _ tfs]) (simp add: fs_def closed_Frees)
      have key: "hb (vpushes bv0 us) (ap \<rho> \<sigma> (f X)) \<longleftrightarrow> holds_at \<eta> \<xi>0 (ap \<rho>0 \<sigma>0 X)"
        if X: "X \<in> set (B # As)" for X
      proof -
        have wX: "wtp X" using X wAB by auto
        have e1: "ap \<rho>0 \<sigma>0 X = bfree 0 fs (ap \<rho> \<sigma> (f X))" unfolding \<rho>0_def \<sigma>0_def f_def
          by (rule bfree_ap_incr_idx[OF gsubstD(2)[OF \<sigma>], symmetric])
            (use wtpD(1)[OF wX] nm(1) in \<open>simp_all add: fs_def Fs_def closed_def\<close>)
        have iF: "ilength Fs = ilength Ts" using nm(1) by (simp add: Fs_def ilength_eq)
        have e2: "sem \<eta> \<xi>0 bv0 (bfree 0 fs (ap \<rho> \<sigma> (f X))) = sem \<eta> \<xi> (vpushes bv0 us) (ap \<rho> \<sigma> (f X))"
          unfolding \<xi>0_def fs_def
        proof (rule sem_bfree[OF dF lus])
          show "fnames (ap \<rho> \<sigma> (f X)) \<inter> fst ` set Fs = {}" using nm(3) X nF by (auto simp: N_def)
          show "\<not> loose_bvar (ap \<rho> \<sigma> (f X)) (0 + ilength Fs)"
            using closed_incr_idx0[OF wtpD(1)[OF wX], of Ts inc] \<sigma> ilength_nonneg[of Ts] iF by (simp add: f_def)
          show "vpushes bv0 us (0 + of_nat j) = us ! (length Fs - 1 - j)" if "j < length Fs" for j
            using vpushes_nth[of j us bv0] that lus by simp
        qed simp_all
        show ?thesis using e1 e2 by (simp add: holds_at_def)
      qed
      have "holds_at \<eta> \<xi>0 (ap \<rho>0 \<sigma>0 P)"
      proof (rule validD[OF v[folded P_def tps_def] sh g0 \<rho>0 \<rho>0i \<sigma>0])
        fix h assume h: "h \<in> set hs"
        have "fnames h \<inter> fst ` set Fs = {}" using nm(3) h nF by (auto simp: N_def)
        then show "holds_at \<eta> \<xi>0 (ap \<rho>0 \<sigma>0 h)"
          using hh[OF h] hs0[OF h] sem_fresh[of h Fs \<eta> \<xi> us bv0] by (simp add: ap_ground holds_at_def \<xi>0_def)
      next
        fix t u assume tu: "(t, u) \<in> set tps"
        obtain T where c: "closed t" "closed u" "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" using tps0[OF tu] by blast
        have "(abs_pre p (f t), abs_pre p (f u)) \<in> set (th_tpairs (lift_rule G gmax rule))"
          unfolding lT using tu by force
        note cv = sol[OF this]
        have bt: "ap \<rho> \<sigma> (abs_pre p (f X)) \<degree>\<degree> fs \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho>0 \<sigma>0 X \<and> wt (ap \<rho> \<sigma> (abs_pre p (f X)) \<degree>\<degree> fs)"
          if "closed X" "e \<turnstile> X : U" for X e U
          unfolding f_def \<rho>0_def \<sigma>0_def fs_def Ts_def
          using lift_beta[OF \<sigma> cinstD(2)[OF \<rho>] cTs[unfolded Ts_def] sF[unfolded Ts_def] cF that] by blast
        have 1: "ap \<rho> \<sigma> (abs_pre p (f t)) \<degree>\<degree> fs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>0 \<sigma>0 t"
          using bt[OF c(1,3)] by (blast intro: conv_beta_eta)
        have 2: "ap \<rho> \<sigma> (abs_pre p (f u)) \<degree>\<degree> fs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>0 \<sigma>0 u"
          using bt[OF c(2,4)] by (blast intro: conv_beta_eta)
        have 3: "ap \<rho> \<sigma> (abs_pre p (f t)) \<degree>\<degree> fs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (abs_pre p (f u)) \<degree>\<degree> fs"
          by (rule conv_apps) (use bt[OF c(1,3)] bt[OF c(2,4)] cv in \<open>simp_all add: list.rel_refl\<close>)
        show "ap \<rho>0 \<sigma>0 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>0 \<sigma>0 u" using conv_trans[OF conv_trans[OF conv_sym[OF 1] 3] 2] .
      qed
      then have h: "holds_at \<eta> \<xi>0 (list_implies (map (ap \<rho>0 \<sigma>0) As) (ap \<rho>0 \<sigma>0 B))"
        by (simp add: PAB ap_list_implies)
      have gt: "gterm (list_implies (map (ap \<rho>0 \<sigma>0) As) (ap \<rho>0 \<sigma>0 B)) propT"
        using gterm_ap_wtp[OF wP cinstD(2)[OF \<rho>0] \<sigma>0] by (simp add: PAB ap_list_implies)
      have "holds_at \<eta> \<xi>0 (ap \<rho>0 \<sigma>0 A)" if "A \<in> set As" for A using key[of A] that hA by auto
      then have "holds_at \<eta> \<xi>0 (ap \<rho>0 \<sigma>0 B)" using V0.holds_list_impliesD[OF gt h] by auto
      then show ?thesis using key[of B] by simp
    qed
    have "holds (list_implies (map (ap \<rho> \<sigma>) (map (\<lambda>X. lift_pre p (f X)) As)) (ap \<rho> \<sigma> (lift_pre p (f B))))"
    proof (rule holds_list_impliesI)
      show "gterm (list_implies (map (ap \<rho> \<sigma>) (map (\<lambda>X. lift_pre p (f X)) As)) (ap \<rho> \<sigma> (lift_pre p (f B)))) propT"
        using gterm_ap_wtp[OF wLP cinstD(2)[OF \<rho>] \<sigma>] by (simp add: lP ap_list_implies)
      assume hA: "\<And>A. A \<in> set (map (ap \<rho> \<sigma>) (map (\<lambda>X. lift_pre p (f X)) As)) \<Longrightarrow> holds A"
      have "hb bv0 (ap \<rho> \<sigma> (lift_pre p (f B)))"
      proof (rule hb_lift_pre_mp[OF cinstD(2)[OF \<rho>] \<sigma> ok _ _ bvals0, where Xs = "map f As"])
        show "\<forall>X\<in>set (map f As). (\<lambda>_. propT) \<turnstile> lift_pre p X : propT" using wL wAB by (auto intro: wtpD(2))
        show "(\<lambda>_. propT) \<turnstile> lift_pre p (f B) : propT" using wL wAB by (auto intro: wtpD(2))
        show "\<forall>X\<in>set (map f As). hb bv0 (ap \<rho> \<sigma> (lift_pre p X))" using hA by (auto simp: holds_hb)
        show "hb (vpushes bv0 us) (ap \<rho> \<sigma> (f B))"
          if "list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) (ptys p) us"
            "\<forall>X\<in>set (map f As). hb (vpushes bv0 us) (ap \<rho> \<sigma> X)" for us
          using core that by (simp add: Ts_def)
      qed
      then show "holds (ap \<rho> \<sigma> (lift_pre p (f B)))" by (simp add: holds_hb)
    qed
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (th_prop (lift_rule G gmax rule)))" by (simp add: lP ap_list_implies)
  qed
qed

end


subsection \<open>The shape of the lifted rule\<close>

context pure_sig
begin

lemma lift_rule_prop:
  assumes "lsplit G = (p, G0)"
  shows "th_prop (lift_rule G gmax rule) =
    list_implies (map (lift_pre p) (map (incr_idx (ptys p) (gmax + 1) 0) (strip_imp_prems (th_prop rule))))
      (lift_pre p (incr_idx (ptys p) (gmax + 1) 0 (strip_imp_concl (th_prop rule))))"
proof -
  have "lift_all (gmax + 1) G = (\<lambda>X. lift_pre p (incr_idx (ptys p) (gmax + 1) 0 X))"
    by (rule ext) (simp add: lift_all_lsplit[OF assms] incr_indexes_idx)
  then show ?thesis by (simp add: lift_rule_def Let_def comp_def)
qed

lemma lift_rule_tpairs:
  assumes "lsplit G = (p, G0)"
  shows "th_tpairs (lift_rule G gmax rule) =
    map (\<lambda>(t, u). (abs_pre p (incr_idx (ptys p) (gmax + 1) 0 t), abs_pre p (incr_idx (ptys p) (gmax + 1) 0 u)))
      (th_tpairs rule)"
  by (simp add: lift_rule_def Let_def lift_abs_lsplit[OF assms] incr_indexes_idx)

lemma lift_rule_maxidx: "th_maxidx (lift_rule G gmax rule) = th_maxidx rule + (gmax + 1)"
  by (simp add: lift_rule_def Let_def)

theorem lift_rule_lifted_over:
  assumes nn: "\<forall>v\<in>vars (th_prop rule). 0 \<le> snd (fst v)"
  shows "lifted_over smax G (th_prop (lift_rule G smax rule)) (nprems_of rule)"
proof -
  obtain p G0 where ls: "lsplit G = (p, G0)" by (cases "lsplit G")
  let ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  let ?f = "incr_idx (ptys p) (smax + 1) 0"
  have v: "\<forall>v\<in>vars X. 0 \<le> snd (fst v)" if "X \<in> insert ?B (set ?As)" for X
    using that strip_imp_vars(1)[of _ "th_prop rule"] strip_imp_vars(2)[of "th_prop rule"] nn by blast
  have "\<forall>v\<in>vars (?f X). smax < snd (fst v)" if "X \<in> insert ?B (set ?As)" for X
    using v[OF that] by (auto simp: vars_incr_idx)
  then have "\<forall>X\<in>insert (?f ?B) (set (map ?f ?As)). \<forall>v\<in>vars X. smax < snd (fst v)" by auto
  moreover have "nprems_of rule = ilength (map ?f ?As)"
    by (simp add: nprems_of_def count_prems_strip_imp ilength_eq)
  ultimately show ?thesis unfolding lifted_over_def using ls lift_rule_prop[OF ls] by blast
qed

end


subsection \<open>Well-typedness of the lifted rule\<close>

context pure_sig
begin

lemma ttvars_combound: "ttvars (combound u n k) = ttvars u"
  by (induction u n k rule: combound.induct) simp_all

lemma tvars_incr_tvar: "((a, i), S) \<in> tvars (incr_tvar inc T) \<longleftrightarrow> ((a, i - inc), S) \<in> tvars T"
  by (induction inc T rule: incr_tvar.induct) (auto simp: algebra_simps)

lemma tvars_funs: "tvars (foldr fun_type Ts U) = (\<Union>V\<in>set Ts. tvars V) \<union> tvars U"
  by (induction Ts) auto

lemma ttvars_incr_idx:
  "((a, i), S) \<in> ttvars (incr_idx Ts inc lev t) \<Longrightarrow>
    (\<exists>U\<in>set Ts. ((a, i), S) \<in> tvars U) \<or> ((a, i - inc), S) \<in> ttvars t"
  by (induction Ts inc lev t rule: incr_idx.induct) (auto simp: ttvars_combound tvars_funs tvars_incr_tvar)

lemma typs_lift_pre_sub: "typs (lift_pre p X) \<subseteq> typs (lift_pre p Y) \<union> typs X"
  by (induction p rule: ptys.induct) auto

lemma ptys_typs: "set (ptys p) \<subseteq> typs (lift_pre p Y)"
  by (induction p rule: ptys.induct) auto

lemma ttvars_lift_pre_sub: "ttvars (lift_pre p X) \<subseteq> ttvars (lift_pre p Y) \<union> ttvars X"
  using typs_lift_pre_sub[of p X Y] by (auto simp: ttvars_def)

lemma ibelow_lift_pre_incr:
  assumes G: "ibelow s (lift_pre p G0)" and X: "ibelow r X" and s: "s \<le> m" and r: "r + inc \<le> m"
  shows "ibelow m (lift_pre p (incr_idx (ptys p) inc 0 X))"
  unfolding ibelow_def
proof safe
  fix x i T assume v: "((x, i), T) \<in> vars (lift_pre p (incr_idx (ptys p) inc 0 X))"
  then consider "((x, i), T) \<in> pvars p" | "((x, i), T) \<in> vars (incr_idx (ptys p) inc 0 X)"
    by (auto simp: vars_lift_pre)
  then show "snd (fst ((x, i), T)) \<le> m"
  proof cases
    case 1
    then have "((x, i), T) \<in> vars (lift_pre p G0)" by (simp add: vars_lift_pre)
    with G s show ?thesis by (force simp: ibelow_def)
  next
    case 2
    then obtain j U where "((x, j), U) \<in> vars X" "i = j + inc" by (auto simp: vars_incr_idx)
    with X r show ?thesis by (force simp: ibelow_def)
  qed
next
  fix a i S assume v: "((a, i), S) \<in> ttvars (lift_pre p (incr_idx (ptys p) inc 0 X))"
  have tG: "\<forall>q\<in>ttvars (lift_pre p G0). snd (fst q) \<le> m" using G s by (force simp: ibelow_def)
  have "(\<Union>U\<in>set (ptys p). tvars U) \<subseteq> ttvars (lift_pre p G0)"
    using ptys_typs[of p G0] by (auto simp: ttvars_def)
  with v ttvars_lift_pre_sub[of p "incr_idx (ptys p) inc 0 X" G0] ttvars_incr_idx[of a i S "ptys p" inc 0 X]
  consider "((a, i), S) \<in> ttvars (lift_pre p G0)" | "((a, i - inc), S) \<in> ttvars X"
    by blast
  then show "snd (fst ((a, i), S)) \<le> m"
  proof cases
    case 1
    with tG show ?thesis by force
  next
    case 2
    with X r show ?thesis by (force simp: ibelow_def)
  qed
qed

lemma ibelow_abs_pre: "ibelow m (lift_pre p X) \<Longrightarrow> ibelow m (abs_pre p X)"
  using ttvars_abs_pre[of p X] by (auto simp: ibelow_def vars_lift_pre)

lemma loose_bvar_abs_pre: "\<not> loose_bvar X (k + ilength (ptys p)) \<Longrightarrow> \<not> loose_bvar (abs_pre p X) k"
  by (induction p arbitrary: k rule: ptys.induct) (auto simp: ac_simps)

lemma wtp_lift_rule_prop:
  assumes P: "wtp (th_prop rule)" and G: "wtp G"
  shows "wtp (th_prop (lift_rule G gmax rule))"
proof -
  obtain p G0 where sp: "lsplit G = (p, G0)" by (cases "lsplit G")
  let ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  let ?f = "incr_idx (ptys p) (gmax + 1) 0"
  have PAB: "th_prop rule = list_implies ?As ?B" by (rule list_implies_strip_imp[OF wtpD(2)[OF P]])
  have wAB: "(\<forall>A\<in>set ?As. wtp A) \<and> wtp ?B" using wtp_list_implies[of ?As ?As ?B ?B] P PAB by simp
  show ?thesis unfolding lift_rule_prop[OF sp]
    using wtp_list_implies[of "map (lift_pre p) (map ?f ?As)" ?As ?B "lift_pre p (?f ?B)"] P PAB wAB
      wtp_lift_pre_incr[OF sp G] by auto
qed

theorem lift_rule_wt_thm:
  assumes w: "wt_thm (th_maxidx rule) hs (th_tpairs rule) (th_prop rule)" and G: "wtp G" "ibelow smax G"
    and m: "-1 \<le> th_maxidx rule"
  shows "wt_thm (th_maxidx (lift_rule G smax rule)) hs (th_tpairs (lift_rule G smax rule))
    (th_prop (lift_rule G smax rule))"
proof -
  obtain p G0 where sp: "lsplit G = (p, G0)" by (cases "lsplit G")
  have pok: "G = lift_pre p G0" and ok: "\<forall>i\<in>set p. litem_ok i" using lsplit_ok[OF sp] by simp_all
  let ?r = "th_maxidx rule" and ?inc = "smax + 1"
  let ?m = "?r + ?inc" and ?f = "incr_idx (ptys p) (smax + 1) 0"
  let ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  have wP: "wtp (th_prop rule)" "ibelow ?r (th_prop rule)" using w by (simp_all add: wt_thm_def)
  have PAB: "th_prop rule = list_implies ?As ?B" by (rule list_implies_strip_imp[OF wtpD(2)[OF wP(1)]])
  have ib: "ibelow ?m (lift_pre p (?f X))" if "ibelow ?r X" for X
    by (rule ibelow_lift_pre_incr[OF G(2)[unfolded pok] that]) (use m in simp_all)
  have "(\<forall>X\<in>set ?As. ibelow ?r X) \<and> ibelow ?r ?B" using wP(2) PAB ibelow_list_implies by metis
  then have "ibelow ?m (th_prop (lift_rule G smax rule))"
    unfolding lift_rule_prop[OF sp] ibelow_list_implies using ib by auto
  moreover have "wtp (th_prop (lift_rule G smax rule))" by (rule wtp_lift_rule_prop[OF wP(1) G(1)])
  moreover have tG: "(\<lambda>_. propT) \<turnstile> lift_pre p G0 : propT" using wtpD(2)[OF G(1)] pok by simp
  then have cTs: "\<forall>T\<in>set (ptys p). cert_typ alg ar T" using typing_lift_pre[OF ok] by blast
  have pair: "closed (abs_pre p (?f t)) \<and> ibelow ?m (abs_pre p (?f t)) \<and> (\<forall>e. e \<turnstile> abs_pre p (?f t) : ptys p \<Rrightarrow> incr_tvar ?inc T)"
    if "closed t" "ibelow ?r t" "\<And>e. e \<turnstile> t : T" for t T
  proof (intro conjI allI)
    show "closed (abs_pre p (?f t))"
      using loose_bvar_abs_pre[of "?f t" 0 p] closed_incr_idx0[OF that(1)] by (simp add: closed_def)
    show "ibelow ?m (abs_pre p (?f t))" by (rule ibelow_abs_pre[OF ib[OF that(2)]])
    fix e
    have "pushes e (map snd (lparams p)) \<turnstile> ?f t : incr_tvar ?inc T"
      using typing_incr_idx0[OF that(3) that(1) cTs] by simp
    moreover have "\<forall>T\<in>snd ` set (lparams p). cert_typ alg ar T" using cTs by (metis map_snd_lparams set_map)
    ultimately have "e \<turnstile> abs_list (lparams p) (?f t) : map snd (lparams p) \<Rrightarrow> incr_tvar ?inc T"
      by (rule typing_abs_list)
    then show "e \<turnstile> abs_pre p (?f t) : ptys p \<Rrightarrow> incr_tvar ?inc T" by (simp add: abs_pre_abs_list)
  qed
  have "\<forall>(t, u)\<in>set (th_tpairs (lift_rule G smax rule)). closed t \<and> closed u \<and> ibelow ?m t \<and> ibelow ?m u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  proof (clarsimp simp: lift_rule_tpairs[OF sp])
    fix t u assume "(t, u) \<in> set (th_tpairs rule)"
    then obtain T where tu: "closed t" "closed u" "ibelow ?r t" "ibelow ?r u" "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T"
      using w by (fastforce simp: wt_thm_def)
    from pair[OF tu(1,3,5)] pair[OF tu(2,4,6)]
    show "closed (abs_pre p (?f t)) \<and> closed (abs_pre p (?f u)) \<and> ibelow ?m (abs_pre p (?f t)) \<and>
        ibelow ?m (abs_pre p (?f u)) \<and> (\<exists>T. \<forall>e. e \<turnstile> abs_pre p (?f t) : T \<and> e \<turnstile> abs_pre p (?f u) : T)"
      by blast
  qed
  ultimately show ?thesis using w by (simp add: wt_thm_def lift_rule_maxidx)
qed

end


subsection \<open>Variables of the lifted rule\<close>

context pure_sig
begin

lemma lift_rule_vars:
  assumes sp: "lsplit G = (p, G0)"
    and v: "((x, i), T) \<in> vars_thm (th_tpairs (lift_rule G gmax rule)) (th_prop (lift_rule G gmax rule))"
  shows "((x, i), T) \<in> vars G \<or> (\<exists>T0. ((x, i - (gmax + 1)), T0) \<in> vars_thm (th_tpairs rule) (th_prop rule) \<and>
    T = foldr fun_type (ptys p) (incr_tvar (gmax + 1) T0))"
proof -
  let ?f = "incr_idx (ptys p) (gmax + 1) 0"
  have G: "pvars p \<subseteq> vars G" using lsplit_ok[OF sp] by (auto simp: vars_lift_pre)
  have fX: "((x, i), T) \<in> vars (?f X) \<Longrightarrow> \<exists>T0. ((x, i - (gmax + 1)), T0) \<in> vars X \<and>
      T = foldr fun_type (ptys p) (incr_tvar (gmax + 1) T0)" for X
    by (auto simp: vars_incr_idx)
  from v consider "((x, i), T) \<in> pvars p"
    | X where "X \<in> insert (strip_imp_concl (th_prop rule)) (set (strip_imp_prems (th_prop rule)))"
        "((x, i), T) \<in> vars (?f X)"
    | t u where "(t, u) \<in> set (th_tpairs rule)" "((x, i), T) \<in> vars (?f t) \<or> ((x, i), T) \<in> vars (?f u)"
    unfolding vars_thm_def lift_rule_prop[OF sp] lift_rule_tpairs[OF sp]
    by (auto simp: vars_list_implies vars_lift_pre split: if_splits)
  then show ?thesis
  proof cases
    case 1
    with G show ?thesis by blast
  next
    case (2 X)
    have "vars X \<subseteq> vars (th_prop rule)" using 2(1) strip_imp_vars by blast
    with fX[OF 2(2)] show ?thesis by (auto simp: vars_thm_def)
  next
    case (3 t u)
    with fX show ?thesis by (fastforce simp: vars_thm_def)
  qed
qed

lemma lift_rule_tvars:
  assumes sp: "lsplit G = (p, G0)" and P: "e \<turnstile> th_prop rule : propT"
    and v: "((a, i), S) \<in> tvars_thm (th_tpairs (lift_rule G gmax rule)) (th_prop (lift_rule G gmax rule))"
  shows "((a, i), S) \<in> ttvars G \<or> ((a, i - (gmax + 1)), S) \<in> tvars_thm (th_tpairs rule) (th_prop rule)"
proof -
  let ?f = "incr_idx (ptys p) (gmax + 1) 0"
  let ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  have pG: "G = lift_pre p G0" using lsplit_ok[OF sp] by simp
  have Ts: "(\<Union>U\<in>set (ptys p). tvars U) \<subseteq> ttvars G" using ptys_typs[of p G0] pG by (auto simp: ttvars_def)
  have fX: "((a, i), S) \<in> ttvars (lift_pre p (?f X)) \<Longrightarrow>
      ((a, i), S) \<in> ttvars G \<or> ((a, i - (gmax + 1)), S) \<in> ttvars X" for X
    using ttvars_lift_pre_sub[of p "?f X" G0] ttvars_incr_idx[of a i S "ptys p" "gmax + 1" 0 X] Ts pG by blast
  have PAB: "th_prop rule = list_implies ?As ?B" by (rule list_implies_strip_imp[OF P])
  have sub: "ttvars X \<subseteq> ttvars (th_prop rule)" if "X \<in> insert ?B (set ?As)" for X
    using that ttvars_list_implies(1)[of X ?As ?B] ttvars_list_implies(2)[of ?B ?As] PAB by auto
  have h1: "ttvars (list_implies (map (lift_pre p) (map ?f ?As)) (lift_pre p (?f ?B))) \<subseteq>
      (\<Union>X\<in>insert ?B (set ?As). ttvars (lift_pre p (?f X)))"
    using ttvars_list_implies_sub[of "map (lift_pre p) (map ?f ?As)" "lift_pre p (?f ?B)"] by auto
  have h2: "ttvars (abs_pre p (?f t)) \<union> ttvars (abs_pre p (?f u)) \<subseteq>
      ttvars (lift_pre p (?f t)) \<union> ttvars (lift_pre p (?f u))" for t u
    using ttvars_abs_pre[of p "?f t"] ttvars_abs_pre[of p "?f u"] by blast
  from v have "((a, i), S) \<in> ttvars (list_implies (map (lift_pre p) (map ?f ?As)) (lift_pre p (?f ?B))) \<or>
      (\<exists>(t, u)\<in>set (th_tpairs rule). ((a, i), S) \<in> ttvars (abs_pre p (?f t)) \<union> ttvars (abs_pre p (?f u)))"
    unfolding tvars_thm_def lift_rule_prop[OF sp] lift_rule_tpairs[OF sp] by (simp add: case_prod_beta)
  then show ?thesis
  proof
    assume "((a, i), S) \<in> ttvars (list_implies (map (lift_pre p) (map ?f ?As)) (lift_pre p (?f ?B)))"
    with h1 obtain X where X: "X \<in> insert ?B (set ?As)" "((a, i), S) \<in> ttvars (lift_pre p (?f X))" by blast
    from fX[OF X(2)] sub[OF X(1)] show ?thesis unfolding tvars_thm_def by blast
  next
    assume "\<exists>(t, u)\<in>set (th_tpairs rule). ((a, i), S) \<in> ttvars (abs_pre p (?f t)) \<union> ttvars (abs_pre p (?f u))"
    then obtain t u where tu: "(t, u) \<in> set (th_tpairs rule)"
      "((a, i), S) \<in> ttvars (abs_pre p (?f t)) \<union> ttvars (abs_pre p (?f u))" by blast
    with h2 have "((a, i), S) \<in> ttvars (lift_pre p (?f t)) \<union> ttvars (lift_pre p (?f u))" by blast
    then have "((a, i), S) \<in> ttvars G \<or> ((a, i - (gmax + 1)), S) \<in> ttvars t \<union> ttvars u"
      using fX[of t] fX[of u] by blast
    with tu(1) show ?thesis unfolding tvars_thm_def by blast
  qed
qed

end

end
