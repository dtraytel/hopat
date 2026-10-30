section \<open>A Semantics of Pure's Meta-Logic\<close>

theory Bicompose_Holds
  imports Bicompose_Syntax
begin

text \<open>
  A theorem of Pure denotes its ground instances. We interpret the meta-logic on the de Bruijn
  terms \<^typ>\<open>dB\<close> of session \<open>Nipkow_Grobauer_Pattern\<close>, into which Pure terms are translated
  (\<^const>\<open>tr\<close>): a predicate \<open>holds\<close> on closed propositions that respects \<open>\<beta>\<eta>\<close>-conversion,
  interprets \<open>\<Longrightarrow>\<close> as implication and \<open>\<And>x :: T\<close> as quantification over a set \<open>inhab T\<close> of
  closed terms. These are the only properties of the meta-logic that the composition of theorems
  depends on.
\<close>


subsection \<open>Simultaneous substitution of closed terms for loose bound variables\<close>

text \<open>\<open>substs k vs t\<close> replaces the loose bound variable \<open>k + i\<close> of \<open>t\<close> by \<open>vs ! i\<close>.\<close>

context csig
begin

primrec substs :: "nat \<Rightarrow> dB list \<Rightarrow> dB \<Rightarrow> dB" where
  "substs k vs (BVar i) =
    (if i < k then BVar i else if i - k < length vs then vs ! (i - k) else BVar (i - length vs))"
| "substs k vs (dB.Var n) = dB.Var n"
| "substs k vs (s \<degree> t) = substs k vs s \<degree> substs k vs t"
| "substs k vs (dB.Abs t) = dB.Abs (substs (Suc k) vs t)"

abbreviation closed :: "dB \<Rightarrow> bool" where
  "closed t \<equiv> no_loose_bound t 0"

lemma substs_Nil[simp]: "substs k [] t = t"
  by (induction t arbitrary: k) auto

lemma substs_closed: "no_loose_bound t k \<Longrightarrow> substs k vs t = t"
  by (induction t arbitrary: k) auto

lemma closed_no_loose_bound: "closed t \<Longrightarrow> no_loose_bound t k"
  by (rule no_loose_bound_mono) auto

lemma substs_closed0[simp]: "closed t \<Longrightarrow> substs k vs t = t"
  by (simp add: substs_closed closed_no_loose_bound)

lemma lift_nlb: "no_loose_bound t k \<Longrightarrow> lift t k = t"
  by (induction t arbitrary: k) auto

lemma lift_closed0[simp]: "closed t \<Longrightarrow> lift t k = t"
  by (simp add: lift_nlb closed_no_loose_bound)

lemma subst_closed0[simp]: "closed t \<Longrightarrow> t[v/k] = t"
  by (rule loose_bound_subst) auto

lemma substs_Cons:
  "closed v \<Longrightarrow> substs k (v # vs) t = substs k vs (t[v/k])"
proof (induction t arbitrary: k)
  case (BVar i)
  then show ?case by (auto simp: subst_BVar nth_Cons')
qed auto

lemma subst_substs: "closed v \<Longrightarrow> t[v/k] = substs k [v] t"
  using substs_Cons[of v k "[]" t] by simp

lemma substs_append:
  "\<forall>u\<in>set us. closed u \<Longrightarrow> substs k (us @ vs) t = substs k vs (substs k us t)"
proof (induction us arbitrary: t)
  case (Cons u us)
  then show ?case by (simp add: substs_Cons)
qed simp

lemma substs_liftn: "substs k (us @ vs) (liftn (length us) t k) = substs k vs t"
  by (induction t arbitrary: k) (auto simp: nth_append simp del: liftn_lift)

lemma no_loose_bound_substs:
  "\<forall>v\<in>set vs. closed v \<Longrightarrow> no_loose_bound t (k + length vs) \<Longrightarrow> no_loose_bound (substs k vs t) k"
proof (induction t arbitrary: k)
  case (BVar i)
  then show ?case by (auto simp: closed_no_loose_bound)
next
  case (Abs t)
  from Abs.IH[of "Suc k"] Abs.prems show ?case by simp
qed auto

lemma mk_subst_substs:
  "closed_on UNIV \<sigma> \<Longrightarrow> mk_subst \<sigma> (substs k vs t) = substs k (map (mk_subst \<sigma>) vs) (mk_subst \<sigma> t)"
proof (induction t arbitrary: k)
  case (Var n)
  then show ?case by (simp add: closed_onD)
qed auto

lemma closed_nth: "\<forall>v\<in>set vs. closed v \<Longrightarrow> j < length vs \<Longrightarrow> closed (vs ! j)"
  by auto

lemma substs_subst:
  "closed u \<Longrightarrow> \<forall>v\<in>set vs. closed v \<Longrightarrow> (substs (Suc k) vs t)[u/k] = substs k vs (t[u/k])"
proof (induction t arbitrary: k)
  case (BVar i)
  then show ?case by (auto simp: subst_BVar closed_nth)
qed auto

lemma Abs_m_Suc': "Abs_m (Suc m) t = Abs_m m (dB.Abs t)"
  by (induction m) simp_all

text \<open>\<open>\<beta>\<close>-reduction of an abstraction over \<open>n\<close> variables, applied to \<open>n\<close> closed terms.\<close>

lemma Abs_m_Suc: "Abs_m (Suc m) t = dB.Abs (Abs_m m t)"
  by simp

lemma Abs_m_subst: "closed v \<Longrightarrow> (Abs_m m t)[v/k] = Abs_m m (t[v/k + m])"
  by (induction m arbitrary: k) (simp_all add: add.commute)

lemma Abs_m_apps_substs:
  "\<forall>u\<in>set us. closed u \<Longrightarrow> length us = m \<Longrightarrow> Abs_m m t \<degree>\<degree> us \<rightarrow>\<^sub>\<beta>\<^sup>* substs 0 (rev us) t"
proof (induction us arbitrary: m t rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc u us)
  then obtain m' where m: "m = Suc m'" "length us = m'" by auto
  have "Abs_m m t = Abs_m m' (dB.Abs t)"
    by (simp only: m(1) Abs_m_Suc')
  then have "Abs_m m t \<degree>\<degree> (us @ [u]) = (Abs_m m' (dB.Abs t) \<degree>\<degree> us) \<degree> u" by simp
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* substs 0 (rev us) (dB.Abs t) \<degree> u"
    using snoc.IH[of m' "dB.Abs t"] snoc.prems m(2) by (auto intro: rtrancl_beta_AppL)
  also have "\<dots> = dB.Abs (substs 1 (rev us) t) \<degree> u" by simp
  also have "\<dots> \<rightarrow>\<^sub>\<beta> (substs 1 (rev us) t)[u/0]" by (rule beta.beta)
  also have "(substs 1 (rev us) t)[u/0] = substs 0 (rev (us @ [u])) t"
    using snoc.prems(1) by (simp add: substs_subst substs_Cons)
  finally show ?case by simp
qed



subsection \<open>The meta-connectives\<close>

definition imp_type :: ptyp where
  "imp_type = propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT"

definition all_type :: "ptyp \<Rightarrow> ptyp" where
  "all_type T = (T \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT"

lemma implies_imp_type: "implies = Const STR ''Pure.imp'' imp_type"
  by (simp add: implies_def imp_type_def)

lemma all_const_all_type: "all_const T = Const STR ''Pure.all'' (all_type T)"
  by (simp add: all_const_def all_type_def)

lemma tsubst_propT[simp]: "tsubst \<rho> propT = propT"
  by (simp add: propT_def)

lemma tsubst_imp_type[simp]: "tsubst \<rho> imp_type = imp_type"
  by (simp add: imp_type_def)

lemma tsubst_all_type[simp]: "tsubst \<rho> (all_type T) = all_type (tsubst \<rho> T)"
  by (simp add: all_type_def)

definition imp_code :: nat where
  "imp_code = code (AConst STR ''Pure.imp'' imp_type)"

definition all_code :: "ptyp \<Rightarrow> nat" where
  "all_code T = code (AConst STR ''Pure.all'' (all_type T))"

abbreviation dIMP :: "dB \<Rightarrow> dB \<Rightarrow> dB" where
  "dIMP A B \<equiv> dB.Var imp_code \<degree> A \<degree> B"

abbreviation dALL :: "ptyp \<Rightarrow> dB \<Rightarrow> dB" where
  "dALL T P \<equiv> dB.Var (all_code T) \<degree> dB.Abs P"

text \<open>
  The constants \<open>Pure.imp\<close> and \<open>Pure.all\<close> occur with their declared types, and the binder of
  a quantification has the type of the quantifier (\<open>cok\<close>). This holds for the propositions
  of all theorems, since the kernel certifies the types of constants.
\<close>

fun cok :: "pterm \<Rightarrow> bool" where
  "cok (Const c U $ Abs a T b) \<longleftrightarrow>
    (c = STR ''Pure.imp'' \<longrightarrow> U = imp_type) \<and> (c = STR ''Pure.all'' \<longrightarrow> U = all_type T) \<and> cok b"
| "cok (Const c U) \<longleftrightarrow>
    (c = STR ''Pure.imp'' \<longrightarrow> U = imp_type) \<and> (c = STR ''Pure.all'' \<longrightarrow> (\<exists>T. U = all_type T))"
| "cok (s $ t) \<longleftrightarrow> cok s \<and> cok t"
| "cok (Abs a T b) \<longleftrightarrow> cok b"
| "cok _ \<longleftrightarrow> True"

lemma cok_imp:
  "cok (Const c U $ A $ B) \<Longrightarrow> c = STR ''Pure.imp'' \<Longrightarrow> U = imp_type \<and> cok A \<and> cok B"
  by (cases A) auto

lemma cok_all:
  "cok (Const c U $ Abs a T b) \<Longrightarrow> c = STR ''Pure.all'' \<Longrightarrow> U = all_type T \<and> cok b"
  by simp

lemma cok_dest_imp: "cok t \<Longrightarrow> dest_imp t = Some (A, B) \<Longrightarrow> t = implies $ A $ B \<and> cok A \<and> cok B"
  by (auto simp: dest_imp_Some implies_imp_type dest: cok_imp)

lemma cok_dest_all: "cok t \<Longrightarrow> dest_all t = Some (a, T, b) \<Longrightarrow> t = all_const T $ Abs a T b \<and> cok b"
  by (auto simp: dest_all_Some all_const_all_type)

lemma cok_implies[simp]: "cok (implies $ A $ B) \<longleftrightarrow> cok A \<and> cok B"
  by (cases A) (auto simp: implies_imp_type all_type_def imp_type_def)

lemma cok_all_const[simp]: "cok (all_const T $ Abs a T b) \<longleftrightarrow> cok b"
  by (simp add: all_const_all_type)

lemma implies_simps[simp]:
  "proper implies" "no_loose_bound (tr implies) k" "cok (implies $ X) \<longleftrightarrow> cok X"
  by (cases X; simp add: implies_imp_type imp_type_def all_type_def)+

lemma all_const_simps[simp]:
  "proper (all_const T)" "no_loose_bound (tr (all_const T)) k"
  by (simp_all add: all_const_def)

lemma cok_list_implies[simp]: "cok (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. cok A) \<and> cok B"
  by (induction As) (auto simp del: cok.simps)

lemma cok_list_forall[simp]: "cok (list_forall vs B) \<longleftrightarrow> cok B"
  by (induction vs B rule: list_forall.induct) auto

lemma cok_inst: "cok t \<Longrightarrow> cok (inst \<rho> t)"
proof (induction t rule: cok.induct)
  case (1 c U a T b)
  then show ?case by auto
next
  case (2 c U)
  then show ?case by (auto simp: all_type_def imp_type_def propT_def)
next
  case ("3_1" v va t)
  then show ?case by (cases v) auto
qed auto


subsection \<open>Ground instances\<close>

text \<open>The instance of a term under a type instantiation \<open>\<rho>\<close> and a substitution \<open>\<sigma>\<close>.\<close>

definition sm :: "tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> pterm \<Rightarrow> dB" where
  "sm \<rho> \<sigma> t = mk_subst \<sigma> (tr (inst \<rho> t))"

lemma sm_App[simp]: "sm \<rho> \<sigma> (s $ t) = sm \<rho> \<sigma> s \<degree> sm \<rho> \<sigma> t"
  by (simp add: sm_def)

lemma sm_Abs[simp]: "sm \<rho> \<sigma> (Abs a T t) = dB.Abs (sm \<rho> \<sigma> t)"
  by (simp add: sm_def)

lemma sm_Bound[simp]: "sm \<rho> \<sigma> (Bound i) = BVar (nat_of_integer i)"
  by (simp add: sm_def)

lemma sm_implies[simp]: "rigid_subst \<sigma> \<Longrightarrow> sm \<rho> \<sigma> implies = dB.Var imp_code"
  by (simp add: sm_def implies_imp_type imp_code_def rigid_substD)

lemma sm_all_const[simp]: "rigid_subst \<sigma> \<Longrightarrow> sm \<rho> \<sigma> (all_const T) = dB.Var (all_code (tsubst \<rho> T))"
  by (simp add: sm_def all_const_all_type all_code_def rigid_substD)

lemma sm_list_implies:
  "rigid_subst \<sigma> \<Longrightarrow> sm \<rho> \<sigma> (list_implies As B) = foldr dIMP (map (sm \<rho> \<sigma>) As) (sm \<rho> \<sigma> B)"
  by (induction As) auto

lemma sm_imp_cok: "rigid_subst \<sigma> \<Longrightarrow> cok t \<Longrightarrow> dest_imp t = Some (A, B) \<Longrightarrow>
    sm \<rho> \<sigma> t = dIMP (sm \<rho> \<sigma> A) (sm \<rho> \<sigma> B)"
  by (drule cok_dest_imp) auto

lemma sm_all_cok: "rigid_subst \<sigma> \<Longrightarrow> cok t \<Longrightarrow> dest_all t = Some (a, T, b) \<Longrightarrow>
    sm \<rho> \<sigma> t = dALL (tsubst \<rho> T) (sm \<rho> \<sigma> b)"
  by (drule cok_dest_all) auto

lemma mk_subst_liftn: "closed_on UNIV \<sigma> \<Longrightarrow> mk_subst \<sigma> (liftn n t k) = liftn n (mk_subst \<sigma> t) k"
proof (induction t arbitrary: k)
  case (Var x)
  have "no_loose_bound (\<sigma> x) k" using Var closed_onD[OF Var, of x] closed_no_loose_bound by blast
  then show ?case by (simp add: liftn_closed)
qed (auto simp del: liftn_lift)

lemma sm_incr_boundvars:
  "closed_on UNIV \<sigma> \<Longrightarrow> proper t \<Longrightarrow> 0 \<le> j \<Longrightarrow>
    sm \<rho> \<sigma> (incr_boundvars j t) = liftn (nat_of_integer j) (sm \<rho> \<sigma> t) 0"
  by (auto simp: sm_def incr_boundvars_def inst_incr_bv tr_incr_bv mk_subst_liftn simp del: liftn_lift)

lemma no_loose_bound_mk_subst:
  "closed_on UNIV \<sigma> \<Longrightarrow> no_loose_bound (mk_subst \<sigma> t) k \<longleftrightarrow> no_loose_bound t k"
proof (induction t arbitrary: k)
  case (Var x)
  then show ?case using closed_onD[OF Var, of x] closed_no_loose_bound by simp
qed auto

lemma no_loose_bound_sm:
  "closed_on UNIV \<sigma> \<Longrightarrow> no_loose_bound (sm \<rho> \<sigma> t) k \<longleftrightarrow> no_loose_bound (tr t) k"
  by (simp add: sm_def no_loose_bound_mk_subst)


lemma strip_params_imp: "dest_imp A = Some (H, B) \<Longrightarrow> strip_params A = strip_params B"
  by (subst strip_params.simps) simp

lemma strip_params_all: "dest_imp A = None \<Longrightarrow> dest_all A = Some (a, T, b) \<Longrightarrow>
    strip_params A = (a, T) # strip_params b"
  by (subst strip_params.simps) simp

lemma strip_params_other: "dest_imp A = None \<Longrightarrow> dest_all A = None \<Longrightarrow> strip_params A = []"
  by (subst strip_params.simps) simp

lemma dest_imp_all: "dest_imp A = Some (H, B) \<Longrightarrow> dest_all A = None"
  by (auto simp: dest_imp_Some)

lemma cok_incr_bv: "cok (incr_bv inc lev t) \<longleftrightarrow> cok t"
proof (induction t arbitrary: lev)
  case (App s t)
  then show ?case
    by (cases s; cases t) (auto simp: incr_boundvars_def)
qed auto

lemma cok_incr_boundvars[simp]: "cok (incr_boundvars j t) \<longleftrightarrow> cok t"
  by (simp add: incr_boundvars_def cok_incr_bv)

lemma proper_incr_boundvars: "proper t \<Longrightarrow> 0 \<le> j \<Longrightarrow> proper (incr_boundvars j t)"
  by (simp add: incr_boundvars_def proper_incr_bv)

lemma tr_incr_boundvars: "proper t \<Longrightarrow> 0 \<le> j \<Longrightarrow> tr (incr_boundvars j t) = liftn (nat_of_integer j) (tr t) 0"
  by (auto simp: incr_boundvars_def tr_incr_bv simp del: liftn_lift)

lemma ilength_Cons: "ilength (x # xs) = ilength xs + 1"
  by simp

lemma remove_params_wf:
  assumes "ok (remove_params j n A) A'" "ilength (strip_params A) = j" "proper A" "cok A"
    "no_loose_bound (tr A) m"
  shows "proper A' \<and> cok A' \<and> no_loose_bound (tr A') (nat_of_integer j + m)"
  using assms
proof (induction j n A arbitrary: A' m rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  have j0: "0 \<le> j" using "1.prems"(2) ilength_nonneg by metis
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp "1.prems" show ?thesis by (subst (asm) remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      from cok_dest_imp[OF "1.prems"(4) HB] have A: "A = implies $ H $ B" "cok H" "cok B" by auto
      have spB: "ilength (strip_params B) = j" using "1.prems"(2) HB by (simp add: strip_params_imp)
      have wB: "proper B" "no_loose_bound (tr B) m" "proper H" "no_loose_bound (tr H) m"
        using "1.prems"(3,5) A(1) by simp_all
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this spB wB(1) A(3) wB(2)] show ?thesis by simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        from "1.IH"(3)[OF False HB refl n1 B' spB wB(1) A(3) wB(2)]
        have "proper B' \<and> cok B' \<and> no_loose_bound (tr B') (nat_of_integer j + m)" by simp
        moreover have "no_loose_bound (tr (incr_boundvars j H)) (nat_of_integer j + m)"
          using no_loose_bound_liftn[OF wB(4), of "nat_of_integer j"] wB(3) j0
          by (simp add: tr_incr_boundvars add.commute)
        ultimately show ?thesis
          using A' A(2) wB(3) j0 by (simp add: proper_incr_boundvars)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        from cok_dest_all[OF "1.prems"(4) aTb] have A: "A = all_const T $ Abs a T b" "cok b" by auto
        with rp False None aTb have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        have sp: "ilength (strip_params b) = j - 1"
          using "1.prems"(2) None aTb by (simp add: strip_params_all)
        have "0 \<le> j - 1" using sp ilength_nonneg by metis
        then have j1: "1 \<le> j" by simp
        have "no_loose_bound (tr b) (Suc m)" using "1.prems"(5) A(1) by simp
        from "1.IH"(1)[OF False None aTb refl refl r sp _ A(2) this] "1.prems"(3) A(1)
        have "proper A' \<and> cok A' \<and> no_loose_bound (tr A') (nat_of_integer (j - 1) + Suc m)" by simp
        moreover have "nat_of_integer (j - 1) + Suc m = nat_of_integer j + m"
          using j1 by (simp add: integer_reps)
        ultimately show ?thesis by (simp only:)
      next
        case None': None
        with rp False None "1.prems" show ?thesis
          by (subst (asm) remove_params.simps) (auto split: if_splits simp: strip_params_other)
      qed
    qed
  qed
qed

lemma substs_Suc_subst:
  "closed u \<Longrightarrow> \<forall>v\<in>set vs. closed v \<Longrightarrow> (substs (Suc 0) vs t)[u/0] = substs 0 (u # vs) t"
  by (simp add: substs_subst substs_Cons)

lemma no_loose_bound_list_forall:
  "no_loose_bound (tr (list_forall ps X)) k \<longleftrightarrow> no_loose_bound (tr X) (length ps + k)"
  by (induction ps X arbitrary: k rule: list_forall.induct) (auto simp: all_const_def)

lemma no_loose_bound_list_implies:
  "no_loose_bound (tr (list_implies As B)) k \<longleftrightarrow> (\<forall>A\<in>set As. no_loose_bound (tr A) k) \<and> no_loose_bound (tr B) k"
  by (induction As) (auto simp: implies_def)

lemma proper_list_forall[simp]: "proper (list_forall ps X) \<longleftrightarrow> proper X"
  by (induction ps X rule: list_forall.induct) (auto simp: all_const_def)

lemma proper_list_implies[simp]: "proper (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. proper A) \<and> proper B"
  by (induction As) (auto simp: implies_def)

lemma substs_foldr_dIMP: "substs k vs (foldr dIMP As B) = foldr dIMP (map (substs k vs) As) (substs k vs B)"
  by (induction As) auto

lemma list_forall_append: "list_forall (xs @ ys) t = list_forall xs (list_forall ys t)"
  by (induction xs t rule: list_forall.induct) auto

text \<open>The structure found by \<^const>\<open>assum_problems\<close>.\<close>

lemma strip_assums_all_struct:
  "strip_assums_all params A = (params', A') \<Longrightarrow> cok A \<Longrightarrow>
    \<exists>ps. params' = ps @ params \<and> A = list_forall (rev ps) A' \<and> cok A'"
proof (induction params A rule: strip_assums_all.induct)
  case (1 params t)
  show ?case
  proof (cases "dest_all t")
    case (Some aTb)
    then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
    from cok_dest_all[OF "1.prems"(2) aTb] have t: "t = all_const T $ Abs a T b" "cok b" by auto
    from "1.prems"(1) aTb have "strip_assums_all ((a, T) # params) b = (params', A')"
      by (subst (asm) strip_assums_all.simps) simp
    from "1.IH"[OF aTb refl refl this t(2)] obtain ps where
      "params' = ps @ (a, T) # params" "b = list_forall (rev ps) A'" "cok A'" by blast
    with t(1) show ?thesis
      by (intro exI[of _ "ps @ [(a, T)]"]) (simp add: list_forall_append)
  next
    case None
    with "1.prems" show ?thesis by (subst (asm) strip_assums_all.simps) auto
  qed
qed

lemma strip_assums_imp_struct:
  "strip_assums_imp k Hs B = (Hs', B') \<Longrightarrow> cok B \<Longrightarrow>
    \<exists>qs. Hs' = rev qs @ Hs \<and> B = list_implies qs B' \<and> (\<forall>H\<in>set qs. cok H) \<and> cok B'"
proof (induction k Hs B rule: strip_assums_imp.induct)
  case (1 k Hs B)
  show ?case
  proof (cases "k = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_assums_imp.simps) auto
  next
    case False
    show ?thesis
    proof (cases "dest_imp B")
      case (Some HB)
      then obtain H B1 where HB: "dest_imp B = Some (H, B1)" by (cases HB) auto
      from cok_dest_imp[OF "1.prems"(2) HB] have B: "B = implies $ H $ B1" "cok H" "cok B1" by auto
      from "1.prems"(1) False HB have "strip_assums_imp (k - 1) (H # Hs) B1 = (Hs', B')"
        by (subst (asm) strip_assums_imp.simps) simp
      from "1.IH"[OF False HB refl this B(3)] obtain qs where
        "Hs' = rev qs @ H # Hs" "B1 = list_implies qs B'" "\<forall>H\<in>set qs. cok H" "cok B'" by blast
      with B show ?thesis by (intro exI[of _ "H # qs"]) simp
    next
      case None
      with "1.prems" False show ?thesis by (subst (asm) strip_assums_imp.simps) auto
    qed
  qed
qed

lemma assum_problems_struct:
  assumes "assum_problems k A = (params, asms, concl)" "cok A"
  shows "A = list_forall (rev params) (list_implies asms concl) \<and> (\<forall>H\<in>set asms. cok H) \<and> cok concl"
proof -
  obtain ps A' where a: "strip_assums_all [] A = (ps, A')" by (cases "strip_assums_all [] A")
  obtain Hs B where b: "strip_assums_imp k [] A' = (Hs, B)" by (cases "strip_assums_imp k [] A'")
  from assms(1) a b have p: "params = ps" "asms = rev Hs" "concl = B"
    by (simp_all add: assum_problems_def)
  from strip_assums_all_struct[OF a assms(2)] obtain ps' where
    "ps = ps'" "A = list_forall (rev ps') A'" "cok A'" by auto
  moreover from strip_assums_imp_struct[OF b \<open>cok A'\<close>] obtain qs where
    "Hs = rev qs" "A' = list_implies qs B" "\<forall>H\<in>set qs. cok H" "cok B" by auto
  ultimately show ?thesis using p by simp
qed

subsection \<open>The semantics\<close>

end

locale pure_sem = csig +
  fixes holds :: "dB \<Rightarrow> bool" and inhab :: "ptyp \<Rightarrow> dB \<Rightarrow> bool"
  assumes inhab_closed: "inhab T t \<Longrightarrow> closed t"
    and holds_equiv: "closed s \<Longrightarrow> closed t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> holds s \<Longrightarrow> holds t"
    and holds_imp: "closed A \<Longrightarrow> closed B \<Longrightarrow> holds (dIMP A B) \<longleftrightarrow> (holds A \<longrightarrow> holds B)"
    and holds_all: "no_loose_bound P 1 \<Longrightarrow> holds (dALL T P) \<longleftrightarrow> (\<forall>t. inhab T t \<longrightarrow> holds (P[t/0]))"
begin

lemma holds_foldr_dIMP:
  "\<forall>A\<in>set As. closed A \<Longrightarrow> closed B \<Longrightarrow>
    holds (foldr dIMP As B) \<longleftrightarrow> ((\<forall>A\<in>set As. holds A) \<longrightarrow> holds B)"
proof (induction As)
  case (Cons A As)
  have "closed (foldr dIMP As B)"
    using Cons.prems by (induction As) auto
  with Cons show ?case by (auto simp: holds_imp)
qed simp

text \<open>
  The semantics of the spine of a proposition, for values \<open>vs\<close> of its loose bound variables
  and values \<open>us\<close> of its parameters (outermost first). The \<open>n\<close>-th assumption is ignored.
\<close>

function asem :: "tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> integer \<Rightarrow> dB list \<Rightarrow> dB list \<Rightarrow> pterm \<Rightarrow> bool" where
  "asem \<rho> \<sigma> n vs us A =
    (case dest_imp A of
      Some (H, B) \<Rightarrow> ((n \<noteq> 1 \<longrightarrow> holds (substs 0 vs (sm \<rho> \<sigma> H))) \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B)
    | None \<Rightarrow>
      (case dest_all A of
        Some (a, T, b) \<Rightarrow> (case us of [] \<Rightarrow> True | u # us' \<Rightarrow> asem \<rho> \<sigma> n (u # vs) us' b)
      | None \<Rightarrow> holds (substs 0 vs (sm \<rho> \<sigma> A))))"
  by auto
termination by (relation "measure (\<lambda>(_, _, _, _, _, A). size A)") (auto dest: dest_size)

declare asem.simps[simp del]

abbreviation ptyped :: "tinst \<Rightarrow> binders \<Rightarrow> dB list \<Rightarrow> bool" where
  "ptyped \<rho> ps us \<equiv> list_all2 (\<lambda>(a, T) u. inhab (tsubst \<rho> T) u) ps us"

lemma ptyped_closed: "ptyped \<rho> ps us \<Longrightarrow> \<forall>u\<in>set us. closed u"
  by (induction rule: list_all2_induct) (auto dest: inhab_closed)

text \<open>A proposition holds iff its spine semantics holds for all values of its parameters.\<close>

lemma holds_asem:
  assumes "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "cok A" "\<forall>v\<in>set vs. closed v"
    "no_loose_bound (tr A) (length vs)" "n \<le> 0"
  shows "holds (substs 0 vs (sm \<rho> \<sigma> A)) \<longleftrightarrow>
    (\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A)"
  using assms(3-6)
proof (induction A arbitrary: n vs rule: measure_induct_rule[of size])
  case (less A)
  note cl = no_loose_bound_substs[OF less.prems(2), of _ 0, simplified]
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    from cok_dest_imp[OF less.prems(1) HB] have A: "A = implies $ H $ B" and ok: "cok H" "cok B"
      by auto
    have nH: "no_loose_bound (tr H) (length vs)" and nB: "no_loose_bound (tr B) (length vs)"
      using less.prems(3) A by simp_all
    have cH: "closed (substs 0 vs (sm \<rho> \<sigma> H))" and cB: "closed (substs 0 vs (sm \<rho> \<sigma> B))"
      using cl assms(2) nH nB by (simp_all add: no_loose_bound_sm)
    have IH: "holds (substs 0 vs (sm \<rho> \<sigma> B)) \<longleftrightarrow>
        (\<forall>us. ptyped \<rho> (strip_params B) us \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B)"
      using less.IH[of B vs "n - 1"] A ok less.prems by simp
    have "holds (substs 0 vs (sm \<rho> \<sigma> A)) \<longleftrightarrow>
        (holds (substs 0 vs (sm \<rho> \<sigma> H)) \<longrightarrow> holds (substs 0 vs (sm \<rho> \<sigma> B)))"
      using A assms(1) cH cB by (simp add: holds_imp)
    also have "\<dots> \<longleftrightarrow> (\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A)"
      using IH less.prems(4) HB by (subst asem.simps) (auto simp: strip_params_imp)
    finally show ?thesis .
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
      from cok_dest_all[OF less.prems(1) aTb] have A: "A = all_const T $ Abs a T b" and ok: "cok b"
        by auto
      have nb: "no_loose_bound (tr b) (Suc (length vs))" using less.prems(3) A by simp
      have IH: "\<And>u. closed u \<Longrightarrow> holds (substs 0 (u # vs) (sm \<rho> \<sigma> b)) \<longleftrightarrow>
          (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b)"
        using less.IH[of b "u # vs" n for u] A ok less.prems nb by simp
      have sb: "substs 0 vs (sm \<rho> \<sigma> A) = dALL (tsubst \<rho> T) (substs 1 vs (sm \<rho> \<sigma> b))"
        using A assms(1) by simp
      have nb': "no_loose_bound (substs 1 vs (sm \<rho> \<sigma> b)) 1"
        using no_loose_bound_substs[OF less.prems(2), of "sm \<rho> \<sigma> b" 1] nb assms(2)
        by (simp add: no_loose_bound_sm)
      have eq: "(substs (Suc 0) vs (sm \<rho> \<sigma> b))[u/0] = substs 0 (u # vs) (sm \<rho> \<sigma> b)" if "closed u" for u
        using that less.prems(2) by (simp add: substs_subst substs_Cons)
      have "holds (substs 0 vs (sm \<rho> \<sigma> A)) \<longleftrightarrow>
          (\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow> holds (substs 0 (u # vs) (sm \<rho> \<sigma> b)))"
      proof -
        have h: "holds ((substs (Suc 0) vs (sm \<rho> \<sigma> b))[u/0]) \<longleftrightarrow> holds (substs 0 (u # vs) (sm \<rho> \<sigma> b))"
          if "inhab (tsubst \<rho> T) u" for u
          using eq[OF inhab_closed[OF that]] by simp
        have "holds (substs 0 vs (sm \<rho> \<sigma> A)) \<longleftrightarrow>
            (\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow> holds ((substs 1 vs (sm \<rho> \<sigma> b))[u/0]))"
          unfolding sb by (rule holds_all[OF nb'])
        also have "\<dots> \<longleftrightarrow> (\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow> holds (substs 0 (u # vs) (sm \<rho> \<sigma> b)))"
          unfolding One_nat_def by (intro iff_allI imp_cong[OF refl]) (rule h)
        finally show ?thesis .
      qed
      also have "\<dots> \<longleftrightarrow> (\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow>
          (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b))"
        using IH inhab_closed by blast
      also have "\<dots> \<longleftrightarrow> (\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A)"
      proof -
        have as: "asem \<rho> \<sigma> n vs (u # us) A = asem \<rho> \<sigma> n (u # vs) us b" for u us
          using None aTb by (subst asem.simps) simp
        have sp: "strip_params A = (a, T) # strip_params b"
          using None aTb by (rule strip_params_all)
        show ?thesis
        proof
          assume H: "\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow>
            (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b)"
          show "\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A"
          proof (intro allI impI)
            fix us assume "ptyped \<rho> (strip_params A) us"
            then obtain u us' where "us = u # us'" "inhab (tsubst \<rho> T) u" "ptyped \<rho> (strip_params b) us'"
              by (auto simp: sp list_all2_Cons1)
            with H as show "asem \<rho> \<sigma> n vs us A" by simp
          qed
        next
          assume H: "\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A"
          show "\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow>
            (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b)"
          proof (intro allI impI)
            fix u us assume "inhab (tsubst \<rho> T) u" "ptyped \<rho> (strip_params b) us"
            then have "ptyped \<rho> (strip_params A) (u # us)" by (simp add: sp)
            with H as show "asem \<rho> \<sigma> n (u # vs) us b" by metis
          qed
        qed
      qed
      finally show ?thesis .
    next
      case None': None
      with None show ?thesis by (subst asem.simps) (simp add: strip_params_other)
    qed
  qed
qed

text \<open>Ignoring an assumption weakens the spine semantics.\<close>

lemma asem_mono: "asem \<rho> \<sigma> n vs us A \<Longrightarrow> m \<le> 0 \<Longrightarrow> asem \<rho> \<sigma> m vs us A"
proof (induction \<rho> \<sigma> n vs us A arbitrary: m rule: asem.induct)
  case (1 \<rho> \<sigma> n vs us A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    from "1.prems"(1) HB have a: "(n \<noteq> 1 \<longrightarrow> holds (substs 0 vs (sm \<rho> \<sigma> H))) \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B"
      by (subst (asm) asem.simps) simp
    have "asem \<rho> \<sigma> (m - 1) vs us B" if hH: "holds (substs 0 vs (sm \<rho> \<sigma> H))"
    proof -
      have ant: "n \<noteq> 1 \<longrightarrow> holds (substs 0 vs (sm \<rho> \<sigma> H))" using hH by simp
      with a have "asem \<rho> \<sigma> (n - 1) vs us B" by simp
      from "1.IH"(2)[OF HB refl ant this, of "m - 1"] "1.prems"(2) show ?thesis by simp
    qed
    with HB "1.prems"(2) show ?thesis by (subst asem.simps) simp
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
      show ?thesis
      proof (cases us)
        case Nil
        with None aTb show ?thesis by (subst asem.simps) simp
      next
        case (Cons u us')
        from "1.prems"(1) None aTb Cons have "asem \<rho> \<sigma> n (u # vs) us' b"
          by (subst (asm) asem.simps) simp
        from "1.IH"(1)[OF None aTb refl refl Cons this "1.prems"(2)] None aTb Cons
        show ?thesis by (subst asem.simps) simp
      qed
    next
      case None': None
      with None "1.prems"(1) show ?thesis by (subst (asm) asem.simps, subst asem.simps) simp
    qed
  qed
qed

text \<open>
  Removing the parameters of a proposition (\<^const>\<open>remove_params\<close>): if the result holds for
  values \<open>us\<close> of the parameters, the spine semantics holds for them, ignoring the \<open>n\<close>-th
  assumption.
\<close>

lemma remove_params_asem:
  assumes "ok (remove_params j n A) A'" "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "cok A" "proper A"
    "\<forall>v\<in>set vs. closed v" "\<forall>u\<in>set us. closed u" "no_loose_bound (tr A) (length vs)"
    "ilength (strip_params A) = j" "length us = length (strip_params A)"
    "holds (substs 0 (rev us @ vs) (sm \<rho> \<sigma> A'))"
  shows "asem \<rho> \<sigma> n vs us A"
  using assms
proof (induction j n A arbitrary: A' vs us rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  have j0: "0 \<le> j" using "1.prems"(9) ilength_nonneg by metis
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp have A': "A' = A" by (subst (asm) remove_params.simps) simp
    have sp: "strip_params A = []"
      using True "1.prems"(9) nat_of_integer_ilength[of "strip_params A"] by simp
    with "1.prems"(10) have us: "us = []" by simp
    from holds_asem[OF "1.prems"(2,3,4,6,8), of n \<rho>] True "1.prems"(11) A' us sp
    show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      from cok_dest_imp[OF "1.prems"(4) HB] have A: "A = implies $ H $ B" "cok H" "cok B" by auto
      have spB: "strip_params A = strip_params B" using HB by (rule strip_params_imp)
      have wB: "proper B" "no_loose_bound (tr B) (length vs)" "proper H"
        "no_loose_bound (tr H) (length vs)"
        using "1.prems"(5,8) A(1) by simp_all
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have r: "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True r "1.prems"(2,3) A(3) wB(1) "1.prems"(6,7) wB(2)]
          "1.prems"(9-11) spB
        have "asem \<rho> \<sigma> (n - 1) vs us B" by simp
        with HB True show ?thesis by (subst asem.simps) simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        have nj: "nat_of_integer j = length us"
          using "1.prems"(9,10) nat_of_integer_ilength[of "strip_params A"] by simp
        have wB': "no_loose_bound (tr B') (nat_of_integer j + length vs)"
          using remove_params_wf[OF B' _ wB(1) A(3) wB(2)] "1.prems"(9) spB by simp
        have ci: "\<forall>u\<in>set (rev us @ vs). closed u" using "1.prems"(6,7) by auto
        have eqH: "substs 0 (rev us @ vs) (sm \<rho> \<sigma> (incr_boundvars j H)) = substs 0 vs (sm \<rho> \<sigma> H)"
          using substs_liftn[of 0 "rev us" vs "sm \<rho> \<sigma> H"] sm_incr_boundvars[OF "1.prems"(3) wB(3) j0] nj
          by simp
        have cH: "closed (substs 0 vs (sm \<rho> \<sigma> H))"
          using no_loose_bound_substs[OF "1.prems"(6), of _ 0] wB(4) "1.prems"(3)
          by (simp add: no_loose_bound_sm)
        have cB: "closed (substs 0 (rev us @ vs) (sm \<rho> \<sigma> B'))"
          using no_loose_bound_substs[OF ci, of _ 0] wB' "1.prems"(3) nj
          by (simp add: no_loose_bound_sm add.commute)
        from "1.prems"(11) A' "1.prems"(2) eqH cH cB
        have h: "holds (substs 0 vs (sm \<rho> \<sigma> H)) \<longrightarrow> holds (substs 0 (rev us @ vs) (sm \<rho> \<sigma> B'))"
          by (simp add: holds_imp)
        have "holds (substs 0 vs (sm \<rho> \<sigma> H)) \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B"
          using "1.IH"(3)[OF False HB refl n1 B' "1.prems"(2,3) A(3) wB(1) "1.prems"(6,7) wB(2)]
            "1.prems"(9,10) spB h by simp
        with HB n1 show ?thesis by (subst asem.simps) simp
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        from cok_dest_all[OF "1.prems"(4) aTb] have A: "A = all_const T $ Abs a T b" "cok b" by auto
        with rp False None aTb have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        have sp: "strip_params A = (a, T) # strip_params b" using None aTb by (rule strip_params_all)
        with "1.prems"(10) obtain u us' where us: "us = u # us'" by (cases us) auto
        have "asem \<rho> \<sigma> n (u # vs) us' b"
        proof (rule "1.IH"(1)[OF False None aTb refl refl r "1.prems"(2,3) A(2)])
          show "proper b" "no_loose_bound (tr b) (length (u # vs))"
            using "1.prems"(5,8) A(1) by simp_all
          show "\<forall>v\<in>set (u # vs). closed v" "\<forall>u\<in>set us'. closed u"
            using "1.prems"(6,7) us by simp_all
          show "ilength (strip_params b) = j - 1" "length us' = length (strip_params b)"
            using "1.prems"(9,10) sp us by simp_all
          show "holds (substs 0 (rev us' @ u # vs) (sm \<rho> \<sigma> A'))"
            using "1.prems"(11) us by simp
        qed
        with None aTb us show ?thesis by (subst asem.simps) simp
      next
        case None': None
        with rp False None "1.prems"(9) show ?thesis
          by (subst (asm) remove_params.simps) (auto split: if_splits simp: strip_params_other)
      qed
    qed
  qed
qed

lemma ptyped_snd: "map snd ps = map snd qs \<Longrightarrow> ptyped \<rho> ps us \<longleftrightarrow> ptyped \<rho> qs us"
proof (induction ps arbitrary: qs us)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then obtain q qs' where "qs = q # qs'" "snd p = snd q" "map snd ps = map snd qs'" by (cases qs) auto
  with Cons.IH show ?case by (cases us) (auto split: prod.splits)
qed

lemma holds_list_forall:
  assumes "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "\<forall>v\<in>set vs. closed v"
    "no_loose_bound (tr X) (length ps + length vs)"
  shows "holds (substs 0 vs (sm \<rho> \<sigma> (list_forall ps X))) \<longleftrightarrow>
    (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ vs) (sm \<rho> \<sigma> X)))"
  using assms(3,4)
proof (induction ps arbitrary: vs)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain a T where p: "p = (a, T)" by (cases p)
  let ?Y = "sm \<rho> \<sigma> (list_forall ps X)"
  have nY: "no_loose_bound (substs 1 vs ?Y) 1"
    using no_loose_bound_substs[OF Cons.prems(1), of ?Y 1] Cons.prems(2) assms(2)
    by (simp add: no_loose_bound_sm no_loose_bound_list_forall add.commute)
  have "holds (substs 0 vs (sm \<rho> \<sigma> (list_forall (p # ps) X))) \<longleftrightarrow>
      (\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow> holds ((substs 1 vs ?Y)[u/0]))"
    using assms(1) p holds_all[OF nY] by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow> holds (substs 0 (u # vs) ?Y))"
    unfolding One_nat_def using Cons.prems(1) inhab_closed
    by (intro iff_allI imp_cong[OF refl]) (simp add: substs_Suc_subst)
  also have "\<dots> \<longleftrightarrow> (\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow>
      (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ u # vs) (sm \<rho> \<sigma> X))))"
    using Cons.IH[of "u # vs" for u] Cons.prems inhab_closed by (intro iff_allI imp_cong[OF refl]) simp
  also have "\<dots> \<longleftrightarrow> (\<forall>us. ptyped \<rho> (p # ps) us \<longrightarrow> holds (substs 0 (rev us @ vs) (sm \<rho> \<sigma> X)))"
  proof
    assume H: "\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow>
      (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ u # vs) (sm \<rho> \<sigma> X)))"
    show "\<forall>us. ptyped \<rho> (p # ps) us \<longrightarrow> holds (substs 0 (rev us @ vs) (sm \<rho> \<sigma> X))"
    proof (intro allI impI)
      fix us assume "ptyped \<rho> (p # ps) us"
      then obtain u us' where "us = u # us'" "inhab (tsubst \<rho> T) u" "ptyped \<rho> ps us'"
        by (auto simp: p list_all2_Cons1)
      with H show "holds (substs 0 (rev us @ vs) (sm \<rho> \<sigma> X))" by simp
    qed
  next
    assume H: "\<forall>us. ptyped \<rho> (p # ps) us \<longrightarrow> holds (substs 0 (rev us @ vs) (sm \<rho> \<sigma> X))"
    show "\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow>
      (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ u # vs) (sm \<rho> \<sigma> X)))"
    proof (intro allI impI)
      fix u us assume "inhab (tsubst \<rho> T) u" "ptyped \<rho> ps us"
      then have "ptyped \<rho> (p # ps) (u # us)" by (simp add: p)
      with H show "holds (substs 0 (rev us @ u # vs) (sm \<rho> \<sigma> X))" by fastforce
    qed
  qed
  finally show ?case .
qed

text \<open>Flattening parameters (\<^const>\<open>flatten_params\<close>) strengthens a proposition.\<close>

lemma flatten_params_holds:
  assumes "ok (flatten_params vl n A) A'"
    "length (vl (map fst (strip_params A))) = length (strip_params A)"
    "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "cok A" "proper A" "no_loose_bound (tr A) 0"
    "holds (sm \<rho> \<sigma> A')"
  shows "holds (sm \<rho> \<sigma> A)"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  have lv: "length ?vars = length ?ps" using assms(2) by simp
  have sv: "map snd ?vars = map snd ?ps" using assms(2) by (simp add: map_snd_zip)
  from assms(1) obtain A'' where r: "ok (remove_params (ilength ?vars) n A) A''"
    and A': "A' = list_forall ?vars A''"
    by (auto simp: flatten_params_def Let_def)
  have j: "ilength (strip_params A) = ilength ?vars" using lv by (simp add: ilength_eq)
  have wA'': "no_loose_bound (tr A'') (length ?ps)"
    using remove_params_wf[OF r j assms(6,5,7)] lv by (simp add: ilength_eq)
  have "\<forall>us. ptyped \<rho> ?vars us \<longrightarrow> holds (substs 0 (rev us) (sm \<rho> \<sigma> A''))"
    using holds_list_forall[OF assms(3,4), of "[]" A'' ?vars \<rho>] assms(8) A' wA'' lv by simp
  then have "\<forall>us. ptyped \<rho> ?ps us \<longrightarrow> asem \<rho> \<sigma> 0 [] us A"
  proof (intro allI impI)
    fix us assume h: "\<forall>us. ptyped \<rho> ?vars us \<longrightarrow> holds (substs 0 (rev us) (sm \<rho> \<sigma> A''))"
      and t: "ptyped \<rho> ?ps us"
    have "asem \<rho> \<sigma> n [] us A"
    proof (rule remove_params_asem[OF r assms(3,4,5,6)])
      show "\<forall>u\<in>set us. closed u" using t by (rule ptyped_closed)
      show "length us = length ?ps" using t by (simp add: list_all2_lengthD)
      show "holds (substs 0 (rev us @ []) (sm \<rho> \<sigma> A''))"
        using h t ptyped_snd[OF sv] by simp
    qed (use assms(7) j in simp_all)
    then show "asem \<rho> \<sigma> 0 [] us A" by (rule asem_mono) simp
  qed
  with holds_asem[OF assms(3,4,5), of "[]" 0 \<rho>] assms(7) show ?thesis by simp
qed

text \<open>
  The first premise of a rule is proved by the assumption \<open>asm\<close> (elim-resolution) if the
  closures of \<open>asm\<close> and of the conclusion of the premise are equal.
\<close>

lemma eres_holds:
  assumes "assum_problems k A = (params, asms, concl)" "asm \<in> set asms"
    "sm \<rho> \<sigma> (rlist_abs params asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> (rlist_abs params concl)"
    "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "cok A" "proper A" "no_loose_bound (tr A) 0"
  shows "holds (sm \<rho> \<sigma> A)"
proof -
  from assum_problems_struct[OF assms(1,6)] have A: "A = list_forall (rev params) (list_implies asms concl)"
    by blast
  let ?m = "length params"
  have nb: "no_loose_bound (tr (list_implies asms concl)) ?m"
    using assms(8) A by (simp add: no_loose_bound_list_forall)
  then have nH: "\<forall>H\<in>set asms. no_loose_bound (tr H) ?m" and nC: "no_loose_bound (tr concl) ?m"
    by (simp_all add: no_loose_bound_list_implies)
  have hl: "holds (substs 0 [] (sm \<rho> \<sigma> (list_forall (rev params) (list_implies asms concl)))) \<longleftrightarrow>
      (\<forall>us. ptyped \<rho> (rev params) us \<longrightarrow>
        holds (substs 0 (rev us @ []) (sm \<rho> \<sigma> (list_implies asms concl))))"
    by (rule holds_list_forall[OF assms(4,5)]) (use nb in simp_all)
  have "\<forall>us. ptyped \<rho> (rev params) us \<longrightarrow>
      holds (substs 0 (rev us @ []) (sm \<rho> \<sigma> (list_implies asms concl)))"
  proof (intro allI impI)
    fix us assume t: "ptyped \<rho> (rev params) us"
    have cu: "\<forall>u\<in>set us. closed u" using t by (rule ptyped_closed)
    have lu: "length us = ?m" using list_all2_lengthD[OF t] by simp
    have cl: "closed (substs 0 (rev us) (sm \<rho> \<sigma> t))" if "no_loose_bound (tr t) ?m" for t
      using no_loose_bound_substs[of "rev us" "sm \<rho> \<sigma> t" 0] cu that lu assms(5)
      by (simp add: no_loose_bound_sm)
    have "substs 0 (rev us) (sm \<rho> \<sigma> asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 (rev us) (sm \<rho> \<sigma> concl)"
    proof -
      have e: "Abs_m ?m (sm \<rho> \<sigma> asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (sm \<rho> \<sigma> concl)"
        using assms(3) by (simp add: sm_def inst_rlist_abs tr_rlist_abs)
      have "substs 0 (rev us) (sm \<rho> \<sigma> asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (sm \<rho> \<sigma> asm) \<degree>\<degree> us"
        by (rule equiv_sym, rule beta_into_equiv, rule Abs_m_apps_substs[OF cu lu])
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (sm \<rho> \<sigma> concl) \<degree>\<degree> us"
        by (rule equiv_list_app[OF e]) (simp add: list_all2_refl)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 (rev us) (sm \<rho> \<sigma> concl)"
        by (rule beta_into_equiv, rule Abs_m_apps_substs[OF cu lu])
      finally show ?thesis .
    qed
    then have "holds (substs 0 (rev us) (sm \<rho> \<sigma> asm)) \<Longrightarrow> holds (substs 0 (rev us) (sm \<rho> \<sigma> concl))"
      using holds_equiv cl nH nC assms(2) by blast
    then show "holds (substs 0 (rev us @ []) (sm \<rho> \<sigma> (list_implies asms concl)))"
      using holds_foldr_dIMP[of "map (substs 0 (rev us) \<circ> sm \<rho> \<sigma>) asms" "substs 0 (rev us) (sm \<rho> \<sigma> concl)"]
        cl nH nC assms(2,4)
      by (simp add: sm_list_implies substs_foldr_dIMP)
  qed
  with hl A show ?thesis by simp
qed

end

end
