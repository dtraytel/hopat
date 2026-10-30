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

subsection \<open>The semantics\<close>

locale pure_sem =
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

end

end
